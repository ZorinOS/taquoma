#!/usr/bin/env python3
"""make_taquoma.py FAUXDANA.ttf METRICS.json OUT.ttf [--bold] [--layout-from DEJAVUSANS.ttf] [--no-hint]

Derives a Tahoma-metric-compatible face from Fauxdana (DejaVu Sans made
metric-compatible with Verdana) and the reference measurements extracted by
extract_metrics.py. Nothing but those numbers is taken from the reference
family: every outline is Fauxdana's, reshaped by arithmetic.
"""
import argparse
from array import array
import copy
import io
import itertools
import json
import math
import os
import statistics
import sys
import unicodedata

import pathops
from fontTools.pens.areaPen import AreaPen
from fontTools.pens.recordingPen import DecomposingRecordingPen
from fontTools.pens.transformPen import TransformPen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.ttLib import TTFont, newTable
from fontTools.ttLib.removeOverlaps import removeOverlaps
from fontTools.ttLib.tables import otTables as ot
from fontTools.ttLib.tables import ttProgram
from fontTools.ttLib.tables._g_l_y_f import Glyph, GlyphCoordinates

FAMILY = "Taquoma"
VERSION = "1.105"

# i and j (Latin and Cyrillic) are dotless i and j plus a dot.
DOTLESS = {0x0069: 0x0131, 0x006A: 0x0237, 0x0456: 0x0131, 0x0458: 0x0237}

ARABIC_RANGES = ((0x0600, 0x0700), (0x0750, 0x0780), (0x08A0, 0x0900), (0xFB50, 0xFE00), (0xFE70, 0xFF00))
HEBREW_RANGES = ((0x0590, 0x0600), (0xFB1D, 0xFB50))
# Glyphs drawn on the line frame so they join from line to line: box
# drawing, block elements, the pieces of tall integrals and brackets.
FRAME_RANGES = ((0x2500, 0x25A0), (0x2320, 0x2322), (0x239B, 0x23B4))
# Scripts whose accents sit above or below a separate letter body.
MARK_SHIFT_RANGES = ((0x0000, 0x0590), (0x1D00, 0x2000), (0x2C60, 0x2C80), (0xA640, 0xA6A0), (0xA720, 0xA800))


def in_ranges(code, ranges):
    return code is not None and any(a <= code < b for a, b in ranges)


def category(code):
    return unicodedata.category(chr(code)) if code is not None else "Cn"


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


# ---------------------------------------------------------------- outlines

def contour_ranges(g):
    start = 0
    for end in g.endPtsOfContours:
        yield start, end
        start = end + 1


def bounds(points):
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    return min(xs), max(xs), min(ys), max(ys)


def ink(glyf, name):
    g = glyf[name]
    if g.numberOfContours <= 0:
        return None
    return bounds(list(g.coordinates))


def map_points(g, fn, indices=None):
    coords = list(g.coordinates)
    for i in (range(len(coords)) if indices is None else indices):
        coords[i] = fn(*coords[i])
    g.coordinates = GlyphCoordinates(coords)


def _shoelace(pts):
    return sum(pts[i][0] * pts[(i + 1) % len(pts)][1] - pts[(i + 1) % len(pts)][0] * pts[i][1] for i in range(len(pts))) / 2


def dot_parts(g, upem, square=True, margin=10):
    """The dots of a glyph: parts that stand apart (no other part's outline
    comes within `margin` units of their box), are small (under 0.18 em; 0.2 em with square=False),
    filled (the outer contour covers at least 70% of its box) and have at
    most one hole (a ring). With square=True only roughly square ones
    (sides within 1:1.43). Each as (contour indices, x0, x1, y0, y1), sorted
    top to bottom, then left to right."""
    if g.numberOfContours <= 0:
        return []
    coords = list(g.coordinates)
    flags = list(g.flags)
    ranges = list(contour_ranges(g))
    boxes = [bounds(coords[a:b + 1]) for a, b in ranges]
    paths = {}
    def path(i):
        if i not in paths:
            a, b = ranges[i]
            paths[i] = _contour_path(coords[a:b + 1], [bool(f & 1) for f in flags[a:b + 1]])
        return paths[i]
    def overlap(p, q):
        return abs(pathops.op(p, q, pathops.PathOp.INTERSECTION, fix_winding=True).area)
    def within(i, j):
        # a hole: inside j's box and inside j's shape (not just its box, as a
        # dot under the tail of a letter is)
        bi, bj = boxes[i], boxes[j]
        if i == j or not (bj[0] <= bi[0] and bi[1] <= bj[1] and bj[2] <= bi[2] and bi[3] <= bj[3]):
            return False
        return overlap(path(i), path(j)) > 0.5 * abs(_shoelace(coords[ranges[i][0]:ranges[i][1] + 1]))
    parent = {i: next((j for j in range(len(boxes)) if within(i, j)), None) for i in range(len(boxes))}
    parts = [([t] + [i for i in parent if parent[i] == t], boxes[t]) for t in parent if parent[t] is None]
    def boxes_meet(a, b):
        return not (a[1] < b[0] or b[1] < a[0] or a[3] < b[2] or b[3] < a[2])
    def meets(k, m):
        # the boxes overlap and the part's box (grown by the margin) meets
        # the other part's outline
        (_, a), (other_idx, b) = parts[k], parts[m]
        if not boxes_meet(a, b):
            return False
        rect = pathops.Path()
        pen = rect.getPen()
        m = margin
        pen.moveTo((a[0] - m, a[2] - m)); pen.lineTo((a[0] - m, a[3] + m)); pen.lineTo((a[1] + m, a[3] + m)); pen.lineTo((a[1] + m, a[2] - m)); pen.closePath()
        return overlap(rect, path(other_idx[0])) > 1
    out = []
    limit = (0.18 if square else 0.2) * upem
    for k, (idx, box) in enumerate(parts):
        w, h = box[1] - box[0], box[3] - box[2]
        if not (0 < w < limit and 0 < h < limit) or len(idx) > 2:
            continue
        if square and not 0.7 <= w / h <= 1.43:
            continue
        if any(meets(k, m) for m in range(len(parts)) if m != k):
            continue
        a, b = ranges[idx[0]]
        if abs(_shoelace(coords[a:b + 1])) < 0.7 * w * h:
            continue
        out.append((idx,) + tuple(box))
    out.sort(key=lambda d: (-round((d[3] + d[4]) / 2 / 40), (d[1] + d[2]) / 2))
    return out


class GlyphCoordinatesGlyph:
    """A view of glyph g with other coordinates, for dot_parts."""
    def __init__(self, g, coords):
        self.numberOfContours = g.numberOfContours
        self.endPtsOfContours = g.endPtsOfContours
        self.flags = g.flags
        self.coordinates = coords


def _side(a, b):
    """Horizontal component (as -1, 0, 1) of the edge a->b's normal pointing
    away from the ink. TrueType outer contours run clockwise with the ink on
    the right, so that normal is the edge direction turned left: (-dy, dx)."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    length = math.hypot(dx, dy)
    nx = -dy / length
    return 1 if nx > 0.05 else -1 if nx < -0.05 else 0


def embolden_x(g, e):
    """Pushes every edge that is not horizontal outwards by e font units along
    x (inwards for e < 0): stems and diagonals gain 2e of width, horizontal
    strokes keep their thickness. Each point moves by +-e according to which
    side the ink lies on along its two edges; points between a left- and a
    right-facing edge (curve tops, the tip of a V) stay put."""
    if abs(e) < 1e-6:
        return
    coords = list(g.coordinates)
    moved = list(coords)
    for start, end in contour_ranges(g):
        pts = coords[start:end + 1]
        n = len(pts)
        if n < 3:
            continue
        for i in range(n):
            j = (i - 1) % n
            while pts[j] == pts[i] and j != i:
                j = (j - 1) % n
            k = (i + 1) % n
            while pts[k] == pts[i] and k != i:
                k = (k + 1) % n
            if j == i or k == i:
                continue
            side = clamp(_side(pts[j], pts[i]) + _side(pts[i], pts[k]), -1, 1)
            moved[start + i] = (pts[i][0] + e * side, pts[i][1])
    g.coordinates = GlyphCoordinates(moved)


def _contour_paths(g):
    coords = list(g.coordinates)
    flags = list(g.flags)
    for start, end in contour_ranges(g):
        pts = coords[start:end + 1]
        on = [bool(f & 1) for f in flags[start:end + 1]]
        area = 0.0
        for i in range(len(pts)):
            (xa, ya), (xb, yb) = pts[i], pts[(i + 1) % len(pts)]
            area += xa * yb - xb * ya
        yield pts, on, area / 2


def _contour_path(pts, on):
    """A closed TrueType contour as a pathops path."""
    path = pathops.Path()
    pen = path.getPen()
    n = len(pts)
    start = next((i for i in range(n) if on[i]), None)
    if start is None:                      # all off-curve: implied on-curve start
        first = ((pts[0][0] + pts[-1][0]) / 2, (pts[0][1] + pts[-1][1]) / 2)
        pen.moveTo(first)
        pen.qCurveTo(*pts, first)
    else:
        seq = pts[start:] + pts[:start]
        flg = on[start:] + on[:start]
        pen.moveTo(seq[0])
        offs = []
        for p, o in zip(seq[1:] + [seq[0]], flg[1:] + [True]):
            if o:
                pen.qCurveTo(*offs, p) if offs else pen.lineTo(p)
                offs = []
            else:
                offs.append(p)
    pen.closePath()
    return path


def _polyline(pts, on, step=6):
    """A contour as a dense polyline (quadratic curves through their
    control points: close enough to measure gaps between parts)."""
    path = _contour_path(pts, on)
    out, cur = [], None
    for verb, args in path:
        for q in args:
            if cur is not None:
                n = max(1, int(math.hypot(q[0] - cur[0], q[1] - cur[1]) / step))
                out += [(cur[0] + (q[0] - cur[0]) * t / n, cur[1] + (q[1] - cur[1]) * t / n) for t in range(1, n + 1)]
            cur = q
    return out or list(pts)


def _distance(pa, pb):
    return min(math.hypot(x0 - x1, y0 - y1) for x0, y0 in pa for x1, y1 in pb)


def _crosses_itself(pts, on):
    """True if a closed TrueType contour crosses itself."""
    path = _contour_path(pts, on)
    area = abs(path.area)
    simple = pathops.simplify(path, fix_winding=True, keep_starting_points=True)
    return len(list(simple.contours)) > 1 or abs(abs(simple.area) - area) > max(4.0, 0.002 * area)


def new_overlaps(before, g, allowed=None):
    """Did a transform make two separate parts of a glyph run into each
    other (two dots of a vowel point, a breathing mark and an accent)?
    Contours that already overlapped (counters, joined marks) do not count,
    nor pairs `allowed(i, j)` accepts."""
    return bool(overlapping_pairs(before, g, allowed, first=True))


def overlapping_pairs(before, g, allowed=None, first=False):
    """The pairs of contours that overlap now but did not before."""
    found = []
    if g.numberOfContours <= 1:
        return found
    ranges = list(contour_ranges(g))
    flags = list(g.flags)
    after = list(g.coordinates)
    def boxes(coords):
        return [(min(coords[i][0] for i in range(a, b + 1)), max(coords[i][0] for i in range(a, b + 1)),
                 min(coords[i][1] for i in range(a, b + 1)), max(coords[i][1] for i in range(a, b + 1))) for a, b in ranges]
    ba = boxes(after)
    def path(coords, k):
        a, b = ranges[k]
        return _contour_path(coords[a:b + 1], [bool(f & 1) for f in flags[a:b + 1]])
    for i in range(len(ranges)):
        for j in range(i + 1, len(ranges)):
            p, q = ba[i], ba[j]
            if p[0] >= q[1] or q[0] >= p[1] or p[2] >= q[3] or q[2] >= p[3]:
                continue
            if allowed is not None and allowed(i, j):
                continue
            now = abs(pathops.op(path(after, i), path(after, j), pathops.PathOp.INTERSECTION, fix_winding=True).area)
            if now <= 20:
                continue
            was = abs(pathops.op(path(before, i), path(before, j), pathops.PathOp.INTERSECTION, fix_winding=True).area)
            if was <= 1:
                found.append((i, j))
                if first:
                    return found
    return found


def damaged(before, g, gaps=True, allowed=None):
    """Did a transform turn a contour inside out or make it cross itself?
    (A stroke thinned past nothing, or a counter closed up.) Separate parts
    running into each other, and (with `gaps`) the space between side-by-side
    parts nearly closing, count too. `before` is the glyph's coordinates
    before the transform; contours that already crossed themselves do not
    count."""
    if g.numberOfContours <= 0:
        return False
    saved = g.coordinates
    # Judge the outline as it will be written: coordinates rounded to whole
    # units (rounding alone can make two nearly touching points cross).
    g.coordinates = GlyphCoordinates([(round(x), round(y)) for x, y in saved])
    after = list(_contour_paths(g))
    g.coordinates = GlyphCoordinates(before)
    prior = list(_contour_paths(g))
    g.coordinates = saved
    for (pa, on, area_after), (pb, _, area_before) in zip(after, prior):
        if abs(area_before) > 50 and (area_after > 0) != (area_before > 0):
            return True
        if _crosses_itself(pa, on) and not _crosses_itself(pb, on):
            return True
    return new_overlaps(before, g, allowed) or (gaps and gaps_closed(before, g))


def _boxes(coords, ranges):
    out = []
    for start, end in ranges:
        xs = [coords[i][0] for i in range(start, end + 1)]
        ys = [coords[i][1] for i in range(start, end + 1)]
        out.append((min(xs), max(xs), min(ys), max(ys)))
    return out


def _side_gaps(coords, ranges):
    """Horizontal gaps between contours that stand side by side (dots, the
    two commas of a quotation mark), keyed by contour pair."""
    boxes = _boxes(coords, ranges)
    out = {}
    for i, a in enumerate(boxes):
        for j, b in enumerate(boxes):
            if i != j and b[0] > a[1]:
                overlap = min(a[3], b[3]) - max(a[2], b[2])
                if overlap > 0.5 * min(a[3] - a[2], b[3] - b[2]):
                    out[(i, j)] = b[0] - a[1]
    return out


def gaps_closed(before, g, keep=0.45, minimum=40):
    """Did a transform nearly close a gap between side-by-side parts? The
    stroke push widens every part, so it eats into the space between two
    dots or two commas; a gap of at least `minimum` units that ends up
    narrower than `keep` of its scaled width counts as damage."""
    if g.numberOfContours <= 1:
        return False
    ranges = list(contour_ranges(g))
    gb = _side_gaps(before, ranges)
    if not gb:
        return False
    after = _boxes(g.coordinates, ranges)        # the same pairs, even if they now overlap
    xb = [x for x, _ in before]
    xa = [x for x, _ in g.coordinates]
    ratio = (max(xa) - min(xa)) / (max(xb) - min(xb)) if max(xb) > min(xb) else 1.0
    return any(gap >= minimum and after[j][0] - after[i][1] < keep * ratio * gap for (i, j), gap in gb.items())


def contour_signatures(g):
    """Per contour: (shape key independent of horizontal position, xMin, area).
    Used to find a base letter's body inside an accented letter."""
    out = []
    coords = list(g.coordinates)
    for start, end in contour_ranges(g):
        pts = coords[start:end + 1]
        x0 = min(p[0] for p in pts)
        key = tuple(sorted((round(x - x0), round(y)) for x, y in pts))
        area = 0.0
        for i in range(len(pts)):
            (xa, ya), (xb, yb) = pts[i], pts[(i + 1) % len(pts)]
            area += xa * yb - xb * ya
        out.append((key, x0, abs(area) / 2))
    return out


# ------------------------------------------------------------ preparation

def _leaves(dglyf, name, dx=0, dy=0):
    """A DejaVu composite flattened to [(simple glyph, x offset, y offset)];
    None if a component is scaled or attached by points."""
    g = dglyf[name]
    if not g.isComposite():
        return [(name, dx, dy)]
    out = []
    for c in g.components:
        if hasattr(c, "transform") or not hasattr(c, "x"):
            return None
        sub = _leaves(dglyf, c.glyphName, dx + c.x, dy + c.y)
        if sub is None:
            return None
        out += sub
    return out


def _point_ranges(g):
    if g.numberOfContours <= 0:
        return []
    out, start = [], 0
    for end in g.endPtsOfContours:
        out.append(list(range(start, end + 1)))
        start = end + 1
    return out


def _script(code):
    name = unicodedata.name(chr(code), "") if code is not None else ""
    return name.split(" ")[0]


def _assemble(glyf, pieces):
    """A simple glyph made of [(source glyph, contour indices or None, dx)]."""
    coords, flags, ends = [], [], []
    for src, keep, dx in pieces:
        g = glyf[src]
        for k, indices in enumerate(_point_ranges(g)):
            if keep is not None and k not in keep:
                continue
            coords += [(g.coordinates[i][0] + dx, g.coordinates[i][1]) for i in indices]
            flags += [g.flags[i] & 1 for i in indices]
            ends.append(len(coords) - 1)
    out = Glyph()
    out.numberOfContours = len(ends)
    out.coordinates = GlyphCoordinates(coords)
    out.flags = array("B", flags)
    out.endPtsOfContours = ends
    out.program = ttProgram.Program()
    out.program.fromBytecode(b"")
    out.recalcBounds(glyf)
    return out


def repair_composites(font, dejavu, tolerance=8):
    """Puts accents back over their letters. DejaVu Sans builds accented
    letters as composites of the base letter and its marks; older releases
    of Fauxdana kept DejaVu's component offsets but moved the marks inside
    their own spacing glyphs (its acute, grave and diaeresis sat about 140
    units further right), and refitted some letters as a whole afterwards,
    so their accents were off centre (o-diaeresis's dots 145 units right of
    the o) and some bodies displaced or narrowed (i-diaeresis's stem 130
    units left of its dots). Current releases place them correctly; this
    then mostly confirms them.
    Where Fauxdana's outline still has the composite's contours, the body is
    replaced by Fauxdana's own base letter, where that letter has it, and
    each mark is moved sideways to where DejaVu puts it relative to the
    body. Composites of marks alone (Greek dialytika with tonos, Hebrew
    tsere) get the same treatment around their first mark.

    Composites of whole letters (IJ, Cyrillic yeru, Yiddish double vav) are
    rebuilt from Fauxdana's letters, each moved by how much wider Fauxdana
    made the letters before it: Fauxdana kept DejaVu's offsets, so the J of
    its IJ sits on its (serifed, wider) I. Inside a letter of another script
    (the I of Cyrillic yeru) a letter Fauxdana gave serifs is plain, as it is
    in DejaVu. Returns ({glyph: [what moved]}, {glyph: [letters]} for the
    whole-letter composites of one script)."""
    glyf, dglyf = font["glyf"], dejavu["glyf"]
    if font.getGlyphOrder() != dejavu.getGlyphOrder():
        return None, {}
    dcmap = dejavu.getBestCmap()
    code_of = {}
    for code, name in sorted(dcmap.items()):
        code_of.setdefault(name, code)
    letters = {name for code, name in dcmap.items() if unicodedata.category(chr(code)) in ("Lu", "Ll", "Lt", "Lo")}
    gdef = dejavu["GDEF"].table.GlyphClassDef.classDefs if "GDEF" in dejavu else {}
    marklike = ({n for n, c in gdef.items() if c == 3} |
                {name for code, name in dcmap.items() if unicodedata.category(chr(code)) in ("Mn", "Me", "Sk", "Lm")})
    repaired, compositions = {}, {}
    for name in font.getGlyphOrder():
        if not dglyf[name].isComposite() or glyf[name].isComposite() or glyf[name].numberOfContours <= 0:
            continue
        leaves = _leaves(dglyf, name)
        if not leaves or len(leaves) < 2:
            continue
        bases = [i for i, (leaf, _, _) in enumerate(leaves) if leaf in letters]
        scripts = {_script(code_of.get(leaf)) for leaf, _, _ in leaves} | {_script(code_of.get(name))}
        if (len(bases) == len(leaves) and "ARABIC" not in scripts and all(y == 0 for _, _, y in leaves)
                and not any(glyf[leaf].isComposite() for leaf, _, _ in leaves)):
            ordered = sorted(leaves, key=lambda l: l[1])
            mixed = len(scripts) > 1
            pieces, before = [], 0
            for leaf, x, _ in ordered:
                keep, dx = None, x + before
                plain = len(_point_ranges(dglyf[leaf]))
                if mixed and len(_point_ranges(glyf[leaf])) > plain:
                    keep = set(range(plain))
                    kept = [glyf[leaf].coordinates[i][0] for k in keep for i in _point_ranges(glyf[leaf])[k]]
                    dx = x + before + dglyf[leaf].xMin - min(kept)
                pieces.append((leaf, keep, round(dx)))
                before += font["hmtx"][leaf][0] - dejavu["hmtx"][leaf][0]
            glyf[name] = _assemble(glyf, pieces)
            repaired[name] = [f"rebuilt from {' + '.join(l for l, _, _ in ordered)}"]
            if not mixed:
                compositions[name] = [l for l, _, _ in ordered]
            continue
        if len(bases) == 1 and leaves[bases[0]][2] == 0:     # one base letter, on the baseline
            b, anchored = bases[0], False
        elif not bases and all(leaf in marklike for leaf, _, _ in leaves):
            b, anchored = 0, True                             # marks only: the first one stays
        else:
            continue
        # Fauxdana's outline split into the components' contours: the same
        # point count contour by contour, in whatever order Fauxdana drew
        # them (its rebuilt l-middle-dot draws the l first; DejaVu's
        # composite has the dot first), matched by size. Fauxdana may draw
        # the base as DejaVu's plain letter where its own has serifs (the I
        # of polytonic Greek iota with breathings): then the glyph is
        # rebuilt with Fauxdana's own base letter, as the base would be.
        matched = _match_components(glyf, dglyf, name, leaves, b)
        if matched is None:
            continue
        groups, plain_base = matched
        rebuilt = []
        if plain_base and not anchored:
            conts = _point_ranges(glyf[name])
            scale = font["hmtx"][leaves[b][0]][0] / dejavu["hmtx"][leaves[b][0]][0]
            pieces = []
            for i, (leaf, own, here) in enumerate(groups):
                if i == b:
                    pieces.append((leaf, None, round(leaves[b][1] * scale)))
                else:
                    pieces.append((name, {conts.index(c) for c in here}, 0))
            glyf[name] = _assemble(glyf, pieces)
            matched = _match_components(glyf, dglyf, name, leaves, b, plain=False, order=False)
            if matched is None:
                continue
            groups = matched[0]
            rebuilt = ["body: the base letter's own drawing for DejaVu's plain one"]
        coords = list(glyf[name].coordinates)
        base_leaf, base_own, base_here = groups[b]
        hxs = [coords[i][0] for c in base_here for i in c]
        hx0, hx1 = min(hxs), max(hxs)
        if anchored:
            # Marks only: the first mark stays where it is, sized as it is.
            dlead = dglyf[base_leaf]
            scale = (hx1 - hx0) / (dlead.xMax - dlead.xMin) if dlead.xMax > dlead.xMin else 1.0
            base_coords = [tuple(coords[j]) for c in base_here for j in c]      # unchanged
            bx0, bx1 = hx0, hx1
        else:
            scale = font["hmtx"][base_leaf][0] / dejavu["hmtx"][base_leaf][0]
            offset = round(leaves[b][1] * scale)      # DejaVu moves a few bases (iota under a diaeresis)
            base_coords = [(x + offset, y) for x, y in glyf[base_leaf].coordinates]
            bxs = [base_coords[i][0] for c in base_own for i in c]
            bx0, bx1 = min(bxs), max(bxs)
        moved = list(rebuilt)
        if not anchored and any(tuple(coords[j]) != tuple(base_coords[i]) for src, dst in zip(base_own, base_here) for i, j in zip(src, dst)):
            for src, dst in zip(base_own, base_here):
                for i, j in zip(src, dst):
                    coords[j] = base_coords[i]
            moved.append(f"body {round((hx0 + hx1 - bx0 - bx1) / 2):+d} wider {round((hx1 - hx0) - (bx1 - bx0)):+d}")
        dbase = dglyf[base_leaf]
        dcentre = (dbase.xMin + dbase.xMax) / 2 + leaves[b][1]
        for i, (leaf, _, here) in enumerate(groups):
            mark = dglyf[leaf]
            if i == b or mark.numberOfContours <= 0:
                continue
            want = (bx0 + bx1) / 2 + ((mark.xMin + mark.xMax) / 2 + leaves[i][1] - dcentre) * scale
            idx = [j for c in here for j in c]
            xs = [coords[j][0] for j in idx]
            shift = round(want - (min(xs) + max(xs)) / 2)
            if abs(shift) > tolerance:
                for j in idx:
                    coords[j] = (coords[j][0] + shift, coords[j][1])
                moved.append(f"{leaf} {shift:+d}")
        if moved:
            glyf[name].coordinates = GlyphCoordinates(coords)
            glyf[name].recalcBounds(glyf)
            repaired[name] = moved
    return repaired, compositions


def _match_components(glyf, dglyf, name, leaves, b, plain=True, order=True):
    """Which of glyph `name`'s contours belong to which of its DejaVu
    composite's leaves: [(leaf, leaf's contours, contours here)] in leaf
    order, and whether the base (leaf b) is drawn as DejaVu's plain letter
    rather than Fauxdana's own. Each leaf's contours must have the same point
    counts as the leaf glyph's, in one block; the blocks may come in any order
    (with order=True), and the assignment whose contour boxes best match the
    leaves' sizes wins. None if nothing fits."""
    conts = _point_ranges(glyf[name])
    coords = glyf[name].coordinates
    if any(glyf[leaf].isComposite() for leaf, _, _ in leaves):
        return None
    options = []
    for i, (leaf, _, _) in enumerate(leaves):
        own = _point_ranges(glyf[leaf])
        opts = [(own, glyf[leaf], False)]
        theirs = _point_ranges(dglyf[leaf])
        if plain and i == b and theirs and [len(c) for c in theirs] != [len(c) for c in own]:
            opts.append((theirs, dglyf[leaf], True))
        options.append(opts)

    def size(ranges, co):
        xs = [co[i][0] for c in ranges for i in c]
        ys = [co[i][1] for c in ranges for i in c]
        return (max(xs) - min(xs), max(ys) - min(ys)) if xs else (0, 0)

    best, best_score = None, None
    perms = itertools.permutations(range(len(leaves))) if order and len(leaves) <= 5 else [tuple(range(len(leaves)))]
    for perm in perms:
        for choice in itertools.product(*[range(len(o)) for o in options]):
            k, groups, score, fits = 0, [None] * len(leaves), 0, True
            for li in perm:
                own, src, is_plain = options[li][choice[li]]
                here = conts[k:k + len(own)]
                if len(here) != len(own) or any(len(a) != len(c) for a, c in zip(own, here)):
                    fits = False
                    break
                (hw, hh), (ow, oh) = size(here, coords), size(own, src.coordinates)
                if abs(hw - ow) > max(40, 0.35 * ow) or abs(hh - oh) > max(40, 0.35 * oh):
                    fits = False
                    break
                score += abs(hw - ow) + abs(hh - oh)
                groups[li] = (leaves[li][0], _point_ranges(glyf[leaves[li][0]]) if not is_plain else own, here, is_plain)
                k += len(own)
            if fits and k == len(conts) and (best_score is None or score < best_score):
                best, best_score = groups, score
    if best is None:
        return None
    return [(leaf, own, here) for leaf, own, here, _ in best], best[b][3]


def embolden_y(g, e):
    """embolden_x for horizontal strokes: positive e thins them, pushing
    every top edge down and every bottom edge up by e (the axes are swapped,
    which reverses the contours' direction, so the sign flips)."""
    g.coordinates = GlyphCoordinates([(y, x) for x, y in g.coordinates])
    embolden_x(g, e)
    g.coordinates = GlyphCoordinates([(y, x) for x, y in g.coordinates])


def horizontal_bar(glyf, name):
    """Thickness of the topmost horizontal stroke through the middle of a
    glyph (the top bar of Hebrew he)."""
    g = glyf[name]
    path = pathops.Path()
    g.draw(path.getPen(), glyf)
    xs = [c[0] for c in g.coordinates]
    cx = (min(xs) + max(xs)) / 2
    band = pathops.Path()
    pen = band.getPen()
    pen.moveTo((cx - 1, -4000)); pen.lineTo((cx + 1, -4000)); pen.lineTo((cx + 1, 4000)); pen.lineTo((cx - 1, 4000)); pen.closePath()
    cut = pathops.op(path, band, pathops.PathOp.INTERSECTION, fix_winding=True)
    spans = []
    for contour in cut.contours:
        ys = [pt[1] for _, pts in contour for pt in pts]
        if ys:
            spans.append((min(ys), max(ys)))
    if not spans:
        return None
    lo, hi = max(spans, key=lambda s: s[1])
    return hi - lo


def drop_duplicate_contours(font):
    """Removes contours that repeat an earlier contour point for point.
    DejaVu builds e and o with circumflex and dot below from e/o with dot
    below plus another dot below, so the dot is drawn twice. Returns the
    glyphs cleaned."""
    glyf, cleaned = font["glyf"], []
    for name in font.getGlyphOrder():
        g = glyf[name]
        if g.isComposite() or g.numberOfContours <= 1:
            continue
        seen, keep = set(), []
        for k, indices in enumerate(_point_ranges(g)):
            key = tuple(tuple(g.coordinates[i]) for i in indices)
            if key not in seen:
                keep.append(k)
            seen.add(key)
        if len(keep) < g.numberOfContours:
            glyf[name] = _assemble(glyf, [(name, set(keep), 0)])
            cleaned.append(name)
    return cleaned


def decompose_and_dehint(font):
    glyf = font["glyf"]
    glyph_set = font.getGlyphSet()
    for name in font.getGlyphOrder():
        g = glyf[name]
        if g.isComposite():
            rec = DecomposingRecordingPen(glyph_set)
            glyph_set[name].draw(rec)
            pen = TTGlyphPen(None)
            rec.replay(pen)
            glyf[name] = pen.glyph()
    for name in font.getGlyphOrder():
        g = glyf[name]
        if g.numberOfContours > 0:
            g.program = ttProgram.Program()
            g.program.fromBytecode(b"")
    for tag in ("fpgm", "prep", "cvt ", "gasp", "hdmx", "LTSH", "VDMX", "MATH", "FFTM"):
        if tag in font:
            del font[tag]


def arabic_gsub(dejavu_path, font, mark_ligatures):
    """DejaVu Sans's Arabic joining (init/medi/fina/isol), lam-alef
    ligatures, and those ligatures of combining marks whose code point
    sequence is in `mark_ligatures` (the reference's: shadda + vowel sign);
    nothing else: no Latin substitutions, no other mark ligatures."""
    src = TTFont(dejavu_path)
    if src.getGlyphOrder() != font.getGlyphOrder():
        sys.exit(f"{dejavu_path}: glyph order differs from the Fauxdana face; use the DejaVu Sans release Fauxdana was built from")
    table = src["GSUB"].table
    script = next(r.Script for r in table.ScriptList.ScriptRecord if r.ScriptTag == "arab")
    dcmap = src.getBestCmap()
    lam_alef = {dcmap[c] for c in range(0xFEF5, 0xFEFD) if c in dcmap}
    marks = {name for code, name in dcmap.items() if unicodedata.category(chr(code)) == "Mn"}
    code_of = {}
    for code, name in sorted(dcmap.items()):
        code_of.setdefault(name, code)

    def mark_key(first, lig):
        parts = [first] + list(lig.Component)
        if all(g in marks for g in parts):
            return " ".join(f"{code_of[g]:04X}" for g in parts)
        return None

    def wanted(first, lig):
        # lam-alef, or a ligature of combining marks (shadda + vowel sign):
        # not DejaVu's space + mark spacing forms, which change advances.
        return lig.LigGlyph in lam_alef or all(g in marks for g in [first] + list(lig.Component))

    kept, filtered = [], {}
    for fi in script.DefaultLangSys.FeatureIndex:
        record = table.FeatureList.FeatureRecord[fi]
        tag = record.FeatureTag
        if tag in ("isol", "init", "medi", "fina"):
            kept.append((tag, list(record.Feature.LookupListIndex)))
        elif tag in ("rlig", "liga"):
            chosen = []
            for li in record.Feature.LookupListIndex:
                lookup = table.LookupList.Lookup[li]
                if lookup.LookupType == 4 and all(wanted(first, lig) for sub in lookup.SubTable
                                                  for first, ligs in sub.ligatures.items() for lig in ligs):
                    # Mark ligatures only in the order and combinations the
                    # reference forms (DejaVu also ligates vowel + shadda, and
                    # hamza + fatha or damma, which the reference leaves apart).
                    lookup = copy.deepcopy(lookup)
                    for sub in lookup.SubTable:
                        for first in list(sub.ligatures):
                            keep = [lig for lig in sub.ligatures[first]
                                    if mark_key(first, lig) is None or mark_key(first, lig) in mark_ligatures]
                            if keep:
                                sub.ligatures[first] = keep
                            else:
                                del sub.ligatures[first]
                    lookup.SubTable = [sub for sub in lookup.SubTable if sub.ligatures]
                    lookup.SubTableCount = len(lookup.SubTable)
                    if lookup.SubTable:
                        filtered[li] = lookup
                        chosen.append(li)
            if chosen:
                # DejaVu makes some of these required ligatures (rlig); the
                # reference has them all as ordinary ligatures (liga), which
                # text with ligatures turned off (CSS font-variant-ligatures:
                # none) sets letter by letter. Taquoma follows it, or lam-alef
                # would be one glyph in Taquoma and two in the reference.
                kept.append(("liga", chosen))
    merged = {}
    for tag, idx in kept:
        merged.setdefault(tag, []).extend(idx)
    kept = [(tag, sorted(set(idx))) for tag, idx in merged.items()]
    old = sorted({li for _, idx in kept for li in idx})       # keep DejaVu's lookup order
    renumber = {li: i for i, li in enumerate(old)}
    gsub = ot.GSUB()
    gsub.Version = 0x00010000
    gsub.LookupList = ot.LookupList()
    gsub.LookupList.Lookup = [filtered[li] if li in filtered else copy.deepcopy(table.LookupList.Lookup[li]) for li in old]
    gsub.LookupList.LookupCount = len(old)
    records = []
    for tag, idx in sorted(kept):
        record = ot.FeatureRecord()
        record.FeatureTag = tag
        record.Feature = ot.Feature()
        record.Feature.FeatureParams = None
        record.Feature.LookupListIndex = [renumber[li] for li in idx]
        record.Feature.LookupCount = len(idx)
        records.append(record)
    gsub.FeatureList = ot.FeatureList()
    gsub.FeatureList.FeatureRecord = records
    gsub.FeatureList.FeatureCount = len(records)
    langsys = ot.LangSys()
    langsys.LookupOrder = None
    langsys.ReqFeatureIndex = 0xFFFF
    langsys.FeatureIndex = list(range(len(records)))
    langsys.FeatureCount = len(records)
    script_out = ot.Script()
    script_out.DefaultLangSys = langsys
    script_out.LangSysRecord = []
    script_out.LangSysCount = 0
    script_record = ot.ScriptRecord()
    script_record.ScriptTag = "arab"
    script_record.Script = script_out
    gsub.ScriptList = ot.ScriptList()
    gsub.ScriptList.ScriptRecord = [script_record]
    gsub.ScriptList.ScriptCount = 1
    out = newTable("GSUB")
    out.table = gsub
    return out


def add_allah_ligature(font, gsub_table, glyph_set):
    """The reference ligates initial lam, medial lam and final heh into
    U+FDF2 (the Allah ligature). Fauxdana has no such glyph, so one is
    assembled from its own three joining forms and substituted by the same
    sequence; it is refitted to the reference's U+FDF2 like any other glyph."""
    cmap = font.getBestCmap()
    parts = [cmap.get(c) for c in (0xFEEA, 0xFEE0, 0xFEDF)]   # left to right on the page
    if None in parts or 0xFDF2 in cmap:
        return None
    name = "uniFDF2"
    pen = TTGlyphPen(None)
    x = 0
    for part in parts:
        rec = DecomposingRecordingPen(glyph_set)
        glyph_set[part].draw(rec)
        rec.replay(TransformPen(pen, (1, 0, 0, 1, x, 0)))
        x += font["hmtx"][part][0]
    glyph = pen.glyph()
    font.setGlyphOrder(font.getGlyphOrder() + [name])
    font["glyf"][name] = glyph
    glyph.recalcBounds(font["glyf"])
    font["hmtx"][name] = (x, glyph.xMin)
    for table in font["cmap"].tables:
        if table.isUnicode():
            table.cmap[0xFDF2] = name
    lookup = ot.Lookup()
    lookup.LookupType = 4
    lookup.LookupFlag = 9                     # right to left, ignore marks
    sub = ot.LigatureSubst()
    sub.Format = 1
    lig = ot.Ligature()
    lig.LigGlyph = name
    lig.Component = [parts[1], parts[0]]      # logical order: lam.init, lam.medi, heh.fina
    lig.CompCount = 3
    sub.ligatures = {parts[2]: [lig]}
    lookup.SubTable = [sub]
    lookup.SubTableCount = 1
    table = gsub_table.table
    table.LookupList.Lookup.append(lookup)
    table.LookupList.LookupCount += 1
    index = table.LookupList.LookupCount - 1
    liga = [r for r in table.FeatureList.FeatureRecord if r.FeatureTag == "liga"]
    if liga:
        liga[0].Feature.LookupListIndex.append(index)
        liga[0].Feature.LookupCount += 1
    else:
        record = ot.FeatureRecord()
        record.FeatureTag = "liga"
        record.Feature = ot.Feature()
        record.Feature.FeatureParams = None
        record.Feature.LookupListIndex = [index]
        record.Feature.LookupCount = 1
        records = sorted(table.FeatureList.FeatureRecord + [record], key=lambda r: r.FeatureTag)
        table.FeatureList.FeatureRecord = records
        table.FeatureList.FeatureCount = len(records)
        langsys = table.ScriptList.ScriptRecord[0].Script.DefaultLangSys
        langsys.FeatureIndex = list(range(len(records)))
        langsys.FeatureCount = len(records)
    return name


# OS/2 code-page bits and the code pages they stand for.
CODE_PAGES = {0: "cp1252", 1: "cp1250", 2: "cp1251", 3: "cp1253", 4: "cp1254", 5: "cp1255", 6: "cp1256",
              7: "cp1257", 8: "cp1258", 16: "cp874", 29: "mac_roman", 48: "cp869", 49: "cp866", 50: "cp865",
              51: "cp864", 52: "cp863", 53: "cp862", 54: "cp861", 55: "cp860", 56: "cp857", 57: "cp855",
              58: "cp852", 59: "cp775", 60: "cp737", 61: "iso8859_6", 62: "cp850", 63: "cp437"}


def lost_scripts(ref_codes, codes):
    """The OS/2 Unicode-range bits and code-page bits of scripts this face
    lacks: where it has fewer than half the reference's characters in the
    range (for a code page, of its letters)."""
    from fontTools.ttLib.tables.O_S_2f_2 import OS2_UNICODE_RANGES
    ranges = []
    for bit, blocks in enumerate(OS2_UNICODE_RANGES):
        in_ref = {c for c in ref_codes for _, (lo, hi) in blocks if lo <= c <= hi}
        if in_ref and 2 * len(in_ref & codes) < len(in_ref):
            ranges.append(bit)
    pages = []
    for bit, codec in sorted(CODE_PAGES.items()):
        letters = set()
        for byte in range(0x80, 0x100):
            try:
                ch = bytes([byte]).decode(codec)
            except UnicodeDecodeError:
                continue
            if len(ch) == 1 and unicodedata.category(ch).startswith("L"):
                letters.add(ord(ch))
        in_ref = letters & ref_codes
        if in_ref and 2 * len(in_ref & codes) < len(in_ref):
            pages.append(bit)
    return ranges, pages


def ligature_glyph(gsub_table, parts):
    """The glyph a ligature lookup makes from the glyph sequence `parts`, or None."""
    if None in parts:
        return None
    for lookup in gsub_table.table.LookupList.Lookup:
        for sub in lookup.SubTable:
            for lig in getattr(sub, "ligatures", {}).get(parts[0], []):
                if list(lig.Component) == parts[1:]:
                    return lig.LigGlyph
    return None


def single_mappings(gsub_table, tag):
    mapping = {}
    for record in gsub_table.table.FeatureList.FeatureRecord:
        if record.FeatureTag != tag:
            continue
        for li in record.Feature.LookupListIndex:
            for sub in gsub_table.table.LookupList.Lookup[li].SubTable:
                mapping.update(getattr(sub, "mapping", {}))
    return mapping


def strip_damaging_hints(font, data, sizes=(6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 20, 24, 32, 48)):
    """ttfautohint fits every glyph to Latin alignment zones; some symbols it
    does not understand (braille cells, pieces of tall brackets and
    integrals, large operators, a few thin symbols and syllabics at 6-8 px)
    come out distorted: ink lost or doubled, or dots snapped onto the
    baseline. Renders every mapped glyph with and
    without hinting (FreeType's full TrueType interpreter, as on Windows)
    and removes the hinting from any glyph whose hinted rendering loses or
    gains more than half its ink or moves its top or bottom by more than two
    pixels; such a glyph is then simply scaled. Needs freetype-py; without
    it nothing is changed."""
    import os
    os.environ.setdefault("FREETYPE_PROPERTIES", "truetype:interpreter-version=35")
    try:
        import freetype
    except ImportError:
        print("freetype-py not installed: hinted glyphs not checked")
        return []
    face = freetype.Face(io.BytesIO(data))

    def render(index, flags):
        face.load_glyph(index, flags)
        face.glyph.render(freetype.FT_RENDER_MODE_NORMAL)
        bm = face.glyph.bitmap
        if not bm.width:
            return 0.0, None
        total = sum(bm.buffer) / 255.0
        return total, (face.glyph.bitmap_top, face.glyph.bitmap_top - bm.rows)

    damaged_glyphs = set()
    for ppem in sizes:
        face.set_pixel_sizes(0, ppem)
        for code, name in font.getBestCmap().items():
            if name in damaged_glyphs or font["glyf"][name].numberOfContours <= 0:
                continue
            index = font.getGlyphID(name)
            plain, plain_box = render(index, freetype.FT_LOAD_NO_HINTING)
            if plain < 1.0:
                continue
            hinted_ink, hinted_box = render(index, freetype.FT_LOAD_DEFAULT | freetype.FT_LOAD_TARGET_NORMAL)
            ratio = hinted_ink / plain
            moved = plain_box and hinted_box and (abs(hinted_box[0] - plain_box[0]) > 2 or abs(hinted_box[1] - plain_box[1]) > 2)
            if ratio < 0.5 or ratio > 2.0 or moved:
                damaged_glyphs.add(name)
    for name in damaged_glyphs:
        program = ttProgram.Program()
        program.fromBytecode(b"")
        font["glyf"][name].program = program
    return sorted(damaged_glyphs, key=font.getGlyphID)


# ------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("fauxdana")
    ap.add_argument("metrics")
    ap.add_argument("out")
    ap.add_argument("--bold", action="store_true")
    ap.add_argument("--layout-from", metavar="DEJAVUSANS.ttf")
    ap.add_argument("--no-hint", action="store_true")
    ap.add_argument("--full-coverage", action="store_true",
                    help="keep every character Fauxdana has, not only the reference's")
    args = ap.parse_args()

    style_key = "bold" if args.bold else "regular"
    style = "Bold" if args.bold else "Regular"
    with open(args.metrics) as f:
        ref = json.load(f)[style_key]

    font = TTFont(args.fauxdana)
    assert font["head"].unitsPerEm == ref["unitsPerEm"] == 2048
    glyf, hmtx = font["glyf"], font["hmtx"]

    repaired, compositions = repair_composites(font, TTFont(args.layout_from)) if args.layout_from else (None, {})
    if repaired is None:
        print("warning: accents not re-centred (needs --layout-from with the DejaVu Sans Fauxdana was made from)")
    decompose_and_dehint(font)
    duplicates = drop_duplicate_contours(font)
    # The shape of every dot as drawn, before any fitting (see "Dots keep
    # their shape" below).
    source_dots = {name: [(d[2] - d[1]) / (d[4] - d[3]) for d in dot_parts(glyf[name], 2048)]
                   for name in font.getGlyphOrder()}
    gsub = None
    if args.layout_from:
        if "markLigatures" not in ref:
            sys.exit(f"{args.metrics}: no markLigatures; re-run extract_metrics.py on the reference fonts")
        gsub = arabic_gsub(args.layout_from, font, {key for entries in ref["markLigatures"].values() for key in entries})
        add_allah_ligature(font, gsub, font.getGlyphSet())
        # Contextual forms only where the reference has them too: where it
        # has none (its alef maksura, noon ghunna and ae never take initial or
        # medial forms) it shows the plain letter, at the plain letter's width.
        encoded = {}
        for code, name in sorted(font.getBestCmap().items()):
            encoded.setdefault(name, code)
        for record in gsub.table.FeatureList.FeatureRecord:
            if record.FeatureTag not in ("isol", "init", "medi", "fina"):
                continue
            allowed = {int(c, 16) for c in ref.get("forms", {}).get(record.FeatureTag, {})}
            for li in record.Feature.LookupListIndex:
                for sub in gsub.table.LookupList.Lookup[li].SubTable:
                    for src in list(getattr(sub, "mapping", {})):
                        if encoded.get(src) not in allowed:
                            del sub.mapping[src]
    cmap = font.getBestCmap()
    order = font.getGlyphOrder()
    code_of = {}
    for code, name in sorted(cmap.items()):
        code_of.setdefault(name, code)
    # Overlapping contours (Fauxdana's I and J bars cross their stems) are
    # merged so the stroke compensation sees one outline. Glyphs with nothing
    # to merge (same contours, same area) keep their outlines as they are:
    # overlap removal redraws curves with other points, and a letter's body
    # must stay point for point the base letter's to be found in it.
    # A base letter drawn off the baseline inside an accented letter (in
    # Fauxdana 1.102 Regular, the U of U-horn and its five Vietnamese
    # forms stands 20 units high) is brought back down to where the plain
    # letter stands, with its marks.
    lifted = []
    for n in order:
        code = code_of.get(n)
        if code is None or glyf[n].numberOfContours <= 0:
            continue
        nfd = unicodedata.normalize("NFD", chr(code))
        if len(nfd) < 2 or not all(unicodedata.category(c).startswith("M") for c in nfd[1:]):
            continue
        base = cmap.get(DOTLESS.get(ord(nfd[0]), ord(nfd[0])))
        if base is None or base == n or glyf[base].numberOfContours <= 0:
            continue
        def shapes(g):
            coords, out, start = list(g.coordinates), [], 0
            for end in g.endPtsOfContours:
                pts = [(round(x), round(y)) for x, y in coords[start:end + 1]]
                x0, y0 = min(p[0] for p in pts), min(p[1] for p in pts)
                out.append((tuple(sorted((x - x0, y - y0) for x, y in pts)), y0))
                start = end + 1
            return out
        b, here = shapes(glyf[base]), shapes(glyf[n])
        key, by0 = max(b, key=lambda t: len(t[0]))
        if any(k == key and y0 == by0 for k, y0 in here):
            continue
        dys = [y0 - by0 for k, y0 in here if k == key]
        if len(dys) == 1 and 0 < abs(dys[0]) <= 60 and all(any(k == kk and y0 - yy == dys[0] for kk, y0 in here) for k, yy in b):
            map_points(glyf[n], lambda x, y, d=dys[0]: (x, y - d))
            lifted.append(code)
    shown = [c for c in lifted if args.full_coverage or f"{c:04X}" in ref["glyphs"]]
    if shown:
        print(f"accented letters whose base letter stood off the baseline, brought down: {' '.join(chr(c) for c in shown)}")
    multi = [n for n in order if glyf[n].numberOfContours > 1]
    untouched_outlines = {n: copy.deepcopy(glyf[n]) for n in multi}
    removeOverlaps(font, multi)
    def area(g):
        pen = AreaPen()
        g.draw(pen, glyf)
        return abs(pen.value)
    merged_now = []
    for n in multi:
        was = untouched_outlines[n]
        if glyf[n].numberOfContours == was.numberOfContours and abs(area(glyf[n]) - area(was)) <= 0.001 * area(was) + 1:
            glyf[n] = copy.deepcopy(was)
        else:
            merged_now.append(n)
    # A mark drawn overlapping its letter (the ogonek and cedilla, the horn
    # of O and U, the comma under t) was merged into it just now, and the
    # letter body could then no longer be found in it: the accented letter
    # was fitted as a whole to the reference's ink box, which stretched the
    # body to wherever the reference's mark reaches (Bold a-ogonek came out
    # about 17% wider than a). Such letters are put back together from the base
    # letter as merged above and the mark as drawn, so they get the base
    # letter's transform; the mark is merged into the letter at the end.
    rejoined = {}            # glyph -> its merged outline, used if the body can't be reused after all
    for n in merged_now:
        code = code_of.get(n)
        if code is None:
            continue
        nfd = unicodedata.normalize("NFD", chr(code))
        if len(nfd) < 2 or not all(unicodedata.category(c).startswith("M") for c in nfd[1:]):
            continue
        base = cmap.get(DOTLESS.get(ord(nfd[0]), ord(nfd[0])))
        if base is None or glyf[base].numberOfContours <= 0:
            continue
        base_drawn = untouched_outlines.get(base, glyf[base])
        sig_base, sig_name = contour_signatures(base_drawn), contour_signatures(untouched_outlines[n])
        key, bx0, _ = max(sig_base, key=lambda c: c[2])
        found = None
        for k, x0, _ in sig_name:
            if k != key:
                continue
            want = sorted((kk, round(xx - bx0 + x0)) for kk, xx, _ in sig_base)
            have = [(kk, round(xx)) for kk, xx, _ in sig_name]
            if all(w in have for w in want):
                found = x0 - bx0
                break
        if found is None:
            continue
        body_ids = {c for c, (kk, xx, _) in enumerate(sig_name) if (kk, round(xx - found - bx0)) in
                    {(k2, round(x2 - bx0)) for k2, x2, _ in sig_base}}
        marks_ids = {c for c in range(len(sig_name)) if c not in body_ids}
        if not marks_ids:
            continue
        rejoined[n] = glyf[n]
        glyf[n] = _assemble({base: glyf[base], n: untouched_outlines[n]},
                            [(base, None, found), (n, marks_ids, 0)])

    ref_glyphs = {int(k, 16): v for k, v in ref["glyphs"].items()}

    # --- Letter heights. Neither font records its x-height or cap height
    # (OS/2 version 1), so browsers measure the x and H glyphs for CSS ex and
    # cap units, font-size-adjust and vertical-align: middle. Fauxdana's are
    # a few units off the reference's (x 1120 vs 1117 / 1123, H 1493 vs
    # 1489); a piecewise-linear vertical map (fixed at the baseline and the
    # ascender) brings every Latin, Greek and Cyrillic letter to the
    # reference's x-height, cap height and ascender. Points move by 4 units
    # at most.
    def top(name):
        return ink(glyf, name)[3]
    anchors = [(0.0, 0.0)]
    for ch in "xHl":
        anchors.append((float(top(cmap[ord(ch)])), float(ref_glyphs[ord(ch)][4])))
    def letter_height(x, y):
        if y <= 0:
            return x, y
        for (a0, b0), (a1, b1) in zip(anchors, anchors[1:]):
            if y <= a1:
                return x, b0 + (y - a0) * (b1 - b0) / (a1 - a0)
        return x, y + anchors[-1][1] - anchors[-1][0]
    for name in order:
        code = code_of.get(name)
        if glyf[name].numberOfContours > 0 and in_ranges(code, MARK_SHIFT_RANGES) and category(code).startswith("L"):
            map_points(glyf[name], letter_height)

    # --- Hebrew height. DejaVu draws Hebrew letters at the Latin x-height
    # (1120); the reference's are taller (the median top of its letters,
    # 1297). Hebrew letters are stretched to that height from the baseline,
    # with their horizontal strokes thinned back so the weight is unchanged;
    # descenders keep their depth and anything above the letter height moves
    # up with it. Dots inside letters (dagesh, shin and sin dots) only move.
    hebrew_count = 0
    he_codes = [c for c in range(0x05D0, 0x05EB) if c in cmap and c in ref_glyphs and len(ref_glyphs[c]) == 5]
    if he_codes and 0x05D4 in cmap:
        src_top = statistics.median(top(cmap[c]) for c in he_codes)
        ref_top = statistics.median(ref_glyphs[c][4] for c in he_codes)
        bar = horizontal_bar(glyf, cmap[0x05D4])          # the top bar of he
        if bar and 1.02 < ref_top / src_top < 1.4:
            k = (ref_top - bar) / (src_top - bar)
            d = (k - 1) * bar / 2
            def stretch(x, y):                           # before thinning by d
                if y <= 0:
                    return x, y - d
                if y <= src_top:
                    return x, -d + k * y
                return x, -d + k * src_top + (y - src_top)
            def settle(y):                               # where a point ends up
                return y if y <= 0 else y * ref_top / src_top if y <= src_top else y + ref_top - src_top
            for name in order:
                code = code_of.get(name)
                g = glyf[name]
                if (g.numberOfContours <= 0 or not (in_ranges(code, ((0x05D0, 0x0600), (0xFB1D, 0xFB50))))
                        or not category(code).startswith("L")):
                    continue
                ranges = list(contour_ranges(g))
                coords = list(g.coordinates)
                small = [k_ for k_, (a, b) in enumerate(ranges)
                         if max(c[0] for c in coords[a:b + 1]) - min(c[0] for c in coords[a:b + 1]) < 1.6 * bar
                         and max(c[1] for c in coords[a:b + 1]) - min(c[1] for c in coords[a:b + 1]) < 1.6 * bar
                         and len(ranges) > 1]
                body = [k_ for k_ in range(len(ranges)) if k_ not in small]
                for k_ in small:                         # dots: moved, not stretched
                    a, b = ranges[k_]
                    ys = [c[1] for c in coords[a:b + 1]]
                    dy = settle((min(ys) + max(ys)) / 2) - (min(ys) + max(ys)) / 2
                    for i in range(a, b + 1):
                        coords[i] = (coords[i][0], coords[i][1] + dy)
                g.coordinates = GlyphCoordinates(coords)
                # the letter: stretched, then its horizontal strokes thinned
                body_glyph = _assemble(glyf, [(name, set(body), 0)])
                map_points(body_glyph, stretch)
                embolden_y(body_glyph, d)
                new = list(g.coordinates)
                k_new = 0
                for k_ in body:
                    a, b = ranges[k_]
                    for i in range(a, b + 1):
                        new[i] = tuple(body_glyph.coordinates[k_new])
                        k_new += 1
                g.coordinates = GlyphCoordinates(new)
                g.recalcBounds(glyf)
                hebrew_count += 1

    # --- Targets: glyph -> reference metrics (by code point, then by the
    # Arabic contextual form the restored GSUB substitutes).
    targets, target_code = {}, {}
    for code, name in sorted(cmap.items()):
        if code in ref_glyphs and name not in targets:
            targets[name] = ref_glyphs[code]
            target_code[name] = code
    form_glyph = {}          # (feature, code) -> glyph
    mark_lig_glyph = {}      # "0651 064E" -> ligature glyph
    if gsub is not None:
        for tag in ("isol", "init", "medi", "fina"):
            mapping = single_mappings(gsub, tag)
            for code, values in ref["forms"].get(tag, {}).items():
                src = cmap.get(int(code, 16))
                dst = mapping.get(src)
                if dst is None:
                    continue
                form_glyph[(tag, int(code, 16))] = dst
                targets[dst] = values
                target_code[dst] = int(code, 16)
        # Mark ligatures (shadda + vowel sign) take the reference's ligature
        # glyph's width and ink box, as single marks take theirs.
        for entries in ref["markLigatures"].values():
            for key, values in entries.items():
                name = ligature_glyph(gsub, [cmap.get(int(c, 16)) for c in key.split()])
                if name is not None:
                    mark_lig_glyph[key] = name
                    targets[name] = values
                    target_code[name] = int(key.split()[0], 16)

    # --- Reference stems and the family-wide condensation.
    ref_l = ref_glyphs[ord("l")]
    stem_ref = ref_l[2] - ref_l[1]
    lx0, lx1, _, _ = ink(glyf, cmap[ord("l")])
    stem = lx1 - lx0

    e_min, e_max = -0.1 * stem, 0.3 * stem

    def solve(W, Wt, lo, hi, damping=1.0):
        """Scale s and edge push e taking ink width W to Wt and a stem to
        stem_ref. Thinning is limited (a stroke is never pushed in by more
        than a tenth of a stem); past that, scaling takes over the width.
        `damping` < 1 weakens the push (used when the full push damages an
        outline); 0 is plain scaling, which cannot."""
        if W < 1.25 * stem:    # a single stroke or dot: plain scaling, within limits
            return (clamp(Wt / W, max(lo, 0.75), min(hi, 1.15)) if W > 0 else 1.0), 0.0
        # Unclamped, s * W + 2e = Wt exactly; clamped (the two designs
        # differ too much), stems still come out near stem_ref wide and the
        # ink is centred on the reference's.
        s = (Wt - stem_ref) / (W - stem)
        e = (stem_ref - s * stem) / 2
        if not e_min <= e <= e_max:
            e = clamp(e, e_min, e_max)
            s = (Wt - 2 * e) / W
        if not lo <= s <= hi:
            s = clamp(s, lo, hi)
            e = clamp((stem_ref - s * stem) / 2, e_min, e_max)
        if damping < 1.0:
            e *= damping
            s = clamp((Wt - 2 * e) / W, lo, hi)
        return s, e

    scales, spacing = [], []
    for ch in "abcdeghkmnopqrsuvwxyzABCDEFGHKLMNOPRSUVWXYZ":
        name = cmap[ord(ch)]
        x0, x1, _, _ = ink(glyf, name)
        t = ref_glyphs[ord(ch)]
        scales.append(solve(x1 - x0, t[2] - t[1], 0.75, 1.3)[0])
        adv = hmtx[name][0]
        spacing.append((t[1] + t[0] - t[2]) / (x0 + adv - x1))
    s_family = statistics.median(scales)
    e_family = (stem_ref - s_family * stem) / 2
    k_spacing = statistics.median(spacing)
    depth_family = statistics.median(ref_glyphs[ord(ch)][3] / ink(glyf, cmap[ord(ch)])[2] for ch in "gjpqy")

    # Snapshot shapes before anything moves (for base-letter matching).
    signatures = {n: contour_signatures(glyf[n]) for n in order if glyf[n].numberOfContours > 0}
    orig_adv = {n: hmtx[n][0] for n in order}

    plans = {}              # glyph -> (s, e, tx): x' = s*x, edges pushed by e, then + tx
    stats = {"fitted": 0, "base": 0, "family": 0, "blank": 0, "clamped": [], "damped": [], "marks_moved": 0,
             "descenders": 0, "clipped_fixed": 0, "framed": 0, "shrunk": 0, "drawn": 0, "widths": 0, "twins": 0, "marks_zeroed": 0, "strays": 0, "repeats": 0, "merged": 0, "boxed": [], "separated": [], "kept": None, "accents_fitted": [], "base_failed": {}, "composed": [], "rejoined": []}

    def letter_marks(name):
        """Contours above / below the letter body (accents, the dot of i)."""
        g = glyf[name]
        parts = []
        coords = list(g.coordinates)
        for start, end in contour_ranges(g):
            parts.append((list(range(start, end + 1)), bounds(coords[start:end + 1])))
        body = [p for p in parts if p[1][2] <= 50]           # contours that reach the baseline
        if not body:
            return [], [], parts
        body_top = max(p[1][3] for p in body)
        upper = [p for p in parts if p[1][2] >= body_top - 10]
        rest = [p for p in parts if p not in upper]
        body_bottom = min(p[1][2] for p in rest if p[1][3] >= 300) if any(p[1][3] >= 300 for p in rest) else None
        lower = [p for p in rest if body_bottom is not None and p[1][3] <= body_bottom + 10 and p[1][3] < -30]
        return upper, lower, parts

    def shift_marks(name, target):
        """Moves accents vertically so the glyph's top/bottom is the reference's."""
        code = target_code.get(name)
        if not in_ranges(code, MARK_SHIFT_RANGES) or len(target) < 5:
            return
        upper, lower, parts = letter_marks(name)
        if not parts:
            return
        g = glyf[name]
        for marks, edge in ((upper, "top"), (lower, "bottom")):
            if not marks or len(marks) == len(parts):
                continue
            others = [p for p in parts if p not in marks]
            if edge == "top":
                mark_edge = max(p[1][3] for p in marks)
                if mark_edge <= max(p[1][3] for p in others):
                    continue
                delta = target[4] - mark_edge
                gap = min(p[1][2] for p in marks) - max(p[1][3] for p in others)
                delta = max(delta, -0.5 * gap) if gap > 0 else max(delta, 0)
            else:
                mark_edge = min(p[1][2] for p in marks)
                if mark_edge >= min(p[1][2] for p in others):
                    continue
                delta = target[3] - mark_edge
                gap = min(p[1][2] for p in others) - max(p[1][3] for p in marks)
                delta = min(delta, 0.5 * gap) if gap > 0 else min(delta, 0)
            if abs(delta) < 8 or abs(delta) > 250:
                continue
            indices = [i for p in marks for i in p[0]]
            map_points(g, lambda x, y, d=delta: (x, y + d), indices)
            stats["marks_moved"] += 1

    descender_maps = {}     # glyph -> (a, y0) of the descender map it got

    def fit_descender(name, target_ymin):
        """Brings the depth of a descender to target_ymin with a map that is
        the identity at the baseline and smooth through it (only y < 0
        moves), so baseline joins and the letter body are untouched."""
        box = ink(glyf, name)
        if box is None:
            return
        y0 = box[2]
        if y0 > -150 or target_ymin > -150 or abs(target_ymin - y0) < 3:
            return
        a = (target_ymin - y0) / -y0
        if abs(a) > 0.25:             # a different design, not a different depth
            return
        map_points(glyf[name], lambda x, y: (x, y + a * y * y / -y0) if y < 0 else (x, y))
        descender_maps[name] = (a, y0)
        stats["descenders"] += 1

    def apply(name, s, e, sy=1.0, ty=0.0):
        g = glyf[name]
        map_points(g, lambda x, y: (x * s, y * sy + ty))
        embolden_x(g, e)

    def translate(name, tx):
        map_points(glyf[name], lambda x, y: (x + tx, y))

    def snapshot(name):
        return list(glyf[name].coordinates)

    def restore(name, coords):
        glyf[name].coordinates = GlyphCoordinates(coords)

    def scale_range(code):
        # DejaVu's Arabic and Hebrew are proportioned unlike the reference's
        # (Tahoma Bold's Hebrew is up to 70% wider): allow them more scaling.
        if in_ranges(code, ARABIC_RANGES):
            return 0.5, 2.0
        if in_ranges(code, HEBREW_RANGES):
            return 0.6, 1.8
        return 0.75, 1.3

    def fit(name, target):
        """Refits a glyph to the reference's ink box."""
        code = target_code.get(name)
        cat = category(code)
        g = glyf[name]
        hmtx[name] = (target[0], 0)
        if len(target) < 5 or g.numberOfContours <= 0:
            stats["blank"] += 1
            plans[name] = (1.0, 0.0, 0.0)
            return
        if cat.startswith("L"):
            shift_marks(name, target)
            fit_descender(name, target[3])
        x0, x1, y0, y1 = ink(glyf, name)
        adv_t, tx0, tx1, ty0, ty1 = target
        lo, hi = scale_range(code)
        sy, ty = 1.0, 0.0
        if not cat.startswith("L") and (abs(ty0 - y0) > 12 or abs(ty1 - y1) > 12) and y1 > y0:
            sy = clamp((ty1 - ty0) / (y1 - y0), 0.8, 1.25)
            ty = (ty0 + ty1) / 2 - sy * (y0 + y1) / 2
        before = snapshot(name)
        for damping in (1.0, 0.5, 0.0):
            restore(name, before)
            s, e = solve(x1 - x0, tx1 - tx0, lo, hi, damping)
            floor = 0.6 if cat.startswith("L") else 0.5
            if s == lo and lo > floor:
                # Still too wide at the usual limit (DejaVu draws some letters
                # with wide accents and some currency signs far wider than the
                # reference): if centring it would push ink into the
                # neighbours past the reference's, condense further.
                nx0 = (tx0 + tx1) / 2 - (s * (x1 - x0) + 2 * e) / 2
                if nx0 < min(tx0, 0) - 40 or nx0 + s * (x1 - x0) + 2 * e > max(tx1, adv_t) + 40:
                    s, e = solve(x1 - x0, tx1 - tx0, floor, hi, damping)
            if cat == "Mn" and g.numberOfContours == 1 and s < 0.7:
                # A one-piece mark narrowed this far (the arrows below) fills
                # in between its parts if its strokes keep their thickness:
                # scale it plainly, as a smaller copy.
                s, e = clamp((tx1 - tx0) / (x1 - x0), floor, hi), 0.0
            apply(name, s, e, sy, ty)
            if not damaged(before, g):
                break
            if damping == 1.0 and separate_small_parts(before, g) and not damaged(before, g):
                stats["separated"].append(name)
                break
            stats["damped"].append(f"{code:04X}" if code is not None else name)
        if s in (lo, hi):
            stats["clamped"].append(f"{code:04X}" if code is not None else name)
        nx0, nx1, _, _ = ink(glyf, name)
        tx = round((tx0 + tx1) / 2 - (nx0 + nx1) / 2)      # whole units: rounding stays as checked
        translate(name, tx)
        plans[name] = (s, e, tx)
        stats["fitted"] += 1
        if not cat.startswith("L"):
            box_refit(name, target, source=before)

    def separate_small_parts(before, g, step=8, most=120, margin=30):
        """The stroke push can run a stroke into a dot or small mark beside
        it (the small v under Bold reh with v). Rather than weaken the push,
        each small part that newly touches a larger one is moved away from
        it (up, down or sideways, whichever way it already lies) or, if that
        would take a longer move, made slightly smaller about its centre
        (to 75% at most), until there is `margin` units of space around it.
        True if every such overlap was cleared."""
        pairs = overlapping_pairs(before, g)
        if not pairs:
            return False
        ranges = list(contour_ranges(g))
        flags = list(g.flags)
        coords = list(g.coordinates)
        def path_of(k, pts):
            a, b = ranges[k]
            return _contour_path(pts[a:b + 1], [bool(f & 1) for f in flags[a:b + 1]])
        def box(k, pts):
            a, b = ranges[k]
            xs = [pts[i][0] for i in range(a, b + 1)]
            ys = [pts[i][1] for i in range(a, b + 1)]
            return min(xs), max(xs), min(ys), max(ys)
        def clear(k, pts):
            """No other contour within `margin` of contour k (k grown by the
            margin about its centre)."""
            x0, x1, y0, y1 = box(k, pts)
            cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
            fx = 1 + 2 * margin / max(x1 - x0, 1)
            fy = 1 + 2 * margin / max(y1 - y0, 1)
            a, b = ranges[k]
            grown = list(pts)
            for i in range(a, b + 1):
                grown[i] = (cx + (pts[i][0] - cx) * fx, cy + (pts[i][1] - cy) * fy)
            mine = path_of(k, grown)
            for other in range(len(ranges)):
                if other != k and abs(pathops.op(mine, path_of(other, pts), pathops.PathOp.INTERSECTION, fix_winding=True).area) > 1:
                    return False
            return True
        moving = {}
        for i, j in pairs:
            small, big = (i, j) if abs(path_of(i, coords).area) < abs(path_of(j, coords).area) else (j, i)
            if abs(path_of(small, coords).area) > 0.25 * abs(path_of(big, coords).area):
                return False
            sb, bb = box(small, coords), box(big, coords)
            sx, sy = (sb[0] + sb[1]) / 2, (sb[2] + sb[3]) / 2
            bx, by = (bb[0] + bb[1]) / 2, (bb[2] + bb[3]) / 2
            moving[small] = [(0, 1 if sy > by else -1), (1 if sx > bx else -1, 0)]
        for k, directions in moving.items():
            a, b = ranges[k]
            original = list(coords)
            options = []
            for dx, dy in directions:
                for shift in range(step, most + step, step):
                    trial = list(original)
                    for i in range(a, b + 1):
                        trial[i] = (original[i][0] + dx * shift, original[i][1] + dy * shift)
                    if clear(k, trial):
                        options.append((shift, trial))
                        break
            x0, x1, y0, y1 = box(k, original)
            cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
            for f in (0.95, 0.9, 0.85, 0.8, 0.75):
                trial = list(original)
                for i in range(a, b + 1):
                    trial[i] = (cx + (original[i][0] - cx) * f, cy + (original[i][1] - cy) * f)
                if clear(k, trial):
                    options.append(((1 - f) * max(x1 - x0, y1 - y0), trial))
                    break
            if not options:
                g.coordinates = GlyphCoordinates(coords)
                return False
            coords = min(options, key=lambda o: o[0])[1]
        g.coordinates = GlyphCoordinates(coords)
        return not overlapping_pairs(before, g)

    def box_refit(name, target, off=60, source=None):
        """Simple shapes the scaling limits keep far from the reference's
        size (DejaVu's small squares are half again as large, its bullet
        operator twice as wide): a filled shape is mapped onto the
        reference's ink box; an outlined one (a ring: one contour inside the
        other) has its outer contour mapped onto the box and its inner one
        onto the box less the stroke, so the stroke keeps its thickness.
        A symbol drawn as a ring of even thickness (the white squares and
        the white bullet) is always redrawn so, with the stroke it had in
        `source` (its outline before fitting): the stroke push meant for
        letters had thinned the sides of Bold's small white square to 20
        units against 52 at the top."""
        g = glyf[name]
        if g.numberOfContours not in (1, 2):
            return
        if in_ranges(target_code.get(name), ((0x0600, 0x0780), (0xFB50, 0xFE00), (0xFE70, 0xFF00))):
            return       # Arabic digits and punctuation are other shapes in DejaVu (a square zero for a diamond)
        _, tx0, tx1, ty0, ty1 = target
        x0, x1, y0, y1 = ink(glyf, name)
        ranges = list(contour_ranges(g))
        coords = list(g.coordinates)
        def boxes_of(points):
            return [(min(c[0] for c in points[a:b + 1]), max(c[0] for c in points[a:b + 1]),
                     min(c[1] for c in points[a:b + 1]), max(c[1] for c in points[a:b + 1])) for a, b in ranges]
        boxes = boxes_of(coords)
        even = None                 # the stroke of a ring of even thickness, as drawn
        if len(ranges) == 2 and source is not None and category(target_code.get(name)).startswith("S"):
            sb = boxes_of(source)
            o_, i_ = (0, 1) if sb[0][1] - sb[0][0] >= sb[1][1] - sb[1][0] else (1, 0)
            so, si = sb[o_], sb[i_]
            def fill(k, box):
                # how much of its box a contour covers (a square 1, a circle
                # 0.79): rings are plain squares or circles inside each other,
                # not the currency sign, whose spokes stick out of its ring
                pts = source[ranges[k][0]:ranges[k][1] + 1]
                a = abs(sum(pts[j][0] * pts[(j + 1) % len(pts)][1] - pts[(j + 1) % len(pts)][0] * pts[j][1]
                            for j in range(len(pts)))) / 2
                return a / max((box[1] - box[0]) * (box[3] - box[2]), 1)
            if (so[0] < si[0] and si[1] < so[1] and so[2] < si[2] and si[3] < so[3]
                    and fill(o_, so) >= 0.75 and abs(fill(o_, so) - fill(i_, si)) <= 0.1):
                sides = (si[0] - so[0], so[1] - si[1], si[2] - so[2], so[3] - si[3])
                if max(sides) <= 1.15 * min(sides):
                    scale = ((tx1 - tx0) / (so[1] - so[0]) + (ty1 - ty0) / (so[3] - so[2])) / 2
                    even = sum(sides) / 4 * scale
        if (even is None and max(abs(x0 - tx0), abs(x1 - tx1), abs(y0 - ty0), abs(y1 - ty1)) <= off) or x1 <= x0 or y1 <= y0:
            return
        def mapper(src, dst):
            sx = (dst[1] - dst[0]) / (src[1] - src[0])
            sy = (dst[3] - dst[2]) / (src[3] - src[2])
            return lambda x, y: (dst[0] + (x - src[0]) * sx, dst[2] + (y - src[2]) * sy), sx, sy
        maps = []
        outer = (x0, x1, y0, y1)
        dst = (tx0, tx1, ty0, ty1)
        if len(ranges) == 1:
            maps.append((ranges[0], mapper(outer, dst)))
        else:
            o, i = (0, 1) if boxes[0][1] - boxes[0][0] >= boxes[1][1] - boxes[1][0] else (1, 0)
            bo, bi = boxes[o], boxes[i]
            if not (bo[0] < bi[0] and bi[1] < bo[1] and bo[2] < bi[2] and bi[3] < bo[3]):
                return                                  # two separate shapes: leave them
            # The stroke push thickened the sides only: give all four sides
            # the same stroke (the average of the sides' and the top's).
            sx_, sy_ = ((bi[0] - bo[0]) + (bo[1] - bi[1])) / 2, ((bi[2] - bo[2]) + (bo[3] - bi[3])) / 2
            t = (sx_ + sy_) / 2 if even is None else even
            inner_dst = (tx0 + t, tx1 - t, ty0 + t, ty1 - t)
            if inner_dst[1] - inner_dst[0] < 0.2 * (tx1 - tx0) or inner_dst[3] - inner_dst[2] < 0.2 * (ty1 - ty0):
                return
            maps.append((ranges[o], mapper(bo, dst)))
            maps.append((ranges[i], mapper(bi, inner_dst)))
        if any(not 0.3 <= f <= 3.0 for _, (_, sx, sy) in maps for f in (sx, sy)):
            return
        before = snapshot(name)
        for (a, b), (fn, _, _) in maps:
            for k in range(a, b + 1):
                coords[k] = fn(*coords[k])
        g.coordinates = GlyphCoordinates(coords)
        if damaged(before, g):
            restore(name, before)
            return
        stats["boxed"].append(name)

    def family_condense(name):
        """Glyphs the reference lacks: family-wide condensation and spacing."""
        g = glyf[name]
        adv = orig_adv[name]
        if g.numberOfContours <= 0:
            hmtx[name] = (round(adv * s_family), 0)
            plans[name] = (1.0, 0.0, 0.0)
            return
        x0, x1, y0, _ = ink(glyf, name)
        if y0 < -150 and category(code_of.get(name)).startswith("L"):
            fit_descender(name, y0 * depth_family)
        before = snapshot(name)
        s, e = s_family, e_family
        apply(name, s, e)
        if damaged(before, g):           # same ink width by plain scaling instead
            restore(name, before)
            s, e = s_family + 2 * e_family / max(x1 - x0, 1), 0.0
            apply(name, s, e)
            stats["damped"].append(name)
        nx0, nx1, _, _ = ink(glyf, name)
        if adv == 0:          # combining marks: keep their place relative to the origin
            tx = round(s_family * (x0 + x1) / 2 - (nx0 + nx1) / 2)
            translate(name, tx)
            hmtx[name] = (0, 0)
        else:
            lsb, rsb = x0, adv - x1
            tx = round(k_spacing * lsb - nx0)
            translate(name, tx)
            hmtx[name] = (max(0, round(k_spacing * lsb + (nx1 - nx0) + k_spacing * rsb)), 0)
        plans[name] = (s, e, tx)
        stats["family"] += 1

    def base_of(name):
        """The glyph whose transform an accented letter (or a symbol with an
        overlay mark, like the negated relations) reuses."""
        code = code_of.get(name)
        if code is None:
            return None
        if code in DOTLESS:
            base = DOTLESS[code]
        else:
            nfd = unicodedata.normalize("NFD", chr(code))
            if len(nfd) < 2 or not all(unicodedata.category(c).startswith("M") for c in nfd[1:]):
                return None
            base = DOTLESS.get(ord(nfd[0]), ord(nfd[0]))
        letters = category(base).startswith("L") and category(code).startswith("L")
        if not letters and composed_info(name) is None:
            return None
        return cmap.get(base)

    def composed_info(name):
        """For a precomposed character the reference lacks but whose base and
        marks it has, how the reference sets it: shaping engines decompose a
        character the font lacks and recompose as far as the font allows (so
        u-diaeresis-macron becomes u-diaeresis + macron, alpha-oxia becomes
        alpha-tonos). Returns (the code point the reference ends up with,
        whether marks are left over after it, its width). Leftover combining
        marks take no width (the shaper zeroes them after a base, even where
        the reference gives a mark an advance). Shaping engines compose
        base + mark into a precomposed glyph when the font has one, so that
        glyph must be exactly this wide."""
        code = code_of.get(name)
        if code is None or code in ref_glyphs:
            return None
        nfd = unicodedata.normalize("NFD", chr(code))
        if len(nfd) == 1 and nfd != chr(code) and ord(nfd) in ref_glyphs:
            return ord(nfd), False, ref_glyphs[ord(nfd)][0]      # a singleton (Kelvin sign = K)
        if len(nfd) < 2 or not all(ord(c) in ref_glyphs for c in nfd):
            return None
        if not all(unicodedata.category(c) == "Mn" for c in nfd[1:]):
            return None
        current, left = nfd[0], []
        for mark in nfd[1:]:
            ccc = unicodedata.combining(mark)
            blocked = any(unicodedata.combining(m) in (0,) or unicodedata.combining(m) >= ccc for m in left)
            composed = unicodedata.normalize("NFC", current + mark)
            if not blocked and len(composed) == 1 and ord(composed) in ref_glyphs:
                current = composed
            else:
                left.append(mark)
        return ord(current), bool(left), ref_glyphs[ord(current)][0]

    merge_marks = set()

    def clear_side_accents(g, marks, gap=40, least=0.55, furthest=400, lo=None, hi=None):
        """Accents standing to one side of the letter (wholly left or right
        of its middle, or starting beyond the letter's edge at their height
        with their centre on that side, as the breathing and accent over
        Greek capital alpha) are narrowed from their outer edge so they end
        `gap` units short of the letter at their own height; where narrowing
        to `least` isn't enough, they also move outward (up to `furthest`,
        and never past `lo` / `hi`, where the neighbouring letters are: the
        gap is smaller then)."""
        coords = list(g.coordinates)
        flags = list(g.flags)
        idx = {i for m in marks for i in m}
        body = [coords[i] for i in range(len(coords)) if i not in idx]
        if not body:
            return
        mx = [coords[i][0] for i in idx]
        my = [coords[i][1] for i in idx]
        m0, m1, y0, y1 = min(mx), max(mx), min(my), max(my)
        centre = (min(p[0] for p in body) + max(p[0] for p in body)) / 2
        # The letter's outline within the accents' height (plus the gap).
        letter = pathops.Path()
        for a, b in contour_ranges(g):
            if a not in idx:
                letter = pathops.op(letter, _contour_path(coords[a:b + 1], [bool(f & 1) for f in flags[a:b + 1]]),
                                    pathops.PathOp.UNION, fix_winding=True)
        band = pathops.Path()
        bp = band.getPen()
        bp.moveTo((m0 - 4000, y0 - gap)); bp.lineTo((m1 + 4000, y0 - gap)); bp.lineTo((m1 + 4000, y1 + gap)); bp.lineTo((m0 - 4000, y1 + gap)); bp.closePath()
        beside = pathops.op(letter, band, pathops.PathOp.INTERSECTION, fix_winding=True)
        if beside.area == 0 or m1 <= m0:
            return
        bx0, _, bx1, _ = beside.bounds
        mid = (m0 + m1) / 2
        if m1 <= centre or (mid < centre and m0 < bx0):      # accents on the left
            limit = bx0 - gap
            if m1 <= limit:
                return
            f = (limit - m0) / (m1 - m0)
            anchor = m0
            outward = -1
        elif m0 >= centre or (mid > centre and m1 > bx1):    # on the right
            limit = bx1 + gap
            if m0 >= limit:
                return
            f = (m1 - limit) / (m1 - m0)
            anchor = m1
            outward = 1
        else:
            return
        shift = 0.0
        if f < least:
            # narrowed as far as it goes, and moved out the rest of the way
            inner = anchor + least * ((m1 if outward < 0 else m0) - anchor)
            shift = limit - inner
            if abs(shift) > furthest:
                return
            if outward < 0 and lo is not None:
                shift = min(0.0, max(shift, lo - m0))
            if outward > 0 and hi is not None:
                shift = max(0.0, min(shift, hi - m1))
            f = least
        for i in idx:
            coords[i] = (anchor + f * (coords[i][0] - anchor) + shift, coords[i][1])
        g.coordinates = GlyphCoordinates(coords)

    def respace_marks(g, before, marks, s):
        """The stroke push widens each dot of a diaeresis (or each part of
        any accent made of side-by-side pieces) and so eats the space
        between them: in Bold the dots of A-diaeresis came out 106 units
        apart where plain scaling gives about 200, and merge at 11-13 px.
        Pieces standing side by side get their gap back, in proportion to
        the (pushed, heavier) pieces, centred where they were."""
        if len(marks) < 2:
            return
        coords = list(g.coordinates)
        def box(points, m):
            xs = [points[i][0] for i in m]
            ys = [points[i][1] for i in m]
            return min(xs), max(xs), min(ys), max(ys)
        now = [box(coords, m) for m in marks]
        was = [box(before, m) for m in marks]
        # Rows: pieces overlapping vertically by at least half the smaller one.
        rows, seen = [], set()
        for i in range(len(marks)):
            if i in seen:
                continue
            row = [i]
            seen.add(i)
            for j in range(len(marks)):
                if j not in seen:
                    a, b = was[i], was[j]
                    if min(a[3], b[3]) - max(a[2], b[2]) > 0.5 * min(a[3] - a[2], b[3] - b[2]):
                        row.append(j)
                        seen.add(j)
            if len(row) > 1:
                rows.append(sorted(row, key=lambda k: was[k][0]))
        for row in rows:
            # Only rows of separate pieces (each gap at least 40 units before).
            gaps = [was[b][0] - was[a][1] for a, b in zip(row, row[1:])]
            if min(gaps) <= 0:
                continue
            centre = (now[row[0]][0] + now[row[-1]][1]) / 2
            x, lefts = 0.0, []
            for k, idx in enumerate(row):
                if k:
                    a, b = row[k - 1], row[k]
                    # The gap keeps its proportion to the pieces beside it
                    # (they were made heavier, so it grows with them), and
                    # never ends up narrower than plain scaling would leave it.
                    widths_was = (was[a][1] - was[a][0] + was[b][1] - was[b][0]) / 2
                    widths_now = (now[a][1] - now[a][0] + now[b][1] - now[b][0]) / 2
                    proportional = gaps[k - 1] / widths_was * widths_now if widths_was > 0 else 0
                    x += max(s * gaps[k - 1], proportional, now[b][0] - now[a][1])
                lefts.append(x)
                x += now[idx][1] - now[idx][0]
            offset = centre - x / 2
            for idx, left in zip(row, lefts):
                shift = offset + left - now[idx][0]
                for i in marks[idx]:
                    coords[i] = (coords[i][0] + shift, coords[i][1])
        g.coordinates = GlyphCoordinates(coords)

    def body_band(g, in_marks, y0, y1):
        """The x extent of the letter body (the points not in `in_marks`)
        between heights y0 and y1, or None if it has no ink there."""
        coords, flags = list(g.coordinates), list(g.flags)
        body = pathops.Path()
        for a, b in contour_ranges(g):
            if a not in in_marks:
                body = pathops.op(body, _contour_path(coords[a:b + 1], [bool(f & 1) for f in flags[a:b + 1]]),
                                  pathops.PathOp.UNION, fix_winding=True)
        band = pathops.Path()
        pen = band.getPen()
        pen.moveTo((-5000, y0)); pen.lineTo((5000, y0)); pen.lineTo((5000, y1)); pen.lineTo((-5000, y1)); pen.closePath()
        cut = pathops.op(body, band, pathops.PathOp.INTERSECTION, fix_winding=True)
        if abs(cut.area) < 1:
            return None
        return cut.bounds[0], cut.bounds[2]

    def respace_stacked(g, before, marks, s):
        """Accent pieces stacked at an angle (the acute or hook beside the
        circumflex of Vietnamese letters) are not side by side, so
        respace_marks leaves them; the stroke push eats the space between
        them all the same (Bold a-circumflex-acute: 41 units became 11).
        The upper piece moves away sideways until the gap is what plain
        scaling would leave (at most 80 units)."""
        if len(marks) < 2:
            return
        coords, flags = list(g.coordinates), list(g.flags)
        def outline(points, m):
            # the contour as a dense polyline (quadratic curves flattened)
            pts = [points[k] for k in m]
            on = [bool(flags[k] & 1) for k in m]
            path = _contour_path(pts, on)
            out, cur = [], None
            for verb, args in path:
                for q in args:
                    if cur is not None:
                        n = max(1, int(math.hypot(q[0] - cur[0], q[1] - cur[1]) / 6))
                        out += [(cur[0] + (q[0] - cur[0]) * t / n, cur[1] + (q[1] - cur[1]) * t / n) for t in range(1, n + 1)]
                    cur = q
            return out or pts
        def gap(pa, pb):
            return min(math.hypot(x0 - x1, y0 - y1) for x0, y0 in pa for x1, y1 in pb)
        def shape(points, m):
            return outline(points, m)
        for i in range(len(marks)):
            for j in range(len(marks)):
                if i == j:
                    continue
                a, b = marks[i], marks[j]        # b: the upper piece, the one that moves
                ya = sum(before[k][1] for k in a) / len(a)
                yb = sum(before[k][1] for k in b) / len(b)
                if yb <= ya:
                    continue
                box = lambda pts, m: (min(pts[k][0] for k in m), max(pts[k][0] for k in m),
                                      min(pts[k][1] for k in m), max(pts[k][1] for k in m))
                A, B = box(before, a), box(before, b)
                if A[3] < B[2] or B[3] < A[2]:
                    continue                      # one wholly above the other: not side by side at all
                was = gap(shape(before, a), shape(before, b))
                if was < 30 or was > 200:
                    continue
                want = s * was
                now = gap(shape(coords, a), shape(coords, b))
                if now >= 0.8 * want:
                    continue
                side = 1 if (A[0] + A[1]) < (B[0] + B[1]) else -1
                moved = 0
                while moved < 80:
                    moved += 4
                    trial = [(x + side * moved, y) if k in b else (x, y) for k, (x, y) in enumerate(coords)]
                    if gap(shape(coords, a), shape(trial, b)) >= 0.9 * want:
                        break
                for k in b:
                    coords[k] = (coords[k][0] + side * moved, coords[k][1])
                stats["stacked_respaced"] = stats.get("stacked_respaced", 0) + 1
        g.coordinates = GlyphCoordinates(coords)

    def level_with(pts, marks, chosen):
        """The marks in `chosen` (indices into marks, lists of point indices)
        and every mark level with one of them, however far it reaches."""
        boxes = [(min(pts[i][1] for i in m), max(pts[i][1] for i in m)) for m in marks]
        chosen = set(chosen)
        grown = True
        while grown:
            grown = False
            for k, (y0, y1) in enumerate(boxes):
                if k not in chosen and any(y0 < boxes[j][1] and boxes[j][0] < y1 for j in chosen):
                    chosen.add(k)
                    grown = True
        return chosen

    def via_base(name, base, slack=0):
        """Applies the base letter's transform; True if the base body was
        found and the result neither damages the outline nor pushes an
        accent into the neighbouring letters further than the reference.
        The body gets exactly the base letter's outline (and descender);
        where the reference makes the accented letter wider or narrower
        than its base (d-caron, Greek capitals with tonos), the body keeps
        its left side bearing, or its right one if the accent is on the
        left."""
        if base not in plans or base not in signatures or name not in signatures:
            stats["base_failed"][name] = "no base"
            return False
        s, e, tx_base = plans[base]
        key, bx0, _ = max(signatures[base], key=lambda c: c[2])
        offsets = [x0 - bx0 for k, x0, _ in signatures[name] if k == key]
        if not offsets:
            stats["base_failed"][name] = "body not found"
            return False
        dx = min(offsets, key=abs)
        # The body: the contours that are the base letter's, where the base
        # has them relative to each other. The rest are the marks.
        placed = {(k, round(x0 - bx0)) for k, x0, _ in signatures[base]}
        g = glyf[name]
        mark_ids = [c for c, ((start, end), (k, x0, _)) in enumerate(zip(contour_ranges(g), signatures[name]))
                    if (k, round(x0 - dx - bx0)) not in placed]
        ranges_now = list(contour_ranges(g))
        marks = [range(ranges_now[c][0], ranges_now[c][1] + 1) for c in mark_ids]
        original = snapshot(name)
        if name in targets:
            shift_marks(name, targets[name])
        if base in descender_maps:
            a, y0 = descender_maps[base]
            body = [i for start, end in contour_ranges(g) for i in range(start, end + 1)
                    if not any(i in m for m in marks)]
            map_points(g, lambda x, y: (x, y + a * y * y / -y0) if y < 0 else (x, y), body)
        before = snapshot(name)
        apply(name, s, e)
        tx = tx_base - s * dx
        translate(name, tx)
        respace_marks(g, before, marks, s)
        respace_stacked(g, before, marks, s)
        if name in targets:
            adv, lim0, lim1 = targets[name][0], targets[name][1], targets[name][2]
            extra = adv - hmtx[base][0]
            if extra and marks:
                # The extra width is for the accent. Where it is at the top
                # left (Greek capitals with tonos or breathings) the body
                # keeps its right side bearing, otherwise (d-caron,
                # r-cedilla) its left one.
                pts = list(g.coordinates)
                in_marks = {i for m in marks for i in m}
                body_pts = [pts[i] for i in range(len(pts)) if i not in in_marks]
                bx = (min(p[0] for p in body_pts) + max(p[0] for p in body_pts)) / 2
                by = (min(p[1] for p in body_pts) + max(p[1] for p in body_pts)) / 2
                top_left = all(max(pts[i][0] for i in m) <= bx and min(pts[i][1] for i in m) >= by for m in marks)
                if dx > 50 or top_left:
                    translate(name, extra)
                    tx += extra
        else:
            adv = hmtx[base][0]
            lim0, lim1, _, _ = ink(glyf, base)
        # Ink may reach past the advance only as far as the reference's does
        # (or the base letter's own, as Taquoma draws it): accents reaching
        # further run into the neighbouring letters (i-grave next to
        # i-diaeresis, a quote before i-circumflex) where the reference's
        # don't. Within the advance there is no limit. Where the accents
        # can't be brought in that far, `slack` more is allowed (see
        # body_first).
        pts = list(g.coordinates)
        in_marks = {i for m in marks for i in m}
        body_x = [pts[i][0] for i in range(len(pts)) if i not in in_marks] or [0]
        lo, hi = min(lim0, 0, min(body_x)) - slack, max(lim1, adv, max(body_x)) + slack
        # Accents beside a capital at the start of a word (Greek breathings
        # and accents) may reach up to 40 units further left rather than
        # crowd the letter: what is left of them is the space before the word.
        side_lo = min(lim0, 0, min(body_x)) - 40
        nx0, nx1, _, _ = ink(glyf, name)
        if (nx0 < lo or nx1 > hi) and marks:
            # DejaVu's accents are wider or further out than the reference's:
            # keep the body where the base letter has it and bring the
            # accents in (narrower if they must be, then sideways). Only the
            # accents that reach too far move, with those level with them
            # (the other dot of a diaeresis): an iota subscript under Greek
            # capital eta stays where it is when the breathing and accent
            # beside the letter are brought in.
            pts = list(g.coordinates)
            chosen = level_with(pts, marks, {k for k, m in enumerate(marks)
                                             if min(pts[i][0] for i in m) < lo or max(pts[i][0] for i in m) > hi})
            idx = [i for k in sorted(chosen) for i in marks[k]] or [i for m in marks for i in m]
            xs = [g.coordinates[i][0] for i in idx]
            m0, m1 = min(xs), max(xs)
            f = min(1.0, (hi - lo) / max(m1 - m0, 1))
            c = (m0 + m1) / 2
            shift = max(lo - (c - f * (c - m0)), 0) + min(hi - (c + f * (m1 - c)), 0)
            # Accents above or below may move sideways by 0.6 of their width;
            # marks beside the letter at its own height (the dagesh beside
            # vav and yod) as far as keeps them 40 units clear of it.
            room = 0.6 * (m1 - m0)
            ys = [g.coordinates[i][1] for i in idx]
            band = body_band(g, in_marks, min(ys), max(ys))
            if band is not None:
                if shift > 0 and c + f * (m1 - c) < band[0]:
                    room = max(room, band[0] - 40 - (c + f * (m1 - c)))
                if shift < 0 and c - f * (c - m0) > band[1]:
                    room = max(room, (c - f * (c - m0)) - (band[1] + 40))
            fits = f >= 0.7 and abs(shift) <= room
            if (not fits and band is not None and shift > 0 and m1 < band[0] and name in targets
                    and lim1 > max(body_x)):
                # A mark beside the letter on its left, with no room for it
                # between the reference's left edge and the letter (DejaVu's
                # dagesh beside vav and yod is wide; the reference's is
                # small and its vav narrow at the foot): the letter moves
                # right, as far as the reference's ink reaches, and the mark
                # takes the space left of it, 40 units clear.
                move = float(math.floor(min(max(0.0, lo + (m1 - m0) - (band[0] - 40)), lim1 - max(body_x))))
                f = min(1.0, (band[0] + move - 40 - lo) / max(m1 - m0, 1))
                if f >= 0.7:
                    body_idx = [i for i in range(len(g.coordinates)) if i not in in_marks]
                    map_points(g, lambda x, y: (x + move, y), body_idx)
                    tx += move
                    c, shift, fits = m0, lo - m0, True      # marks: x -> lo + f * (x - m0)
            if fits:
                map_points(g, lambda x, y: (round(c + f * (x - c) + shift), y), idx)
                stats["accents_fitted"].append(name)
            elif os.environ.get("TAQUOMA_DEBUG"):
                print(f"  accents not fitted: {name} marks {m0:.0f}..{m1:.0f} f {f:.2f} shift {shift:.0f} room {room:.0f} band {band}")
            nx0, nx1, _, _ = ink(glyf, name)
            nudge = max(lo - nx0, 0) + min(hi - nx1, 0)        # rounding
            if name in stats["accents_fitted"] and 0 < abs(nudge) <= 2:
                map_points(g, lambda x, y: (x + math.copysign(math.ceil(abs(nudge)), nudge), y), idx)
                nx0, nx1, _, _ = ink(glyf, name)
        # Accents brought in beside the letter (the breathings and accents
        # of Greek capitals) may now run into it: narrow them, from their
        # outer edge, to clear the letter where they stand.
        in_marks = set(mark_ids)
        hit = {c for a, b in overlapping_pairs(before, g) if (a in in_marks) != (b in in_marks) for c in (a, b) if c in in_marks}
        if marks and hit:
            # only the accents that ran into the letter, with those level
            # with them (not an iota subscript under the letter)
            side = level_with(list(g.coordinates), marks, {k for k, c in enumerate(mark_ids) if c in hit})
            clear_side_accents(g, [marks[k] for k in sorted(side)], lo=min(lo, side_lo), hi=hi)
            nx0, nx1, _, _ = ink(glyf, name)
            lo = min(lo, side_lo)
        # Accents beside the letter, at its own height, that come close to
        # it without touching (the breathing and accent of Greek capital
        # alpha came within 6 units of its apex) are cleared the same way.
        # (Not marks drawn joined to the letter: the ogonek and the horn.)
        if marks:
            pts_now = list(g.coordinates)
            mark_pts = {i for m in marks for i in m}
            body_y = [pts_now[i][1] for i in range(len(pts_now)) if i not in mark_pts]
            flags_ = list(g.flags)
            body_lines = [_polyline(before[a:b + 1], [bool(f_ & 1) for f_ in flags_[a:b + 1]])
                          for a, b in contour_ranges(g) if a not in mark_pts]
            beside = set()
            for k, m in enumerate(marks):
                drawn = _polyline([before[i] for i in m], [bool(flags_[i] & 1) for i in m])
                if any(_distance(drawn, line) <= 4 for line in body_lines):
                    continue                      # joined to the letter (or touching it) as drawn

                xs_ = [pts_now[i][0] for i in m]
                ys_ = [pts_now[i][1] for i in m]
                if not body_y or min(ys_) >= max(body_y) or max(ys_) <= min(body_y):
                    continue
                band = body_band(g, mark_pts, min(ys_), max(ys_))
                if band is None:
                    continue
                mid, centre_ = (min(xs_) + max(xs_)) / 2, (band[0] + band[1]) / 2
                if (mid < centre_ and min(xs_) < band[0]) or (mid > centre_ and max(xs_) > band[1]):
                    beside.add(k)
            if beside:
                group = level_with(pts_now, marks, beside)
                clear_side_accents(g, [marks[k] for k in sorted(group)], lo=min(lo, side_lo), hi=hi)
                nx0, nx1, _, _ = ink(glyf, name)
                lo = min(lo, side_lo)
        # (Gaps between accent pieces are kept by respace_marks; accents
        # moved in towards the letter on purpose are not damage; accent
        # pieces that now touch each other are merged into one outline at
        # the end.)
        both_marks = lambda a, b: a in in_marks and b in in_marks
        bad = damaged(before, glyf[name], gaps=False, allowed=both_marks)
        if bad or nx0 < lo - 2 or nx1 > hi + 2:
            if name in stats["accents_fitted"]:
                stats["accents_fitted"].remove(name)
            stats["base_failed"][name] = "damaged" if bad else f"ink {nx0:.0f}..{nx1:.0f} outside {lo}..{hi}"
            restore(name, original)
            return False
        if overlapping_pairs(before, g) or name in rejoined:
            merge_marks.add(name)
        if rejoined.pop(name, None) is not None:
            stats["rejoined"].append(name)
        plans[name] = (s, e, tx)
        stats["base"] += 1
        return True

    def body_first(name, base):
        """The base letter's body with the accents kept within the
        reference's reach; failing that, with the accents reaching up to 40
        units further (DejaVu's double grave over i, the breathing and
        accent beside Greek capital omega) rather than a body fitted out of
        shape."""
        return via_base(name, base) or via_base(name, base, slack=40)

    def centred_on_base(name, base, advance):
        """Fallback for a precomposed letter whose base body could not be
        reused as is: the base's scale and push (or plain scaling if that
        damages it), centred where the base letter's ink sits."""
        s, e, _ = plans[base]
        x0, x1, _, _ = ink(glyf, name)
        before = snapshot(name)
        apply(name, s, e)
        if damaged(before, glyf[name]):
            restore(name, before)
            s, e = s + 2 * e / max(x1 - x0, 1), 0.0
            apply(name, s, e)
        bx0, bx1, _, _ = ink(glyf, base)
        nx0, nx1, _, _ = ink(glyf, name)
        tx = round((bx0 + bx1) / 2 - (nx0 + nx1) / 2)
        translate(name, tx)
        plans[name] = (s, e, tx)
        hmtx[name] = (advance, 0)
        stats["base"] += 1

    def family_ok(code):
        """Letters, marks, digits and punctuation outside Arabic follow the family's condensation."""
        if code is None or in_ranges(code, ARABIC_RANGES):
            return False
        cat = category(code)
        return cat[0] in "LMNP" or cat in ("Sk", "Sc")

    def unjoin(name):
        """A letter put back together from its base and an overlapping mark
        whose body could not be reused after all goes back to its merged
        outline (as drawn) before it is fitted some other way."""
        if name in rejoined:
            glyf[name] = rejoined.pop(name)

    # Pass 1: glyphs without a base letter. Pass 2: accented letters.
    deferred = []
    for name in order:
        base = base_of(name)
        if base is not None and base != name:
            deferred.append((name, base))
            continue
        unjoin(name)
        if name in targets:
            fit(name, targets[name])
        elif family_ok(code_of.get(name)):
            family_condense(name)
    for name, base in deferred:
        if name in targets:
            if not (base in targets and body_first(name, base)):
                unjoin(name)
                fit(name, targets[name])
            continue
        info = composed_info(name)
        composed = info[2] if info else None
        if composed is not None and base in plans:
            if body_first(name, base):
                hmtx[name] = (composed, 0)
            else:
                unjoin(name)
                centred_on_base(name, base, composed)
        elif orig_adv[name] == orig_adv[base] and body_first(name, base):
            hmtx[name] = (hmtx[base][0], 0)
        else:
            unjoin(name)
            if family_ok(code_of.get(name)):
                family_condense(name)
    for name in list(rejoined):          # never reached pass 2
        unjoin(name)

    # The crossbar of f ends at the advance. Fitted to the reference's ink
    # box (which its hook sets), Fauxdana's longer crossbar ran 25 units
    # (Bold 43) into the next letter's space and touched the arms of v, w,
    # x, y and the crossbars of t and f, which stay clear in the reference.
    xh = ref_glyphs[ord("x")][4]
    for code in (0x0066, 0x1E1F):
        name = cmap.get(code)
        if name is None or glyf[name].numberOfContours <= 0:
            continue
        g, adv = glyf[name], hmtx[cmap[0x0066]][0]          # f-dot's width is f's (set later)
        coords = list(g.coordinates)
        bar = [i for i, (x, y) in enumerate(coords) if x > adv and xh - 400 < y <= xh + 20]
        if 2 <= len(bar) <= 4:
            for i in bar:
                coords[i] = (adv, coords[i][1])
            before = list(g.coordinates)
            g.coordinates = GlyphCoordinates(coords)
            if damaged(before, g):
                g.coordinates = GlyphCoordinates(before)
            else:
                stats["f_bar"] = stats.get("f_bar", 0) + 1

    # Pass 3: letters made of whole letters (IJ, ij, the Yiddish double vav
    # and yod ligatures) are those letters as Taquoma has them, one advance
    # apart as the reference sets them, centred on the reference's ink. Fitted
    # as one wide glyph they would get other proportions and, being narrow
    # strokes far apart, much heavier stems than the letters themselves.
    def compose_from_parts(name, parts):
        adv_t, tx0, tx1 = targets[name][:3]
        lo, hi = min(tx0, 0) - 40, max(tx1, adv_t) + 40
        offsets, x = [], 0
        for leaf in parts:
            offsets.append(x)
            x += targets[leaf][0] if leaf in targets else hmtx[leaf][0]
        spans = []
        for leaf, o in zip(parts, offsets):
            lx0, lx1, _, _ = ink(glyf, leaf)
            spans.append([lx0 + o, lx1 + o])
        width = spans[-1][1] - spans[0][0]
        if width > hi - lo:
            # Close the gaps, keeping at least 40% of each.
            excess = width - (hi - lo)
            gaps = [spans[i + 1][0] - spans[i][1] for i in range(len(spans) - 1)]
            room = sum(max(0.6 * g, 0) for g in gaps)
            if excess > room:
                return False
            moved = 0
            for i, g in enumerate(gaps):
                moved += max(0.6 * g, 0) * excess / room
                offsets[i + 1] -= moved
                spans[i + 1] = [spans[i + 1][0] - moved, spans[i + 1][1] - moved]
            width = spans[-1][1] - spans[0][0]
        shift = (tx0 + tx1) / 2 - (spans[0][0] + spans[-1][1]) / 2
        shift = min(max(shift, lo - spans[0][0]), hi - spans[-1][1])
        glyf[name] = _assemble(glyf, [(leaf, None, round(o + shift)) for leaf, o in zip(parts, offsets)])
        hmtx[name] = (adv_t, 0)
        plans[name] = plans.get(parts[0], (1.0, 0.0, 0.0))
        stats["composed"].append(name)
        return True

    for name, parts in compositions.items():
        if name in targets and all(p in plans for p in parts):
            compose_from_parts(name, parts)

    for name, target in targets.items():
        hmtx[name] = (target[0], 0)

    # Glyphs the passes did not reshape keep Fauxdana's outlines exactly
    # (overlap removal was only needed for the ones that are reshaped).
    for name, original in untouched_outlines.items():
        if name not in plans:
            glyf[name] = original

    # --- Canonically equivalent characters are the same character: the
    # Kelvin sign is K, the Ohm sign is omega, Greek letters with oxia are
    # the ones with tonos. One the reference lacks becomes an exact copy of
    # its equivalent (the reference sets it as that equivalent too).
    for code, name in cmap.items():
        if name in targets:
            continue
        nfc = unicodedata.normalize("NFC", chr(code))
        if len(nfc) == 1 and nfc != chr(code) and ord(nfc) in cmap and cmap[ord(nfc)] != name:
            twin = cmap[ord(nfc)]
            glyf[name] = copy.deepcopy(glyf[twin])
            hmtx[name] = (hmtx[twin][0], 0)
            plans[name] = plans.get(twin, (1.0, 0.0, 0.0))
            stats["twins"] += 1

    # --- Combining marks take no width. DejaVu draws a few as spacing
    # glyphs (U+065A ARABIC VOWEL SIGN SMALL V ABOVE has a 1024 advance):
    # those the reference lacks get a zero advance, with their ink centred
    # where the other zero-width marks of the same Unicode block centre.
    for code, name in cmap.items():
        if name in targets or category(code) != "Mn" or hmtx[name][0] == 0 or ink(glyf, name) is None:
            continue
        block = code >> 7
        centres = [(b[0] + b[1]) / 2 for c, n in cmap.items()
                   if c >> 7 == block and category(c) == "Mn" and hmtx[n][0] == 0 and (b := ink(glyf, n))]
        x0, x1, _, _ = ink(glyf, name)
        centre = statistics.median(centres) if centres else -(hmtx[name][0] / 2)
        translate(name, round(centre - (x0 + x1) / 2))
        hmtx[name] = (0, 0)
        stats["marks_zeroed"] += 1

    # --- Width relationships. Some characters are defined by the width of
    # others, and sets of digits are drawn to one width so numbers line up;
    # per-glyph condensing must not break that. Characters the reference has
    # keep the reference's widths; the rest follow them.
    def set_advance(name, advance):
        """New advance, ink kept centred where it was relative to the old one."""
        old = hmtx[name][0]
        if glyf[name].numberOfContours > 0 and old != advance:
            translate(name, round((advance - old) / 2))
        hmtx[name] = (advance, 0)
        stats["widths"] += 1

    def advance_of(code):
        return hmtx[cmap[code]][0]

    def digit_key(code):
        name = unicodedata.name(chr(code), "")
        if "SUPERSCRIPT" in name or "SUBSCRIPT" in name:
            return "superscript/subscript"
        return " ".join(w for w in name.split() if w not in ("ZERO", "ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX", "SEVEN", "EIGHT", "NINE", "DIGIT"))

    tabular = {}
    for code, name in cmap.items():
        if unicodedata.digit(chr(code), None) is not None and orig_adv.get(name):
            tabular.setdefault(digit_key(code), []).append(code)
    # Vulgar fractions with one-digit numerator and denominator share a width
    # (the reference's are all one width); a tenth or a bare numerator is wider.
    tabular["vulgar fractions"] = [c for c in cmap if "VULGAR FRACTION" in unicodedata.name(chr(c), "")
                                   and len(unicodedata.normalize("NFKD", chr(c))) == 3]
    for key, codes in tabular.items():
        if len(codes) < 3:
            continue
        names = [cmap[c] for c in codes]
        own = [n for n in names if n not in targets]
        shared = {targets[n][0] for n in names if n in targets}
        if not own or len(shared) > 1:
            continue          # all from the reference, or the reference's own set is not one width
        if shared:
            width = shared.pop()          # follow the reference's width for the set
        elif len({orig_adv[n] for n in own}) == 1:
            width = round(statistics.median(hmtx[n][0] for n in own))   # keep a one-width set one width
        else:
            continue                      # proportional by design (Lao digits)
        for n in own:
            set_advance(n, width)
    fixed = {0x2007: advance_of(ord("0")), 0x2012: advance_of(ord("0")), 0x2008: advance_of(ord(".")),
             0x2000: 1024, 0x2001: 2048, 0x2002: 1024, 0x2003: 2048, 0x2004: 683, 0x2005: 512, 0x2006: 341}
    for code, width in fixed.items():
        if code in cmap and cmap[code] not in targets:
            set_advance(cmap[code], width)
    for code in (0x2010, 0x2011):       # HYPHEN, NON-BREAKING HYPHEN: the hyphen itself
        if code in cmap and cmap[code] not in targets and ord("-") in cmap:
            glyf[cmap[code]] = copy.deepcopy(glyf[cmap[ord("-")]])
            hmtx[cmap[code]] = (advance_of(ord("-")), 0)
            stats["widths"] += 1

    # --- Keep ink inside the clipping box. Windows (GDI) clips glyphs at
    # usWinAscent / usWinDescent; where Fauxdana's stacked accents or deep
    # descenders reach past them, the part beyond the body is compressed
    # smoothly (identity at the anchor, monotonic) so the glyph fits.
    win_top, win_bottom = ref["OS/2"]["usWinAscent"], -ref["OS/2"]["usWinDescent"]
    for name in order:
        box = ink(glyf, name)
        if box is None:
            continue
        # A contextual form has no code point of its own: judge it by the
        # letter it is a form of.
        code = code_of.get(name, target_code.get(name))
        if name not in targets and not (code is None or category(code)[0] in "LM"):
            continue
        _, _, y0, y1 = box
        if y1 > win_top:
            anchor = 1556 if y0 < 1556 else y0
            span = y1 - anchor
            a = (y1 - win_top) / span if span > 0 else 1
            if 0 < a <= 0.45:
                map_points(glyf[name], lambda x, y, a=a, c=anchor, sp=span: (x, y - a * (y - c) ** 2 / sp) if y > c else (x, y))
                stats["clipped_fixed"] += 1
        if y0 < win_bottom:
            depth = -y0
            a = (depth + win_bottom) / depth
            if 0 < a <= 0.45:
                map_points(glyf[name], lambda x, y, a=a, d=depth: (x, y + a * y * y / d) if y < 0 else (x, y))
                stats["clipped_fixed"] += 1
            elif a > 0.45 and category(code)[0] in "LM":
                # Too deep for a smooth squeeze (a few Arabic letters with
                # dots far below): scale everything below the baseline.
                k = -win_bottom / depth
                map_points(glyf[name], lambda x, y, k=k: (x, y * k) if y < 0 else (x, y))
                stats["clipped_fixed"] += 1

    # --- Box drawing, block elements and the pieces of tall brackets and
    # integrals are drawn on DejaVu's line frame so that they join up from
    # line to line; map that frame exactly onto this font's (usWinDescent to
    # usWinAscent, which is also its hhea line height), or they leave gaps
    # between lines and are clipped on Windows.
    frame = ink(glyf, cmap[0x2588]) if 0x2588 in cmap else None     # FULL BLOCK spans the frame
    if frame:
        f0, f1 = frame[2], frame[3]
        k = (win_top - win_bottom) / (f1 - f0)
        for code, name in cmap.items():
            if name in targets or name in plans or not in_ranges(code, FRAME_RANGES) or ink(glyf, name) is None:
                continue
            map_points(glyf[name], lambda x, y: (x, win_bottom + (y - f0) * k))
            stats["framed"] += 1
    # Other characters the reference lacks that reach past the clipping box
    # (playing cards, dominoes, tall operators, a few punctuation marks and
    # digits): scaled down about their centre to fit, keeping their advance.
    for code, name in cmap.items():
        if name in targets or in_ranges(code, FRAME_RANGES) or category(code)[0] in "LM":
            continue
        box = ink(glyf, name)
        if box is None or (box[3] <= win_top and box[2] >= win_bottom):
            continue
        x0, x1, y0, y1 = box
        k = min(1.0, (win_top - win_bottom) / (y1 - y0))
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        dy = 0.0
        if cy + k * (y1 - cy) > win_top:
            dy = win_top - (cy + k * (y1 - cy))
        if cy + k * (y0 - cy) + dy < win_bottom:
            dy = win_bottom - (cy + k * (y0 - cy))
        map_points(glyf[name], lambda x, y: (cx + k * (x - cx), cy + k * (y - cy) + dy))
        stats["shrunk"] += 1

    # --- Dots keep their shape. Fitting a glyph into the reference's ink box
    # can scale it more one way than the other, and keeping deep descenders
    # inside the clipping box squeezes them only vertically: a square dot
    # comes out as a dash (under a few Arabic letters it then reads as a
    # kasra) or a sliver. Each dot whose proportions changed by more than a
    # quarter gets its own back (or up to 1.4 times longer one way, for more
    # ink where space runs short), as large as fits (up to its present area)
    # without coming within 20 units (or 0.4 of its size) of another part or
    # past the clipping box, and at worst inside the box the distorted dot
    # had.
    reshaped = []
    for name in order:
        before_dots = source_dots.get(name)
        g = glyf[name]
        if not before_dots or g.numberOfContours <= 0:
            continue
        now = dot_parts(g, 2048, square=False, margin=0)
        if len(now) != len(before_dots):
            continue
        coords = list(g.coordinates)
        flags = list(g.flags)
        ranges = list(contour_ranges(g))
        changed = False
        for (idx, x0, x1, y0, y1), r in zip(now, before_dots):
            w, h = x1 - x0, y1 - y0
            if max((w / h) / r, r / (w / h)) <= 1.25:
                continue
            cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
            inner_w, inner_h = (h * r, h) if w / h > r else (w, w / r)
            full_h = math.sqrt(w * h / r)
            others = [_contour_path(coords[a:b + 1], [bool(f & 1) for f in flags[a:b + 1]])
                      for k, (a, b) in enumerate(ranges) if k not in idx]
            choice = None
            flat = w / h > r                  # flattened (else narrowed)
            for step in range(11):
                size = max(inner_h if flat else inner_w, (full_h if flat else full_h * r) * (1 - 0.05 * step))
                # Where height (or width) is what runs short, the dot may stay
                # up to 1.4 times longer the other way, for more ink at text
                # sizes: still a dot, not a dash.
                for longer in (1.4, 1.2, 1.0):
                    if flat:
                        nh, nw = size, min(w, size * r * longer)
                    else:
                        nw, nh = size, min(h, size / r * longer)
                    ny = clamp(cy, win_bottom + nh / 2, win_top - nh / 2)
                    trial = list(coords)
                    for k in idx:
                        a, b = ranges[k]
                        for i in range(a, b + 1):
                            x, y = coords[i]
                            trial[i] = (cx + (x - cx) * nw / w, ny + (y - cy) * nh / h)
                    # clear of the other parts by 20 units, or by 0.4 of
                    # the dot's size if more: dots closer than that run
                    # together at text sizes, and two dots read as one
                    clear = max(20.0, 0.4 * min(nw, nh))
                    grown = []
                    for k in idx:
                        a, b = ranges[k]
                        grown += [(cx + (trial[i][0] - cx) * (nw + 2 * clear) / nw, ny + (trial[i][1] - ny) * (nh + 2 * clear) / nh) for i in range(a, b + 1)]
                    a, b = ranges[idx[0]]
                    mine = _contour_path(grown[:b - a + 1], [bool(f & 1) for f in flags[a:b + 1]])
                    if not any(abs(pathops.op(mine, o, pathops.PathOp.INTERSECTION, fix_winding=True).area) > 1 for o in others):
                        choice = trial
                        break
                if choice is not None or size <= (inner_h if flat else inner_w):
                    break
            if choice is None:              # the box the distorted dot had
                ny = cy
                choice = list(coords)
                for k in idx:
                    a, b = ranges[k]
                    for i in range(a, b + 1):
                        x, y = coords[i]
                        choice[i] = (cx + (x - cx) * inner_w / w, cy + (y - cy) * inner_h / h)
            coords = choice
            changed = True
        if changed:
            # Two dots stacked one above the other (ې) that began the same
            # size share the height between them evenly, rather than the
            # first taking the room and leaving the other a speck, or the
            # two coming so close that they read as one.
            after = dot_parts(GlyphCoordinatesGlyph(g, coords), 2048, square=False, margin=0)
            for (ia, ax0, ax1, ay0, ay1), (ib, bx0, bx1, by0, by1) in zip(after, after[1:]):
                upper, lower = ((ia, ax0, ax1, ay0, ay1), (ib, bx0, bx1, by0, by1)) if ay0 > by0 else ((ib, bx0, bx1, by0, by1), (ia, ax0, ax1, ay0, ay1))
                if min(ax1, bx1) - max(ax0, bx0) <= 0 or upper[3] - lower[4] > 60:
                    continue
                hu, hl = upper[4] - upper[3], lower[4] - lower[3]
                if hu < 1.5 * hl and upper[3] - lower[4] >= 0.4 * min(hu, hl):
                    continue
                # the gap between them half a dot high (at least 20 units),
                # as in the source's proportions, so they stay two dots
                total = upper[4] - lower[3]
                share = total / 2.5 if total / 2.5 * 0.5 >= 20 else (total - 20) / 2
                common = min(share * 1.4, max(upper[2] - upper[1], lower[2] - lower[1]))
                for (idx, x0, x1, y0, y1), top in ((upper, upper[4]), (lower, lower[3] + share)):
                    w, h = x1 - x0, y1 - y0
                    nh, nw = share, common
                    cx = (x0 + x1) / 2
                    for k in idx:
                        a, b = ranges[k]
                        for i in range(a, b + 1):
                            x, y = coords[i]
                            coords[i] = (cx + (x - cx) * nw / w, top - (y1 - y) * nh / h)
            g.coordinates = GlyphCoordinates(coords)
            reshaped.append(name)
    stats["dots_reshaped"] = reshaped

    # U+FFFC OBJECT REPLACEMENT CHARACTER is blank in DejaVu; the reference
    # draws it. Draw a plain dashed box filling the reference's ink box.
    if 0xFFFC in cmap and 0xFFFC in ref_glyphs and len(ref_glyphs[0xFFFC]) == 5 and ink(glyf, cmap[0xFFFC]) is None:
        _, bx0, bx1, by0, by1 = ref_glyphs[0xFFFC]
        t = 94                     # a thin dashed frame in both weights, as in the reference
        dash, gap = 4 * t, round(2.5 * t)
        pen = TTGlyphPen(None)
        def rect(x0, y0, x1, y1):
            pen.moveTo((x0, y0)); pen.lineTo((x0, y1)); pen.lineTo((x1, y1)); pen.lineTo((x1, y0)); pen.closePath()
        def dashes(a, b, margin):
            length = b - a - 2 * margin
            n = max(1, round((length + gap) / (dash + gap)))
            d = (length - (n - 1) * gap) / n
            return [(round(a + margin + i * (d + gap)), round(a + margin + i * (d + gap) + d)) for i in range(n)]
        for a, b in dashes(bx0, bx1, 0):
            rect(a, by0, b, by0 + t)
            rect(a, by1 - t, b, by1)
        for a, b in dashes(by0 + t, by1 - t, gap):
            rect(bx0, a, bx0 + t, b)
            rect(bx1 - t, a, bx1, b)
        glyf[cmap[0xFFFC]] = pen.glyph()
        stats["drawn"] += 1

    # --- The missing-glyph box (glyph 0) is shown for characters the font
    # lacks wherever no other font is substituted, so it must be as wide as
    # the reference's. Fauxdana's own box is scaled onto the reference's.
    notdef = order[0]
    if "notdef" in ref and len(ref["notdef"]) == 5 and ink(glyf, notdef):
        adv_t, tx0, tx1, ty0, ty1 = ref["notdef"]
        x0, x1, y0, y1 = ink(glyf, notdef)
        map_points(glyf[notdef], lambda x, y: (tx0 + (x - x0) * (tx1 - tx0) / (x1 - x0),
                                               ty0 + (y - y0) * (ty1 - ty0) / (y1 - y0)))
        hmtx[notdef] = (adv_t, 0)
    elif "notdef" in ref:
        hmtx[notdef] = (ref["notdef"][0], 0)

    # --- Stray single points. DejaVu leaves a few one- or two-point
    # contours (in U+2244 and some unencoded alternates); they draw nothing
    # but some tools warn about them.
    for name in order:
        g = glyf[name]
        if g.numberOfContours <= 0:
            continue
        coords, flags = list(g.coordinates), list(g.flags)
        keep_coords, keep_flags, ends = [], [], []
        for start, end in contour_ranges(g):
            if end - start + 1 >= 3:
                keep_coords += coords[start:end + 1]
                keep_flags += flags[start:end + 1]
                ends.append(len(keep_coords) - 1)
        if len(ends) != g.numberOfContours:
            g.coordinates = GlyphCoordinates(keep_coords)
            g.flags = bytearray(keep_flags)
            g.endPtsOfContours = ends
            g.numberOfContours = len(ends)
            stats["strays"] += 1

    # --- Accent pieces that the stroke push made touch (the circumflex and
    # acute of Vietnamese letters in Bold) are merged into one outline, so
    # no contours overlap; the letter's own contours are left as they are.
    for name in sorted(merge_marks):
        g = glyf[name]
        ranges = list(contour_ranges(g))
        flags = list(g.flags)
        coords = list(g.coordinates)
        paths = [_contour_path(coords[a:b + 1], [bool(f & 1) for f in flags[a:b + 1]]) for a, b in ranges]
        # groups of contours that overlap each other and are not counters
        groups = list(range(len(ranges)))
        def root(k):
            while groups[k] != k:
                k = groups[k]
            return k
        for i in range(len(ranges)):
            for j in range(i + 1, len(ranges)):
                inter = abs(pathops.op(paths[i], paths[j], pathops.PathOp.INTERSECTION, fix_winding=True).area)
                smaller = min(abs(paths[i].area), abs(paths[j].area))
                least = 0 if name in stats["rejoined"] else 20      # a rejoined mark is merged however little it overlaps
                if least < inter < 0.5 * smaller:       # touching, not one inside the other
                    groups[root(j)] = root(i)
        members = {}
        for k in range(len(ranges)):
            members.setdefault(root(k), []).append(k)
        if all(len(v) == 1 for v in members.values()):
            continue
        pen = TTGlyphPen(None)
        for k, (a, b) in enumerate(ranges):
            if len(members[root(k)]) == 1:
                glyf_contour = _assemble(glyf, [(name, {k}, 0)])
                glyf_contour.draw(pen, glyf)
        for v in members.values():
            if len(v) > 1:
                union = pathops.Path()
                for k in v:
                    union = pathops.op(union, paths[k], pathops.PathOp.UNION, fix_winding=True)
                pathops.simplify(union, fix_winding=True, clockwise=True).draw(pen)   # TrueType: outer contours clockwise
        merged = pen.glyph()
        merged.program = ttProgram.Program()
        merged.program.fromBytecode(b"")
        glyf[name] = merged
        stats["merged"] += 1

    # --- Round, bounds, side bearings. Rounding (and overlap removal where
    # o meets its horn) can leave runs of repeated points, zero-length
    # segments that some tools warn about. A run is replaced by one on-curve
    # point there: every segment into or out of it was already straight at
    # that end, so the outline is unchanged.
    for name in order:
        g = glyf[name]
        if g.numberOfContours > 0:
            g.coordinates.toInt()
            coords, flags = list(g.coordinates), list(g.flags)
            new_coords, new_flags, ends = [], [], []
            for start, end in contour_ranges(g):
                pts = [(tuple(coords[i]), flags[i] & 1) for i in range(start, end + 1)]
                kept = []
                for p, on in pts:
                    if kept and kept[-1][0] == p:
                        kept[-1] = (p, 1)
                    else:
                        kept.append((p, on))
                while len(kept) > 1 and kept[0][0] == kept[-1][0]:
                    kept[0] = (kept[0][0], 1)
                    kept.pop()
                if len(kept) < 3:
                    continue
                new_coords += [p for p, _ in kept]
                new_flags += [on for _, on in kept]
                ends.append(len(new_coords) - 1)
            if len(new_coords) != len(coords):
                g.coordinates = GlyphCoordinates(new_coords)
                g.flags = bytearray(new_flags)
                g.endPtsOfContours = ends
                g.numberOfContours = len(ends)
                stats["repeats"] += 1
            g.recalcBounds(glyf)
            hmtx[name] = (hmtx[name][0], g.xMin)
        else:
            hmtx[name] = (hmtx[name][0], 0)

    # --- Code points sharing a glyph. The reference draws some characters
    # with another's glyph (private-use U+F001/U+F002 with the fi/fl
    # ligatures, U+F031 with dotless i). Where this face has one of such a
    # group but not another, the other is mapped to the same glyph, so it
    # doesn't fall back to another font where the reference shows it.
    if "sharedGlyphs" not in ref:
        sys.exit(f"{args.metrics}: no sharedGlyphs; re-run extract_metrics.py on the reference fonts")
    aliased = []
    for group in ref["sharedGlyphs"]:
        have = [c for c in group if c in cmap and not 0xE000 <= c <= 0xF8FF]
        for c in group:
            # Missing here, or a private-use character Fauxdana draws as
            # something else (its U+F001/U+F002 are placeholder boxes, where
            # the reference's are the fi and fl ligatures).
            missing = c not in cmap or (0xE000 <= c <= 0xF8FF and have and cmap[c] != cmap[have[0]])
            if have and missing and c in ref_glyphs and hmtx[cmap[have[0]]][0] == ref_glyphs[c][0]:
                for table in font["cmap"].tables:
                    if table.isUnicode() and (c <= 0xFFFF or table.format in (12, 13)):
                        table.cmap[c] = cmap[have[0]]
                cmap[c] = cmap[have[0]]
                aliased.append(c)

    # --- Layout tables.
    for tag in ("GSUB", "GPOS", "GDEF", "kern", "morx", "feat"):
        if tag in font:
            del font[tag]
    if gsub is not None:
        font["GSUB"] = gsub
    classes = {}
    for code, cls in ref.get("classes", {}).items():
        name = cmap.get(int(code, 16))
        if name:
            classes[name] = cls
    for tag, entries in ref.get("formClasses", {}).items():
        for code, cls in entries.items():
            name = form_glyph.get((tag, int(code, 16)))
            if name:
                classes[name] = cls
    for key, cls in ref.get("markLigatureClasses", {}).items():
        if key in mark_lig_glyph:
            classes[mark_lig_glyph[key]] = cls
    if gsub is not None:
        # Arabic glyphs the reference does not classify (letters it lacks).
        arabic_glyphs = set()
        for lookup in gsub.table.LookupList.Lookup:
            for sub in lookup.SubTable:
                for a, b in getattr(sub, "mapping", {}).items():
                    arabic_glyphs.update((a, b))
                for first, ligs in getattr(sub, "ligatures", {}).items():
                    arabic_glyphs.add(first)
                    for lig in ligs:
                        arabic_glyphs.update(lig.Component)
                        if lig.LigGlyph not in targets:
                            parts = [first] + list(lig.Component)
                            mark_lig = all(category(code_of.get(p)) == "Mn" for p in parts)
                            classes.setdefault(lig.LigGlyph, 3 if mark_lig else 2)
        for code, name in cmap.items():
            if in_ranges(code, ARABIC_RANGES):
                arabic_glyphs.add(name)
        for name in arabic_glyphs:
            # Glyphs the reference has keep its classification (or lack of one).
            if name not in classes and name not in targets:
                code = code_of.get(name)
                classes[name] = 3 if code is not None and category(code) == "Mn" else 1
    if classes:
        gdef = ot.GDEF()
        gdef.Version = 0x00010000
        gdef.GlyphClassDef = ot.ClassDef()
        gdef.GlyphClassDef.classDefs = classes
        gdef.AttachList = gdef.LigCaretList = gdef.MarkAttachClassDef = None
        font["GDEF"] = newTable("GDEF")
        font["GDEF"].table = gdef

    # --- Kerning: the reference's pairs, by code point, in the same kind of
    # table it has (a legacy 'kern' table, format 0, horizontal), so that
    # engines that kern by default (browsers, LibreOffice, word processors
    # with kerning on) set text exactly as they do with the reference, and
    # treat marks between letters the same way. Pairs between characters
    # this face lacks are left out.
    kern_pairs, kern_conflicts = {}, 0
    for first, second, value in ref.get("kern", []):
        if first in cmap and second in cmap:
            pair = (cmap[first], cmap[second])
            if kern_pairs.get(pair, value) != value:
                kern_conflicts += 1
            kern_pairs.setdefault(pair, value)
    if kern_pairs:
        from fontTools.ttLib.tables._k_e_r_n import KernTable_format_0
        table = KernTable_format_0()
        table.version, table.format, table.coverage = 0, 0, 1
        table.kernTable = kern_pairs
        font["kern"] = newTable("kern")
        font["kern"].version = 0
        font["kern"].kernTables = [table]
    if kern_conflicts:
        print(f"warning: {kern_conflicts} kerning pairs disagree where two characters share a glyph here")

    # --- Vertical metrics and line positions.
    for field, value in ref["hhea"].items():
        setattr(font["hhea"], field, value)
    os2 = font["OS/2"]
    for field, value in ref["OS/2"].items():
        setattr(os2, field, value)
    for field, value in ref["post"].items():
        setattr(font["post"], field, value)
    if args.full_coverage:
        # Not the reference's character set: declare what this face covers.
        os2.recalcUnicodeRanges(font)
        os2.recalcCodePageRanges(font)
    os2.achVendID = "NONE"
    os2.fsType = 0

    # --- Names.
    name_table = font["name"]
    dejavu_copyright = (name_table.getDebugName(0) or "").split(" Fauxdana:")[0].strip()
    original_licence = name_table.getDebugName(13) or ""
    full = FAMILY if style == "Regular" else f"{FAMILY} {style}"
    records = {
        0: f"{dejavu_copyright}\nCopyright 2026 The Fauxdana Project Authors (https://github.com/muglug/fauxdana)\nCopyright 2026 The Taquoma Project Authors",
        1: FAMILY,
        2: style,
        3: f"{FAMILY} {style}; {VERSION}",
        4: full,
        5: f"Version {VERSION}",
        6: f"{FAMILY}-{style}",
        10: ("Taquoma is derived from Fauxdana and DejaVu Sans; its outlines are theirs, refitted to "
             f"a reference font's {'advance widths, line metrics and kerning' if kern_pairs else 'advance widths and line metrics'}."),
        13: ("This Font Software is licensed under the SIL Open Font License, Version 1.1 "
             "(https://openfontlicense.org). Taquoma is derived from Fauxdana, which is derived from "
             "DejaVu Sans; the notices of the fonts it derives from follow.\n\n" + original_licence),
        14: "https://openfontlicense.org",
    }
    name_table.names = []
    for nid, value in records.items():
        name_table.setName(value, nid, 3, 1, 0x409)
    font["head"].fontRevision = float(VERSION)
    font.recalcTimestamp = False

    # --- Character set. Only the characters the reference has are kept
    # (with the glyphs its contextual forms need). A character the reference
    # lacks then falls back to another font, or is decomposed into base +
    # marks, exactly as it is with the reference, instead of being drawn in
    # this font at different widths.
    if not args.full_coverage:
        from fontTools import subset
        options = subset.Options()
        options.layout_features = ["*"]
        options.name_IDs = ["*"]
        options.name_languages = ["*"]
        options.name_legacy = True
        options.glyph_names = True
        options.notdef_glyph = True
        options.notdef_outline = True
        options.recalc_bounds = True
        options.recalc_timestamp = False
        options.recalc_average_width = False        # keep the reference's
        options.prune_unicode_ranges = False      # set below
        options.prune_codepage_ranges = False
        subsetter = subset.Subsetter(options)
        kept = sorted(c for c in font.getBestCmap() if c in ref_glyphs)
        subsetter.populate(unicodes=kept)
        subsetter.subset(font)
        stats["kept"] = len(kept)
        # The scripts the face declares (OS/2 Unicode-range and code-page
        # bits, which Word and other apps choose fonts by) are the
        # reference's, so apps treat the two alike; except scripts this face
        # lacks (Thai), which it must not claim.
        lost_ranges, lost_pages = lost_scripts(set(ref_glyphs), set(font.getBestCmap()))
        os2 = font["OS/2"]
        os2.setUnicodeRanges(os2.getUnicodeRanges() - set(lost_ranges))
        for bit in lost_pages:
            if bit < 32:
                os2.ulCodePageRange1 &= ~(1 << bit)
            else:
                os2.ulCodePageRange2 &= ~(1 << (bit - 32))
        stats["lost_scripts"] = (lost_ranges, lost_pages)

    buf = io.BytesIO()
    font.save(buf)
    data = buf.getvalue()
    if not args.no_hint:
        import ttfautohint
        data = ttfautohint.ttfautohint(in_buffer=data, windows_compatibility=True,
                                       default_script="latn", fallback_script="none")
        hinted = TTFont(io.BytesIO(data))
        unhinted = strip_damaging_hints(hinted, data)
        if unhinted:
            print(f"hinting removed from {len(unhinted)} glyphs it distorted: {' '.join(unhinted[:12])}{' ...' if len(unhinted) > 12 else ''}")
        # ttfautohint must not have changed any advance.
        bad = [n for n in font.getGlyphOrder() if hinted["hmtx"][n][0] != font["hmtx"][n][0]]
        assert not bad, bad[:10]
        # Deterministic output: keep the source's timestamps, not the build time.
        hinted["head"].created = font["head"].created
        hinted["head"].modified = font["head"].modified
        hinted.recalcTimestamp = False
        buf = io.BytesIO()
        hinted.save(buf)
        data = buf.getvalue()
    # --- Glyph names. A ligature of marks is named after the marks it is
    # made of, so text extraction that goes by glyph names (a PDF without a
    # ToUnicode map) reads the right vowel. DejaVu names two after their
    # shape: shadda + kasra as uni064E0651 ("fatha + shadda") and shadda +
    # kasratan as uni064B0651. Only the post table's names change; every
    # other table is copied as it is.
    renames = {name: "uni" + key.replace(" ", "") for key, name in mark_lig_glyph.items()
               if name != "uni" + key.replace(" ", "")}
    if renames:
        final = TTFont(io.BytesIO(data), recalcTimestamp=False, recalcBBoxes=False)
        order = final.getGlyphOrder()
        assert not set(renames.values()) & set(order), renames
        final.setGlyphOrder([renames.get(n, n) for n in order])
        final["post"].compile(final)          # names come from the new glyph order
        buf = io.BytesIO()
        final.save(buf)
        renamed = TTFont(io.BytesIO(buf.getvalue()))
        before = TTFont(io.BytesIO(data))
        assert all(before.reader[t] == renamed.reader[t] for t in before.reader.keys() if t not in ("post", "head")), "rename touched other tables"
        data = buf.getvalue()
    with open(args.out, "wb") as f:
        f.write(data)

    if os.environ.get("TAQUOMA_DEBUG"):
        for name, why in stats["base_failed"].items():
            print(f"  not via base: {name} U+{code_of.get(name, 0):04X}: {why}")
    if duplicates:
        print(f"duplicate contours removed from {len(duplicates)} glyphs")
    if stats.get("lost_scripts") and any(stats["lost_scripts"]):
        r, p = stats["lost_scripts"]
        print(f"script declarations of the reference left out (scripts this face lacks): Unicode-range bits {r}, "
              f"code pages {[CODE_PAGES[b][2:] if CODE_PAGES[b].startswith('cp') else CODE_PAGES[b] for b in p]}")
    if stats["rejoined"]:
        print(f"letters built on their base letter with an overlapping mark: {len(stats['rejoined'])} "
              f"({' '.join(chr(code_of[n]) for n in stats['rejoined'] if n in code_of)})")
    if stats.get("dots_reshaped"):
        names = stats["dots_reshaped"]
        labels = [f"U+{code_of[n]:04X}" if n in code_of else n for n in names]
        print(f"dots given back their shape in {len(names)} glyphs: {' '.join(labels)}")
    if aliased:
        print(f"mapped to the glyph the reference shares them with: {' '.join(f'U+{c:04X}' for c in aliased)}")
    if stats["composed"]:
        print(f"made from their letters: {' '.join(chr(code_of[n]) if n in code_of else n for n in stats['composed'])}")
    if repaired is not None:
        print(f"accents re-centred over their letters in {len(repaired)} of Fauxdana's glyphs "
              f"({sum(any(m.startswith('body') for m in v) for v in repaired.values())} with the base letter's body restored)")
    print(f"{args.out}: {stats['fitted']} glyphs refitted to the reference, {stats['base']} accented letters "
          f"via their base, {stats['family']} condensed family-wide, {stats['blank']} blank; accents moved in "
          f"{stats['marks_moved']}; stem {stem} -> {stem_ref}, family scale {s_family:.3f} + {2 * e_family:.0f} "
          f"stem, spacing x{k_spacing:.3f}; {len(kern_pairs)} kerning pairs; "
          f"descenders fitted {stats['descenders']}; {stats['clipped_fixed']} pulled inside the clipping box; "
          f"{stats['framed']} frame glyphs mapped to the line box; {stats['shrunk']} oversize symbols shrunk; "
          f"{stats['widths']} widths set by their relationships; {stats['twins']} copied from canonical equivalents; "
          f"{stats['marks_zeroed']} spacing marks made zero-width; {len(stats['accents_fitted'])} accents narrowed or moved inside the reference's ink box; {stats['strays']} glyphs cleared of stray points; {stats['repeats']} of repeated points; {stats['merged']} with touching accent pieces merged; {stats.get('f_bar', 0)} f crossbars ended at the advance; {stats.get('stacked_respaced', 0)} stacked accent pieces moved apart; {hebrew_count} Hebrew letters brought to the reference's height; {len(stats['boxed'])} simple shapes mapped onto the reference's ink box; {len(stats['separated'])} with a dot or mark moved clear of a stroke; "
          f"{'all characters kept' if stats['kept'] is None else str(stats['kept']) + ' characters kept (the reference has them)'}; "
          f"stroke push reduced to avoid damage in {len(stats['damped'])}: {' '.join(stats['damped'][:30])}; "
          f"{len(stats['clamped'])} scale-clamped: {' '.join(stats['clamped'][:40])}")


if __name__ == "__main__":
    main()
