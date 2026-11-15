#!/usr/bin/env python3
"""verify.py REFERENCE.ttf TAQUOMA.ttf [--source FAUXDANA.ttf] [--report N]

Checks a Taquoma face against the reference face it was measured from.

Metric compatibility (any failure here is a layout difference):
  * every code point both fonts map has the same advance width, and so does
    the missing-glyph box; Taquoma maps no character the reference lacks
    (so such characters fall back exactly as they do with the reference);
  * line metrics (hhea, OS/2, post, head) agree;
  * text shaped with HarfBuzz, which applies Arabic joining, mark handling
    and the legacy 'kern' table the way browsers and LibreOffice do, puts
    every character at the same pen position and ends at the same width,
    with kerning on (the default) and with kerning off. Shaped: sample texts in several
    scripts; every shared character alone and between letters; every
    kerning pair; every Arabic letter in every joining position; and every
    precomposed character Taquoma has but the reference lacks, written both
    precomposed and decomposed, between other letters (the reference sets
    those as base + mark, Taquoma composes them). The samples and the Arabic
    tests are shaped again with ligatures off (CSS font-variant-ligatures:
    none) and with each joining, ligature and composition feature off.

Width relationships within Taquoma (failures count): figure space and
figure dash one digit wide, punctuation space a period wide, hyphens and the
no-break space like their plain forms, em-fraction spaces exact, digit sets
and one-digit vulgar fractions at the reference's width where it has them,
and (with --source) sets that were one width in Fauxdana still one width.

Dots (with --source; failures count): no dot more than 1.45 times off its
proportions in Fauxdana (a dot squashed into a dash can read as a kasra).

Outline quality (reported):
  * contours that cross themselves, overlap, run anticlockwise, are drawn
    twice or repeat a point (all must be absent);
  * accented letters that do not contain their base letter exactly, where
    the base letter has it;
  * glyphs reaching beyond usWinAscent/usWinDescent (clipped on Windows)
    where the reference's do not;
  * letters reaching past their advance (into the neighbouring letters'
    space) further than the reference's;
  * ink-box deviations from the reference.
"""
import statistics
import os
import sys
import unicodedata

import pathops
import uharfbuzz as hb
from fontTools.pens.recordingPen import RecordingPen
from fontTools.ttLib import TTFont

SAMPLES = [
    "The quick brown fox jumps over the lazy dog. 0123456789",
    "AVATAR Toyota LTA WAVE Yo Tr Ty P. F, L' \"quoted\" (parens) [brackets] {braces}",
    "Sphinx of black quartz, judge my vow! @#$%^&*_+-=<>?/|\\~`",
    "Ærøskøbing, Œuvre, façade, naïve, Ångström, Đorđe, Łódź, Žižkov",
    "Việt Nam: Tiếng Việt có dấu thanh — ở, ữ, ặ, ễ, ỵ",
    "Привет, мир! Съешь же ещё этих мягких французских булок.",
    "Ξεσκεπάζω την ψυχοφθόρα βδελυγμία. Άλφα Έψιλον Ήτα",
    "שלום עולם, אבגדהוזחטיכלמנסעפצקרשת",
    "מִי שֶׁלֹּא טָעַם",
    "مرحبا بالعالم، لا إله إلا الله. سلام",
    "بِسْمِ اللَّهِ الرَّحْمَنِ الرَّحِيمِ — شُكْرًا جَزِيلًا",
    "é ä ô ñ ǹ ṇ xǒx — combining sequences",
    "€ £ ¥ © ® ™ ° ± × ÷ ¶ § • … ‰ ‹ › « » “ ” ‘ ’ ‚ „",
]
KERN_CONTEXTS = ["{}", "x{}x", "A{}T", "T{}V", "r{}y", "f{}.", "L{}'", "({})"]


class Shaper:
    """Shapes with HarfBuzz; kern=False turns kerning off (as CSS
    font-kerning: none and word processors with pair kerning off do)."""
    def __init__(self, path, kern=False, off=()):
        self.font = hb.Font(hb.Face(hb.Blob.from_file_path(path)))
        self.features = {} if kern else {"kern": False}
        self.features.update({tag: False for tag in off})

    def __call__(self, text):
        """(pen position at the start of each character cluster, total width)"""
        buf = hb.Buffer()
        buf.add_str(text)
        buf.guess_segment_properties()
        hb.shape(self.font, buf, self.features)
        starts, x = {}, 0
        for info, pos in zip(buf.glyph_infos, buf.glyph_positions):
            starts.setdefault(info.cluster, x)
            x += pos.x_advance
        return starts, x

    def renders(self, text):
        """False if any character comes out as the missing-glyph box."""
        buf = hb.Buffer()
        buf.add_str(text)
        buf.guess_segment_properties()
        hb.shape(self.font, buf, self.features)
        return all(info.codepoint != 0 for info in buf.glyph_infos)


def same_layout(a, b):
    (sa, wa), (sb, wb) = a, b
    common = set(sa) & set(sb)
    return wa == wb and all(sa[k] == sb[k] for k in common)


def crossing_contours(font, name):
    glyph_set = font.getGlyphSet()
    rec = RecordingPen()
    glyph_set[name].draw(rec)
    current, count = [], 0
    for op, args in rec.value:
        current.append((op, args))
        if op in ("closePath", "endPath"):
            path = pathops.Path()
            pen = path.getPen()
            for o, a in current:
                getattr(pen, o)(*a)
            area = abs(path.area)
            simple = pathops.simplify(path, fix_winding=True, keep_starting_points=True)
            if len(list(simple.contours)) > 1 or abs(abs(simple.area) - area) > max(4.0, 0.002 * area):
                count += 1
            current = []
    return count


CODE_PAGES = {0: "cp1252", 1: "cp1250", 2: "cp1251", 3: "cp1253", 4: "cp1254", 5: "cp1255", 6: "cp1256",
              7: "cp1257", 8: "cp1258", 16: "cp874", 29: "mac_roman", 48: "cp869", 49: "cp866", 50: "cp865",
              51: "cp864", 52: "cp863", 53: "cp862", 54: "cp861", 55: "cp860", 56: "cp857", 57: "cp855",
              58: "cp852", 59: "cp775", 60: "cp737", 61: "iso8859_6", 62: "cp850", 63: "cp437"}


def lost_scripts(ref_codes, codes):
    """OS/2 Unicode-range and code-page bits of scripts the font lacks
    (as in make_taquoma.py)."""
    from fontTools.ttLib.tables.O_S_2f_2 import OS2_UNICODE_RANGES
    ranges = [bit for bit, blocks in enumerate(OS2_UNICODE_RANGES)
              if (in_ref := {c for c in ref_codes for _, (lo, hi) in blocks if lo <= c <= hi})
              and 2 * len(in_ref & codes) < len(in_ref)]
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


def main():
    ref_path, path = sys.argv[1:3]
    report = int(sys.argv[sys.argv.index("--report") + 1]) if "--report" in sys.argv else 15
    source = TTFont(sys.argv[sys.argv.index("--source") + 1]) if "--source" in sys.argv else None
    R, T = TTFont(ref_path), TTFont(path)
    rc, tc = R.getBestCmap(), T.getBestCmap()
    rs, ts = Shaper(ref_path), Shaper(path)                            # kerning off
    rk, tk = Shaper(ref_path, kern=True), Shaper(path, kern=True)      # kerning on (the default)
    ok = True

    shared = sorted(set(rc) & set(tc))
    bad = [(c, R["hmtx"][rc[c]][0], T["hmtx"][tc[c]][0]) for c in shared if R["hmtx"][rc[c]][0] != T["hmtx"][tc[c]][0]]
    print(f"advances: {len(shared) - len(bad)}/{len(shared)} shared code points identical; "
          f"{len(set(rc) - set(tc))} reference code points missing from Taquoma")
    for c, a, b in bad[:report]:
        print(f"   U+{c:04X} {chr(c)!r}: reference {a}, Taquoma {b}")
    ok &= not bad

    nd_r, nd_t = R["hmtx"][R.getGlyphOrder()[0]][0], T["hmtx"][T.getGlyphOrder()[0]][0]
    print(f"missing-glyph box (glyph 0) advance: {'identical' if nd_r == nd_t else f'{nd_r} vs {nd_t}'}")
    ok &= nd_r == nd_t
    extra = sorted(set(tc) - set(rc))
    print(f"characters Taquoma has that the reference lacks: {len(extra)}"
          f"{' (they would not fall back to another font as with the reference)' if extra else ''}")
    ok &= not extra

    for table, fields in (("hhea", ("ascent", "descent", "lineGap")),
                          ("OS/2", ("sTypoAscender", "sTypoDescender", "sTypoLineGap", "usWinAscent", "usWinDescent", "xAvgCharWidth",
                                    "sxHeight", "sCapHeight", "usDefaultChar", "usBreakChar", "fsSelection", "usWeightClass",
                                    "sFamilyClass", "version")),
                          ("post", ("underlinePosition", "underlineThickness")),
                          ("head", ("unitsPerEm",))):
        # (fields a table version lacks, such as sxHeight in OS/2 version 1, must be absent from both)
        diff = [(f, getattr(R[table], f, None), getattr(T[table], f, None)) for f in fields
                if getattr(R[table], f, None) != getattr(T[table], f, None)]
        print(f"{table}: {'identical' if not diff else diff}")
        ok &= not diff

    # Declared scripts (OS/2 Unicode-range and code-page bits): Word and
    # other apps choose fonts by them, so they must be the reference's,
    # except for scripts Taquoma lacks (fewer than half the reference's
    # characters in the range; letters, for a code page).
    lost_r, lost_p = lost_scripts(set(rc), set(tc))
    ur = lambda o: o.ulUnicodeRange1 | o.ulUnicodeRange2 << 32 | o.ulUnicodeRange3 << 64 | o.ulUnicodeRange4 << 96
    cpr = lambda o: o.ulCodePageRange1 | o.ulCodePageRange2 << 32
    want_ur = ur(R["OS/2"]) & ~sum(1 << b for b in lost_r)
    want_cp = cpr(R["OS/2"]) & ~sum(1 << b for b in lost_p)
    bad_ur = [b for b in range(128) if (want_ur ^ ur(T["OS/2"])) >> b & 1]
    bad_cp = [b for b in range(64) if (want_cp ^ cpr(T["OS/2"])) >> b & 1]
    print(f"declared scripts (OS/2 Unicode ranges and code pages): {'the reference' + chr(39) + 's' if not (bad_ur or bad_cp) else 'DIFFERENT'}"
          f" (left out for scripts Taquoma lacks: Unicode-range bits {lost_r}, code-page bits {lost_p})"
          + (f"; differing Unicode-range bits {bad_ur}, code-page bits {bad_cp}" if bad_ur or bad_cp else ""))
    ok &= not (bad_ur or bad_cp)

    def check(label, texts):
        nonlocal ok
        # Text the reference cannot render (it shows the missing-glyph box;
        # a browser would substitute another font) has no layout to match.
        skipped = [t for t in texts if not rs.renders(t)]
        texts = [t for t in texts if rs.renders(t)]
        failures = [(t, "kerning on") for t in texts if not same_layout(rk(t), tk(t))]
        failures += [(t, "kerning off") for t in texts if not same_layout(rs(t), ts(t))]
        note = f" ({len(skipped)} skipped: the reference cannot render them)" if skipped else ""
        print(f"{label}: {len(texts) - len({t for t, _ in failures})}/{len(texts)} identical with kerning on and off{note}")
        for t, mode in failures[:report]:
            a, b = (rk(t), tk(t)) if mode == "kerning on" else (rs(t), ts(t))
            print(f"   {t!r} ({mode}): width {a[1]} vs {b[1]}")
        ok &= not failures

    check("sample texts", SAMPLES)
    check("every shared character, alone and between letters",
          [t for c in shared for t in (chr(c), "n" + chr(c) + "n", "o" + chr(c) + "H")])
    if "kern" in R:
        rev = {}
        for c, n in sorted(rc.items()):
            rev.setdefault(n, c)
        pairs = [(rev.get(a), rev.get(b)) for table in R["kern"].kernTables for (a, b) in table.kernTable]
        pair_texts = [chr(a) + chr(b) for a, b in pairs if a in tc and b in tc]
        # each pair alone, in words, and with a mark or a joiner between
        # (marks and default-ignorables change whether a legacy pair applies)
        check("the reference's kerning pairs, alone and in context",
              [ctx.format(t) for t in pair_texts for ctx in KERN_CONTEXTS]
              + [t[0] + mark + t[1] for t in pair_texts for mark in ("\u0301", "\u0308", "\u200d", "\u00ad")])
    arabic = [c for c in shared if 0x620 <= c <= 0x6FF and unicodedata.category(chr(c)) == "Lo"]
    check("Arabic letters in every joining position",
          [t for c in arabic for t in (chr(c), chr(c) + "ـ", "ـ" + chr(c) + "ـ", "ـ" + chr(c),
                                       "ب" + chr(c) + "ب", chr(c) + "لا")])
    marks = ["\u064E", "\u064F", "\u0650", "\u0651", "\u0652", "\u064B", "\u0651\u064E", "\u0653", "\u0654", "\u0670"]
    ligature_texts = ["\u0627\u0644\u0644\u0651\u0670\u0647", "\u0644\u200d\u0627", "\u0644\u200c\u0627", "\u0628\u200d", "\u200d\u0628", "\u0644\u0640\u0627"]
    for m in marks:
        for alef in ("\u0627", "\u0622", "\u0623", "\u0625"):
            ligature_texts += ["\u0644" + m + alef, "\u0628\u0644" + m + alef, "\u0644" + alef + m]
        ligature_texts += ["\u0627\u0644\u0644" + m + "\u0647", "\u0627\u0644" + m + "\u0644\u0647", "\u0627\u0644\u0644\u0647" + m, "\u0628" + m + "\u0628" + m + "\u0628"]
    check("Arabic lam-alef and Allah ligatures with marks in between, and joining controls", ligature_texts)

    # Pages can switch layout features off (CSS font-variant-ligatures: none
    # turns off liga, clig, dlig and calt; font-feature-settings any tag).
    # Taquoma must make the same substitutions as the reference under each,
    # so its ligatures have to sit in the same features as the reference's.
    feature_texts = SAMPLES + ligature_texts + [t for c in arabic for t in (chr(c) + "لا", "ب" + chr(c) + "ب")]
    switched = [("liga", "clig", "dlig", "calt")] + [(tag,) for tag in ("liga", "rlig", "ccmp", "locl", "isol", "init", "medi", "fina")]
    broken = []
    for off in switched:
        for kern in (True, False):
            rf, tf = Shaper(ref_path, kern=kern, off=off), Shaper(path, kern=kern, off=off)
            texts = [t for t in feature_texts if rf.renders(t)]
            broken += [(off, t) for t in texts if not same_layout(rf(t), tf(t))]
    print(f"with layout features switched off ({len(switched)} settings, ligatures off as in CSS font-variant-ligatures: none): "
          f"{len(broken)} texts set differently")
    for off, t in broken[:report]:
        print(f"   {'+'.join(off)} off: {t!r}")
    ok &= not broken
    # Shaping zeroes mark advances, so the checks above can't see a mark
    # glyph's own stored width, or a ligature of marks one font forms and the
    # other doesn't. So compare the glyphs shaping produces directly: in each
    # character cluster, the same number of glyphs with the same stored
    # (hmtx) advances. Text whose composed form the font lacks is left out:
    # HarfBuzz builds it from parts there (U+06D5 + U+0654 for U+06C0), with
    # the same layout, which the checks above confirm.
    def glyph_runs(font, path):
        order, hm = font.getGlyphOrder(), font["hmtx"]
        shaper = hb.Font(hb.Face(hb.Blob.from_file_path(path)))
        def run(text):
            buf = hb.Buffer()
            buf.add_str(text)
            buf.guess_segment_properties()
            hb.shape(shaper, buf, {})
            out = {}
            for info in buf.glyph_infos:
                out.setdefault(info.cluster, []).append(hm[order[info.codepoint]][0])
            return {k: sorted(v) for k, v in out.items()}
        return run
    rg, tg = glyph_runs(R, ref_path), glyph_runs(T, path)
    mn = [c for c in shared if unicodedata.category(chr(c)) == "Mn"]
    arabic_marks = [c for c in mn if 0x064B <= c <= 0x065F or c == 0x0670]
    glyph_texts = [chr(c) for c in shared] + [b + chr(m) for m in mn for b in ("o", "ב", "ب")]
    glyph_texts += [chr(c) + chr(m) for c in arabic for m in arabic_marks]
    glyph_texts += [chr(c) + chr(m1) + chr(m2) for c in arabic + [0x0621] if c in tc for m1 in arabic_marks for m2 in arabic_marks]
    glyph_texts = [t for t in glyph_texts if rs.renders(t) and all(ord(x) in tc for x in unicodedata.normalize("NFC", t))]
    glyph_bad = [t for t in glyph_texts if rg(t) != tg(t)]
    print(f"glyphs produced by shaping (marks and mark ligatures included): {len(glyph_texts) - len(glyph_bad)}/{len(glyph_texts)} "
          f"texts with the same glyphs per character and the same stored widths")
    for t in glyph_bad[:report]:
        print(f"   {' '.join(f'U+{ord(x):04X}' for x in t)}: reference {rg(t)}, Taquoma {tg(t)}")
    ok &= not glyph_bad

    composable = [c for c in range(0x20, 0x30000) if not 0xD800 <= c <= 0xDFFF and c not in rc]
    composable = [c for c in composable
                  if unicodedata.normalize("NFD", chr(c)) != chr(c)
                  and all(ord(x) in rc for x in unicodedata.normalize("NFD", chr(c)))]
    check(f"{len(composable)} characters the reference lacks but sets by canonical equivalent (base + mark, or a singleton like the Kelvin sign)",
          [ctx.format(form) for c in composable for ctx in KERN_CONTEXTS
           for form in (chr(c), unicodedata.normalize("NFD", chr(c)))])

    # --- Width relationships within Taquoma.
    adv = lambda c: T["hmtx"][tc[c]][0]
    rules = [(0x2007, ord("0"), "figure space = digit"), (0x2012, ord("0"), "figure dash = digit"),
             (0x2008, ord("."), "punctuation space = period"), (0x2010, ord("-"), "hyphen = hyphen-minus"),
             (0x2011, ord("-"), "non-breaking hyphen = hyphen-minus"), (0x00A0, ord(" "), "no-break space = space")]
    broken = [f"{label} ({adv(a)} vs {adv(b)})" for a, b, label in rules if a in tc and b in tc and adv(a) != adv(b)]
    for code, width in ((0x2000, 1024), (0x2001, 2048), (0x2002, 1024), (0x2003, 2048), (0x2004, 683), (0x2005, 512), (0x2006, 341)):
        if code in tc and adv(code) != width:
            broken.append(f"U+{code:04X} {adv(code)} vs {width}")
    def digit_sets(cmap):
        sets = {}
        for c in cmap:
            if unicodedata.digit(chr(c), None) is not None:
                n = unicodedata.name(chr(c), "")
                key = "superscript/subscript" if ("SUPERSCRIPT" in n or "SUBSCRIPT" in n) else " ".join(
                    w for w in n.split() if w not in ("ZERO", "ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX", "SEVEN", "EIGHT", "NINE", "DIGIT"))
                sets.setdefault(key, []).append(c)
        sets["vulgar fractions"] = [c for c in cmap if "VULGAR FRACTION" in unicodedata.name(chr(c), "")
                                    and len(unicodedata.normalize("NFKD", chr(c))) == 3]
        return sets
    for key, cs in digit_sets(tc).items():
        ref_widths = {R["hmtx"][rc[c]][0] for c in cs if c in rc}
        widths = {adv(c) for c in cs}
        if len(ref_widths) == 1 and widths != ref_widths:
            broken.append(f"{key}: widths {sorted(widths)}, the reference's {sorted(ref_widths)}")
        elif not ref_widths and source is not None and len(widths) > 1:
            sc = source.getBestCmap()
            if len({source["hmtx"][sc[c]][0] for c in cs if c in sc}) == 1:
                broken.append(f"{key}: one width in the source font, now {sorted(widths)}")
    spacing_marks = [c for c in tc if unicodedata.category(chr(c)) == "Mn" and adv(c) != 0
                     and not (c in rc and R["hmtx"][rc[c]][0] == adv(c))]
    broken += [f"combining mark U+{c:04X} has an advance of {adv(c)}" for c in spacing_marks]
    print(f"width relationships (figure/punctuation spaces, hyphens, em spaces, digit sets, fractions, zero-width marks): {len(broken)} broken")
    for b in broken[:report]:
        print(f"   {b}")
    ok &= not broken

    # --- Outline quality (informational).
    crossing = [c for c in shared if T["glyf"][tc[c]].numberOfContours > 0 and crossing_contours(T, tc[c])]
    print(f"contours crossing themselves: {len(crossing)} shared glyphs {' '.join(f'U+{c:04X}' for c in crossing[:report])}")

    # Outline hygiene: no contour drawn twice, no parts overlapping (they
    # render, but some tools and printers show seams), outer contours
    # clockwise as TrueType expects, no zero-length segments.
    from fontTools.pens.areaPen import AreaPen
    tgs = T.getGlyphSet()
    overlapping, reversed_, repeated, duplicated = [], [], [], []
    for name in T.getGlyphOrder():
        g = T["glyf"][name]
        if g.numberOfContours <= 0:
            continue
        pen = AreaPen(tgs)
        tgs[name].draw(pen)
        if pen.value > 0:
            reversed_.append(name)
        coords = g.getCoordinates(T["glyf"])[0]
        start, seen = 0, set()
        for end in g.endPtsOfContours:
            pts = [tuple(p) for p in coords[start:end + 1]]
            if any(a == b for a, b in zip(pts, pts[1:] + pts[:1])):
                repeated.append(name)
            if tuple(pts) in seen:
                duplicated.append(name)
            seen.add(tuple(pts))
            start = end + 1
        if g.numberOfContours > 1:
            path = pathops.Path()
            tgs[name].draw(path.getPen())
            area = abs(pen.value)
            path.simplify(fix_winding=True)
            if area > 0 and abs(abs(path.area) - area) > 0.002 * area + 4:
                overlapping.append(name)
    for label, names in (("overlapping contours", overlapping), ("anticlockwise outer contours", reversed_),
                         ("contours drawn twice", duplicated), ("repeated points (zero-length segments)", repeated)):
        names = sorted(set(names))
        print(f"{label}: {len(names)} glyphs {' '.join(names[:report])}")
        ok &= not names

    # Dots keep their shape (with --source): a square dot that came out as a
    # dash or a sliver (more than 1.45 times off its proportions in the
    # source font) can read as another mark, such as a kasra.
    if source is not None:
        import importlib.util
        spec = importlib.util.spec_from_file_location("make_taquoma", os.path.join(os.path.dirname(os.path.abspath(__file__)), "make_taquoma.py"))
        mt = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mt)
        sc, sg = source.getBestCmap(), source["glyf"]
        distorted, compared = [], 0
        for c in shared:
            if c not in sc:
                continue
            before = [(d[2] - d[1]) / (d[4] - d[3]) for d in mt.dot_parts(sg[sc[c]], 2048)]
            if not before:
                continue
            now = mt.dot_parts(T["glyf"][tc[c]], 2048, square=False, margin=0)
            if len(now) != len(before):
                continue
            compared += 1
            if any(max(((d[2] - d[1]) / (d[4] - d[3])) / r, r / ((d[2] - d[1]) / (d[4] - d[3]))) > 1.45 for d, r in zip(now, before)):
                distorted.append(f"U+{c:04X}")
        print(f"dots out of proportion (vs the source font): {len(distorted)} of {compared} characters with dots {' '.join(distorted[:report])}")
        ok &= not distorted

    # Accented letters should contain their base letter exactly, where the
    # base letter has it (the accent then sits over the letter as designed),
    # or moved sideways as a whole where the accented letter is wider (the
    # Greek capitals with tonos). Bases a mark is joined to (cedilla, ogonek,
    # horn, dagesh) are expected here; anything else is a misplaced or
    # reshaped body.
    def contour_set(name, dx=0):
        g = T["glyf"][name]
        coords, out, start = g.getCoordinates(T["glyf"])[0], set(), 0
        for end in g.endPtsOfContours:
            out.add(tuple((x + dx, y) for x, y in coords[start:end + 1]))
            start = end + 1
        return out

    def contains(name, base):
        here = contour_set(name)
        shifts = {0}
        if T["hmtx"][name][0] != T["hmtx"][base][0]:
            first = next(iter(contour_set(base)))
            shifts |= {c[0][0] - first[0][0] for c in here if len(c) == len(first)}
        return any(contour_set(base, dx) <= here for dx in shifts)
    dotless = {0x69: 0x131, 0x6A: 0x237, 0x456: 0x131, 0x458: 0x237}
    displaced = []
    for c in sorted(tc):
        nfd = unicodedata.normalize("NFD", chr(c))
        if c in dotless:
            base = dotless[c]
        elif len(nfd) > 1 and all(unicodedata.category(m) == "Mn" for m in nfd[1:]):
            base = dotless.get(ord(nfd[0]), ord(nfd[0]))
        else:
            continue
        if base not in tc or unicodedata.category(chr(base)) not in ("Lu", "Ll", "Lt", "Lo"):
            continue
        if T["glyf"][tc[c]].numberOfContours > 0 and T["glyf"][tc[base]].numberOfContours > 0 and not contains(tc[c], tc[base]):
            displaced.append(c)
    print(f"accented letters not containing their base letter exactly, in place (mostly marks joined to the letter): "
          f"{len(displaced)} {''.join(chr(c) for c in displaced[:80])}")

    def box(font, name):
        g = font["glyf"][name]
        if g.numberOfContours == 0:
            return None
        g.recalcBounds(font["glyf"])
        return g.xMin, g.xMax, g.yMin, g.yMax
    top, bottom = T["OS/2"].usWinAscent, -T["OS/2"].usWinDescent
    clipped, overhang, devs = [], [], []
    for c in shared:
        a, b = box(R, rc[c]), box(T, tc[c])
        if not b:
            continue
        if (b[3] > top and (not a or a[3] <= top)) or (b[2] < bottom and (not a or a[2] >= bottom)):
            clipped.append(c)
        adv = T["hmtx"][tc[c]][0]
        if a and adv > 0 and unicodedata.category(chr(c))[0] in "LNPS":
            excess = max(min(a[0], 0) - b[0], b[1] - max(a[1], adv))
            if excess > 2:
                overhang.append((excess, c))
        if a:
            d = [b[i] - a[i] for i in range(4)]
            devs.append((max(abs(v) for v in d), c, d))
    print(f"reaching past the Windows clipping box where the reference does not: {len(clipped)} "
          f"{' '.join(f'U+{c:04X}' for c in clipped[:report])}")
    encoded = set(tc.values())
    unencoded_clipped = [n for n in T.getGlyphOrder()[1:] if n not in encoded and (b := box(T, n))
                         and (b[3] > top or b[2] < bottom)]
    print(f"contextual forms and other unencoded glyphs reaching past the clipping box: {len(unencoded_clipped)} "
          f"{' '.join(unencoded_clipped[:report])}")
    ok &= not unencoded_clipped
    overhang.sort(reverse=True)
    print(f"reaching past the advance further than the reference (letters, digits, punctuation, symbols; by more than 2 units): "
          f"{len(overhang)}{f', at most {overhang[0][0]:.0f} units' if overhang else ''} "
          f"{' '.join(f'{chr(c)}:{e:.0f}' for e, c in overhang[:report])}")
    devs.sort(reverse=True)
    print(f"ink boxes: median max-edge deviation {statistics.median(v for v, _, _ in devs):.0f} units, "
          f"{sum(1 for v, _, _ in devs if v <= 20)}/{len(devs)} within 20 units (1% em)")
    for v, c, d in devs[:report]:
        print(f"   U+{c:04X} {chr(c)!r} dxMin {d[0]:+} dxMax {d[1]:+} dyMin {d[2]:+} dyMax {d[3]:+}")
    print("RESULT:", "metric-compatible" if ok else "DIFFERENCES FOUND")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
