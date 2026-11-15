#!/usr/bin/env python3
"""extract_metrics.py REGULAR.ttf BOLD.ttf OUT.json

Reads the measurements Taquoma reproduces from a reference family, so the
faces can be rebuilt from the JSON without the reference fonts at hand.
Only numbers are recorded, keyed by Unicode code point (never by the
reference's glyph names): no outlines, no hinting instructions, no names.

Per style:
  glyphs   code point -> [advance] for blank glyphs, or
                         [advance, xMin, xMax, yMin, yMax] (ink box)
  notdef   metrics of the missing-glyph box (glyph 0), shown for characters
           the font lacks where no other font is substituted
  classes  GDEF glyph class (1 base, 2 ligature, 3 mark) by code point
  forms    Arabic contextual forms (isol/init/medi/fina): feature -> code
           point -> metrics of the glyph the feature substitutes
  formClasses  GDEF class of those substituted glyphs
  markLigatures  ligatures of combining marks (Arabic shadda + vowel sign):
           feature -> the marks' code points in ligature order, e.g.
           "0651 064E" -> metrics of the ligature glyph
  markLigatureClasses  GDEF class of those ligature glyphs
  sharedGlyphs  groups of code points the reference draws with one glyph
  hhea / OS/2 / post   vertical metrics and line positions; the OS/2
           family class and the Unicode-range and code-page bits (the
           scripts the font declares, which some apps choose fonts by)
  kern     the legacy 'kern' table's pairs as [first, second, value] by
           code point (a glyph with several code points gives a pair for
           each), so text kerned by a layout engine lands in the same place

Adapted from Fauxdana's scripts/extract_metrics.py (SIL OFL 1.1)."""
import json
import sys
import unicodedata
from fontTools.ttLib import TTFont


def glyph_metrics(font, name):
    glyf, hmtx = font["glyf"], font["hmtx"]
    advance, _ = hmtx[name]
    g = glyf[name]
    if g.numberOfContours == 0 and not g.isComposite():
        return [advance]
    g.recalcBounds(glyf)
    return [advance, g.xMin, g.xMax, g.yMin, g.yMax]


def metrics(path):
    font = TTFont(path)
    cmap = font.getBestCmap()
    encoded = {}
    for code, name in cmap.items():
        encoded.setdefault(name, code)

    glyphs = {f"{code:04X}": glyph_metrics(font, name) for code, name in sorted(cmap.items())}

    # GDEF glyph classes (1 base, 2 ligature, 3 mark) by code point: shaping
    # engines zero mark advances and skip marks by these, so the derived face
    # must classify the same characters the same way to lay out the same.
    classes, glyph_class = {}, {}
    if "GDEF" in font and font["GDEF"].table.GlyphClassDef:
        glyph_class = font["GDEF"].table.GlyphClassDef.classDefs
        for code, name in sorted(cmap.items()):
            if glyph_class.get(name):
                classes[f"{code:04X}"] = glyph_class[name]

    # Contextual forms (Arabic joining): the glyph each feature turns a code
    # point into, whether or not that glyph has a code point of its own.
    forms, form_classes = {}, {}
    if "GSUB" in font:
        gsub = font["GSUB"].table
        for record in gsub.FeatureList.FeatureRecord:
            tag = record.FeatureTag
            if tag not in ("isol", "init", "medi", "fina"):
                continue
            for index in record.Feature.LookupListIndex:
                for sub in gsub.LookupList.Lookup[index].SubTable:
                    for source, target in getattr(sub, "mapping", {}).items():
                        if source in encoded:
                            key = f"{encoded[source]:04X}"
                            forms.setdefault(tag, {})[key] = glyph_metrics(font, target)
                            if glyph_class.get(target):
                                form_classes.setdefault(tag, {})[key] = glyph_class[target]

    # Ligatures of combining marks (Arabic shadda + vowel sign): feature ->
    # the marks' code points, in the order the ligature takes them -> metrics
    # of the ligature glyph. The derived face forms only these, with these
    # widths and ink boxes.
    mark_ligatures, mark_ligature_classes = {}, {}
    if "GSUB" in font:
        gsub = font["GSUB"].table
        feature_of = {}
        for record in gsub.FeatureList.FeatureRecord:
            for index in record.Feature.LookupListIndex:
                feature_of.setdefault(index, record.FeatureTag)
        for index, lookup in enumerate(gsub.LookupList.Lookup):
            for sub in lookup.SubTable:
                if lookup.LookupType == 7:
                    sub = sub.ExtSubTable
                for first, ligatures in getattr(sub, "ligatures", {}).items():
                    for lig in ligatures:
                        parts = [first] + list(lig.Component)
                        if not all(p in encoded and unicodedata.category(chr(encoded[p])) == "Mn" for p in parts):
                            continue
                        key = " ".join(f"{encoded[p]:04X}" for p in parts)
                        tag = feature_of.get(index)
                        if tag is None:
                            continue                      # in no feature: never applied
                        mark_ligatures.setdefault(tag, {})[key] = glyph_metrics(font, lig.LigGlyph)
                        if glyph_class.get(lig.LigGlyph):
                            mark_ligature_classes[key] = glyph_class[lig.LigGlyph]

    # Code points the reference draws with one shared glyph (the space and
    # no-break space, private-use U+F001 and the fi ligature, ...).
    shared = {}
    for code, name in sorted(cmap.items()):
        shared.setdefault(name, []).append(code)
    shared_glyphs = [codes for codes in shared.values() if len(codes) > 1]

    # Kerning pairs by code point. Every code point a glyph has gets the
    # pair (the reference uses one glyph for the hyphen and the soft hyphen).
    codes_of = {}
    for code, name in sorted(cmap.items()):
        codes_of.setdefault(name, []).append(code)
    kern, unencoded = [], 0
    if "kern" in font:
        for table in font["kern"].kernTables:
            if getattr(table, "format", 0) != 0 or (table.coverage & 0b111) != 1:
                # only plain horizontal format 0 pairs (not minimum or cross-stream values)
                print(f"WARNING {path}: a 'kern' subtable (format {getattr(table, 'format', '?')}, "
                      f"coverage {table.coverage}) is not read; verify.py will show its pairs as differences")
                continue
            for (left, right), value in sorted(table.kernTable.items()):
                if left not in codes_of or right not in codes_of:
                    unencoded += 1
                    continue
                kern += [[a, b, value] for a in codes_of[left] for b in codes_of[right]]
    if unencoded:
        print(f"{path}: {unencoded} kerning pairs between glyphs without code points left out")
    if "GPOS" in font:
        # Tahoma 3.x has no GPOS. A later version that kerns through GPOS would need its pairs read
        # from there; until then verify.py reports any pair it moves (it checks with kerning on).
        print(f"WARNING {path}: has a GPOS table, whose positioning (kerning included) is not read")

    hhea, os2, post = font["hhea"], font["OS/2"], font["post"]
    return {
        "unitsPerEm": font["head"].unitsPerEm,
        "hhea": {"ascent": hhea.ascent, "descent": hhea.descent, "lineGap": hhea.lineGap},
        "OS/2": {f: getattr(os2, f) for f in (
            "sTypoAscender", "sTypoDescender", "sTypoLineGap", "usWinAscent", "usWinDescent",
            "xAvgCharWidth", "yStrikeoutSize", "yStrikeoutPosition",
            "ySubscriptXSize", "ySubscriptYSize", "ySubscriptXOffset", "ySubscriptYOffset",
            "ySuperscriptXSize", "ySuperscriptYSize", "ySuperscriptXOffset", "ySuperscriptYOffset",
            "sFamilyClass", "ulUnicodeRange1", "ulUnicodeRange2", "ulUnicodeRange3", "ulUnicodeRange4",
            "ulCodePageRange1", "ulCodePageRange2")},
        "post": {"underlinePosition": post.underlinePosition, "underlineThickness": post.underlineThickness},
        "notdef": glyph_metrics(font, font.getGlyphOrder()[0]),
        "glyphs": glyphs,
        "classes": classes,
        "forms": forms,
        "formClasses": form_classes,
        "markLigatures": mark_ligatures,
        "markLigatureClasses": mark_ligature_classes,
        "sharedGlyphs": shared_glyphs,
        "kern": sorted(kern),
    }


def main():
    regular, bold, out = sys.argv[1:4]
    data = {"source": "advance widths, ink extents, vertical metrics and kerning of the reference family, by code point",
            "regular": metrics(regular), "bold": metrics(bold)}
    with open(out, "w") as f:
        json.dump(data, f, indent=0, sort_keys=True)
        f.write("\n")
    for k in ("regular", "bold"):
        d = data[k]
        print(f"{k}: {len(d['glyphs'])} code points, {sum(len(v) for v in d['forms'].values())} contextual forms, "
              f"{sum(len(v) for v in d['markLigatures'].values())} mark ligatures, {len(d['kern'])} kerning pairs")


if __name__ == "__main__":
    main()
