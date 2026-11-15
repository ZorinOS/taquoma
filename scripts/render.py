#!/usr/bin/env python3
"""render.py OUT.png SIZE_PX "label=font.ttf" ["label=font.ttf" ...] [--overlay] [--hinted] [--no-kern] [--text FILE]

Sets the sample lines in each font with HarfBuzz (so kerning and Arabic
joining apply) and FreeType, one block per sample line: each font on its own
row, plus (with --overlay) both drawn on top of each other in red and blue,
which shows any horizontal drift as colour fringes."""
import sys
import freetype
import numpy
import uharfbuzz as hb
from PIL import Image, ImageDraw, ImageFont

LOAD_FLAGS = freetype.FT_LOAD_DEFAULT | freetype.FT_LOAD_NO_HINTING

LINES = [
    "Hamburgefonstiv HOH nnoonn 0123456789",
    "The quick brown fox jumps over the lazy dog.",
    "AVATAR Toyota WAVE Yo. \"Quoted\" (parens) [x] {y} @#$%&*?!",
    "Ærøskøbing façade naïve Ångström Łódź Žižkov ijsje",
    "Tiếng Việt: ở ữ ặ ễ ỵ — Привет, мир! Съешь ещё",
    "Ξεσκεπάζω την ψυχοφθόρα βδελυγμία — שלום עולם",
    "مرحبا بالعالم — سلام عليكم",
]


FEATURES = {}


def setline(path, text, size):
    face = hb.Face(hb.Blob.from_file_path(path))
    font = hb.Font(face)
    upem = face.upem
    buf = hb.Buffer()
    buf.add_str(text)
    buf.guess_segment_properties()
    hb.shape(font, buf, FEATURES)
    ft = freetype.Face(path)
    ft.set_pixel_sizes(0, size)
    scale = size / upem
    glyphs, x = [], 0.0
    for info, pos in zip(buf.glyph_infos, buf.glyph_positions):
        glyphs.append((info.codepoint, x + pos.x_offset * scale, pos.y_offset * scale))
        x += pos.x_advance * scale
    return ft, glyphs, x


def draw(ft, glyphs, canvas, ox, baseline, colour):
    for gid, x, y in glyphs:
        ft.load_glyph(gid, LOAD_FLAGS)
        ft.glyph.render(freetype.FT_RENDER_MODE_NORMAL)
        bm = ft.glyph.bitmap
        if bm.width == 0:
            continue
        mask = Image.frombytes("L", (bm.width, bm.rows), bytes(bm.buffer))
        px = round(ox + x + ft.glyph.bitmap_left)
        py = round(baseline - y - ft.glyph.bitmap_top)
        canvas.paste(Image.new("RGB", mask.size, colour), (px, py), mask)


def main():
    argv = sys.argv[1:]
    overlay = "--overlay" in argv
    lines = LINES
    if "--text" in argv:
        with open(argv[argv.index("--text") + 1]) as f:
            lines = [l.rstrip("\n") for l in f if l.strip()]
        argv = [a for i, a in enumerate(argv) if a != "--text" and (i == 0 or argv[i - 1] != "--text")]
    argv = [a for a in argv if a != "--overlay"]
    global LOAD_FLAGS
    if "--no-kern" in argv:          # as with CSS font-kerning: none
        FEATURES["kern"] = False
        argv.remove("--no-kern")
    if "--hinted" in argv:          # TrueType bytecode, as on a hinting rasteriser
        LOAD_FLAGS = freetype.FT_LOAD_DEFAULT | freetype.FT_LOAD_TARGET_NORMAL
        argv.remove("--hinted")
    out, size, fonts = argv[0], int(argv[1]), [a.split("=", 1) for a in argv[2:]]
    label_w = 150
    row = int(size * 1.45)
    rows_per_line = len(fonts) + (1 if overlay else 0)
    widths = []
    for text in lines:
        for _, path in fonts:
            widths.append(setline(path, text, size)[2])
    W = int(max(widths)) + label_w + 40
    H = len(lines) * (rows_per_line * row + size // 2) + 20
    img = Image.new("RGB", (W, H), "white")
    d = ImageDraw.Draw(img)
    try:
        lab = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 14)
    except OSError:
        lab = ImageFont.load_default()
    y = 10
    colours = [(200, 30, 30), (20, 60, 200)]
    for text in lines:
        set_ = [(label, setline(path, text, size)) for label, path in fonts]
        for label, (ft, glyphs, width) in set_:
            baseline = y + int(size * 1.05)
            d.text((10, baseline - 14), label, fill=(110, 110, 110), font=lab)
            draw(ft, glyphs, img, label_w, baseline, (0, 0, 0))
            d.line([(label_w + width, y + 4), (label_w + width, baseline + 6)], fill=(0, 170, 0))
            y += row
        if overlay:
            baseline = y + int(size * 1.05)
            d.text((10, baseline - 14), "overlay", fill=(110, 110, 110), font=lab)
            over = Image.new("RGB", (W, row), "white")
            for i, (label, (ft, glyphs, width)) in enumerate(set_[:2]):
                layer = Image.new("RGB", (W, row), "white")
                draw(ft, glyphs, layer, label_w, int(size * 1.05), colours[i])
                over = Image.fromarray(numpy.minimum(numpy.asarray(over), numpy.asarray(layer)))
            img.paste(over, (0, y))
            y += row
        y += size // 2
    img.save(out)
    print(out, img.size)


if __name__ == "__main__":
    main()
