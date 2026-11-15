#!/bin/sh
# Rebuild Taquoma Regular and Bold into ttfs/ (and WOFF2 into webfonts/) from
# the Fauxdana TTFs and the DejaVu Sans TTFs Fauxdana was built from (2.37;
# used for the Arabic joining tables only). Run from anywhere:
#   scripts/build.sh /path/to/fauxdana/ttfs /usr/share/fonts/truetype/dejavu
set -eu
fauxdana=${1:?usage: build.sh FAUXDANA_TTF_DIR DEJAVU_TTF_DIR}
dejavu=${2:?usage: build.sh FAUXDANA_TTF_DIR DEJAVU_TTF_DIR}
root=$(cd "$(dirname "$0")/.." && pwd)
py=${PYTHON:-python3}
make="$py $root/scripts/make_taquoma.py"
metrics="$root/tahoma-metrics.json"
mkdir -p "$root/ttfs" "$root/webfonts"
$make "$fauxdana/Fauxdana-Regular.ttf" "$metrics" "$root/ttfs/Taquoma-Regular.ttf"        --layout-from "$dejavu/DejaVuSans.ttf"
$make "$fauxdana/Fauxdana-Bold.ttf"    "$metrics" "$root/ttfs/Taquoma-Bold.ttf"    --bold --layout-from "$dejavu/DejaVuSans-Bold.ttf"
# The WOFF2 keeps the TTF's modification date (a fresh one on every build
# would make the web fonts differ from build to build).
for style in Regular Bold; do
    $py -c "import sys; from fontTools.ttLib import TTFont; f = TTFont(sys.argv[1], recalcTimestamp=False); f.flavor = 'woff2'; f.save(sys.argv[2])" \
        "$root/ttfs/Taquoma-$style.ttf" "$root/webfonts/Taquoma-$style.woff2"
done
