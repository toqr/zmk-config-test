#!/usr/bin/env python3
"""
zmk_visualizer.py - turn a ZMK .keymap or a QMK keymap.c into a 2-page PDF.

    python3 zmk_visualizer.py my.keymap                 # ZMK:  writes my.pdf
    python3 zmk_visualizer.py keymap.c                  # QMK:  writes keymap.pdf
    python3 zmk_visualizer.py keymap.c --split no       # QMK board that is one block of keys (no gap in the middle)
    python3 zmk_visualizer.py my.keymap -o out.pdf --open
    python3 zmk_visualizer.py my.keymap --rows 10,10,10,4   # only if the key rows can't be detected
    python3 zmk_visualizer.py keymap.c --no-video       # skip the video (see below)

Give ONE file: a ZMK .keymap or a QMK keymap.c. The kind is taken from the file ending (.keymap = ZMK,
.c = QMK; --format overrides it). The file is looked for in the "config" folder (then in the current
folder, where a QMK keymap.c usually is); leave the name out and the one .keymap (or .c) file there is used.

Besides the PDF it writes, next to it:
    current-keymap.pdf                            - a copy of the PDF you just made
    previous-keymaps-visualizer/keymap-YYYY-MM-DD.pdf - a dated copy, so you can look back
    preview.png                                   - a snapshot of the flow chart (page 1)
Use --no-archive to write only the PDF, and --preview-scale to change the zoom of the snapshot.
The snapshot is scaled down when needed so that it stays below the size at which image tools
refuse to open it; the PDF itself is vector, so it stays sharp at any zoom.

Page 1 - FLOW CHART. Every layer is a node, placed left to right by how many steps it is from the base
         layer; the layers of one column are stacked and lined up with the layers they connect to.
         The columns are arranged so that as many arrows as possible point to the right: an arrow
         always comes in on the LEFT side of the layer it leads to, at the height of its name,
         and it stops AT the frame - it never crosses it, and it never comes in from the top.
         Each arrow starts ON the key that triggers it and leaves the layer through its bottom
         edge; a key that is not in the bottom row is left at the side of the card that is
         closest to it and the line runs down the margin of the card, so that it never has to
         cross the keyboard. The keys of a combo are marked with a dot and joined up under the
         layer, and every arrow that has to go around a column gets a lane of its own, so
         that no two lines lie on top of each other. The arrows then use the gap under the layer to spread out. The lanes are handed out in the order the
         keys are in and the arrows that go up take the top of the gap, the ones that go down the
         bottom, so the lines run parallel instead of crossing each other. Where two lines do meet,
         the one on top is given a dark outline, so you can still follow it. Several arrows that
         leave the same key get a little space between them, so they do not run on top of each other.
         An arrow that has to point back (a cycle in the keymap) goes under all the layers in
         one wide rounded loop and comes up on the left again.
         The name of a layer is always on the LEFT of its name plate, and the frame of every
         layer is thick, so the card reads as a frame and not as a key.
         A "&tog N" key on layer N switches back to the layer you came from, so it is drawn
         as an arrow that circles back underneath the layers.
         An arrow is coloured like the layer it leads to; several arrows to the same layer get
         different shades of that colour, so they can be told apart. Arrows are solid for hold and
         dashed for toggle / go to / one-shot; "combo" means the keys are pressed together.
         PINK keys are layer keys; the RED key(s) on a layer are the ones you must be holding to be
         there. Both get a bright rim, so they stand out on the dark card.
         A pink key is a key you press to go to another layer, a violet key is a key that
         toggles a layer on and off, and a red key is a key that has to be held down while
         you are on that layer - so only a temporary (momentary) layer has red keys. The
         keys pile up along the way: a layer that you reach through two momentary layers
         has two red keys, and a layer that you reach with a combo has one red key per
         key of the combo. The media keys that ZMK knows (mute, volume and brightness)
         are drawn as little symbols.
         A "how to read" panel explains the colours. Combos are drawn at the bottom as mini
         keyboards (red = keys pressed together).
Page 2 - ZMK: the whole keymap as text, with every comment removed.
         QMK: the keymap.c as it is, with its comments removed.

QMK keymaps: the layers come from `keymaps[]` (LAYOUT(...) macros or a raw matrix) and are named after
the layer enum / #defines. Understood: KC_* keycodes, MO / TG / TO / OSL / TT / DF / LM / LT, mod-taps
(LSFT_T(), MT(), ...), modifier wrappers (LCTL(KC_C), S(KC_1)), OSM, tap dance (TD), #define macros
(also variadic row macros), custom keycodes that turn a layer on in process_record_user, COMBO(...)
(keys are looked up on the base layer) and update_tri_layer_state(), which is drawn like a ZMK
conditional layer. The result goes through the same drawing code as a ZMK keymap.

VIDEO: every run also writes video/<keyboard>-<date>.mp4 (a folder called video next to the PDF), a 60 FPS H.264
video of the flow chart being drawn. The arrows are drawn one after the other,
following the connections: first the arrows that leave the base layer, then - as soon as a layer has been
reached - the arrows that leave that layer. Every arrow follows its exact path from the key that triggers it to
the layer it leads to, with its own colour, width, dashes, rounded corners and label; the chart itself is never
redrawn (the video reveals pixels of the normal render), and the last frame is the finished chart as it is in the
PDF. The video is 3840 px wide with the aspect ratio of the page, 8-9 seconds long, and under 2 MB. It takes about
30 seconds; use --no-video to skip it. When numpy, scipy, Pillow, pdftoppm or ffmpeg is missing the PDF is still
written and the video is skipped with a note.

Standard library only for the PDF (the video also needs numpy, scipy, Pillow, pdftoppm and ffmpeg).
Comments in the .keymap (including boxed/aligned ones) are ignored.
"""
import argparse
import copy
import itertools
import math
import re
import shutil
import subprocess
import sys
import tempfile
import webbrowser
import zlib
from collections import defaultdict, deque
from datetime import date, datetime
from pathlib import Path


# --------------------------------------------------------------------------- parsing
def strip_comments(t):
    t = re.sub(r"/\*.*?\*/", "", t, flags=re.S)
    return re.sub(r"//[^\n]*", "", t)


_ONE_LINE_BLOCK = re.compile(r"/\*(?:(?!\*/)[^\n])*\*/")
SPLIT_MARK = "\x01"


def strip_comments_marked(t):
    """Like strip_comments, but a one-line /* ... */ comment is kept as a marker: it is
    often put between the two halves of a keyboard, and tells where the split is."""
    t = _ONE_LINE_BLOCK.sub(SPLIT_MARK, t)
    return strip_comments(t)


def _call_args(s, j):
    """s[j] == '(' -> ([arguments], index after the closing ')') - or (None, j) if it never closes."""
    depth, args, cur, k = 0, [], "", j
    while k < len(s):
        ch = s[k]
        if ch == "(":
            depth += 1
            if depth > 1:
                cur += ch
        elif ch == ")":
            depth -= 1
            if depth == 0:
                args.append(cur)
                return args, k + 1
            cur += ch
        elif ch == "," and depth == 1:
            args.append(cur)
            cur = ""
        else:
            cur += ch
        k += 1
    return None, j


def _expand(s, objs, funcs, blocked=frozenset(), depth=0):
    """Expand #define macros (object-like and function-like, with ## pasting), like the C preprocessor."""
    if depth > 40:
        return s
    out, pos = [], 0
    for m in re.finditer(r"[A-Za-z_]\w*", s):
        if m.start() < pos:
            continue
        name = m.group(0)
        if name in blocked:
            continue
        if name in funcs:
            j = m.end()
            while j < len(s) and s[j] in " \t":
                j += 1
            if j < len(s) and s[j] == "(":
                args, end = _call_args(s, j)
                if args is not None:
                    params, body = funcs[name]
                    mp = {p: a.strip() for p, a in zip(params, args)}
                    body = re.sub(r"[A-Za-z_]\w*", lambda mm: mp.get(mm.group(0), mm.group(0)), body)
                    body = re.sub(r"\s*##\s*", "", body)
                    out += [s[pos:m.start()], _expand(body, objs, funcs, blocked | {name}, depth + 1)]
                    pos = end
        elif name in objs:
            out += [s[pos:m.start()], _expand(objs[name], objs, funcs, blocked | {name}, depth + 1)]
            pos = m.end()
    out.append(s[pos:])
    return "".join(out)


def preprocess(t):
    """Resolve #define macros so that `G_A`, `COMBO(...)` or `TYPING_LAYERS` become what they stand for.
    -> (expanded text, {macro: plain number}, set of macros that expand to a whole binding)"""
    t = re.sub(r"\\[ \t]*\n", " ", t)
    objs, funcs, keep = {}, {}, []
    for line in t.split("\n"):
        m = re.match(r"\s*#\s*define\s+(\w+)(\(([^)]*)\))?[ \t]*(.*)$", line)
        if m:
            body = m.group(4).replace(SPLIT_MARK, " ").strip()
            if m.group(3) is not None:
                funcs[m.group(1)] = ([p.strip() for p in m.group(3).split(",") if p.strip()], body)
            else:
                objs[m.group(1)] = body
            keep.append("")
        elif re.match(r"\s*#\s*(include|if|ifdef|ifndef|else|elif|endif|undef|pragma)\b", line):
            keep.append("")
        else:
            keep.append(line)
    parts = re.split(r'("[^"\n]*")', "\n".join(keep))          # never touch text inside quotes
    text = "".join(p if i % 2 else _expand(p, objs, funcs) for i, p in enumerate(parts))
    numbers, starts = {}, set()
    for name, body in objs.items():
        v = _expand(body, objs, funcs, frozenset({name})).strip()
        if re.fullmatch(r"-?\d+", v):
            numbers[name] = int(v)
        if v.startswith("&"):
            starts.add(name)
    return text, numbers, starts


def parse_nodes(body):
    """Return [(header, inner_body)] for the child nodes found at depth 0 of `body`."""
    out, i, n = [], 0, len(body)
    while i < n:
        j = body.find("{", i)
        if j < 0:
            break
        k = max(body.rfind(";", i, j), body.rfind("}", i, j))
        header = body[(k + 1 if k >= 0 else i):j]
        lines = [l for l in header.splitlines() if l.strip()]
        header = lines[-1].strip() if lines else ""
        depth, p = 1, j + 1
        while p < n and depth:
            depth += {"{": 1, "}": -1}.get(body[p], 0)
            p += 1
        out.append((header, body[j + 1:p - 1]))
        i = p
    return out


def find_node(nodes, name):
    for header, body in nodes:
        if header.split(":")[-1].strip() == name:
            return body
        found = find_node(parse_nodes(body), name)
        if found is not None:
            return found
    return None


BINDING_STARTS = set()          # macro names that stand for a whole binding (set while parsing)
ROW_LEFTS = None                # keys on the left half of each row, when the file shows where the split is


BUILTIN_CELLS = {"kp": 1, "kt": 1, "mo": 1, "to": 1, "tog": 1, "sl": 1, "sk": 1, "lt": 2, "mt": 2, "mkp": 1,
                 "mmv": 1, "msc": 1, "trans": 0, "none": 0, "bootloader": 0, "sys_reset": 0, "caps_word": 0,
                 "key_repeat": 0, "gresc": 0, "out": 1}


def cells_of(binding):
    """How many parameters the behaviour of this binding takes, or None when that is not known."""
    beh = binding.split()[0].lstrip("&")
    if beh in BEH and BEH[beh].get("cells") is not None:
        return BEH[beh]["cells"]
    return BUILTIN_CELLS.get(beh)


def split_bindings(line):
    """'&kp Q &mo 1 &kp LG(Z)' -> ['&kp Q', '&mo 1', '&kp LG(Z)']"""
    merged, buf = [], ""
    for tok in line.split():
        buf = f"{buf} {tok}" if buf else tok
        if buf.count("(") <= buf.count(")"):
            merged.append(buf)
            buf = ""
    if buf:
        merged.append(buf)
    out = []
    for tok in merged:
        if tok.startswith("&") or tok in BINDING_STARTS or not out:
            out.append(tok)
        elif re.fullmatch(r"[A-Za-z_]\w*", tok) and cells_of(out[-1]) is not None \
                and len(out[-1].split()) - 1 >= cells_of(out[-1]):
            out.append("&kp " + tok)           # a macro that is not defined in this file (U_MS_U): a key of its own
        else:
            out[-1] += " " + tok
    return out


def split_marked(line):
    """A line of bindings -> (bindings, number of keys left of the split marker or None)."""
    groups = [split_bindings(g.strip()) for g in line.split(SPLIT_MARK)]
    groups = [g for g in groups if g]
    toks = [b for g in groups for b in g]
    if len(groups) < 2:
        return toks, None
    cuts, n = [], 0
    for g in groups[:-1]:
        n += len(g)
        cuts.append(n)
    return toks, min(cuts, key=lambda k: abs(k - len(toks) / 2))


def guess_rows(total):
    for cols in (12, 10, 6, 5, 4):
        rest = total - 3 * cols
        if 0 < rest <= 8:
            return [cols] * 3 + [rest]
    return [total]


# --------------------------------------------------------------------------- zmk-helpers macros
# Many keymaps (urob's zmk-config and everything built on the zmk-helpers module) do not write
# `keymap { ... }` / `behaviors { ... }` nodes. They call macros - ZMK_LAYER(), ZMK_HOLD_TAP(),
# ZMK_MOD_MORPH(), ZMK_CONDITIONAL_LAYER(), ZMK_COMBO() ... - that a header from a module turns into
# those nodes. That header is not part of the keymap file, so the macros are expanded here.
_ZH_BEH = {"HOLD_TAP": "zmk,behavior-hold-tap", "MOD_MORPH": "zmk,behavior-mod-morph",
           "TAP_DANCE": "zmk,behavior-tap-dance", "MACRO": "zmk,behavior-macro",
           "MACRO_ONE_PARAM": "zmk,behavior-macro-one-param", "MACRO_TWO_PARAM": "zmk,behavior-macro-two-param",
           "TRI_STATE": "zmk,behavior-tri-state", "ADAPTIVE_KEY": "zmk,behavior-adaptive-key"}
_ZH_CELLS = {"HOLD_TAP": 2, "MACRO_ONE_PARAM": 1, "MACRO_TWO_PARAM": 2}          # the others take no parameter
_ZH = re.compile(r"\bZMK_(LAYER|CONDITIONAL_LAYER|COMBO(?:_\d+)?|" + "|".join(sorted(_ZH_BEH, key=len, reverse=True)) + r")\s*\(")


def inline_local_includes(text, folder, depth=0):
    """`#include "combos.dtsi"` -> the content of that file, when it sits next to the keymap."""
    def one(m):
        f = Path(folder) / m.group(1)
        if depth < 4 and f.is_file():
            try:
                return inline_local_includes(f.read_text(errors="replace"), f.parent, depth + 1)
            except OSError:
                pass
        return m.group(0)
    return re.sub(r'^[ \t]*#[ \t]*include[ \t]+"([^"\n]+)"[^\n]*$', one, text, flags=re.M)


def zmk_combo_dispatch(src):
    """zmk-helpers picks ZMK_COMBO_<n> by the number of arguments; a keymap may redefine one of them."""
    mine = set(re.findall(r"#\s*define\s+ZMK_COMBO_(\d+)\s*\(", src))
    if not mine:
        return src
    out, pos = [], 0
    for m in re.finditer(r"\bZMK_COMBO\s*\(", src):
        if m.start() < pos:
            continue
        args, end = _call_args(src, m.end() - 1)
        if args is not None and str(len(args)) in mine:
            out += [src[pos:m.start()], f"ZMK_COMBO_{len(args)}("]
            pos = m.end()
    out.append(src[pos:])
    return "".join(out)


def zmk_helpers(clean):
    """Expand the zmk-helpers macros left in the preprocessed text into plain devicetree nodes."""
    if not _ZH.search(clean):
        return clean
    out, pos = [], 0
    layer_nodes, beh_nodes, combo_nodes, cond_nodes = [], [], [], []
    for m in _ZH.finditer(clean):
        if m.start() < pos:
            continue
        args, end = _call_args(clean, m.end() - 1)
        if args is None:
            continue
        kind, name = m.group(1), (args[0].strip() if args else "")
        rest = ",".join(args[1:])
        if kind == "LAYER" and len(args) >= 2:
            layer_nodes.append(f"{name} {{ bindings = <{' '.join(a.strip() for a in args[1:])}>; }};")
        elif kind == "CONDITIONAL_LAYER" and len(args) >= 3:
            cond_nodes.append(f"{name} {{ if-layers = <{args[1].strip()}>; then-layer = <{args[2].strip()}>; }};")
        elif kind.startswith("COMBO") and len(args) >= 4:
            pos_toks = args[2].replace(SPLIT_MARK, " ").split()
            if not all(re.fullmatch(r"\d+", t) for t in pos_toks):
                print(f"warning: combo {name}: its key positions ({' '.join(pos_toks)}) are labels from a "
                      f"key-label header, which is not in the file - it is left out", file=sys.stderr)
            else:
                lay = " ".join(re.findall(r"-?\d+", args[3]))
                tmo = args[4].strip() if len(args) > 4 and re.fullmatch(r"\s*\d+\s*", args[4]) else ""
                combo_nodes.append(
                    f"{name} {{ key-positions = <{' '.join(pos_toks)}>; bindings = <{args[1].strip()}>;"
                    + (f" layers = <{lay}>;" if lay else "") + (f" timeout-ms = <{tmo}>;" if tmo else "") + " };")
        elif kind in _ZH_BEH:
            beh_nodes.append(f'{name}: {name} {{ compatible = "{_ZH_BEH[kind]}"; '
                             f'#binding-cells = <{_ZH_CELLS.get(kind, 0)}>; {rest} }};')
        else:
            continue
        out.append(clean[pos:m.start()])
        pos = end
    out.append(clean[pos:])
    gen = []
    if layer_nodes:
        gen.append('keymap { compatible = "zmk,keymap"; ' + " ".join(layer_nodes) + " };")
    if beh_nodes:
        gen.append("behaviors { " + " ".join(beh_nodes) + " };")
    if combo_nodes:
        gen.append('combos { compatible = "zmk,combos"; ' + " ".join(combo_nodes) + " };")
    if cond_nodes:
        gen.append('conditional_layers { compatible = "zmk,conditional-layers"; ' + " ".join(cond_nodes) + " };")
    return "".join(out) + "\n/ { " + " ".join(gen) + " };\n"


CONDITIONAL = []   # conditional layers: [{"name", "ifs": [layers], "then": layer}]
LEADER = {"keys": set(), "seqs": []}   # QMK leader key: keycode names, and [{"seq": "L Q", "kind", "layer"}]
BEH = {}        # behaviours defined in the file: label -> {"compat", "bindings", "mode"}


def parse_behaviors(root):
    BEH.clear()

    def walk(nodes):
        for header, body in nodes:
            comp = re.search(r'compatible\s*=\s*"([^"]*)"', body)
            if comp and "behavior" in comp.group(1) and ":" in header:
                bd = re.search(r"\bbindings\s*=\s*([^;]*);", body)
                mode = re.search(r'toggle-mode\s*=\s*"([^"]*)"', body)
                cells = re.search(r"#binding-cells\s*=\s*<(\d+)>", body)
                BEH[header.split(":")[0].strip()] = {
                    "compat": comp.group(1),
                    "cells": int(cells.group(1)) if cells else None,
                    "bindings": re.findall(r"&(\w+)", bd.group(1)) if bd else [],
                    "raw": [x.strip() for x in re.findall(r"<([^>]*)>", bd.group(1))] if bd else [],
                    "mode": mode.group(1) if mode else "toggle"}
            walk(parse_nodes(body))
    walk(root)


def parse_keymap(text, forced_rows=None, base_dir=None):
    global BINDING_STARTS, ROW_LEFTS
    if base_dir is not None:                           # #include "combos.dtsi" next to the keymap
        text = inline_local_includes(text, base_dir)
    clean, defines, BINDING_STARTS = preprocess(zmk_combo_dispatch(strip_comments_marked(text)))
    clean = zmk_helpers(clean)
    root = parse_nodes(clean)
    parse_behaviors(root)
    keymap_body = find_node(root, "keymap")
    if keymap_body is None:
        sys.exit("error: no `keymap { ... }` node found in the file")

    layers, lefts0 = [], None
    for header, body in parse_nodes(keymap_body):
        m = re.search(r"\bbindings\s*=\s*<(.*?)>\s*;", body, re.S)
        if not m:
            continue
        name = header.split(":")[-1].strip()
        dn = re.search(r'(?:display-name|label)\s*=\s*"([^"]*)"', body)
        parsed = [split_marked(l) for l in m.group(1).splitlines() if l.replace(SPLIT_MARK, "").strip()]
        lines = [p[0] for p in parsed]
        if not layers:
            lefts0 = [p[1] for p in parsed]
        layers.append({"idx": len(layers), "name": name, "title": dn.group(1) if dn else name,
                       "lines": lines, "flat": [b for l in lines for b in l]})
    if not layers:
        sys.exit("error: no layers with `bindings = < ... >;` found")
    if len(layers) > 1 and all(re.search(r"[_-]layer$", L["name"]) for L in layers):
        for L in layers:                                  # "macro_layer" -> "macro": shorter, easier to read
            L["name"] = re.sub(r"[_-]layer$", "", L["name"])

    ROW_LEFTS = None
    if forced_rows:
        row_lens = forced_rows
        QMK_INFO[:] = ["rows given with --rows"]
    else:
        first = [len(l) for l in layers[0]["lines"]]
        has_marks = bool(lefts0 and any(k is not None for k in lefts0))
        if len(first) > 1 and has_marks:                # medium: halves marked with /* */ in the file
            row_lens = first
            ROW_LEFTS = [k if k is not None else n // 2 for k, n in zip(lefts0, row_lens)]
            QMK_INFO[:] = ["medium", "from the line breaks and the /* */ markers in the file"]
        elif len(first) >= 6 and qmk_pair_halves(first) and first[-1] < first[0] and len(set(first[:-2])) == 1:
            row_lens, ROW_LEFTS = qmk_pair_halves(first)  # medium: lines come in equal pairs (left, right half)
            QMK_INFO[:] = ["medium", "lines come in equal pairs (left half, right half), with a shorter last pair"]
        elif len(first) > 1:                            # medium: the rows as they are written
            row_lens = first
            QMK_INFO[:] = ["medium", "from the line breaks in the file"]
        else:                                           # low: only the number of keys is known
            row_lens = guess_rows(len(layers[0]["flat"]))
            QMK_INFO[:] = ["low", f"guessed from the number of keys ({len(layers[0]['flat'])}); use --rows to set it"]
    total = sum(row_lens)
    for L in layers:
        flat = L["flat"]
        if len(flat) != total:
            print(f"warning: layer {L['idx']} ({L['name']}) has {len(flat)} keys, expected {total}",
                  file=sys.stderr)
            flat = (flat + ["&none"] * total)[:total]
        L["flat"], it = flat, iter(flat)
        L["rows"] = [[next(it) for _ in range(n)] for n in row_lens]

    combos = []
    combos_body = find_node(root, "combos")
    for header, body in (parse_nodes(combos_body) if combos_body else []):
        body = body.replace(SPLIT_MARK, " ")
        kp = re.search(r"key-positions\s*=\s*<([^>]*)>", body)
        bd = re.search(r"\bbindings\s*=\s*<([^>]*)>", body)
        if not (kp and bd):
            continue
        if not all(re.fullmatch(r"\d+", t) for t in kp.group(1).split()):
            continue                                   # key labels (LT1 ...) that could not be resolved
        ly = re.search(r"\blayers\s*=\s*<([^>]*)>", body)
        to = re.search(r"timeout-ms\s*=\s*<(\d+)>", body)
        nm = header.split(":")[-1].strip()
        combos.append({"name": nm[6:] if nm.startswith("combo_") else nm,
                       "positions": [int(x) for x in re.findall(r"\d+", kp.group(1))],
                       "binding": " ".join(bd.group(1).split()),
                       "layers": [int(x) for x in re.findall(r"-?\d+", ly.group(1)) if int(x) >= 0] if ly else None,
                       "timeout": int(to.group(1)) if to else None})
    CONDITIONAL.clear()
    LEADER["keys"], LEADER["seqs"] = set(), []
    cl_body = find_node(root, "conditional_layers")
    for header, body in (parse_nodes(cl_body) if cl_body else []):
        ifs = re.search(r"if-layers\s*=\s*<([^>]*)>", body)
        then = re.search(r"then-layer\s*=\s*<\s*(\d+)\s*>", body)
        if ifs and then:
            CONDITIONAL.append({"name": header.split(":")[-1].strip(),
                                "ifs": [int(x) for x in re.findall(r"\d+", ifs.group(1))],
                                "then": int(then.group(1))})
    return layers, combos, row_lens, defines


# --------------------------------------------------------------------------- labels
ICON_MUTE = "\U0001F507"       # speaker with a cross
ICON_VOL_DN = "\U0001F508"     # speaker, one wave
ICON_VOL_UP = "\U0001F50A"     # speaker, two waves
ICON_BR_DN = "\U0001F505"      # sun, outline
ICON_BR_UP = "\U0001F506"      # sun, filled
MEDIA_ICONS = (ICON_MUTE, ICON_VOL_DN, ICON_VOL_UP, ICON_BR_DN, ICON_BR_UP)
KP = {
    "ESC": "Esc", "GRAVE": "`", "TILDE": "~", "TAB": "Tab", "DELETE": "Del", "DEL": "Del",
    "MINUS": "-", "EQUAL": "=", "BACKSPACE": "Bksp", "BSPC": "Bksp", "CAPSLOCK": "Caps",
    "LEFT": "←", "DOWN": "↓", "UP": "↑", "RIGHT": "→", "ENTER": "Enter", "RET": "Enter",
    "SPACE": "Space", "SEMICOLON": ";", "SEMI": ";", "COMMA": ",", "DOT": ".", "SLASH": "/", "FSLH": "/",
    "SQT": "'", "APOS": "'", "DOUBLE_QUOTES": '"', "DQT": '"', "LEFT_BRACE": "{", "LBRC": "{",
    "RIGHT_BRACE": "}", "RBRC": "}", "LEFT_BRACKET": "[", "LBKT": "[", "RIGHT_BRACKET": "]",
    "RBKT": "]", "LEFT_PARENTHESIS": "(", "LPAR": "(", "RIGHT_PARENTHESIS": ")", "RPAR": ")",
    "BACKSLASH": "\\", "BSLH": "\\", "PIPE": "|", "UNDERSCORE": "_", "PLUS": "+", "STAR": "*",
    "EXCLAMATION": "!", "AT_SIGN": "@", "HASH": "#", "DOLLAR": "$", "PERCENT": "%", "CARET": "^",
    "AMPERSAND": "&", "COLON": ":", "LESS_THAN": "<", "GREATER_THAN": ">", "QUESTION": "?",
    "HOME": "Home", "END": "End", "PG_UP": "PgUp", "PG_DN": "PgDn", "INSERT": "Ins",
    "PRINTSCREEN": "PrtSc", "K_APP": "Menu",
    "LSHIFT": "Shift", "LEFT_SHIFT": "Shift", "RSHIFT": "RShift", "RIGHT_SHIFT": "RShift",
    "LSHFT": "Shift", "RSHFT": "RShift", "LSFT": "Shift", "RSFT": "RShift", "LCTL": "Ctrl", "RCTL": "RCtrl",
    "LWIN": "Win", "RWIN": "RWin", "LCMD": "Cmd", "RCMD": "RCmd", "LCTRL": "Ctrl", "LEFT_CONTROL": "Ctrl", "RCTRL": "RCtrl", "RIGHT_CONTROL": "RCtrl",
    "LALT": "Alt", "LEFT_ALT": "Alt", "RALT": "RAlt", "RIGHT_ALT": "RAlt",
    "LGUI": "GUI", "LEFT_GUI": "GUI", "LEFT_WIN": "Win", "LEFT_COMMAND": "Cmd",
    "RGUI": "RGUI", "RIGHT_GUI": "RGUI", "RIGHT_WIN": "RWin", "RIGHT_COMMAND": "RCmd",
    "KP_DIVIDE": "KP /", "KP_MULTIPLY": "KP *", "KP_MINUS": "KP -", "KP_SUBTRACT": "KP -",
    "KP_PLUS": "KP +", "KP_ENTER": "KP Enter", "KP_DOT": "KP .", "KP_EQUAL": "KP =",
    "K_PP": "Play/Pause", "K_PLAY_PAUSE": "Play/Pause", "K_NEXT": "Next", "K_PREVIOUS": "Prev",
    "K_MUTE": ICON_MUTE, "K_VOL_UP": ICON_VOL_UP, "K_VOLUME_UP": ICON_VOL_UP,
    "K_VOL_DN": ICON_VOL_DN, "K_VOLUME_DOWN": ICON_VOL_DN, "C_BRI_UP": ICON_BR_UP, "C_BRI_DN": ICON_BR_DN,
    "C_NEXT": "Next", "C_PREVIOUS": "Prev", "C_PLAY_PAUSE": "Play/Pause", "C_PP": "Play/Pause",
    "C_MUTE": ICON_MUTE, "MUTE": ICON_MUTE,
    "C_VOLUME_UP": ICON_VOL_UP, "C_VOL_UP": ICON_VOL_UP, "VOL_UP": ICON_VOL_UP,
    "VOLUME_UP": ICON_VOL_UP,
    "C_VOLUME_DOWN": ICON_VOL_DN, "C_VOL_DN": ICON_VOL_DN, "VOL_DN": ICON_VOL_DN,
    "VOLUME_DOWN": ICON_VOL_DN,
    "C_BRIGHTNESS_INC": ICON_BR_UP, "C_BRI_UP": ICON_BR_UP, "BRIGHTNESS_UP": ICON_BR_UP,
    "C_BRIGHTNESS_DEC": ICON_BR_DN, "C_BRI_DN": ICON_BR_DN, "BRIGHTNESS_DOWN": ICON_BR_DN,
    "C_STOP": "Stop", "C_PREV": "Prev", "QMARK": "?", "EXCL": "!", "LT": "<", "GT": ">", "K_CANCEL": "Cancel",
}
MODFN = {"S": "Shift", "C": "Ctrl", "A": "Alt", "G": "GUI"}
ARROW = {"LEFT": "←", "DOWN": "↓", "UP": "↑", "RIGHT": "→"}
MKP = {"MB1": "Btn 1", "MB2": "Btn 2", "MB3": "Btn 3", "MB4": "Btn 4", "MB5": "Btn 5",
       "LCLK": "Left Click", "RCLK": "Right Click", "MCLK": "Mid Click"}


SHIFTED = {"N1": "!", "N2": "@", "N3": "#", "N4": "$", "N5": "%", "N6": "^", "N7": "&", "N8": "*",
           "N9": "(", "N0": ")", "MINUS": "_", "EQUAL": "+", "SEMI": ":", "SQT": '"', "COMMA": "<",
           "DOT": ">", "FSLH": "?", "LBKT": "{", "RBKT": "}", "BSLH": "|", "GRAVE": "~"}


QMK_TEXT = {}                   # QMK keys: code used inside a binding -> the text drawn on the key


def kp_label(code):
    if code in QMK_TEXT:
        return QMK_TEXT[code]
    m = re.fullmatch(r"([LR])([SCAG])\((.+)\)", code)
    if m and m.group(2) == "S" and m.group(3) in SHIFTED:
        return SHIFTED[m.group(3)]                  # LS(N9) is just "("
    if m:
        return ("R" if m.group(1) == "R" else "") + MODFN[m.group(2)] + "+" + kp_label(m.group(3))
    if code in KP:
        return KP[code]
    if re.fullmatch(r"[A-Z]", code):
        return code
    if re.fullmatch(r"N\d|NUMBER_\d", code):
        return code[-1]
    if re.fullmatch(r"F\d+", code):
        return code
    m = re.fullmatch(r"KP_N(?:UMBER_)?(\d)", code)
    if m:
        return "KP " + m.group(1)
    return code.replace("_", " ").title()


def label(binding):
    """-> (main label, small raw text)"""
    p = binding.split()
    beh, arg = p[0].lstrip("&"), p[1:]
    raw = binding
    try:
        if beh == "kp":
            return kp_label(arg[0]), raw
        if beh == "sk":
            return "Sticky " + kp_label(arg[0]), raw
        if beh == "mo":
            return f"Hold L{arg[0]}", raw
        if beh == "tog":
            return f"Toggle L{arg[0]}", raw
        if beh == "to":
            return f"Go to L{arg[0]}", raw
        if beh == "sl":
            return f"1-shot L{arg[0]}", raw
        if beh == "lt":
            return f"{kp_label(arg[1])}·L{arg[0]}", raw
        if beh == "mt":
            return f"{kp_label(arg[1])}·{kp_label(arg[0])}", raw
        if beh == "trans":
            return "▽", raw
        if beh == "none":
            return "—", raw
        if beh == "sys_reset":
            return "RESET", raw
        if beh == "bootloader":
            return "BOOT", raw
        if beh == "bt":
            return ("BT " + arg[1]) if len(arg) > 1 else ("BT " + arg[0].replace("BT_", "")), raw
        if beh == "msc":
            return "Scroll " + ARROW.get(arg[0].split("_")[-1], arg[0]), raw
        if beh == "mmv":
            return "Move " + ARROW.get(arg[0].split("_")[-1], arg[0]), raw
        if beh == "mkp":
            return MKP.get(arg[0], arg[0]), raw
        if beh == "out":
            return {"OUT_USB": "USB", "OUT_BLE": "BLE", "OUT_TOG": "USB/BLE"}.get(arg[0], arg[0]), raw
        if beh in BEH and "toggle-layer" in BEH[beh]["compat"]:
            return ("Layer off" if BEH[beh]["mode"] == "off" else "Layer on") + f" L{arg[0]}", raw
        if beh == "caps_word":
            return "CapsWord", raw
        if beh == "key_repeat":
            return "Repeat", raw
    except (IndexError, KeyError):
        pass
    if arg:
        return kp_label(arg[-1]), raw
    return beh, raw


LAYER_BEH = {"mo": "hold", "tog": "toggle", "to": "switch", "sl": "oneshot"}
KIND_TEXT = {"hold": "hold", "toggle": "toggle", "switch": "switch to", "oneshot": "one-shot",
             "taphold": "hold (tap-hold)", "off": "turn off"}
HELD_KINDS = ("hold", "taphold")


def holdtap(beh):
    """A hold-tap behaviour -> (behaviour used on hold, behaviour used on tap), else None."""
    if beh == "lt":
        return "mo", "kp"
    if beh == "mt":
        return "kp", "kp"
    b = BEH.get(beh)
    if b and "hold-tap" in b["compat"] and len(b["bindings"]) >= 2:
        return b["bindings"][0], b["bindings"][1]
    return None


def is_toggle_key(binding):
    beh = binding.split()[0].lstrip("&")
    return beh == "tog" or (beh in BEH and "toggle-layer" in BEH[beh]["compat"])


def layer_action(binding, defines):
    """-> (kind, target layer) or None"""
    p = binding.split()
    beh = p[0].lstrip("&")
    if len(p) < 2:
        return None
    tok = p[1]
    tgt = int(tok) if tok.isdigit() else defines.get(tok)
    if tgt is None:
        return None
    ht = holdtap(beh)
    if ht:                                           # a layer-tap: tap = key, hold = layer
        if ht[0] not in LAYER_BEH:
            return None
        return ("taphold" if ht[0] == "mo" else LAYER_BEH[ht[0]]), tgt
    if beh in BEH and "toggle-layer" in BEH[beh]["compat"]:
        return ("off" if BEH[beh]["mode"] == "off" else "toggle"), tgt
    if beh in LAYER_BEH:
        return LAYER_BEH[beh], tgt
    return None


# --------------------------------------------------------------------------- graph
def build_edges(layers, combos, defines):
    n = len(layers)
    nkeys = len(layers[0]["flat"]) if layers else 0
    grouped, self_toggles = {}, defaultdict(list)
    for L in layers:
        for pos, b in enumerate(L["flat"]):
            act = layer_action(b, defines)
            if not act or not (0 <= act[1] < n):
                continue
            kind, dst = act
            if dst == L["idx"]:
                self_toggles[L["idx"]].append(pos)
                continue
            if kind == "off":                         # turning another layer off is no way to get anywhere
                continue
            grouped.setdefault((L["idx"], dst, kind, "key", ""), []).append(pos)
    for c in combos:
        act = layer_action(c["binding"], defines)
        if not act or not (0 <= act[1] < n):
            continue
        kind, dst = act
        if kind == "off":
            continue
        # a combo may name a key that this board does not have: skip the ones that
        # are not there, and skip the combo entirely when none of them are
        pos = [p for p in c["positions"] if 0 <= p < nkeys]
        if not pos:
            print(f"warning: combo {c['name']} uses key positions that do not exist",
                  file=sys.stderr)
            continue
        for src in (c["layers"] if c["layers"] else [0]):
            if src != dst and 0 <= src < n:
                grouped.setdefault((src, dst, kind, "combo", c["name"]), pos)
    # QMK leader key: LEADER, then a key sequence, changes the layer. The arrow starts on the LEADER key(s)
    if LEADER["seqs"]:
        for L in layers:
            raw = L.get("raw") or []
            lpos = [p for p, t in enumerate(raw) if str(t).strip() in LEADER["keys"]]
            if not lpos:
                continue
            for sq in LEADER["seqs"]:
                dst = sq["layer"]
                if not (0 <= dst < n) or dst == L["idx"]:
                    continue
                kind = "switch" if sq["kind"] == "to" else "toggle"
                grouped.setdefault((L["idx"], dst, kind, "leader", sq["seq"]), lpos)
    edges = []
    for (src, dst, kind, via, name), pos in grouped.items():
        edges.append({"id": f"e{len(edges)}", "src": src, "dst": dst, "kind": kind,
                      "via": via, "name": name, "positions": pos})
    # conditional layers: when all the `if-layers` are on, the `then-layer` turns on by itself.
    # No key is involved, so these arrows start on the name plate of the layer (position nkeys)
    for cl in CONDITIONAL:
        ifs = [i for i in cl["ifs"] if 0 <= i < n]
        if not (0 <= cl["then"] < n) or len(ifs) < 2:
            continue
        for src in ifs:
            if src != cl["then"]:
                edges.append({"id": f"e{len(edges)}", "src": src, "dst": cl["then"], "kind": "cond",
                              "via": "cond", "name": "+".join(str(i) for i in ifs), "positions": [nkeys]})
    return edges, self_toggles


def bfs(n, edges):
    depth, prev = {0: 0}, {0: None}
    q = deque([0])
    while q:
        u = q.popleft()
        for e in edges:
            if e["src"] == u and e["dst"] not in depth:
                depth[e["dst"]] = depth[u] + 1
                prev[e["dst"]] = e
                q.append(e["dst"])
    for _ in range(n):                  # a conditional layer sits after all the layers it needs
        moved = False
        for e in edges:
            if e["kind"] == "cond" and e["dst"] in depth and e["src"] in depth \
                    and depth[e["dst"]] <= depth[e["src"]]:
                depth[e["dst"]] = depth[e["src"]] + 1
                moved = True
                for e2 in edges:        # and whatever is reached through it moves along
                    if prev.get(e2["dst"]) is e2 and e2["src"] == e["dst"] and depth[e2["dst"]] <= depth[e2["src"]]:
                        depth[e2["dst"]] = depth[e2["src"]] + 1
        if not moved:
            break
    extra = max(depth.values()) + 1
    for i in range(n):
        depth.setdefault(i, extra)
    return depth, prev


def path_to(L, prev):
    out = []
    while prev.get(L):
        out.append(prev[L])
        L = prev[L]["src"]
    return out[::-1]


# --------------------------------------------------------------------------- fonts
# Helvetica-Bold advance widths (per 1000 em) for ASCII 32..126, so text can be centred exactly.
HB = [278, 333, 474, 556, 556, 889, 722, 238, 333, 333, 389, 584, 278, 333, 278, 278, 556, 556, 556, 556,
      556, 556, 556, 556, 556, 556, 333, 333, 584, 584, 584, 611, 975, 722, 722, 722, 722, 667, 611, 778,
      722, 278, 556, 722, 611, 833, 722, 778, 667, 778, 722, 667, 611, 722, 667, 944, 667, 667, 611, 333,
      278, 333, 584, 556, 333, 556, 611, 556, 611, 556, 333, 611, 611, 278, 278, 556, 278, 889, 611, 611,
      611, 611, 389, 556, 333, 611, 556, 778, 556, 556, 500, 389, 280, 389, 584]
GLYPHS = "←→↑↓▽" + ICON_MUTE + ICON_VOL_DN + ICON_VOL_UP + ICON_BR_DN + ICON_BR_UP
FONTRES = {"sans": "F3", "mono": "F1", "monob": "F2"}


def tw(s, size, font="sans"):
    """Text width in points."""
    if font != "sans":
        return 0.6 * size * len(s)
    return size * sum(700 if ch in GLYPHS else HB[ord(ch) - 32] if 32 <= ord(ch) <= 126 else 600
                      for ch in s) / 1000


# --------------------------------------------------------------------------- tiny PDF writer
class Canvas:
    """One PDF page. Coordinates: origin top-left, y grows downward."""

    def __init__(self, w, h, bg=None):
        self.w, self.h, self.ops = w, h, []
        if bg:
            self.rect(0, 0, w, h, fill=bg)

    @staticmethod
    def rgb(c):
        return " ".join(f"{int(c[i:i + 2], 16) / 255:.3f}" for i in (1, 3, 5))

    def _y(self, y):
        return self.h - y

    def _paint(self, fill, stroke, sw):
        if fill:
            self.ops.append(f"{self.rgb(fill)} rg")
        if stroke:
            self.ops.append(f"{self.rgb(stroke)} RG {sw:.2f} w")
        self.ops.append("B" if fill and stroke else "f" if fill else "S")

    def rect(self, x, y, w, h, fill=None, stroke=None, sw=1.0, r=0.0):
        r = min(r, w / 2, h / 2)
        x0, y0 = x, self.h - y - h
        if r <= 0:
            self.ops.append(f"{x0:.2f} {y0:.2f} {w:.2f} {h:.2f} re")
        else:
            k = r * 0.5523
            f = lambda *v: " ".join(f"{n:.2f}" for n in v)
            self.ops += [
                f(x0 + r, y0) + " m", f(x0 + w - r, y0) + " l",
                f(x0 + w - r + k, y0, x0 + w, y0 + r - k, x0 + w, y0 + r) + " c",
                f(x0 + w, y0 + h - r) + " l",
                f(x0 + w, y0 + h - r + k, x0 + w - r + k, y0 + h, x0 + w - r, y0 + h) + " c",
                f(x0 + r, y0 + h) + " l",
                f(x0 + r - k, y0 + h, x0, y0 + h - r + k, x0, y0 + h - r) + " c",
                f(x0, y0 + r) + " l", f(x0, y0 + r - k, x0 + r - k, y0, x0 + r, y0) + " c", "h",
            ]
        self._paint(fill, stroke, sw)

    def circle(self, cx, cy, r, fill=None, stroke=None, sw=1.0):
        k, f = r * 0.5523, lambda *v: " ".join(f"{n:.2f}" for n in v)
        x, y = cx, self._y(cy)
        self.ops += [f(x + r, y) + " m",
                     f(x + r, y + k, x + k, y + r, x, y + r) + " c",
                     f(x - k, y + r, x - r, y + k, x - r, y) + " c",
                     f(x - r, y - k, x - k, y - r, x, y - r) + " c",
                     f(x + k, y - r, x + r, y - k, x + r, y) + " c", "h"]
        self._paint(fill, stroke, sw)

    def poly(self, pts, color, sw=1.0, closed=False, fill=None, dash=None):
        self.ops.append(f"{self.rgb(color)} RG {sw:.2f} w 1 J 1 j" + (f" [{dash[0]} {dash[1]}] 0 d" if dash else ""))
        if fill:
            self.ops.append(f"{self.rgb(fill)} rg")
        for i, (x, y) in enumerate(pts):
            self.ops.append(f"{x:.2f} {self._y(y):.2f} {'m' if i == 0 else 'l'}")
        self.ops.append(("b" if fill else "s") if closed else "S")
        if dash:
            self.ops.append("[] 0 d")

    def line(self, x1, y1, x2, y2, color, sw=1.0, dash=None):
        self.poly([(x1, y1), (x2, y2)], color, sw, dash=dash)

    def rpath(self, pts, color, sw=2.0, dash=None, r=24):
        """Polyline with rounded corners."""
        self.ops.append(f"{self.rgb(color)} RG {sw:.2f} w 1 J 1 j" + (f" [{dash[0]} {dash[1]}] 0 d" if dash else ""))
        P = lambda p: f"{p[0]:.2f} {self._y(p[1]):.2f}"
        self.ops.append(f"{P(pts[0])} m")
        for i in range(1, len(pts) - 1):
            a, b, c = pts[i - 1], pts[i], pts[i + 1]
            la, lc = math.hypot(a[0] - b[0], a[1] - b[1]), math.hypot(c[0] - b[0], c[1] - b[1])
            rr = min(r, la / 2, lc / 2)
            if rr < 0.5:
                self.ops.append(f"{P(b)} l")
                continue
            p1 = (b[0] + (a[0] - b[0]) / la * rr, b[1] + (a[1] - b[1]) / la * rr)
            p2 = (b[0] + (c[0] - b[0]) / lc * rr, b[1] + (c[1] - b[1]) / lc * rr)
            self.ops.append(f"{P(p1)} l {P(b)} {P(b)} {P(p2)} c")
        self.ops.append(f"{P(pts[-1])} l S")
        if dash:
            self.ops.append("[] 0 d")

    def curve(self, p0, c1, c2, p1, color, sw=2.0, dash=None):
        self.ops.append(f"{self.rgb(color)} RG {sw:.2f} w 1 J 1 j" + (f" [{dash[0]} {dash[1]}] 0 d" if dash else ""))
        P = lambda p: f"{p[0]:.2f} {self._y(p[1]):.2f}"
        self.ops.append(f"{P(p0)} m {P(c1)} {P(c2)} {P(p1)} c S")
        if dash:
            self.ops.append("[] 0 d")

    def _show(self, x, y, run, size, color, font):
        s = run.encode("cp1252", "replace").decode("latin-1")
        s = s.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")
        self.ops.append(f"{self.rgb(color)} rg BT /{FONTRES[font]} {size:.2f} Tf {x:.2f} {self._y(y):.2f} Td ({s}) Tj ET")

    def _glyph(self, cx, base, ch, size, color):
        cy, L, H, sw = base - 0.3 * size, 0.28 * size, 0.18 * size, max(0.8, size * 0.12)
        if ch == "→":
            self.poly([(cx - L, cy), (cx + L, cy)], color, sw)
            self.poly([(cx + L - H, cy - H), (cx + L, cy), (cx + L - H, cy + H)], color, sw)
        elif ch == "←":
            self.poly([(cx + L, cy), (cx - L, cy)], color, sw)
            self.poly([(cx - L + H, cy - H), (cx - L, cy), (cx - L + H, cy + H)], color, sw)
        elif ch == "↑":
            self.poly([(cx, cy + L), (cx, cy - L)], color, sw)
            self.poly([(cx - H, cy - L + H), (cx, cy - L), (cx + H, cy - L + H)], color, sw)
        elif ch == "↓":
            self.poly([(cx, cy - L), (cx, cy + L)], color, sw)
            self.poly([(cx - H, cy + L - H), (cx, cy + L), (cx + H, cy + L - H)], color, sw)
        elif ch == ICON_MUTE:
            self._speaker(cx, cy, size, color, sw, 0)
            self.poly([(cx + 0.08 * size, cy - 0.16 * size), (cx + 0.30 * size, cy + 0.10 * size)],
                      color, sw)
            self.poly([(cx + 0.30 * size, cy - 0.16 * size), (cx + 0.08 * size, cy + 0.10 * size)],
                      color, sw)
        elif ch == ICON_VOL_DN:
            self._speaker(cx, cy, size, color, sw, 1)
        elif ch == ICON_VOL_UP:
            self._speaker(cx, cy, size, color, sw, 2)
        elif ch in (ICON_BR_DN, ICON_BR_UP):
            filled = ch == ICON_BR_UP
            self.circle(cx, cy, 0.15 * size, fill=color if filled else None,
                        stroke=color, sw=sw)
            for a in range(0, 360, 45):
                rad = math.radians(a)
                self.poly([(cx + 0.24 * size * math.cos(rad), cy + 0.24 * size * math.sin(rad)),
                           (cx + 0.38 * size * math.cos(rad), cy + 0.38 * size * math.sin(rad))],
                          color, sw)
        else:  # ▽
            self.poly([(cx - 0.3 * size, cy - 0.22 * size), (cx + 0.3 * size, cy - 0.22 * size),
                       (cx, cy + 0.26 * size)], color, sw, closed=True)

    def _speaker(self, cx, cy, size, color, sw, waves):
        """A speaker: a small body and a cone that opens to the right, plus 0, 1 or 2
        sound waves. The whole thing is centred on (cx, cy)."""
        s = size
        body = [(-0.46, -0.115), (-0.30, -0.115), (-0.30, 0.115), (-0.46, 0.115)]
        cone = [(-0.30, -0.115), (-0.30, 0.115), (-0.135, 0.30), (-0.135, -0.30)]
        # the waves bulge to the right, away from the cone
        r1 = 0.175 + 0.135 * max(0, waves - 1)
        x0, x1 = -0.46, (-0.135 + r1) if waves else -0.135
        off = -(x0 + x1) / 2                      # centre the whole icon
        M = lambda p: (cx + off * s + p[0] * s, cy + p[1] * s)
        self.poly([M(p) for p in body], color, sw, closed=True, fill=color)
        self.poly([M(p) for p in cone], color, sw, closed=True, fill=color)
        for k in range(waves):
            r = 0.175 + k * 0.135
            pts = []
            for a in range(-52, 53, 13):
                rad = math.radians(a)
                pts.append(M((-0.135 + r * math.cos(rad), r * math.sin(rad))))
            self.poly(pts, color, sw)

    def _sun(self, cx, cy, size, color, sw, filled=True):
        """A sun: a disc in the middle and eight pointed rays around it."""
        s = size
        self.circle(cx, cy, 0.155 * s, fill=color if filled else None, stroke=color, sw=sw)
        for a in range(0, 360, 45):
            rad = math.radians(a)
            ca, sa = math.cos(rad), math.sin(rad)
            pa, pb = math.radians(a - 11), math.radians(a + 11)
            p0 = (cx + 0.235 * s * math.cos(pa), cy + 0.235 * s * math.sin(pa))
            p1 = (cx + 0.235 * s * math.cos(pb), cy + 0.235 * s * math.sin(pb))
            p2 = (cx + 0.405 * s * ca, cy + 0.405 * s * sa)
            self.poly([p0, p2, p1], color, sw, closed=True, fill=color)

    def media_icon(self, cx, cy, size, ch, color, bg=None):
        """Draw a media icon (speaker / brightness) centred on (cx, cy).

        These are drawn as real shapes instead of text characters, so they stay
        sharp and readable no matter how big the key is."""
        s = size
        sw = max(1.6, s * 0.055)
        bg = bg or color
        if ch == ICON_MUTE:
            # a speaker with a cross next to it, to say "muted"
            self._speaker(cx - 0.20 * s, cy, s * 0.92, color, sw, 0)
            r = 0.15 * s
            mx, my = cx + 0.18 * s, cy
            for col, w in ((bg, sw * 2.2), (color, sw)):
                self.poly([(mx - r, my - r), (mx + r, my + r)], col, w)
                self.poly([(mx + r, my - r), (mx - r, my + r)], col, w)
        elif ch == ICON_VOL_DN:
            self._speaker(cx - 0.07 * s, cy, s, color, sw, 1)
        elif ch == ICON_VOL_UP:
            self._speaker(cx - 0.07 * s, cy, s, color, sw, 2)
        elif ch == ICON_BR_DN:
            self._sun(cx, cy, s, color, sw, filled=False)
        elif ch == ICON_BR_UP:
            self._sun(cx, cy, s, color, sw, filled=True)

    def text(self, x, y, s, size, color, font="sans", anchor="start"):
        """y is the baseline."""
        x -= {"start": 0, "middle": tw(s, size, font) / 2, "end": tw(s, size, font)}[anchor]
        run = ""
        for ch in s:
            if ch in GLYPHS:
                if run:
                    self._show(x, y, run, size, color, font)
                    x += tw(run, size, font)
                    run = ""
                w = tw(ch, size, font) if font == "sans" else 0.6 * size
                self._glyph(x + w / 2, y, ch, size, color)
                x += w
            else:
                run += ch
        if run:
            self._show(x, y, run, size, color, font)

    def text_up(self, cx, cy, s, size, color, font="sans"):
        """Text rotated to read bottom-to-top, centred on (cx, cy)."""
        w = tw(s, size, font)
        x, y = cx + 0.36 * size, cy + w / 2
        t = s.encode("cp1252", "replace").decode("latin-1").replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")
        self.ops.append(f"{self.rgb(color)} rg BT /{FONTRES[font]} {size:.2f} Tf 0 1 -1 0 {x:.2f} {self._y(y):.2f} Tm ({t}) Tj ET")


def build_pdf(pages, title):
    """Several Canvas pages -> PDF bytes."""
    t = title.encode("ascii", "replace").decode().replace("\\", "").replace("(", "").replace(")", "")
    first = 7
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        ("<< /Type /Pages /Kids [" + " ".join(f"{first + 2 * i} 0 R" for i in range(len(pages))) +
         f"] /Count {len(pages)} >>").encode(),
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Courier /Encoding /WinAnsiEncoding >>",
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Courier-Bold /Encoding /WinAnsiEncoding >>",
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding /WinAnsiEncoding >>",
        f"<< /Title ({t}) /Producer (zmk_visualizer.py) >>".encode(),
    ]
    for i, pg in enumerate(pages):
        data = zlib.compress("\n".join(pg.ops).encode("latin-1"))
        objs.append((f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {pg.w:.2f} {pg.h:.2f}] /Resources << /Font "
                     f"<< /F1 3 0 R /F2 4 0 R /F3 5 0 R >> >> /Contents {first + 2 * i + 1} 0 R >>").encode())
        objs.append(f"<< /Length {len(data)} /Filter /FlateDecode >>\nstream\n".encode() + data + b"\nendstream")
    out, offs = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n"), []
    for i, o in enumerate(objs, 1):
        offs.append(len(out))
        out += f"{i} 0 obj\n".encode() + o + b"\nendobj\n"
    xref = len(out)
    out += f"xref\n0 {len(objs) + 1}\n".encode() + b"0000000000 65535 f \n"
    for o in offs:
        out += f"{o:010d} 00000 n \n".encode()
    out += (f"trailer\n<< /Size {len(objs) + 1} /Root 1 0 R /Info 6 0 R >>\nstartxref\n{xref}\n%%EOF\n").encode()
    return bytes(out)


# --------------------------------------------------------------------------- theme
TH = dict(bg="#181818", card="#222222", key="#474747", keytext="#ffffff", ksub="#dcdcdc", dim="#9a9a9a",
          press="#ff6fa5", press_hi="#ffc2da", presstext="#1c0a12", held="#ee3b3b", held_hi="#ff9b9b",
          heldtext="#ffffff", pink="#ff6fa5", blue="#2a56b8", bluetext="#ffffff", title="#ffffff",
          toggle="#9d7bff", toggle_hi="#c9b3ff", togletext="#141026",
          sub="#bdbdbd")
PALETTE = ["#4c9eff", "#3ecf8e", "#b388ff", "#ffb74d", "#26c6da", "#ff6b6b", "#d4e157", "#8d9bff"]
INV_W = 0.5                    # cost of moving a layer out of numeric order (a crossing costs 10)
KIND_WORD = {"cond": "both on", "off": "off", "hold": "hold", "toggle": "toggle", "switch": "go to", "oneshot": "1-shot", "taphold": "hold"}
SIZES = [36 - 0.5 * i for i in range(56)]          # label font sizes tried, biggest first (36 .. 8.5)


def layer_color(i):
    return "#a8a8a8" if i == 0 else PALETTE[(i - 1) % len(PALETTE)]


# --------------------------------------------------------------------------- key labels
PLAIN_BEH = {"kp", "sk", "mo", "tog", "to", "sl", "lt", "mt", "trans", "none", "sys_reset", "bootloader", "bt",
             "msc", "mmv", "mkp", "out", "caps_word", "key_repeat"}


def nested_label(b, depth=0):
    """The text for a binding that may be a custom behaviour: a mod-morph, tap-dance or adaptive-key shows
    what a plain tap of it does (its first binding); other behaviours that are not defined here by name."""
    p = b.split()
    beh = p[0].lstrip("&")
    mb = BEH.get(beh)
    if mb and depth < 6 and mb["raw"] and any(k in mb["compat"] for k in ("mod-morph", "tap-dance", "adaptive-key")):
        return nested_label(mb["raw"][0], depth + 1)
    if mb is None and beh not in PLAIN_BEH and len(p) > 1 and beh not in ("kt",):
        return beh.replace("_", " ").title()        # a behaviour from a module (num_word 3 -> Num Word)
    return label(b)[0]


def describe(b, layers, defines):
    """binding -> (main text, small text, underline main, underline small)"""
    p = b.split()
    beh = p[0].lstrip("&")
    if beh in ("trans", "none"):
        return beh, "", False, False
    act = layer_action(b, defines)
    ht = holdtap(beh)
    if act:
        kind, tgt = act
        name = layers[tgt]["name"] if 0 <= tgt < len(layers) else f"L{tgt}"
        if kind == "taphold":                         # tap = the key, hold = the layer
            tap = nested_label(f"&{ht[1]} {p[2]}") if len(p) > 2 else ""
            return tap, name, False, True
        return name, {"hold": "", "toggle": "toggle", "switch": "go to", "oneshot": "1-shot",
                      "off": "turn off"}[kind], True, False
    mb = BEH.get(beh)
    if mb and "mod-morph" in mb["compat"] and len(mb["raw"]) >= 2:    # e.g. Backspace, Delete with Shift
        return label(mb["raw"][0])[0], nested_label(mb["raw"][1]), False, False
    if ht and len(p) > 2:                             # a mod-tap: tap = the key, hold = the modifier
        return nested_label(f"&{ht[1]} {p[2]}"), nested_label(f"&{ht[0]} {p[1]}"), False, False
    return label(b)[0], "", False, False


def tokens(text):
    """Break points: spaces, after '-', '/' or '_', and camelCase joins (mirrorNumpad -> mirror|Numpad).
    Returns [(piece, glue_before)]: the glue is printed between two pieces and dropped on a line break."""
    out = []
    prev_end = 0
    # a piece is a word, or a word with the '-' or '/' that ends it attached
    for m in re.finditer(r"[^\s\-/]*[-/]|[^\s\-/]+", text):
        gap = text[prev_end:m.start()]              # the space before this piece
        parts = re.split(r"(?<=[a-z])(?=[A-Z])", m.group(0))
        for j, part in enumerate(parts):
            out.append((part, gap if j == 0 else ""))
        prev_end = m.end()
    return out


def wrap(text, maxw, maxh, sizes=SIZES):
    """Largest font size at which `text` fits in maxw x maxh -> (lines, size)."""
    toks = tokens(text)
    for size in sizes:
        lines, cur, ok = [], "", True
        for piece, glue in toks:
            cand = piece if not cur else cur + glue + piece
            if tw(cand, size) <= maxw:
                cur = cand
            else:
                if not cur:
                    ok = False
                    break
                lines.append(cur)
                cur = piece
        if not ok:
            continue
        if cur.strip():
            lines.append(cur)
        if len(lines) * size * 1.12 <= maxh:
            return lines, size
    size = sizes[-1]
    s = text
    while len(s) > 1 and tw(s, size) > maxw:
        s = s[:-2] + "…"
    return [s], size


def draw_key(c, x, y, ks, b, layers, defines, th, state=None, part="both"):
    """state: 'held' = red (the key you hold to be on this layer), 'layer' = pink (a key
    that takes you to another layer), 'toggle' = violet (a key that toggles a layer).
    part: 'fill' draws only the key shape, 'text' only the label, 'both' everything."""
    beh = b.split()[0].lstrip("&")
    fill, tc = {"layer": (th["press"], th["presstext"]), "held": (th["held"], th["heldtext"]),
                "toggle": (th["toggle"], th["togletext"])}.get(
        state, (th["key"], th["keytext"]))
    if part in ("fill", "both"):
        rim = {"layer": th["press_hi"], "held": th["held_hi"],
               "toggle": th["toggle_hi"]}.get(state)
        c.rect(x, y, ks, ks, fill=fill, stroke=rim, sw=4.5 if rim else 0, r=ks * 0.14)
    if part == "fill" or beh == "none" or (beh == "trans" and state):
        return
    if beh == "trans":
        c.text(x + ks / 2, y + ks / 2 + 0.3 * 32, "▽", 32, th["dim"], anchor="middle")
        return
    main, sub, ul_main, ul_sub = describe(b, layers, defines)
    cx = x + ks / 2
    if main and len(main) == 1 and main in MEDIA_ICONS:
        # a media key: draw the icon big and clear in the middle of the key
        sz = ks * 0.52
        c.media_icon(cx, y + ks / 2, sz, main, tc, bg=fill)
        return
    if main:
        lines, size = wrap(main, ks - 10, ks - (56 if sub else 14))
        lh = size * 1.12
        top = y + ks / 2 - len(lines) * lh / 2 - (16 if sub else 0)
        for i, ln in enumerate(lines):
            base = top + (i + 0.82) * lh
            c.text(cx, base, ln, size, tc, anchor="middle")
            if ul_main:
                w = tw(ln, size)
                c.line(cx - w / 2, base + 2.6, cx + w / 2, base + 2.6, tc, 1.5)
    if sub:
        sl, ss = wrap(sub, ks - 10, 26, [24, 23, 22, 21, 20, 19, 18, 17, 16.5, 16, 15.5, 15, 14.5, 14, 13.5, 13, 12, 11, 10, 9, 8])
        base = y + ks - 26                    # raised, so the combo squares do not cover it
        sc = (th["presstext"] if state == "layer" else th["heldtext"] if state == "held"
              else th["togletext"] if state == "toggle" else th["ksub"])
        c.text(cx, base, sl[0], ss, sc, anchor="middle")
        if ul_sub:
            w = tw(sl[0], ss)
            c.line(cx - w / 2, base + 2, cx + w / 2, base + 2, sc, 1.1)


# --------------------------------------------------------------------------- geometry
MONOBLOCK = False               # True for a QMK keyboard that is one block of keys (no gap between halves)


def key_slot(row, nrows, i, left, n, M):
    """Column slot (0 .. 2M-1) of key i in a row of n keys whose left half has `left` keys.
    Every row but the last is aligned to the outer edges, so the two halves mirror each other and a row
    with extra inner keys (the 3rd row of a Kyria) sticks out toward the middle. The last row is the thumb
    cluster: it stays centred around the middle."""
    if row < nrows - 1:
        return i if i < left else 2 * M - (n - left) + (i - left)
    return (M - left + i) if i < left else (M + i - left)


class Board:
    """Split keyboard: left/right halves, short bottom row sits under the inner columns."""

    def __init__(self, row_lens, ks, gap, split):
        self.ks, self.gap, self.split = ks, gap, split
        if MONOBLOCK:                                   # one block of keys, every row starts at the left
            self.cells = [(i * (ks + gap), r * (ks + gap)) for r, n in enumerate(row_lens) for i in range(n)]
            self.w = max(row_lens) * (ks + gap) - gap
            self.h = len(row_lens) * (ks + gap) - gap
            return
        lefts = [(ROW_LEFTS[r] if ROW_LEFTS and len(ROW_LEFTS) == len(row_lens) else n // 2)
                 for r, n in enumerate(row_lens)]
        M = max(max(lf, n - lf) for lf, n in zip(lefts, row_lens))
        self.cells = []
        for r, n in enumerate(row_lens):
            left = lefts[r]
            for i in range(n):
                slot = key_slot(r, len(row_lens), i, left, n, M)
                self.cells.append((slot * (ks + gap) + (split if i >= left else 0), r * (ks + gap)))
        self.w = 2 * M * (ks + gap) - gap + split
        self.h = len(row_lens) * (ks + gap) - gap


def held_positions(i, prev):
    """The keys that have to be held down while you are on layer i.

    A momentary layer is reached by holding a key down, so that key stays held while
    you are on the layer.  If the layer before it is momentary as well, you keep that
    key held as well, so the keys pile up along the way: reaching a layer through two
    momentary layers means that two keys are held at the same time.  A layer that you
    reach with a combo holds all the keys of the combo.  A layer that you reach with a
    toggle, a one-shot or a "go to" needs nothing held down, so nothing on it is red."""
    held, cur = set(), i
    while True:
        e = prev.get(cur)
        if not e or e["kind"] not in HELD_KINDS:
            break               # a toggle / one-shot / go to: nothing is held from here on
        held |= set(e["positions"])
        cur = e["src"]
    return held


# --------------------------------------------------------------------------- combos
def combo_result(cb, layers, defines):
    act = layer_action(cb["binding"], defines)
    if act:
        kind, tgt = act
        return (layers[tgt]["name"] if 0 <= tgt < len(layers) else f"L{tgt}"), KIND_WORD[kind], True
    return describe(cb["binding"], layers, defines)[0], "", False


def layout_combos(combos, width, mini, layers, defines):
    """Lay the combo panels out in rows that fit `width`."""
    placed, x, y, row_h = [], 0, 0, 0
    PAD = 48
    for cb in combos:
        main, sub, ul = combo_result(cb, layers, defines)
        bw = max(tw(main, 26), tw(sub, 18)) + 58
        w = max(mini.w + 30, bw, tw(cb["name"], 20) + 46)
        if x > 0 and x + w > width:
            x, y, row_h = 0, y + row_h + 46, 0
        placed.append(dict(cb=cb, main=main, sub=sub, ul=ul, bw=bw, w=w, x=x, y=y))
        x += w + PAD
        row_h = mini.h + 210
    return placed, (y + row_h if placed else 0)


def draw_combos(c, placed, ox, oy, mini, th):
    for it in placed:
        x0, y0 = ox + it["x"], oy + it["y"]
        c.rect(x0, y0, it["w"], mini.h + 190, fill="#1c1c1c", r=22)
        bh = 74 if it["sub"] else 50
        bx, by = x0 + (it["w"] - it["bw"]) / 2, y0 + 80 - bh
        c.rect(bx, by, it["bw"], bh, fill=th["blue"], r=14)
        base = by + (37 if not it["sub"] else 33)
        c.text(bx + it["bw"] / 2, base, it["main"], 26, th["bluetext"], anchor="middle")
        if it["ul"]:
            w = tw(it["main"], 26)
            c.line(bx + it["bw"] / 2 - w / 2, base + 5, bx + it["bw"] / 2 + w / 2, base + 5, th["bluetext"], 2)
        if it["sub"]:
            c.text(bx + it["bw"] / 2, by + 63, it["sub"], 18, th["bluetext"], anchor="middle")
        mx, my = x0 + (it["w"] - mini.w) / 2, y0 + 104
        pos = set(it["cb"]["positions"])
        for k, (kx, ky) in enumerate(mini.cells):
            c.rect(mx + kx, my + ky, mini.ks, mini.ks, fill=th["held"] if k in pos else th["key"], r=5)
        nm = it["cb"]["name"] + (f" (layers {','.join(map(str, it['cb']['layers']))})" if it["cb"]["layers"] else "")
        c.text(x0 + it["w"] / 2, my + mini.h + 42, nm, 20, th["sub"], anchor="middle")


# --------------------------------------------------------------------------- arrow heads & legend
def arrow_head(c, x, y, d, color, size=22):
    """d: 'R', 'L', 'U' or 'D' - the direction the arrow points."""
    if d == "R":
        c.poly([(x, y), (x - size, y - size * 0.60), (x - size, y + size * 0.60)], color, 1, closed=True, fill=color)
    elif d == "L":
        c.poly([(x, y), (x + size, y - size * 0.60), (x + size, y + size * 0.60)], color, 1, closed=True, fill=color)
    elif d == "D":
        c.poly([(x, y), (x - size * 0.60, y - size), (x + size * 0.60, y - size)], color, 1, closed=True, fill=color)
    else:
        c.poly([(x, y), (x - size * 0.60, y + size), (x + size * 0.60, y + size)], color, 1, closed=True, fill=color)


def draw_legend(c, x, y, th, chips=False):
    """Small 'how to read' panel."""
    items = [("pink", "pink key  =  press it to go to another layer"),
             ("violet", "violet key  =  press it to toggle a layer on and off"),
             ("red", "red key(s)  =  held down while you are on this layer"),
             ("solid", "solid arrow  =  hold"),
             ("dash", "dashed arrow  =  toggle / go to / one-shot"),
             ("combo", "combo  =  press the red keys together"),
             ("colour", "arrow colour  =  the layer it leads to")]
    if chips:
        items.insert(6, ("chip", "blue key between keys  =  combo of those keys"))
    w, rh = 660, 58
    h = 100 + rh * len(items)
    c.rect(x, y, w, h, fill="#1d1d1d", stroke="#343434", sw=2, r=22)
    c.text(x + 32, y + 56, "how to read", 30, th["title"])
    yy = y + 112
    for kind, txt in items:
        if kind == "pink":
            c.rect(x + 32, yy - 26, 32, 32, fill=th["pink"], r=8)
        elif kind == "violet":
            c.rect(x + 32, yy - 26, 32, 32, fill=th["toggle"], r=8)
        elif kind == "red":
            c.rect(x + 32, yy - 26, 32, 32, fill=th["held"], r=8)
        elif kind == "solid":
            c.rpath([(x + 32, yy - 10), (x + 84, yy - 10)], th["title"], 6, r=6)
            arrow_head(c, x + 98, yy - 10, "R", th["title"], 17)
        elif kind == "dash":
            c.rpath([(x + 32, yy - 10), (x + 84, yy - 10)], th["sub"], 6, dash=(16, 10), r=6)
            arrow_head(c, x + 98, yy - 10, "R", th["sub"], 17)
        elif kind == "colour":
            for k, col in enumerate(("#4c9eff", "#7fb4ff", "#a9c9ff")):
                c.rect(x + 32 + k * 26, yy - 22, 22, 22, fill=col, r=5)
        elif kind == "chip":
            c.rect(x + 28, yy - 28, 42, 32, fill=th["blue"], r=10)
        else:
            c.text(x + 32, yy, "combo", 25, th["pink"])
        c.text(x + 128, yy, txt, 25, th["sub"])
        yy += rh
    return h


# --------------------------------------------------------------------------- page 1: flow chart
def _hv(sg):
    (x1, y1), (x2, y2) = sg
    return ("h", y1, min(x1, x2), max(x1, x2)) if abs(y1 - y2) < 0.5 else ("v", x1, min(y1, y2), max(y1, y2))


def _cross(s, t):
    """Do two axis-aligned segments properly cross?"""
    a, b = _hv(s), _hv(t)
    if a[0] == b[0]:
        return False
    h, v = (a, b) if a[0] == "h" else (b, a)
    return h[2] + 1 < v[1] < h[3] - 1 and v[2] + 1 < h[1] < v[3] - 1


def _hits(sg, rect, m=8):
    """Does a segment run through the inside of a rectangle (x, y, w, h)?"""
    k, p, lo, hi = _hv(sg)
    x, y, w, h = rect
    if k == "h":
        return y + m < p < y + h - m and lo < x + w - m and hi > x + m
    return x + m < p < x + w - m and lo < y + h - m and hi > y + m


def _seg_hits_rect(seg, rect):
    """Does an axis-aligned piece of line run into the rectangle (x, y, w, h)?"""
    (x1, y1), (x2, y2) = seg
    rx, ry, rw, rh = rect
    rx1, ry1 = rx + rw, ry + rh
    if abs(y1 - y2) < 0.5:
        lo, hi = sorted((x1, x2))
        return ry < y1 < ry1 and hi > rx and lo < rx1
    lo, hi = sorted((y1, y2))
    return rx < x1 < rx1 and hi > ry and lo < ry1


def shade(hexc, f):
    """f > 1 mixes the colour with white, f < 1 with black."""
    r, g, b = (int(hexc[i:i + 2], 16) for i in (1, 3, 5))
    if f >= 1:
        t = min(1.0, f - 1.0)
        r, g, b = (int(v + (255 - v) * t) for v in (r, g, b))
    else:
        r, g, b = (int(v * f) for v in (r, g, b))
    return "#%02x%02x%02x" % (r, g, b)


FLOW_TRACE = None          # set to {"edges": [], "labels": []} to record where every arrow and label is drawn (animation)


def flow_page(layers, combos, row_lens, defines, src_name):
    th = TH
    # combos that type a key sit between the keys on the layers they work on; only the combos that
    # change layer are drawn as arrows (and listed at the bottom)
    all_combos = combos
    kcombos = [cb for cb in combos if not layer_action(cb["binding"], defines)
               and describe(cb["binding"], layers, defines)[0] not in ("trans", "none")]
    combos = [cb for cb in combos if layer_action(cb["binding"], defines)]
    edges, self_toggles = build_edges(layers, combos, defines)
    depth, prev = bfs(len(layers), edges)
    # "&tog N" on layer N switches back to the layer you came from, so it is drawn as
    # an arrow from N back to that layer
    for i, poss in self_toggles.items():
        if not prev.get(i):
            continue
        back = prev[i]["src"]
        if back == i:
            continue
        edges.append({"id": f"e{len(edges)}", "src": i, "dst": back, "kind": "toggle",
                      "via": "toggle", "name": "", "positions": list(poss)})
    # the colour of an arrow is the colour of the layer it leads to; arrows that lead to the
    # same layer get different shades of it, so that they can be told apart
    FACTS = [1.0, 1.5, 0.55, 1.85, 0.4]
    per_target = defaultdict(list)
    for e in edges:
        per_target[e["dst"]].append(e)
    acolor = {}
    for j, es in per_target.items():
        es.sort(key=lambda e: (e["src"], e["via"], e["positions"][0] if e["positions"] else 0))
        for k, e in enumerate(es):
            acolor[e["id"]] = shade(layer_color(j), FACTS[k % len(FACTS)])
    last_row_start = sum(row_lens[:-1])
    needs_gap = any(p < last_row_start for e in edges for p in e["positions"])
    KS, GAP, SPLIT = 150, (10 if kcombos else 20 if needs_gap else 15), 60
    board, mini = Board(row_lens, KS, GAP, SPLIT), Board(row_lens, 26, 5, 30)
    PAD, HD, PADB = 28, 118, 34
    # arrows of a conditional layer have no key: they start on a pretend key at the right end of
    # the layer's name plate (index = number of real keys)
    VIRT = len(board.cells)
    VCELL = (board.w - KS, -HD / 2 - KS / 2)
    cell_of = lambda p: VCELL if p == VIRT else board.cells[p]
    nw = board.w + 2 * PAD
    PM, HEAD = 112, 430
    TOP0 = PM + HEAD
    VGAP = 140
    GM, LANE = 76, 86
    ids = [L["idx"] for L in layers]

    # ---------- columns: how many steps each layer is away from the base layer
    def bad_edges(col):
        """What the arrows that do not point to the right cost (the further back, the worse)."""
        tot = 0
        for e in edges:
            a, b = col[e["src"]], col[e["dst"]]
            if a >= b:
                tot += (a - b + 1) * 12
        return tot

    ncol0 = max(depth.values()) + 1
    col_of = dict(depth)
    best_cost = bad_edges(col_of)
    for _ in range(4):
        improved = False
        for i in sorted(depth, key=lambda i: -depth[i]):
            if i == 0:
                continue
            for dc in (1, 2):
                trial = dict(col_of)
                trial[i] += dc
                cost = bad_edges(trial) + 6 * (max(trial.values()) + 1 - ncol0)
                if cost < best_cost - 1e-9:
                    col_of, best_cost, improved = trial, cost, True
                    break
        if not improved:
            break
    used = sorted(set(col_of.values()))         # moving layers may have emptied a column: close the gap
    depth = {i: used.index(c) for i, c in col_of.items()}

    cols = defaultdict(list)
    for L in layers:
        cols[depth[L["idx"]]].append(L["idx"])
    ncols = max(cols) + 1
    succ, pred = defaultdict(list), defaultdict(list)
    for e in edges:
        succ[e["src"]].append(e["dst"])
        pred[e["dst"]].append(e["src"])

    # ---------- how every arrow leaves its layer (static, does not depend on the layout)
    emode = {}
    for e in edges:
        a, b = depth[e["src"]], depth[e["dst"]]
        if b > a:                       # to the right: the normal case
            emode[e["id"]] = "fwd" if b == a + 1 else "corr"
        elif b == a:                    # two layers in the same column
            emode[e["id"]] = "same"
        else:                           # it has to point back
            emode[e["id"]] = "bwd"

    # ---------- the keys that trigger each arrow (static, does not depend on the layout)
    trig_cells = {}
    for e in edges:
        ps = [p for p in e["positions"] if p <= VIRT]
        trig_cells[e["id"]] = sorted([cell_of(p) for p in ps], key=lambda cl: cl[0])

    def room_below(cl):
        """Is there room straight below this key, or is another key in the way?"""
        cx, cy = cl
        for bx, by in board.cells:
            if by > cy and bx < cx + KS and bx + KS > cx:
                return False
        return True

    # ---------- the key an arrow starts on, and how it leaves the layer
    anchor_idx, anchor_leg = {}, {}
    for e in edges:
        cells = trig_cells[e["id"]]
        if not cells:                     # the trigger key is not on this board
            anchor_idx[e["id"]] = 0
            anchor_leg[e["id"]] = "down"
            continue
        down = [room_below(cl) for cl in cells]
        if len(cells) == 1:
            ai = 0
        else:
            # a key that can send the line straight down is preferred; among those the
            # one the arrow travels towards
            cand = [i for i in range(len(cells)) if down[i]] or list(range(len(cells)))
            ai = max(cand) if emode[e["id"]] in ("fwd", "corr") else min(cand)
        anchor_idx[e["id"]] = ai
        anchor_leg[e["id"]] = "down" if down[ai] else "side"

    # ---------- which arrows need a lane in which channel
    ch_tasks = defaultdict(list)
    for e in edges:
        a, b = depth[e["src"]], depth[e["dst"]]
        m = emode[e["id"]]
        if m == "fwd":
            ch_tasks[a].append(("fwd", e))
        elif m == "corr":
            # an arrow that skips whole columns goes around them, under the layers
            ch_tasks[a].append(("descF", e))
            ch_tasks[b - 1].append(("ascF", e))
        elif m == "same":
            # two layers in the same column: the arrow goes around the column, on the left
            ch_tasks[max(0, a - 1)].append(("same", e))
        else:
            # an arrow that points back: it goes under everything and comes up on the left
            ch_tasks[max(0, a - 1)].append(("descB", e))
            ch_tasks[max(0, b - 1)].append(("ascB", e))
    LEFT_ROLES = ("fwd", "descF")
    RIGHT_ROLES = ("ascF", "same", "descB", "ascB")
    CW = {}
    for c in range(max(0, ncols - 1)):
        # the lanes of the left group grow to the right, those of the right group grow
        # to the left, so the two groups only need one lane of clearance between them
        nl = sum(1 for t in ch_tasks[c] if t[0] in LEFT_ROLES)
        nr = sum(1 for t in ch_tasks[c] if t[0] in RIGHT_ROLES)
        CW[c] = 2 * GM + LANE * (nl + nr - 1) if (nl or nr) else 2 * GM
    XCOL = {0: PM}
    for c in range(1, ncols):
        XCOL[c] = XCOL[c - 1] + nw + CW[c - 1]

    nh = {i: HD + board.h + PADB for i in ids}

    # ---------- order the layers inside a column so that as few arrows as possible cross
    def order_cost(order):
        pos = {i: k for c in order for k, i in enumerate(order[c])}
        tot = 0
        for c in range(ncols - 1):
            pair = [(pos[e["src"]], pos[e["dst"]]) for e in edges
                    if depth[e["src"]] == c and depth[e["dst"]] == c + 1]
            for a in range(len(pair)):
                for b in range(a + 1, len(pair)):
                    if (pair[a][0] - pair[b][0]) * (pair[a][1] - pair[b][1]) < 0:
                        tot += 1
        return tot

    order = {c: sorted(cols[c]) for c in cols}
    best = order_cost(order)
    for _ in range(6):
        improved = False
        for c in sorted(cols, key=lambda d: -len(cols[d])):
            if len(cols[c]) < 2:
                continue
            for ref in (c - 1, c + 1):
                if ref not in cols:
                    continue
                key = {}
                for i in cols[c]:
                    ns = [j for j in (pred[i] if ref < c else succ[i]) if depth[j] == ref]
                    ys = sorted(order[ref].index(j) for j in ns)
                    key[i] = (sum(ys) / len(ys), i) if ys else (1e9, i)
                trial = dict(order)
                trial[c] = sorted(cols[c], key=lambda i: key[i])
                cost = order_cost(trial)
                if cost < best:
                    best, order, improved = cost, trial, True
        if not improved:
            break

    # ---------- vertical placement: pull every layer towards its neighbours
    def align_col(pos, order, c, ref, which):
        """Put the layers of column c at the height of their neighbours, then keep them apart."""
        lst = order[c]
        if not lst:
            return
        want = []
        for i in lst:
            ns = [j for j in (pred[i] if which == "pred" else succ[i]) if depth[j] == ref]
            if not ns:
                ns = [j for j in (succ[i] if which == "pred" else pred[i]) if depth[j] == ref]
            ys = sorted(pos[j] + nh[j] / 2 for j in ns)
            want.append(ys[len(ys) // 2] if ys else pos[i] + nh[i] / 2)
        for k, i in enumerate(lst):
            pos[i] = want[k] - nh[i] / 2
        for k in range(1, len(lst)):                  # no overlap: push the lower ones down
            i, j = lst[k - 1], lst[k]
            need = pos[i] + nh[i] + VGAP
            if pos[j] < need:
                pos[j] = need
        for k in range(len(lst) - 2, -1, -1):         # and pull the upper ones back up
            i, j = lst[k], lst[k + 1]
            limit = pos[j] - VGAP
            if pos[i] + nh[i] > limit:
                pos[i] = limit - nh[i]

    def place(order):
        pos = {}
        for c in range(ncols):
            y = 0.0
            for i in order[c]:
                pos[i] = y
                y += nh[i] + VGAP
        for _ in range(3):
            for c in range(1, ncols):
                align_col(pos, order, c, c - 1, "pred")
        bottom = max(pos[i] + nh[i] for i in ids)
        for c in range(ncols):                    # keep every column inside the same band
            top = min(pos[i] for i in order[c])
            bot = max(pos[i] + nh[i] for i in order[c])
            if bot > bottom and top > bot - bottom:
                sh = bot - bottom
                for i in order[c]:
                    pos[i] -= sh
        shift = TOP0 - min(pos[i] for i in ids)     # the title sits above everything
        return {i: pos[i] + shift for i in ids}

    # ---------- routing: every arrow gets a lane in the channel next to its layer
    def route(order, ypos):
        colrow = {}
        for c in range(ncols):
            for k, i in enumerate(order[c]):
                colrow[i] = (c, k)
        # where each arrow leaves its layer: the position of the key inside the layer
        dep = {}
        for e in edges:
            i = e["src"]
            ps = [p for p in e["positions"] if p <= VIRT]
            cells = [cell_of(p) for p in ps]
            if anchor_leg[e["id"]] == "down":
                where = PAD + sum(cl[0] for cl in cells) / len(cells)
            else:
                where = HD + sum(cl[1] for cl in cells) / len(cells)
            dep[e["id"]] = (ypos[i] + nh[i] / 2, where)

        lane = {}
        for c in range(max(0, ncols - 1)):
            chan_l, chan_r = XCOL[c] + nw, XCOL[c + 1]
            left = sorted([t for t in ch_tasks[c] if t[0] in LEFT_ROLES], key=lambda t: dep[t[1]["id"]])
            right = sorted([t for t in ch_tasks[c] if t[0] in RIGHT_ROLES], key=lambda t: dep[t[1]["id"]])
            for k, (role, e) in enumerate(left):
                lane[(role, e["id"])] = chan_l + GM + k * LANE
            for k, (role, e) in enumerate(right):
                lane[(role, e["id"])] = chan_r - GM - k * LANE

        def lane_of(e):
            """The x of the vertical part of an arrow (used to order them)."""
            m = emode[e["id"]]
            key = {"fwd": ("fwd", e["id"]), "same": ("same", e["id"]),
                   "corr": ("descF", e["id"]) if depth[e["dst"]] > depth[e["src"]] else ("descB", e["id"]),
                   "bwd": ("descB", e["id"])}
            return lane.get(key[m], 0)

        def side_free(cl, left):
            """Can the line leave this key sideways without passing over other keys?"""
            cx, cy = cl
            for bx, by in board.cells:
                if by != cy:
                    continue
                if left and bx < cx:
                    return False
                if not left and bx > cx:
                    return False
            return True

        # key anchors of every arrow
        info = {}
        for e in edges:
            ps = [p for p in e["positions"] if p <= VIRT]
            cells = [cell_of(p) for p in ps]
            kx0 = PAD + min(cl[0] for cl in cells)
            kx1 = PAD + max(cl[0] for cl in cells) + KS
            kyc = sum(cl[1] for cl in cells) / len(cells)
            # every key that triggers this arrow, at the bottom edge of the key
            pairs = sorted(((XCOL[depth[e["src"]]] + PAD + cl[0] + KS / 2,
                             ypos[e["src"]] + HD + cl[1] + KS,
                             XCOL[depth[e["src"]]] + PAD + cl[0] + KS,
                             ypos[e["src"]] + HD + cl[1] + KS / 2), cl)
                           for cl in cells)
            trig = [p for p, _ in pairs]
            tcl = [cl for _, cl in pairs]
            info[e["id"]] = {"kx0": XCOL[depth[e["src"]]] + kx0, "kx1": XCOL[depth[e["src"]]] + kx1,
                             "kxc": XCOL[depth[e["src"]]] + (kx0 + kx1) / 2,
                             "ky": ypos[e["src"]] + HD + kyc + KS / 2,
                             "kbot": ypos[e["src"]] + HD + kyc + KS,
                             "trig": trig, "tcl": tcl}
        # ---- the gap under a layer is where the arrows that leave through the bottom of
        #      that layer spread out, so that no two of them run on top of each other
        gpos, gusers = {}, defaultdict(list)
        for e in edges:
            gusers[e["src"]].append(e)
        for i, es in gusers.items():
            c_i, k_i = colrow[i]
            nxt = order[c_i][k_i + 1] if k_i + 1 < len(order[c_i]) else None
            g_top = ypos[i] + nh[i]
            g_bot = ypos[nxt] if nxt is not None else g_top + 360
            up = [e for e in es if ypos[e["dst"]] + nh[e["dst"]] / 2 < ypos[i] + nh[i] / 2]
            dn = [e for e in es if e not in up]
            up.sort(key=lambda e: lane_of(e))
            dn.sort(key=lambda e: lane_of(e))
            step = max(26, min(62, (g_bot - g_top - 54) / max(1, len(es))))
            # the arrows that go up take the top of the gap, the ones that go down the
            # bottom - and inside each group the arrow with the far lane is put first, so
            # that no line has to cross another one
            for k, e in enumerate(up):
                gpos[e["id"]] = g_top + 28 + step * (len(up) - 1 - k)
            for k, e in enumerate(dn):
                gpos[e["id"]] = g_bot - 28 - step * k

        # where every arrow lands on its target layer: always on the side, at the height
        # of the name, never on top of it
        arrivals = defaultdict(list)
        for e in edges:
            arrivals[(e["dst"], "L")].append(e)
        for (j, side), es in arrivals.items():
            es.sort(key=lambda e: dep[e["id"]])
            n = len(es)
            step = min(30, 76 / max(1, n - 1))
            for k, e in enumerate(es):
                rec = info[e["id"]]
                rec["side"] = side
                rec["ey"] = ypos[j] + 13 + (HD - 26) / 2 + (k - (n - 1) / 2) * step
        # the corridor under every layer: the arrows that have to go around a column
        # use it, each one on its own line
        corridor = {}
        cu = [e for e in edges if emode[e["id"]] in ("corr", "bwd")]
        cu.sort(key=lambda e: dep[e["id"]])
        cbase = max(ypos[i] + nh[i] for i in ids) + 78
        for k, e in enumerate(cu):
            corridor[e["id"]] = cbase + k * 96

        R = {}
        # arrows that leave the same key are spread out, so that they do not run on top
        # of each other: the dots on the key and the lines that leave it get a little
        # space between them
        kg = defaultdict(list)
        for e in edges:
            seen = set()
            for t in info[e["id"]]["trig"]:
                k = (e["src"], round(t[0]))
                if k in seen:
                    continue
                seen.add(k)
                kg[k].append(e)
        side_n, sn = {}, defaultdict(int)
        side_left = {}
        for e in sorted(edges, key=lambda e: dep[e["id"]]):
            # an arrow runs down the margin when its anchor key cannot go straight down - or, for a
            # combo, when one of the other keys of the combo cannot
            if anchor_leg[e["id"]] == "side" or any(
                    not room_below(cl) for k_, cl in enumerate(trig_cells[e["id"]])
                    if k_ != anchor_idx[e["id"]]):
                side_n[e["id"]] = sn[e["src"]]
                sn[e["src"]] += 1
        keyoff = {}
        for k, es in kg.items():
            es.sort(key=lambda e: dep[e["id"]])
            n = len(es)
            for i, e in enumerate(es):
                keyoff[(k, e["id"])] = (i - (n - 1) / 2) * 32

        # the level at which the other keys of a combo join the line: every combo of
        # a layer gets its own level, so that they do not run into each other
        join_y = {}
        by_src = defaultdict(list)
        for e in edges:
            if len(trig_cells[e["id"]]) > 1:
                by_src[e["src"]].append(e)
        for i, es in by_src.items():
            es.sort(key=lambda e: trig_cells[e["id"]][anchor_idx[e["id"]]][0])
            base = ypos[i] + nh[i] + 16
            for k, e in enumerate(es):
                join_y[e["id"]] = max(min(base + k * 30, gpos[e["id"]] - 12),
                                      ypos[i] + nh[i] + 10)

        for e in edges:
            rec, m = info[e["id"]], emode[e["id"]]
            j, ey = e["dst"], rec["ey"]
            tx_l = XCOL[depth[j]]
            tx_r = tx_l + nw
            trig = rec["trig"]
            cells = trig_cells[e["id"]]
            gy = gpos[e["id"]]
            y0 = gy
            joins = []
            ai = anchor_idx[e["id"]]
            a = trig[ai]
            ax = a[0] + keyoff.get(((e["src"], round(a[0])), e["id"]), 0.0)
            jy = join_y.get(e["id"], ypos[e["src"]] + nh[e["src"]] + 18)
            via = ex = None

            def exit_side(ti):
                """The point where the line leaves trigger ti sideways, and the x of the
                margin of the card that it runs down."""
                t = trig[ti]
                cx0 = XCOL[depth[e["src"]]]
                left = t[2] - KS
                right = t[2]
                lfree = side_free(cells[ti], True)
                rfree = side_free(cells[ti], False)
                if lfree and not rfree:
                    return left, t[3], cx0 + 16, None
                if rfree and not lfree:
                    return right, t[3], cx0 + nw - 16 - side_n[e["id"]] * 26, None
                if lfree and rfree:
                    if left - cx0 <= cx0 + nw - right:
                        return left, t[3], cx0 + 16, None
                    return right, t[3], cx0 + nw - 16 - side_n[e["id"]] * 26, None
                # keys on both sides and below: the line drops into the gap under the key's
                # row, runs along the gap and leaves the card - it never crosses a key
                kx = t[0] + keyoff.get(((e["src"], round(t[0])), e["id"]), 0.0)
                if m not in ("fwd", "corr"):          # leave on the side the arrow is heading to
                    return kx, t[3], cx0 + 16, t[1] + GAP / 2
                return kx, t[3], cx0 + nw - 16 - side_n[e["id"]] * 26, t[1] + GAP / 2

            if anchor_leg[e["id"]] == "down":
                # the line starts on the key and goes straight down
                start = (ax, a[1])
                dx = ax
                pts = [start, (dx, gy)]
                dots = [(ax, a[1])]
                jx = ax
            else:
                # there is a key below the trigger, so the line leaves it on the side of
                # the card that is closest to it and runs down the margin of the card,
                # so that it does not cross the keyboard
                ex, sy, mx, via = exit_side(ai)
                if via is None:
                    pts = [(ex, sy), (mx, sy), (mx, gy)]
                    start = (ex, sy)
                    dots = [(ex, sy)]
                else:
                    start = (ex, a[1])
                    pts = [start, (ex, via), (mx, via), (mx, gy)]
                    dots = [start]
                dx = mx
                jx = mx
            # the other keys of a combo join this line, like a circuit
            for ti, t in enumerate(trig):
                if ti == ai:
                    continue
                if anchor_leg[e["id"]] == "down" and room_below(cells[ti]):
                    # the key can send a line straight down: it drops down and joins
                    # the line of the anchor below the layer
                    kx = t[0] + keyoff.get(((e["src"], round(t[0])), e["id"]), 0.0)
                    joins.append([(kx, t[1]), (kx, jy), (jx, jy)])
                    dots.append((kx, t[1]))
                else:
                    # a key is in the way below: this one leaves sideways and joins
                    # the line of the anchor below the layer as well
                    ex, sy, mx2, via2 = exit_side(ti)
                    if via2 is None:
                        joins.append([(ex, sy), (mx2, sy), (mx2, jy), (jx, jy)])
                        dots.append((ex, sy))
                    else:
                        joins.append([(ex, t[1]), (ex, via2), (mx2, via2), (mx2, jy), (jx, jy)])
                        dots.append((ex, t[1]))

            if m == "fwd" and anchor_leg[e["id"]] == "side" and via is not None and dx > ex \
                    and e["via"] != "cond" and not joins:
                # it already left the card on the right, along the row gap: go straight on to
                # the lane instead of dropping under the layer and coming back up
                lx = lane[("fwd", e["id"])]
                pts = [start, (ex, via), (lx, via), (lx, ey)]
            elif e["via"] == "cond" and m == "fwd":
                # a conditional layer has no key: the line goes straight out of the name plate
                lx = lane[("fwd", e["id"])]
                pts = [dots[0], (lx, dots[0][1]), (lx, ey)]
            elif m == "fwd":
                lx = lane[("fwd", e["id"])]
                pts += [(lx, y0), (lx, ey)]
            elif m == "corr":
                l1, l2 = lane[("descF", e["id"])], lane[("ascF", e["id"])]
                cy = corridor[e["id"]]
                if anchor_leg[e["id"]] == "side" and via is not None and dx > ex and not joins:
                    pts = [start, (ex, via), (l1, via), (l1, cy), (l2, cy), (l2, ey)]
                else:
                    pts += [(l1, y0), (l1, cy), (l2, cy), (l2, ey)]
            elif m == "same":
                lx = lane[("same", e["id"])]
                pts += [(lx, y0), (lx, ey)]
            else:                                  # it has to point back
                l1, l2 = lane[("descB", e["id"])], lane[("ascB", e["id"])]
                if depth[j] == 0:                   # the base layer: come up on its left
                    l2 = XCOL[0] - 62
                cy = corridor[e["id"]]
                if anchor_leg[e["id"]] == "side" and via is not None and dx < ex and not joins:
                    pts = [start, (ex, via), (l1, via), (l1, cy), (l2, cy), (l2, ey)]
                else:
                    pts += [(l1, y0), (l1, cy), (l2, cy), (l2, ey)]

            # the arrow stops at the frame of the layer it leads to, at the height of
            # its name - it never crosses the frame
            pts += [(tx_l, ey)]
            d = "R"
            # where to put the label: on the longest horizontal piece that is not under a card
            lx_, ly_, lw_ = 0, 0, 0
            for i in range(len(pts) - 1):
                (x1, y1), (x2, y2) = pts[i], pts[i + 1]
                if abs(y1 - y2) < 0.5 and abs(x2 - x1) > 1:
                    mx = (x1 + x2) / 2
                    if any(XCOL[depth[q]] - 24 <= mx <= XCOL[depth[q]] + nw + 24
                           and ypos[q] - 24 <= y1 <= ypos[q] + nh[q] + 24 for q in ids):
                        continue
                    if abs(x2 - x1) > lw_:
                        lx_, ly_, lw_ = mx, y1, abs(x2 - x1)
            if lw_ < 120:                       # too short: hang the label beside the line
                vbest = None
                for i in range(len(pts) - 1):
                    (x1, y1), (x2, y2) = pts[i], pts[i + 1]
                    if abs(x1 - x2) < 0.5 and abs(y2 - y1) > 1:
                        if vbest is None or abs(y2 - y1) > vbest[2]:
                            vbest = (x1, (y1 + y2) / 2, abs(y2 - y1))
                if vbest:
                    lx_, ly_, lw_ = vbest[0], vbest[1], 0
            R[e["id"]] = {"e": e, "pts": pts, "dir": d, "start": pts[0], "end": pts[-1],
                          "side": rec.get("side", "L"),
                          "rad": 170 if m in ("corr", "bwd") else 32,
                          "lbl": (lx_, ly_, lw_),
                          "mode": m, "trig": rec["trig"], "dots": dots,
                          "joins": joins, "ey": ey,
                          "col": acolor[e["id"]]}
        return R

    # ---------- scoring: fewer crossings, fewer lines through a layer, shorter lines
    def score(ypos, order):
        R = route(order, ypos)
        segs = {k: list(zip(d["pts"], d["pts"][1:])) for k, d in R.items()}
        keys = list(R)
        cross = sum(1 for a in range(len(keys)) for b in range(a + 1, len(keys))
                    for s in segs[keys[a]] for t in segs[keys[b]] if _cross(s, t))
        pen = 0
        for k, d in R.items():
            for j in ids:
                if j not in (d["e"]["src"], d["e"]["dst"]):
                    r = (XCOL[depth[j]], ypos[j], nw, nh[j])
                    pen += sum(1 for s in segs[k] if _hits(s, r))
        length = sum(abs(s[0][0] - s[1][0]) + abs(s[0][1] - s[1][1]) for k in keys for s in segs[k])
        return 10 * cross + 70 * pen + length / 3000

    # ---------- pick the arrangement with the fewest crossings
    def total(order):
        inv = sum(1 for d in order for a in range(len(order[d])) for b in range(a + 1, len(order[d]))
                  if order[d][a] > order[d][b])
        return score(place(order), order) + INV_W * inv

    best_score = total(order)
    for _ in range(3):
        for d in sorted(cols, key=lambda d: -len(cols[d])):
            if not 2 <= len(cols[d]) <= 6:
                continue
            for perm in itertools.permutations(sorted(cols[d])):
                trial = dict(order)
                trial[d] = list(perm)
                s = total(trial)
                if s < best_score - 1e-9:
                    best_score, order = s, trial
    ypos = place(order)
    R = route(order, ypos)

    # ---- the name of every layer is always on the left, so that the arrows, which all
    #      come from the left, point right at it
    title = {}
    for L in layers:
        i = L["idx"]
        title[i] = (XCOL[depth[i]] + 60, 62 + 20 + tw(L["name"], 46))

    top = min(ypos[i] for i in ids)
    bottom = max(ypos[i] + nh[i] for i in ids)
    PW = XCOL[ncols - 1] + nw + PM
    ncorr = sum(1 for m in emode.values() if m in ("corr", "bwd"))
    CORR = 96 + 96 * max(0, ncorr - 1)
    placed, ch = layout_combos(combos, PW - 2 * PM, mini, layers, defines)
    lowest = max((p[1] for d in R.values() for p in d["pts"]), default=bottom)   # the lowest line drawn
    oy = max(bottom + VGAP + CORR, lowest + 110)   # where the combos panel starts
    # the page ends just below the lowest thing that is actually drawn: the combos
    # panel, or - when there is none - the corridor lines under the layers
    if combos:
        PH = oy + ch + 76 + PM
    else:
        PH = max(bottom + 78 + 96 * max(0, ncorr - 1) + 48 + PM, lowest + 90 + PM)
    c = Canvas(PW, PH, bg=th["bg"])

    c.text(PM, PM + 56, src_name, 58, th["title"])
    c.text(PM, PM + 100, f"{len(layers)} layers   ·   {sum(row_lens)} keys   ·   {len(all_combos)} combos", 26, th["sub"])
    c.text(PM, PM + 136, "every arrow starts on the key that triggers it", 22, th["dim"])
    c.rect(PM, PM + 162, 190, 5, fill=layer_color(1), r=3)
    draw_legend(c, PW - PM - 660, PM - 6, th, bool(kcombos))

    # ---- 1. a soft band behind every column, so the layers are grouped
    for c_ in range(ncols):
        groups = []                         # layers that are far apart get a band each, not one long band
        for i in sorted(cols[c_], key=lambda i: ypos[i]):
            if groups and ypos[i] - groups[-1][1] <= 2 * VGAP:
                groups[-1][1] = ypos[i] + nh[i]
            else:
                groups.append([ypos[i], ypos[i] + nh[i]])
        for ct, cb in groups:
            c.rect(XCOL[c_] - 26, ct - 34, nw + 52, cb - ct + 68, fill="#1c1c1c", r=30)

    # ---- 2. layer cards
    for L in layers:
        i, x, y, col = L["idx"], XCOL[depth[L["idx"]]], ypos[L["idx"]], layer_color(L["idx"])
        c.rect(x + 6, y + 11, nw, nh[i], fill="#0f0f0f", r=30)
        c.rect(x, y, nw, nh[i], fill=th["card"], stroke=col, sw=13, r=30)
        # the name plate: the name of the layer, in the band the arrows point at
        px, py, pw, ph = x + 13, y + 13, nw - 26, HD - 26
        c.rect(px, py, pw, ph, fill="#303030", r=20)
        c.rect(px + 18, py + ph - 4, pw - 36, 4, fill=col, r=2)
        gx, gw = title[i]
        gy = py + ph / 2
        c.circle(gx + 31, gy, 31, fill=col)
        c.text(gx + 31, gy + 13, str(i), 38, "#101010", anchor="middle")
        c.text(gx + 82, gy + 16, L["name"], 46, th["title"])
        if i == 0:                       # the tag of the base layer, if it fits
            tag = "base layer"
            tw_ = tw(tag, 24)
            if x + nw - 34 - tw_ > gx + gw + 24:
                c.text(x + nw - 34, gy + 10, tag, 24, th["sub"], anchor="end")
            elif x + 34 + tw_ < gx - 24:
                c.text(x + 34, gy + 10, tag, 24, th["sub"])

    # ---- 3. key shapes (red = held to be on this layer, pink = a key that switches layers)
    held_by = {i: held_positions(i, prev) for i in ids}

    lead_pos = defaultdict(set)                      # QMK leader keys start arrows too
    for e in edges:
        if e["via"] == "leader":
            lead_pos[e["src"]].update(e["positions"])

    def kstate(L, k):
        if k in held_by[L["idx"]]:
            return "held"
        b = L["flat"][k]
        if is_toggle_key(b) and layer_action(b, defines):
            return "toggle"
        if k in lead_pos.get(L["idx"], ()):
            return "layer"
        return "layer" if layer_action(b, defines) else None

    def kpos(i, k):
        return XCOL[depth[i]] + PAD + board.cells[k][0], ypos[i] + HD + board.cells[k][1]

    for L in layers:
        for k in range(len(board.cells)):
            x, y = kpos(L["idx"], k)
            draw_key(c, x, y, KS, L["flat"][k], layers, defines, th, kstate(L, k), part="fill")

    # ---- 4. the arrows. Every line gets a dark casing first, so that where two lines
    #         cross, the one on top is still easy to follow.
    card_rects = [(XCOL[depth[q]], ypos[q], nw, nh[q]) for q in ids]
    SW, CASE, HEAD_SZ, DOT_SZ = 15, 23, 32, 16
    for d in R.values():
        e, col = d["e"], d["col"]
        dash = None if e["kind"] in HELD_KINDS else (26, 16)
        _op0 = len(c.ops)
        run = []
        for seg in zip(d["pts"], d["pts"][1:]):
            if any(_seg_hits_rect(seg, r) for r in card_rects):
                if len(run) > 1:
                    c.rpath([run[0][0]] + [x[1] for x in run], th["bg"], CASE, r=d["rad"])
                run = []
            else:
                run.append(seg)
        if len(run) > 1:
            c.rpath([run[0][0]] + [x[1] for x in run], th["bg"], CASE, r=d["rad"])
        # the other keys of a combo join the line with a short elbow
        for jp in d["joins"]:
            c.rpath(jp, col, SW, dash, r=20)
        c.rpath(d["pts"], col, SW, dash, r=d["rad"])
        arrow_head(c, d["end"][0], d["end"][1], d["dir"], col, HEAD_SZ)
        for tx, ty in d["dots"]:                  # the key(s) that trigger this arrow
            c.circle(tx, ty, DOT_SZ, fill=col, stroke=th["card"], sw=5)
        if FLOW_TRACE is not None:
            FLOW_TRACE["edges"].append({"id": e["id"], "src": e["src"], "dst": e["dst"], "kind": e["kind"],
                                        "col": col, "dash": dash, "pts": d["pts"], "joins": d["joins"],
                                        "dots": d["dots"], "end": d["end"], "dir": d["dir"], "rad": d["rad"],
                                        "ops": (_op0, len(c.ops)), "SW": SW, "CASE": CASE, "HEAD": HEAD_SZ,
                                        "DOT": DOT_SZ, "page": (c.w, c.h)})

    # ---- 5. key labels, on top of the arrows
    for L in layers:
        for k in range(len(board.cells)):
            x, y = kpos(L["idx"], k)
            draw_key(c, x, y, KS, L["flat"][k], layers, defines, th, kstate(L, k), part="text")

    # ---- 5b. combos that type a key: a small blue key between the keys that make the combo
    for L in layers:
        i = L["idx"]
        for cb in kcombos:
            if cb["layers"] is not None and i not in cb["layers"]:
                continue
            ps = [p for p in cb["positions"] if p < len(board.cells)]
            if not ps:
                continue
            pts = [kpos(i, p) for p in ps]
            cx = sum(p[0] for p in pts) / len(pts) + KS / 2
            cy = sum(p[1] for p in pts) / len(pts) + KS / 2
            main = describe(cb["binding"], layers, defines)[0]
            w, h = max(68, tw(main, 32) + 28), 46
            c.rect(cx - w / 2, cy - h / 2, w, h, fill=th["blue"], stroke=th["card"], sw=5, r=15)
            c.text(cx, cy + 11, main, 31, th["bluetext"], anchor="middle")

    # ---- 6. arrow labels, last so that no line crosses them
    lbl_boxes = []

    def box_free(cx, cy, w, h):
        x0, x1 = cx - w / 2 - 5, cx + w / 2 + 5
        y0, y1 = cy - h / 2 - 5, cy + h / 2 + 5
        for b in lbl_boxes:                  # not on top of another label
            if x0 < b[2] and x1 > b[0] and y0 < b[3] and y1 > b[1]:
                return False
        for r in card_rects:                 # not on top of a layer
            if x0 < r[0] + r[2] and x1 > r[0] and y0 < r[1] + r[3] and y1 > r[1]:
                return False
        return True

    for d in R.values():
        e, col = d["e"], d["col"]
        txt = ("combo " if e["via"] == "combo" else "") + KIND_WORD[e["kind"]]
        if e["via"] == "cond":
            txt = f"layers {e['name']} on"
        elif e["via"] == "leader":
            txt = f"leader {e['name']}"
        w, h = tw(txt, 24) + 32, 50
        pts = d["pts"]
        cands = []
        hsegs = [(abs(pts[i + 1][0] - pts[i][0]), i) for i in range(len(pts) - 1)
                 if abs(pts[i][1] - pts[i + 1][1]) < 0.5 and abs(pts[i + 1][0] - pts[i][0]) > 1]
        hsegs.sort(reverse=True)
        for ln, i in hsegs:                 # on the line, longest piece first
            x1, y1 = pts[i]
            x2 = pts[i + 1][0]
            for f in (0.5, 0.3, 0.7, 0.12, 0.88):
                cands.append((x1 + (x2 - x1) * f, y1))
            cands.append(((x1 + x2) / 2, y1 - 44))
            cands.append(((x1 + x2) / 2, y1 + 44))
        for i in range(len(pts) - 1):        # next to the vertical pieces
            x1, y1 = pts[i]
            x2, y2 = pts[i + 1]
            if abs(x1 - x2) < 0.5 and abs(y2 - y1) > 1:
                for f in (0.5, 0.25, 0.75):
                    cands.append((x1, y1 + (y2 - y1) * f))
                cands.append((x1 - 100, y1 + (y2 - y1) * 0.5))
                cands.append((x1 + 100, y1 + (y2 - y1) * 0.5))
        ax, ay = cands[0] if cands else (0, 0)
        for cand in cands:
            if box_free(cand[0], cand[1], w, h):
                ax, ay = cand
                break
        lbl_boxes.append((ax - w / 2, ay - h / 2, ax + w / 2, ay + h / 2))
        _l0 = len(c.ops)
        c.rect(ax - w / 2, ay - h / 2, w, h, fill=th["bg"], stroke=col, sw=3.5, r=h / 2)
        c.text(ax, ay + 8.5, txt, 24, col, anchor="middle")
        if FLOW_TRACE is not None:
            FLOW_TRACE["labels"].append({"id": e["id"], "box": (ax - w / 2, ay - h / 2, w, h), "ops": (_l0, len(c.ops))})

    # ---- 7. combos
    if combos:
        c.text(PM, oy + 44, "combos", 46, th["title"])
        c.text(PM + tw("combos", 46) + 28, oy + 44, "press the red keys together", 26, th["sub"])
        draw_combos(c, placed, PM, oy + 96, mini, th)
    return c


# --------------------------------------------------------------------------- QMK keymap.c parser
# A QMK keymap is C code, not a device tree, so it has its own parser.  It reads the layer names
# (enum / #define), the `keymaps[]` array (LAYOUT(...) macros or raw matrices), the keycodes
# (KC_*, MO/TG/TO/OSL/TT/DF/LM/LT, mod-taps, modifier wrappers, tap dance, custom keycodes), the
# combos and the tri-layer rule, and turns them into exactly the same model the ZMK parser makes
# (layers of "&kp A" / "&mo 1" style bindings), so the flow chart is drawn by the same code.
_QK = {}


def _qk(text, *names):
    for n in names:
        _QK[n] = text


for _t, _n in [
    ("Esc", "ESCAPE ESC"), ("`", "GRAVE GRV"), ("~", "TILDE TILD"), ("Tab", "TAB"),
    ("Caps", "CAPS_LOCK CAPS CLCK CAPSLOCK"), ("Enter", "ENTER ENT RETURN"), ("Space", "SPACE SPC"),
    ("Bksp", "BACKSPACE BSPC"), ("Del", "DELETE DEL"), ("-", "MINUS MINS"), ("=", "EQUAL EQL"),
    ("[", "LEFT_BRACKET LBRC"), ("]", "RIGHT_BRACKET RBRC"), ("\\", "BACKSLASH BSLS"),
    (";", "SEMICOLON SCLN"), ("'", "QUOTE QUOT"), (",", "COMMA COMM"), (".", "DOT"), ("/", "SLASH SLSH"),
    ("#", "NONUS_HASH NUHS HASH"), ("\\", "NONUS_BACKSLASH NUBS"),
    ("!", "EXCLAIM EXLM"), ("@", "AT"), ("$", "DOLLAR DLR"), ("%", "PERCENT PERC"),
    ("^", "CIRCUMFLEX CIRC"), ("&", "AMPERSAND AMPR"), ("*", "ASTERISK ASTR"), ("(", "LEFT_PAREN LPRN"),
    (")", "RIGHT_PAREN RPRN"), ("_", "UNDERSCORE UNDS"), ("+", "PLUS"), ("{", "LEFT_CURLY_BRACE LCBR"),
    ("}", "RIGHT_CURLY_BRACE RCBR"), ("|", "PIPE"), (":", "COLON COLN"),
    ('"', "DOUBLE_QUOTE DQUO DQT"), ("<", "LEFT_ANGLE_BRACKET LABK LT"),
    (">", "RIGHT_ANGLE_BRACKET RABK GT"), ("?", "QUESTION QUES"),
    ("←", "LEFT"), ("→", "RIGHT RGHT"), ("↑", "UP"), ("↓", "DOWN"),
    ("Home", "HOME"), ("End", "END"), ("PgUp", "PAGE_UP PGUP"), ("PgDn", "PAGE_DOWN PGDN"),
    ("Ins", "INSERT INS"), ("PrtSc", "PRINT_SCREEN PSCR"), ("ScrLk", "SCROLL_LOCK SCRL SLCK"),
    ("Pause", "PAUSE PAUS BRK"), ("Menu", "APPLICATION APP"),
    ("Ctrl", "LEFT_CTRL LCTL LCTRL"), ("RCtrl", "RIGHT_CTRL RCTL RCTRL"),
    ("Shift", "LEFT_SHIFT LSFT LSHIFT"), ("RShift", "RIGHT_SHIFT RSFT RSHIFT"),
    ("Alt", "LEFT_ALT LALT LOPT"), ("RAlt", "RIGHT_ALT RALT ROPT ALGR"),
    ("GUI", "LEFT_GUI LGUI LCMD LWIN"), ("RGUI", "RIGHT_GUI RGUI RCMD RWIN"),
    (ICON_MUTE, "AUDIO_MUTE MUTE"), (ICON_VOL_UP, "AUDIO_VOL_UP VOLU"), (ICON_VOL_DN, "AUDIO_VOL_DOWN VOLD"),
    ("Play/Pause", "MEDIA_PLAY_PAUSE MPLY"), ("Next", "MEDIA_NEXT_TRACK MNXT"),
    ("Prev", "MEDIA_PREV_TRACK MPRV"), ("Stop", "MEDIA_STOP MSTP"), ("Eject", "MEDIA_EJECT EJCT"),
    ("FF", "MEDIA_FAST_FORWARD MFFD"), ("Rew", "MEDIA_REWIND MRWD"),
    (ICON_BR_UP, "BRIGHTNESS_UP BRIU"), (ICON_BR_DN, "BRIGHTNESS_DOWN BRID"),
    ("Calc", "CALCULATOR CALC"), ("Mail", "MAIL"), ("Computer", "MY_COMPUTER MYCM"),
    ("Browser", "WWW_HOME WHOM"), ("Back", "WWW_BACK WBAK"), ("Fwd", "WWW_FORWARD WFWD"),
    ("Refresh", "WWW_REFRESH WREF"), ("Search", "WWW_SEARCH WSCH"),
    ("KP /", "KP_SLASH PSLS"), ("KP *", "KP_ASTERISK PAST"), ("KP -", "KP_MINUS PMNS"),
    ("KP +", "KP_PLUS PPLS"), ("KP Enter", "KP_ENTER PENT"), ("KP .", "KP_DOT PDOT"),
    ("KP =", "KP_EQUAL PEQL"), ("NumLk", "NUM_LOCK NUM NLCK"),
    ("Move ↑", "MS_UP MS_U"), ("Move ↓", "MS_DOWN MS_D"), ("Move ←", "MS_LEFT MS_L"),
    ("Move →", "MS_RIGHT MS_R"), ("Btn 1", "MS_BTN1 BTN1"), ("Btn 2", "MS_BTN2 BTN2"),
    ("Btn 3", "MS_BTN3 BTN3"), ("Btn 4", "MS_BTN4 BTN4"), ("Btn 5", "MS_BTN5 BTN5"),
    ("Scroll ↑", "MS_WHEEL_UP WH_U"), ("Scroll ↓", "MS_WHEEL_DOWN WH_D"),
    ("Scroll ←", "MS_WHEEL_LEFT WH_L"), ("Scroll →", "MS_WHEEL_RIGHT WH_R"),
    ("Accel 0", "MS_ACCEL0 ACL0"), ("Accel 1", "MS_ACCEL1 ACL1"), ("Accel 2", "MS_ACCEL2 ACL2"),
    ("BOOT", "QK_BOOT QK_BOOTLOADER RESET"), ("Reboot", "QK_REBOOT QK_RBT"), ("Clear EEPROM", "EE_CLR QK_CLEAR_EEPROM"),
    ("RGB", "RGB_TOG UG_TOGG"), ("RGB Mode", "RGB_MOD UG_NEXT"), ("RGB Mode -", "RGB_RMOD UG_PREV"),
    ("Hue +", "RGB_HUI UG_HUEU"), ("Hue -", "RGB_HUD UG_HUED"), ("Sat +", "RGB_SAI UG_SATU"),
    ("Sat -", "RGB_SAD UG_SATD"), ("Val +", "RGB_VAI UG_VALU"), ("Val -", "RGB_VAD UG_VALD"),
    ("Back-light", "BL_TOGG BL_TOG"), ("Light +", "BL_INC BL_UP"), ("Light -", "BL_DEC BL_DOWN"),
    ("Hyper", "HYPR"), ("Meh", "MEH"), ("Language", "LANG1 LNG1"), ("Copy", "COPY"), ("Paste", "PSTE PASTE"),
    ("Cut", "CUT"), ("Undo", "UNDO"), ("Redo", "AGIN"), ("Find", "FIND"), ("Help", "HELP"),
    ("Sleep", "SYSTEM_SLEEP SLEP"), ("Power", "SYSTEM_POWER PWR"), ("Wake", "SYSTEM_WAKE WAKE"),
    ("Caps Word", "CAPS_WORD CW_TOGG"), ("Repeat", "REPEAT_KEY QK_REPEAT_KEY"),
]:
    _qk(_t, *_n.split())
for _i in range(10):
    _qk(f"KP {_i}", f"KP_{_i}", f"P{_i}")
_QK_MODS = {"CTL": "Ctrl", "CTRL": "Ctrl", "SFT": "Shift", "SHIFT": "Shift", "ALT": "Alt", "OPT": "Alt",
            "GUI": "GUI", "CMD": "GUI", "WIN": "GUI"}
_QK_MODNAME = {"C": "Ctrl", "S": "Shift", "A": "Alt", "G": "GUI"}
# wrapper functions around a keycode: name -> modifiers it presses
_QK_WRAP = {"LCTL": ["Ctrl"], "LSFT": ["Shift"], "LALT": ["Alt"], "LGUI": ["GUI"], "LCMD": ["GUI"],
            "RCTL": ["RCtrl"], "RSFT": ["RShift"], "RALT": ["RAlt"], "RGUI": ["RGUI"], "RCMD": ["RGUI"],
            "C": ["Ctrl"], "S": ["Shift"], "A": ["Alt"], "G": ["GUI"], "ALGR": ["RAlt"],
            "HYPR": ["Ctrl", "Shift", "Alt", "GUI"], "MEH": ["Ctrl", "Shift", "Alt"],
            "LCA": ["Ctrl", "Alt"], "LSG": ["Shift", "GUI"], "SGUI": ["Shift", "GUI"],
            "LCAG": ["Ctrl", "Alt", "GUI"], "LSA": ["Shift", "Alt"], "LCS": ["Ctrl", "Shift"],
            "RSA": ["RShift", "RAlt"], "RCS": ["RCtrl", "RShift"], "RSG": ["RShift", "RGUI"]}
_QK_ORDER = {"Ctrl": 0, "RCtrl": 0, "Shift": 1, "RShift": 1, "Alt": 2, "RAlt": 2, "GUI": 3, "RGUI": 3}
# mod-tap names: LSFT_T(kc) -> modifiers it presses when held
_QK_MT = {f"{p}_T": m for p, m in {
    "LCTL": ["Ctrl"], "CTL": ["Ctrl"], "RCTL": ["RCtrl"], "LSFT": ["Shift"], "SFT": ["Shift"],
    "RSFT": ["RShift"], "LALT": ["Alt"], "ALT": ["Alt"], "LOPT": ["Alt"], "RALT": ["RAlt"],
    "ROPT": ["RAlt"], "ALGR": ["RAlt"], "LGUI": ["GUI"], "GUI": ["GUI"], "LCMD": ["GUI"], "LWIN": ["GUI"],
    "RGUI": ["RGUI"], "RCMD": ["RGUI"], "RWIN": ["RGUI"], "SGUI": ["Shift", "GUI"], "SCMD": ["Shift", "GUI"],
    "SWIN": ["Shift", "GUI"], "LSG": ["Shift", "GUI"], "LCA": ["Ctrl", "Alt"], "LCAG": ["Ctrl", "Alt", "GUI"],
    "MEH": ["Ctrl", "Shift", "Alt"], "HYPR": ["Ctrl", "Shift", "Alt", "GUI"], "ALL": ["Ctrl", "Shift", "Alt", "GUI"],
    "C_S": ["Ctrl", "Shift"], "LCS": ["Ctrl", "Shift"], "LSA": ["Shift", "Alt"], "RSA": ["RShift", "RAlt"],
    "RCS": ["RCtrl", "RShift"], "RSG": ["RShift", "RGUI"]}.items()}
_QK_MT["ALL_T"] = ["Hyper"]
_QK_MT["HYPR_T"] = ["Hyper"]
_QK_MT["MEH_T"] = ["Meh"]
_QK_MT["LCAG_T"] = ["Ctrl+Alt+GUI"]
_QK_SHIFT_OF = {t: _QK[n] for t, n in {"1": "EXCLAIM", "2": "AT", "3": "HASH", "4": "DOLLAR", "5": "PERCENT",
                                       "6": "CIRCUMFLEX", "7": "AMPERSAND", "8": "ASTERISK", "9": "LEFT_PAREN",
                                       "0": "RIGHT_PAREN", "-": "UNDERSCORE", "=": "PLUS", "[": "LEFT_CURLY_BRACE",
                                       "]": "RIGHT_CURLY_BRACE", "\\": "PIPE", ";": "COLON", "'": "DOUBLE_QUOTE",
                                       ",": "LEFT_ANGLE_BRACKET", ".": "RIGHT_ANGLE_BRACKET", "/": "QUESTION",
                                       "`": "TILDE", "#": "TILDE"}.items()}
_QMK_CODES = {}                  # display text -> synthetic code ("Q#3") used inside bindings


def qk_code(text):
    """A binding is split on spaces, so a key's text is stored once and the binding carries a
    short code for it (kp_label() turns the code back into the text)."""
    if text not in _QMK_CODES:
        _QMK_CODES[text] = f"Q#{len(_QMK_CODES)}"
        QMK_TEXT[_QMK_CODES[text]] = text
    return _QMK_CODES[text]


def qmk_args(s):
    """Split on the commas that are not inside brackets: 'LT(1, KC_A), KC_B' -> ['LT(1, KC_A)', 'KC_B']"""
    out, cur, depth = [], [], 0
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    last = "".join(cur).strip()
    if last or out:
        out.append(last)
    return out


def qmk_inner(s, j):
    """s[j] is an opening bracket -> (text inside, index after the closing bracket)."""
    pairs = {"(": ")", "{": "}", "[": "]"}
    open_, close, depth, k = s[j], pairs[s[j]], 0, j
    while k < len(s):
        if s[k] == open_:
            depth += 1
        elif s[k] == close:
            depth -= 1
            if depth == 0:
                return s[j + 1:k], k + 1
        k += 1
    return s[j + 1:], len(s)


def qmk_expand(s, objs, funcs, blocked=frozenset(), depth=0):
    """#define expansion like _expand(), plus variadic macros (__VA_ARGS__), which keymaps use for
    LAYOUT_wrapper() and the row macros."""
    if depth > 40:
        return s
    out, pos = [], 0
    for m in re.finditer(r"[A-Za-z_]\w*", s):
        if m.start() < pos:
            continue
        name = m.group(0)
        if name in blocked:
            continue
        if name in funcs:
            j = m.end()
            while j < len(s) and s[j] in " \t":
                j += 1
            if j < len(s) and s[j] == "(":
                inner, end = qmk_inner(s, j)
                args = qmk_args(inner) if inner.strip() else []
                params, body = funcs[name]
                named = [p for p in params if p != "..."]
                mp = {p: a.strip() for p, a in zip(named, args)}
                if "..." in params:
                    mp["__VA_ARGS__"] = ", ".join(a.strip() for a in args[len(named):])
                body = re.sub(r"[A-Za-z_]\w*", lambda mm: mp.get(mm.group(0), mm.group(0)), body)
                body = re.sub(r"\s*##\s*", "", body)
                out += [s[pos:m.start()], qmk_expand(body, objs, funcs, blocked | {name}, depth + 1)]
                pos = end
        elif name in objs:
            out += [s[pos:m.start()], qmk_expand(objs[name], objs, funcs, blocked | {name}, depth + 1)]
            pos = m.end()
    out.append(s[pos:])
    return "".join(out)


def qmk_defines(t):
    """-> (text without preprocessor lines, object macros, function macros)"""
    t = re.sub(r"\\[ \t]*\r?\n", " \x0c ", t)         # \x0c: white space that remembers where the line ended
    objs, funcs, keep = {}, {}, []
    for line in t.split("\n"):
        m = re.match(r"\s*#\s*define\s+(\w+)(\(([^)]*)\))?[ \t]*(.*)$", line)
        if m:
            body = m.group(4).replace(SPLIT_MARK, " ").strip()
            if m.group(3) is not None:
                funcs[m.group(1)] = ([p.strip() for p in m.group(3).split(",") if p.strip()], body)
            else:
                objs[m.group(1)] = body
            keep.append("")
        elif re.match(r"\s*#", line):
            keep.append("")
        else:
            keep.append(line)
    return "\n".join(keep), objs, funcs


def qmk_enums(text, objs, funcs):
    """Every enum member and every numeric #define -> its number (the layer names live here)."""
    nums = {}
    for name, body in objs.items():
        v = qmk_expand(body, objs, funcs, frozenset({name})).strip()
        if re.fullmatch(r"-?\d+", v):
            nums[name] = int(v)
    for m in re.finditer(r"\benum\b[^{;]*\{([^}]*)\}", text):
        n, custom = -1, False
        for item in qmk_args(m.group(1)):
            if not item:
                continue
            nm, _, val = item.partition("=")
            nm, val = nm.strip(), val.strip()
            if not re.fullmatch(r"\w+", nm):
                continue
            if val:
                v = nums.get(val, val)
                if isinstance(v, int) or re.fullmatch(r"-?\d+", str(v)):
                    n = int(v)
                else:
                    custom = True                  # e.g. SAFE_RANGE: custom keycodes, not layers
            else:
                n += 1
            if not custom:
                nums.setdefault(nm, n)
    return nums


def qmk_layer_name(tok, k):
    s = tok.strip()
    if re.fullmatch(r"-?\d+", s):
        return f"layer {s}"
    s = re.sub(r"^_+", "", s)
    s = re.sub(r"^(?:L|LAYER|LYR)_(?=\w)", "", s, flags=re.I)
    if s.isupper() or s.islower():
        s = s.lower()
    s = s.replace("_", " ").strip()
    return s or f"layer {k}"


def qmk_pretty(code):
    """A keycode this script does not know -> readable text (MY_MACRO -> My Macro)."""
    s = re.sub(r"\s+", "", code)
    s = re.sub(r"^(?:KC|QK)_", "", s)
    if re.fullmatch(r"[A-Z0-9_]+", s):
        return s.replace("_", " ").title()
    return s


class QmkKeys:
    """Turns QMK keycodes into ZMK-style bindings ('&kp ..', '&mo 1', '&lt 1 ..', '&mt .. ..')."""

    def __init__(self, layer_ref, custom_layer_keys):
        self.layer_ref = layer_ref                     # name / number -> layer index or None
        self.custom = custom_layer_keys                # custom keycode -> (behaviour, layer index)

    def text(self, t):
        """The label of a plain key (also modifier wrappers like LCTL(KC_C) and LSFT(KC_1))."""
        t = t.strip()
        n = t[3:] if t.startswith("KC_") else t
        if n in _QK:
            return _QK[n]
        if re.fullmatch(r"[A-Z0-9]", n) or re.fullmatch(r"F\d{1,2}", n):
            return n
        m = re.fullmatch(r"(\w+)\s*\((.*)\)", t, re.S)
        if m and m.group(1) in _QK_WRAP:
            mods, inner = list(_QK_WRAP[m.group(1)]), m.group(2).strip()
            while True:                                # LCTL(LSFT(KC_T)): collect the modifiers
                mi = re.fullmatch(r"(\w+)\s*\((.*)\)", inner, re.S)
                if mi and mi.group(1) in _QK_WRAP:
                    mods += _QK_WRAP[mi.group(1)]
                    inner = mi.group(2).strip()
                else:
                    break
            base = self.text(inner)
            if mods == ["Shift"] and base in _QK_SHIFT_OF:
                return _QK_SHIFT_OF[base]
            mods = sorted(dict.fromkeys(mods), key=lambda x: _QK_ORDER.get(x, 9))
            return "+".join(mods + [base])
        m = re.fullmatch(r"(?:TD|TAP_DANCE)\s*\((.*)\)", t)
        if m:
            return "TD " + qmk_pretty(re.sub(r"^TD_", "", m.group(1).strip()))
        return qmk_pretty(t)

    def mods(self, expr):
        """MOD_LCTL | MOD_LSFT -> 'Ctrl+Shift'"""
        out = []
        for w in re.findall(r"MOD_(\w+)", expr):
            side = "R" if w[0] == "R" else ""
            base = w[1:] if w[0] in "LR" and w[1:] in _QK_MODS else w
            out.append(side + _QK_MODS.get(base, base.title()))
        return "+".join(dict.fromkeys(out)) or qmk_pretty(expr)

    def kc(self, t):
        return qk_code(self.text(t))

    def binding(self, tok):
        t = re.sub(r"\s+", " ", tok.strip())
        if t in ("KC_NO", "XXXXXXX", "KC_NONE", ""):
            return "&none"
        if t in ("KC_TRNS", "_______", "KC_TRANSPARENT", "KC_TRANS"):
            return "&trans"
        if t in self.custom:
            beh, idx = self.custom[t]
            return f"&{beh} {idx}"
        m = re.fullmatch(r"(\w+)\s*\((.*)\)", t, re.S)
        if not m:
            return f"&kp {self.kc(t)}"
        fn, args = m.group(1), qmk_args(m.group(2))
        ref = lambda a: self.layer_ref(a)
        simple = {"MO": "mo", "TG": "tog", "TO": "to", "OSL": "sl", "TT": "mo", "DF": "to", "PDF": "to"}
        if fn in simple and len(args) == 1 and ref(args[0]) is not None:
            return f"&{simple[fn]} {ref(args[0])}"
        if fn == "LM" and len(args) == 2 and ref(args[0]) is not None:
            return f"&mo {ref(args[0])}"
        if fn == "LT" and len(args) == 2 and ref(args[0]) is not None:
            return f"&lt {ref(args[0])} {self.kc(args[1])}"
        if fn == "MT" and len(args) == 2:
            return f"&mt {qk_code(self.mods(args[0]))} {self.kc(args[1])}"
        if fn in _QK_MT and len(args) == 1:
            return f"&mt {qk_code('+'.join(_QK_MT[fn]))} {self.kc(args[0])}"
        if fn == "OSM" and len(args) == 1:
            return f"&sk {qk_code(self.mods(args[0]))}"
        if fn == "SH_T" and len(args) == 1:
            return f"&mt {qk_code('Swap')} {self.kc(args[0])}"
        return f"&kp {self.kc(t)}"


def qmk_split_keys(s):
    """The text between the brackets of LAYOUT( ... ) -> (keys, row breaks, split markers).
    A row break is a line break after N keys; a marker is a one-line /* */ comment after N keys
    (people put one between the two halves of the keyboard)."""
    toks, cur, depth, breaks, marks = [], [], 0, [], []
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and ch == ",":
            toks.append("".join(cur).strip())
            cur = []
        elif depth == 0 and ch == "\n":
            breaks.append(len(toks) + (1 if "".join(cur).strip() else 0))
        elif depth == 0 and ch == SPLIT_MARK:
            marks.append(len(toks) + (1 if "".join(cur).strip() else 0))
        elif ch == "\n" or ch == SPLIT_MARK:
            cur.append(" ")
        else:
            cur.append(ch)
    if "".join(cur).strip():
        toks.append("".join(cur).strip())
    return toks, breaks, marks


def qmk_rows(n, breaks, marks):
    """-> (row lengths, left-half sizes) from the line breaks of one layer"""
    cuts = sorted({b for b in breaks if 0 < b < n})
    edges_ = [0] + cuts + [n]
    lens = [b - a for a, b in zip(edges_, edges_[1:])]
    lefts = []
    for a, b in zip(edges_, edges_[1:]):
        inside = [m - a for m in marks if a < m < b]
        lefts.append(min(inside, key=lambda k: abs(k - (b - a) / 2)) if inside else None)
    return lens, lefts


QMK_INFO = []          # [confidence, why] of the rows/halves of the last QMK keymap


def qmk_name_geometry(layout_name, n):
    """How sure can we be of the rows? The best signal is the layout macro itself: LAYOUT_split_3x5_2 is
    3 rows of 5 keys per half and 2 thumb keys per half; LAYOUT_ortho_4x12 is 4 rows of 12. It is only
    believed when the number of keys in the layer is exactly what the name says.
    -> (row lengths, left-half sizes or None, is split) or None"""
    m = re.search(r"(?<!\d)(\d{1,2})x(\d{1,2})(?:_(\d{1,2}))?(?!\d)", layout_name)
    if not m:
        return None
    rows, per, thumb = int(m.group(1)), int(m.group(2)), int(m.group(3) or 0)
    split = "split" in layout_name.lower()
    if split:
        lens = [2 * per] * rows + ([2 * thumb] if thumb else [])
        lefts = [per] * rows + ([thumb] if thumb else [])
    else:
        lens = [per] * rows + ([thumb] if thumb else [])
        lefts = None
    if rows < 1 or per < 1 or sum(lens) != n:
        return None
    return lens, lefts, split


def qmk_pair_halves(lens):
    """A split keymap written with the left half on one line and the right half on the next:
    5,5, 5,5, 5,5, 2,2 -> rows of 10,10,10,4. -> (row lengths, left sizes) or None"""
    if len(lens) < 4 or len(lens) % 2 or any(a != b for a, b in zip(lens[::2], lens[1::2])):
        return None
    return [2 * a for a in lens[::2]], list(lens[::2])


def qmk_find_array(text):
    """The text inside `keymaps[][..][..] = { ... };`"""
    m = re.search(r"\bkeymaps\s*(?:\[[^\]]*\]\s*)+=\s*\{", text)
    if not m:
        return None
    return qmk_inner(text, m.end() - 1)[0]


def qmk_custom_layer_keys(text, layer_ref):
    """process_record_user() often turns a custom keycode into a layer key:
    `case LOWER: layer_on(_LOWER) ... layer_off(_LOWER)` -> a key that holds _LOWER."""
    out = {}
    m = re.search(r"\bprocess_record\w*\s*\([^)]*\)\s*\{", text)
    if not m:
        return out
    body = qmk_inner(text, m.end() - 1)[0]
    parts = re.split(r"\bcase\s+(\w+)\s*:", body)
    for name, chunk in zip(parts[1::2], parts[2::2]):
        ons = re.findall(r"\blayer_on\s*\(\s*(\w+)\s*\)", chunk)
        offs = re.findall(r"\blayer_off\s*\(\s*(\w+)\s*\)", chunk)
        inv = re.findall(r"\blayer_invert\s*\(\s*(\w+)\s*\)", chunk)
        mv = re.findall(r"\b(?:layer_move|set_single_persistent_default_layer|default_layer_set)\s*\(\s*(\w+)\s*\)", chunk)
        pick = None
        if ons and ons[0] in offs:
            pick = ("mo", ons[0])
        elif inv:
            pick = ("tog", inv[0])
        elif mv:
            pick = ("to", mv[0])
        elif ons:
            pick = ("tog", ons[0])
        if pick and layer_ref(pick[1]) is not None:
            out[name] = (pick[0], layer_ref(pick[1]))
    return out

_LEADER_NAMES = {"QK_LEAD", "QK_LEADER", "KC_LEAD", "KC_LEAD", "QK_LDR", "LEADER", "LDR", "KC_LEADER"}


def qmk_leader_label(tok):
    t = tok.strip()
    t = re.sub(r"^(?:KC_|QK_)", "", t)
    names = {"SPC": "Space", "SPACE": "Space", "ENT": "Enter", "ENTER": "Enter", "TAB": "Tab", "ESC": "Esc",
             "COMM": ",", "DOT": ".", "SLSH": "/", "MINS": "-", "EQL": "=", "SCLN": ";", "QUOT": "'"}
    return names.get(t, t)


def qmk_layer_effect(chunk, layer_ref):
    """What a piece of code does to the layers -> ("to" | "tog" | "mo", layer index) or None."""
    pats = [("to", r"\b(?:layer_move|set_single_persistent_default_layer|default_layer_set)\s*\(\s*(\w+)\s*\)"),
            ("tog", r"\b(?:layer_invert|layer_on)\s*\(\s*(\w+)\s*\)")]
    for kind, rx in pats:
        m = re.search(rx, chunk)
        if m and layer_ref(m.group(1)) is not None:
            return kind, layer_ref(m.group(1))
    return None


def qmk_leader_sequences(text, layer_ref):
    """Leader-key sequences that change layers -> (names of the leader keycodes, [{"seq", "kind", "layer"}]).
    Understands the function-pointer style (`case KC_L: return leader_layers_func;`) and
    QMK's own leader_sequence_two_keys(KC_L, KC_Q) / SEQ_TWO_KEYS(KC_L, KC_Q) blocks."""
    keys = set()
    for m in re.finditer(r"\bcase\s+(\w+)\s*:(?:(?!\bcase\b|\bbreak\b)[^}]){0,200}?\bstart_leading\s*\(", text, re.S):
        keys.add(m.group(1))
    seqs = []
    funcs = {}
    for m in re.finditer(r"\bvoid\s*\*\s*(\w+)\s*\(\s*uint16_t\s+\w+\s*\)\s*\{", text):
        funcs[m.group(1)] = qmk_inner(text, m.end() - 1)[0]
    if funcs:
        called = set()
        for body in funcs.values():
            called.update(re.findall(r"\breturn\s+(\w+)\s*;", body))
        roots = [f for f in funcs if f not in called] or []

        def walk(fn, prefix, seen):
            if fn in seen:
                return
            body = funcs[fn]
            parts = re.split(r"\bcase\s+(\w+)\s*:", body)
            for name, chunk in zip(parts[1::2], parts[2::2]):
                label = (prefix + " " + qmk_leader_label(name)).strip()
                nxt = [f for f in re.findall(r"\breturn\s+(\w+)\s*;", chunk) if f in funcs]
                if nxt:
                    walk(nxt[0], label, seen | {fn})
                    continue
                eff = qmk_layer_effect(chunk, layer_ref)
                if eff:
                    seqs.append({"seq": label, "kind": eff[0], "layer": eff[1]})
        for r in roots:
            walk(r, "", set())
    # QMK's own leader: leader_end_user() { if (leader_sequence_two_keys(KC_L, KC_Q)) { layer_move(_QWERTY); } }
    for m in re.finditer(r"\b(?:leader_sequence_\w+?_keys|SEQ_\w+?_KEYS)\s*\(([^)]*)\)\s*\)?\s*\{", text):
        eff = qmk_layer_effect(qmk_inner(text, m.end() - 1)[0], layer_ref)
        if eff:
            seqs.append({"seq": " ".join(qmk_leader_label(a) for a in m.group(1).split(",") if a.strip()),
                         "kind": eff[0], "layer": eff[1]})
    if seqs:
        keys |= _LEADER_NAMES
    return keys, seqs


QMK_SPLIT_BOARDS = ("kyria", "corne", "crkbd", "lily58", "sofle", "iris", "totem", "sweep", "ferris", "charybdis",
                    "cradio", "lotus", "dactyl", "imprint", "cantor", "reviung", "nyquist", "elora", "moonlander",
                    "ergodox", "bastardkb", "splitkb", "helix", "quefrency", "svalboard")
_SPLIT_API = re.compile(r"\b(is_keyboard_master|is_keyboard_left|is_keyboard_right|SPLIT_KEYBOARD|SPLIT_HAND_PIN"
                        r"|SPLIT_TRANSPORT_MIRROR|SPLIT_[A-Z_]{4,}|EE_HANDS|MASTER_LEFT|MASTER_RIGHT)\b")


def qmk_split_evidence(text, hint=""):
    """Is there anything in the file (or in its path) that says this is a split keyboard?
    -> why, or "" when there is nothing. The layout name is checked elsewhere."""
    m = _SPLIT_API.search(text)
    if m:
        return f"the file uses {m.group(1)}, which only exists on split keyboards"
    low = (text + "\n" + hint).lower()
    for b in QMK_SPLIT_BOARDS:
        if re.search(r"(?<![a-z])" + b + r"(?![a-z])", low):
            return f"the file or its folder mentions {b}, a split keyboard"
    return ""


def qmk_wants_split(layout_name, row_lens, has_marks):
    """Is this a split keyboard (two halves with a gap) or one block of keys?"""
    n = layout_name.lower()
    if "split" in n or any(k in n for k in ("crkbd", "corne", "lily58", "sofle", "kyria", "cradio", "iris",
                                           "totem", "sweep", "ferris", "charybdis", "lotus", "dactyl")):
        return True
    if has_marks:
        return True
    if len(row_lens) >= 3 and all(r % 2 == 0 for r in row_lens) and row_lens[-1] < row_lens[-2] \
            and row_lens[0] >= 8 and row_lens[0] == row_lens[1]:
        return True
    return False


def parse_qmk(text, forced_rows=None, split=None, hint=""):
    """A QMK keymap.c -> (layers, combos, row_lens, defines), like parse_keymap() does for ZMK."""
    global BINDING_STARTS, ROW_LEFTS, MONOBLOCK
    BINDING_STARTS = set()
    BEH.clear()
    CONDITIONAL.clear()
    LEADER["keys"], LEADER["seqs"] = set(), []
    QMK_TEXT.clear()
    _QMK_CODES.clear()
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    clean = strip_comments_marked(text)
    body_text, objs, funcs = qmk_defines(clean)
    nums = qmk_enums(body_text, objs, funcs)
    array = qmk_find_array(body_text)
    if array is None:
        sys.exit("error: no `keymaps[]` array found in the file (is this a QMK keymap.c?)")

    # --- the layers: `[_NAME] = LAYOUT(...)`, or a plain `LAYOUT(...)`, or a raw matrix `{ {..}, {..} }`
    items = []
    for k, item in enumerate(qmk_args("\n".join(l for l in array.split("\n") if not l.lstrip().startswith("#")))):
        if not item.strip():
            continue
        m = re.match(r"\s*\[\s*([^\]]+?)\s*\]\s*=\s*(.*)$", item, re.S)
        idx_tok, expr = (m.group(1), m.group(2).strip()) if m else (str(len(items)), item.strip())
        items.append((idx_tok, expr))

    def number_of(tok):
        tok = tok.strip()
        if re.fullmatch(r"-?\d+", tok):
            return int(tok)
        if tok in nums:
            return nums[tok]
        v = qmk_expand(tok, objs, funcs).strip()
        return int(v) if re.fullmatch(r"-?\d+", v) else None

    raw_layers, seen = [], set()
    for k, (idx_tok, expr) in enumerate(items):
        num = number_of(idx_tok)
        if num is None:
            num = k
        if num in seen:                                # the other branch of an #ifdef: keep the first
            continue
        seen.add(num)
        lm = re.match(r"(\w+)\s*\(", expr)
        if lm:
            inner, _ = qmk_inner(expr, lm.end() - 1)
            inner = qmk_expand(inner, objs, funcs)
            toks, breaks, marks = qmk_split_keys(inner)
            name = lm.group(1)
            if name in funcs:                          # the keymap's own layout macro: use what it expands to
                full = qmk_expand(expr, objs, funcs)
                lm2 = re.match(r"\s*(\w+)\s*\(", full)
                if lm2 and lm2.group(1) not in funcs:
                    inner2, _ = qmk_inner(full, lm2.end() - 1)
                    toks2, breaks2, marks2 = qmk_split_keys(inner2.replace("\x0c", "\n"))
                    if len(toks2) == len(toks):        # key for key (home row mods...): keep the layout as written
                        toks = toks2
                    else:                              # it adds keys (50 from 32...): the rows are the macro's own
                        toks, breaks, marks = toks2, breaks2, marks2
                    name = lm2.group(1)
        elif expr.startswith("{"):                     # a raw matrix: every inner {...} is a row
            inner = qmk_inner(expr, 0)[0]
            rows_ = [qmk_args(qmk_inner(r, 0)[0]) for r in qmk_args(inner) if r.startswith("{")]
            toks = [t for r in rows_ for t in r if t != ""]
            breaks, acc = [], 0
            for r in rows_:
                acc += len([t for t in r if t != ""])
                breaks.append(acc)
            marks, name = [], "matrix"
        else:
            continue
        raw_layers.append({"num": num, "tok": idx_tok, "layout": name, "toks": toks,
                           "breaks": breaks, "marks": marks})
    if not raw_layers:
        sys.exit("error: no layers found in the `keymaps[]` array")
    raw_layers.sort(key=lambda r: r["num"])
    numidx = {r["num"]: i for i, r in enumerate(raw_layers)}

    def layer_ref(a):
        v = number_of(a)
        return numidx.get(v) if v is not None else None

    custom = qmk_custom_layer_keys(body_text, layer_ref)
    LEADER["keys"], LEADER["seqs"] = set(), []
    try:
        LEADER["keys"], LEADER["seqs"] = qmk_leader_sequences(body_text, layer_ref)
    except Exception:
        pass
    keys = QmkKeys(layer_ref, custom)

    layers, lefts0 = [], None
    for i, r in enumerate(raw_layers):
        flat = [keys.binding(t) for t in r["toks"]]
        lens, lefts = qmk_rows(len(flat), r["breaks"], r["marks"])
        it = iter(flat)
        lines = [[next(it) for _ in range(n)] for n in lens]
        if i == 0:
            lefts0 = lefts
        layers.append({"idx": i, "name": qmk_layer_name(r["tok"], i), "title": r["tok"].strip(),
                       "lines": lines, "flat": flat, "raw": r["toks"]})
    if len(layers) > 1 and all(L["name"].endswith(" layer") for L in layers):
        for L in layers:
            L["name"] = L["name"][:-6]

    # --- rows and halves
    first = [len(l) for l in layers[0]["lines"]]
    layout0, n0 = raw_layers[0]["layout"], len(layers[0]["flat"])
    has_marks = bool(lefts0 and any(k is not None for k in lefts0))
    split_why = qmk_split_evidence(text, hint) if split is None else ""
    name_split = (qmk_wants_split(layout0, first, False) or bool(split_why)) and not has_marks
    geo, pair, lefts_geo = qmk_name_geometry(layout0, n0), None, None
    if forced_rows:
        row_lens, QMK_INFO[:] = forced_rows, ["rows given with --rows"]
    elif geo:                                           # high: the layout name says so
        row_lens, lefts_geo = geo[0], geo[1]
        QMK_INFO[:] = ["high", f"from the layout name {layout0}"]
    elif has_marks and len(first) > 1:                  # medium: halves marked with /* */ in the file
        row_lens = first
        QMK_INFO[:] = ["medium", "from the line breaks and the /* */ markers in the file"]
    elif len(first) > 1 and name_split and qmk_pair_halves(first):
        row_lens, lefts_geo = qmk_pair_halves(first)    # medium: left half and right half on separate lines
        QMK_INFO[:] = ["medium", "each line is one half of a row, so two lines were joined"]
    elif len(first) >= 6 and qmk_pair_halves(first) and first[-1] < first[0] and len(set(first[:-2])) == 1:
        row_lens, lefts_geo = qmk_pair_halves(first)    # medium: unknown name, but the lines come in equal pairs
        QMK_INFO[:] = ["medium", "lines come in equal pairs (left half, right half), with a shorter last pair"]
        name_split = True
    elif len(first) > 1:                                # medium: the rows as they are written
        row_lens = first
        QMK_INFO[:] = ["medium", "from the line breaks in the file"]
    else:                                               # low: only the number of keys is known
        row_lens = guess_rows(n0)
        QMK_INFO[:] = ["low", f"guessed from the number of keys ({n0}); use --rows to set it"]
    if geo and split is None:
        is_split = geo[2]
    else:
        is_split = split if split is not None else (qmk_wants_split(layout0, row_lens, has_marks or bool(lefts_geo))
                                                    or bool(split_why))
        if is_split and split is None and not has_marks and not geo and not qmk_wants_split(layout0, [], False) \
                and len(QMK_INFO) > 1:
            QMK_INFO[1] += "; split because " + (
                split_why or "all rows have an even number of keys and the last (thumb) row is shorter")
    ROW_LEFTS = None
    MONOBLOCK = not is_split
    if is_split and not forced_rows and lefts_geo:
        ROW_LEFTS = list(lefts_geo)
    elif is_split and not forced_rows and len(first) > 1 and has_marks:
        ROW_LEFTS = [k if k is not None else n // 2 for k, n in zip(lefts0, row_lens)]
    total = sum(row_lens)
    for L in layers:
        flat = L["flat"]
        if len(flat) != total:
            print(f"warning: layer {L['idx']} ({L['name']}) has {len(flat)} keys, expected {total}",
                  file=sys.stderr)
            flat = (flat + ["&none"] * total)[:total]
            L["raw"] = (L["raw"] + ["KC_NO"] * total)[:total]
        L["flat"], it = flat, iter(flat)
        L["rows"] = [[next(it) for _ in range(n)] for n in row_lens]

    # --- combos: COMBO(name, result) with `name[] = {KC_A, KC_B, COMBO_END}`; keys are keycodes in
    # QMK, so they are looked up on the base layer to get key positions
    seqs = {}
    for m in re.finditer(r"\b(\w+)\s*\[\s*\]\s*=\s*\{([^}]*)\}", body_text):
        parts = [p for p in qmk_args(qmk_expand(m.group(2), objs, funcs)) if p]
        if parts and parts[-1] in ("COMBO_END", "0"):
            seqs[m.group(1)] = parts[:-1]
    base_raw = [re.sub(r"\s+", "", t) for t in layers[0]["raw"]]

    def base_of(t):
        """The plain keycode a key sends when tapped: LT(1,KC_A) / LGUI_T(KC_A) -> KC_A"""
        m = re.fullmatch(r"(\w+)\((.*)\)", t)
        if not m:
            return t
        a = qmk_args(m.group(2))
        if m.group(1) in ("LT", "MT") and len(a) == 2:
            return base_of(a[1])
        if m.group(1) in _QK_MT and len(a) == 1:
            return base_of(a[0])
        return t

    def positions_of(kc):
        """Every key of the base layer that sends this keycode (the exact key first, else the same tap)."""
        kc = re.sub(r"\s+", "", kc)
        hits = [i for i, t in enumerate(base_raw) if t == kc]
        return hits or [i for i, t in enumerate(base_raw) if base_of(t) == base_of(kc)]

    lefts_c = [(ROW_LEFTS[r] if ROW_LEFTS and len(ROW_LEFTS) == len(row_lens) else n_ // 2)
               for r, n_ in enumerate(row_lens)]
    M_c = max(max(lf, n_ - lf) for lf, n_ in zip(lefts_c, row_lens))
    pts = []
    for r, n_ in enumerate(row_lens):
        for i in range(n_):
            pts.append((i if MONOBLOCK else key_slot(r, len(row_lens), i, lefts_c[r], n_, M_c), r))

    def resolve(kcs):
        """Key positions of a combo. A keycode that is on the base layer twice (a Leader key on each side)
        is the one next to the other keys of the combo."""
        cands = [positions_of(k) for k in kcs]
        if any(not c for c in cands):
            return None
        if all(len(c) == 1 for c in cands):
            return [c[0] for c in cands]
        from itertools import product
        best, best_d = None, None
        for combo in product(*[c[:4] for c in cands]):
            d = sum(abs(pts[a][0] - pts[b][0]) + 1.5 * abs(pts[a][1] - pts[b][1])
                    for ai, a in enumerate(combo) for b in combo[ai + 1:])
            if best_d is None or d < best_d - 1e-9:
                best, best_d = list(combo), d
        return best

    combos = []
    for m in re.finditer(r"\b(COMBO|COMB)\s*\(", body_text):
        inner, _ = qmk_inner(body_text, m.end() - 1)
        a = qmk_args(qmk_expand(inner, objs, funcs))
        if m.group(1) == "COMBO" and len(a) == 2 and a[0] in seqs:
            name, result, kcs = a[0], a[1], seqs[a[0]]
        elif m.group(1) == "COMB" and len(a) >= 3:          # combos.def style: COMB(name, result, KC_A, KC_B)
            name, result, kcs = a[0], a[1], a[2:]
        else:
            continue
        pos = resolve(kcs)
        if not pos or len(set(pos)) != len(pos):
            print(f"warning: combo {name}: its keys are not all on the base layer, so it is left out",
                  file=sys.stderr)
            continue
        nm = re.sub(r"^(?:COMBO_|CMB_|C_)", "", name)
        combos.append({"name": nm, "positions": pos, "binding": keys.binding(result),
                       "layers": None, "timeout": None})

    # --- COMBO_ACTION(name): the keys do whatever process_combo_event() does for that event
    actions = {}
    pm = re.search(r"\bprocess_combo_event\s*\([^)]*\)\s*\{", body_text)
    if pm:
        fbody = qmk_inner(body_text, pm.end() - 1)[0]
        pending, parts_ = [], re.split(r"(\bcase\s+\w+\s*:|\bdefault\s*:)", fbody)
        for lab, txt in zip(parts_[1::2], parts_[2::2]):
            pending.append(re.sub(r"\bcase\s+|\s*:", "", lab))
            if txt.strip().strip("}").strip():
                for ev in pending:
                    actions[ev] = txt
                pending = []

    def action_text(txt):
        """What a case of process_combo_event() does, as a few words for the key."""
        taps = re.findall(r"\b(?:tap_code|register_code)(?:16)?\s*\(\s*([^;]*?)\s*\)\s*;", txt)
        if taps:
            return " ".join(keys.text(t) for t in taps)
        sent = re.findall(r'\bSEND_STRING\s*\(\s*"([^"]*)"', txt)
        if sent:
            return "".join(sent)
        calls = [c for c in re.findall(r"\b([A-Za-z_]\w*)\s*\(", txt)
                 if c not in ("if", "switch", "while", "for", "return", "sizeof")]
        words = lambda c: " ".join(w.capitalize() for w in re.sub(r"^(?:toggle|enable)_", "", c).split("_"))
        return " + ".join(words(c) for c in list(dict.fromkeys(calls))[:2])

    for m in re.finditer(r"\[\s*(\w+)\s*\]\s*=\s*COMBO_ACTION\s*\(\s*(\w+)\s*\)", body_text):
        ev, seq = m.group(1), m.group(2)
        if seq not in seqs:
            continue
        pos = resolve(seqs[seq])
        if not pos or len(set(pos)) != len(pos):
            print(f"warning: combo {ev}: its keys are not all on the base layer, so it is left out",
                  file=sys.stderr)
            continue
        label = action_text(actions.get(ev, "")) or re.sub(r"_COMBO$", "", ev)
        combos.append({"name": re.sub(r"_COMBO$", "", ev), "positions": pos,
                       "binding": f"&kp {qk_code(label)}", "layers": None, "timeout": None})

    # --- tri-layer: update_tri_layer_state(state, _LOWER, _RAISE, _ADJUST) = conditional layer
    for m in re.finditer(r"\bupdate_tri_layer(?:_state)?\s*\(\s*(?:\w+\s*,\s*)?(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)",
                         body_text):
        a, b, c = (layer_ref(x) for x in m.groups())
        rule = {"name": "tri", "ifs": [a, b], "then": c}
        if None not in (a, b, c) and rule not in CONDITIONAL:     # it is often called more than once
            CONDITIONAL.append(rule)
    defines = {r["tok"].strip(): i for i, r in enumerate(raw_layers) if re.fullmatch(r"\w+", r["tok"].strip())}
    return layers, combos, row_lens, defines


# --------------------------------------------------------------------------- page 2 for QMK: the original code
def strip_c_comments(text):
    """C source without its comments: // and /* */ (also over several lines) are removed, markers inside
    "strings" and 'chars' are left alone, a line that held only a comment is dropped altogether, and runs
    of blank lines shrink to one."""
    out, in_block = [], False
    for line in text.replace("\r\n", "\n").replace("\r", "\n").split("\n"):
        res, i, q, n = [], 0, "", len(line)
        while i < n:
            ch = line[i]
            if in_block:
                j = line.find("*/", i)
                if j < 0:
                    i = n
                else:
                    in_block, i = False, j + 2
            elif q:
                res.append(ch)
                if ch == "\\" and i + 1 < n:
                    res.append(line[i + 1])
                    i += 1
                elif ch == q:
                    q = ""
                i += 1
            elif ch in "\"'":
                q = ch
                res.append(ch)
                i += 1
            elif line.startswith("//", i):
                i = n
            elif line.startswith("/*", i):
                in_block, i = True, i + 2
            else:
                res.append(ch)
                i += 1
        code = "".join(res).rstrip()
        if line.strip() and not code.strip():
            continue                                    # the line was nothing but a comment
        out.append(code)
    lines, blank = [], True
    for l in out:
        if not l.strip():
            if not blank:
                lines.append("")
            blank = True
        else:
            lines.append(l)
            blank = False
    while lines and not lines[-1]:
        lines.pop()
    return "\n".join(lines) + "\n"


def source_page(text, src_name):
    """The keymap.c (comments already removed by the caller), in as many columns as
    needed to keep the page a sane height."""
    th, PM, fs = TH, 50, 15
    LH = fs * 1.4
    lines = []
    for l in text.replace("\r\n", "\n").replace("\r", "\n").split("\n"):
        l = l.replace("\t", "    ").rstrip()
        lines.append("".join(ch if 32 <= ord(ch) < 256 else ("?" if ord(ch) >= 256 else " ") for ch in l))
    while lines and not lines[-1]:
        lines.pop()
    per_col = max(40, int((9000 - 2 * PM - 130) / LH))
    ncols = max(1, -(-len(lines) // per_col))
    per_col = -(-len(lines) // ncols)
    cw = max(len(l) for l in lines) * 0.6 * fs + 60
    PW = max(1500, ncols * cw + 2 * PM - 60)
    PH = PM + 130 + per_col * LH + PM
    c = Canvas(PW, PH, bg=th["bg"])
    c.text(PM, PM + 34, src_name, 44, th["title"])
    c.text(PM, PM + 66, "keymap source, comments removed", 19, th["sub"])
    CM, CHW = "#7d8590", 0.6 * fs
    in_block = False
    for n, l in enumerate(lines):
        col, row = divmod(n, per_col)
        x, y = PM + col * cw, PM + 120 + row * LH + fs
        code, cmt = l, ""
        if in_block:
            code, cmt = "", l
            if "*/" in l:
                in_block = False
                k = l.index("*/") + 2
                cmt, code = l[:k], l[k:]
        else:
            k = len(l)
            for mm in re.finditer(r"//|/\*", l):
                if l[:mm.start()].count('"') % 2 == 0:
                    k = mm.start()
                    break
            code, cmt = l[:k], l[k:]
            if cmt.startswith("/*") and "*/" not in cmt:
                in_block = True
        s = code.strip()
        if s.startswith("#"):
            colr, font = "#c3a6ff", "mono"
        elif re.search(r"\[[^\]]+\]\s*=\s*\w+\s*\($", s) or re.search(r"\bkeymaps\b", s):
            colr, font = "#8ab4ff", "monob"
        else:
            colr, font = "#ececec", "mono"
        if code.strip():
            c.text(x, y, code, fs, colr, font)
        if cmt:
            c.text(x + len(code) * CHW, y, cmt, fs, CM, "mono")
    return c


# --------------------------------------------------------------------------- page 2: keymap text
def align_rows(rows):
    """Rows of bindings -> aligned text lines (same grid as the keyboard halves)."""
    lefts = [(ROW_LEFTS[k] if ROW_LEFTS and len(ROW_LEFTS) == len(rows) else len(r) // 2)
             for k, r in enumerate(rows)]
    M = max(max(lf, len(r) - lf) for lf, r in zip(lefts, rows))
    grid = []
    for k, r in enumerate(rows):
        left = lefts[k]
        cells = [""] * (2 * M)
        for i, b in enumerate(r):
            cells[key_slot(k, len(rows), i, left, len(r), M)] = b
        grid.append(cells)
    widths = [max(len(g[k]) for g in grid) for k in range(2 * M)]
    lines = []
    for g in grid:
        l = "   ".join(g[k].ljust(widths[k]) for k in range(M))
        r_ = "   ".join(g[k].ljust(widths[k]) for k in range(M, 2 * M))
        lines.append((l + "         " + r_).rstrip())
    return lines


def keymap_text(src_text, total_keys):
    """The keymap with every comment removed; layer bindings re-aligned into keyboard grids."""
    t = strip_comments(src_text)

    def fix(m):
        body = m.group(2)
        rows = [split_bindings(l.strip()) for l in body.splitlines() if l.strip()]
        if len(rows) < 2 or sum(len(r) for r in rows) != total_keys:
            return m.group(0)
        pad = " " * 12
        return m.group(1) + "\n" + "\n".join(pad + l for l in align_rows(rows)) + "\n" + pad + ">;"

    t = re.sub(r"(bindings\s*=\s*<)(.*?)>\s*;", fix, t, flags=re.S)
    lines = [l.rstrip() for l in t.replace("\t", "    ").splitlines()]
    out, blank = [], True
    for l in lines:
        if not l.strip():
            if not blank:
                out.append("")
            blank = True
        else:
            out.append(l)
            blank = False
    while out and not out[-1]:
        out.pop()
    return out


def text_page(lines, src_name):
    th, PM, fs = TH, 50, 15
    maxlen = max(len(l) for l in lines)
    PW = max(1500, maxlen * 0.6 * fs + 2 * PM)
    LH = fs * 1.4
    PH = PM + 100 + len(lines) * LH + PM
    c = Canvas(PW, PH, bg=th["bg"])
    c.text(PM, PM + 34, src_name, 44, th["title"])
    c.text(PM, PM + 66, "keymap source, comments removed (bindings re-aligned as keyboard rows)", 19, th["sub"])
    y = PM + 120
    for l in lines:
        s = l.strip()
        if s.endswith("{") or s.startswith("&") and s.endswith("{"):
            c.text(PM, y, l, fs, "#8ab4ff", "monob")
        elif s.startswith("#"):
            c.text(PM, y, l, fs, "#c3a6ff", "mono")
        else:
            c.text(PM, y, l, fs, "#ececec", "mono")
        y += LH
    return c


# The flow chart page is drawn on a very large sheet, so a PNG snapshot of it
# comes out at a huge pixel count.  Pillow (and a few other tools) refuse to open
# images above ~89 megapixels, so the snapshot is scaled down to stay under that
# limit while still being far sharper than the screen it is looked at on.
PREVIEW_MAX_PIXELS = 64_000_000


def import_pymupdf():
    """PyMuPDF, or None. It is imported as `pymupdf`; the old name `fitz` prints a FutureWarning, so it is only
    a fallback for old versions, and its warning is silenced. A broken install counts as not installed."""
    try:
        import pymupdf
        return pymupdf
    except Exception:
        pass
    try:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            import fitz
        return fitz
    except Exception:
        return None


def snapshot_png(pdf_bytes, png_path, scale=2.0, max_pixels=PREVIEW_MAX_PIXELS):
    """Render page 1 of the PDF to a PNG, as a quick look at the flow chart.

    PyMuPDF is used when it is installed; otherwise the PDF is rasterised with
    poppler's pdftoppm, which gives the same result.

    `scale` is the zoom factor (2.0 means twice the size of the PDF page).  It is
    lowered when needed so that the PNG stays below `max_pixels`; the PDF itself
    is vector and stays sharp at any zoom."""
    import math
    import shutil
    import subprocess
    import tempfile

    # the page size is in the PDF's /MediaBox, so the snapshot can be sized
    # before anything is rendered
    size = None
    for m in re.finditer(rb"/MediaBox\s*\[\s*([\d.+-]+)\s+([\d.+-]+)\s+"
                          rb"([\d.+-]+)\s+([\d.+-]+)\s*\]", pdf_bytes):
        w = float(m.group(3)) - float(m.group(1))
        h = float(m.group(4)) - float(m.group(2))
        size = (w, h)
        break
    if size and max_pixels:
        w, h = size
        if w > 0 and h > 0:
            too_big = (w * scale) * (h * scale)
            if too_big > max_pixels:
                scale = math.sqrt(max_pixels / too_big)

    fitz = import_pymupdf()
    if fitz is not None:
        document = fitz.open(stream=pdf_bytes, filetype="pdf")
        try:
            page = document[0]
            pixmap = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False)
            pixmap.save(str(png_path))
        finally:
            document.close()
        return True
    exe = shutil.which("pdftoppm")
    if exe is None:
        return False
    # pdftoppm works in points; 72 dpi is 1x, so the same zoom is 72 * scale dpi
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "page.pdf"
        src.write_bytes(pdf_bytes)
        stem = Path(tmp) / "page"
        r = subprocess.run([exe, "-png", "-r", f"{72 * scale:g}", "-f", "1", "-l", "1",
                            "-singlefile", str(src), str(stem)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        made = stem.with_suffix(".png")
        if r.returncode != 0 or not made.exists():
            return False
        png_path.write_bytes(made.read_bytes())
    return True


def save_outputs(pdf_bytes, out, src_name, archive=True, scale=2.0):
    """Write the PDF, keep a copy of it next to it as "current-keymap.pdf", file a
    dated copy in "previous-keymaps-visualizer", and make a PNG snapshot."""
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(pdf_bytes)
    if not archive:
        return None, None
    folder = out.parent / "previous-keymaps-visualizer"
    folder.mkdir(parents=True, exist_ok=True)
    today = date.today()
    dated = folder / f"keymap-{today}.pdf"
    if dated.exists() and dated.read_bytes() != pdf_bytes:
        # a second run on the same day: keep both, do not throw the old one away
        stamp = datetime.now().strftime("%H%M%S")
        dated = folder / f"keymap-{today}-{stamp}.pdf"
    dated.write_bytes(pdf_bytes)
    (out.parent / "current-keymap.pdf").write_bytes(pdf_bytes)
    png = out.parent / "preview.png"
    if snapshot_png(pdf_bytes, png, scale):
        return folder, png
    return folder, None


def find_config_dir(name="config"):
    """The folder the keymap file lives in: "config" next to where the command is run,
    or - if that is not there - next to this script."""
    here = Path.cwd() / name
    if here.is_dir():
        return here
    beside = Path(__file__).resolve().parent / name
    if beside.is_dir():
        return beside
    return here


def find_keymap(config, arg):
    """The keymap file, which is only ever looked for inside the config folder.

    With a name, that file in that folder is used; without one, the folder has to
    hold exactly one .keymap file.  A path that is given in full is taken as it
    is, so that a keymap from somewhere else can still be drawn."""
    if arg:
        p = Path(arg)
        if p.is_absolute() or len(p.parts) > 1:
            # a path that was spelled out in full - the caller means it
            if p.is_file():
                return p
            raise SystemExit(f"error: no keymap file at {p}")
        # a plain name: it is looked for in the config folder first ...
        for cand in (config / p.name, config / (p.stem + ".keymap"), config / (p.stem + ".c")):
            if cand.is_file():
                return cand
        # ... and then in the current folder, where a QMK keymap.c usually is
        here = Path.cwd() / p.name
        if here.is_file():
            return here
        raise SystemExit(f"error: no keymap file {arg!r} in {config}")
    # no name: the folder has to hold exactly one keymap file (.keymap for ZMK, else .c for QMK)
    for folder in (config, Path.cwd()):
        found = sorted(folder.glob("*.keymap")) or sorted(folder.glob("*.c"))
        if found:
            break
    if not found:
        raise SystemExit(f"error: no .keymap or .c file in {config}")
    if len(found) > 1:
        names = ", ".join(f.name for f in found)
        raise SystemExit(f"error: {folder} holds more than one keymap ({names}); "
                         f"say which one to use")
    return found[0]


def detect_format(path, text):
    """'qmk' for a keymap.c, 'zmk' for a .keymap (decided by the file ending, else by what is inside)."""
    ext = path.suffix.lower()
    if ext == ".keymap":
        return "zmk"
    if ext in (".c", ".h"):
        return "qmk"
    if re.search(r"\bkeymaps\s*\[", text) and re.search(r"\bKC_\w+|\bLAYOUT\w*\s*\(", text):
        return "qmk"
    return "zmk"


# --------------------------------------------------------------------------- video
# The flow chart drawn as a video: the arrows are drawn one after the other, each one following its own
# path from the key that triggers it to the layer it leads to. Nothing in the chart is redrawn: the page is
# rendered in layers (the chart without arrows, every arrow on its own, the labels) and the video only
# reveals pixels of those renders, along the exact path of each arrow - so the colours, widths, dashes,
# rounded corners and labels are the original ones. Needs numpy, PyMuPDF (or pdftoppm + Pillow) and ffmpeg
# (libx264, e.g. from the imageio-ffmpeg package); they are only imported when a video is made, so the
# PDF part stays standard library.
np = Image = cKDTree = None


VIDEO_FPS = 60
VIDEO_HOLD_START, VIDEO_HOLD_END = 0.5, 1.0        # seconds of the bare chart before, and of the finished chart after
VIDEO_DRAW_SECONDS = 7.0                     # all arrows are finished this long after the drawing starts
VIDEO_STAGGER = 0.22                         # between arrows that leave the same layer
VIDEO_SOFT = 5.0                             # softness of the drawing front, in page points
VIDEO_MIN_DUR, VIDEO_MAX_DUR = 1.1, 3.2            # fewest / most seconds an arrow takes to be drawn



VIDEO_FFMPEG = "ffmpeg"


def _vid_imports():
    """Load what the video needs. -> "" when all is there, else a message that says what to install.
    Needed: numpy; PyMuPDF (or pdftoppm + Pillow) to render the chart; ffmpeg (a system one, or the one that comes
    with the imageio-ffmpeg package). scipy is used when it is there (faster), but is not needed."""
    global np, Image, cKDTree, VIDEO_FFMPEG
    need, hint = [], []
    try:
        import numpy as np_
        np = np_
    except Exception:
        need.append("numpy")
    if import_pymupdf() is None:
        try:
            from PIL import Image as Image_
            Image = Image_
            if not shutil.which("pdftoppm"):
                raise ImportError
        except Exception:
            need.append("pymupdf")
    try:
        from scipy.spatial import cKDTree as KD
        cKDTree = KD
    except Exception:
        cKDTree = None
    exe = shutil.which("ffmpeg")
    if not exe:
        try:
            import imageio_ffmpeg
            exe = imageio_ffmpeg.get_ffmpeg_exe()
        except Exception:
            need.append("imageio-ffmpeg")
    VIDEO_FFMPEG = exe or "ffmpeg"
    if need:
        return ("it needs " + ", ".join(need) + ".\n  Install with:   " + Path(sys.executable).name
                + " -m pip install " + " ".join(need) + ("\n  (for ffmpeg you can also use: brew install ffmpeg)"
                                                         if "imageio-ffmpeg" in need else ""))
    return ""


def _vid_nearest(P, pt):
    """For every point of pt (n,2): the distance to the nearest point of P (m,2) and the index of that point."""
    if cKDTree is not None:
        return cKDTree(P).query(pt)
    d, idx = np.empty(len(pt)), np.empty(len(pt), int)
    P32 = P.astype(np.float32)
    for a in range(0, len(pt), 4000):                         # in pieces, to keep the memory small
        q = pt[a:a + 4000].astype(np.float32)
        dd = ((q[:, None, :] - P32[None, :, :]) ** 2).sum(axis=2)
        idx[a:a + 4000] = dd.argmin(axis=1)
        d[a:a + 4000] = np.sqrt(dd[np.arange(len(q)), idx[a:a + 4000]])
    return d, idx


def keyboard_name(path, text=""):
    """The name used in the video file name: the file name without the usual filler words (old-kyria.c -> kyria,
    cradio2.keymap -> cradio2); for a plain keymap.c it is the keyboard's folder in a QMK tree
    (keyboards/planck/keymaps/me/keymap.c -> planck), else the folder the file is in."""
    skip = ("keymap", "old", "new", "config")
    words = [w for w in re.split(r"[^A-Za-z0-9]+", path.stem)
             if w and w.lower() not in skip and not re.fullmatch(r"[0-9a-f]{8}", w.lower())]
    if words:
        return "-".join(words).lower()
    folders = [p.name for p in path.resolve().parents]
    if "keymaps" in folders and folders.index("keymaps") + 1 < len(folders):
        return folders[folders.index("keymaps") + 1].lower()
    return (folders[0] if folders and folders[0] not in ("config", "") else (folders[1] if len(folders) > 1 else "keyboard")).lower()


def _vid_render_layers(page, trace, width, work):
    """name -> numpy image. scene: no arrows, no labels. e<i>: scene + that arrow. alledges: all arrows, no labels.
    full: the page as it is."""
    edge_rng = [e["ops"] for e in trace["edges"]]
    label_rng = [l["ops"] for l in trace["labels"]]
    inside = lambda i, rngs: any(a <= i < b for a, b in rngs)
    variants = {
        "scene": lambda i: not inside(i, edge_rng) and not inside(i, label_rng),
        "alledges": lambda i: not inside(i, label_rng),
        "full": lambda i: True,
    }
    for k, rng in enumerate(edge_rng):
        variants[f"e{k}"] = (lambda rng: lambda i: (not inside(i, edge_rng) and not inside(i, label_rng))
                             or rng[0] <= i < rng[1])(rng)
    mupdf = import_pymupdf()
    procs, imgs = [], {}
    for name, keep in variants.items():
        v = copy.copy(page)
        v.ops = [o for i, o in enumerate(page.ops) if keep(i)]
        data = build_pdf([v], "chart")
        if mupdf is not None:                                  # PyMuPDF: no files, no other program
            doc = mupdf.open(stream=data, filetype="pdf")
            try:
                pg = doc[0]
                sc = width / pg.rect.width
                pix = pg.get_pixmap(matrix=mupdf.Matrix(sc, sc), alpha=False)
                imgs[name] = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.height, pix.width, pix.n)[:, :, :3].copy()
            finally:
                doc.close()
            continue
        pdf = work / f"{name}.pdf"
        pdf.write_bytes(data)
        procs.append((name, subprocess.Popen(
            ["pdftoppm", "-f", "1", "-l", "1", "-scale-to-x", str(width), "-scale-to-y", "-1", "-png",
             "-singlefile", str(pdf), str(work / name)])))
        while sum(p.poll() is None for _, p in procs) >= 2:        # two at a time
            procs[[p.poll() is None for _, p in procs].index(True)][1].wait()
    for name, p in procs:
        p.wait()
        imgs[name] = np.asarray(Image.open(work / f"{name}.png").convert("RGB"))
    return imgs


# --------------------------------------------------------------------------- 2. the exact path of an arrow
def _vid_rounded_polyline(pts, r, step=1.0):
    """The points of Canvas.rpath(pts, r) - straight pieces and the Bezier corners - every `step` points."""
    out = [pts[0]]

    def line_to(p):
        a = out[-1]
        n = max(1, int(math.hypot(p[0] - a[0], p[1] - a[1]) / step))
        for i in range(1, n + 1):
            out.append((a[0] + (p[0] - a[0]) * i / n, a[1] + (p[1] - a[1]) * i / n))

    for i in range(1, len(pts) - 1):
        a, b, c = pts[i - 1], pts[i], pts[i + 1]
        la, lc = math.hypot(a[0] - b[0], a[1] - b[1]), math.hypot(c[0] - b[0], c[1] - b[1])
        rr = min(r, la / 2, lc / 2)
        if rr < 0.5:
            line_to(b)
            continue
        p1 = (b[0] + (a[0] - b[0]) / la * rr, b[1] + (a[1] - b[1]) / la * rr)
        p2 = (b[0] + (c[0] - b[0]) / lc * rr, b[1] + (c[1] - b[1]) / lc * rr)
        line_to(p1)
        for k in range(1, 25):
            t = k / 24
            w = ((1 - t) ** 3, 3 * (1 - t) ** 2 * t + 3 * (1 - t) * t ** 2, t ** 3)
            out.append((w[0] * p1[0] + w[1] * b[0] + w[2] * p2[0], w[0] * p1[1] + w[1] * b[1] + w[2] * p2[1]))
    line_to(pts[-1])
    P = np.array(out, float)
    S = np.concatenate([[0], np.cumsum(np.hypot(*np.diff(P, axis=0).T))])
    return P, S


class _VidArrow:
    """The pixels that belong to one arrow, each with the part of the arrow it is (the line, a trigger dot, the
    head, a join) and how far along the path it is."""

    def __init__(self, tr, imgs, k, sx, sy):
        self.tr = tr
        scene, own = imgs["scene"], imgs[f"e{k}"]
        ys, xs = np.nonzero(np.any(own != scene, axis=2))
        self.ys, self.xs, self.vals = ys, xs, own[ys, xs]
        pt = np.stack([(xs + 0.5) / sx, (ys + 0.5) / sy], axis=1)
        self.main_P, self.main_S = _vid_rounded_polyline(tr["pts"], tr["rad"])
        self.L = float(self.main_S[-1])
        paths = [(self.main_P, self.main_S)]
        for jp in tr["joins"]:
            paths.append(_vid_rounded_polyline(jp, 20))
        dist = np.full(len(pt), np.inf)
        self.s = np.zeros(len(pt))
        self.part = np.zeros(len(pt), int)                   # 0 line, 1 dot, 2 head, 3+ joins
        for j, (P, S) in enumerate(paths):
            d, idx = _vid_nearest(P, pt)
            better = d < dist
            dist[better], self.s[better], self.part[better] = d[better], S[idx[better]], (0 if j == 0 else 2 + j)
        end = np.array(tr["end"])
        self.part[np.hypot(*(pt - end).T) <= tr["HEAD"] * 1.25] = 2
        for dx, dy in tr["dots"]:
            self.part[np.hypot(pt[:, 0] - dx, pt[:, 1] - dy) <= tr["DOT"] + 5] = 1
        self.dot_idx = self.part == 1
        self.head_idx = self.part == 2
        self.start_xy = tr["pts"][0]
        self.t0 = self.dur = 0.0
        self.labels = []

    def front(self, tau):
        u = min(1.0, max(0.0, (tau - self.t0) / self.dur))
        return self.L * _vid_ease(u)

    def alpha(self, tau):
        a = np.zeros(len(self.ys))
        if tau <= self.t0:
            return a
        f = self.front(tau)
        line = self.part == 0
        a[line] = np.clip((f - self.s[line]) / VIDEO_SOFT, 0, 1)
        a[self.dot_idx] = min(1.0, (tau - self.t0) / 0.14)
        head_start = self.L - self.tr["HEAD"] * 1.25
        a[self.head_idx] = np.clip((f - head_start) / (self.L - head_start), 0, 1) ** 1.5 if f < self.L else 1.0
        for j in range(len(self.tr["joins"])):          # joins: a short elbow, drawn in the first 0.3 s
            m = self.part == 3 + j
            if m.any():
                reach = min(1.0, (tau - self.t0) / 0.3) * self.s[m].max()
                a[m] = np.clip((reach - self.s[m]) / VIDEO_SOFT, 0, 1)
        return a


def _vid_ease(u):
    """Gentle _vid_ease in and out (half sine, half linear): smooth start and stop without a slow crawl."""
    return 0.5 * u + 0.5 * (0.5 - 0.5 * math.cos(math.pi * u))


def _vid_ease_inv(p):
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if _vid_ease(mid) < p else (lo, mid)
    return (lo + hi) / 2


# --------------------------------------------------------------------------- 3. the order they are drawn in
def _vid_schedule(arrows):
    """Start time and duration of every arrow, following the connections of the chart: the arrows that leave the
    base layer first, then, as soon as a layer has been reached, the arrows that leave that layer."""
    def plan(v):
        reached, done = {0: 0.0}, {}
        order = []
        todo = list(range(len(arrows)))
        while todo:
            ready = [i for i in todo if arrows[i].tr["src"] in reached]
            if not ready:                                   # a layer nothing leads to: it starts on its own
                reached[min(arrows[i].tr["src"] for i in todo)] = 0.0
                continue
            src = min((arrows[i].tr["src"] for i in ready), key=lambda s: reached[s])
            group = sorted((i for i in ready if arrows[i].tr["src"] == src), key=lambda i: arrows[i].start_xy[0])
            for n, i in enumerate(group):
                a = arrows[i]
                a.dur = min(VIDEO_MAX_DUR, max(VIDEO_MIN_DUR, a.L / v))
                a.t0 = reached[src] + (0.12 if src in reached and reached[src] > 0 else 0.0) + n * VIDEO_STAGGER
                fin = a.t0 + a.dur
                dst = a.tr["dst"]
                reached[dst] = min(reached.get(dst, 1e9), fin)
                order.append(i)
                todo.remove(i)
        return max(a.t0 + a.dur for a in arrows)

    lo, hi = 200.0, 60000.0                                  # speed in page points per second
    for _ in range(60):
        mid = math.sqrt(lo * hi)
        if plan(mid) > VIDEO_DRAW_SECONDS:
            lo = mid
        else:
            hi = mid
    plan(hi)



def make_video(page, trace, outdir="video", name="keyboard", day=None, width=3840, crf=16):
    """Write <outdir>/<name>-<day>.mp4 from the flow-chart page and the trace of where its arrows are."""
    day = day or date.today().isoformat()
    work = Path(tempfile.mkdtemp(prefix="flowvideo_"))
    print("rendering the chart in layers ...", file=sys.stderr)
    imgs = _vid_render_layers(page, trace, width, work)
    H, W = imgs["full"].shape[:2]
    W, H = W - W % 2, H - H % 2                                   # even sizes for yuv420
    imgs = {k: v[:H, :W] for k, v in imgs.items()}
    sx, sy = W / page.w, H / page.h
    scene, full = imgs["scene"], imgs["full"]

    arrows = [_VidArrow(t, imgs, k, sx, sy) for k, t in enumerate(trace["edges"])]
    _vid_schedule(arrows)
    by_id = {t["id"]: ar for t, ar in zip(trace["edges"], arrows)}

    # labels: the pixels that differ between 'all arrows' and 'the full page', shown when the arrow reaches them
    lab_changed = np.any(full != imgs["alledges"], axis=2)
    labels = []
    for lb in trace["labels"]:
        ar = by_id[lb["id"]]
        x, y, w, h = lb["box"]
        x0, x1, y0, y1 = int((x - 6) * sx), int((x + w + 6) * sx) + 1, int((y - 6) * sy), int((y + h + 6) * sy) + 1
        m = np.zeros_like(lab_changed)
        m[max(y0, 0):y1, max(x0, 0):x1] = lab_changed[max(y0, 0):y1, max(x0, 0):x1]
        ys, xs = np.nonzero(m)
        P, S = ar.main_P, ar.main_S
        c = np.array([x + w / 2, y + h / 2])
        i = int(np.argmin(np.hypot(*(P - c).T)))
        tang = P[min(i + 3, len(P) - 1)] - P[max(i - 3, 0)]
        tang = tang / (np.hypot(*tang) or 1)
        s_trig = min(ar.L, S[i] + 0.5 * w * abs(tang[0]))     # a label sitting on a horizontal piece: after it
        t_trig = ar.t0 + ar.dur * _vid_ease_inv(s_trig / ar.L)
        labels.append((t_trig, ys, xs, full[ys, xs]))

    total = VIDEO_HOLD_START + max(ar.t0 + ar.dur for ar in arrows) + 0.25 + VIDEO_HOLD_END
    n_frames = int(round(total * VIDEO_FPS))
    print(f"{W}x{H}, {n_frames} frames, {total:.2f} s; arrows finish at "
          f"{VIDEO_HOLD_START + max(ar.t0 + ar.dur for ar in arrows):.2f} s", file=sys.stderr)
    for ar in arrows:
        t = ar.tr
        print(f"  {t['id']}: layer {t['src']} -> {t['dst']}  start {VIDEO_HOLD_START + ar.t0:.2f}s  "
              f"draw {ar.dur:.2f}s  ({ar.L:.0f} pt)", file=sys.stderr)

    out_dir = Path(outdir)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / f"{name}-{day}.mp4"
    cmd = [VIDEO_FFMPEG, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{W}x{H}",
           "-r", str(VIDEO_FPS), "-i", "-",
           "-vf", "scale=in_range=full:out_range=tv:out_color_matrix=bt709,format=yuv420p",
           "-c:v", "libx264", "-preset", "slow", "-crf", str(crf), "-tune", "animation",
           "-profile:v", "high", "-level", "5.2", "-g", str(VIDEO_FPS * 4), "-r", str(VIDEO_FPS),
           "-colorspace", "bt709", "-color_primaries", "bt709", "-color_trc", "bt709", "-color_range", "tv",
           "-movflags", "+faststart", "-an", str(out)]
    ff = subprocess.Popen(cmd, stdin=subprocess.PIPE)
    last = None
    done_at = VIDEO_HOLD_START + max(ar.t0 + ar.dur for ar in arrows) + 0.25
    for k in range(n_frames):
        t = k / VIDEO_FPS
        tau = t - VIDEO_HOLD_START
        if t >= done_at + 0.2:
            frame = full                                       # the finished chart, exactly as rendered
        elif tau <= 0:
            frame = scene
        else:
            frame = scene.copy()
            for ar in arrows:                                  # in the order the chart paints them
                al = ar.alpha(tau)
                sel = al > 0
                if sel.any():
                    ys, xs, al = ar.ys[sel], ar.xs[sel], al[sel, None]
                    cur = frame[ys, xs].astype(np.float32)
                    frame[ys, xs] = np.rint(cur + (ar.vals[sel].astype(np.float32) - cur) * al).astype(np.uint8)
            for t_trig, ys, xs, vals in labels:
                al = min(1.0, max(0.0, (tau - t_trig) / 0.18))
                if al > 0:
                    cur = frame[ys, xs].astype(np.float32)
                    frame[ys, xs] = np.rint(cur + (vals.astype(np.float32) - cur) * al).astype(np.uint8)
        ff.stdin.write(frame.tobytes())
        if k % 60 == 0:
            print(f"  frame {k}/{n_frames}", file=sys.stderr)
    ff.stdin.close()
    if ff.wait():
        sys.exit("ffmpeg failed")
    shutil.rmtree(work, ignore_errors=True)
    return out



def main():
    ap = argparse.ArgumentParser(description="Draw a ZMK .keymap or a QMK keymap.c as a 2-page PDF: "
                                             "layer flow chart + keymap text.")
    ap.add_argument("keymap", nargs="?",
                    help="the ONE keymap file: a ZMK .keymap or a QMK keymap.c (looked for in the config folder, "
                         "then in the current folder)")
    ap.add_argument("--format", choices=("auto", "zmk", "qmk"), default="auto",
                    help="zmk or qmk (default: auto - .keymap is ZMK, .c is QMK)")
    ap.add_argument("--split", choices=("auto", "yes", "no"), default="auto",
                    help="QMK only: draw the keyboard as two halves with a gap (yes) or as one block (no)")
    ap.add_argument("-o", "--output", help="output PDF (default: <keymap>.pdf in the current folder)")
    ap.add_argument("--config", default="config",
                    help="folder the keymap file is in (default: config)")
    ap.add_argument("--rows", help="keys per row, e.g. 10,10,10,4 (only if auto-detection fails)")
    ap.add_argument("--open", action="store_true", help="open the PDF when done")
    ap.add_argument("--no-archive", action="store_true",
                    help="do not write current-keymap.pdf / previous-keymaps-visualizer/ / preview.png")
    ap.add_argument("--preview-scale", type=float, default=2.0,
                    help="zoom of the preview.png snapshot (default: 2)")
    ap.add_argument("--no-video", action="store_true",
                    help="do not write the video of the flow chart being drawn (video/<keyboard>-<date>.mp4, "
                         "60 FPS H.264; it needs numpy, scipy, Pillow, pdftoppm and ffmpeg, and is skipped "
                         "with a note when they are missing)")
    ap.add_argument("--video-dir", help="folder for the video (default: a folder called video next to the PDF)")
    ap.add_argument("--video-name", help="keyboard name in the video file name (default: found from the file name)")
    ap.add_argument("--video-width", type=int, default=3840, help="width of the video in pixels (default: 3840)")
    ap.add_argument("--video-crf", type=int, default=16, help="x264 quality: lower is better and larger (default: 16)")
    a = ap.parse_args()

    config = find_config_dir(a.config)
    path = find_keymap(config, a.keymap)
    text = path.read_text(encoding="utf-8", errors="replace")
    rows = [int(x) for x in a.rows.split(",")] if a.rows else None
    fmt = detect_format(path, text) if a.format == "auto" else a.format
    if fmt == "qmk":
        layers, combos, row_lens, defines = parse_qmk(
            text, rows, {"auto": None, "yes": True, "no": False}[a.split], hint=str(path.resolve()))
    else:
        layers, combos, row_lens, defines = parse_keymap(text, rows, base_dir=path.parent)
    if not layers:                        # nothing to draw: say so and write nothing
        print(f"{path.name}: no layers found, nothing written", file=sys.stderr)
        sys.exit(1)
    # the PDF and the copies of it go in the folder the command is run from, not
    # in the config folder with the keymap
    out = Path(a.output) if a.output else Path.cwd() / (path.stem + ".pdf")
    global FLOW_TRACE
    video_note, video_dir = "", None
    if not a.no_video:
        try:
            video_dir = Path(a.video_dir) if a.video_dir else out.parent / "video"
            video_dir.mkdir(parents=True, exist_ok=True)        # the folder is made when it is not there
            video_note = _vid_imports()
        except Exception as err:                                # never let the video get in the way of the PDF
            video_note = f"could not set it up ({err})"
        if not video_note:
            FLOW_TRACE = {"edges": [], "labels": []}
    if fmt == "qmk":                      # page 2 is the keymap.c without its comments
        pages = [flow_page(layers, combos, row_lens, defines, path.name), source_page(strip_c_comments(text), path.name)]
    else:
        pages = [flow_page(layers, combos, row_lens, defines, path.name),
                 text_page(keymap_text(text, sum(row_lens)), path.name)]
    data = build_pdf(pages, path.name)
    folder, png = save_outputs(data, out, path.name,
                               archive=not a.no_archive, scale=a.preview_scale)
    print(f"{path.name} ({fmt.upper()}): {len(layers)} layers, {sum(row_lens)} keys {row_lens}, {len(combos)} combos")
    if QMK_INFO:
        print("layout: " + (f"{QMK_INFO[0]} confidence, {QMK_INFO[1]}" if len(QMK_INFO) > 1 else QMK_INFO[0]))
    print(f"read {path}")
    print(f"wrote {out}")
    if folder is not None:
        print(f"wrote {out.parent / 'current-keymap.pdf'}")
        print(f"wrote {folder / f'keymap-{date.today()}.pdf'}")
    if png is not None:
        print(f"wrote {png}")
    elif folder is not None:
        print("note: could not render preview.png (no PyMuPDF and no pdftoppm)", file=sys.stderr)
    if not a.no_video:
        try:
            if video_note:
                print(f"\nNO VIDEO WRITTEN: {video_note}")
            elif not FLOW_TRACE["edges"]:
                print("\nno video: the keymap has no arrows to draw (one layer)")
            else:
                print("making the video (about 30 seconds) ...", flush=True)
                movie = make_video(pages[0], FLOW_TRACE, video_dir, a.video_name or keyboard_name(path, text),
                                   width=a.video_width, crf=a.video_crf)
                print(f"wrote {movie}  ({movie.stat().st_size / 1e6:.1f} MB)")
        except BaseException as err:                            # the PDF is already written: the video is a bonus
            if isinstance(err, KeyboardInterrupt):
                print("\nvideo stopped")
            else:
                print(f"\nNO VIDEO WRITTEN: {err or type(err).__name__}")
    if a.open:
        webbrowser.open(out.resolve().as_uri())


if __name__ == "__main__":
    main()
