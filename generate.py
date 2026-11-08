#!/usr/bin/env python3
"""
zmk_visualizer.py - turn a ZMK .keymap into a 2-page PDF.

    python3 zmk_visualizer.py my.keymap                 # writes my.pdf
    python3 zmk_visualizer.py my.keymap -o out.pdf --open
    python3 zmk_visualizer.py my.keymap --rows 10,10,10,4   # only if the key rows can't be detected

The keymap file is looked for in the "config" folder and nowhere else: give its name, or leave
the name out and the one .keymap file in that folder is used.

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
Page 2 - the whole keymap as text, with every comment removed.

Standard library only. Comments in the .keymap (including boxed/aligned ones) are ignored.
"""
import argparse
import itertools
import math
import re
import sys
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


BEH = {}        # behaviours defined in the file: label -> {"compat", "bindings", "mode"}


def parse_behaviors(root):
    BEH.clear()

    def walk(nodes):
        for header, body in nodes:
            comp = re.search(r'compatible\s*=\s*"([^"]*)"', body)
            if comp and "behavior" in comp.group(1) and ":" in header:
                bd = re.search(r"\bbindings\s*=\s*([^;]*);", body)
                mode = re.search(r'toggle-mode\s*=\s*"([^"]*)"', body)
                BEH[header.split(":")[0].strip()] = {
                    "compat": comp.group(1),
                    "bindings": re.findall(r"&(\w+)", bd.group(1)) if bd else [],
                    "mode": mode.group(1) if mode else "toggle"}
            walk(parse_nodes(body))
    walk(root)


def parse_keymap(text, forced_rows=None):
    global BINDING_STARTS, ROW_LEFTS
    clean, defines, BINDING_STARTS = preprocess(strip_comments_marked(text))
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
    else:
        first = [len(l) for l in layers[0]["lines"]]
        row_lens = first if len(first) > 1 else guess_rows(len(layers[0]["flat"]))
        if len(first) > 1 and lefts0 and any(k is not None for k in lefts0):
            ROW_LEFTS = [k if k is not None else n // 2 for k, n in zip(lefts0, row_lens)]
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
        ly = re.search(r"\blayers\s*=\s*<([^>]*)>", body)
        to = re.search(r"timeout-ms\s*=\s*<(\d+)>", body)
        nm = header.split(":")[-1].strip()
        combos.append({"name": nm[6:] if nm.startswith("combo_") else nm,
                       "positions": [int(x) for x in re.findall(r"\d+", kp.group(1))],
                       "binding": " ".join(bd.group(1).split()),
                       "layers": [int(x) for x in re.findall(r"-?\d+", ly.group(1)) if int(x) >= 0] if ly else None,
                       "timeout": int(to.group(1)) if to else None})
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
    "C_STOP": "Stop",
}
MODFN = {"S": "Shift", "C": "Ctrl", "A": "Alt", "G": "GUI"}
ARROW = {"LEFT": "←", "DOWN": "↓", "UP": "↑", "RIGHT": "→"}
MKP = {"MB1": "Btn 1", "MB2": "Btn 2", "MB3": "Btn 3", "MB4": "Btn 4", "MB5": "Btn 5",
       "LCLK": "Left Click", "RCLK": "Right Click", "MCLK": "Mid Click"}


SHIFTED = {"N1": "!", "N2": "@", "N3": "#", "N4": "$", "N5": "%", "N6": "^", "N7": "&", "N8": "*",
           "N9": "(", "N0": ")", "MINUS": "_", "EQUAL": "+", "SEMI": ":", "SQT": '"', "COMMA": "<",
           "DOT": ">", "FSLH": "?", "LBKT": "{", "RBKT": "}", "BSLH": "|", "GRAVE": "~"}


def kp_label(code):
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
    edges = []
    for (src, dst, kind, via, name), pos in grouped.items():
        edges.append({"id": f"e{len(edges)}", "src": src, "dst": dst, "kind": kind,
                      "via": via, "name": name, "positions": pos})
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
KIND_WORD = {"off": "off", "hold": "hold", "toggle": "toggle", "switch": "go to", "oneshot": "1-shot", "taphold": "hold"}
SIZES = [36 - 0.5 * i for i in range(56)]          # label font sizes tried, biggest first (36 .. 8.5)


def layer_color(i):
    return "#a8a8a8" if i == 0 else PALETTE[(i - 1) % len(PALETTE)]


# --------------------------------------------------------------------------- key labels
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
            tap = label(f"&{ht[1]} {p[2]}")[0] if len(p) > 2 else ""
            return tap, name, False, True
        return name, {"hold": "", "toggle": "toggle", "switch": "go to", "oneshot": "1-shot",
                      "off": "turn off"}[kind], True, False
    if ht and len(p) > 2:                             # a mod-tap: tap = the key, hold = the modifier
        return label(f"&{ht[1]} {p[2]}")[0], label(f"&{ht[0]} {p[1]}")[0], False, False
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
class Board:
    """Split keyboard: left/right halves, short bottom row sits under the inner columns."""

    def __init__(self, row_lens, ks, gap, split):
        self.ks, self.gap, self.split = ks, gap, split
        lefts = [(ROW_LEFTS[r] if ROW_LEFTS and len(ROW_LEFTS) == len(row_lens) else n // 2)
                 for r, n in enumerate(row_lens)]
        M = max(max(lf, n - lf) for lf, n in zip(lefts, row_lens))
        self.cells = []
        for r, n in enumerate(row_lens):
            left = lefts[r]
            for i in range(n):
                slot = (M - left + i) if i < left else (M + i - left)
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
    depth = col_of

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
        ps = [p for p in e["positions"] if p < len(board.cells)]
        trig_cells[e["id"]] = sorted([board.cells[p] for p in ps], key=lambda cl: cl[0])

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
            ps = [p for p in e["positions"] if p < len(board.cells)]
            cells = [board.cells[p] for p in ps]
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
            ps = [p for p in e["positions"] if p < len(board.cells)]
            cells = [board.cells[p] for p in ps]
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
            if anchor_leg[e["id"]] == "side":
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
                if kx - cx0 <= cx0 + nw - kx:
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

            if m == "fwd":
                lx = lane[("fwd", e["id"])]
                pts += [(lx, y0), (lx, ey)]
            elif m == "corr":
                l1, l2 = lane[("descF", e["id"])], lane[("ascF", e["id"])]
                cy = corridor[e["id"]]
                pts += [(l1, y0), (l1, cy), (l2, cy), (l2, ey)]
            elif m == "same":
                lx = lane[("same", e["id"])]
                pts += [(lx, y0), (lx, ey)]
            else:                                  # it has to point back
                l1, l2 = lane[("descB", e["id"])], lane[("ascB", e["id"])]
                if depth[j] == 0:                   # the base layer: come up on its left
                    l2 = XCOL[0] - 62
                cy = corridor[e["id"]]
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
    oy = bottom + VGAP + CORR                  # where the combos panel starts
    # the page ends just below the lowest thing that is actually drawn: the combos
    # panel, or - when there is none - the corridor lines under the layers
    if combos:
        PH = oy + ch + 76 + PM
    else:
        PH = bottom + 78 + 96 * max(0, ncorr - 1) + 48 + PM
    c = Canvas(PW, PH, bg=th["bg"])

    c.text(PM, PM + 56, src_name, 58, th["title"])
    c.text(PM, PM + 100, f"{len(layers)} layers   ·   {sum(row_lens)} keys   ·   {len(all_combos)} combos", 26, th["sub"])
    c.text(PM, PM + 136, "every arrow starts on the key that triggers it", 22, th["dim"])
    c.rect(PM, PM + 162, 190, 5, fill=layer_color(1), r=3)
    draw_legend(c, PW - PM - 660, PM - 6, th, bool(kcombos))

    # ---- 1. a soft band behind every column, so the layers are grouped
    for c_ in range(ncols):
        ct = min(ypos[i] for i in cols[c_])
        cb = max(ypos[i] + nh[i] for i in cols[c_])
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

    def kstate(L, k):
        if k in held_by[L["idx"]]:
            return "held"
        b = L["flat"][k]
        if is_toggle_key(b) and layer_action(b, defines):
            return "toggle"
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
        c.rect(ax - w / 2, ay - h / 2, w, h, fill=th["bg"], stroke=col, sw=3.5, r=h / 2)
        c.text(ax, ay + 8.5, txt, 24, col, anchor="middle")

    # ---- 7. combos
    if combos:
        c.text(PM, oy + 44, "combos", 46, th["title"])
        c.text(PM + tw("combos", 46) + 28, oy + 44, "press the red keys together", 26, th["sub"])
        draw_combos(c, placed, PM, oy + 96, mini, th)
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
            cells[(M - left + i) if i < left else (M + i - left)] = b
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

    try:
        import fitz
    except ImportError:
        fitz = None
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
        # a plain name: it is looked for in the config folder and nowhere else
        for cand in (config / p.name, config / (p.stem + ".keymap")):
            if cand.is_file():
                return cand
        raise SystemExit(f"error: no keymap file {arg!r} in {config}")
    found = sorted(config.glob("*.keymap"))
    if not found:
        raise SystemExit(f"error: no .keymap file in {config}")
    if len(found) > 1:
        names = ", ".join(f.name for f in found)
        raise SystemExit(f"error: {config} holds more than one keymap ({names}); "
                         f"say which one to use")
    return found[0]


def main():
    ap = argparse.ArgumentParser(description="Draw a ZMK keymap as a 2-page PDF: layer flow chart + keymap text.")
    ap.add_argument("keymap", nargs="?", help="name of the keymap file inside the config folder")
    ap.add_argument("-o", "--output", help="output PDF (default: <keymap>.pdf in the current folder)")
    ap.add_argument("--config", default="config",
                    help="folder the keymap file is in (default: config)")
    ap.add_argument("--rows", help="keys per row, e.g. 10,10,10,4 (only if auto-detection fails)")
    ap.add_argument("--open", action="store_true", help="open the PDF when done")
    ap.add_argument("--no-archive", action="store_true",
                    help="do not write current-keymap.pdf / previous-keymaps-visualizer/ / preview.png")
    ap.add_argument("--preview-scale", type=float, default=2.0,
                    help="zoom of the preview.png snapshot (default: 2)")
    a = ap.parse_args()

    config = find_config_dir(a.config)
    path = find_keymap(config, a.keymap)
    text = path.read_text(encoding="utf-8", errors="replace")
    rows = [int(x) for x in a.rows.split(",")] if a.rows else None
    layers, combos, row_lens, defines = parse_keymap(text, rows)
    # the PDF and the copies of it go in the folder the command is run from, not
    # in the config folder with the keymap
    out = Path(a.output) if a.output else Path.cwd() / (path.stem + ".pdf")
    pages = [flow_page(layers, combos, row_lens, defines, path.name),
             text_page(keymap_text(text, sum(row_lens)), path.name)]
    data = build_pdf(pages, path.name)
    folder, png = save_outputs(data, out, path.name,
                               archive=not a.no_archive, scale=a.preview_scale)
    print(f"{path.name}: {len(layers)} layers, {sum(row_lens)} keys {row_lens}, {len(combos)} combos")
    print(f"read {path}")
    print(f"wrote {out}")
    if folder is not None:
        print(f"wrote {out.parent / 'current-keymap.pdf'}")
        print(f"wrote {folder / f'keymap-{date.today()}.pdf'}")
    if png is not None:
        print(f"wrote {png}")
    elif folder is not None:
        print("note: could not render preview.png (no PyMuPDF and no pdftoppm)", file=sys.stderr)
    if a.open:
        webbrowser.open(out.resolve().as_uri())


if __name__ == "__main__":
    main()
