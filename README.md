# zmk-config-test

previously edited with https://nickcoutsos.github.io/keymap-editor/ but it depreciated<br>
it was pretty helpful to learn how to edit keymap.
<br><br>
edit directly from keymap file, with flowchart below (click below)<br><br>
[View PDF](current-keymap.pdf)
[![Keymap Preview](preview.png)](preview.png) 

### generate.py
- reads a single *.keymap (ZMK) or *.c (QMK) file from folder 'config'
- creates 2 page pdf (flow chart png + keymap code) named as keymap-{date}.pdf and current-keymap.pdf
- rewrites preview.png for above
  
### known limitations and assumptions for generate.py
- parser depends on newlines for next row -> keymap use standard layout (ie 5 keys left, 5 keys right, \n...)
- assumes that there are layer keys -> if none, will not display
