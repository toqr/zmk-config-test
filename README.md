# zmk-config-test

previously edited with https://nickcoutsos.github.io/keymap-editor/ but it depreciated<br>
<br><br>
edit directly from keymap file, with flowchart below (click below)<br><br>
[View PDF](current-keymap.pdf)
[![Keymap Preview](preview.png)](preview.png) 

## known limitations and assumptions for generate.py
- does not work with qmk
- keymaps with large key clusters are not displayed well
- parser depends on newlines for next row -> keymap must use standard layout (ie 5 keys left, 5 keys right, \n...)
- qmk can be unibody / variable names may not be reliable -> assume it will always be a symmetric split or fails
