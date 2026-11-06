from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import letter
from datetime import date
from io import BytesIO
from pathlib import Path
import fitz

output = BytesIO()
pdf = canvas.Canvas(output, pagesize=letter)

pdf.drawString(100, 750, "Hello World!")

pdf.save()
data = output.getvalue()

folder = Path("previous-keymaps-visualizer")
folder.mkdir(exist_ok=True)

Path("current-keymap.pdf").write_bytes(data)
(folder / f"keymap-{date.today()}.pdf").write_bytes(data)

document = fitz.open(stream=data, filetype="pdf")
page = document[0]

pixmap = page.get_pixmap(matrix=fitz.Matrix(2, 2), alpha=False)
pixmap.save("preview.png")

document.close()
