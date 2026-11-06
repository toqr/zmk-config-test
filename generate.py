from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import letter
from datetime import date
from io import BytesIO
from pathlib import Path
output = BytesIO()
pdf = canvas.Canvas(output, pagesize=letter)
pdf.drawString(100, 750, "Hello World!")
pdf.save()
data = output.getvalue()
folder = Path("previous-keymaps-visualizer")
folder.mkdir(exist_ok=True)
(folder / f"keymap-{date.today()}.pdf").write_bytes(data)
Path("current-keymap.pdf").write_bytes(data)
