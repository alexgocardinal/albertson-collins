"""Compile the two LaTeX documents twice on a normal TeX Live installation."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("Install TeX Live with pdflatex and the packages listed in README.md.")
    for relative in ["paper/canonical_coloring.tex", "verification/proof_and_audit.tex"]:
        source = ROOT / relative
        for _ in range(2):
            subprocess.run(
                [executable, "-interaction=nonstopmode", "-halt-on-error",
                 f"-output-directory={source.parent}", str(source)],
                cwd=ROOT, check=True,
            )
        print(source.with_suffix(".pdf"))


if __name__ == "__main__":
    main()
