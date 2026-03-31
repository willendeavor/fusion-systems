from __future__ import annotations

import re
import sys
from pathlib import Path


INTRINSIC_START_RE = re.compile(
    r"^\s*intrinsic\s+([A-Za-z_][A-Za-z0-9_]*)\s*\((.*?)\)\s*(?::\s*(.*?))?\s*->\s*(.*?)\s*$",
    re.IGNORECASE,
)

INTRINSIC_END_RE = re.compile(r"^\s*end\s+intrinsic\s*;?\s*$", re.IGNORECASE)


def clean_whitespace(s: str) -> str:
    """Collapse repeated whitespace and trim ends."""
    return " ".join(s.strip().split())


def parse_intrinsic_header(header_lines: list[str]) -> dict[str, str] | None:
    """
    Parse a MAGMA intrinsic header from one or more lines.

    Expected general shape:
        intrinsic Name(arg1::Type, arg2::Type : opt:=...) -> ReturnType
    """
    header_text = " ".join(line.strip() for line in header_lines)
    header_text = clean_whitespace(header_text)

    match = INTRINSIC_START_RE.match(header_text)
    if not match:
        return None

    name = match.group(1)
    parameters = clean_whitespace(match.group(2) or "")
    optional_parameters = clean_whitespace(match.group(3) or "")
    outputs = clean_whitespace(match.group(4) or "")

    if optional_parameters:
        full_parameters = f"{parameters} : {optional_parameters}"
    else:
        full_parameters = parameters

    signature = f"`{name}({full_parameters}) -> {outputs}`"

    return {
        "name": name,
        "parameters": full_parameters,
        "outputs": outputs,
        "signature": signature,
    }


def extract_intrinsics(text: str) -> list[dict[str, str]]:
    """
    Extract intrinsic signatures from a MAGMA source file.

    This supports headers split across multiple lines, as long as the full
    intrinsic declaration appears before the body begins.
    """
    lines = text.splitlines()
    intrinsics: list[dict[str, str]] = []

    i = 0
    while i < len(lines):
        line = lines[i]

        if re.match(r"^\s*intrinsic\b", line, re.IGNORECASE):
            header_lines = [line]
            j = i + 1

            # Keep reading until we see an arrow and can parse the header.
            while j < len(lines):
                candidate = parse_intrinsic_header(header_lines)
                if candidate is not None:
                    intrinsics.append(candidate)
                    break

                # Stop if we somehow hit the end before parsing a valid header.
                if INTRINSIC_END_RE.match(lines[j]):
                    break

                header_lines.append(lines[j])
                j += 1

            i = j
        else:
            i += 1

    return intrinsics


def make_markdown(source_file: Path, intrinsics: list[dict[str, str]]) -> str:
    lines: list[str] = [f"# {source_file.name}", ""]

    for intrinsic in intrinsics:
        lines.append(f"### {intrinsic['name']}")
        lines.append(intrinsic["signature"])
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def write_markdown_for_file(input_path: str | Path, output_path: str | Path | None = None) -> Path:
    input_path = Path(input_path)

    if not input_path.exists():
        raise FileNotFoundError(f"Input file does not exist: {input_path}")

    text = input_path.read_text(encoding="utf-8")
    intrinsics = extract_intrinsics(text)

    if output_path is None:
        output_path = input_path.with_suffix(".md")
    else:
        output_path = Path(output_path)

    markdown = make_markdown(input_path, intrinsics)
    output_path.write_text(markdown, encoding="utf-8")

    return output_path


def main() -> None:
    if len(sys.argv) not in {2, 3}:
        print("Usage:")
        print("  python magma_intrinsics_to_md.py input.m [output.md]")
        raise SystemExit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) == 3 else None

    written = write_markdown_for_file(input_file, output_file)
    print(f"Wrote documentation to: {written}")


if __name__ == "__main__":
    main()