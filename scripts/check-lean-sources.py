#!/usr/bin/env python3
"""Read-only checks for the local Palomar source contract.

This checks source layout and lexical proof holes; Audit.lean checks transitive
axiom dependencies, and Comparator checks the independent theorem statement.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXCLUDED = {".git", ".lake"}
COMPILED = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}


def code_only(source: str) -> str:
    """Blank nested Lean comments and strings without removing newlines."""
    out = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out[i:i + 2] = "  "
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
            else:
                if source[i] not in "\r\n":
                    out[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                out[i] = " "
                i += 1
                if i < len(source):
                    if source[i] not in "\r\n":
                        out[i] = " "
                    i += 1
            else:
                string = source[i] != '"'
                if source[i] not in "\r\n":
                    out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif source.startswith("--", i):
            while i < len(source) and source[i] not in "\r\n":
                out[i] = " "
                i += 1
        elif source[i] == '"':
            string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    return "".join(out)


def main() -> int:
    errors: list[str] = []
    source_count = 0
    specification_holes = 0
    advertised = len(json.loads((ROOT / "comparator.json").read_text())["theorem_names"])
    for path in sorted(ROOT.rglob("*")):
        relative = path.relative_to(ROOT)
        if any(part in EXCLUDED for part in relative.parts):
            continue
        if path.suffix == ".lean" and path.is_symlink():
            errors.append(f"{relative}: Lean source symbolic links are not permitted")
            continue
        if not path.is_file():
            continue
        if path.suffix in COMPILED:
            errors.append(f"{relative}: compiled output belongs below .lake")
        if path.suffix != ".lean":
            continue
        source_count += 1
        source = path.read_text(encoding="utf-8")
        code = code_only(source)
        lines = len(source.splitlines())
        if lines > 10_000:
            errors.append(f"{relative}: {lines} physical lines exceed the 10,000-line cap")
        if path.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
            errors.append(f"{relative}: missing module header")
        holes = list(re.finditer(r"\b(sorry|admit|axiom)\b", code))
        if relative == pathlib.Path("Challenge.lean"):
            if lines > 1_000 or len(source.encode("utf-8")) > 100 * 1024:
                errors.append("Challenge.lean: exceeds 1,000 lines or 100 KiB")
            specification_holes += len(holes)
            if any(h.group() != "sorry" for h in holes) or len(holes) != advertised:
                errors.append("Challenge.lean: one deliberate statement-only sorry per advertised theorem is required")
        else:
            for hole in holes:
                line = source.count("\n", 0, hole.start()) + 1
                errors.append(f"{relative}:{line}: proof development contains {hole.group()}")

    manifest = ROOT / "lake-manifest.json"
    if not manifest.is_file():
        errors.append("lake-manifest.json: missing dependency manifest")
    else:
        data = json.loads(manifest.read_text(encoding="utf-8"))
        for package in data.get("packages", []):
            if package.get("type") != "git":
                errors.append(f"dependency {package.get('name')}: must be a pinned Git dependency")
            if not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
                errors.append(f"dependency {package.get('name')}: revision is not a full commit SHA")
            if not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?", package.get("url", "")):
                errors.append(f"dependency {package.get('name')}: URL is not a public GitHub HTTPS URL")

    if errors:
        print("Source checks failed:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    print(f"PASS: {source_count} Lean files satisfy source layout; proof development has zero lexical holes/custom axioms.")
    print(f"Challenge specification holes: {specification_holes} (excluded from proof-development count).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
