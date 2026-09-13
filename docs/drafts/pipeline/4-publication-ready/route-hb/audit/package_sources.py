"""Archive selected local Lean import closure. Reads sources; never invokes Lean/Lake."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "formal/lean-toolchain").exists())
FORMAL = ROOT / "formal"


def without_comments(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif not string and text.startswith("/-", i):
            depth = 1
            i += 2
        elif not string and text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            ch = text[i]
            out.append(ch)
            if ch == '"' and (i == 0 or text[i - 1] != "\\"):
                string = not string
            i += 1
    return "".join(out)


def main():
    declarations = json.loads((HERE / "declarations.json").read_text())
    pending = [d["module"] for d in declarations]
    local, external, red_flags = {}, set(), []
    while pending:
        module = pending.pop()
        if module in local or module in external:
            continue
        path = FORMAL / (module.replace(".", "/") + ".lean")
        if not path.exists():
            external.add(module)
            continue
        data = path.read_bytes()
        clean = without_comments(data.decode())
        imports = []
        for line in clean.splitlines():
            m = re.match(r"\s*(?:public\s+|private\s+)?import\s+(.+)", line)
            if m:
                imports.extend(m.group(1).split())
        local[module] = (path, data, imports)
        pending.extend(imports)
        for m in re.finditer(r"\b(sorry|admit|axiom|opaque|unsafe)\b", clean):
            red_flags.append({"module": module, "token": m.group(),
                              "line": clean[:m.start()].count("\n") + 1})
    mismatches = []
    for d in declarations:
        actual = hashlib.sha256(local[d["module"]][1]).hexdigest()
        if actual != d["source_sha256"]:
            mismatches.append(d["name"])
    if mismatches:
        raise RuntimeError("Selected files changed since manifest: " + str(mismatches))
    archive = HERE / "source-snapshot.zip"
    files = []
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as z:
        for module, (path, data, imports) in sorted(local.items()):
            name = str(path.relative_to(ROOT))
            z.writestr(name, data)
            files.append({"module": module, "path": name, "imports": imports,
                          "sha256": hashlib.sha256(data).hexdigest()})
        for name in ["lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean"]:
            path = FORMAL / name
            if path.exists():
                data = path.read_bytes()
                z.writestr("formal/" + name, data)
                files.append({"path": "formal/" + name,
                              "sha256": hashlib.sha256(data).hexdigest()})
    report = {"created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "audit_kind": "lexical local import closure, not compiler dependency or axiom analysis",
              "local_modules": len(local), "external_imports": sorted(external),
              "lexical_red_flags": red_flags, "files": files,
              "archive_sha256": hashlib.sha256(archive.read_bytes()).hexdigest()}
    (HERE / "source-closure.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["created_utc", "local_modules", "lexical_red_flags", "archive_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
