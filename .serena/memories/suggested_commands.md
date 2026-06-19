# Suggested Commands

- Build Lean library: `cd formal && lake build`.
- Run authoritative Lean audit: `bash scripts/check_axioms.sh` from project root.
- Check Lean/Lake versions: `cd formal && lean --version && lake --version`.
- Verify recalled Lean names by scratch file, not memory: `cd formal && lake env lean /tmp/x.lean` with `have := @Name` / `#check Name` lines.
- Print axioms only through scratch files or `scripts/check_axioms.sh`, not by editing source files.
- Fast repo search: `rg <pattern>` and file inventory: `rg --files`; use `find ... -maxdepth` when stage/column inventory matters.
- Check working tree before edits: `git status --short`.
- Serena memory sanity check after memory edits: `serena memories check` from project root.