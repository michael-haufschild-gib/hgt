# DifferentialGeometry dependency subset

- Upstream: <https://github.com/qinz1yang/differential-geometry>
- Revision: `7a48598d35109aa99d1cc678e2724c213cdf4ff3` (release 0.1.3).
- License: Apache-2.0; see `LICENSE` and retained nested external licenses.
- Upstream toolchain: Lean/mathlib 4.33.1.
- Local toolchain: Lean/mathlib 4.32.2.

This package contains the exact transitive upstream-source closure of the eight endpoints
listed in `upstream-manifest.json`: Bochner, integrated tensor Weitzenböck, conformal and
regularized Gauss–Bonnet, weak harmonic-map energy lower semicontinuity, smooth Poisson
existence, the de Rham cochain complex, and low-degree Hurewicz. It contains 1,284 source
modules; Mathlib and Batteries resolve from the parent project's existing dependencies.

The manifest records each original source path, SHA-256 hash, imports and line count.
Namespace and import paths are preserved. Local compatibility edits are described in
`LOCAL_CHANGES.md`; the original hashes remain unchanged to make those edits auditable.
The local Lake configuration selects the parent's mathlib version and has no default build
target. Only requested endpoints and their dependencies are built.

All 1,284 modules and all eight endpoints compile on the local toolchain. The final
combined endpoint build passes (5,463 Lake jobs), and the combined geometry-adapter
import check passes. Eighteen endpoint/operator axiom audits contain only `propext`,
`Classical.choice` and `Quot.sound`. All 105 modified sources carry notices.

The original hashes match the pinned checkout, internal DifferentialGeometry import
edges are unchanged, and all four license/NOTICE files match upstream. The complete
vendored Lean source scan finds no `sorry`, `admit`, `axiom`, `opaque`, `unsafe` or
`native_decide`. Machine-readable evidence and the current-source fingerprint are in
[`validation.json`](validation.json).

All eleven native geometry adapter closures have current dependency certificates.
The five arithmetic adapters passed targeted compilation and axiom checks earlier;
the final full-closure freshness scan encounters 47 pre-existing stale dependency
roots, so it does not certify the entire current arithmetic dependency tree.
The project lint/index gate finds zero active proof debt and current generated files,
but fails on 14 unrelated modules missing from their theorem-area umbrellas.
This is a checked dependency integration, not a claim of a clean whole-worktree build,
a new RH proof, or a port of the full Poincaré proof.

The completed implementation ledger is
`docs/drafts/pipeline/3-formalized/differential-geometry-four-integrations.md` at repository
root. For a normal dependency-aware endpoint rebuild, run from `formal/`:

```sh
python3 - <<'PYBUILD'
import json, os, subprocess
from pathlib import Path
manifest = json.loads(Path("vendor/differential-geometry/upstream-manifest.json").read_text())
subprocess.run(
    ["lake", "build", *("+" + name for name in manifest["targets"])],
    env=dict(os.environ, LEAN_NUM_THREADS="1"), check=True,
)
PYBUILD
```

Axiom probes belong in `/tmp`, importing the relevant endpoint and using `#print axioms`
for the declarations recorded in `validation.json`. Generated project indexes are
refreshed with `scripts/formal_tools.py index`; the authoritative source/wiring gate is
`scripts/formal_tools.py lint --check-generated` from repository root.
