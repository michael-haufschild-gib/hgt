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

Validation is in progress. Presence in this directory is not evidence of a completed
backport or a local kernel check. The implementation ledger is
`docs/drafts/pipeline/1-in-progress/differential-geometry-four-integrations.md` at repository
root. The source closure scan found no active `sorry`, `admit`, `axiom`, `opaque`, `unsafe`
or `native_decide`; compiled endpoint axiom audits remain required.
