# QuantumAlg provenance

This directory is a vendored copy of an external Lean 4 library.  It is not
original work of this project.

| Field | Value |
|---|---|
| Upstream | <https://github.com/QudeLeap/Lean-QuantumAlg> |
| Upstream commit | `7e80846034b9e76fdeded711775a513a7d5ba917` |
| Upstream toolchain | `leanprover/lean4:v4.31.0`, mathlib `v4.31.0`, cslib `v4.31.0` |
| Vendored toolchain | `leanprover/lean4:v4.32.2`, mathlib `v4.32.2`, cslib `v4.32.2` |
| License | Apache License 2.0 (`LICENSE` in this directory) |
| Copyright | 2026 QudeLeap |

## What it contains

230 Lean modules (~187k lines) over mathlib and CSLib:

| Subtree | Modules | Content |
|---|---|---|
| `Util/` | 36 | quantum-free helper lemmas: complex/exp identities, polynomial parity and reflection, Dirichlet kernels, `Fin (2 ^ ·)` index plumbing |
| `Core/` | 23 | pure-state, gate, tensor, measurement, circuit, cost, and resource-model framework |
| `Primitives/` | 139 | phase kickback, Hadamard and SWAP tests, QFT, modular-arithmetic units, quantum signal processing and QSVT, quantum neural networks and their dynamical Lie algebras |
| `Algorithms/` | 27 | Bell states, Deutsch–Jozsa, order finding, finite-cyclic discrete log, Shor- and Ekerå–Håstad-style factoring |

## Changes made when vendoring

The vendored sources are byte-identical to upstream except for the module-path
rewrite that places them inside this package:

* every `public import QuantumAlg.X` became `public import GaloisForLFunctions.QuantumAlg.X`
  (790 import lines across 229 files);
* the upstream root module `QuantumAlg.lean` was not copied.  Its replacement is
  the area umbrella `GaloisForLFunctions/QuantumAlg.lean`, which imports the
  complete inventory rather than a hand-picked subset.

Declaration namespaces are unchanged: the library still lives in the root
`QuantumAlg` namespace, so upstream names resolve exactly as documented
upstream.  Keeping them unchanged is what makes re-syncing with upstream a
mechanical import rewrite.

## Module system

All 230 modules use the Lean module system (`module`, `public import`,
`@[expose] public section`).  This project's own modules are legacy files; a
legacy file may import a module-system file, so the area umbrella is a plain
`import` list like every other umbrella in this package.  Two consequences:

* `scripts/formal_tools.py` matches `^import`, not `public import`, so it cannot
  traverse the internal import graph of this area.  Umbrella completeness is
  what keeps the area reachable, and the umbrella therefore lists every module
  explicitly.
* Adding a module here requires adding its `import` line to
  `GaloisForLFunctions/QuantumAlg.lean` by hand, as elsewhere in the package.

## Dependency

`Core/Cost.lean` and `Init.lean` require CSLib
(`Cslib.Algorithms.Lean.TimeM`, `Cslib.Init`).  CSLib is declared in
`formal/lakefile.toml` at tag `v4.32.2`, which itself pins mathlib `v4.32.2` —
the same revision this project already uses.

## Re-syncing with upstream

```bash
git clone --depth 1 https://github.com/QudeLeap/Lean-QuantumAlg
# replace formal/GaloisForLFunctions/QuantumAlg/ with the clone's QuantumAlg/
# rewrite:  ^public import QuantumAlg  ->  public import GaloisForLFunctions.QuantumAlg
# regenerate GaloisForLFunctions/QuantumAlg.lean from the file list
```
