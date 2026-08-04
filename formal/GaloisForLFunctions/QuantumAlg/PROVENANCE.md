# QuantumAlg provenance

Vendored copy of <https://github.com/QudeLeap/Lean-QuantumAlg>, commit
`7e80846034b9e76fdeded711775a513a7d5ba917`, Apache-2.0 (`LICENSE` here).
Do not edit; re-sync from upstream instead.

Only change from upstream: `public import QuantumAlg.X` rewritten to
`public import GaloisForLFunctions.QuantumAlg.X`.  Declaration namespaces are
untouched, so everything still lives in the root `QuantumAlg` namespace.  The
upstream root module was replaced by `GaloisForLFunctions/QuantumAlg.lean`,
which imports all 230 modules.

Upstream builds on Lean/mathlib/cslib `v4.31.0`; here it builds on `v4.32.2`.
`Init.lean` and `Core/Cost.lean` need cslib, declared in `formal/lakefile.toml`.
