# Semilocal Bruhat tensors in product-Haar L²

- **ID:** `field-one-semilocal-bruhat-to-l2`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-semilocal-l2-weyl-multiplier`
- **Statement:** every algebraic real--finite Schwartz--Bruhat tensor has a canonical
  product-Haar \(L^2(\mathbb R\times\mathbb A_f)\) realization, and this realization exactly
  intertwines the algebraic and \(L^2\) Weyl actions.

## Theorem

For \(f\in\mathcal S(\mathbb R)\) and
\(g\in C_c^{\mathrm{lc}}(\mathbb A_f)\), define
\[
  J(f\otimes g)(x_\infty,x_f)=f(x_\infty)g(x_f).
\]
The squared norm is the product of the two integrable squared norms. Product integrability
therefore proves \(J(f\otimes g)\in L^2\) without assuming sigma-finiteness of finite-adele Haar
measure. Bilinearity descends \(J\) to
\[
  \mathcal S(\mathbb R)\otimes_{\mathbb C}
    C_c^{\mathrm{lc}}(\mathbb A_f)
  \longrightarrow L^2(\mathbb R\times\mathbb A_f).
\]
For every \(a\in\mathbb R\times\mathbb A_f\),
\[
  W_a^{L^2}J=J\,W_a^{\mathrm{Bruhat}}.
\]

The follow-up module `FieldOneSemilocalBruhatL2Embedding` proves this map injective. This module
itself does not assert density, finite-adele sigma-finiteness, or a completed Hilbert-tensor
identification.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatToL2`
- **Core theorems:** `fieldOneSemilocalPureTensorFun_memLp`,
  `fieldOneSemilocalBruhatToL2_tmul`,
  `fieldOneSemilocalL2WeylUnitary_bruhat`,
  `fieldOneRationalDiagonalL2WeylUnitary_bruhat`
- **Audit:** direct `lake env lean` passed. In-file transient `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved
  for final audit.

## Gates

- [x] 0 → 1: pure-product function and product Haar measure typed
- [x] 1 → 2: dependency-closed \(L^2\), bilinearity, and equivariance proof
- [x] 2 → 3: unconditional direct Lean check
- [ ] 3 → 4: publication-ready integration
