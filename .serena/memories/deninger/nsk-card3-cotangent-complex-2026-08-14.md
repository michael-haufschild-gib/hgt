# Card 3: the monic-lift cotangent complex is formalized (2026-08-14)

`formal/GaloisForLFunctions/RHTower/DeningerMonicCotangentComplex.lean` — compiles clean, axioms
`propext, Classical.choice, Quot.sound`, wired into `RHTower.lean`.

- `deningerMonicExtension P : Algebra.Extension A (DeningerMonicQuotient P)` — the polynomial
  presentation, section by `Function.surjInv (Ideal.Quotient.mk_surjective)`.
- `deningerMonicExtension_ker` — kernel is `Ideal.span {P}` (proved via
  `Ideal.Quotient.eq_zero_iff_mem`, NOT `Ideal.mk_ker`, which now needs `IsTwoSided`).
- **`deningerMonicCotangentComplex_mk`** — under `deningerMonicConormalEquiv` (corpus) and
  `deningerKaehlerBaseChangeEquiv` (corpus, after `TensorProduct.comm`), mathlib's
  `Algebra.Extension.cotangentComplex` sends the class of `qP` to `derivative P • q̄`.

Mathlib API notes: `Algebra.Extension` lives in `Mathlib/RingTheory/Extension/Basic.lean`,
`cotangentComplex` and `H1Cotangent` in `Mathlib/RingTheory/Extension/Cotangent/Basic.lean`;
`cotangentComplex_mk x = 1 ⊗ₜ D _ _ x`.  `TensorProduct.smul_tmul : (r•m) ⊗ₜ n = m ⊗ₜ (r•n)` —
use `← smul_tmul` to move a scalar from the right factor to the left.  The `Polynomial A`-module
structure on the quotient is `Submodule.Quotient`, so `P • (1 : B)` unfolds to
`Ideal.Quotient.mk _ (P * 1)`, not via `Algebra.smul_def`.

What remains on card 3: the Milnor–Witt layer (oriented fundamental class, determinant twist,
Gysin map to `[Z_P]`) and the ∞-categorical positive-cell `π₀` theorem (free `E_∞`-algebra on a
1-connective object, homotopy pushout).  Neither exists in mathlib in any form.
Possible next reachable increment: `H₀(A ⊗ B) ≅ H₀A ⊗ H₀B` for non-negatively graded complexes,
as a concrete-model surrogate for the positive-cell `π₀` invariance.
