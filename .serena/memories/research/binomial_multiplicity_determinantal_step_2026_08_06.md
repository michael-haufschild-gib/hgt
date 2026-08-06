---
name: binomial-multiplicity-determinantal-step
---

# Critical binomial multiplicity: everything is reduced to one determinantal degree

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/projective-horizon/projective-horizon-critical-binomial-multiplicity.md`
Module: `formal/GaloisForLFunctions/HTGeometry/CriticalTailFibreCount.lean` (in the umbrella).

## What is proved (2026-08-06, all `[propext, Classical.choice, Quot.sound]`)

- `nat_card_monic_divisors_criticalTails` — the count for **arbitrary** tails of the critical
  degrees with squarefree target (previously: monomial tails only).
- `dvd_criticalLowProduct_sub_one_congr`, `fibre_eq_of_dvd_sub` — the fibre depends on the tails
  only modulo `X ^ L`, so long tails reduce to truncations.
- `criticalLowProduct_eq_affine`, `fibre_snd_unique` — the equation is affine-linear in `B`, so
  `B` is unique given `A`.
- `coeff_zero_ne_zero_of_mem_criticalFibre` — `U + A` is invertible at the origin automatically,
  given only `(1 + U V)(0) ≠ 0`.
- `criticalFibre`, `criticalFibre_fst_injOn`, `exists_snd_iff_linear_solvable`,
  `criticalFibre_fst_image` — the fibre is in bijection with the set of `A` of degree `< m` for
  which `(U + A) B ≡ 1 - A V (mod X ^ L)` is solvable with `deg B < n`.

## The single remaining input

> The degree of the locus where a generic `(m+n) x (n+1)` matrix of linear forms in `m+1`
> homogeneous variables drops rank is `C(m+n, n)`.

Giambelli–Thom–Porteous.  Mathlib has neither this nor multiprojective Bezout.  The Chow-ring side
of the number is already formalized: `criticalHorizonMultiplicity_eq_chowCoefficient`.

## Next concrete Lean step, with names already resolved

Turn `exists_snd_iff_linear_solvable` into a range-membership statement:

```lean
noncomputable def mulTrunc (G : F[X]) (L : ℕ) : F[X] →ₗ[F] F[X] where
  toFun B := (G * B) %ₘ (X : F[X]) ^ L
```

then solvability ⟺ `((1 - A*V) %ₘ X^L) ∈ Submodule.map (mulTrunc (U+A) L) (Polynomial.degreeLT F n)`.

Resolved names (checked against this toolchain):
- `Polynomial.modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p`
  — in `Mathlib/Algebra/Polynomial/Div.lean` line 399.  NOTE it did **not** resolve from a bare
  `import Mathlib.Algebra.Polynomial.Div` probe; find it via the source path, not `#check`.
- `Polynomial.add_modByMonic (p₁ p₂) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q` ✓
- `Polynomial.mem_degreeLT : f ∈ degreeLT R n ↔ f.degree < ↑n` ✓ (import
  `Mathlib.RingTheory.Polynomial.Basic`; `Polynomial.degreeLT` does not `#check` on its own)
- `Polynomial.monic_X_pow` ✓
- **Open at the time of writing:** the `map_smul'` field needs `(c • p) %ₘ q = c • (p %ₘ q)`;
  `Polynomial.smul_modByMonic` does not exist under that name.  Either find the real name or
  derive it from `smul_eq_C_mul` plus the `C`-multiplication behaviour of `%ₘ`.

## Corpus assets not to rebuild

`HorizonTruncationCancel.lean` (`dvd_of_mul_dvd_of_coeff_zero_ne_zero`,
`isCoprime_X_of_coeff_zero_ne_zero`), `SeparableSplitDivisorCount.lean` (`nat_card_monic_divisors`),
`MonomialTailFibreCount.lean`, `MatrixRankFactor.lean` (`rank_factor`), `MatrixCompound.lean`,
`CompoundKyFan.lean`, `BlockComplementaryMinor.lean`, `SchurCofactorLocus.lean`.
