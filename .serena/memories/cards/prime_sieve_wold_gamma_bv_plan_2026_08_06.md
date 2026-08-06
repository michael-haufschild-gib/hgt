# Card: prime-sieve-wold-gamma-bv-relative-character — FORMALIZATION COMPLETE

Card: `docs/drafts/pipeline/2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`
Every proved theorem of the card (Sections 1–7) is now formalized
unconditionally. Only Conjecture (24) is left, and it has no paper proof, so it
is explicitly NOT a formalization target. The card is ready to move to
`3-formalized`.

Axioms everywhere: propext / Classical.choice / Quot.sound.
Umbrellas: HTGeometry 15149 jobs, RHTower 17156 jobs, both clean.

## Module map
### HTGeometry
- `PrimeSieveDensityTelescope.lean` — (13),(14): `sieveDensity`, `sievePrefix`,
  `tsum_sieveDensity_div_prime`, `tendsto_sieveDensity_sievePrefix`.
- `PrimeSieveEulerTrace.lean` — arithmetic of (3): `sievePrimorial`,
  `sievedSum`, `sievedSum_insert`, `sievedSum_eq_mul_prod`.
- `PrimeSieveHarmonicInclusionExclusion.lean` — (11),(12) and
  `sum_divisors_moebiusDiv_sievePrimorial` (`∑_{d|M_P} μ(d)/d = a_P`).
- `PrimeSieveRegularDeterminant.lean` — (5),(6),(7),(9): `sieveTrace`,
  `sieveLogPhi`, `sieveLogPhi_insert`, `abs_sieveLogPhi_le`,
  `abs_sieveLogPhi_insert_sub_le`, `vacuumLogPhi`, `exp_vacuumLogPhi`,
  `tendsto_sieveTrace_sievePrefix`, `tendsto_sieveLogPhi_sievePrefix`.
- `LpDiagonalOperator.lean` — REUSABLE diagonal operators on ℓ²(ι).
- `PrimeSieveOperator.lean` — (1),(2),(4),(8): `sieveOperator`, `sievePhi`,
  `sievePhi_eq_exp_sieveLogPhi`, `vacuumProjection`,
  `tendsto_hsNormSq_sieveOperator_sub_vacuum`,
  `sieveOffMultiple_inv_eq_sieveWeight`.
- `CoefficientDecimationSieve.lean` — Section 4 coefficient layer:
  `decimate`/`inflate`/`offMultiple`/`sieveOffMultiple`,
  `sieveOffMultiple_eq_sum_divisors`, `LSeries_inflate`, `LSeries_offMultiple`,
  `J_sieveOffMultiple`.
- `PrimeSieveTransitionSize.lean` — Sections 6,7: `sieveRegularConstant`,
  `abs_sieveLogPhi_div_le`, `sieveTransitionSize` (22),
  `summable_sieveTransitionSize` (23), `sieveTrace_empty_pos`,
  `sieveLogPhi_empty_neg`, `tendsto_naiveRegularDefect`,
  `not_summable_naiveRegularDefect`, `not_summable_naiveSingularDefect`.

### RHTower
- `BVPrimeWindowSieveResidue.lean` — Sections 4,5 at the actual residue:
  `natDilate`, `polarCoefficient_decimate` (=(15), GENERAL q — the parent card
  had only the square case), `continuedSourceResidueValue_natDilate` (=(16a)),
  `sievedContinuedSource`, `LSeries_sieveOffMultiple_polarCoefficient`,
  `tendsto_sievedContinuedSource_residue` (=(18)),
  `tendsto_sievedContinuedSource_residue_normalized` (=(21)),
  `tendsto_sievedResidueValue_sievePrefix`,
  `relativeCharacter` (=(19)), `tendsto_relativeCharacter` (=(20)).

## Traps (cumulative, reusable)
- `∘L` binds TIGHTER than `^`; `T^(k+1) = T^k * T` → `ContinuousLinearMap.mul_def`.
- `rw` of an `Iff` inside an `if` condition fails on the `Decidable` motive —
  use `by_cases` + `if_pos`/`if_neg` with `.mp`/`.mpr`.
- `rw [someDef]` can fail for `def f a b : X → Y := fun m => ...`; add `f_eq := rfl`.
- `LSeries_sub`/`_sum`/`_smul` live in `Mathlib.NumberTheory.LSeries.Linearity`.
- `Complex.natCast_mul_natCast_cpow`; `continuousAt_const_cpow` (ROOT namespace).
- `Summable.tsum_pos` (not `tsum_pos`); `Real.sSup_nonneg` takes only the
  hypothesis; `Real.sSup_le h ha`.
- `Tendsto` into a product: `rw [nhds_prod_eq]` then `Tendsto.prodMk`.
- Injective `ℕ → ℕ` tends atTop: `.tendsto_cofinite` + `Nat.cofinite_eq_atTop`.
- Corpus BV lemmas produce `((d:ℝ):ℂ)`; bridge to `(d:ℂ)` with `push_cast`.
- Name collisions are caught by the umbrella build, not the linter. Grep first.
- `HilbertSchmidt.diagMul` already existed in `FredholmDeterminantExamples.lean`.
