# Card: prime-sieve-wold-gamma-bv-relative-character — formalization progress

Card: `docs/drafts/pipeline/2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`
(its "Formalization status" section carries the full declaration tables).

## DONE — Sections 1, 2, 3 are complete and unconditional
(axioms = propext/Classical.choice/Quot.sound; all wired into
`GaloisForLFunctions/HTGeometry.lean`)

- `HTGeometry/PrimeSieveDensityTelescope.lean` — Section 3 (13),(14):
  `sieveDensity`, `sieveDensity_insert`, `sievePrefix`,
  `tendsto_sieveDensity_sievePrefix`, `tsum_sieveDensity_div_prime` (boxed (14)).
- `HTGeometry/PrimeSieveEulerTrace.lean` — arithmetic of (3):
  `sievePrimorial`, `sievedSum`, `sievedSum_insert`, `sievedSum_eq_mul_prod`,
  `sievedSum_rpow_inv`.
- `HTGeometry/PrimeSieveHarmonicInclusionExclusion.lean` — Section 3 (11),(12):
  `sievedHarmonic_eq_sum_divisors` (12), `sum_divisors_moebiusDiv_sievePrimorial`
  (`∑_{d|M_P} μ(d)/d = a_P`), `tendsto_sievedHarmonic_sub` (11),
  plus `moebiusDiv`, `tendsto_natDiv_div_self`, `tendsto_harmonic_natDiv_sub_log`.
- `HTGeometry/PrimeSieveRegularDeterminant.lean` — Section 2 (5)–(9) analytically:
  `sieveTrace`, `sieveTraceBound`, `sieveTrace_le_bound`, `sieveLogPhi` (6),
  `sieveLogPhi_insert` (boxed (5)), `abs_sieveLogPhi_insert_sub_le` (7),
  `vacuumLogPhi`, `exp_vacuumLogPhi` (9), `hasSum_vacuumSeries`,
  `tendsto_sieveTrace_sievePrefix`, `tendsto_sieveLogPhi_sievePrefix` (9).
- `HTGeometry/LpDiagonalOperator.lean` — REUSABLE generic layer, namespace
  `HilbertSchmidt`: `diagMul_diag`, `diagMul_of_ne`, `isHS_diagMul_of_summable`,
  `tsum_diagMul_normSq`, `diagOp`, `diagOp_apply`, `diagOp_congr`,
  `isHilbertSchmidt_diagOp`, `hsNormSq_diagOp`, `diagOp_comp`, `diagOp_sub`,
  `summable_pow_normSq`, `diagOp_pow`, `opTrace_diagOp_comp`, `opTrace_diagOp_pow`.
- `HTGeometry/PrimeSieveOperator.lean` — Section 1 (1)–(3) + (4) + (8):
  `sieveWeight`, `sieveOperator`, `isHilbertSchmidt_sieveOperator`,
  `opTrace_sieveOperator_pow`, `operatorFredholmExpGerm_sieveOperator`,
  `sieveTraceBoundTwo`, `sieveTrace_le_boundTwo`, `summable_expGerm_term`,
  `expGermDiff`/`_even`/`_odd`, `expGerm_sub_eq_sieveLogPhi`, `sievePhi` (4),
  `sievePhi_eq_exp_sieveLogPhi` (**(4) = (6)**), `vacuumProjection`,
  `hsNormSq_sieveOperator_sub_vacuum`,
  `tendsto_hsNormSq_sieveOperator_sub_vacuum` (8).

## Corpus facts learned (do not rebuild)
- `HilbertSchmidt.diagMul` (general diagonal kernel), `hsComp_diagMul`,
  `hsPow_diagMul`, `isHS_diagMul` (finite support only) already exist in
  `HTGeometry/FredholmDeterminantExamples.lean`. My layer adds the
  infinite/square-summable case and the OPERATOR side.
- `HTGeometry/HilbertSchmidtMatrix.lean`: `lpBasis`, `toOperator`,
  `toOperator_apply`, `isHilbertSchmidt_toOperator`, `hsNormSq_toOperator`.
- `HTGeometry/HilbertSchmidtTrace.lean`: `opTrace`, `opTrace_toOperator_comp`.
- `HTGeometry/OperatorFredholmGerm.lean`: `operatorFredholmExpGerm`,
  `operatorFredholmDet2Germ`, `operatorFredholmDet1Germ` (ROOT namespace
  `HTGeometry`, so write `HTGeometry.operatorFredholmExpGerm` from inside
  `GaloisForLFunctions.HTGeometry`).
- `RHTower/XiDivisorDiagonalTraceClass.lean` has an Xi-specialized diagonal
  layer; do not import it from HTGeometry.

## Traps hit
- `∘L` binds TIGHTER than `^`: write `((T) ^ k) ∘L T`.
- `T ^ (k+1) = T ^ k * T`; convert `*` to `∘L` with
  `ContinuousLinearMap.mul_def`.
- `ext f i` on a CLM into `lp` already descends to coordinates — no `lp.ext`.
- Beta-redexes from `Function.support (fun p => ...)` block `rw` — insert `show`.
- `omit [inst] in` must precede the DOCSTRING.
- `summable_of_finite_support` is deprecated with a different signature; use
  `summable_of_ne_finset_zero (s := ...)`.
- Name collisions are checked by the umbrella build, not the linter:
  `HilbertSchmidt.diagKernel` already existed. Grep before naming.

## REMAINING
1. Section 4 (15)–(18): BV scale-decimation and `J(E_P p_a) = a_P J(p_a)`.
   `J` is the pole-cancelled BV/co-Poisson principal-normal class; the two
   homogeneity laws (16) come from the parent card
   `not_new_scientific_knowledge/bv-prime-window-polar-coefficient-decimation-law.md`.
   Locate/construct the corpus `J` first; (17)–(18) are then a purely algebraic
   induction over commuting `E_q = I − S_q D_q`.
2. Sections 5–6: assemble (19)–(21) and the naive no-go.
Conjecture (24) has no paper proof — NOT a formalization target.
