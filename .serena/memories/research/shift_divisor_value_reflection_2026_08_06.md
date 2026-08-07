# Shift-divisor value reflection (corpus-owned)

The one-shift, pairwise, and iterated-forward-difference reflection laws are one divisor law.

## Primitive

`GaloisForLFunctions/HTGeometry/ShiftDivisorReflection.lean`

- `shiftDivisorValue (w : ℂ →₀ ℂ) (f : ℂ → ℂ) s = ∑ a, w a * f (s + a)`
- `reflectShiftDivisor c w` = divisor pushed along `a ↦ c - a` (involutive)
- `translateShiftDivisor τ w` = pushed along `a ↦ a + τ`

## The law

`shiftDivisorValue_signed_reflection`: if `f (2*c₀ - z) = ε * f z` then

    shiftDivisorValue w f (σ - s) = ε * shiftDivisorValue (reflectShiftDivisor (2*c₀ - σ) w) f s

So a translate family has an exact reflection law about `σ/2` **iff** its divisor is an eigenvector
of `reflectShiftDivisor (2*c₀ - σ)`; the eigenvalue multiplies `ε`.

Subsumes (machine-checked connectors exist):
- `forwardDifference_signed_reflection` / `iteratedForwardDifference_signed_reflection`
  (divisor `(δ_τ - δ_0)`; `reflectShiftDivisor_iteratedDifferenceDivisor` gives eigenvalue
  `(-1)^n` about `τs.sum`), via `iteratedForwardDifference_eq_shiftDivisorValue`
- `xiTransverseShiftRawLogDerivDefect_reflection` (point pair `δ_a - δ_0`)
- `xiPairwiseShiftRawLogDerivDifference_reflection` (`pairShiftDivisor a b`, anti-invariant about
  `(a+b)/2`) — the `if b ≤ a then … else …` endpoint-order bookkeeping disappears: the divisor law
  needs no order and no integrality.

## Laws with NO eigen hypothesis

- annihilator `shiftDivisorAnnihilator f` is a `Submodule ℂ (ℂ →₀ ℂ)` stable under translation and
  (for `ε ≠ 0`) under reflection
- canonical splitting `w = ½(w + refl w) + ½(w - refl w)`; hence
  `xiShiftDivisorLogDeriv_symm_add_antisymm`: every weighted `logDeriv xi` family splits into a
  reflection-fixed part and a part vanishing at `σ/2`.  This is the conceptual source of the
  half-cocycle centering in `XiPairwiseShiftValueReflection`.
- `iteratedDeriv_xiShiftDivisorValue_center_eq_zero`: for entire `xi`, all-order central jet parity.

## Arithmetic shadow

`GaloisForLFunctions/HTGeometry/ShiftDivisorLSeries.lean` +
`GaloisForLFunctions/RHTower/XiShiftDivisorPrimeSymbol.lean`

- symbol `shiftDivisorSymbol w n = ∑ a, w a * n^(-a)`; `LSeries_shiftDivisorStream` turns the
  twisted stream into `∑ a w a * LSeries f (s+a)`
- base identity proved here: `logDeriv xi s - logDeriv archFactor s = -LSeries Λ s` for `1 < s.re`
  (`logDeriv_xi_sub_archFactor_eq_neg_vonMangoldtLSeries`)
- `xiShiftDivisorPrimeValue_eq_lSeries`: corrected divisor value = `-LSeries (Λ · symbol w)`
- **dictionary**: divisor reflection about `(1-σ)/2` = symbol inversion `n^(-a) ↦ n^a` twisted by
  `n^(σ-1)` (`shiftDivisorSymbol_of_xiReflection_eigen`)

## Faithfulness (trivial annihilator)

`GaloisForLFunctions/RHTower/XiShiftDivisorFaithful.lean`

- bridge `shiftDivisorSymbol_eq_translationChar`: `shiftDivisorSymbol w n =
  GaloisForLFunctions.RHTower.translationChar (Real.log n) (AddMonoidAlgebra.ofCoeff w)`
  (`AddMonoidAlgebra` is a structure in this toolchain; constructor `ofCoeff`, projection `coeff`)
- with `euler_translation_faithful` (already in `RayCompleteTranslationFaithful`):
  symbol vanishing at every prime power implies `w = 0`
- with `LSeries.eq_of_LSeries_eventually_eq` plus the prime-symbol law:
  `xiShiftDivisorPrimeValue_eq_zero_iff` — for shifts with `0 <= a.re`, the corrected completed-Xi
  value vanishes on `Re s > 1` iff `w = 0`.  So `logDeriv xi - logDeriv archFactor` satisfies no
  nontrivial constant-coefficient linear difference relation
  (`shiftDivisor_eq_zero_of_completedPrimeSource_relation`), and divisor to value is injective.
- already present: character-level faithfulness.  New: the analytic-value-relation to
  character-vanishing bridge.
- finite-family form `completedPrimeSource_translate_independent`: distinct complex shifts with
  `0 <= Re a` give linearly independent corrected completed log-derivatives on `Re s > 1`.
  The corpus route (`linearIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff`, via
  differential independence) only covers distinct nonzero NATURAL shifts; the arithmetic route
  reproves that and extends to complex shifts.

## Parity balance (archimedean rationality)

`GaloisForLFunctions/RHTower/XiEvenShiftDivisorRationality.lean`

- `xiTransverseShiftArchimedeanCorrection_even`: for `1 < s.re`,
  `xiTransverseShiftArchimedeanCorrection (2*m) s = xiEvenShiftPrimeCorrection m s` POINTWISE.
  The corpus only had this as an upper-end germ
  (`xiEvenShiftPrimeCorrection_upperEndGerm_eq_archimedean`); the pointwise shift-two step
  `logDeriv_archFactor_shift_two` was already in `XiShiftPrimeExposure`.
- `xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect`: pointwise on `1 < s.re`.
- `logDeriv_archFactor_shift_split`: reduce any natural shift `a` to residue `a % 2` plus rational.
- **`archimedeanCorrection_family_of_parity_balanced`**: the archimedean correction of a
  natural-shift family is rational as soon as the EVEN-shift coefficient mass and the ODD-shift
  coefficient mass separately vanish.  Odd shifts are NOT the obstruction — unbalanced parity mass
  is.  `delta_1 - delta_3` is odd and rational; `delta_1 - delta_0` is not.  This closes the
  "no rationality claim for odd shifts" caveat in `XiTransverseShiftPrimeDefectValueReflection`.
- divisor forms: `xiShiftDivisorArchimedeanCorrection_parityBalanced`,
  `xiShiftDivisorPrimeValue_parityBalanced`.
- **`archimedeanCorrection_family_parity_decomposition`** (no hypothesis on coefficients) is the
  primary law: `sum c_i logDeriv archFactor (s + a_i) = (even mass)*logDeriv archFactor s +
  (odd mass)*logDeriv archFactor (s+1) + explicit rational`.  Balance is the corollary.
- domain: `logDeriv_archFactor_shift_two_of_re_pos` weakens the corpus's
  `logDeriv_archFactor_shift_two` from `1 < s.re` to `0 < s.re` and `s <> 1`; the whole parity layer
  inherits that.
- same-parity pairs: `xiPairwiseShiftPrimeDifference_eq_explicit`,
  `xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit`, `pairShiftDivisor_parityBalanced`.
  The corpus shift-two theory (`XiShiftPrimeReflectionCocycle`) is the pair `(2,0)`.
- converse input NOW PROVED:
  * `GaloisForLFunctions/HTGeometry/DifferenceTwoOrbitBrick.lean` —
    `difference_two_orbit_pole_free`: a rational function has no unit-shift difference whose pole
    part sits on two ZZ-orbits with incommensurable base points.  Also
    `difference_two_orbit_pole_free_of_eval` (pointwise identity on any infinite set suffices) and
    `q_eval_ne_zero_of_orbit` (the orbit pinch, reusable).
    The corpus already had the SINGLE-orbit version `difference_single_pole_free` in
    `HolderDifferenceBricks` (engine of its Hoelder/hypertranscendence proof); two orbits is what the
    parity problem needs since poles of psi(s/2) and psi((s+1)/2) differ by a half-integer.
    `difference_multi_orbit_pole_free` now covers ANY finite family of pairwise incommensurable
    orbit centres (single- and two-orbit are d = 1, 2); same pinch, product coprimality, degree bound
    `A.natDegree < sum (n i + 1)`.
    RELATED CORPUS ASSET (different formulation, do not confuse): `HTGeometry/OrbitResidueVector.lean`
    gives the combinatorial obstruction — a finitely supported coefficient datum is not a translation
    coboundary when its orbit-residue vector is nonzero.  That is about finite DATA; the bricks are
    about RATIONAL FUNCTIONS with unknown poles.  Deriving the bricks from it would need a
    principal-part bridge (partial fractions for `RatFunc`), which the corpus does not have.
  * `GaloisForLFunctions/HTGeometry/DigammaHalfTranslateIndependent.lean` —
    `digamma_half_translate_independent`: psi(z) and psi(z+1/2) are linearly independent over C(z).
  * `GaloisForLFunctions/HTGeometry/DigammaTranslatesIndependent.lean` —
    `digamma_translates_independent`: ANY finite family of digamma translates `psi(z + a i)` with
    pairwise incommensurable shifts (no two differing by an integer) is linearly independent over
    the rational functions.  Half-translate case is d = 2, shifts 0 and 1/2.  Proof: shift by 1,
    partial-fraction numerator `digammaResidueNumerator` of degree < d, then
    `difference_multi_orbit_pole_free_of_eval` with centres `-a i`; residues extracted by
    evaluating the numerator at `-a i`.
    This is what a degree-d archimedean factor `prod_j Gamma(s/2 + kappa_j)` needs to run the
    parity/rationality dichotomy, not just zeta's degree-1 factor.
    `digamma_halfArgument_modes_independent` (same file) is the half-argument form for a product of
    `Gammaℝ (s + kappa_j)` factors: the modes `psi((s + kappa_j)/2)` are independent over the
    rational functions as soon as no two exponents differ by an EVEN integer.  Completed zeta is
    d = 1; the parity-dichotomy pair is d = 2 with kappa = (0,1).
    `digamma_half_translate_independent_of_cofinite` is now DERIVED from
    `digamma_translates_independent` (d = 2, shifts 0 and 1/2); its bespoke proof was deleted.
    Import edge reversed: brick -> DigammaTranslatesIndependent -> DigammaHalfTranslateIndependent,
    with `finite_setOf_translate_isRoot` moved down into the brick file.
  Three strengths available: lowest terms; lowest terms off a finite exceptional set
  (`..._of_cofinite`); arbitrary quotient off a finite exceptional set (`..._of_quotient`, reduces
  via `RatFunc.num`/`RatFunc.denom`).  Use `..._of_quotient` in applications — no coprimality
  obligation.
- NEGATIVE HALF DONE: `GaloisForLFunctions/RHTower/XiOddShiftArchimedeanIrrationality.lean`
  * `xiTransverseShiftArchimedeanCorrection_one_closed`: for `0 < s.re`, `s <> 1`,
    `logDeriv archFactor (s+1) - logDeriv archFactor s = 1/(s+1) - 1/(s-1)
       + psi((s+1)/2)/2 - psi(s/2)/2`
  * `xiTransverseShiftArchimedeanCorrection_one_not_rational`: NO quotient of polynomials agrees
    with the shift-one archimedean correction on the right half-plane.  Substitution s = 2z turns
    the two modes into psi(z), psi(z+1/2).
  So parity balance is genuinely necessary, already at the single odd shift the corpus left open.
- DICHOTOMY CLOSED (iff):
  * `GaloisForLFunctions/HTGeometry/HalfPlaneRational.lean` — predicate `IsHalfPlaneRational f`
    (agrees with a polynomial quotient on `0 < re`, off a finite set).  Closed under add, sub,
    const_mul, finsetSum, `comp_two` (z -> 2z), and `congr` off a finite set.  Use this class
    instead of hand-building numerators/denominators.
    `digamma_parity_modes_independent`: `E*psi(s/2) + O*psi((s+1)/2)` half-plane rational implies
    `E = O = 0`.
  * `GaloisForLFunctions/RHTower/XiParityMassDichotomy.lean` —
    `archimedeanCorrection_family_isHalfPlaneRational_iff`: a natural-shift family's archimedean
    correction is half-plane rational IFF both parity masses vanish.
- UNBLOCKED (no identity theorem needed): `0 < s.re` in the corpus's
  `hasDerivAt_Gammaℝ_of_re_pos` was only used to keep `s/2` off the poles of Gamma.  Generalized in
  place (old names kept as corollaries): `hasDerivAt_Gammaℝ_off_poles`,
  `hasDerivAt_archFactor_off_poles` (ArchEnvelope.lean),
  `logDeriv_archFactor_closed_off_poles` (XiShiftPrimeExposure.lean).
  `GaloisForLFunctions/RHTower/ArchLadderRegular.lean` defines `ArchLadderRegular s` =
  (s/2 off Gamma poles) AND (s not an odd integer); stable under even translation
  (`ArchLadderRegular.shift`).  Gives
  `xiTransverseShiftArchimedeanCorrection_even_of_ladderRegular` on the whole ladder and
  `xiPairwiseShiftReflectionCocycle_eq_explicit` — explicit rational reflection cocycle for every
  same-parity integral pair, valid at the reflected point in the LEFT half-plane.
  DISCHARGE: `archLadderRegular_of_re_not_int` — both ladder conditions force an INTEGER real part,
  so a non-integral real part discharges them with no positivity requirement.  Hence
  `archLadderRegular_strip_add_nat` and `archLadderRegular_strip_reflect`: at any point of the open
  critical strip (in particular at every Xi zero, via `xi_divisor_support_re_mem_open_unit`) all
  side conditions vanish — see the `..._of_strip` forms.
  Endpoint order `b <= a` also discharged via truncated Nat subtraction plus
  `xiEvenShiftPrimeCorrection_zero` (no if-then-else in the conclusion): `..._eq_explicit_symm`.
- `archFactor_ne_zero_iff : archFactor s <> 0 <-> s <> 1 AND (for all n : Nat, s <> -(2n))`.
  Sharp, no positivity, no strip.  The corpus only had `archFactor_ne_zero_strip`
  (`0 < re AND re < 1`) or `archFactor_ne_zero` with a supplied `Gammaℝ s <> 0`.
  Corollaries: `archFactor_ne_zero_of_re_pos` (strip UPPER bound discharged; reaches `re > 1`,
  where the corpus had no nonvanishing lemma) and `archFactor_ne_zero_of_ladderRegular`
  (no nonvanishing side condition anywhere on the even ladder).
- `logDeriv_Gammaℝ_off_poles` and `logDeriv_Gammaℝ_translate_off_poles` (ArchLadderRegular.lean):
  `logDeriv Gammaℝ w = psi(w/2)/2 - log(pi)/2` needing only the pole condition, and the translated
  form `logDeriv (fun z => Gammaℝ (z + kappa)) s = psi((s+kappa)/2)/2 - log(pi)/2`.
  The corpus's `logDeriv_Gammaℝ_of_re_pos` (ReflectionCocycleArchimedean) assumes `0 < re w`.
  The translated form is the digamma mode of a completed L-function factor `Gammaℝ(s + kappa)` —
  the input shape of `digamma_halfArgument_modes_independent`.
- `logDeriv_Gammaℝ_reflect_off_poles` (ArchLadderRegular.lean): the archimedean reflection cocycle
  `logDeriv (z -> Gammaℝ z / Gammaℝ (1-z)) s = psi(s/2)/2 + psi((1-s)/2)/2 - log pi`, valid wherever
  both Gamma factors are off their poles (so also `re > 1` and `re < 0`).  The corpus derives this
  only LOCALLY, as an EventuallyEq near 3/4 buried inside `archReflCocycle_curvature_ne_zero`
  (ReflectionCocycleArchimedean.lean), and only where `s` and `1-s` both have positive real part.
  Helper `Gammaℝ_ne_zero_off_poles` extracted too.
- `logDeriv_archFactor_add_reflect`: `logDeriv archFactor s + logDeriv archFactor (1-s) =
  logDeriv (z -> Gammaℝ z / Gammaℝ (1-z)) s`.  The rational part `1/s + 1/(s-1)` of the completed
  archimedean factor CANCELS EXACTLY against its reflection, so the polynomial factor `s(s-1)/2`
  contributes nothing to the reflection defect — the whole defect is the pure Gamma weld.
- CAPSTONE `logDeriv_Gammaℝ_translates_independent` (ArchLadderRegular.lean): no C-combination of
  `logDeriv (z -> Gammaℝ (z + kappa_j))` is a rational function unless trivial, provided no two
  exponents differ by an EVEN integer.  The constant `-log(pi)/2` in every factor is absorbed into
  the rational side via `IsCoprime.add_mul_left_left` (coprimality survives adding a multiple of Q),
  so it obstructs nothing.  This is the archimedean-side independence for an arbitrary completed
  L-function Gamma factor.
- pointwise even-shift defect identification (corpus has it only as an upper-end germ):
  `xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect_of_ladderRegular` / `..._of_strip`.
- `GaloisForLFunctions/RHTower/CompletedSplitRightHalfPlane.lean`:
  `logDeriv_completed_split_of_re_pos` and
  `seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_of_re_pos` — hypotheses `0 < s.re`,
  `s <> 1`, `riemannZeta s <> 0`.  The strip upper bound `re < 1` was used ONLY to get `s <> 1`.
  Unifies the corpus's two regional statements (strip form in
  `CompletedFluxPrimeArchDecomposition`, absolute-convergence form
  `seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re` in `XiRelativeResolventFlux`) into one.
  On `1 <= s.re` the zeta side condition DISCHARGES via mathlib's
  `riemannZeta_ne_zero_of_one_le_re` (already used in RHTower by
  `xi_ne_zero_of_one_le_re` in `RHLadderTheory`, but not in the seam layer):
  `logDeriv_completed_split_of_one_le_re`,
  `seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_of_one_le_re` are hypothesis-free apart
  from `s <> 1`.  These reach the LINE `re = 1`, which neither corpus regional statement covers.
- `logDeriv_riemannZeta_add_reflect_of_strip` (CompletedSplitRightHalfPlane.lean): the classical
  reflection formula `zeta'/zeta(s) + zeta'/zeta(1-s) = log(pi) - psi(s/2)/2 - psi((1-s)/2)/2`
  on the open strip away from zeros at s and 1-s.  The corpus had NO zeta log-derivative reflection
  identity (checked).  Proof = corpus strip seam split at s and 1-s + `logDeriv_xi_reciprocity`
  + `logDeriv_archFactor_add_reflect` + `logDeriv_Gammaℝ_reflect_off_poles`, one `linear_combination`.
  Also `logDeriv_completed_split_off_poles` (positivity discharged to the pole condition).
- `logDeriv_riemannZeta_add_reflect_criticalLine` (s = 1/2 + it) and
  `re_logDeriv_riemannZeta_criticalLine`:
  `2 * Re(zeta'/zeta(1/2+it)) = log(pi) - Re psi(1/4 + it/2)`, away from zeros; the second
  nonvanishing hypothesis discharges by conjugation.  Uses `logDeriv_riemannZeta_conj` (proved in
  RHTower from mathlib `riemannZeta_conj` + `deriv_conj_conj`; PNTPlus has its own vendored copy
  `logDerivZeta_conj'` which RHTower does NOT import) and the corpus's
  `ReflectedDigammaAnomaly.digamma_conj` (HTGeometry).
- `isOpen_setOf_offPoles` (ArchLadderRegular.lean): `{z | forall m, z/2 <> -m}` is OPEN (poles march
  off to infinity; finitely many are near any point).  mathlib has no such lemma.  This unblocked
  `analyticAt_Gammaℝ_off_poles`, `analyticAt_archFactor_off_poles` (corpus only had
  `archFactor_analyticOnNhd_re_pos`), and then the OFF-POLES seam decomposition
  `seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_off_poles` and reflection
  `logDeriv_riemannZeta_add_reflect_off_poles` — valid on the whole plane except s = 0, 1, the
  ladder -2n and its reflection 1+2n.  The strip form is now a COROLLARY.
- `re_logDeriv_riemannZeta_criticalLine_le`: `2 Re(zeta'/zeta(1/2+it)) <= log(pi) - Re psi(1/4)`,
  unconditional (away from the zero at that point).  Uses the corpus's
  `re_logDeriv_Gammaℝ_real_le` (DigammaVerticalMinimum): Re logDeriv Gammaℝ is minimised on the
  real axis.
- discharged redundant `s <> 0` from `completedRiemannZeta_eq_Gammaℝ_mul` (XiRealAxisGrowth).
  NOT done: same redundancy in `logDeriv_archFactor_closed` — 18 call sites, unlocks nothing.

## Scope boundary

Divisor-side bookkeeping of the functional equation only.  It creates no positivity and is blind to
zero location; do not expect an RH criterion from it.  Use it to avoid re-proving reflection,
centering, and symbol laws for any new weighted family of completed-Xi translates.

All four modules build; `#print axioms` on every named law = `propext, Classical.choice, Quot.sound`.
Card: `docs/drafts/pipeline/3-formalized/shift-divisor-value-reflection.md`.

## Zeta zero-locus reflection (plane-wide)

`RHTower/ReflectionCocycleClass.lean` §7 had the strip forms
`riemannZeta_one_sub_eq_gammaRatio_mul` and `riemannZeta_one_sub_eq_zero_iff`. The strip was used
only to keep `Γ_ℝ(s)` and `Γ_ℝ(1−s)` nonzero, so both are now corollaries of
`…_of_Gammaℝ_ne_zero` root forms whose hypotheses are exactly those two nonvanishings — which
themselves force `s ≠ 0` and `s ≠ 1` because `Γ_ℝ` vanishes on the nonpositive even integers.
Ladder-form corollaries `…_off_poles` match the archimedean layer's calling convention.

New, absent from mathlib and the corpus:
- `riemannZeta_ne_zero_of_re_lt_zero` — no zeros with `Re s < 0` beyond `−2, −4, −6, …`.
- `riemannZeta_eq_zero_iff_of_re_lt_zero` — the zero locus left of the strip is exactly that ladder.
mathlib has only `riemannZeta_neg_two_mul_nat_add_one` (the forward direction).

Hypotheses discharged in `CompletedSplitRightHalfPlane.lean`:
- `logDeriv_riemannZeta_add_reflect_off_poles` no longer takes `s ≠ 0`, `s ≠ 1` (index `0` of the
  two ladder hypotheses gives them).
- both mirror theorems no longer take nonvanishing at the mirror point.
- `logDeriv_riemannZeta_add_reflect_of_one_lt_re`: reflection identity with **no** nonvanishing
  hypothesis, valid for `Re s > 1` away from the odd integers.

Audit note: the `GaloisForLFunctions.RHTower` umbrella is red for an unrelated reason — another
agent's `RHTower.deningerExtendFun` is declared in both `DeningerResidueSequence` and
`DeningerDolbeaultFine`. Audited instead by building every direct dependent of
`ReflectionCocycleClass`; all clean.

## Zeta zero-locus classification and the ζ/ξ bridge

`ReflectionCocycleClass.lean` now closes the classification of ζ's zeros outside the strip.
`riemannZeta_ne_zero_of_re_le_zero` covers `Re s ≤ 0` (the endpoint `s = 0` needs no hypothesis —
`riemannZeta_zero : ζ(0) = -1/2`), giving `riemannZeta_zero_re_mem_Ioo`: every nontrivial zero of ζ
lies in the OPEN critical strip. Also `riemannZeta_zero_trivial_or_mem_strip` (global dichotomy) and
`riemannZeta_zero_ne_one`.

This is the connector the corpus was missing: `0 < ρ.re` and `ρ.re < 1` appear as *hypotheses* on a
ζ zero in BurnolCoPoisson*, CCMBVMuntzSummation, ZeroDetectionEM, TentDivisorRecovery and others.
They are now derivable from `riemannZeta ρ = 0` + nontriviality.

New module `RHTower/ZetaXiZeroCorrespondence.lean`:
- `xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial` — global, no strip hypothesis either side.
  (`xi_eq_zero_iff` in RiemannTower.lean is the gated version: needs `0 < Re s`, `s ≠ 1`.)
- `riemannZeta_eq_zero_iff_xi_or_trivial`.
- `riemannHypothesis_iff_forall_nontrivial_zero` — mathlib's RH def carries a redundant `s ≠ 1`.
- `riemannHypothesis_iff_xi_zero_re_eq_half` — RH = "every ξ zero has Re = 1/2"; the corpus's
  `rh_iff_xi_ne_zero_right` half-plane restriction is removable.

Already corpus-owned, do not rebuild: `xi_zero_re_mem_open_unit` (BornTemperatureFactorType),
`xi_zero_re_lt_one`, `xi_ne_zero_of_one_le_re` (RHLadderTheory), `xi_zero_re_eq_half_of_RH`.

## The `ρ ≠ 1` discharge across the prime-polar RH criterion family

`riemannZeta_zero_ne_one` (ReflectionCocycleClass, no nontriviality needed — it follows from
`riemannZeta_zero_re_lt_one`, i.e. contraposed Euler-product nonvanishing) makes the premise
`ρ ≠ 1` redundant wherever it sits beside `riemannZeta ρ = 0`. Discharged at the root
`ZetaLogDerivResidue.neg_logDeriv_zeta_zero_residue` and cascaded through:

WindowRHCriterion, PrimePolarResidueCancellation, PrimePolarRHCriterion, PolarPrimeRegularity,
TentDivisorRecovery, CCMBulkCharacterTentPoleDetectionUniversalityLaw, ZeroDetectionEM (5 theorems).

Effect on the RH criteria: all six `RH_iff_*` / `RH_of_*` statements in this family previously read
`∀ ρ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1/2`. They now read `∀ ρ, riemannZeta ρ = 0 → ρ.re ≤ 1/2`.
Equivalent propositions, but the criterion no longer carries the clause.

`ZetaLogDerivResidue.lean` now imports `ReflectionCocycleClass` (checked cycle-free with an import
closure walk; RCC's closure is 105 modules and contains none of this family).

Repo-wide check after the edit: zero remaining occurrences of the old form.

## The criterion family now states RiemannHypothesis itself

`riemannHypothesis_iff_forall_zero_re_le_half` (ReflectionCocycleClass):

  RiemannHypothesis ↔ ∀ ρ, riemannZeta ρ = 0 → ρ.re ≤ 1/2

Nothing is excluded on the right: trivial zeros have Re < 0 ≤ 1/2 outright, the pole is not a zero
(`riemannZeta_zero_ne_one`), and at a nontrivial zero the one-sided bound becomes equality because
`1 - ρ` is a zero too (`riemannZeta_one_sub_eq_zero_iff_off_poles`) and carries the same bound.

Consequence: the prime-polar / window criterion family previously stated an RH-*shaped* proposition
with no formal link to mathlib's `RiemannHypothesis`. All of them now literally say
`RiemannHypothesis`:

  RH_of_windowObservable_regular, RH_of_sharpWindow_regular, RH_of_primeObservable_regular,
  RH_of_polarPrimeObservable_regular, RH_iff_windowObservable_regular, RH_iff_sharpWindow_regular,
  RH_iff_polarPrimeObservable_regular, RH_iff_primeObservable_polar_regular,
  RH_iff_PcalObservable_regular, RH_iff_sharpWindowPolar_regular,
  windowObservable_regular_of_RH, polarPrimeObservable_regular_of_RH.

Trap when doing this: a `RH_of_*` whose proof delegates to another `RH_of_*` must NOT get the
`rw [riemannHypothesis_iff_forall_zero_re_le_half]` prelude — the delegate already returns
`RiemannHypothesis` (hit this in RH_of_sharpWindow_regular).

## Zero-free half-plane forms of RH, and the reflected-character verdict

In ReflectionCocycleClass:
- `riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re` — RH ↔ `∀ s, 1/2 < Re s → ζ(s) ≠ 0`.
  The corpus had only the ξ-side `rh_iff_xi_ne_zero_right`.
- `riemannHypothesis_iff_riemannZeta_ne_zero_of_re_lt_half` — RH ↔ `∀ s, 0 < Re s < 1/2 → ζ(s) ≠ 0`.
  Reflection exchanges the halves, so forbidding zeros on either side is the same statement.

`ReflectedCharacterCarrierClassification.reflectedCharacterNorm_eq_iff_criticalLine` stated its
re-encoding verdict as `… ↔ (∀ rho, xi rho = 0 → rho.re = 1/2)`. That right side IS
`RiemannHypothesis` (`riemannHypothesis_iff_xi_zero_re_eq_half`), so the verdict now says so
directly. That file now imports ZetaXiZeroCorrespondence (cycle-checked).

Build note: this module sits under ~9750 jobs of dependencies and other agents hold the lake lock;
the Bash tool caps at 10 min, so the build needed six successive resumed invocations. lake resumes
from cache, so this is just repetition, not rework.

## The Burnol co-Poisson layer becomes an RH criterion

`riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip` (ReflectionCocycleClass):
RH ↔ `∀ s, 1/2 < Re s < 1 → ζ(s) ≠ 0`. Outside the strip ζ is nonvanishing for free, so a criterion
only has to be checked where zeros can be — this is the form that matches criteria stated on the
open strip.

`riemannHypothesis_iff_exists_burnolCoPoisson_inner_ne_zero` (BurnolCoPoissonSourceVectorSpace):
RH ↔ at every `w` with `1/2 < Re w < 1` some co-Poisson vector is detected by the Riesz evaluator.
The Burnol layer already had both halves (`inner_eq_zero_of_mem_burnolCoPoissonVectorSpace` and
`exists_mem_burnolCoPoissonVectorSpace_inner_ne_zero`, packaged as
`inner_eq_zero_on_burnolCoPoissonVectorSpace_iff`) but NO RiemannHypothesis-level statement at all
— grep for RiemannHypothesis in Burnol*.lean returned nothing. The upper-strip form is what closes
it. Aperture `b` is arbitrary in (0,1); the criterion is equivalent to RH for each b separately.

Blocked, do NOT retry: dropping `hhi : w.re < 1` from the Burnol inner-product theorems. It is not a
mere premise there — `burnolExtendedSoninEvaluationVector w b hlo hhi hb` is proof-carrying and
takes `hhi` as an argument, so the hypothesis occurs in the STATEMENT. Only the four theorems where
`w.re < 1` appears solely in hypotheses could be discharged
(integral_Ioi_burnolCoPoisson_subWindow{,_pair}_cpow_eq_zero,
soninMellinEvaluation_burnolCoPoissonSource_eq_zero, mellin_arithmeticSum_eq_zero_of_zeta_eq_zero),
via `riemannZeta_zero_re_lt_one`.

## Systematic sweep: per-point zero-criteria with no RH statement

Search recipe that found these (reusable): scan RHTower theorem headers for an iff whose one side is
`riemannZeta w = 0` / `xi w = 0` (or `≠ 0`), then split by whether the FILE mentions
`RiemannHypothesis` at all. 33 hits, 17 of them in files with no RH statement anywhere — each is a
complete two-sided law with no bridge to RH.

Closed this round:
- `riemannHypothesis_iff_xi_ne_zero_of_re_lt_half` (ZetaXiZeroCorrespondence) — RH ↔ ξ has no zeros
  LEFT of the line. Mirror of the corpus's `rh_iff_xi_ne_zero_right`; `xi_one_sub` exchanges them.
- `riemannHypothesis_iff_squarefreePartition_ne_zero` (SquarefreeFixedCurrentLocalization, namespace
  GaloisForLFunctions — needs the `_root_.RHTower.` prefix) — RH ↔ ζ(s)/ζ(2s) ≠ 0 on Re s > 1/2.
- `riemannHypothesis_iff_xiPowerCompletion_zero_re_eq_half` (XiPowerAutomorphicRealCoronaSmoothness)
  — RH is read off ξ^d for every d ≠ 0.
- `riemannHypothesis_iff_stokes_annihilation_criticalLine`
  (EulerHedenmalmGammaStokesTransgression) — RH ↔ the completed Euler multiplier can kill the Gamma
  Stokes jump only on the critical line. Backward direction picks t = 1; any positive t works.

Still open in that list (candidates for later rounds): the three
`CompletedPrimeFluxFittingAttachment.xiCanonicalFittingSeamAt_*_iff`, `XiThetaEndpointResidual`,
`HighExponentShellZeroFree`, `MFreeTwinNoGo`, `Sieve/InvZetaRegular`, `SeamStripRamification`,
the two `XiCTaylorMovingPositive...ChargeScreenedAt_iff_xi_ne_zero` (these two are stated on
Re σ < 1/2, so `riemannHypothesis_iff_xi_ne_zero_of_re_lt_half` is the matching bridge — but they
carry schedule/gauge hypotheses that must be threaded).

Note: EulerHedenmalmGammaStokesTransgression emits a pre-existing `Try this: ring_nf` suggestion on
`lake env lean`; it is not an error and the module builds clean.

## Three more RH criteria from the sweep (Re s > 1/2 family)

All three had a per-point iff with a zeta zero and no RH statement in the file; the bridge is
`riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re`.

- `RHTower.Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero` — RH ↔ the entire unit `(s-1)·ζ(s)`
  is nonvanishing on Re s > 1/2. No exclusion at s = 1 is needed: `zetaResidueUnit_one` is the
  residue value, and mathlib's junk `ζ(1)` is nonzero, so both directions close at the pole.
- `RHTower.riemannHypothesis_iff_dyadicMFreeZetaRung_zero_ne_zero` — RH ↔ the base dyadic rung
  ζ(s)/ζ(2s) is nonvanishing on Re s > 1/2.
- `RHTower.riemannHypothesis_iff_riemannZeta_mul_shellMultiplier_ne_zero` (m ≥ 12) — RH ↔ the shell
  current is nonvanishing on Re s > 1/2.

HighExponentShellZeroFree and MFreeTwinNoGo gained an `import ReflectionCocycleClass`
(cycle-checked); Sieve/InvZetaRegular already had it transitively.

Remaining from the sweep, not yet closed: the three
`CompletedPrimeFluxFittingAttachment.xiCanonicalFittingSeamAt_*_iff`, `XiThetaEndpointResidual`,
`SeamStripRamification` (that one is a ξ/ζ bridge, not a new criterion), and the two
`XiCTaylorMovingPositive...ChargeScreenedAt_iff_xi_ne_zero` (stated on Re σ < 1/2 — the matching
bridge is `riemannHypothesis_iff_xi_ne_zero_of_re_lt_half`, but schedule/gauge hypotheses must be
threaded into the criterion rather than discharged).

## Sweep closed: the last six criteria (2026-08-07, clean tree)

Tree verified clean first: lint reports no errors, the `deningerExtendFun` duplicate is gone.

- `riemannHypothesis_iff_forall_movingCriticalLogPhaseTailPacketChargeScreened` and
  `riemannHypothesis_iff_forall_movingPositiveTailCompletionGaugeChargeScreened`
  (XiCTaylorMovingPositiveCompletionGaugeNoGo) — RH ↔ the moving gauge/packet screens the finite
  Taylor charge at every point LEFT of the critical line. Bridge:
  `riemannHypothesis_iff_xi_ne_zero_of_re_lt_half`. The packet version's schedule data (hS, hL, hM)
  is sigma-independent so it stays outside the quantifier; the gauge version's positivity condition
  is not, so it is stated only for `Re sigma < 1/2` — the minimal form, not a new global hypothesis.
- `riemannHypothesis_iff_completedRiemannZeta₀_eq_neg_inv_mul_criticalLine`
  (XiThetaEndpointResidual) — RH ↔ the rational endpoint anchor `Λ₀(s) = -1/(s(s-1))` is attained
  only on the critical line.
- Three in CompletedPrimeFluxFittingAttachment for the canonical torsion seam:
  `..._hasNontrivialFittingBoundary`, `..._boundaryCoeffWitness`,
  `..._hasDeterminantTransverseDefect`. All three interfaces detect the ξ divisor exactly, so each
  is RH.

The 17-candidate sweep from the previous round is now fully closed. `SeamStripRamification.
xi_zero_iff_zeta_zero_of_mem_strip` was the only entry needing nothing: it is a ξ/ζ bridge already
subsumed by `xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial`, not a new criterion.
