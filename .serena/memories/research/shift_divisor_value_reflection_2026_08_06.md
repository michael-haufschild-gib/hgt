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
  * `GaloisForLFunctions/HTGeometry/DigammaHalfTranslateIndependent.lean` —
    `digamma_half_translate_independent`: psi(z) and psi(z+1/2) are linearly independent over C(z).
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

## Scope boundary

Divisor-side bookkeeping of the functional equation only.  It creates no positivity and is blind to
zero location; do not expect an RH criterion from it.  Use it to avoid re-proving reflection,
centering, and symbol laws for any new weighted family of completed-Xi translates.

All four modules build; `#print axioms` on every named law = `propext, Classical.choice, Quot.sound`.
Card: `docs/drafts/pipeline/3-formalized/shift-divisor-value-reflection.md`.
