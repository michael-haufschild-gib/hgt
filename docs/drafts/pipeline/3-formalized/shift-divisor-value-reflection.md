# Shift-divisor value reflection for completed Xi

- **ID:** shift-divisor-value-reflection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus audit of the `Xi*ValueReflection` / `Xi*ValueRelation` family
- **Statement:** For every finitely supported complex divisor `w` of shifts and every function with a
  signed reflection `f(2c₀ − z) = ε f(z)`, reflecting the observation coordinate about `σ/2` is
  exactly reflecting the divisor about `(2c₀ − σ)/2`, with the factor `ε`.

## Goal

The corpus carried a one-shift value reflection (`XiTransverseShiftPrimeDefectValueReflection`) and
a two-endpoint pairwise one (`XiPairwiseShiftValueReflection`), each with its own reflection centre,
its own archimedean cocycle, its own half-cocycle centering, and — in the pairwise case — an
endpoint-order hypothesis discharged by an `if b ≤ a` case split. Independently,
`ReflectionDifferenceFaces` carried the classical centre-shift-and-flip rule for iterated forward
differences. These are all the same statement about a divisor of shifts. Making the divisor the
primitive removes the order hypothesis, removes the integrality hypothesis, and exposes two laws that
hold with no eigen hypothesis at all.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `lake build` green, `#print axioms` = `propext, Classical.choice, Quot.sound`
- [ ] 3 → 4  publication-ready

## The law

For `w : ℂ →₀ ℂ`, `shiftDivisorValue w f s = ∑ a w a · f (s + a)` and
`reflectShiftDivisor c w` is the divisor with `a ↦ c − a`. Then

    shiftDivisorValue w f (σ − s) = ε · shiftDivisorValue (reflectShiftDivisor (2c₀ − σ) w) f s.

Consequences:

- the value has an exact reflection law about `σ/2` iff the divisor is a reflection eigenvector, and
  the eigenvalue `η` multiplies the functional-equation sign;
- the annihilating divisors of `f` form a submodule stable under translation and (when `ε ≠ 0`)
  under reflection;
- every divisor splits canonically into invariant and anti-invariant parts, so *every* weighted
  completed-Xi family splits into a reflection-fixed piece and a piece vanishing at the centre —
  no eigen hypothesis needed;
- for entire `xi` the vanishing piece vanishes to all orders in the prescribed jet parity.

Arithmetic side: the divisor acts on Dirichlet coefficient streams by its symbol
`n ↦ ∑ a w a · n^(−a)`, and on the Euler half-plane the corrected completed-Xi divisor value is
minus the von Mangoldt L-series twisted by that symbol. Divisor reflection about `(1−σ)/2` is the
symbol inversion `n^(−a) ↦ n^a` twisted by `n^(σ−1)`.

## Lean

| Module | Content |
|---|---|
| `HTGeometry/ShiftDivisorReflection.lean` | divisor value, divisor reflection/translation, the signed reflection law, eigen corollaries, annihilator submodule, canonical splitting, iterated difference divisors, analyticity |
| `HTGeometry/ShiftDivisorLSeries.lean` | Dirichlet symbol, twisted stream, `LSeries_shiftDivisorStream`, symbol inversion under reflection |
| `RHTower/XiShiftDivisorValueReflection.lean` | completed-Xi and `logDeriv xi` instances, corrected value + cocycle + half-centering at divisor level, central jet parity, point/two-point connectors to the existing one-shift and pairwise theories |
| `RHTower/XiShiftDivisorPrimeSymbol.lean` | `logDeriv xi − logDeriv archFactor = −LSeries Λ` on `Re s > 1`, the divisor prime-symbol law, the reflection/inversion dictionary |
| `RHTower/XiShiftDivisorFaithful.lean` | symbol = translation character at frequency `log n`; trivial annihilator of the corrected completed-Xi value; injectivity of divisor ↦ value |
| `RHTower/XiEvenShiftDivisorRationality.lean` | pointwise closed form of the archimedean correction at every even shift; parity reduction of an arbitrary natural shift; the parity-balance criterion for rationality |

## Parity balance

The archimedean factor `archFactor s = s(s−1)/2 · Γ_ℝ(s)` contributes exactly two digamma modes to a
natural-shift family, one per parity class. Reducing an arbitrary shift `a` to its residue
`a % 2` (`logDeriv_archFactor_shift_split`) makes this explicit, and gives

**Exact parity decomposition** (`archimedeanCorrection_family_parity_decomposition`, no hypothesis on
the coefficients): for `0 < Re s`, `s ≠ 1`,

    ∑ᵢ cᵢ · logDeriv archFactor (s + aᵢ)
      = (even mass) · logDeriv archFactor s
      + (odd mass) · logDeriv archFactor (s+1)
      + explicit rational function.

**Parity-balance criterion.** If the even-shift coefficients sum to zero and the odd-shift
coefficients sum to zero, both digamma modes cancel and the family's archimedean correction is an
explicit rational function (`archimedeanCorrection_family_of_parity_balanced`).

This covers odd shifts, which the corpus previously excluded — `XiTransverseShiftPrimeDefectValueReflection`
states "no rationality … claim is made here for odd shifts", and the even-shift telescope only handles
shifts `2m` against the base. The point is that oddness is not the obstruction; unbalanced parity mass
is. The pair `δ_1 − δ_3` is odd and rational; `δ_1 − δ_0` is not.

By-products:

- `xiTransverseShiftArchimedeanCorrection (2m) s = xiEvenShiftPrimeCorrection m s` now holds
  **pointwise** (the corpus had it only as an upper-end germ, via
  `xiEvenShiftPrimeCorrection_upperEndGerm_eq_archimedean`), and with it the pointwise identification
  `xiEvenShiftPrimeDefect m s = xiTransverseShiftPrimeDefect (2m) s`.
- The Euler-half-plane hypothesis `1 < Re s` is not needed: `logDeriv_archFactor_shift_two_of_re_pos`
  weakens the corpus's `logDeriv_archFactor_shift_two` to `0 < Re s` and `s ≠ 1`, and the whole
  parity layer inherits that domain.
- **Same-parity pairs** (`xiPairwiseShiftPrimeDifference_eq_explicit`): for integral shifts of equal
  parity the corrected pairwise value is the raw logarithmic-derivative difference minus the explicit
  rational telescope of their half-difference. The corpus's shift-two theory
  (`XiShiftPrimeReflectionCocycle`) is the pair `(2,0)`.

### The converse input

The decomposition isolates one missing fact: independence of the two digamma modes over the rational
functions. That fact is now proved.

| Module | Content |
|---|---|
| `HTGeometry/DifferenceTwoOrbitBrick.lean` | a rational function has no unit-shift difference whose pole part sits on finitely many pairwise incommensurable `ℤ`-orbits (`difference_multi_orbit_pole_free`); the corpus's single-orbit brick and the two-orbit form are `d = 1, 2` |
| `HTGeometry/DigammaHalfTranslateIndependent.lean` | `ψ(z)` and `ψ(z+1/2)` are linearly independent over `ℂ(z)` |

The corpus already had the single-orbit brick (`difference_single_pole_free` in
`HolderDifferenceBricks`, the engine of its Hölder/hypertranscendence proof). The two-orbit version is
what the parity problem needs, because the poles of `ψ(s/2)` and `ψ((s+1)/2)` lie in `ℤ`-orbits that
differ by a half-integer. Mechanism: pinch each orbit separately — evaluating the cross-multiplied
identity at the largest root of the denominator in an orbit forces that root to be the orbit's base
point, and evaluating one step below the smallest forces the smallest to be one past it; incompatible
unless the denominator has no root in the orbit at all. Then the denominator is coprime to both
linear factors, so the pole-part numerator is divisible by a polynomial of larger degree, hence zero.

Applied to the digamma recurrence: `E·ψ(z) + O·ψ(z+1/2) = P(z)/Q(z)` becomes
`R(z+1) − R(z) = E/z + O/(z+1/2)`, whose pole part sits on the orbits of `0` and `−1/2`. The brick
forces `E = O = 0`.

### The negative half

`RHTower/XiOddShiftArchimedeanIrrationality.lean` closes the shift-one case in the negative
direction. The closed form

    logDeriv archFactor (s+1) − logDeriv archFactor s
      = 1/(s+1) − 1/(s−1) + ψ((s+1)/2)/2 − ψ(s/2)/2

carries both digamma modes with opposite nonzero weights; substituting `s = 2z` turns them into
`ψ(z)` and `ψ(z+1/2)`, so half-translate independence applies directly and gives
`xiTransverseShiftArchimedeanCorrection_one_not_rational`: **no quotient of polynomials agrees with
the shift-one archimedean correction on the right half-plane.**

So parity balance is not merely a convenient sufficient condition — it is genuinely needed already
for the single odd shift, which is exactly the case the corpus had left open.

To make the applications plumbing-free, the independence theorem is stated in three strengths:
lowest terms; lowest terms off a finite exceptional set; and an arbitrary quotient off a finite
exceptional set (reduction to lowest terms via `RatFunc.num`/`RatFunc.denom`).

### The dichotomy, closed

`HTGeometry/HalfPlaneRational.lean` introduces `IsHalfPlaneRational f` — agreement with a quotient of
polynomials on the right half-plane, off a finite exceptional set. The class is closed under sums,
differences, constant multiples, finite sums, the substitution `z ↦ 2z`, and agreement off a finite
set, which is exactly the bookkeeping a value relation assembled from simple fractions needs.

`RHTower/XiParityMassDichotomy.lean` then gives the biconditional
(`archimedeanCorrection_family_isHalfPlaneRational_iff`):

> A natural-shift family's archimedean correction is half-plane rational **iff** its even-shift
> coefficient mass and its odd-shift coefficient mass both vanish.

Sufficiency is the explicit telescope; necessity is half-translate digamma independence applied to
the parity decomposition after subtracting the telescope and the finitely many simple fractions
contributed by `s(s−1)/2`.

### Off the right half-plane

Reading the corpus proof of `hasDerivAt_Gammaℝ_of_re_pos` shows `0 < Re s` is used only to place `s/2`
away from the poles of `Γ`. Generalizing that hypothesis in place (keeping the old name as a
corollary) propagates: `hasDerivAt_archFactor_off_poles`, `logDeriv_archFactor_closed_off_poles`, and
then the whole even ladder.

`RHTower/ArchLadderRegular.lean` packages the two conditions the ladder actually needs —
`s` avoids the poles of `Γ(s/2)`, and `s` is not an odd integer (where `s(s−1)/2` vanishes after an
even translation) — as `ArchLadderRegular s`, stable under even translation. Consequence:

- `xiTransverseShiftArchimedeanCorrection_even_of_ladderRegular` — the rational telescope holds on the
  whole ladder, not merely on the right half-plane;
- `xiPairwiseShiftReflectionCocycle_eq_explicit` — the previously blocked item: an **explicit rational
  reflection cocycle for every same-parity integral pair**. The reflected point `1 − a − s` sits in
  the left half-plane, which is exactly what the old domain restriction could not reach.
- `xiPairwiseCenteredShiftPrimeDifference_eq_explicit` — half-cocycle centering subtracts the average
  of the rational telescope at the point and at its reflection, so the completed-Xi content of the
  centered value is the raw logarithmic-derivative difference alone. The corpus's shift-two centering
  (`XiShiftPrimeReflectionCocycle`) is the pair `(2,0)`.

### Side conditions discharged

`archLadderRegular_of_re_not_int` — both ladder conditions force the real part to be an integer, so a
**non-integral real part discharges them together**, with no positivity requirement at all. Hence:

- `archLadderRegular_strip_add_nat` — every natural translate of a point of the open critical strip;
- `archLadderRegular_strip_reflect` — every reflection `1 − a − ρ` of such a point.

Both real parts land strictly between consecutive integers. Consequently the same-parity explicit
laws hold at any strip point with **only** the strip hypothesis — which at a Xi zero is itself a
corpus theorem (`xi_divisor_support_re_mem_open_unit`):
`xiPairwiseShiftReflectionCocycle_eq_explicit_of_strip`,
`xiPairwiseShiftPrimeDifference_eq_explicit_of_strip`,
`xiPairwiseCenteredShiftPrimeDifference_eq_explicit_of_strip`.

The even-shift defect identification follows the same path:
`xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect_of_ladderRegular` holds on the whole ladder
and `..._of_strip` at every strip point. The corpus records this identification only as an upper-end
germ; it is a pointwise identity wherever the real part is not an integer.

Unrelated hygiene: `completedRiemannZeta_eq_Gammaℝ_mul` carried a redundant `s ≠ 0` alongside
`0 < Re s`; the premise is discharged and its two call sites updated.

### Archimedean nonvanishing, sharpened

The corpus proves `archFactor z ≠ 0` only on the strip (`archFactor_ne_zero_strip`, hypothesis
`0 < Re z ∧ Re z < 1`) or from a supplied `Γ_ℝ z ≠ 0`. The sharp statement needs no positivity at all:

    archFactor_ne_zero_iff : archFactor s ≠ 0 ↔ s ≠ 1 ∧ ∀ n : ℕ, s ≠ -(2n)

`archFactor` vanishes exactly at `1` and at the poles of `Γ(s/2)`; `s ≠ 0` is subsumed by the `n = 0`
clause. Two premises fall out of it:

- `archFactor_ne_zero_of_re_pos` — the strip's **upper** bound `Re z < 1` was only ever used to get
  `z ≠ 1`, so `0 < Re z` plus `z ≠ 1` suffices. This reaches the region `Re s > 1` where the ladder
  work lives and where the corpus previously had no nonvanishing lemma at all.
- `archFactor_ne_zero_of_ladderRegular` — ladder regularity already implies nonvanishing, so no
  separate side condition is needed anywhere on the even ladder, reflected points included.

### The completed split, unified

The strip form of the completed logarithmic-derivative split uses its upper bound `Re s < 1` for one
thing only: to know `s ≠ 1`. With sharp archimedean nonvanishing the bound goes away
(`RHTower/CompletedSplitRightHalfPlane.lean`):

- `logDeriv_completed_split_of_re_pos` — `0 < Re s`, `s ≠ 1`, `riemannZeta s ≠ 0`;
- `seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_of_re_pos` — the prime/archimedean
  decomposition of the seam flux on the same region.

The corpus records the strip case (`seamFluxCochain_eq_infinitePrimeFlux_add_archimedean`) and the
absolute-convergence case (`seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re`) as two separate
theorems for two disjoint regions. Both are instances of this one, which also covers the gap between
them (`Re s = 1` excepting `s = 1`, and the rest of `Re s > 0`).

On `Re s ≥ 1` the zeta side condition discharges outright, by classical non-vanishing
(`riemannZeta_ne_zero_of_one_le_re`), giving hypothesis-free forms
`logDeriv_completed_split_of_one_le_re` and
`seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_of_one_le_re`. These reach the **line**
`Re s = 1`, which neither regional statement covers — one needs `Re s < 1`, the other `Re s > 1` —
and which is exactly where the classical non-vanishing theorem lives.

### Endpoint order discharged

`xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit_symm` and
`xiPairwiseShiftPrimeDifference_eq_explicit_symm` drop the `b ≤ a` premise with no case split in the
conclusion: truncated `ℕ` subtraction makes exactly one of the two telescopes nonempty, and
`xiEvenShiftPrimeCorrection 0 = 0` kills the other. The regularity hypothesis moves to `s + min a b`,
which is the point the formula actually reads.

## Faithfulness

The Dirichlet symbol at `n` is the translation character of the divisor at the frequency `log n`
(`shiftDivisorSymbol_eq_translationChar`). Ray-complete translation faithfulness on the prime-log
rays (`euler_translation_faithful`) then gives: a divisor whose symbol vanishes at every prime power
is zero. Feeding the prime-symbol law and Dirichlet-series injectivity into this converts an
*analytic* value relation into the *algebraic* conclusion:

    (∀ s, 1 < Re s → ∑ a w a · (logDeriv xi (s+a) − logDeriv archFactor (s+a)) = 0) → w = 0

for divisors with shifts of nonnegative real part. So the corrected completed logarithmic derivative
satisfies no nontrivial linear difference relation with constant complex coefficients, and distinct
divisors give distinct values. The corpus already had the character-level faithfulness; the new
content is the bridge from the analytic value relation down to it.

In finite-family form (`completedPrimeSource_translate_independent`): distinct complex shifts of
nonnegative real part give linearly independent corrected completed logarithmic derivatives on the
Euler half-plane. The corpus proved the corresponding statement for distinct nonzero *natural*
shifts through differential independence
(`linearIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff`); the arithmetic route reproves it
and extends it to arbitrary complex shifts with `0 ≤ Re a`.

Named laws: `shiftDivisorValue_signed_reflection`, `shiftDivisorValue_reflection_of_eigen`,
`reflectShiftDivisor_mem_annihilator`, `reflectShiftDivisor_iteratedDifferenceDivisor`,
`iteratedForwardDifference_eq_shiftDivisorValue`, `xiShiftDivisorLogDeriv_reflection`,
`xiShiftDivisorLogDeriv_symm_add_antisymm`, `iteratedDeriv_xiShiftDivisorValue_center_eq_zero`,
`xiShiftDivisorCenteredPrimeValue_reflection`, `LSeries_shiftDivisorStream`,
`xiShiftDivisorPrimeValue_eq_lSeries`, `shiftDivisorSymbol_of_xiReflection_eigen`.

## What this does not do

It does not decide RH. The reflection law is divisor-side bookkeeping of the functional equation; it
creates no positivity and sees no zero location. Its value is that every future weighted family of
completed-Xi translates inherits its reflection law, its centering, and its Dirichlet symbol without
re-proving them, and that the arithmetic shadow of the reflection is now an explicit involution on
symbols.

## Log

- 2026-08-06 — created directly in 3-formalized; four modules built, axioms clean.
