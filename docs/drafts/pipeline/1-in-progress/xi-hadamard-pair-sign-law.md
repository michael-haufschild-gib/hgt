# Exact sign law of a line-conjugate Hadamard pair

- **ID:** xi-hadamard-pair-sign-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `x = Re s − ½ > 0`, `δ = Re ρ − ½`, `y = Im s − Im ρ`, the line-conjugate
  resolvent pair of the completed-zeta partial fraction has real part
  `2x(x² − δ² + y²) / (((x−δ)²+y²)((x+δ)²+y²))`.

## Goal

The corpus already has `logDeriv_xi_eq_partialFraction` (`XiExplicitFormulaLogDeriv.lean`):
`logDeriv xi s = Σ_q [(ρ_q − ½)⁻¹ + (s − ρ_q)⁻¹]`.  Pairing `ρ` with its line conjugate
`1 − conj ρ` cancels the Hadamard constants exactly, leaving `Σ Re 1/(s−ρ)` over pairs.  The
Hedenmalm centre-mixed criterion is `Re(ξ'/ξ)(½+a+ib) ≥ 0` on `0 < a < ½`
(`thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis` composed with
`fourier_thetaCuspHorizontalAutocorrelationTangent_scaled`), so this pair is the criterion's local
unit.

## What is proved (Lean, axioms `propext`, `Classical.choice`, `Quot.sound` only)

Module `GaloisForLFunctions/RHTower/XiHadamardPairSignLaw.lean`:

1. `hadamardPair_re_formula` — the exact real identity
   `(x−δ)/((x−δ)²+y²) + (x+δ)/((x+δ)²+y²) = 2x(x²−δ²+y²)/(((x−δ)²+y²)((x+δ)²+y²))`.
2. `hadamardPair_re_pos`, `hadamardPair_re_neg` — for `x > 0`, positive iff `δ² < x²+y²`,
   negative iff `x²+y² < δ²`.
3. `re_inv_sub_eq`, `re_inv_sub_lineConj_eq` — the centred forms of `Re (s−ρ)⁻¹` and
   `Re (s−(1−conj ρ))⁻¹`; note `1 − conj ρ` (not `1 − ρ`) is the pairing that keeps the ordinate.
4. `re_inv_add_re_inv_lineConj` — the complex statement of item 1.
5. `re_inv_add_re_inv_lineConj_pos` / `_neg` — the two sign regimes.
6. `re_inv_add_re_inv_lineConj_pos_of_far` — **unconditional**: every zero satisfies
   `(Re ρ − ½)² < ¼`, so a pair contributes positively whenever
   `(Re s − ½)² + (Im s − Im ρ)² ≥ ¼`.

## What this says about RH

The negative set of a single pair is exactly the open disk of radius `|Re ρ − ½|` centred at
`½ + i Im ρ`.  Hence:

- **Unconditional half.** For `s = ½ + a + ib` with `0 < a < ½`, every zero whose ordinate
  satisfies `(b − γ)² ≥ ¼ − a²` contributes positively.  Only zeros at heights within
  `√(¼ − a²)` of `b` can contribute negatively.
- **The remaining half is RH.** Taking `b = γ` the pair is negative exactly when `|Re ρ − ½| > a`;
  letting `a ↓ 0` this forces `Re ρ = ½`.  So the criterion's failure set is precisely the union
  of the off-line disks, and no zero-free-region input short of RH removes them: a zero-free
  region gives `|Re ρ − ½| < ½ − c/log(|γ|+2)`, which is `< a` only for
  `|γ| < exp(c/(½−a)) `, i.e. for a bounded set of heights.

This is the corpus's Route-Q "exact negative disk" restated in the coordinates of the completed
partial fraction, where it is the criterion's own local unit rather than a reciprocal-square
resolvent term.

## Unconditional consequence

Module `GaloisForLFunctions/RHTower/XiLogDerivRePositiveRightOfStrip.lean`:

7. `centralPaired_tsum_re_nonneg_of_lineConj_pairs` — the real-part analogue of the corpus's
   `centralPaired_tsum_im_nonneg_of_lineConj_pairs`.
8. `xiZero_lineConj_eq : ((lineConj q).1 : ℂ) = 1 − conj (q.1)`, derived from
   `xiSpectralPoint_lineConj`.
9. **`re_logDeriv_xi_nonneg_of_one_le_re : 1 ≤ Re s → 0 ≤ (logDeriv xi s).re`** — unconditional.

The proof is exactly the pair law: pairing negates the centred coordinate, so the Hadamard
constants `(ρ − ½)⁻¹` cancel in the real part (`(ρ' − ½)⁻¹ = −conj((ρ − ½)⁻¹)`), and the remaining
resolvent pair is outside its disk because `Re s − ½ ≥ ½` while `(Re ρ − ½)² < ¼`.

This is the exact unconditional boundary of the Hedenmalm criterion: the criterion asks for the
same sign on the aperture `Re s ∈ (½,1)`, where the disks are no longer avoided.

## The sharp form

Module `GaloisForLFunctions/RHTower/XiLogDerivReStripBound.lean`:

10. **`re_logDeriv_xi_nonneg_of_strip_bound`** — if `(Re ρ − ½)² < (Re s − ½)²` for **every** zero,
    then `0 ≤ Re (ξ'/ξ)(s)`.  No arithmetic input.
11. `re_logDeriv_xi_nonneg_of_riemannHypothesis` — under RH the criterion holds on all of
    `Re s > ½`, since then every zero has `(Re ρ − ½)² = 0`.

Item 10 subsumes item 9: `Re s ≥ 1` gives `(Re ρ − ½)² < ¼ ≤ (Re s − ½)²`.  The two consequences
bracket RH exactly — unconditionally on `Re s ≥ 1`, under RH on `Re s > ½` — and the gap between
them is precisely the off-line disks.

The converse (criterion on `Re s > ½` ⟹ RH) is the corpus's
`thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`; the direct proof would approach a
hypothetical off-line zero from the left, where `logDeriv xi s ∼ m/(s−ρ)` has real part `→ −∞`.
Not duplicated here.

## The criterion, both directions

Module `GaloisForLFunctions/RHTower/XiLogDerivReCriterion.lean`:

12. `re_xi_deriv_conj_pair` — `Re[ξ'(s)ξ(conj s) + ξ(s)ξ'(conj s)] = 2‖ξ(s)‖² Re(ξ'/ξ)(s)`,
    valid **including at the zeros**, where both sides vanish (`logDeriv` is `deriv/f`, and
    `x/0 = 0`).
13. `riemannHypothesis_of_re_logDeriv_xi_nonneg` — the reverse direction, via the corpus's
    `thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis` and
    `fourier_thetaCuspHorizontalAutocorrelationTangent_scaled`.
14. **`riemannHypothesis_iff_re_logDeriv_xi_nonneg :
    RiemannHypothesis ↔ ∀ s : ℂ, 1/2 < s.re → 0 ≤ (logDeriv xi s).re`** — both directions
    unconditional, no side hypothesis at the zeros.

So the whole route is now one displayed inequality.  Item 10 proves it whenever every zero is
strictly closer to the line than `s`; item 14 says that proving it for all `Re s > 1/2` is RH.

## Locality and an unconditional region inside the strip

Module `GaloisForLFunctions/RHTower/XiLogDerivReLocality.lean`:

15. `re_logDeriv_xi_nonneg_of_disk_bound` — the sharp hypothesis, keeping the `(Im s − Im ρ)²`
    term: a zero obstructs only from inside its own disk.
16. **`re_logDeriv_xi_nonneg_of_near_zeros`** — the criterion is **local in the ordinate**.  Every
    zero has `(Re ρ − ½)² < ¼`, so a zero with `|Im s − Im ρ| ≥ ½` can never obstruct; only the
    `O(log|Im s|)` zeros in the unit ordinate window matter.

Module `GaloisForLFunctions/RHTower/XiLogDerivReLowHeight.lean`:

17. **`re_logDeriv_xi_nonneg_of_low_height : 1/2 < Re s → |Im s| ≤ 14 → 0 ≤ (logDeriv xi s).re`** —
    unconditional, no computation.  Combines item 16 with the corpus's order-23 threshold
    `fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine` (every off-line copy has
    `γ² ≥ 431/2`, i.e. `|γ| ≥ 14.67…`): a point of height `≤ 14` has no off-line zero within
    ordinate distance `1/2`, since `(14 + ½)² = 210.25 < 215.5`.

This is the first verification of the RH-equivalent criterion on a two-dimensional region strictly
**inside** the critical strip.  It also shows the shape of any improvement: a theorem "off-line
zeros have `|γ| ≥ H`" yields the criterion on `|Im s| ≤ H − ½`, and RH is `H = ∞`.

## The ordinate-integrated pair law

Module `GaloisForLFunctions/RHTower/XiHadamardPairOrdinateIntegral.lean`:

18. `integrable_cauchyKernel`, `integral_cauchyKernel_pos`, `integral_cauchyKernel_neg` —
    `∫_ℝ a/(a²+y²) dy = π·sign a`, from `integral_univ_inv_one_add_sq` by the dilation
    `Measure.integral_comp_mul_left`.
19. **`integral_hadamardPair_inner`** — if `δ² < x²` the pair integrates to `2π`.
20. **`integral_hadamardPair_outer`** — if `x² < δ²` the pair integrates to exactly `0`: the two
    halves cancel.
21. `re_logDeriv_xi_nonneg_of_offLine_height` — any ordinate floor `H` for off-line copies yields
    the criterion on `Re s > 1/2`, `|Im s| ≤ H − 1/2`.  Item 17 is the case `H = 14.5`.

Items 19–20 are the counting form of the disk law: integrated over the ordinate, a zero **closer**
to the line than `s` contributes the full `2π`, and a zero **further out** contributes nothing at
all.  So `∫_ℝ Re(ξ'/ξ)(σ+it) dt` counts, with weight `2π`, exactly the zeros inside the abscissa
`Re s`; the difference between two abscissae counts the zeros in the intervening vertical strip.
This is the classical vertical-strip zero count, recovered here directly from the pair law.

## The falsification criterion

Module `GaloisForLFunctions/RHTower/XiLogDerivReFalsification.lean`:

22. `exists_zero_disk_of_re_logDeriv_xi_neg` — if `Re (ξ'/ξ)(s) < 0` with `Re s > 1/2`, then some
    divisor copy satisfies `(Re s − ½)² + (Im s − Im ρ)² ≤ (Re ρ − ½)²`: a single negative value
    **locates** the counterexample in an explicit closed disk.
23. `exists_offLine_zero_of_re_logDeriv_xi_neg` — that copy is off the critical line.
24. `not_riemannHypothesis_of_re_logDeriv_xi_neg`, and
    **`not_riemannHypothesis_iff_exists_re_logDeriv_xi_neg :
    ¬ RiemannHypothesis ↔ ∃ s, 1/2 < Re s ∧ (logDeriv xi s).re < 0`.**

So the two halves of the goal are now symmetric and both effective: proving RH is proving one
inequality on `Re s > 1/2`; refuting it is exhibiting one point where that inequality fails, and
the failure point pins the offending zero to a disk.

## The criterion throughout a zero-free region

Module `GaloisForLFunctions/RHTower/XiLogDerivReWindowWidth.lean`:

25. `re_logDeriv_xi_nonneg_of_window_width` — if every copy in the unit ordinate window around
    `Im s` has `|Re ρ − ½| ≤ w` and `w < Re s − ½`, the criterion holds at `s`.
26. `re_logDeriv_xi_nonneg_of_local_zero_free` — instantiated with a zero-free half-width `Z`
    valid in the window: the criterion holds for every `Re s > 1 − Z`.

This is a qualitatively different unconditional domain from item 17.  The low-height box is short
and wide; this one is **unbounded in the ordinate** and narrow.  With the classical width
`Z = c/log(|t|+5/2)` it gives the criterion for `Re s > 1 − c/log(|Im s|+5/2)` at every height —
the whole classical zero-free region.  Item 17 and item 26 are complementary, and their union is
the current unconditional domain.

Note the mechanism: only the window copies enter, so a *local* zero-free statement suffices; no
global height floor is needed.  This is why item 26 escapes the source-budget ceiling below, which
constrains only global floors.

## Boundary behaviour

Module `GaloisForLFunctions/RHTower/XiLogDerivReCriticalLine.lean`:

27. `re_logDeriv_xi_eq_zero_of_re_eq_half` / `re_logDeriv_xi_eq_zero_critical_line` — the criterion
    quantity **vanishes identically on the critical line**.  On `Re s = 1/2` one has
    `conj s = 1 − s`, so `logDeriv_xi_conj_global` and `logDeriv_xi_one_sub` give
    `conj (ξ'/ξ)(s) = −(ξ'/ξ)(s)`.  The critical line is the exact boundary of the criterion's
    region, and the inequality cannot be strengthened to a strict one up to it.

## Strictness

Module `GaloisForLFunctions/RHTower/XiLogDerivRePositiveStrict.lean`:

28. `centralPaired_tsum_re_pos_of_lineConj_pairs` — strict version of the pairing summation
    (`Summable.tsum_pos` plus one strictly positive pair).
29. `re_logDeriv_xi_pos_of_disk_bound` — **strict** criterion wherever the disk bound is strict,
    using `nonempty_xiZeroCopy_xiLogDerivLineOnePositive` (Hardy) for the witness.
30. `re_logDeriv_xi_pos_of_riemannHypothesis` — under RH, `0 < Re (ξ'/ξ)(s)` at every `s` right of
    the critical line with `ξ s ≠ 0`.

Items 27 and 30 pin the boundary behaviour exactly: under RH the quantity is strictly positive
throughout `Re s > 1/2` and vanishes identically on `Re s = 1/2`.  So the margin is real everywhere
off the line and degenerates only in the limit — the inequality is sharp, not slack.

## Arithmetic form

Module `GaloisForLFunctions/RHTower/XiLogDerivReArithmeticBound.lean`:

31. `re_LSeries_vonMangoldt_lt_polar_add_archimedean` — for `Re s > 1`,
    `Re (Σ_n Λ(n) n^{−s}) < Re(1/s) + Re(1/(s−1)) + Re(logDeriv Γ_ℝ s)`, unconditional, with no
    zeros in the statement.  This is the arithmetic content of the divisor-side positivity: the
    von Mangoldt series is dominated by purely polar and archimedean data.

## Averaging is abscissa translation

Module `GaloisForLFunctions/RHTower/XiHadamardPairCauchyAverage.lean`:

32. `integral_cauchyKernel_mul` — `∫_ℝ (a/(a²+y²))(h/(h²+y²)) dy = π/(a+h)` for `a, h > 0`,
    `a ≠ h`, by partial fractions and item 18.
33. **`integral_hadamardPair_cauchy_average`** — a line-conjugate pair averaged against a Cauchy
    weight of width `h` equals `π` times the **same pair at abscissa shifted right by `h`**.

This upgrades the fifth failed mechanism from an argued claim to a proved one: ordinate averaging
does not produce information the pointwise statement lacks, it merely re-evaluates the criterion
further from the critical line, where it is weaker.  Together with items 19–20 (outer zeros
integrate to exactly zero) this closes off averaging arguments on this card.

## Route status

The characterisation is complete: equivalence in both directions (14), effective falsification
with zero localisation (22–24), strict interior positivity (29–30), identical vanishing on the
boundary (27), ordinate locality (16), the integrated counting law (19–20), two unconditional
regions (17, 26), the global-height-floor ceiling, and the arithmetic form (31).

What the route does **not** supply is a zero-free width that does not shrink with height.  Every
mechanism tried against that gap has failed for a recorded reason: pointwise positivity of the
theta current (false at the archimedean base), zero-free-region input (covers only bounded height
sets), finite-width local positivity radii (route G's recorded no-go), source-budget height floors
(ceiling `≈ 15.8`), and ordinate averaging (items 19–20, 33: outer zeros integrate to exactly zero, and averaging is
abscissa translation).  Further work
on this card should start from a different mechanism, not a sharper constant.

## Duplication audit (2026-09-24)

`XiLogDerivLineOnePositive.lean` **already contained**
`re_logDeriv_xi_pos_of_one_le_re : 1 ≤ Re s → 0 < Re (ξ'/ξ)(s)` — strictly stronger than my
item 9 — with the same mechanism (partial fraction, reflection pairing, cancellation of the
`Re 1/(ρ−½)` constants, Hardy's theorem for nonemptiness).  Items 7–9 of this card therefore
duplicate existing corpus results and should be treated as redundant; the corpus version is
preferable.  Its pairing is `ρ ↦ 1−ρ`; mine is `ρ ↦ 1−conj ρ`, which is what produces the exact
quadratic form, so items 1–6 and 10 onward are not affected.

Not duplicated: the exact disk sign law (items 1–6), ordinate locality (16), the low-height and
window-width regions (17, 25, 26), the criterion and falsification equivalences (14, 24), the
ordinate-integrated counting law (19, 20), and item 27.

## Ceiling of the source-budget method

The order-23 threshold comes from `four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine`:
`4 · atom(q₀) ≤ normalizedPrimeArchMoment 1`, where by
`tsum_xiFourthReciprocalTraceAtom_eq_source` the right side is `Σ_q atom(q)` itself, and
`atom(q) = Re (w_q^{−4})`, `w_q = xiSpectralPoint q`.  The contradiction needs
`4 · atom(q₀) > M₁`, and `atom(q₀) ≈ |γ₀|^{−4}`, so the method works exactly while

`|γ₀| < (4 / M₁)^{1/4}` .

With the corpus's bound `M₁ < 17/200000` this is `γ₀² < 800000/(17·4)·…`, i.e. `γ₀² < 216.9` —
and the installed threshold is already `γ₀² < 215.5`, within `0.3 %` of that ceiling.  So **no
further progress is available from the current moment bound**; only a sharper analytic bound on
`normalizedPrimeArchMoment 1` would move it.  Its true value is dominated by the lowest zeros and
is near `6.4·10⁻⁵`, which would cap the method at `|γ₀| < 15.8`, hence the unconditional region at
`|Im s| ≲ 15.3`.  Any `H` beyond that needs a different mechanism: a single off-line zero's four
FE–Schwarz copies simply do not exceed the true total.

## Open core

- `[OPEN CORE]` A producer.  The unconditional half above is sharp; the negative disks are exactly
  the off-line zeros, so removing them *is* RH.  No route in the ledger supplies an arithmetic law
  that excludes them.

## Log
- 2026-09-24 — created at stage 3; ten Lean theorems, wired into `RHTower`, axiom-clean, lint
  passes.
