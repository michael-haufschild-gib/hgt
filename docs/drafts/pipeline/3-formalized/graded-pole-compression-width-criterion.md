# The two-by-two pole criterion is graded by the width and reads a size, not a sign

- **ID:** graded-pole-compression
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md` §5 item 2
  (faithfulness of the pole compression); `RHTower.CCMRestrictedWeilPoleCompressionRHCriterion`;
  `SquareRootThreshold.PrimeTailCouplingCriterion`;
  `BiScaleUncertainty.DeficitPrimitiveOneSidedWidth`, `.BandSpectrumZeroWidthLaw`.
- **Statement:** The exponential growth rate of the single cross entry `|ccmWeilPoleCross a|` of
  the literal two-exponential pole matrix is exactly `1 + 2 · zetaZeroWidth`; in particular
  `|ccmWeilPoleCross a| ≤ C e^{a}` at every aperture implies RH, with no diagonal and no sign.

## Goal
The corpus owns the pole-compression RH criterion in **sign** form (`RiemannHypothesis ↔
∀ a, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a`) and, separately, the one-sided width criterion
for the integrated Chebyshev deficit and generalized von Koch in the gauge. Composing the three
changes what has to be estimated and answers the admissibility question of
`ScaleSignedIncidenceCriticality` §5.2:

1. **Size, not sign.** The criterion's content is an order of magnitude. Since the diagonal itself
   satisfies `|ccmWeilPoleDiagonal a| ≤ C₀ e^{a}`, the sign inequality is the special case of a
   square-root-scale bound, and the compression may *fail* — by as much as `e^{a}` — and still
   decide the line. So no sign mechanism is required of the two-by-two inequality, and the
   positivity framing is not where its difficulty lies.
2. **Graded by the width.** For every `0 ≤ α < 1/2` a bound `|ccmWeilPoleCross a| ≤ C e^{(1+2α)a}`
   gives the zero-free half-plane `Re ρ ≤ 1/2 + α`. Partial progress is an explicit exponent in the
   shared width unit, not an all-or-nothing demand.
3. **Faithful.** The converse holds at every rate above the width, so the reading
   `a ↦ ccmWeilPoleCross a` loses nothing about the width: it is the smallest faithful reading the
   corpus has (one scalar function of one real variable), and therefore the natural target of any
   construction, in the sense of the admissibility calculus.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (composition of three owned theorems; see Approach)
- [x] 2 → 3  formalized:
  `formal/GaloisForLFunctions/BiScaleUncertainty/GradedPoleCompressionWidthCriterion.lean`,
  wired into `GaloisForLFunctions.BiScaleUncertainty`; every capstone depends only on
  `propext, Classical.choice, Quot.sound`.
- [ ] 3 → 4  publication-ready

## Approach
The cross entry *is* the integrated Chebyshev deficit `D(T) = ∫_0^T (e^t − ψ(e^t)) dt` at `T = 2a`,
up to its Gamma boundary mass, an explicit linear radius correction and an endpoint
(`RHTower.abs_integratedChebyshevDeficit_sub_weilPoleCross_le`); all three are at most
`poleCrossDeficitAllowance · e^{a}`. Hence `|cross a|` and `|D(2a)|` differ by at most the
square-root scale, in both directions.

* Forward: a bound `|cross a| ≤ C e^{(1+2α)a}` gives `|D(T)| ≤ (C + allowance) e^{(1/2+α)T}`, which
  is the one-sided hypothesis of `xiZeroHalfPlaneBound_of_deficitPrimitive_oneSided` with `ε = +1`
  and `B = C + allowance`. Only one side of the deficit is used, so the sign of the cross entry is
  free.
* Converse: generalized von Koch in the gauge
  (`ChebyshevGauge.exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound`) gives
  `|ψ(e^t) − e^t| ≤ C₀ e^{(1/2+β')t}` for every `β' > α`; integrating over `[0, T]` and absorbing
  the factor `T` into `e^{(β−β')T}/(β−β')` gives `|D(T)| ≤ (C₀/δ) e^{(1/2+β)T}`, hence the matching
  bound on the cross entry.
* The two directions meet by density in `β`, which is the faithfulness statement.

## Lean (unconditional, standard axioms only)
- `abs_ccmLogChebyshevDeficitPrimitive_le_abs_ccmWeilPoleCross_add`,
  `abs_ccmWeilPoleCross_le_abs_ccmLogChebyshevDeficitPrimitive_add` — the two-sided identification
  at the square-root scale, with the explicit `poleCrossDeficitAllowance`.
- `xiZeroHalfPlaneBound_of_abs_ccmWeilPoleCross_le` — the graded criterion.
- `xiZeroHalfPlaneBound_of_poleCompression_slack` — the published criterion as the slack case.
- `riemannHypothesis_of_abs_ccmWeilPoleCross_le` — RH from one square-root-scale size bound.
- `exists_abs_ccmLogChebyshevDeficitPrimitive_le_of_xiZeroHalfPlaneBound`,
  `exists_abs_ccmWeilPoleCross_le_of_xiZeroHalfPlaneBound` — the converse.
- `xiZeroHalfPlaneBound_iff_forall_exists_abs_ccmWeilPoleCross_le` — faithfulness.

## Units and selectivity
In the shared units the contribution is the gradation itself: an estimate on the cross entry at
rate `1 + 2α` is the zero-free strip `Θ ≤ 1/2 + α`, so progress is reported as an exponent and not
as an identity. The criterion is **not** selective in the sign sense — it is a size statement about
one explicit function, so it cannot be attacked by a sign or positivity mechanism; the required
input is a square-root-scale estimate for the integrated Chebyshev deficit, which is Wall 1. The
contribution is therefore a change of what must be estimated, not an estimate.

## What it does not prove
Nothing about the size of `ccmWeilPoleCross`. The unconditional bound available is the
Vinogradov–Korobov one, `|D(T)| ≪ e^{T}e^{−cT^{3/5}}`, which is `e^{2a}` up to the VK factor and so
far above the needed `e^{(1+2α)a}` for every `α < 1/2`.

## Log
- 2026-10-22 — created at stage 3; module written, compiled, wired into `BiScaleUncertainty`.
