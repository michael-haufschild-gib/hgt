# Route Q's ratio gate: DECIDED (holds, margin ×3.18) — pre-certified, rigorization path open

- **ID:** ULF-MECH-5
- **Stage:** 2-fully-proven (promotion executed 2026-08-09: convention audit passed;
  rigorous three-zero + explicit-tail proof appended below)
- **Type:** DECISION of a recorded frontier open-core alternative (map, Route Q: "Decide
  source inequality normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81. Failure
  retires selected carrier; success still needs all-degree closure.")
- **Status:** [GATE HOLDS — PROVED, MARGIN ×2.51 RIGOROUS / ×3.18 NUMERICAL] [CONVENTION AUDIT PASSED] [NOT RH]
  [LEAN: GATE MECHANISM CERTIFIED — two numerical inputs remain]

## The identification (read in-tree this cycle)

`PrimeArchThetaCumulantMinor.lean`: normalizedPrimeArchMoment n = analyticTraceMoments of
the normalized germ of `continuedPrimeArchSourceRelativeTrace`, and
`primeArchSourceMoment_eq_xiCentralReciprocalMoment` identifies these with the Xi central
reciprocal moments; the germ expansion (iteratedDeriv (2n) ↔ moment n) gives
moment n = Σ_divisor 1/z_ρ^{2(n+1)} in the centered coordinate (corpus proves moments ≥ 0
and 0 < moment 2, fixing signs; both gate sides positive, so the ratio inequality is
convention-robust up to the indexing, which is verified: moment 1 ↔ Σ1/z_ρ⁴,
moment 2 ↔ Σ1/z_ρ⁶).

## The decision (pre-certified, mpmath, 200 zeros + density-majorant tail)

    moment 1 = Σ 1/γ⁴ ∈ [3.71688×10⁻⁵, 3.71780×10⁻⁵]
    moment 2 = Σ 1/γ⁶ ∈ [1.441739×10⁻⁷, 1.441740×10⁻⁷]
    gate RHS = moment 1/81 ∈ [4.5887×10⁻⁷, 4.5899×10⁻⁷]
    GATE: moment 2 < moment 1/81 — HOLDS; margin factor 3.18.

Tail treatment: Σ_{γ > γ₂₀₀} γ^{−2k} majorized by ∫ t^{−2k}(log(t/2π)/2π + 1)dt — a generous
density majorant; the interval widths above already include it. Off-line zeros above the
verified height contribute ≤ 2Σ_{γ>3×10¹²} γ^{−6} < 10⁻⁶⁰: the decision needs no RH.

**Consequence (movement on a route's recorded open core):** Q's selected carrier SURVIVES
its gate; the "failure retires" branch is closed off; Route Q's open core reduces to the
all-degree closure alone. The frontier map's Route Q dossier should be updated accordingly
once promoted.

## Promotion path to stage 2 (explicit, mechanical)

1. Convention audit: read `xiCentralReciprocalSquare`'s literal sign/normalization and
   `analyticTraceMoments`' scaling; re-derive the two power sums in the corpus's exact
   normalization (the ×3.18 margin absorbs any bounded renormalization, but signs must be
   pinned).
2. Replace mpmath zeros by cited verified tables (first 200 ordinates, rigorous enclosures)
   and the density majorant by an explicit N(T) bound (Backlund/Trudgian-type; check
   PNTPlus/corpus for an owned explicit zero-counting bound).
3. Then the decision is a dependency-closed paper theorem; promote and notify the map.

## Companion typing note: the near-line uniformity invariant (D2–T residual)

The D2–T resolution isolated the pair's entire difference as one invariant: uniformity of
the continued-trace ceiling as im z → 0⁺. Typed precisely: for each δ > 0 let C(δ) be the
best ceiling on {δ ≤ im z < 1/2, re z > R}. T's line bound controls C(δ) for every δ with
blow-up as δ → 0; D2 demands sup_δ C(δ) < ∞. The invariant is the divergence class of
C(δ) — by the routes' endpoint equivalences, RH ⟺ C(δ) = O(1); an off-line zero at
displacement β forces C(δ) = ∞ for δ < β. So the invariant is exactly a zero-displacement
detector of Landau type, and the D2–T difference is the classical gap between
"bounded on every compact sub-strip" and "bounded up to the boundary" — recorded as the
pair's typed residual, closing the graph's last annotation.

## Lean status: the gate mechanism is certified; the arithmetic input is not

`GaloisForLFunctions.HTGeometry.DivisorHeightRatioGate` (wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`) replaces the card's 200-zero numerical
argument by the exact structural mechanism, unconditionally:

- `xiCentralAbsMoment n` — the absolute centered reciprocal moments
  `∑_ρ mult(ρ) ‖ρ − 1/2‖^{−2(n+1)}` of the actual xi divisor; `xiCentralAbsMoment_summable`.
- `norm_xiCentralReciprocalMoment_le`, `abs_normalizedPrimeArchMoment_le` — the absolute moments
  dominate the signed corpus moments, through
  `primeArchSourceMoment_eq_xiCentralReciprocalMoment`.
- `xiCentralAbsMoment_succ_le_div` — **height damping**: a lower bound `c` on the centered heights
  gives `absMoment (n+1) ≤ absMoment n / c²`, for every `n`, by one bounded multiplier under the
  sum.  No tail estimate, no zero table, no density majorant.
- `xiCentralAbsMoment_add_le_div` — the iterated form `absMoment (n+k) ≤ absMoment n / c^{2k}`.
- `exists_pos_xiCentralHeightFloor`, `exists_pos_xiCentralAbsMoment_ratio` — such a `c > 0` always
  exists, from local finiteness of the divisor alone; so geometric decay of the absolute moments
  is unconditional, with only the *size* of `c` arithmetic.
- `xiCentralAbsMoment_two_lt_div_of_height`, `normalizedPrimeArchMoment_two_lt_of_height` — **the
  gate**: `9 < c` already forces `absMoment 2 < absMoment 1 / 81`.  The margin the card computes
  numerically as ×2.51 is, structurally, `(γ₁/9)² = (14.134…/9)² = 2.466…`; the numerical work was
  never needed for the mechanism, only for the constant.

All declarations audit to `propext`, `Classical.choice`, `Quot.sound`.

**What is not formalizable here.**  Two arithmetic inputs remain, and both are numerical facts
about the zeta zeros rather than mathematics of the gate:

1. `9 < c`, i.e. the divisor of xi has no point within distance `9` of `1/2`.  Classically this is
   `γ₁ = 14.1347…`; certifying it in Lean is a verified-zero computation (argument principle plus
   explicit bounds on `ξ` along a contour), which the project's working rules exclude.
2. A lower bound on the *signed* moment `normalizedPrimeArchMoment 1`.  The Lean gate above bounds
   the second moment against the *absolute* first moment; the two coincide exactly when every zero
   is on the critical line, so replacing `xiCentralAbsMoment 1` by `normalizedPrimeArchMoment 1`
   unconditionally is not a matter of effort but requires a zero-location input.

The card therefore stays at stage 2: the decision's mathematics is certified, its two numerical
inputs are named and are computations.

## Log

- 2026-08-09 — gate decided (pre-certified ×3.18); identification read in-tree; promotion
  path stated; near-line invariant typed. No Lean.

## PROMOTION EXECUTED (2026-08-09): the dependency-closed paper proof

**Convention audit (item 1) — PASSED.** `xiCentralReciprocalSquare ρ = −((ρ−1/2)⁻¹)²`
(read literally, `CentralReciprocalMoments.lean:62`): at an on-line zero this is +1/γ² > 0,
matching the corpus's positivity theorems; with the germ indexing (iteratedDeriv(2n) ↔
moment n) the identification moment 1 = Σ m_ρ/γ⁴, moment 2 = Σ m_ρ/γ⁶ is exact, both sides
of the gate positive, no sign ambiguity remains.

**Rigorous bounds (items 2–3) — EXECUTED.** Inputs: the three classical ordinate enclosures
γ₁ = 14.1347251417…, γ₂ = 21.0220396387…, γ₃ = 25.0108575801… (rigorously verified since
Backlund; modern verification to height 3×10¹²), and an explicit counting majorant
N(t) ≤ (t/2π)log(t/2π) + 7/8 + 0.112 log t + 0.278 loglog t + 2.510 (Trudgian-type explicit
argument bound; cite Trudgian 2014).

- moment 1 ≥ 1/γ₁⁴ + 1/γ₂⁴ + 1/γ₃⁴ − (off-line slack above 3×10¹², < 10⁻²⁴)
           ≥ 3.27283×10⁻⁵.
- moment 2 ≤ 1/γ₁⁶ + 1/γ₂⁶ + 1/γ₃⁶ + Σ_{γ≥30} γ⁻⁶, with the tail bounded by parts through
  the counting majorant: Σ_{γ≥30}γ⁻⁶ ≤ 6∫₃₀^∞ N(t)t⁻⁷dt ≤ 1.95×10⁻⁸ (certified numerically
  with a generous grid and tail-of-tail term). Total: moment 2 ≤ 1.60601×10⁻⁷.
- Gate threshold: moment 1/81 ≥ 4.04054×10⁻⁷.

**Conclusion: moment 2 < moment 1/81 holds with margin factor ≥ 2.51, unconditionally**
(off-line zeros above the verified height enter both sides below 10⁻²⁴; no RH input).
Everything above is three cited enclosures, one cited explicit counting theorem, and
elementary integration — dependency-closed at paper level. Status upgraded; card moves to
stage 2. Route Q's recorded decision point is settled: the selected carrier SURVIVES, and
Q's open core is the all-degree closure alone.

- 2026-08-11 — the gate mechanism formalized unconditionally as a height-damping law
  (`DivisorHeightRatioGate`); the numerical proof is superseded by `9 < c ⇒ gate`, and the two
  remaining inputs are isolated as verified-zero computations.
