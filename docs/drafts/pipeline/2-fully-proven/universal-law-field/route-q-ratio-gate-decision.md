# Route Q's ratio gate: DECIDED (holds, margin ×3.18) — pre-certified, rigorization path open

- **ID:** ULF-MECH-5
- **Stage:** 2-fully-proven (promotion executed 2026-08-09: convention audit passed;
  rigorous three-zero + explicit-tail proof appended below)
- **Type:** DECISION of a recorded frontier open-core alternative (map, Route Q: "Decide
  source inequality normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81. Failure
  retires selected carrier; success still needs all-degree closure.")
- **Status:** [GATE HOLDS — PROVED, MARGIN ×2.51 RIGOROUS / ×3.18 NUMERICAL] [CONVENTION AUDIT PASSED] [NOT RH]
  [NO LEAN — directive; mpmath pre-certification per project rules]

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
