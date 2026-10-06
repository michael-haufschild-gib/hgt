# Route Q's ratio gate: DECIDED (holds) — proved unconditionally in Lean, no zero data

- **ID:** ULF-MECH-5
- **Stage:** 3-formalized
  rigorous three-zero + explicit-tail proof appended below)
- **Type:** THEOREM (Lean)
  source inequality normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81. Failure
  retires selected carrier; success still needs all-degree closure.")
- **Status:** [GATE HOLDS — PROVED, MARGIN ×2.51 RIGOROUS / ×3.18 NUMERICAL] [CONVENTION AUDIT PASSED] [NOT RH]
  [LEAN-PROVED]

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

**Both inputs are now proved (2026-10-06), without any zero computation.**  The strip-edge
sum rules of the ξ divisor replace the verified-zero inputs:

1. *Height floor.*  With `w_ρ = 1/(ρ(1−ρ))` and `Λ₀ = completedRiemannZeta₀`,
   `Σ_ρ w_ρ = 2Λ₀(1)` and `Σ_ρ w_ρ² = 2(Λ₀(1)² − 2Λ₀'(1))` (Hadamard jets of ξ at `s = 1`).
   Every term has `Re w² ≥ (A−1)/(A(A+1)²) ≥ 0`, `A = 1/4 + (Im ρ)² − (Re ρ − 1/2)²`.
   `Λ₀(1) = 1 + (γ − log 4π)/2 ≤ 93/4000` from `γ ≤ H₁₃ − log(27/2)` (half-shifted harmonic
   bound) and artanh floors for `log 2, log 3, log(π/3)`; `Re Λ₀'(1) ≥ 111/500000` from the
   theta Mellin form `Λ₀'(1) = ¼∫₁^∞ (x^{−1/2} − x^{−1}) log x (θ(x) − 1) dx`, `θ − 1 ≥ 2e^{−πx}`
   and `(x^{−1/2} − x^{−1}) log x ≥ (2/5)(x−1)²e^{−9(x−1)/8}`.  So `Σ Re w² ≤ 2/8000`, each
   reflection pair carries `Re w² ≤ 1/8000`, and the cubic `A(A+1)² < 8000(A−1)` on `[32, 83]`
   gives `(Im ρ)² > 331/4` for every zero: no zero of ξ has `|Im ρ| ≤ 9.09`, hence
   `9 < ‖ρ − 1/2‖`.
2. *Signed moment.*  Above that floor `81|a|² < Re a⁴` for every copy `a = (ρ − 1/2)(−i)`,
   i.e. `Re a⁻⁶ < Re a⁻⁴/81` termwise; the divisor is nonempty (otherwise `Λ₀'(1) = 0`), so
   summing gives `normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81` directly for
   the signed moments.

The mpmath enclosures and the three-zero + counting-majorant proof above are superseded: the
decision is a theorem about classical constants and the theta function alone.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.HalfShiftHarmonicEulerBound`, `GaloisForLFunctions.RHTower.XiStripEdgeSquaredWeightSum`, `GaloisForLFunctions.RHTower.CompletedZetaStripEdgeJetBounds`, `GaloisForLFunctions.RHTower.XiStripEdgeHeightFloorRatioGate`, `GaloisForLFunctions.HTGeometry.DivisorHeightRatioGate`, `GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.HalfShiftHarmonicEulerBound` (the half-shifted harmonic
bound `γ ≤ H_n − log(n + 1/2)` and artanh logarithm floors),
`GaloisForLFunctions.RHTower.XiStripEdgeSquaredWeightSum` (the two strip-edge sum rules of the ξ
divisor), `GaloisForLFunctions.RHTower.CompletedZetaStripEdgeJetBounds` (certified bounds on
`Λ₀(1)` and `Λ₀'(1)` from classical constants and the theta Mellin representation) and
`GaloisForLFunctions.RHTower.XiStripEdgeHeightFloorRatioGate` (height floor and the signed gate),
together with the existing gate mechanism `GaloisForLFunctions.HTGeometry.DivisorHeightRatioGate`
and the moment identification of `GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm`.  All
declarations live in namespace `RHTower` except the `GaloisForLFunctions.HTGeometry` ones.  The
proof uses no zero of ζ, no zero table and no counting majorant: the card's numerical route
(mpmath enclosures, three ordinate enclosures, explicit `N(T)`) is replaced by the strip-edge sum
rules.

| Claim | Lean declaration |
|-|-|
| identification: `normalizedPrimeArchMoment n` is the centred reciprocal divisor moment `Σ_ρ m_ρ (−(ρ−1/2)⁻²)^{n+1}`, a sum of real parts over multiplicity copies | `primeArchSourceMoment_eq_xiCentralReciprocalMoment`, `tsum_xiZeroCopyReciprocalSquare_pow`, `normalizedPrimeArchMoment_eq_tsum_re` |
| convention audit: `xiCentralReciprocalSquare ρ = −((ρ−1/2)⁻¹)²`, positive real `1/γ²` at an on-line zero; moment 1 ↔ `Σ z⁻⁴`, moment 2 ↔ `Σ −z⁻⁶` | `xiCentralReciprocalSquare`, `xiCentralReciprocalSquare_pos_real_of_re_eq_half`, `xiZeroCopyReciprocalSquare_eq`, `xiZeroCopy_gate_term_lt` |
| sum rules at the strip edge: `Σ_ρ 1/(ρ(1−ρ)) = 2Λ₀(1)`, `Σ_ρ 1/(ρ(1−ρ))² = 2(Λ₀(1)² − 2Λ₀'(1))`, `(ξ'/ξ)'(1) = 2Λ₀(1) + 2Λ₀'(1) − Λ₀(1)²` | `hasSum_xiStripEdgeWeight`, `hasSum_xiStripEdgeWeight_sq`, `deriv_logDeriv_xi_one_eq_completedZeta₀`, `hasDerivAt_deriv_xi_one`, `xiStripEdgeWeight_sq_eq` |
| `Λ₀(1) = 1 + (γ − log 4π)/2 ≤ 93/4000`, via `γ ≤ H₁₃ − log(27/2)` | `completedRiemannZeta₀_one_eq_ofReal`, `completedRiemannZeta₀_one_re_le`, `eulerMascheroniConstant_le_harmonic_sub_log_add_half`, `antitone_harmonic_sub_log_add_half`, `log_three_ge_artanh`, `two_mul_sub_one_div_add_one_le_log` |
| `Λ₀'(1) = ¼∫₁^∞ (x^{−1/2} − x^{−1}) log x (θ(x) − 1) dx ≥ (2/5)e^{−π}/(π+9/8)³ ≥ 111/500000` | `hasDerivAt_completedRiemannZeta₀_one_mellin`, `mellin_log_f_modif_half_eq`, `integral_stripEdgeLogThetaIntegrand_eq`, `logWeight_floor`, `integral_stripEdgeComparison`, `completedRiemannZeta₀_deriv_one_re_ge`, `completedRiemannZeta₀_deriv_one_re_ge_num`, `exp_pi_le_twentyThree_fifteen` |
| per-copy weight: `Re w > 0`, `Re w² ≥ (A−1)/(A(A+1)²) ≥ 0`; budget `Σ Re w² ≤ 2/8000`, each reflection pair `Re w² ≤ 1/8000` | `xiStripEdgeWeight_re_pos`, `xiStripEdgeWeight_sq_re_ge`, `xiStripEdgeWeight_sq_re_nonneg`, `completedRiemannZeta₀_one_re_nonneg`, `hasSum_xiStripEdgeWeight_sq_re`, `stripEdgeBudget_le`, `xiStripEdgeWeight_sq_re_le` |
| the height input `9 < c` of the gate mechanism: every zero has `(Im ρ)² > 331/4`, so `9 < ‖ρ − 1/2‖` | `xiSpectralPoint_re_sq_gt_floor`, `xi_zero_im_sq_gt_floor`, `nine_lt_norm_sub_half_of_xi_zero`, `stripEdge_cubic_lt` |
| gate mechanism: height damping `absMoment(n+1) ≤ absMoment n / c²` and `9 < c ⇒ absMoment 2 < absMoment 1/81` | `xiCentralAbsMoment_succ_le_div`, `xiCentralAbsMoment_two_lt_div_of_height`, `normalizedPrimeArchMoment_two_lt_of_height` |
| the signed input: above the floor `Re a⁻⁶ < Re a⁻⁴/81` termwise; the divisor is nonempty | `xiZeroCopy_gate_term_lt`, `xiZeroCopy_nonempty` |
| **the decision**: `normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81`, unconditionally (no RH) | `normalizedPrimeArchMoment_two_lt_one_div_eightyOne` |

The numerical enclosures of the two power sums, the margin factors ×3.18 / ×2.51, the cited
ordinate enclosures and the Trudgian-type majorant belonged to the superseded numerical proof and
are not used.  The companion typing note on the near-line uniformity invariant (D2–T residual)
restates endpoint equivalences of other routes and is commentary, as is the route-level
consequence for Route Q's open core.

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
- 2026-10-06 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
