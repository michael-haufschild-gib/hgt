# WD slice theory: near-double law, exposure, detection order, source bands

- **ID:** WD-SLICE-20261010
- **Stage:** 3-formalized
- **Type:** THEOREM FAMILY (all [L], standard axioms)
- **Source:** WD loop `1-in-progress/wd-goal-loop-2026-10-09.md`, rows 24–38

## Statements

Write c_n(t) for the Taylor coefficients of g_t(x) = ξ(½+x+it)ξ(½−x+it), and h_t(σ) = Ξ(t+σ)Ξ(t−σ).
An off-line zero z = γ + iδ of Ξ is *exposed* at t when |γ − t| < |δ|.

1. **Near-double law.** An off-line pair z, z̄ differs from the double critical atom at γ by the exact defect
   (1 + |w|y)² − (1 + wy)(1 + w̄y) = 4βy, with β = δ²/|z−t|⁴. The defect is second order in δ.
   - Reciprocal PF_k: `pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_nearDouble`.
   - Direct slice: `xiSliceCoeff_re_pos_of_offLine_nearDouble`.
2. **Exposure + multiplicity law.** Re c_{2j}(t) > 0 whenever m ≥ j critical copies lie within D of t and
   3jD²·Σ_exposed δ²/|z−t|⁴ ≤ m − j + 1. Pairs inside the cone cost nothing (`xiSliceCoeff_re_pos_of_exposed_nearDouble_card`).
   - Algebra: `HTGeometry.cornerRatio_elemProd_count`, `coeff_mul_prod_pair_ge`.
3. **Obstruction.** ¬RH ⟹ weakly shadowed exposed zeros at some order < max(K, κ log t), near every off-line ordinate
   (`exists_weakly_shadowed_near_offLine_zero`).
4. **Detection order.** At the ordinate γ of an off-line zero:
   - some c_n(γ), n < N, is negative once 2·5^m·e^{4δ²S} < 2^N (`exists_re_xiSliceCoeff_neg_of_offLine_mass`);
   - explicitly, with nearest-other distance r₀: N ≈ 6 + 92δ²(1 + r₀⁻²)(K + log(|γ|+4)) (`exists_re_xiSliceCoeff_neg_of_isolated_offLine`);
   - reciprocal analogue: `exists_not_nonneg_iteratedDeriv_inv_xiHorizontalPair_of_offLine`;
   - general lemma: `HTGeometry.norm_le_re_add_two_mul_tail_of_taylor_nonneg_lt`;
   - mixed classes (ξ(½+iγ) = 0 with order k): some c_n(γ) with 2k ≤ n < 2k + N is negative under the same condition
     (`exists_re_xiSliceCoeff_neg_of_offLine_mass_order`, module `XiSliceMixedClassDetection`).
5. **Smallness.** Shadowing depth j ⟹ |ξ(½+iγ)|² ≤ M(R)(δ/R)^{2j+1}/(1−δ/R) (`re_xiSliceCoeff_zero_le_of_shadowed`).
   This is essentially Jensen's formula.
6. **Source bands (order-23 trace budget).**
   - All-order slice positivity for |t| ≤ 14.18 and Turán (PF_2) for |t| ≤ 13.68.
   - PF_45 at the centre (was 37) and 46 nonnegative reciprocal centre coefficients (was 38).
   - Module: `XiSliceCoeffOrderTwentyThreeBand`.

7. **Husimi positivity (uncertainty form).** For every σ > 0 and height t, e^{σ²x²}·∫G_σ(t−t′)g_{t′}(x)dt′ is the exponential
   transform of the nonnegative Husimi density |V_σ(·,t)|² (`exp_mul_xiSliceHeightAverage_eq`, module `XiSliceHusimiPositivity`).
   Height localization at scale 1/σ costs exactly e^{σ²x²}; this is the bandwidth wall as Heisenberg uncertainty.

8. **Husimi sharpness (no-go for density methods).** The Husimi density vanishes somewhere at every resolution
   (`exists_gaborAmp_eq_zero`), so it is not a strictly positive smoothing of any nonnegative density
   (`not_nonneg_smoothing_eq_husimi`, module `XiSliceHusimiZero`). Below the Husimi constant, WD positivity can only come
   from moment cancellation.

9. **Husimi = backward heat.** The theta source equals the de Bruijn kernel (`thetaCuspFullSource_eq_riemannKernelReal`), and
   B_σ(w) = H_{−1/(2σ²)}(iw/σ²). Husimi zeros are backward-heat zeros, with infinitely many off-axis ones at every σ
   (`husimiZeros_offAxis_infinite`, module `XiSliceHusimiHeatDictionary`).
10. **Euler-blindness of the averaged side.** The source e^{−u²}cos2u satisfies the Husimi identity, has a non-real transform
    zero (F(iπ/2) = 0) and a negative slice coefficient (`exists_not_nonneg_taylorCoeff_gaussCos_slice`, module
    `XiSliceHusimiEulerBlind`).

## Map of WD statements (rows 82–85)
| | averaged | pointwise |
|---|---|---|
| Euler-blind | Husimi family: positivity at the uncertainty cost; information-free about RH [L] | detection/exposure: receivers [L] |
| Euler-using | densities (433/500 slice positivity, horizontal simplicity 0.655) [L] | exclusion only at σ ≥ 1 − c/log t (ZFR); near σ = ½ EMPTY = RH |

Crossing the bottom row needs a positive amplifier of length N > T with a T-scale mean value (the long-mollifier problem,
θ > 1) or, pointwise, the absence of negative resonances of a length-√t quadratic Dirichlet form (Riemann–Siegel form).

## Frontier statement

Low-order slice signs fail only through unshadowed exposed off-line zeros. Zeros with δ²S = O(1) are detected at bounded
order at their ordinate. The order-1 forms are the corpus Laguerre lane (`XiLaguerreSeparation`, `XiLaguerreShadow`).

What remains is source-side, and it sits behind the bandwidth-one Nyquist wall. A pair is an O(δ²) perturbation of a double
critical zero in every functional that depends continuously on ξ. The three source targets therefore reduce as follows:
- |ξ| lower bound: equivalent to zero clustering, by Jensen.
- Ward energy: < 8π is equivalent to RH; finiteness alone would give finitely many off-line zeros.
- Bounded-order positivity at every height: implies a zero-free neighbourhood of the critical line.

Each needs an input beyond the density hypothesis near the line, a mollifier with θ > 1, or averaged HL power savings.

## Gates
- [x] 0 → 1, 1 → 2 (paper proofs in the loop rows)
- [x] 2 → 3 (all items formalized, audited with `#print axioms`, wired into the umbrellas)

## Log
- 2026-10-10 — created from loop rows 24–38.
- 2026-10-10 — row 44: mixed-class detection added.
- 2026-10-11 — row 50: Husimi slice positivity added.
- 2026-10-11 — rows 52/55: all-coefficient form and the Husimi zero no-go added.
- 2026-10-11 — rows 59/81–85: heat dictionary, Euler-blind countermodel, final map added.
- 2026-10-11 — row 106: single-pair shadowing law for the reciprocal slice [L] (`XiReciprocalPairShadowingLaw`): one critical copy at distance d shadows a pair z, z̄ when d²/|t−z|² < √2−1; mixed class shadowed for 10(t−γ)² ≤ 7δ²; threshold ≤ ½. Positive survivor of the row-105 no-go (reciprocal slice is locally blind to mixed classes; the direct slice detects them, item for row 44). Rows 103/104/107: quarter edge is a double wall (Euler edge + convexity edge); density law 1 − (1/2π)[ln(1+2θ)/(2θ) + ln(1+1/(2θ))]; Hall matching criterion (receiver).
- 2026-10-11 — row 109: shadowing threshold sharpened to ½ [L]; mixed class shadowed on the whole exposure window; slice-level sharpness `coeff_one_reciprocalPairModel_neg`.
- 2026-10-11 — row 110: angle criterion and all-height mixed-class blindness of reciprocal coefficients [L] (`coeff_reciprocalPairModel_pos_mixed_all`); the dense-shadowing barrier is sharp.
- 2026-10-11 — row 111: direct-slice detection interval of the mixed triple, |t−γ| < √(2/3)|δ| [L]; complementary to reciprocal blindness (row 110).
- 2026-10-11 — row 115: three-zero dichotomy [L] `reciprocalPairModel_globally_pos_iff` (global reciprocal blindness ⟺ exact mixed class).
- 2026-10-11 — row 116: explicit countermodel [L] (`mixedSextic`, `coeff_mixedSextic_reciprocal_pos`): reciprocal coefficient positivity everywhere does not force real zeros.
- 2026-10-11 — rows 117–150: producer-side closure (Pólya–Schur, axiomatic, exact identities, imports, Landau, multiplicative signs, truncation, integrality, lattice theta, polyharmonic). Constraints (i)–(iv) on any producer recorded in ledger row 150; `DeBruijnHeatNoSlack` [L] formalizes (i).
- 2026-10-11 — rows 151–180: `RiemannKernelMomentsNotMultiplier` [L] (Pólya–Schur closed with CANNOT-497), `XiDirectMixedMultiplicityLaw` [L]; quantifier map (rows 168/169): unconditional inputs are ∃/μ/∀-edge, WD is ∀-centre.
- 2026-10-11 — rows 201–240: `EisensteinSliceLSeries` [L] (slice = completed Eisenstein L-function Λ(½+x, E(·,½+it)) on x > ½); multiplicity m = 9 enlargement [L]. Precise arithmetic target: higher Gross–Zagier over ℚ for the Eisenstein family (rows 224–226).
- 2026-10-11 (rows 260–262): `XiSliceLowestCoeffPositive` (lowest nonvanishing slice coefficient is h(t)² > 0 at every height; local lemma `xiSliceCoeff_lowest_of_factor`) and `XiSliceMixedOrdinateDetectionOrder` (`exists_re_xiSliceCoeff_neg_of_offLine_mass_of_order`: bounded detection order without Ξ(γ) ≠ 0, shifted by twice the order of Ξ at γ). Standard axioms; wired into RHTower.
- 2026-10-11 (row 263): `XiSliceClusterDetectionOrder` — `exists_re_xiSliceCoeff_neg_of_offLine_cluster`: a cluster of k zero copies within ε of the ordinate (containing all copies at γ) delays detection by at most 2k + O(log B), continuously as ε → 0. With the near-double positivity law this pins the detection order at the ordinate. Standard axioms; wired.
- 2026-10-11 (rows 265–267): `RiemannHeatSliceTaylorPositivity` (WD all orders for H_λ at all large heights; RH ⟺ WD for all λ>0), `RiemannHeatSliceEvolution` (∂_λc_n = ½(n+2)(n+1)c_{n+2} − ½∂_t²c_n), `XiSliceHeatTransferPositivity` (unconditional: Σ_k (1/16)^k/k!·(n+2k)!/n!·c_{n+2k}(t) ≥ 0 at every height; RH ⟺ the heated positivity for every λ > 0). Standard axioms; wired.
