# PA: fixed-order large-shift positivity of the calibrated Hausdorff tower (2026-10-17, [L])

Module: `formal/GaloisForLFunctions/RHTower/PrimeArchHausdorffFixedOrderLargeShiftPositivity.lean` (wired into `RHTower.lean`; axioms propext/Classical.choice/Quot.sound).
Card: `docs/drafts/pipeline/3-formalized/pa-hausdorff-fixed-order-large-shift-positivity-2026-10-17.md`. STATUS: MUST-1575.

Main theorem `exists_forall_scaledHausdorffMomentDifference_nonneg (k) : ∃ r₀, ∀ r ≥ r₀, 0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius normalizedPrimeArchMoment k r` — unconditional.
Corollaries: `riemannHypothesis_iff_forall_lt_shiftThreshold_nonneg` (RH ⟺ positivity for `r < primeArchHausdorffShiftThreshold k`, all k); `eventually_bernsteinCoefficient_endpoint_nonneg` (fixed Bernstein index i, all large degrees).

Mechanism: threshold Λ = KR/r, K = 10(k+1)+20, T = √(r/(KR)). Atoms Re x ≤ Λ ↔ zeros of ordinate ≥ 0.97T, tilt ≤ 2/|γ| → phase budget ≤ 1/20 → Re term ≥ ½|term|. Atoms Re x > Λ: ordinate < T, count ≤ 0.33 T log T (Riemann–von Mangoldt, `exists_xiSymmetricMass_close`), each ≤ (4.1Λ)^(k+1) R^r e^{−0.99K}. Band (1.2T,1.4T]: ≥ 0.04 T log T atoms, each ≥ ½(0.49Λ)^(k+1) R^r e^{−3K/4}. e^{2.4} ≥ 9, e^{4.8} ≥ 18 close the margin.

Insight: large shifts probe HIGH zeros (Weyl regime) where positivity is a density statement; RH content of the Hausdorff tower is confined to bounded shifts r < r₀(k) per order. Asymmetry: fixed shift / large order is governed by the LOWEST zero and is not provable this way.

Reusable lemmas in the module: `norm_real_sub_le_of_abs_im_le` (‖R − x‖ ≤ R − (1−δ)λ), `half_norm_le_re_of_small_phase`, `one_sub_pow_le_exp_neg`, `exp_neg_div_le_one_sub_pow`, `pow_mul_exp_neg_antitone_beyond`, `xiSymmetricMass_zero`, `card_le_xiSymmetricMass_of_forall_abs_im_le`, `card_xiCopiesBand_eq_real`, per-atom geometry (`xiZeroCopyReciprocalSquare_re/_im`, `norm_xiZeroCopyReciprocalSquare`, tilt bounds), `tsum_nonneg_of_band_dominates`.
