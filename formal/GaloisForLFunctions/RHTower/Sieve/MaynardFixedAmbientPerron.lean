import GaloisForLFunctions.RHTower.Sieve.MaynardAggregateSelection
import GaloisForLFunctions.RHTower.Sieve.MaynardMellinScaleCovariance
import GaloisForLFunctions.RHTower.Sieve.MaynardNormalizedReferenceTargetPerron
import GaloisForLFunctions.RHTower.Sieve.MaynardZeroReserveSupportNull

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

private theorem arithmeticFunction_sum_apply_full
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

theorem upperSupported_heathBrownFiniteCompressedPacket
    (L X k : ℕ) :
    UpperSupported (heathBrownFiniteCompressedPacket L X k)
      ((L + 1) ^ k * (X + 1) ^ k) := by
  rw [heathBrownFiniteCompressedPacket_eq_sum_terms]
  intro n hn
  have hexists : ∃ m ∈ Finset.range k, heathBrownFiniteTerm L X k m n ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    rw [arithmeticFunction_sum_apply_full]
    exact Finset.sum_eq_zero fun m hm => h m hm
  obtain ⟨m, hm, hmn⟩ := hexists
  have hm' : m < k := Finset.mem_range.mp hm
  have hmem := upperSupported_heathBrownFiniteTerm L X k m hm' n hmn
  refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hmem).1, ?_⟩
  have hLbase : L ^ (k - m) ≤ (L + 1) ^ (k - m) :=
    pow_le_pow_left₀ (Nat.zero_le L) (by omega) (k - m)
  have hLexp : (L + 1) ^ (k - m) ≤ (L + 1) ^ k :=
    pow_le_pow_right₀ (by omega) (Nat.sub_le k m)
  have hXbase : X ^ (k - m) ≤ (X + 1) ^ (k - m) :=
    pow_le_pow_left₀ (Nat.zero_le X) (by omega) (k - m)
  have hXexp : (X + 1) ^ (k - m) ≤ (X + 1) ^ k :=
    pow_le_pow_right₀ (by omega) (Nat.sub_le k m)
  exact (Finset.mem_Icc.mp hmem).2.trans
    (Nat.mul_le_mul (hLbase.trans hLexp) (hXbase.trans hXexp))

theorem integrable_heathBrownDyadicAggregate_mul_mellin_smoothWeight
    (L X k : ℕ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hint := integrable_LSeries_mul_mellin_smoothWeight_of_upperSupported
    (upperSupported_heathBrownFiniteCompressedPacket L X k) hN hH hsigma
  refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
  change LSeries (complexCoeff (heathBrownFiniteCompressedPacket L X k))
      ((sigma : ℂ) + (y : ℝ) * I) * _ =
    heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) * _
  rw [LSeries_heathBrownFiniteCompressedPacket_eq_sum_dyadicProducts,
    heathBrownDyadicAggregate]

theorem integrable_heathBrownDyadicAggregate_mul_routeTNormalizedMellin
    (L X k : ℕ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hint := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownFiniteCompressedPacket L X k) hN hH hsigma
  refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
  change LSeries (complexCoeff (heathBrownFiniteCompressedPacket L X k))
      ((sigma : ℂ) + (y : ℝ) * I) * _ =
    heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) * _
  rw [LSeries_heathBrownFiniteCompressedPacket_eq_sum_dyadicProducts,
    heathBrownDyadicAggregate]

theorem smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral_fullAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • ((H : ℂ)⁻¹ *
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
      ∫ y : ℝ,
        heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I) := by
  have hraw := tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownDyadicAggregate
    L X k hXL hN hH hsupport hsigma
  dsimp only at hraw
  have hplus := integrable_heathBrownDyadicAggregate_mul_mellin_smoothWeight
    L X k (N := N + H) (H := H) (sigma := sigma) (by linarith) hH (by linarith)
  have hbase := integrable_heathBrownDyadicAggregate_mul_mellin_smoothWeight
    L X k (N := N) (H := H) (sigma := sigma) hN hH (by linarith)
  have hcombine :
      (∫ y : ℝ, heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) -
        ∫ y : ℝ, heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) =
        ∫ y : ℝ, heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
    rw [← integral_sub hplus hbase]
    apply integral_congr_ae
    filter_upwards with y
    rw [mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
      linarith)]
    ring
  have hraw' :
      (2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ, heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
    rw [← hcombine]
    simpa only [routeTSmoothWindowWeight, Complex.ofReal_sub,
      heathBrownDyadicAggregate] using hraw
  calc
    (2 * Real.pi : ℝ) • ((H : ℂ)⁻¹ *
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
        (H : ℂ)⁻¹ * ((2 * Real.pi : ℝ) •
          (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) := by
      exact (mul_smul_comm (2 * Real.pi : ℝ) (H : ℂ)⁻¹
        (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))).symm
    _ = (H : ℂ)⁻¹ * ∫ y : ℝ,
        heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by rw [hraw']
    _ = ∫ y : ℝ,
        heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [routeTNormalizedSmoothWindowMellin]
      ring

theorem smul_normalized_reference_sub_target_vonMangoldt_eq_integral_fullAggregate_defect
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {N H R sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) •
        ((R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
          (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
      ∫ y : ℝ,
        heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I)) := by
  have href := smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral_fullAggregate
    L X k hXL hN hR hsupportR hsigma
  have htarget := smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral_fullAggregate
    L X k hXL hN hH hsupportH hsigma
  have hintR := integrable_heathBrownDyadicAggregate_mul_routeTNormalizedMellin
    L X k hN hR (by linarith)
  have hintH := integrable_heathBrownDyadicAggregate_mul_routeTNormalizedMellin
    L X k hN hH (by linarith)
  calc
    (2 * Real.pi : ℝ) •
        ((R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
          (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
      (2 * Real.pi : ℝ) • ((R : ℂ)⁻¹ *
          (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ))) -
        (2 * Real.pi : ℝ) • ((H : ℂ)⁻¹ *
          (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) := by rw [smul_sub]
    _ = (∫ y : ℝ, heathBrownDyadicAggregate L X k
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N R ((sigma : ℂ) + (y : ℝ) * I)) -
      ∫ y : ℝ, heathBrownDyadicAggregate L X k
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I) := by rw [href, htarget]
    _ = _ := by
      rw [← integral_sub hintR hintH]
      apply integral_congr_ae
      filter_upwards with y
      ring

/-- Exact fixed-ambient outer formula.  Once base and widths vary proportionally, all physical
dependence is the single Mellin character `lambda^(s-1)`; the full Heath--Brown aggregate and
relative kernel defect remain fixed. -/
theorem smul_scaled_normalized_reference_sub_target_vonMangoldt_eq_integral_fullAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {lambda N H R sigma : ℝ}
    (hlambda : 0 < lambda) (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hsupportH : lambda * N + 2 * (lambda * H) ≤ X)
    (hsupportR : lambda * N + 2 * (lambda * R) ≤ X)
    (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) •
        (((lambda * R : ℝ) : ℂ)⁻¹ *
            (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((routeTSmoothWindowWeight (lambda * N) (lambda * R)
                (n : ℝ) : ℝ) : ℂ)) -
          (((lambda * H : ℝ) : ℂ)⁻¹ *
            (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((routeTSmoothWindowWeight (lambda * N) (lambda * H)
                (n : ℝ) : ℝ) : ℂ)))) =
      ∫ y : ℝ,
        heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          ((lambda : ℂ) ^ (((sigma : ℂ) + (y : ℝ) * I) - 1) *
            (routeTNormalizedSmoothWindowMellin N R
                ((sigma : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((sigma : ℂ) + (y : ℝ) * I))) := by
  have hfull :=
    smul_normalized_reference_sub_target_vonMangoldt_eq_integral_fullAggregate_defect
      L X k hXL (N := lambda * N) (H := lambda * H) (R := lambda * R)
        (sigma := sigma) (mul_pos hlambda hN) (mul_pos hlambda hH)
        (mul_pos hlambda hR) hsupportH hsupportR hsigma
  calc
    (2 * Real.pi : ℝ) •
        (((lambda * R : ℝ) : ℂ)⁻¹ *
            (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((routeTSmoothWindowWeight (lambda * N) (lambda * R)
                (n : ℝ) : ℝ) : ℂ)) -
          (((lambda * H : ℝ) : ℂ)⁻¹ *
            (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((routeTSmoothWindowWeight (lambda * N) (lambda * H)
                (n : ℝ) : ℝ) : ℂ)))) =
      ∫ y : ℝ,
        heathBrownDyadicAggregate L X k ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
              ((sigma : ℂ) + (y : ℝ) * I)) := hfull
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [routeTNormalizedSmoothWindowMellin_defect_mul_scale
        lambda N R H ((sigma : ℂ) + (y : ℝ) * I) hlambda hR hH]

end RHTower.Sieve

