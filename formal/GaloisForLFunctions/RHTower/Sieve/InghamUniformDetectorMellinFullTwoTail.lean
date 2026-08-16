import GaloisForLFunctions.HTGeometry.PowerTailBochnerBoundInward
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfPoleContour
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSeriesBound

open Complex Filter Topology intervalIntegral
open MeasureTheory Set
open ArithmeticFunction
open GaloisForLFunctions.HTGeometry
open RHTower RHTower.Sieve

namespace RHTower.Sieve

noncomputable section

theorem norm_integral_sub_interval_le_powerTail
    {f : ℝ → ℂ} (hf : Integrable f) {C q T : ℝ}
    (hC : 0 ≤ C) (hq : 1 < q) (hT : 0 < T)
    (hbound : ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ C * |t| ^ (-q)) :
    ‖(∫ t : ℝ, f t) - ∫ t in (-T)..T, f t‖ ≤
      2 * C * (T ^ (1 - q) / (q - 1)) := by
  have hnegT : -T ≤ T := by linarith
  have hinterval : (∫ t in (-T)..T, f t) = ∫ t in Icc (-T) T, f t := by
    rw [intervalIntegral.integral_of_le hnegT,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hsplit := MeasureTheory.integral_add_compl
    (s := Icc (-T) T) measurableSet_Icc hf
  have hdiff : (∫ t : ℝ, f t) - ∫ t in (-T)..T, f t =
      ∫ t in (Icc (-T) T)ᶜ, f t := by
    rw [hinterval]
    rw [← hsplit]
    abel
  have hcompl : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
    ext t
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  have hleft : ‖∫ t in Iio (-T), f t‖ ≤
      C * (T ^ (1 - q) / (q - 1)) := by
    rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
    simpa only [neg_neg] using
      (norm_integral_Iic_le_powerTail (f := f) hq (by linarith : -T < 0)
        (fun t ht => hbound t (by
          rw [mem_Iic] at ht
          have : T ≤ -t := by linarith
          rw [abs_of_nonpos (by linarith)]
          exact this)))
  have hright : ‖∫ t in Ioi T, f t‖ ≤
      C * (T ^ (1 - q) / (q - 1)) := by
    exact norm_integral_Ioi_le_powerTail (f := f) hq hT
      (fun t ht => hbound t (by
        rw [mem_Ioi] at ht
        rw [abs_of_pos (hT.trans ht)]
        exact ht.le))
  have hunion : (∫ t in Iio (-T) ∪ Ioi T, f t) =
      (∫ t in Iio (-T), f t) + ∫ t in Ioi T, f t := by
    rw [setIntegral_union]
    · rw [Set.disjoint_left]
      intro t htleft htright
      change t < -T at htleft
      change T < t at htright
      linarith
    · exact measurableSet_Ioi
    · exact hf.integrableOn
    · exact hf.integrableOn
  rw [hdiff, hcompl, hunion]
  calc
    ‖(∫ t in Iio (-T), f t) + ∫ t in Ioi T, f t‖ ≤
        ‖∫ t in Iio (-T), f t‖ + ‖∫ t in Ioi T, f t‖ := norm_add_le _ _
    _ ≤ C * (T ^ (1 - q) / (q - 1)) +
          C * (T ^ (1 - q) / (q - 1)) := add_le_add hleft hright
    _ = 2 * C * (T ^ (1 - q) / (q - 1)) := by ring

theorem norm_routeT_two_vonMangoldt_full_sub_interval_le_natOrder
    {N H T C : ℝ} (hN : 0 < N) (hH : 0 < H) (hT : 0 < T)
    {j : ℕ} (hj : 2 ≤ j) (hC : 0 ≤ C)
    (hK : ∀ t : ℝ, 0 < |t| →
      |t| ^ j * ‖routeTNormalizedSmoothWindowMellin N H
        (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C) :
    ‖(∫ t : ℝ,
        (-(deriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          routeTNormalizedSmoothWindowMellin N H
            (((2 : ℝ) : ℂ) + (t : ℂ) * I)) -
      ∫ t in (-T)..T,
        (-(deriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          routeTNormalizedSmoothWindowMellin N H
            (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      16 * C * (T ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
  let F : ℝ → ℂ := fun t =>
    -(deriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
      riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)
  let K : ℝ → ℂ := fun t =>
    routeTNormalizedSmoothWindowMellin N H (((2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hFcont : Continuous F := by
    simpa only [F] using (continuous_neg_logDeriv_line (d := 2) (by norm_num))
  have hKcont : Continuous K := by
    simpa only [K] using continuous_routeTNormalizedSmoothWindowMellin_line
      hN hH (by norm_num : (0 : ℝ) < 2)
  have hKint : Integrable K := by
    have hplus := verticalIntegrable_mellin_smoothWeight
      (N := N + H) (H := H) (σ := 2) (by linarith) hH (by norm_num)
    have hbase := verticalIntegrable_mellin_smoothWeight
      (N := N) (H := H) (σ := 2) hN hH (by norm_num)
    refine ((hplus.sub hbase).const_mul ((H : ℂ)⁻¹)).congr ?_
    filter_upwards with t
    dsimp only [K]
    simp only [Pi.sub_apply]
    rw [routeTNormalizedSmoothWindowMellin,
      mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by norm_num)]
  have hFbound : ∀ t : ℝ, ‖F t‖ ≤ 8 := by
    intro t
    calc
      ‖F t‖ ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
        simpa only [F] using norm_neg_logDeriv_le_line
          (d := 2) (y := t) (by norm_num)
      _ ≤ 8 := by
        have h := tsum_vonMangoldt_rpow_neg_le
          (d := 2) (by norm_num) (by norm_num)
        convert h using 1 <;> norm_num
  have hFKint : Integrable (fun t => F t * K t) :=
    hKint.bdd_mul hFcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hFbound)
  have hjR : (1 : ℝ) < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hj)
  have htail : ∀ t : ℝ, T ≤ |t| →
      ‖F t * K t‖ ≤ (8 * C) * |t| ^ (-(j : ℝ)) := by
    intro t ht
    have ht0 : 0 < |t| := hT.trans_le ht
    have hpow0 : 0 < |t| ^ j := pow_pos ht0 j
    have hK' : ‖K t‖ ≤ C * |t| ^ (-(j : ℝ)) := by
      have hraw : |t| ^ j * ‖K t‖ ≤ C := by simpa only [K] using hK t ht0
      calc
        ‖K t‖ = (|t| ^ j * ‖K t‖) / |t| ^ j := by field_simp
        _ ≤ C / |t| ^ j := div_le_div_of_nonneg_right hraw hpow0.le
        _ = C * |t| ^ (-(j : ℝ)) := by
          rw [Real.rpow_neg (abs_nonneg t), Real.rpow_natCast]
          ring
    rw [norm_mul]
    calc
      ‖F t‖ * ‖K t‖ ≤ 8 * (C * |t| ^ (-(j : ℝ))) :=
        mul_le_mul (hFbound t) hK' (norm_nonneg _) (by norm_num)
      _ = (8 * C) * |t| ^ (-(j : ℝ)) := by ring
  simpa only [F, K, show 2 * (8 * C) = 16 * C by ring] using
    (norm_integral_sub_interval_le_powerTail hFKint
      (mul_nonneg (by norm_num) hC) hjR hT htail)

theorem exists_routeTBufferedMellin_two_natOrder_frequency_bound (j : ℕ) (hj : 1 ≤ j) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {X : ℕ} {t : ℝ}, 3 ≤ X → 0 < |t| →
      |t| ^ j * ‖routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X)
          (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        D * inghamRouteTMellinPhysicalCenter X *
          inghamRouteTMellinBufferedFrequency X ^ j := by
  obtain ⟨C, hC, hraw⟩ := exists_bound_routeTNormalizedSmoothWindowMellin_line j
  let D : ℝ := C * (3 : ℝ) ^ (j + 1)
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro X t hX ht
  have hX1 : 1 ≤ X := by omega
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let H : ℝ := inghamRouteTMellinBufferedPhysicalWidth X
  let F : ℝ := inghamRouteTMellinBufferedFrequency X
  have hN : 0 < N := inghamRouteTMellinPhysicalCenter_pos hX1
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hF : 0 < F := inghamRouteTMellinBufferedFrequency_pos hX1
  have hHN : H ≤ N := inghamRouteTMellinBufferedPhysicalWidth_le_center hX1
  have hj0R : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hbound := hraw 2 N H t hN hH hHN hj (by linarith) ht
  have hscale : C * (3 * N) ^ ((2 : ℝ) + (j : ℝ) - 1) / H ^ j =
      D * N * F ^ j := by
    have hexp : (2 : ℝ) + (j : ℝ) - 1 = ((j + 1 : ℕ) : ℝ) := by
      norm_num
      ring
    rw [hexp, Real.rpow_natCast, mul_pow, show H = N / F by rfl, div_pow]
    dsimp only [D]
    field_simp [hN.ne', hF.ne']
    ring
  simpa only [N, H, F, hscale] using hbound

def inghamRouteTBufferedFullTwoVonMangoldtEdge (X : ℕ) : ℂ :=
  ∫ t : ℝ,
    (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        (((2 : ℝ) : ℂ) + (t : ℂ) * I)

theorem exists_norm_inghamRouteTBufferedFullTwoVonMangoldtEdge_sub_selected_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {X : ℕ}, 12 ≤ X →
      ‖inghamRouteTBufferedFullTwoVonMangoldtEdge X -
          inghamRouteTBufferedSelectedTwoVonMangoldtEdge X‖ ≤
        16 * (D * inghamRouteTMellinPhysicalCenter X *
            inghamRouteTMellinBufferedFrequency X ^ 5000) *
          (inghamRouteTBufferedNegativeHalfHeight X ^ (1 - (5000 : ℝ)) /
            ((5000 : ℝ) - 1)) := by
  obtain ⟨D, hD, hfrequency⟩ :=
    exists_routeTBufferedMellin_two_natOrder_frequency_bound 5000 (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro X hX
  have hX3 : 3 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let H : ℝ := inghamRouteTMellinBufferedPhysicalWidth X
  let F : ℝ := inghamRouteTMellinBufferedFrequency X
  let T : ℝ := inghamRouteTBufferedNegativeHalfHeight X
  have hN : 0 < N := inghamRouteTMellinPhysicalCenter_pos hX1
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hF : 0 < F := inghamRouteTMellinBufferedFrequency_pos hX1
  have hT : 0 < T := by
    have hspec := (inghamRouteTBufferedNegativeHalfHeight_spec hX).1
    have hXcast : (12 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hlow : (X : ℝ) - 3 < inghamRouteTBufferedNegativeHalfHeight X := hspec.1
    dsimp only [T]
    linarith
  have hK : ∀ t : ℝ, 0 < |t| →
      |t| ^ 5000 * ‖routeTNormalizedSmoothWindowMellin N H
        (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ D * N * F ^ 5000 := by
    intro t ht
    simpa only [N, H, F] using hfrequency (X := X) (t := t) hX3 ht
  have hlog := norm_routeT_two_vonMangoldt_full_sub_interval_le_natOrder
    hN hH hT (j := 5000) (by norm_num) (by positivity) hK
  have hpoint (t : ℝ) :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) =
        -(deriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
          riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    exact tsum_vonMangoldt_cpow_eq (by norm_num)
  have hfull : inghamRouteTBufferedFullTwoVonMangoldtEdge X =
      ∫ t : ℝ,
        (-(deriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          routeTNormalizedSmoothWindowMellin N H
            (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [inghamRouteTBufferedFullTwoVonMangoldtEdge]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [hpoint t]
  have hpointC (t : ℝ) :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))) =
        -(deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)) /
          riemannZeta ((2 : ℂ) + (t : ℂ) * I) := by
    exact tsum_vonMangoldt_cpow_eq (by norm_num)
  have hselectedRaw : inghamRouteTBufferedSelectedTwoVonMangoldtEdge X =
      ∫ t in (-T)..T,
        (-(deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I)) /
            riemannZeta ((2 : ℂ) + (t : ℂ) * I)) *
          routeTNormalizedSmoothWindowMellin N H
            ((2 : ℂ) + (t : ℂ) * I) := by
    rw [inghamRouteTBufferedSelectedTwoVonMangoldtEdge]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [N, H]
    rw [hpointC t]
  have hselected : inghamRouteTBufferedSelectedTwoVonMangoldtEdge X =
      ∫ t in (-T)..T,
        (-(deriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          routeTNormalizedSmoothWindowMellin N H
            (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    simpa using hselectedRaw
  rw [hfull, hselected]
  dsimp only [N, H, F, T] at hlog ⊢
  convert hlog using 1 <;> norm_num

theorem inghamRouteTMellinCenter_mul_bufferedFrequency_pow_5000_div_height_pow_4999
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinPhysicalCenter X *
        inghamRouteTMellinBufferedFrequency X ^ 5000 /
          (X : ℝ) ^ 4999 =
      (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  unfold inghamRouteTMellinPhysicalCenter inghamRouteTMellinBufferedFrequency
    inghamRouteTPhysicalScaleExponent inghamRouteTMellinBufferedFrequencyExponent
  rw [← Real.rpow_natCast, ← Real.rpow_mul hXR.le,
    ← Real.rpow_add hXR, ← Real.rpow_natCast, ← Real.rpow_sub hXR]
  congr 1
  norm_num

theorem halfHeight_rpow_neg_4999 {X : ℕ} (hX : 1 ≤ X) :
    ((X : ℝ) / 2) ^ (-(4999 : ℝ)) =
      (2 : ℝ) ^ 4999 / (X : ℝ) ^ 4999 := by
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  rw [show (-(4999 : ℝ)) = -((4999 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (div_nonneg hXR.le (by norm_num)), Real.rpow_natCast, div_pow]
  field_simp [hXR.ne']

theorem inghamRouteTMellinCenter_mul_bufferedFrequency_pow_5000_mul_halfHeight_rpow_neg_4999
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinPhysicalCenter X *
        inghamRouteTMellinBufferedFrequency X ^ 5000 *
          ((X : ℝ) / 2) ^ (-(4999 : ℝ)) =
      (2 : ℝ) ^ 4999 * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  rw [halfHeight_rpow_neg_4999 hX]
  calc
    inghamRouteTMellinPhysicalCenter X *
          inghamRouteTMellinBufferedFrequency X ^ 5000 *
            ((2 : ℝ) ^ 4999 / (X : ℝ) ^ 4999) =
        (2 : ℝ) ^ 4999 *
          (inghamRouteTMellinPhysicalCenter X *
            inghamRouteTMellinBufferedFrequency X ^ 5000 /
              (X : ℝ) ^ 4999) := by ring
    _ = _ := by
      rw [inghamRouteTMellinCenter_mul_bufferedFrequency_pow_5000_div_height_pow_4999 hX]

theorem exists_norm_inghamRouteTBufferedFullTwoVonMangoldtEdge_sub_selected_rpow_le :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {X : ℕ}, 12 ≤ X →
      ‖inghamRouteTBufferedFullTwoVonMangoldtEdge X -
          inghamRouteTBufferedSelectedTwoVonMangoldtEdge X‖ ≤
        E * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_norm_inghamRouteTBufferedFullTwoVonMangoldtEdge_sub_selected_le
  let E : ℝ := 16 * D * (2 : ℝ) ^ 4999 / 4999
  refine ⟨E, by dsimp only [E]; positivity, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := by omega
  have hXR : (0 : ℝ) < X := by positivity
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let F : ℝ := inghamRouteTMellinBufferedFrequency X
  let T : ℝ := inghamRouteTBufferedNegativeHalfHeight X
  have hTspec := (inghamRouteTBufferedNegativeHalfHeight_spec hX).1
  have hXcast : (12 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hTlow : (X : ℝ) / 2 ≤ T := by
    dsimp only [T]
    linarith [hTspec.1]
  have hhalf : 0 < (X : ℝ) / 2 := by positivity
  have hN0 : 0 ≤ N := by
    dsimp only [N]
    exact (inghamRouteTMellinPhysicalCenter_pos hX1).le
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact (inghamRouteTMellinBufferedFrequency_pos hX1).le
  have hpow : T ^ (1 - (5000 : ℝ)) ≤
      ((X : ℝ) / 2) ^ (1 - (5000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hhalf hTlow (by norm_num)
  have hscale0 : 0 ≤ 16 * (D * N * F ^ 5000) := by
    positivity
  have htail :
      16 * (D * N * F ^ 5000) *
          (T ^ (1 - (5000 : ℝ)) / ((5000 : ℝ) - 1)) ≤
        16 * (D * N * F ^ 5000) *
          (((X : ℝ) / 2) ^ (1 - (5000 : ℝ)) / ((5000 : ℝ) - 1)) := by
    apply mul_le_mul_of_nonneg_left _ hscale0
    exact div_le_div_of_nonneg_right hpow (by norm_num)
  calc
    ‖inghamRouteTBufferedFullTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoVonMangoldtEdge X‖ ≤
      16 * (D * N * F ^ 5000) *
        (T ^ (1 - (5000 : ℝ)) / ((5000 : ℝ) - 1)) := by
          simpa only [N, F, T] using hbound hX
    _ ≤ 16 * (D * N * F ^ 5000) *
        (((X : ℝ) / 2) ^ (1 - (5000 : ℝ)) / ((5000 : ℝ) - 1)) := htail
    _ = E * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
      have hscale :=
        inghamRouteTMellinCenter_mul_bufferedFrequency_pow_5000_mul_halfHeight_rpow_neg_4999 hX1
      rw [show (1 - (5000 : ℝ)) = -(4999 : ℝ) by norm_num]
      rw [show ((5000 : ℝ) - 1) = 4999 by norm_num]
      calc
        16 * (D * N * F ^ 5000) *
              (((X : ℝ) / 2) ^ (-(4999 : ℝ)) / 4999) =
            (16 * D / 4999) *
              (N * F ^ 5000 * ((X : ℝ) / 2) ^ (-(4999 : ℝ))) := by ring
        _ = (16 * D / 4999) *
              ((2 : ℝ) ^ 4999 * (X : ℝ) ^ (-(196 / 299 : ℝ))) := by
            rw [show N * F ^ 5000 * ((X : ℝ) / 2) ^ (-(4999 : ℝ)) =
              (2 : ℝ) ^ 4999 * (X : ℝ) ^ (-(196 / 299 : ℝ)) by
                simpa only [N, F] using hscale]
        _ = E * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
            dsimp only [E]
            ring

theorem tendsto_inghamRouteTBufferedFullTwoVonMangoldtEdge_sub_selected_zero :
    Tendsto (fun X : ℕ =>
      inghamRouteTBufferedFullTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoVonMangoldtEdge X) atTop (nhds 0) := by
  obtain ⟨E, hE, hbound⟩ :=
    exists_norm_inghamRouteTBufferedFullTwoVonMangoldtEdge_sub_selected_rpow_le
  have hcore : Tendsto (fun X : ℕ =>
      (X : ℝ) ^ (-(196 / 299 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 196 / 299)).comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ =>
      E * (X : ℝ) ^ (-(196 / 299 : ℝ))) atTop (nhds 0) :=
    by simpa using hcore.const_mul E
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
  exact hbound hX

end

end RHTower.Sieve
