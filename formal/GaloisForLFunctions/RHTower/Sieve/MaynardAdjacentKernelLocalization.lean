import GaloisForLFunctions.RHTower.Sieve.MaynardMultiscaleReferenceTelescope
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

theorem exists_routeTNormalizedSmoothWindowMellin_quadratic_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ N H c y : ℝ, 0 < N → 0 < H → 0 < c →
        |y| ^ 2 * ‖routeTNormalizedSmoothWindowMellin N H
          ((c : ℂ) + (y : ℝ) * I)‖ ≤
          (C / H) *
            (((N + 2 * H) / H) * (N + 2 * H) ^ c +
              ((N + H) / H) * (N + H) ^ c) := by
  obtain ⟨_C0, C, _hC0, hC, hscale⟩ :=
    exists_mellin_smoothWeight_two_scale_bounds
  refine ⟨C, hC, ?_⟩
  intro N H c y hN hH hc
  let s : ℂ := (c : ℂ) + (y : ℝ) * I
  have hsre : s.re = c := by simp [s]
  have hsim : s.im = y := by simp [s]
  have hplus := (hscale (N + H) H (by linarith) hH s (by simpa [hsre] using hc)).2
  have hbase := (hscale N H hN hH s (by simpa [hsre] using hc)).2
  rw [hsre, hsim] at hplus hbase
  let Mp : ℂ := mellin (fun x : ℝ =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ)) s
  let Mb : ℂ := mellin (fun x : ℝ =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s
  have hplus' : |y| ^ 2 * ‖Mp‖ ≤
      C * ((N + 2 * H) / H) * (N + 2 * H) ^ c := by
    simpa only [Mp, two_mul, add_assoc] using hplus
  have hbase' : |y| ^ 2 * ‖Mb‖ ≤
      C * ((N + H) / H) * (N + H) ^ c := by
    simpa [Mb] using hbase
  have hsub : ‖Mp - Mb‖ ≤ ‖Mp‖ + ‖Mb‖ := norm_sub_le _ _
  have hnorm : ‖routeTNormalizedSmoothWindowMellin N H s‖ = H⁻¹ * ‖Mp - Mb‖ := by
    rw [routeTNormalizedSmoothWindowMellin,
      mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by simpa [hsre] using hc),
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  rw [hnorm]
  calc
    |y| ^ 2 * (H⁻¹ * ‖Mp - Mb‖) =
        H⁻¹ * (|y| ^ 2 * ‖Mp - Mb‖) := by ring
    _ ≤ H⁻¹ * (|y| ^ 2 * (‖Mp‖ + ‖Mb‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsub (sq_nonneg |y|)) (inv_nonneg.mpr hH.le)
    _ = H⁻¹ * (|y| ^ 2 * ‖Mp‖ + |y| ^ 2 * ‖Mb‖) := by ring
    _ ≤ H⁻¹ *
        (C * ((N + 2 * H) / H) * (N + 2 * H) ^ c +
          C * ((N + H) / H) * (N + H) ^ c) :=
      mul_le_mul_of_nonneg_left (add_le_add hplus' hbase') (inv_nonneg.mpr hH.le)
    _ = (C / H) *
        (((N + 2 * H) / H) * (N + 2 * H) ^ c +
          ((N + H) / H) * (N + H) ^ c) := by ring

theorem exists_routeTNormalizedSmoothWindowMellin_one_quadratic_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ N H y : ℝ, 0 < N → 0 < H → H ≤ N →
        |y| ^ 2 * ‖routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I)‖ ≤ 13 * C * (N / H) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro N H y hN hH hHN
  have hraw := hbound N H 1 y hN hH (by norm_num)
  norm_num at hraw
  have hplus : (N + 2 * H) ^ 2 ≤ (3 * N) ^ 2 := by
    nlinarith [sq_nonneg (N + 2 * H), sq_nonneg (3 * N)]
  have hbase : (N + H) ^ 2 ≤ (2 * N) ^ 2 := by
    nlinarith [sq_nonneg (N + H), sq_nonneg (2 * N)]
  have hsum : (N + 2 * H) ^ 2 + (N + H) ^ 2 ≤ 13 * N ^ 2 := by
    nlinarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hHsq : 0 < H ^ 2 := sq_pos_of_pos hH
  calc
    |y| ^ 2 * ‖routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * I)‖ ≤
        (C / H) * (((N + 2 * H) / H) * (N + 2 * H) +
          ((N + H) / H) * (N + H)) := by simpa [sq_abs] using hraw
    _ = (C / H ^ 2) * ((N + 2 * H) ^ 2 + (N + H) ^ 2) := by
      field_simp
    _ ≤ (C / H ^ 2) * (13 * N ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hC0 hHsq.le)
    _ = 13 * C * (N / H) ^ 2 := by
      field_simp

theorem exists_integral_routeTNormalizedSmoothWindowMellin_one_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ N H U : ℝ, 0 < N → 0 < H → H ≤ N → 0 < U →
        ∫ y in {y : ℝ | U ≤ |y|},
            ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖ ≤
          26 * C * (N / H) ^ 2 / U := by
  obtain ⟨C, hC, hquad⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_one_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro N H U hN hH hHN hU
  let f : ℝ → ℝ := fun y =>
    ‖routeTNormalizedSmoothWindowMellin N H
      ((1 : ℂ) + (y : ℝ) * I)‖
  let K : ℝ := 13 * C * (N / H) ^ 2
  have hpoint : ∀ y : ℝ, U ≤ |y| → f y ≤ K * |y| ^ (-(2 : ℝ)) := by
    intro y hy
    have hypos : 0 < |y| := hU.trans_le hy
    have hraw := hquad N H y hN hH hHN
    have hpow : |y| ^ (-(2 : ℝ)) = (|y| ^ 2)⁻¹ := by
      rw [Real.rpow_neg (abs_nonneg y), Real.rpow_two]
    rw [hpow]
    rw [mul_comm]
    apply (le_inv_mul_iff₀ (sq_pos_of_pos hypos)).2
    simpa [f, K, mul_comm] using hraw
  have htail := setIntegral_le_of_le_powerTail
    (f := f) (K := K) (t := U) (p := (2 : ℝ))
    (fun y => norm_nonneg _) hU (by norm_num) hpoint
  norm_num at htail
  rw [Real.rpow_neg hU.le, Real.rpow_one] at htail
  change (∫ y in {y : ℝ | U ≤ |y|}, f y) ≤ _
  convert htail using 1
  dsimp only [K]
  field_simp
  ring

theorem integrable_routeTNormalizedSmoothWindowMellin_one
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    Integrable (fun y : ℝ =>
      routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * I)) := by
  have hplus := verticalIntegrable_mellin_smoothWeight
    (N := N + H) (H := H) (by linarith) hH (by norm_num : (0 : ℝ) < 1)
  have hbase := verticalIntegrable_mellin_smoothWeight
    (N := N) (H := H) hN hH (by norm_num : (0 : ℝ) < 1)
  have hsub := hplus.sub hbase
  refine (hsub.const_mul ((H : ℂ)⁻¹)).congr ?_
  filter_upwards with y
  rw [routeTNormalizedSmoothWindowMellin,
    mellin_routeTSmoothWindowWeight_eq_sub hN.le hH (by simp)]
  rfl

theorem integrable_norm_routeTNormalizedSmoothWindowMellin_one
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    Integrable (fun y : ℝ =>
      ‖routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * I)‖) := by
  have hkernel : Integrable (fun y : ℝ =>
      routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * I)) :=
    integrable_routeTNormalizedSmoothWindowMellin_one hN hH
  exact hkernel.norm

theorem exists_integral_routeTAdjacentNormalizedKernel_one_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ N H R : ℝ, 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N →
        ∫ y in {y : ℝ | N / (2 * R) ≤ |y|},
            ‖routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * I)‖ ≤
          260 * C * (N / R) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_routeTNormalizedSmoothWindowMellin_one_tail_le
  refine ⟨C, hC, ?_⟩
  intro N H R hN hH hR hHR hRH hRN
  let tail : Set ℝ := {y : ℝ | N / (2 * R) ≤ |y|}
  let KR : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I)
  let KH : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  have hHleN : H ≤ N := hHR.trans hRN
  have hU : 0 < N / (2 * R) := by positivity
  have htailR := htail N R (N / (2 * R)) hN hR hRN hU
  have htailH := htail N H (N / (2 * R)) hN hH hHleN hU
  have hKR : Integrable KR := by
    exact integrable_routeTNormalizedSmoothWindowMellin_one hN hR
  have hKH : Integrable KH := by
    exact integrable_routeTNormalizedSmoothWindowMellin_one hN hH
  have hmono :
      (∫ y in tail, ‖KR y - KH y‖) ≤
        ∫ y in tail, (‖KR y‖ + ‖KH y‖) := by
    apply setIntegral_mono_on (hKR.sub hKH).norm.integrableOn
      (hKR.norm.add hKH.norm).integrableOn (measurableSet_centralTail _)
    intro y _hy
    exact norm_sub_le _ _
  have hsplit :
      (∫ y in tail, (‖KR y‖ + ‖KH y‖)) =
        (∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖ := by
    exact integral_add hKR.norm.integrableOn hKH.norm.integrableOn
  have hRbound : 26 * C * (N / R) ^ 2 / (N / (2 * R)) =
      52 * C * (N / R) := by field_simp; ring
  have hHbound : 26 * C * (N / H) ^ 2 / (N / (2 * R)) ≤
      208 * C * (N / R) := by
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    have hratio : R / H ≤ 2 := (div_le_iff₀ hH).2 hRH
    have hratio0 : 0 ≤ R / H := by positivity
    have hNdivR : 0 ≤ N / R := by positivity
    have hrewrite : 26 * C * (N / H) ^ 2 / (N / (2 * R)) =
        52 * C * (N / R) * (R / H) ^ 2 := by field_simp; ring
    rw [hrewrite]
    have hsq : (R / H) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_nonneg hC0 hNdivR]
  calc
    (∫ y in {y : ℝ | N / (2 * R) ≤ |y|},
        ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖) =
        ∫ y in tail, ‖KR y - KH y‖ := by rfl
    _ ≤ ∫ y in tail, (‖KR y‖ + ‖KH y‖) := hmono
    _ = (∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖ := hsplit
    _ ≤ 26 * C * (N / R) ^ 2 / (N / (2 * R)) +
        26 * C * (N / H) ^ 2 / (N / (2 * R)) :=
      add_le_add (by simpa [tail, KR] using htailR)
        (by simpa [tail, KH] using htailH)
    _ ≤ 52 * C * (N / R) + 208 * C * (N / R) := by
      exact add_le_add hRbound.le hHbound
    _ = 260 * C * (N / R) := by ring

end RHTower.Sieve
