import GaloisForLFunctions.RHTower.Sieve.MaynardMultiscaleReferenceTelescope
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

private theorem integral_abs_symmetric {U : ℝ} (hU : 0 ≤ U) :
    (∫ y in (-U)..U, |y|) = U ^ 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-U) 0)
    (continuous_abs.intervalIntegrable 0 U)]
  have hleft_congr : (∫ y in (-U)..0, |y|) = ∫ y in (-U)..0, -y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    simpa using abs_of_nonpos hy.2
  have hleft : (∫ y in (-U)..0, |y|) = U ^ 2 / 2 := by
    rw [hleft_congr, intervalIntegral.integral_neg, integral_id]
    ring
  have hright_congr : (∫ y in (0 : ℝ)..U, |y|) = ∫ y in (0 : ℝ)..U, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hU] at hy
    exact abs_of_nonneg hy.1
  have hright : (∫ y in (0 : ℝ)..U, |y|) = U ^ 2 / 2 := by
    rw [hright_congr, integral_id]
    ring
  rw [hleft, hright]
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

/-- On the common low band, pole cancellation makes adjacent-kernel mass proportional to its
natural ordinate length `N / R`, independently of the narrower width. -/
theorem integral_routeTAdjacentNormalizedKernel_one_central_le
    {N H R : ℝ} (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hHR : H ≤ R) :
    (∫ y in (-(N / (2 * R)))..(N / (2 * R)),
      ‖routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I)‖) ≤ 2 * (N / R) := by
  let U : ℝ := N / (2 * R)
  let f : ℝ → ℝ := fun y =>
    ‖routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I)‖
  let g : ℝ → ℝ := fun y => 8 * (R / N) * |y|
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hpoint : ∀ y ∈ Set.Icc (-U) U, f y ≤ g y := by
    intro y hy
    have hyabs : |y| ≤ U := abs_le.mpr ⟨hy.1, hy.2⟩
    let s : ℂ := (1 : ℂ) + (y : ℝ) * I
    have hsre : s.re = 1 := by simp [s]
    have hsnorm : ‖s - 1‖ = |y| := by
      simp [s, Real.norm_eq_abs]
    have hsmall : ‖s - 1‖ * (2 * R / N) ≤ 1 := by
      rw [hsnorm]
      calc
        |y| * (2 * R / N) ≤ U * (2 * R / N) :=
          mul_le_mul_of_nonneg_right hyabs (by positivity)
        _ = 1 := by dsimp [U]; field_simp
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
      hN hH hR hHR (by simpa [hsre]) hsmall
    norm_num [hsre, hsnorm] at hkernel
    have hlocal : f y ≤ 8 * |y| * (R / N) := by
      simpa [f, s] using hkernel
    calc
      f y ≤ 8 * |y| * (R / N) := hlocal
      _ = g y := by dsimp [g]; ring
  have hfint : Integrable f := by
    exact ((integrable_routeTNormalizedSmoothWindowMellin_one hN hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one hN hH)).norm
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (by linarith : -U ≤ U)
    hfint.intervalIntegrable (hgcont.intervalIntegrable _ _) hpoint
  have hgintegral : (∫ y in (-U)..U, g y) = 8 * (R / N) * U ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_abs_symmetric hU]
  rw [hgintegral] at hmono
  calc
    (∫ y in (-(N / (2 * R)))..(N / (2 * R)),
      ‖routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I)‖) = ∫ y in (-U)..U, f y := by rfl
    _ ≤ 8 * (R / N) * U ^ 2 := hmono
    _ = 2 * (N / R) := by dsimp [U]; field_simp; ring

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

/-- Arbitrary-cutoff form of adjacent-kernel tail localization.  Comparable widths turn the two
one-width quadratic tails into one `130 C (N/R)^2/U` bound. -/
theorem exists_integral_routeTAdjacentNormalizedKernel_one_general_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ N H R U : ℝ, 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N → 0 < U →
        ∫ y in {y : ℝ | U ≤ |y|},
            ‖routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * I)‖ ≤
          130 * C * (N / R) ^ 2 / U := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_routeTNormalizedSmoothWindowMellin_one_tail_le
  refine ⟨C, hC, ?_⟩
  intro N H R U hN hH hR hHR hRH hRN hU
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  let KR : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I)
  let KH : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  have hHleN : H ≤ N := hHR.trans hRN
  have htailR := htail N R U hN hR hRN hU
  have htailH := htail N H U hN hH hHleN hU
  have hKR : Integrable KR :=
    integrable_routeTNormalizedSmoothWindowMellin_one hN hR
  have hKH : Integrable KH :=
    integrable_routeTNormalizedSmoothWindowMellin_one hN hH
  have hmono : (∫ y in tail, ‖KR y - KH y‖) ≤
      ∫ y in tail, (‖KR y‖ + ‖KH y‖) := by
    apply setIntegral_mono_on (hKR.sub hKH).norm.integrableOn
      (hKR.norm.add hKH.norm).integrableOn (measurableSet_centralTail _)
    intro y _hy
    exact norm_sub_le _ _
  have hsplit : (∫ y in tail, (‖KR y‖ + ‖KH y‖)) =
      (∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖ :=
    integral_add hKR.norm.integrableOn hKH.norm.integrableOn
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hratio : R / H ≤ 2 := (div_le_iff₀ hH).2 hRH
  have hratio0 : 0 ≤ R / H := by positivity
  have hratioSq : (R / H) ^ 2 ≤ 4 := by nlinarith
  have hNH : (N / H) ^ 2 ≤ 4 * (N / R) ^ 2 := by
    have hre : N / H = (N / R) * (R / H) := by field_simp
    rw [hre, mul_pow]
    calc
      (N / R) ^ 2 * (R / H) ^ 2 ≤ (N / R) ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left hratioSq (sq_nonneg (N / R))
      _ = 4 * (N / R) ^ 2 := by ring
  have hHbound : 26 * C * (N / H) ^ 2 / U ≤
      104 * C * (N / R) ^ 2 / U := by
    have hnum : 26 * C * (N / H) ^ 2 ≤
        104 * C * (N / R) ^ 2 := by
      calc
        26 * C * (N / H) ^ 2 ≤ 26 * C * (4 * (N / R) ^ 2) :=
          mul_le_mul_of_nonneg_left hNH (mul_nonneg (by norm_num) hC0)
        _ = 104 * C * (N / R) ^ 2 := by ring
    exact (div_le_div_iff_of_pos_right hU).2 hnum
  calc
    (∫ y in {y : ℝ | U ≤ |y|},
        ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)‖) =
        ∫ y in tail, ‖KR y - KH y‖ := by rfl
    _ ≤ ∫ y in tail, (‖KR y‖ + ‖KH y‖) := hmono
    _ = (∫ y in tail, ‖KR y‖) + ∫ y in tail, ‖KH y‖ := hsplit
    _ ≤ 26 * C * (N / R) ^ 2 / U +
        26 * C * (N / H) ^ 2 / U :=
      add_le_add (by simpa [tail, KR] using htailR)
        (by simpa [tail, KH] using htailH)
    _ ≤ 26 * C * (N / R) ^ 2 / U +
        104 * C * (N / R) ^ 2 / U :=
      add_le_add (le_refl _) hHbound
    _ = 130 * C * (N / R) ^ 2 / U := by ring

/-- Adjacent normalized window kernels have total vertical `L¹` mass on their natural scale.
The low band uses exact pole cancellation; the high band uses two integrations by parts. -/
theorem exists_integral_routeTAdjacentNormalizedKernel_one_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ N H R : ℝ, 0 < N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N →
        ∫ y : ℝ,
            ‖routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * I)‖ ≤
          262 * C * (N / R) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_routeTAdjacentNormalizedKernel_one_tail_le
  refine ⟨C, hC, ?_⟩
  intro N H R hN hH hR hHR hRH hRN
  let U : ℝ := N / (2 * R)
  let tail : Set ℝ := {y : ℝ | U ≤ |y|}
  let f : ℝ → ℝ := fun y =>
    ‖routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I)‖
  have hfint : Integrable f := by
    exact ((integrable_routeTNormalizedSmoothWindowMellin_one hN hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one hN hH)).norm
  have htailBound : (∫ y in tail, f y) ≤ 260 * C * (N / R) := by
    simpa [tail, U, f] using htail N H R hN hH hR hHR hRH hRN
  have hcentral := integral_routeTAdjacentNormalizedKernel_one_central_le
    hN hH hR hHR
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcompl : tailᶜ = Ioo (-U) U := by
    ext y
    simp [tail, Set.mem_Ioo, abs_lt]
  have hcentralSet : (∫ y in tailᶜ, f y) ≤ 2 * (N / R) := by
    rw [hcompl, MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -U ≤ U)]
    simpa [U, f] using hcentral
  have hsplit := integral_add_compl (measurableSet_centralTail U) hfint
  change (∫ y : ℝ, f y) ≤ _
  rw [← hsplit]
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hNR0 : 0 ≤ N / R := by positivity
  calc
    (∫ y in tail, f y) + ∫ y in tailᶜ, f y ≤
        260 * C * (N / R) + 2 * (N / R) :=
      add_le_add htailBound hcentralSet
    _ ≤ 260 * C * (N / R) + 2 * C * (N / R) := by
      nlinarith
    _ = 262 * C * (N / R) := by ring

end RHTower.Sieve
