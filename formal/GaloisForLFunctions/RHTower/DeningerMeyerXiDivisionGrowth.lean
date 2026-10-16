import GaloisForLFunctions.RHTower.DeningerMeyerMellinStripControl
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianStripRegularization
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness

/-!+# Xi division has admissible vertical growth

Good horizontal Xi ratios, the Gamma floor, and the rectangle maximum
principle control an entire quotient of a genuine Meyer Mellin transform.
The resulting growth is local in strip width. Gaussian reconstruction
therefore applies without any global horizontal growth restriction.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

private theorem quotient_bound_of_exp_floor {a b : ℂ} {d u C : ℝ}
    (hd : 0 < d) (hf : Real.exp (-u)/d ≤ ‖a‖) (hb : ‖a*b‖ ≤ C) :
    ‖b‖ ≤ d*C*Real.exp u := by
  have he : Real.exp u ≠ 0 := Real.exp_ne_zero u
  calc ‖b‖ = (d*Real.exp u)*((Real.exp (-u)/d)*‖b‖) := by
        rw [Real.exp_neg]
        field_simp
    _ ≤ (d*Real.exp u)*(‖a‖*‖b‖) := by
      gcongr
    _ ≤ (d*Real.exp u)*C := by
      rw [← norm_mul]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private theorem xi_floor_edges (s : ℂ) (hs : s.re = -1 ∨ s.re = 2) :
    Real.exp (-(Real.pi*|s.im|/4))/(3*Real.pi) ≤ ‖xi s‖ := by
  rcases hs with hs | hs
  · have he : 1-s = (2 : ℂ)+((-s.im : ℝ) : ℂ)*I := by
      apply Complex.ext <;> norm_num [hs]
    have h := xi_floor_two (-s.im)
    rw [← he, xi_one_sub, abs_neg] at h
    exact h
  · have he : s = (2 : ℂ)+(s.im : ℂ)*I := by
      apply Complex.ext <;> simp [hs]
    simpa only [← he] using xi_floor_two s.im

private theorem centred_profile_mellin (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    centredLaplace (fun t => Complex.exp ((t : ℂ)/2)*g.val t) s =
      deningerMeyerStrongLogMellin g s := by
  apply integral_congr_ae
  filter_upwards with t
  change Complex.exp ((s-1/2)*t)*(Complex.exp ((t : ℂ)/2)*g.val t) =
    deningerMeyerStrongLogMellinJet 0 s g.val t
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem quotient_core_growth
    (g : DeningerMeyerStrongLogTarget) {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hdiv : ∀ s, deningerMeyerStrongLogMellin g s = xi s * H s) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖H s‖ ≤ C * Real.exp (B*|s.im|) := by
  obtain ⟨K, hK, hk⟩ := deningerMeyerStrongLogMellin_strip_bound g (-1) 2
  obtain ⟨M, n₀, hsel⟩ := exists_xi_horizontal_ratio_nat_bound
  let B : ℝ := M + Real.pi/4
  let C : ℝ := 3*Real.pi*K*Real.exp (B*(|n₀|+2))
  refine ⟨C, B, by positivity, by positivity, fun s hs₁ hs₂ => ?_⟩
  obtain ⟨T, hnT, hTn, hgood⟩ := hsel (max |s.im| (max n₀ 1))
    (le_trans (le_max_left _ _) (le_max_right _ _))
  have hT : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnT
  have hsi : |s.im| ≤ T := (le_max_left _ _).trans hnT
  have hTpos : 0 < T := by linarith
  have hTN : T ≤ |s.im|+(|n₀|+2) := by
    have : max |s.im| (max n₀ 1) ≤ |s.im|+|n₀|+1 :=
      max_le (by linarith [abs_nonneg n₀])
        (max_le (by linarith [le_abs_self n₀, abs_nonneg s.im])
          (by linarith [abs_nonneg n₀, abs_nonneg s.im]))
    linarith
  have hrect : ‖H s‖ ≤ (3*Real.pi*K)*T^M*Real.exp (Real.pi*T/4) := by
    refine norm_le_of_rectangle_frontier_bound hH (by norm_num : (-1:ℝ) < 2)
      (by linarith : -T < T) (fun u hu₁ hu₂ hu₃ hu₄ he => ?_)
      hs₁ hs₂ (by linarith [neg_abs_le s.im]) (by linarith [le_abs_self s.im])
    rcases he with he | he | he | he
    · have hu := quotient_bound_of_exp_floor (C := K) (by positivity : 0 < 3*Real.pi)
        (xi_floor_edges u (Or.inl he)) (by rw [← hdiv]; exact hk u hu₁ hu₂)
      calc ‖H u‖ ≤ (3*Real.pi)*K*Real.exp (Real.pi*|u.im|/4) := hu
        _ ≤ (3*Real.pi)*K*Real.exp (Real.pi*T/4) := by
          gcongr
          exact abs_le.mpr ⟨hu₃, hu₄⟩
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right (by positivity : 0 ≤ 3*Real.pi*K)
              (one_le_pow₀ hT)) (Real.exp_nonneg _)
    · have hu := quotient_bound_of_exp_floor (C := K) (by positivity : 0 < 3*Real.pi)
        (xi_floor_edges u (Or.inr he)) (by rw [← hdiv]; exact hk u hu₁ hu₂)
      calc ‖H u‖ ≤ (3*Real.pi)*K*Real.exp (Real.pi*|u.im|/4) := hu
        _ ≤ (3*Real.pi)*K*Real.exp (Real.pi*T/4) := by
          gcongr
          exact abs_le.mpr ⟨hu₃, hu₄⟩
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right (by positivity : 0 ≤ 3*Real.pi*K)
              (one_le_pow₀ hT)) (Real.exp_nonneg _)
    · have hu := norm_quotient_le_horizontal (M := M) (G₀ := 0) hT
        (fun z => (centred_profile_mellin g z).trans (hdiv z))
        (fun z hz₁ hz₂ => by simpa [centred_profile_mellin] using hk z hz₁ hz₂)
        hgood hu₁ hu₂ (by rw [he, abs_neg, abs_of_pos hTpos])
      simpa using hu
    · have hu := norm_quotient_le_horizontal (M := M) (G₀ := 0) hT
        (fun z => (centred_profile_mellin g z).trans (hdiv z))
        (fun z hz₁ hz₂ => by simpa [centred_profile_mellin] using hk z hz₁ hz₂)
        hgood hu₁ hu₂ (by rw [he, abs_of_pos hTpos])
      simpa using hu
  have hp : T^M ≤ Real.exp ((M : ℝ)*T) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hTpos]
    apply Real.exp_le_exp.mpr
    have := Real.log_le_sub_one_of_pos hTpos
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  calc ‖H s‖ ≤ (3*Real.pi*K)*T^M*Real.exp (Real.pi*T/4) := hrect
    _ ≤ (3*Real.pi*K)*Real.exp ((M:ℝ)*T)*Real.exp (Real.pi*T/4) := by gcongr
    _ = (3*Real.pi*K)*Real.exp (B*T) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [B]
      ring
    _ ≤ (3*Real.pi*K)*Real.exp (B*(|s.im|+(|n₀|+2))) := by
      gcongr
    _ = C*Real.exp (B*|s.im|) := by
      dsimp [C]
      rw [mul_add, Real.exp_add]
      ring

private theorem gamma_exp_floor {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-x) ≤ Real.Gamma x := by
  have hxp : 0 < x := by linarith
  have h := stirling_le_log_Gamma hxp
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hplog : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [← Real.exp_log (Real.Gamma_pos_of_pos hxp)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (by linarith : 0 ≤ x-1/2) hxlog]

private theorem xi_crude_exterior_floor (s : ℂ) (hs : 2 ≤ s.re) :
    Real.exp (-(((Real.log Real.pi+1)/2)*s.re + Real.pi*|s.im|/4))/3 ≤ ‖xi s‖ := by
  have h := xi_floor (σ := s.re) (t := s.im) hs
  rw [Complex.re_add_im] at h
  have hg := gamma_exp_floor (x := s.re/2) (by linarith)
  calc Real.exp (-(((Real.log Real.pi+1)/2)*s.re + Real.pi*|s.im|/4))/3
      = (1/3)*(Real.pi^(-(s.re/2))*Real.exp (-(s.re/2)))*
          Real.exp (-(Real.pi*|s.im|/4)) := by
        rw [Real.rpow_def_of_pos Real.pi_pos]
        rw [mul_assoc (1/3), ← Real.exp_add, ← Real.exp_add]
        rw [div_eq_mul_inv, mul_comm _ (3⁻¹ : ℝ)]
        congr 2 <;> ring
    _ ≤ (1/3)*(Real.pi^(-(s.re/2))*Real.Gamma (s.re/2))*
          Real.exp (-(Real.pi*|s.im|/4)) := by gcongr
    _ ≤ _ := h

/-- Entire Xi division of an actual Meyer transform has at most exponential
growth in height on each fixed strip. -/
theorem deningerMeyerXiQuotient_verticalExponential
    (g : DeningerMeyerStrongLogTarget) {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hdiv : ∀ s, deningerMeyerStrongLogMellin g s = xi s * H s) :
    DeningerVerticalExponential H := by
  obtain ⟨C₀, B₀, hC₀, hB₀, hcore⟩ := quotient_core_growth g hH hdiv
  intro a b
  obtain ⟨K, hK, hk⟩ := deningerMeyerStrongLogMellin_strip_bound g a b
  let R := |a|+|b|+3
  let D := (Real.log Real.pi+1)/2
  let E := 3*K*Real.exp (D*R)
  have hD : 0 ≤ D := by
    have := Real.log_nonneg (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
    dsimp [D]
    positivity
  have hE : 0 ≤ E := by positivity
  refine ⟨C₀+E, B₀+Real.pi/4, by positivity, by positivity, fun s ha hb => ?_⟩
  have hext (x : ℝ) (hx : x ≤ R)
      (hf : Real.exp (-(D*x+Real.pi*|s.im|/4))/3 ≤ ‖xi s‖) :
      ‖H s‖ ≤ E*Real.exp ((Real.pi/4)*|s.im|) := by
    have hq := quotient_bound_of_exp_floor (C := K) (by norm_num : (0:ℝ) < 3) hf
      (by rw [← hdiv]; exact hk s ha hb)
    calc ‖H s‖ ≤ 3*K*Real.exp (D*x+Real.pi*|s.im|/4) := hq
      _ ≤ 3*K*Real.exp (D*R+Real.pi*|s.im|/4) := by gcongr
      _ = _ := by
        rw [Real.exp_add]
        dsimp [E]
        rw [show Real.pi*|s.im|/4 = (Real.pi/4)*|s.im| by ring]
        ring
  have hext_le : E*Real.exp ((Real.pi/4)*|s.im|) ≤
      (C₀+E)*Real.exp ((B₀+Real.pi/4)*|s.im|) := by
    apply mul_le_mul (by linarith)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)))
      (Real.exp_nonneg _) (by positivity)
  by_cases hl : s.re ≤ -1
  · have hf := xi_crude_exterior_floor (1-s) (by simp; linarith)
    simp only [xi_one_sub, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hf
    have hq := hext (1-s.re) (by
      dsimp [R]
      linarith [neg_le_abs a, abs_nonneg b]) hf
    exact hq.trans hext_le
  · by_cases hr : 2 ≤ s.re
    · have hq := hext s.re (by
        dsimp [R]
        linarith [le_abs_self b, abs_nonneg a]) (xi_crude_exterior_floor s hr)
      exact hq.trans hext_le
    · have hq := hcore s (by linarith) (by linarith)
      apply hq.trans
      exact mul_le_mul (by linarith)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (by linarith [Real.pi_pos]) (abs_nonneg _)))
        (Real.exp_nonneg _) (by positivity)

/-- Every entire Xi quotient of a genuine source admits Gaussian inversion
in the original source space. -/
theorem deningerMeyerXiQuotient_regularized
    (g : DeningerMeyerStrongLogTarget) {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hdiv : ∀ s, deningerMeyerStrongLogMellin g s = xi s * H s)
    {ε : ℝ} (hε : 0 < ε) :
    DeningerEntireMellinRegular (deningerGaussianMellinRegularization ε H) :=
  deningerGaussianMellinRegularization_entireRegular hH
    (deningerMeyerXiQuotient_verticalExponential g hH hdiv) hε

end
end RHTower
