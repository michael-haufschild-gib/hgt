import GaloisForLFunctions.RHTower.SuzukiSelectedContourSides
import GaloisForLFunctions.RHTower.SuzukiCanonicalArithmeticMellin

/-!
# Endpoint integrability for Suzuki's finite-pole contour

Boundary unimodularity controls the real line. Suzuki's exact absolutely convergent source Mellin
representation controls the Euler line `Im z = 1`. Rapid decay of the Deninger--Meyer test transform
then gives unconditional `L¹` endpoint pairings without meromorphic-innerness.
-/

namespace RHTower

open Complex MeasureTheory Set Filter Topology

noncomputable section

theorem norm_suzukiCanonicalTheta_ofReal_le_one (omega x : ℝ) :
    ‖suzukiCanonicalTheta omega (x : ℂ)‖ ≤ 1 := by
  by_cases hE : suzukiCanonicalE omega (x : ℂ) = 0
  · rw [suzukiCanonicalTheta_eq_E_neg_div_E, hE, div_zero, norm_zero]
    norm_num
  · rw [norm_suzukiCanonicalTheta_ofReal_eq_one omega x hE]

/-- On the fixed Euler line `Im z = 1`, Suzuki's absolutely convergent source Mellin
representation gives a uniform bound for the shifted-Xi quotient. -/
theorem exists_bound_norm_suzukiCanonicalTheta_horizontal_one
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖suzukiCanonicalTheta omega ((x : ℂ) + Complex.I)‖ ≤ C := by
  have hEuler : 1 / 2 + omega < (Complex.I : ℂ).im := by
    simp
    linarith
  have h0 := suzuki2012_proposition_one homega0 hEuler
  let C : ℝ := ∫ t : ℝ in Set.Ioi 0,
    ‖(t : ℂ) ^ ((1 / 2 + Complex.I * Complex.I) - 1) •
      suzukiSourceHFinite omega t‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  refine ⟨C, hC, ?_⟩
  intro x
  let z : ℂ := (x : ℂ) + Complex.I
  have hz : 1 / 2 + omega < z.im := by
    dsimp [z]
    simp
    linarith
  have h := suzuki2012_proposition_one homega0 hz
  have hnorm : ∀ t : ℝ, t ∈ Set.Ioi 0 →
      ‖(t : ℂ) ^ ((1 / 2 + z * Complex.I) - 1) •
          suzukiSourceHFinite omega t‖ =
        ‖(t : ℂ) ^ ((1 / 2 + Complex.I * Complex.I) - 1) •
          suzukiSourceHFinite omega t‖ := by
    intro t ht
    rw [norm_smul, norm_smul,
      Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_cpow_eq_rpow_re_of_pos ht]
    congr 2
    dsimp [z]
    simp [Complex.mul_re]
  calc
    ‖suzukiCanonicalTheta omega z‖ = ‖mellin (suzukiSourceHFinite omega)
        (1 / 2 + z * Complex.I)‖ := congrArg norm h.2.symm
    _ ≤ ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ ((1 / 2 + z * Complex.I) - 1) •
          suzukiSourceHFinite omega t‖ := norm_integral_le_integral_norm _
    _ = C := by
      dsimp [C]
      exact setIntegral_congr_fun measurableSet_Ioi hnorm

theorem measurable_suzukiCanonicalHankelContourIntegrand_horizontal
    (omega sigma : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    Measurable fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrand omega g r
        ((x : ℂ) + (sigma : ℂ) * Complex.I) := by
  rw [show (fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrand omega g r
        ((x : ℂ) + (sigma : ℂ) * Complex.I)) =
      fun x : ℝ =>
        (suzukiCanonicalESharp omega
            ((x : ℂ) + (sigma : ℂ) * Complex.I) /
          suzukiCanonicalE omega
            ((x : ℂ) + (sigma : ℂ) * Complex.I)) *
        deningerMeyerStrongLogMellin g
          (-Complex.I * ((x : ℂ) + (sigma : ℂ) * Complex.I)) *
        Complex.exp
          (-Complex.I * ((x : ℂ) + (sigma : ℂ) * Complex.I) * (r : ℂ)) by
    funext x
    rw [suzukiCanonicalHankelContourIntegrand,
      suzukiCanonicalTheta_eq_ESharp_div_E]]
  have hsharp : Continuous fun x : ℝ =>
      suzukiCanonicalESharp omega ((x : ℂ) + (sigma : ℂ) * Complex.I) :=
    (differentiable_suzukiCanonicalESharp omega).continuous.comp (by fun_prop)
  have hE : Continuous fun x : ℝ =>
      suzukiCanonicalE omega ((x : ℂ) + (sigma : ℂ) * Complex.I) :=
    (differentiable_suzukiCanonicalE omega).continuous.comp (by fun_prop)
  have hM : Continuous fun x : ℝ => deningerMeyerStrongLogMellin g
      (-Complex.I * ((x : ℂ) + (sigma : ℂ) * Complex.I)) :=
    (differentiable_deningerMeyerStrongLogMellin g.property).continuous.comp (by fun_prop)
  exact ((hsharp.measurable.div hE.measurable).mul hM.measurable).mul (by fun_prop)

/-- A bounded horizontal restriction of Suzuki's quotient is an `L¹` multiplier of the
all-order Deninger--Meyer Mellin line. -/
theorem integrable_suzukiCanonicalHankelContourIntegrand_of_theta_line_bound
    {omega sigma B : ℝ} (hB : 0 ≤ B)
    (htheta : ∀ x : ℝ,
      ‖suzukiCanonicalTheta omega
        ((x : ℂ) + (sigma : ℂ) * Complex.I)‖ ≤ B)
    (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    Integrable fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrand omega g r
        ((x : ℂ) + (sigma : ℂ) * Complex.I) := by
  have hM0 : Integrable fun y : ℝ =>
      deningerMeyerStrongLogMellin g
        ((sigma : ℂ) + (y : ℂ) * Complex.I) := by
    apply integrable_line_of_stripRapidDecrease
      (hasStripRapidDecrease_deningerMeyerStrongLogMellin g)
    exact (differentiable_deningerMeyerStrongLogMellin g.property).continuous.comp
      (by fun_prop)
  have hM : Integrable fun x : ℝ =>
      deningerMeyerStrongLogMellin g
        ((sigma : ℂ) - (x : ℂ) * Complex.I) := by
    simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using hM0.comp_neg
  let K : ℝ := B * Real.exp (|sigma| * |r|)
  have hK : 0 ≤ K := mul_nonneg hB (Real.exp_pos _).le
  refine Integrable.mono' (hM.norm.const_mul K)
    (measurable_suzukiCanonicalHankelContourIntegrand_horizontal omega sigma g r).aestronglyMeasurable
    ?_
  filter_upwards with x
  have hrot : -Complex.I * ((x : ℂ) + (sigma : ℂ) * Complex.I) =
      (sigma : ℂ) - (x : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hexp : ‖Complex.exp
      (((sigma : ℂ) - (x : ℂ) * Complex.I) * (r : ℂ))‖ ≤
        Real.exp (|sigma| * |r|) := by
    rw [Complex.norm_exp]
    have hre :
        (((sigma : ℂ) - (x : ℂ) * Complex.I) * (r : ℂ)).re =
          sigma * r := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    exact Real.exp_le_exp.mpr (by
      calc
        sigma * r ≤ |sigma * r| := le_abs_self _
        _ = |sigma| * |r| := abs_mul _ _)
  rw [suzukiCanonicalHankelContourIntegrand, norm_mul, norm_mul, hrot]
  calc
    ‖suzukiCanonicalTheta omega ((x : ℂ) + (sigma : ℂ) * Complex.I)‖ *
          ‖deningerMeyerStrongLogMellin g
            ((sigma : ℂ) - (x : ℂ) * Complex.I)‖ *
          ‖Complex.exp
            (((sigma : ℂ) - (x : ℂ) * Complex.I) * (r : ℂ))‖ ≤
        B * ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) - (x : ℂ) * Complex.I)‖ *
          Real.exp (|sigma| * |r|) := by
      gcongr
      exact htheta x
    _ = K * ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) - (x : ℂ) * Complex.I)‖ := by
      dsimp [K]
      ring

theorem integrable_suzukiCanonicalHankelContourIntegrand_real
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    Integrable fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrand omega g r (x : ℂ) := by
  have h := integrable_suzukiCanonicalHankelContourIntegrand_of_theta_line_bound
    (omega := omega) (sigma := 0) (B := 1) (by norm_num)
    (by intro x; simpa using norm_suzukiCanonicalTheta_ofReal_le_one omega x)
    g r
  simpa using h

theorem integrable_suzukiCanonicalHankelContourIntegrand_horizontal_one
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2)
    (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    Integrable fun x : ℝ =>
      suzukiCanonicalHankelContourIntegrand omega g r
        ((x : ℂ) + Complex.I) := by
  obtain ⟨B, hB, htheta⟩ :=
    exists_bound_norm_suzukiCanonicalTheta_horizontal_one homega0 homegaHalf
  have h := integrable_suzukiCanonicalHankelContourIntegrand_of_theta_line_bound
    (omega := omega) (sigma := 1) hB (by simpa using htheta) g r
  simpa using h

end

end RHTower
