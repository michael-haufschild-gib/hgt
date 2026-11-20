import GaloisForLFunctions.goldbach.LiLiu.ArithmeticKernel
import GaloisForLFunctions.goldbach.LiLiu.EulerBounds
import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBound
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZetaMultiplierBound

/-! # Growth of the continued Beta kernel on closed arithmetic strips -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Set
open scoped ComplexConjugate
noncomputable section

/-- The opposite imaginary parts in the Gamma quotient have equal Gamma modulus. -/
theorem signedBetaGammaFactor_vertical {s : ℂ} (hs : 0 ≤ s.re) (hu : s.re < 3/2) :
    ‖signedBetaGammaFactor s‖ ≤ Real.Gamma ((3/2-s.re)/2) / Real.Gamma ((3/2+s.re)/2) := by
  let a := (3/2 - s.re)/2
  let b := (3/2 + s.re)/2
  let t := s.im/2
  have ha : 0 < a := half_pos (sub_pos.mpr hu)
  have hab : a ≤ b := by dsimp [a,b]; linarith only [hs]
  have hn : (3/2-s)/2 = conj ((a : ℂ)+t*I) := by
    apply Complex.ext <;> norm_num [a,t,Complex.div_re,Complex.div_im] <;> ring
  have hd : (3/2+s)/2 = ((b : ℂ)+t*I) := by
    apply Complex.ext <;> norm_num [b,t,Complex.div_re,Complex.div_im] <;> ring
  rw [signedBetaGammaFactor, hn, hd, Gamma_conj, norm_div, RCLike.norm_conj]
  exact _root_.HTGeometry.norm_Gamma_div_le ha hab t

private theorem realGamma_continuous {x : ℝ} (hx : 0 < x) : ContinuousAt Real.Gamma x :=
  (Real.differentiableAt_Gamma x fun m he => by
    have hm := Nat.cast_nonneg (α := ℝ) m
    linarith only [he,hx,hm]).continuousAt

theorem signedBetaGammaFactor_strip_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1/8 → ‖signedBetaGammaFactor s‖ ≤ B := by
  let F := fun x : ℝ => Real.Gamma ((3/2-x)/2) / Real.Gamma ((3/2+x)/2)
  have hF : ContinuousOn F (Icc (0:ℝ) (1/8)) := by
    intro x hx
    have hn : 0 < (3/2-x)/2 := by linarith only [hx.2]
    have hd : 0 < (3/2+x)/2 := by linarith only [hx.1]
    exact (((realGamma_continuous hn).comp (by fun_prop)).div
      ((realGamma_continuous hd).comp (by fun_prop)) (Real.Gamma_pos_of_pos hd).ne').continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  refine ⟨max 0 B, le_max_left .., fun s hs hs' => ?_⟩
  exact (signedBetaGammaFactor_vertical hs (by linarith only [hs'])).trans
    ((le_abs_self (F s.re)).trans ((hB s.re ⟨hs,hs'⟩).trans (le_max_right ..)))

/-- Near zero height the closed strip stays a positive distance from the zeta pole. -/
theorem modelZeta_strip_bound {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 2*a ≤ w.re → w.re ≤ 1/4 →
      ‖riemannZeta (1-w)‖ ≤ B*(1+|w.im|)^(1/4:ℝ) := by
  let K := (Icc (3/4 : ℝ) (1-2*a)) ×ˢ Icc (-1 : ℝ) 1
  let f := fun p : ℝ × ℝ => riemannZeta ((p.1 : ℂ) + p.2 * I)
  have hc : ContinuousOn f K := by
    intro p hp
    have hne : (p.1 : ℂ) + p.2 * I ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
        neg_zero, add_zero, Complex.one_re] at hr
      linarith only [hp.1.2,hr,ha]
    exact ((differentiableAt_riemannZeta hne).continuousAt.comp (by fun_prop)).continuousWithinAt
  obtain ⟨D,hD⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max 26 D, (by norm_num : (0:ℝ)≤26).trans (le_max_left ..), ?_⟩
  intro w hlo hhi
  let z : ℂ := 1-w
  have hz : 3/4 ≤ z.re := by dsimp [z]; simp; linarith only [hhi]
  have hz' : z.re ≤ 1-2*a := by simpa [z] using sub_le_sub_left hlo 1
  have him : |z.im| = |w.im| := by simp [z]
  have hpow : 1 ≤ (1+|w.im|)^(1/4:ℝ) := Real.one_le_rpow (by linarith only [abs_nonneg w.im]) (by norm_num)
  change ‖riemannZeta z‖ ≤ _
  by_cases ht : 1 ≤ |z.im|
  · have hb := AbsoluteGeometryOfSpecZ.norm_zeta_le_ordinate_power_in_closed_strip
      (by norm_num : (0:ℝ)<3/4) (by norm_num : (3/4:ℝ)<1) hz (by linarith only [hz',ha]) ht
    norm_num only [show (22 + 1 / (1 - 3/4) : ℝ) = 26 by norm_num,
      show (1-3/4:ℝ) = 1/4 by norm_num, him] at hb
    exact hb.trans (mul_le_mul (le_max_left ..)
      (Real.rpow_le_rpow (abs_nonneg _) (by linarith only) (by norm_num)) (by positivity)
      (by positivity))
  · have hmem : (z.re,z.im) ∈ K := ⟨⟨hz,hz'⟩, abs_le.mp (le_of_not_ge ht)⟩
    have hb := hD (z.re,z.im) hmem
    simp only [f, Complex.re_add_im] at hb
    exact hb.trans ((le_max_right ..).trans (le_mul_of_one_le_right (by positivity) hpow))

/-- The factors separate the heights after the Gamma and zeta estimates. -/
theorem betaModel_strip_bound {N : ℕ} (hN : 4 ≤ N) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s z : ℂ, s.re ∈ Icc a (1/8) → z.re ∈ Icc a (1/8) →
      ‖betaModel N s z‖ ≤ B*((1+|s.im|)^(1/4:ℝ))*((1+|z.im|)^(1/4:ℝ)) := by
  obtain ⟨E,hE,he⟩ := densityEuler_norm_bound (a := 2*a) (by positivity)
  obtain ⟨G,hG,hg⟩ := signedBetaGammaFactor_strip_bound
  obtain ⟨Z,hZ,hzeta⟩ := modelZeta_strip_bound ha
  have hn : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hnp : 0 < (N:ℝ) := by linarith only [hn]
  refine ⟨singularSeries N * E * Z * G^2, by have := singularSeries_pos N; positivity, ?_⟩
  intro s z hs hz
  have hlo : 2*a ≤ (s+z).re := by rw [Complex.add_re]; linarith only [hs.1,hz.1]
  have hhi : (s+z).re ≤ 1/4 := by rw [Complex.add_re]; linarith only [hs.2,hz.2]
  have hp : ‖((Real.pi / N : ℝ) : ℂ)^(s+z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos Real.pi_pos hnp)]
    exact Real.rpow_le_one (div_nonneg Real.pi_pos.le hnp.le)
      ((div_le_one hnp).mpr (Real.pi_lt_four.le.trans hn)) (by linarith only [ha,hlo])
  have hab : 1 + |(s+z).im| ≤ (1+|s.im|)*(1+|z.im|) := by
    rw [Complex.add_im]
    linarith only [abs_add_le s.im z.im, mul_nonneg (abs_nonneg s.im) (abs_nonneg z.im)]
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1+|(s+z).im|) hab (by norm_num : (0:ℝ)≤1/4)
  rw [Real.mul_rpow (by positivity) (by positivity)] at hh
  have hZ' := (hzeta (s+z) hlo hhi).trans (mul_le_mul_of_nonneg_left hh hZ)
  simp only [betaModel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (singularSeries_pos _)]
  calc
    _ ≤ singularSeries N * 1 * E * (Z*((1+|s.im|)^(1/4:ℝ) * (1+|z.im|)^(1/4:ℝ))) * G * G := by
      gcongr
      · exact hp
      · exact he N _ hlo
      · exact hZ'
      · exact hg s (ha.le.trans hs.1) hs.2
      · exact hg z (ha.le.trans hz.1) hz.2
    _ = _ := by ring

#print axioms betaModel_strip_bound
end
end GaloisForLFunctions.Goldbach.LiLiu
