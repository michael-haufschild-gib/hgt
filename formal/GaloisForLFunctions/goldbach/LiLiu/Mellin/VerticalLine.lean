import GaloisForLFunctions.goldbach.LiLiu.MellinWeight
import GaloisForLFunctions.RHTower.ZetaGaussianZeroSums

/-! # The real Mellin test on conjugate vertical lines -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set MetaplecticMobiusDescent.CubicEisenstein
open scoped ComplexConjugate
noncomputable section

def mellinLine (σ t : ℝ) : ℂ := (σ:ℂ)+t*I

def mellinMultiplier (N : ℕ) (φ : TestWeight) (s : ℂ) : ℂ :=
  (N:ℂ)^s * mellin (companion φ) s

theorem mellinLine_reflect {w : ℂ} {σ : ℝ} (hw : w.re = 2*σ) (t : ℝ) :
    mellinLine σ (w.im-t) = w - mellinLine σ t := by
  apply Complex.ext <;> simp [mellinLine,hw]
  all_goals ring

theorem mellin_companion_conj (φ : TestWeight) (s : ℂ) :
    mellin (companion φ) (conj s) = conj (mellin (companion φ) s) := by
  simp only [mellin, smul_eq_mul, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change (x:ℂ)^(conj s-1) * companion φ x = conj ((x:ℂ)^(s-1) * companion φ x)
  rw [map_mul, show conj s-1 = conj (s-1) by simp,
    _root_.RHTower.GaussZeroSum.ofReal_cpow_conj hx]
  simp [companion,Vstar]

theorem mellinMultiplier_conj (N : ℕ) (hN : 0 < N) (φ : TestWeight) (s : ℂ) :
    mellinMultiplier N φ (conj s) = conj (mellinMultiplier N φ s) := by
  rw [mellinMultiplier,mellinMultiplier,mellin_companion_conj,map_mul]
  congr 1
  simpa only [Complex.ofReal_natCast] using _root_.RHTower.GaussZeroSum.ofReal_cpow_conj
    (Nat.cast_pos.mpr hN) s

theorem mellinMultiplier_continuous (N : ℕ) (hN : 0 < N) (φ : TestWeight) :
    Continuous (mellinMultiplier N φ) :=
  (continuous_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))).mul
    (mellin_companion_differentiable φ).continuous

theorem mellinMultiplier_integrable (N : ℕ) (hN : 0 < N) (φ : TestWeight) (σ : ℝ) :
    Integrable (fun t => mellinMultiplier N φ (mellinLine σ t)) := by
  have hm := compactMellin_vertical_integrable _ _ _ (by norm_num)
    (companion_support φ) (companion_smooth φ) σ
  simpa only [mellinMultiplier,mellinLine,Complex.ofReal_natCast] using
    vertical_power_mul_integrable _ hm (N:ℝ) σ (Nat.cast_pos.mpr hN)

/-- A quarter-power of height can be absorbed on either Mellin contour. -/
theorem mellinMultiplier_quarter_integrable (N : ℕ) (hN : 0 < N) (φ : TestWeight) (σ : ℝ) :
    Integrable (fun t : ℝ => (1+|t|)^(1/4:ℝ) * ‖mellinMultiplier N φ (mellinLine σ t)‖) := by
  obtain ⟨D,hD,hd⟩ := compact_source_mellin_strip_decay _ _ _ (by norm_num)
    (companion_support φ) (companion_smooth φ) σ σ 3
  have hc : Continuous (mellinLine σ) := by unfold mellinLine; fun_prop
  have hv := ((mellinMultiplier_continuous N hN φ).comp hc).norm
  have hq : Continuous (fun t : ℝ => (1+|t|)^(1/4:ℝ)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp (by fun_prop)
  let P := (N:ℝ)^σ
  have hP : 0 < P := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  apply (integrable_inv_one_add_sq.const_mul (P*D)).mono' (hq.mul hv).aestronglyMeasurable
  filter_upwards with t
  let r := 1+|t|
  have hr : 1 ≤ r := by dsimp [r]; linarith only [abs_nonneg t]
  have hq' : r^(1/4:ℝ) ≤ r := (Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1/4:ℝ) ≤ 1)).trans_eq
    (Real.rpow_one r)
  have hsq : 1+t^2 ≤ r^2 := by dsimp [r]; nlinarith only [sq_abs t,abs_nonneg t]
  have hM : r^3 * ‖mellin (companion φ) (mellinLine σ t)‖ ≤ D := hd σ ⟨le_rfl,le_rfl⟩ t
  have hpow : ‖(N:ℂ)^mellinLine σ t‖ = P := by simp [mellinLine,P,Complex.norm_natCast_cpow_of_pos hN]
  change ‖(1+|t|)^(1/4:ℝ) * ‖mellinMultiplier N φ (mellinLine σ t)‖‖ ≤ P*D*(1+t^2)⁻¹
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)),
    ← div_eq_mul_inv,le_div_iff₀ (by positivity),mellinMultiplier,norm_mul,hpow]
  calc
    _ ≤ r*(P*‖mellin (companion φ) (mellinLine σ t)‖)*r^2 := by gcongr
    _ = P*(r^3 * ‖mellin (companion φ) (mellinLine σ t)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM hP.le

#print axioms mellin_companion_conj
end
end GaloisForLFunctions.Goldbach.LiLiu
