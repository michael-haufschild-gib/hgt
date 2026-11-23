import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SeamDensity
import GaloisForLFunctions.HTGeometry.GaussianSmallBallLowerBound

/-! # Exponential radii suffice for exponentially weak boundary bonds -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- A strip of B^L independent bonds finds a guard of strength g^L
with prescribed failure probability, uniformly over its starting site. -/
theorem geometric_weak_guards {g η : ℝ} (hg : 0 < g) (hg₁ : g ≤ 1) (hη : 0 < η) :
    ∃ B : ℕ, 0 < B ∧ ∀ L : ℕ, 0 < L → ∀ j : ℕ,
      pathPauliDisorderLaw.real (absentStrip (g^L) (B^L) j) ≤ η := by
  let c := (2*gaussianDensityFloor)^9
  have hc : 0 < c := pow_pos (mul_pos (by norm_num) gaussianDensityFloor_pos) _
  let v := 1+|Real.log η|
  obtain ⟨B,hB⟩ := exists_nat_gt (max 1 (v/c)/g^9)
  have hb := (div_lt_iff₀ (pow_pos hg 9)).mp hB
  have hu : 1 ≤ (B:ℝ)*g^9 := (le_max_left ..).trans hb.le
  have hv : v ≤ c*((B:ℝ)*g^9) := by
    have hh := (div_le_iff₀ hc).mp ((le_max_right ..).trans hb.le)
    rwa [mul_comm c] 
  have hB₀ : 0<B := by
    by_contra! he
    have hzero : B=0 := Nat.eq_zero_of_le_zero he
    rw [hzero,Nat.cast_zero,zero_mul] at hu
    norm_num at hu
  refine ⟨B,hB₀,?_⟩
  intro L hL j
  obtain ⟨z,hz,hm,hstrip⟩ := gaussian_weak_strip_mass (pow_pos hg L)
  have h1 := ENNReal.toReal_mono (measure_ne_top _ _)
    (gaussianReal_Icc_lower (pow_le_one₀ hg.le hg₁ : g^L ≤ 1))
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (by positivity))] at h1
  have hm' : c*(g^9)^L ≤ 1-z := by
    rw [hm]
    have hh := pow_le_pow_left₀ (mul_nonneg gaussianDensityFloor_pos.le (by positivity)) h1 9
    apply le_trans (le_of_eq ?_) hh
    dsimp only [c]
    ring
  have hvol : v ≤ (1-z)*(B^L:ℕ) := by
    calc v ≤ c*((B:ℝ)*g^9) := hv
         _ ≤ c*((B:ℝ)*g^9)^L := mul_le_mul_of_nonneg_left (le_self_pow₀ hu hL.ne') hc.le
         _ = (c*(g^9)^L)*(B^L:ℕ) := by push_cast; rw [mul_pow]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg _)
  rw [absentStrip,hstrip _ (fun i => j+i.val) (fun _ _ he => Fin.ext (Nat.add_left_cancel he))]
  have he : z ≤ Real.exp (z-1) := by linarith only [Real.add_one_le_exp (z-1)]
  apply (pow_le_pow_left₀ hz.1 he (B^L)).trans
  rw [←Real.exp_nat_mul,←Real.exp_log hη]
  apply Real.exp_le_exp.mpr
  change 1+|Real.log η| ≤ (1-z)*(B^L:ℕ) at hvol
  nlinarith only [hvol,neg_abs_le (Real.log η)]

#print axioms geometric_weak_guards
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
