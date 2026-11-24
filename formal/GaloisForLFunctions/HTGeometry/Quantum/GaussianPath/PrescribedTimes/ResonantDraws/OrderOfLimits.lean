import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.HaarScale

/-! # Noncommuting time and size limits of the empty-circuit probability -/
open Filter MeasureTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open SharpOccupation
noncomputable section

private theorem haar_log_rate {x : ℝ} (hx : 0<x) :
    let D (k : ℕ) := (2:ℕ)^(k+3)
    Tendsto (fun k => log ((D k:ℝ)*x^(D k-1))/(D k:ℝ)) atTop (𝓝 (log x)) := by
  intro D
  have hd : Tendsto (fun k : ℕ => (D k:ℝ)) atTop atTop := by
    simpa only [D,Nat.cast_pow,Nat.cast_ofNat,Function.comp_apply] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp (tendsto_add_atTop_nat 3)
  have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hd).add
    ((hd.inv_tendsto_atTop.const_sub 1).mul_const (log x))
  simp only [sub_zero,one_mul,zero_add] at hh
  apply hh.congr
  intro k
  have hk : 1≤D k := Nat.one_le_two_pow
  have hD : 0<(D k:ℝ) := by exact_mod_cast hk
  change log (D k)/(D k:ℝ)+(1-(D k:ℝ)⁻¹)*log x=_
  rw [log_mul hD.ne' (pow_pos hx _).ne',log_pow,Nat.cast_sub hk,Nat.cast_one,add_div]
  congr 1
  rw [mul_div_right_comm,sub_div,div_self hD.ne',one_div]

/-- At fixed laboratory time the size limit of the log probability
per dimension is zero. Taking the time limit at fixed size first gives
the strictly negative log arc width when the prefix then grows. -/
theorem gaussian_scalar_time_size_limits :
    let D (k : ℕ) := (2:ℕ)^(k+3)
    let x := physicalArc (1/10)
    let f (k : ℕ) (t : ℝ) := log (prescribedScalarProbability (k+1) t)/(D k:ℝ)
    let l (k : ℕ) := log ((D k:ℝ)*x^(D k-1))/(D k:ℝ)
    (∀ t, Tendsto (fun k => f k t) atTop (𝓝 0)) ∧
    (∀ k, Tendsto (f k) atTop (𝓝 (l k))) ∧ Tendsto l atTop (𝓝 (log x)) ∧ log x<0 := by
  intro D x f l
  have he : (1/10:ℝ)<sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    nlinarith only [h,Real.sqrt_nonneg 2]
  have hx := (physicalArc_spec (by norm_num : (0:ℝ)<1/10) he).1
  have hx₀ : 0<x := hx.1
  refine ⟨fun t => ?_,fun k => ?_,haar_log_rate hx₀,log_neg hx₀ (hx.2.trans (by norm_num))⟩
  · have hd := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp (tendsto_add_atTop_nat 2)
    have hconst := hd.inv_tendsto_atTop.const_mul (log (1+|t|))
    have hh := gaussian_prescribed_scalar_before_haar (fun _ => t)
      (by simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using hconst)
    simpa only [f,D,Nat.cast_pow,Nat.cast_ofNat,Function.comp_apply] using hh.comp (tendsto_add_atTop_nat 1)
  · have hh := (gaussian_late_scalar_probability k 0 (by norm_num : (0:ℝ)<1/10) he).1
    have hp : 0 < (D k:ℝ)*x^(D k-1) := by dsimp only [D]; positivity
    exact (hh.log hp.ne').div_const _

#print axioms gaussian_scalar_time_size_limits
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
