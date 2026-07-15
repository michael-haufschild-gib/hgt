import GaloisForLFunctions.RHTower.GaussComponentCriticalPower

namespace RHTower

open Complex Filter Topology

noncomputable section

/-- Sampling the critical Gauss-component magnitude at the prime logarithmic lattice leaves the
exact local scale `log p`. -/
theorem gaussComponentVerticalMagnitude_primeSample_tendsto
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun n : ℕ =>
      (gaussComponentVerticalMagnitude k
        (2 * Real.pi * (n : ℝ) / Real.log (p : ℝ))) ^ (2 * m) * (n : ℝ))
      atTop (nhds (Real.log (p : ℝ))) := by
  have hlog : 0 < Real.log ((p : Nat.Primes) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hsample : Tendsto
      (fun n : ℕ => 2 * Real.pi * (n : ℝ) / Real.log (p : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < 2 * Real.pi)).atTop_div_const
      hlog
  have hcritical :=
    (gaussComponentVerticalMagnitude_pow_mul_tendsto hm k).comp hsample
  have hscaled := hcritical.mul_const (Real.log (p : ℝ) / (2 * Real.pi))
  have hlimit :
      (2 * Real.pi) * (Real.log (p : ℝ) / (2 * Real.pi)) = Real.log (p : ℝ) := by
    field_simp
  rw [hlimit] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with n
  simp only [Function.comp_apply]
  field_simp

end

end RHTower
