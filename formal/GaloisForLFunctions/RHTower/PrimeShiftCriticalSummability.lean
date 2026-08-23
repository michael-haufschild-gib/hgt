import GaloisForLFunctions.RHTower.PrimeShiftCharacterBasic
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic

/-!
# Critical summability of normalized prime-shift characters

The right-half prime coefficient estimate is independent of the later
residue-domain and closability construction.
-/

noncomputable section

namespace RHTower

open Filter Complex
open scoped Topology BigOperators

/-- A normalized prime-shift character has critical summable absolute field
strictly to the right of the critical line. -/
theorem memCriticalSummableLayer_absField_primeShiftCharacter {z : ℂ} (hz : 1 / 2 < z.re) :
    MemCriticalSummableLayer (absField (primeShiftCharacter z)) := by
  have hsigma : (1 : ℝ) < 1 / 2 + z.re := by linarith
  have hbase := HTGeometry.summable_log_pow_div_nat_rpow 1 hsigma
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · refine Set.indicator_nonneg (fun m _ => ?_) n
    have : (0 : ℝ) ≤ Real.log m / (m : ℝ) :=
      div_nonneg (Real.log_natCast_nonneg m) (Nat.cast_nonneg m)
    positivity
  · by_cases hp : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
      have hnorm : absField (primeShiftCharacter z) n = (n : ℝ) ^ ((1 : ℝ) / 2 - z.re) := by
        rw [absField, primeShiftCharacter, if_pos hp, Complex.norm_natCast_cpow_of_pos hp.pos]
        congr 1
        simp
      rw [hnorm, abs_of_nonneg (Real.rpow_nonneg hnpos.le _), pow_one]
      have h1 : ((n : ℝ)) ^ (-(1 : ℝ)) = ((n : ℝ))⁻¹ := by
        rw [Real.rpow_neg hnpos.le, Real.rpow_one]
      calc Real.log n / (n : ℝ) * ((n : ℝ)) ^ ((1 : ℝ) / 2 - z.re)
          = Real.log n * (((n : ℝ)) ^ (-(1 : ℝ)) * ((n : ℝ)) ^ ((1 : ℝ) / 2 - z.re)) := by
            rw [h1]
            ring
        _ = Real.log n * ((n : ℝ)) ^ (-(1 : ℝ) + ((1 : ℝ) / 2 - z.re)) := by
            rw [← Real.rpow_add hnpos]
        _ = Real.log n * ((n : ℝ)) ^ (-((1 : ℝ) / 2 + z.re)) := by
            congr 1
            ring_nf
        _ = Real.log n / ((n : ℝ)) ^ ((1 : ℝ) / 2 + z.re) := by
            rw [Real.rpow_neg hnpos.le, div_eq_mul_inv]
            ring_nf
        _ ≤ Real.log n / ((n : ℝ)) ^ ((1 : ℝ) / 2 + z.re) := le_rfl
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
      positivity

end RHTower

end
