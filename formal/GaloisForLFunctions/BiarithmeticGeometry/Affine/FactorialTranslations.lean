import GaloisForLFunctions.HTGeometry.RationalDenominatorLadder
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A cofinal sequence of rational cyclic subgroups

The steps `1/n!` decrease to zero and every rational becomes an integral multiple of all sufficiently late steps.
-/

open Filter Topology
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A decreasing rational step whose cyclic subgroups exhaust the rationals. -/
def factorialTranslationStep (n : ℕ) : ℚ := (n.factorial : ℚ)⁻¹

theorem factorialTranslationStep_pos (n : ℕ) : 0 < factorialTranslationStep n := by
  apply inv_pos.mpr
  exact_mod_cast Nat.factorial_pos n

/-- Successive factorial steps enlarge the cyclic translation subgroup. -/
theorem factorialTranslationStep_eq_succ_mul (n : ℕ) :
    factorialTranslationStep n = (n + 1 : ℕ) * factorialTranslationStep (n + 1) := by
  simp only [factorialTranslationStep, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hn, hf]

/-- Every rational translation is eventually an integral multiple of the factorial step. -/
theorem eq_int_mul_factorialTranslationStep (q : ℚ) {n : ℕ} (hn : q.den ≤ n) :
    ∃ m : ℤ, q = (m : ℚ) * factorialTranslationStep n := by
  obtain ⟨m, hm⟩ := (HTGeometry.exists_intCast_natMul_iff_den_dvd
    (Nat.factorial_pos n) q).mpr (Nat.dvd_factorial q.den_pos hn)
  refine ⟨m, ?_⟩
  have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  change q = (m : ℚ) * (n.factorial : ℚ)⁻¹
  calc
    q = (q * (n.factorial : ℚ)) * (n.factorial : ℚ)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hf, mul_one]
    _ = (m : ℚ) * (n.factorial : ℚ)⁻¹ := by
      congr 1
      simpa only [mul_comm] using hm

/-- Nonnegative rational translations are eventually natural multiples of the factorial step. -/
theorem eq_nat_mul_factorialTranslationStep (q : ℚ) (hq : 0 ≤ q)
    {n : ℕ} (hn : q.den ≤ n) : ∃ m : ℕ, q = (m : ℚ) * factorialTranslationStep n := by
  obtain ⟨m, hm⟩ := eq_int_mul_factorialTranslationStep q hn
  have hmQ : (0 : ℚ) ≤ m := by
    have hstep := factorialTranslationStep_pos n
    by_contra h
    have hmneg : (m : ℚ) < 0 := lt_of_not_ge h
    have hneg := mul_neg_of_neg_of_pos hmneg hstep
    rw [← hm] at hneg
    exact (not_lt_of_ge hq) hneg
  have hmZ : (0 : ℤ) ≤ m := by exact_mod_cast hmQ
  lift m to ℕ using hmZ with a ha
  exact ⟨a, by simpa only [Int.cast_natCast] using hm⟩

/-- The factorial translation orbit of the identity column has length exactly `n!`. -/
theorem factorialTranslationStep_den (n : ℕ) : (factorialTranslationStep n).den = n.factorial := by
  rw [factorialTranslationStep, Rat.inv_natCast_den, if_neg (Nat.factorial_ne_zero n)]

theorem tendsto_factorialTranslationStep :
    Tendsto (fun n => (factorialTranslationStep n : ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, factorialTranslationStep, Rat.cast_inv, Rat.cast_natCast, one_div] using
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp factorial_tendsto_atTop

#print axioms eq_int_mul_factorialTranslationStep
#print axioms eq_nat_mul_factorialTranslationStep
#print axioms tendsto_factorialTranslationStep
end GaloisForLFunctions.BiarithmeticGeometry
