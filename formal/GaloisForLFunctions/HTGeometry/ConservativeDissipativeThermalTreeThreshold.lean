import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalPopulationTree

/-!
# Exact physical-time threshold for measured tree response

The conservative–dissipative split of arXiv:2609.04530 supplies the exponential
survival realized by the thermal Kraus semigroup. Its measured tree response has
an exact critical time `log(n+1)/(2*exp(s)^(2 : ℕ))`. Positive rates and branch counts
are constructed from unrestricted coordinates. The below/at/above-one regimes
are proved for the actual analytic derivative, with no numerical computation.
-/

set_option autoImplicit false
open Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- The nonnegative physical time at which an `(n+1)`-branch population multiplier becomes one. -/
def spinTreeCriticalTime (s : ℝ) (n : ℕ) : NNReal :=
  ⟨Real.log ((n : ℝ) + 1) / (2 * (Real.exp s) ^ 2),
    div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])) (by positivity)⟩

/-- Exact rate-scaled critical time; its nonnegativity was constructed in the definition. -/
theorem spinTreeCriticalTime_scaled (s : ℝ) (n : ℕ) :
    2 * (Real.exp s) ^ 2 * (spinTreeCriticalTime s n : ℝ) = Real.log ((n : ℝ) + 1) := by
  change 2 * (Real.exp s) ^ 2 * (Real.log ((n : ℝ) + 1) / (2 * (Real.exp s) ^ 2)) = _
  field_simp

/-- The measured tree multiplier is an exponential distance from its critical time. -/
theorem spinThermalTree_multiplier_exp (s u : ℝ) (n : ℕ) (t : NNReal) :
    deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t) 0 =
      Real.exp (2 * (Real.exp s) ^ 2 * ((spinTreeCriticalTime s n : ℝ) - (t : ℝ))) := by
  rw [deriv_spinThermalTreeBP, spinDecayMass, mul_sub, spinTreeCriticalTime_scaled]
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity : 0 < (n : ℝ) + 1)]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2
  ring

/-- The unbiased message has derivative below one exactly after the physical critical time. -/
theorem spinThermalTree_multiplier_lt_one_iff (s u : ℝ) (n : ℕ) (t : NNReal) :
    deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t) 0 < 1 ↔ spinTreeCriticalTime s n < t := by
  rw [spinThermalTree_multiplier_exp, Real.exp_lt_one_iff]
  have hp : 0 < 2 * (Real.exp s) ^ 2 := by positivity
  change 2 * (Real.exp s) ^ 2 * ((spinTreeCriticalTime s n : ℝ) - (t : ℝ)) < 0 ↔ (spinTreeCriticalTime s n : ℝ) < (t : ℝ)
  simpa only [mul_zero, sub_neg] using (mul_lt_mul_iff_right₀ hp (b := (spinTreeCriticalTime s n : ℝ) - (t : ℝ)) (c := 0))

/-- Before that time the unbiased message has derivative greater than one. -/
theorem spinThermalTree_multiplier_one_lt_iff (s u : ℝ) (n : ℕ) (t : NNReal) :
    1 < deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t) 0 ↔ t < spinTreeCriticalTime s n := by
  rw [spinThermalTree_multiplier_exp, Real.one_lt_exp_iff]
  have hp : 0 < 2 * (Real.exp s) ^ 2 := by positivity
  rw [mul_pos_iff_of_pos_left hp, sub_pos]
  rfl

/-- Neutral linear response occurs at exactly one time for every constructed positive branching. -/
theorem spinThermalTree_multiplier_eq_one_iff (s u : ℝ) (n : ℕ) (t : NNReal) :
    deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t) 0 = 1 ↔ t = spinTreeCriticalTime s n := by
  rw [spinThermalTree_multiplier_exp, Real.exp_eq_one_iff]
  have hp : 2 * (Real.exp s) ^ 2 ≠ 0 := by positivity
  rw [mul_eq_zero, or_iff_right hp, sub_eq_zero]
  exact ⟨fun h => NNReal.eq (Eq.symm h), fun h => congrArg (fun v : NNReal => (v : ℝ)) h.symm⟩

/-- The zero-message response is always strictly positive for nonzero branching. -/
theorem spinThermalTree_multiplier_pos (s u : ℝ) (n : ℕ) (t : NNReal) :
    0 < deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t) 0 := by
  rw [spinThermalTree_multiplier_exp]
  exact Real.exp_pos _

/-- Longer channel evolution strictly decreases the tree's linear response. -/
theorem spinThermalTree_multiplier_strictAnti (s u : ℝ) (n : ℕ) :
    StrictAnti (fun t : NNReal => deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t) 0) := by
  intro t₁ t₂ ht
  change deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t₂) 0 < deriv (spinThermalTreeBP (n + 1) (Real.exp s) u t₁) 0
  rw [spinThermalTree_multiplier_exp, spinThermalTree_multiplier_exp, Real.exp_lt_exp]
  have hp : 0 < 2 * (Real.exp s) ^ 2 := by positivity
  apply mul_lt_mul_of_pos_left _ hp
  exact sub_lt_sub_left (show (t₁ : ℝ) < (t₂ : ℝ) from ht) _

/-- Tree sensitivity vanishes in the same positive-damping limit as quantum thermalization. -/
theorem spinThermalTree_multiplier_tendsto_zero (s u : ℝ) (p : ℕ) :
    Tendsto (fun t : NNReal => deriv (spinThermalTreeBP p (Real.exp s) u t) 0) atTop (nhds 0) := by
  simpa only [deriv_spinThermalTreeBP, mul_zero] using (spinDecayMass_tendsto_zero s).const_mul (p : ℝ)

end
end GaloisForLFunctions.HTGeometry.SchafferExl
