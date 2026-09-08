import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicHypergeometricAnalyticODE

/-! Spatial Gauss derivatives without a nontermination assumption. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every totalized Gauss series converges on the unit disk; terminating parameters are retained. -/
theorem hypergeometric_radius_one_le (a b c : ℂ) :
    1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
  by_cases ha : ∃ k : ℕ, a = -(k:ℂ)
  · obtain ⟨k,rfl⟩ := ha
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₁]; exact le_top
  by_cases hb : ∃ k : ℕ, b = -(k:ℂ)
  · obtain ⟨k,rfl⟩ := hb
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₂]; exact le_top
  by_cases hc : ∃ k : ℕ, c = -(k:ℂ)
  · obtain ⟨k,rfl⟩ := hc
    rw [ordinaryHypergeometric_radius_top_of_neg_nat₃]; exact le_top
  rw [ordinaryHypergeometricSeries_radius_eq_one]
  · intro k
    exact ⟨fun h => ha ⟨k,by linear_combination h⟩,
      fun h => hb ⟨k,by linear_combination h⟩, fun h => hc ⟨k,by linear_combination h⟩⟩

private theorem pochhammer_shift (a : ℂ) (n : ℕ) :
    (ascPochhammer ℂ (n+1)).eval a = a*(ascPochhammer ℂ n).eval (a+1) := by
  rw [ascPochhammer_succ_left]
  simp [Polynomial.eval_mul,Polynomial.eval_comp]

/-- Differentiated coefficients equal the shifted Gauss coefficients even at numerator zeros. -/
theorem hypergeometric_coefficient_shift (a b c : ℂ) (n : ℕ) :
    (n+1:ℂ)*ordinaryHypergeometricCoefficient a b c (n+1) =
      (a*b/c)*ordinaryHypergeometricCoefficient (a+1) (b+1) (c+1) n := by
  dsimp [ordinaryHypergeometricCoefficient]
  rw [pochhammer_shift,pochhammer_shift,pochhammer_shift,Nat.factorial_succ]
  push_cast
  have hn : (n+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [mul_inv_rev]
  field_simp [hn]

/-- The actual derivative-series sum has the shifted-parameter formula throughout the unit disk. -/
theorem hypergeometric_first_eq_shift (a b c z : ℂ) (hz : ‖z‖ₑ < 1) :
    RHTower.ordinaryHypergeometricFirstDerivativeSeriesValue a b c z =
      (a*b/c)*ordinaryHypergeometric (a+1) (b+1) (c+1) z := by
  have h1 := (RHTower.ordinaryHypergeometric_hasSum_value_first_second a b c z
    (hz.trans_le (hypergeometric_radius_one_le a b c))).2.1
  have h2 := ((RHTower.ordinaryHypergeometric_hasSum_value_first_second (a+1) (b+1) (c+1) z
    (hz.trans_le (hypergeometric_radius_one_le (a+1) (b+1) (c+1)))).1).mul_left (a*b/c)
  apply h1.unique
  convert! h2 using 1
  funext n
  simpa only [RHTower.ordinaryHypergeometricFormalCoefficient,Nat.cast_add,Nat.cast_one,mul_assoc] using
    congrArg (fun v : ℂ => v*z^n) (hypergeometric_coefficient_shift a b c n)

end
end GaloisForLFunctions.HTGeometry
