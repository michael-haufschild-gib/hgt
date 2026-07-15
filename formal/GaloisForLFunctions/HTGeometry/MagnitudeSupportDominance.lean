import GaloisForLFunctions.HTGeometry.MagnitudeBalancedAtomExistence

/-!
# Support-restricted magnitude dominance

Zero grouped weights do not participate in a coefficient identity. These criteria
therefore require a valuation gap only against other nonzero weights, while retaining
the same total-mass domination bound. The integer form uses the unit lower bound for
a nonzero integer grouped weight.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

/-- The inhomogeneous coefficient survival criterion with the valuation gap restricted to
nonzero grouped weights. -/
theorem aeval_coeff_ne_zero_of_dominant_on_support (n N : ℕ) (F : ℂ⟦X⟧)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {b : ℕ → ℝ}
    (hb : ∀ i, ‖coeff i F‖ = Real.exp (- b i))
    (ν₀ : ℕ →₀ ℕ) (hν₀ : ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hw₀ : aevalWeight n N Q ν₀ ≠ 0) {G : ℝ}
    (hgap : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
        ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤
          ν.sum (fun i k => (k : ℝ) * b i))
    (hG : (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
        < ‖aevalWeight n N Q ν₀‖ * Real.exp G) :
    (coeff N) (aeval (formalJets n F) Q) ≠ 0 := by
  classical
  rw [coeff_aeval_regrouped_weight]
  rw [Finset.sum_congr rfl fun ν (_ : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) =>
    mul_comm (ν.prod (fun i j => (coeff i F) ^ j)) (aevalWeight n N Q ν)]
  exact weighted_sum_ne_zero_of_min_valuation_on_support _
    (fun ν => ν.sum (fun i k => (k : ℝ) * b i)) _
    (fun ν => norm_aval (f := F) hb ν) _ hν₀ hw₀ hgap hG

/-- Integer-normalized support-restricted dominance: zero grouped weights impose no valuation
condition, while a nonzero distinguished integer weight has norm at least one. -/
theorem aeval_coeff_ne_zero_of_int_dominant_on_support (n N : ℕ) (F : ℂ⟦X⟧)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {b : ℕ → ℝ}
    (hb : ∀ i, ‖coeff i F‖ = Real.exp (- b i))
    (hQ : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (ν₀ : ℕ →₀ ℕ) (hν₀ : ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hw₀ : aevalWeight n N Q ν₀ ≠ 0) {G : ℝ}
    (hgap : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
        ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤
          ν.sum (fun i k => (k : ℝ) * b i))
    (hmass : (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
      < Real.exp G) :
    (coeff N) (aeval (formalJets n F) Q) ≠ 0 := by
  refine aeval_coeff_ne_zero_of_dominant_on_support n N F Q hb ν₀ hν₀ hw₀ hgap ?_
  calc
    (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
        < Real.exp G := hmass
    _ = 1 * Real.exp G := (one_mul _).symm
    _ ≤ ‖aevalWeight n N Q ν₀‖ * Real.exp G := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg G)
      exact aevalWeight_norm_ge_one n N Q ν₀ hQ hw₀

end GaloisForLFunctions

