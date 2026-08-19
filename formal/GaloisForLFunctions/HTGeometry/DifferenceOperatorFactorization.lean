import GaloisForLFunctions.HTGeometry.DifferenceCompanionCasoratian
import GaloisForLFunctions.HTGeometry.BesselOrderRiccati

/-!
# Factoring a second-order difference operator is solving its Riccati equation

A second-order difference operator over a difference field factors into two first-order operators
exactly when its Riccati equation has a solution in the field.  So a proof that the Riccati equation
has no solution is a proof that the operator is irreducible, which is what forces the difference
Galois group of the equation to be large.

The reverse implication is the coefficient comparison; it needs the difference operator to be
nontrivial, since for the identity shift every operator degenerates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- A first-order difference operator `y ↦ σ y - r y`. -/
def firstOrderOp (σ : K →+* K) (r y : K) : K := σ y - r * y

/-- A second-order difference operator in normal form. -/
def secondOrderOp (σ : K →+* K) (a₁ a₀ y : K) : K := σ (σ y) - a₁ * σ y - a₀ * y

/-- **A Riccati solution factors the operator.** -/
theorem secondOrderOp_eq_comp (σ : K →+* K) (a₁ a₀ r : K)
    (hr : σ r * r = a₁ * r + a₀) (y : K) :
    secondOrderOp σ a₁ a₀ y = firstOrderOp σ (a₁ - σ r) (firstOrderOp σ r y) := by
  simp only [firstOrderOp, secondOrderOp, map_sub, map_mul]
  linear_combination y * hr

/-- **A factorization solves the Riccati equation.** -/
theorem riccati_of_secondOrderOp_eq_comp (σ : K →+* K) {z : K} (hz : σ z ≠ z)
    {a₁ a₀ r s : K}
    (h : ∀ y : K, secondOrderOp σ a₁ a₀ y = firstOrderOp σ s (firstOrderOp σ r y)) :
    σ r * r = a₁ * r + a₀ := by
  have h1 := h 1
  have h2 := h z
  simp only [secondOrderOp, firstOrderOp, map_one, map_sub, map_mul, mul_one] at h1 h2
  have hQ : (a₀ + s * r) * (σ z - z) = 0 := by linear_combination h2 - σ z * h1
  have hsr : a₀ + s * r = 0 := by
    rcases mul_eq_zero.mp hQ with hcase | hcase
    · exact hcase
    · exact absurd (sub_eq_zero.mp hcase) hz
  have hRs : σ r + s = a₁ := by linear_combination h1 + hsr
  linear_combination r * hRs - hsr

/-- **Factorization is exactly the Riccati equation.** -/
theorem exists_factorization_iff_exists_riccati (σ : K →+* K) {z : K} (hz : σ z ≠ z)
    (a₁ a₀ : K) :
    (∃ r s : K, ∀ y : K,
        secondOrderOp σ a₁ a₀ y = firstOrderOp σ s (firstOrderOp σ r y)) ↔
      ∃ r : K, σ r * r = a₁ * r + a₀ := by
  constructor
  · rintro ⟨r, s, h⟩
    exact ⟨r, riccati_of_secondOrderOp_eq_comp σ hz h⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, a₁ - σ r, secondOrderOp_eq_comp σ a₁ a₀ r hr⟩

/-! ### The Bessel order recurrence is irreducible over the rational functions -/

theorem ratShift_ratFuncX_ne :
    ratShift (RatFunc.X : RatFunc ℂ) ≠ (RatFunc.X : RatFunc ℂ) := by
  have hX : ratShift (RatFunc.X : RatFunc ℂ)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X + Polynomial.C 1) := by
    rw [← RatFunc.algebraMap_X, ratShift_algebraMap]
    congr 1
    simp
  rw [hX, ← RatFunc.algebraMap_X]
  intro hcon
  have h1 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 1) = 0 := by
    have hthis := hcon
    rw [map_add] at hthis
    have hcancel : algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C 1)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X + 0 := by
      rw [add_zero]
      exact hthis
    exact add_left_cancel hcancel
  have h2 : (Polynomial.C (1 : ℂ)) = 0 :=
    RatFunc.algebraMap_injective ℂ (by rw [h1, map_zero])
  simp at h2

/-- **The Bessel order recurrence has no first-order factorization over `ℂ(X)`.**  Combined with
`exists_factorization_iff_exists_riccati`, the rational-Riccati obstruction of the corpus becomes
an irreducibility theorem for the order recurrence: no first-order right factor exists, so the
difference module of the recurrence is irreducible. -/
theorem besselOrderOperator_no_factorization {c : ℂ} (hc : c ≠ 0) :
    ¬ ∃ r s : RatFunc ℂ, ∀ y : RatFunc ℂ,
      secondOrderOp ratShift
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C c * (Polynomial.X + Polynomial.C 1))) 1 y
        = firstOrderOp ratShift s (firstOrderOp ratShift r y) := by
  rintro ⟨r, s, h⟩
  have hric := riccati_of_secondOrderOp_eq_comp ratShift ratShift_ratFuncX_ne h
  exact orderBesselRiccati_no_ratFunc_solution hc ⟨r, by linear_combination hric⟩

/-- The physical specialization: for every positive Bessel argument the order recurrence is
irreducible over `ℂ(X)`. -/
theorem modifiedBesselOrderOperator_no_factorization {s : ℝ} (hs : 0 < s) :
    ¬ ∃ r t : RatFunc ℂ, ∀ y : RatFunc ℂ,
      secondOrderOp ratShift
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (2 / (s : ℂ)) * (Polynomial.X + Polynomial.C 1))) 1 y
        = firstOrderOp ratShift t (firstOrderOp ratShift r y) := by
  apply besselOrderOperator_no_factorization
  exact div_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt hs)


end

end GaloisForLFunctions.HTGeometry
