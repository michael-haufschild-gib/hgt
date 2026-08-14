import GaloisForLFunctions.HTGeometry.NewtonIrrationalLevelVertex

/-!
# The leading vertex of a composition

Composing two Euler-form operators convolves their shift polynomials,

```text
(Ψ ⋆ Φ)_ν = ∑_{a + b = ν} Ψ_a(X + b) · Φ_b(X) ,
```

and the substitution `X ↦ X + b` changes neither the degree nor the leading coefficient.  Two
consequences organise the Newton polygon of a product.

* Every monomial of the convolution is dominated by a sum of monomials of the factors, so the
  weighted level is subadditive.
* At an **irrational** level the leading vertices of the two factors are unique, and the single
  product term that reaches their sum cannot be cancelled by any other: all other pairs have
  strictly smaller weighted level, hence strictly smaller degree at the same shift.  The leading
  coefficient of the convolution at that shift is therefore the product of the two leading
  coefficients.

This is the multiplicativity that a factorization of an operator along its Newton polygon has to
respect, and it is where irrationality of the level removes the degeneracy that the classical
theory otherwise has to resolve by hand.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### Translating the argument of a polynomial -/

theorem natDegree_comp_X_add_C (p : Polynomial ℂ) (c : ℂ) :
    (p.comp (Polynomial.X + Polynomial.C c)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp]
  simp

theorem leadingCoeff_comp_X_add_C (p : Polynomial ℂ) (c : ℂ) :
    (p.comp (Polynomial.X + Polynomial.C c)).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (by simp)]
  simp

theorem comp_X_add_C_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (c : ℂ) :
    p.comp (Polynomial.X + Polynomial.C c) ≠ 0 := by
  intro hc
  apply hp
  have h := leadingCoeff_comp_X_add_C p c
  rw [hc, Polynomial.leadingCoeff_zero] at h
  exact Polynomial.leadingCoeff_eq_zero.mp h.symm

/-! ### Subadditivity of the degree -/

theorem natDegree_shiftComp_le_of_bound {Ψ Φ : ℕ → Polynomial ℂ} {ν D : ℕ}
    (h : ∀ a b : ℕ, a + b = ν → Ψ a ≠ 0 → Φ b ≠ 0 →
      (Ψ a).natDegree + (Φ b).natDegree ≤ D) :
    (shiftComp Ψ Φ ν).natDegree ≤ D := by
  classical
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
  have hbν : b ≤ ν := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  by_cases hΨ : Ψ (ν - b) = 0
  · rw [hΨ]
    simp
  by_cases hΦ : Φ b = 0
  · rw [hΦ]
    simp
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [natDegree_comp_X_add_C]
  exact h (ν - b) b (by omega) hΨ hΦ

/-! ### The leading vertex of a convolution -/

/-- **At an irrational level the leading vertex of a composition is the sum of the leading vertices
of the factors**, and its leading coefficient is the product of theirs. -/
theorem coeff_shiftComp_leading {r : ℝ} (hr : Irrational r) {Ψ Φ : ℕ → Polynomial ℂ} {a b : ℕ}
    (hΨmax : ∀ a', Ψ a' ≠ 0 → weightedLevel r Ψ a' ≤ weightedLevel r Ψ a)
    (hΦmax : ∀ b', Φ b' ≠ 0 → weightedLevel r Φ b' ≤ weightedLevel r Φ b) :
    (shiftComp Ψ Φ (a + b)).coeff ((Ψ a).natDegree + (Φ b).natDegree)
      = (Ψ a).leadingCoeff * (Φ b).leadingCoeff := by
  classical
  set D : ℕ := (Ψ a).natDegree + (Φ b).natDegree with hD
  have hbmem : b ∈ Finset.range (a + b + 1) := Finset.mem_range.mpr (by omega)
  rw [shiftComp, Polynomial.finsetSum_coeff, Finset.sum_eq_single b]
  · have hidx : a + b - b = a := by omega
    rw [hidx]
    have hdeg : ((Ψ a).comp (Polynomial.X + Polynomial.C ((b : ℕ) : ℂ))).natDegree
        = (Ψ a).natDegree := natDegree_comp_X_add_C _ _
    have hcoef := Polynomial.coeff_mul_degree_add_degree
      ((Ψ a).comp (Polynomial.X + Polynomial.C ((b : ℕ) : ℂ))) (Φ b)
    rw [hdeg] at hcoef
    rw [hD, hcoef, leadingCoeff_comp_X_add_C]
  · intro c hc hcb
    have hcν : c ≤ a + b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    by_cases hΨc : Ψ (a + b - c) = 0
    · rw [hΨc]
      simp
    by_cases hΦc : Φ c = 0
    · rw [hΦc]
      simp
    have hane : a + b - c ≠ a := by
      intro hcc
      exact hcb (by omega)
    have h1 : weightedLevel r Ψ (a + b - c) < weightedLevel r Ψ a := by
      rcases lt_or_eq_of_le (hΨmax _ hΨc) with h | h
      · exact h
      · exact absurd (weightedLevel_injective_of_irrational hr Ψ h) hane
    have h2 : weightedLevel r Φ c < weightedLevel r Φ b := by
      rcases lt_or_eq_of_le (hΦmax _ hΦc) with h | h
      · exact h
      · exact absurd (weightedLevel_injective_of_irrational hr Φ h) hcb
    have hcast : ((a + b - c : ℕ) : ℝ) + ((c : ℕ) : ℝ) = ((a : ℕ) : ℝ) + ((b : ℕ) : ℝ) := by
      have : ((a + b - c) + c : ℕ) = a + b := by omega
      have hr' : (((a + b - c) + c : ℕ) : ℝ) = ((a + b : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hr' ⊢
      linarith
    have hdeglt : (Ψ (a + b - c)).natDegree + (Φ c).natDegree < D := by
      have hsum : (((Ψ (a + b - c)).natDegree : ℕ) : ℝ) + (((Φ c).natDegree : ℕ) : ℝ)
          < (((Ψ a).natDegree : ℕ) : ℝ) + (((Φ b).natDegree : ℕ) : ℝ) := by
        rw [weightedLevel, weightedLevel] at h1
        rw [weightedLevel, weightedLevel] at h2
        have hrcast : r * (((a + b - c : ℕ) : ℝ)) + r * (((c : ℕ) : ℝ))
            = r * (((a : ℕ) : ℝ)) + r * (((b : ℕ) : ℝ)) := by
          rw [← mul_add, ← mul_add, hcast]
        linarith [h1, h2, hrcast]
      rw [hD]
      exact_mod_cast hsum
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    refine lt_of_le_of_lt (le_trans Polynomial.natDegree_mul_le ?_) hdeglt
    rw [natDegree_comp_X_add_C]
  · intro hcon
    exact absurd hbmem hcon

/-- The convolution does not vanish at the sum of the leading vertices. -/
theorem shiftComp_leading_ne_zero {r : ℝ} (hr : Irrational r) {Ψ Φ : ℕ → Polynomial ℂ} {a b : ℕ}
    (hΨa : Ψ a ≠ 0) (hΦb : Φ b ≠ 0)
    (hΨmax : ∀ a', Ψ a' ≠ 0 → weightedLevel r Ψ a' ≤ weightedLevel r Ψ a)
    (hΦmax : ∀ b', Φ b' ≠ 0 → weightedLevel r Φ b' ≤ weightedLevel r Φ b) :
    shiftComp Ψ Φ (a + b) ≠ 0 := by
  intro hz
  have h := coeff_shiftComp_leading hr hΨmax hΦmax
  rw [hz, Polynomial.coeff_zero] at h
  have hΨl : (Ψ a).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hΨa
  have hΦl : (Φ b).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hΦb
  exact (mul_ne_zero hΨl hΦl) h.symm

/-- **The degree of the convolution at the leading shift is the sum of the two degrees.** -/
theorem natDegree_shiftComp_leading {r : ℝ} (hr : Irrational r) {Ψ Φ : ℕ → Polynomial ℂ} {a b : ℕ}
    (hΨa : Ψ a ≠ 0) (hΦb : Φ b ≠ 0)
    (hΨmax : ∀ a', Ψ a' ≠ 0 → weightedLevel r Ψ a' ≤ weightedLevel r Ψ a)
    (hΦmax : ∀ b', Φ b' ≠ 0 → weightedLevel r Φ b' ≤ weightedLevel r Φ b) :
    (shiftComp Ψ Φ (a + b)).natDegree = (Ψ a).natDegree + (Φ b).natDegree := by
  classical
  refine le_antisymm ?_ ?_
  · refine natDegree_shiftComp_le_of_bound fun a' b' hab hΨ' hΦ' => ?_
    by_cases hcase : a' = a ∧ b' = b
    · rw [hcase.1, hcase.2]
    · have hne : a' ≠ a ∨ b' ≠ b := by
        by_contra hc
        push Not at hc
        exact hcase ⟨hc.1, hc.2⟩
      have hboth : a' ≠ a ∧ b' ≠ b := by
        rcases hne with h | h
        · exact ⟨h, fun hc => h (by omega)⟩
        · exact ⟨fun hc => h (by omega), h⟩
      have h1 : weightedLevel r Ψ a' < weightedLevel r Ψ a := by
        rcases lt_or_eq_of_le (hΨmax _ hΨ') with h | h
        · exact h
        · exact absurd (weightedLevel_injective_of_irrational hr Ψ h) hboth.1
      have h2 : weightedLevel r Φ b' < weightedLevel r Φ b := by
        rcases lt_or_eq_of_le (hΦmax _ hΦ') with h | h
        · exact h
        · exact absurd (weightedLevel_injective_of_irrational hr Φ h) hboth.2
      have hcast : ((a' : ℕ) : ℝ) + ((b' : ℕ) : ℝ) = ((a : ℕ) : ℝ) + ((b : ℕ) : ℝ) := by
        have hr' : (((a' + b' : ℕ)) : ℝ) = ((a + b : ℕ) : ℝ) := by exact_mod_cast hab
        push_cast at hr' ⊢
        linarith
      have hsum : (((Ψ a').natDegree : ℕ) : ℝ) + (((Φ b').natDegree : ℕ) : ℝ)
          < (((Ψ a).natDegree : ℕ) : ℝ) + (((Φ b).natDegree : ℕ) : ℝ) := by
        rw [weightedLevel, weightedLevel] at h1
        rw [weightedLevel, weightedLevel] at h2
        have hrcast : r * (((a' : ℕ) : ℝ)) + r * (((b' : ℕ) : ℝ))
            = r * (((a : ℕ) : ℝ)) + r * (((b : ℕ) : ℝ)) := by
          rw [← mul_add, ← mul_add, hcast]
        linarith [h1, h2, hrcast]
      have : (Ψ a').natDegree + (Φ b').natDegree < (Ψ a).natDegree + (Φ b).natDegree := by
        exact_mod_cast hsum
      omega
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [coeff_shiftComp_leading hr hΨmax hΦmax]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hΨa)
      (Polynomial.leadingCoeff_ne_zero.mpr hΦb)

end GaloisForLFunctions.HTGeometry
