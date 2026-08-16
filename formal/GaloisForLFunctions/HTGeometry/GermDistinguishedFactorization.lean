import GaloisForLFunctions.HTGeometry.GermSliceRegular

/-!
# Factorizations of a distinguished polynomial are polynomial factorizations

A distinguished polynomial is characterized among monic polynomials by the vanishing of its
coefficients at the origin, equivalently by its image under the coefficientwise value map being
`X^d`.  In that form distinguishedness is visibly multiplicative.

If the germ of a distinguished polynomial factors in the germ ring, both factors are regular in the
distinguished coordinate — regularity is multiplicative — so both can be prepared.  The product of
their distinguished polynomials is distinguished and its germ differs from the original by a unit,
so the uniqueness of the preparation identifies it with the original polynomial: the factorization
descends to `ℂ{z'}[X]`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Filter Topology

variable {n : ℕ}

/-- The coefficientwise value map on polynomials over the parameter germ ring. -/
noncomputable abbrev germValueMap (n : ℕ) :
    AnalyticGerm (0 : Fin n → ℂ) →+* ℂ := analyticGermValue (0 : Fin n → ℂ)

/-- **A monic polynomial is its own distinguished normal form.** -/
theorem monic_eq_distPoly {P : Polynomial (AnalyticGerm (0 : Fin n → ℂ))} (hP : P.Monic) :
    P = distPoly P.natDegree (fun j => P.coeff j) := by
  refine Polynomial.ext fun m => ?_
  rw [distPoly, coeff_add, coeff_X_pow, lowDegreePoly_coeff]
  rcases lt_trichotomy m P.natDegree with hm | hm | hm
  · rw [if_neg (by omega), if_pos hm, zero_add]
  · rw [if_pos hm, if_neg (by omega), add_zero, hm]
    exact hP.coeff_natDegree
  · rw [if_neg (by omega), if_neg (by omega), add_zero]
    exact coeff_eq_zero_of_natDegree_lt hm

/-- **Distinguishedness in terms of the value map.** -/
theorem map_distPoly_eq_X_pow {d : ℕ} {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0) :
    (distPoly d α).map (germValueMap n) = Polynomial.X ^ d := by
  rw [distPoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
  have hlow : (lowDegreePoly α d).map (germValueMap n) = 0 := by
    refine Polynomial.ext fun m => ?_
    rw [coeff_map, lowDegreePoly_coeff, coeff_zero]
    by_cases hm : m < d
    · rw [if_pos hm]
      exact hzero m hm
    · rw [if_neg hm, map_zero]
  rw [hlow, add_zero]

theorem coeff_eq_zero_of_map_eq_X_pow {P : Polynomial (AnalyticGerm (0 : Fin n → ℂ))}
    (h : P.map (germValueMap n) = Polynomial.X ^ P.natDegree) :
    ∀ j, j < P.natDegree → germValueMap n (P.coeff j) = 0 := by
  intro j hj
  have := congrArg (fun p : Polynomial ℂ => p.coeff j) h
  simp only [coeff_map, coeff_X_pow] at this
  rw [this, if_neg (by omega)]

/-- **The product of two distinguished polynomials is distinguished.** -/
theorem coeff_mul_eq_zero_of_distinguished {d₁ d₂ : ℕ}
    {α₁ α₂ : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (h₁ : ∀ j, j < d₁ → germValueMap n (α₁ j) = 0)
    (h₂ : ∀ j, j < d₂ → germValueMap n (α₂ j) = 0) :
    ∀ j, j < (distPoly d₁ α₁ * distPoly d₂ α₂).natDegree →
      germValueMap n ((distPoly d₁ α₁ * distPoly d₂ α₂).coeff j) = 0 := by
  have hmul : (distPoly d₁ α₁ * distPoly d₂ α₂).natDegree = d₁ + d₂ := by
    rw [(distPoly_monic d₁ α₁).natDegree_mul (distPoly_monic d₂ α₂),
      natDegree_distPoly, natDegree_distPoly]
  refine coeff_eq_zero_of_map_eq_X_pow ?_
  rw [Polynomial.map_mul, map_distPoly_eq_X_pow h₁, map_distPoly_eq_X_pow h₂, hmul, pow_add]

theorem analyticGermValue_germEval_distPoly {d : ℕ} (hd : 0 < d)
    {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0) :
    analyticGermValue (0 : Fin (n + 1) → ℂ) (germEval n (distPoly d α)) = 0 := by
  rw [germEval_distPoly, map_add, map_pow, analyticGermValue_germCoord, zero_pow (by omega),
    zero_add, map_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [map_mul, analyticGermValue_germTail, hzero j (Finset.mem_range.mp hj), zero_mul]

theorem not_isUnit_germEval_distPoly {d : ℕ} (hd : 0 < d)
    {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0) :
    ¬ IsUnit (germEval n (distPoly d α)) := by
  intro hU
  rw [isUnit_analyticGerm_iff] at hU
  exact hU (analyticGermValue_germEval_distPoly hd hzero)

/-- **A germ-ring factorization of a distinguished polynomial descends to the polynomial ring.** -/
theorem exists_distPoly_factorization {d : ℕ}
    {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0)
    {g h : AnalyticGerm (0 : Fin (n + 1) → ℂ)}
    (hgh : germEval n (distPoly d α) = g * h) :
    ∃ (dG dH : ℕ) (αG αH : ℕ → AnalyticGerm (0 : Fin n → ℂ))
      (u v : AnalyticGerm (0 : Fin (n + 1) → ℂ)),
      (∀ j, j < dG → germValueMap n (αG j) = 0) ∧
      (∀ j, j < dH → germValueMap n (αH j) = 0) ∧
      IsUnit u ∧ IsUnit v ∧
      g = germEval n (distPoly dG αG) * u ∧ h = germEval n (distPoly dH αH) * v ∧
      distPoly d α = distPoly dG αG * distPoly dH αH := by
  classical
  have hreg : germSlice n (g * h) ≠ 0 := by
    rw [← hgh]
    exact germSlice_germEval_distPoly_ne_zero hzero
  obtain ⟨hgreg, hhreg⟩ := germSlice_ne_zero_of_mul_ne_zero hreg
  obtain ⟨G, hGA, hGeq⟩ := g.2
  obtain ⟨H, hHA, hHeq⟩ := h.2
  have hgeq : g = analyticGermOf hGA := Subtype.ext hGeq.symm
  have hheq : h = analyticGermOf hHA := Subtype.ext hHeq.symm
  have hGreg : ¬ (fun z : ℂ => G (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    rw [hgeq] at hgreg
    exact (germSlice_ne_zero_iff hGA).mp hgreg
  have hHreg : ¬ (fun z : ℂ => H (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    rw [hheq] at hhreg
    exact (germSlice_ne_zero_iff hHA).mp hhreg
  obtain ⟨dG, αG, u, hu, hzG, hGprep⟩ := germ_preparation_algebraic hGA hGreg
  obtain ⟨dH, αH, v, hv, hzH, hHprep⟩ := germ_preparation_algebraic hHA hHreg
  have hgP : g = germEval n (distPoly dG αG) * u := by
    rw [hgeq, hGprep, germEval_distPoly]
  have hhQ : h = germEval n (distPoly dH αH) * v := by
    rw [hheq, hHprep, germEval_distPoly]
  refine ⟨dG, dH, αG, αH, u, v, hzG, hzH, hu, hv, hgP, hhQ, ?_⟩
  -- the product of the two distinguished polynomials
  have hRmonic : (distPoly dG αG * distPoly dH αH).Monic :=
    (distPoly_monic dG αG).mul (distPoly_monic dH αH)
  have hRdeg : (distPoly dG αG * distPoly dH αH).natDegree = dG + dH := by
    rw [(distPoly_monic dG αG).natDegree_mul (distPoly_monic dH αH),
      natDegree_distPoly, natDegree_distPoly]
  have hRzero : ∀ j, j < (distPoly dG αG * distPoly dH αH).natDegree →
      germValueMap n ((distPoly dG αG * distPoly dH αH).coeff j) = 0 :=
    coeff_mul_eq_zero_of_distinguished hzG hzH
  have hRnorm : distPoly dG αG * distPoly dH αH
      = distPoly (dG + dH) (fun j => (distPoly dG αG * distPoly dH αH).coeff j) := by
    conv_lhs => rw [monic_eq_distPoly hRmonic]
    rw [hRdeg]
  have hRzero' : ∀ j, j < dG + dH →
      germValueMap n ((distPoly dG αG * distPoly dH αH).coeff j) = 0 := by
    intro j hj
    exact hRzero j (by rw [hRdeg]; exact hj)
  have hEval : germEval n (distPoly d α)
      = germEval n (distPoly (dG + dH) (fun j => (distPoly dG αG * distPoly dH αH).coeff j))
        * (u * v) := by
    rw [← hRnorm, hgh, hgP, hhQ, map_mul]
    ring
  have hunit : IsUnit (u * v) := hu.mul hv
  rw [hRnorm]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hone : distPoly 0 α = 1 := by
      rw [distPoly, lowDegreePoly, Finset.range_zero, Finset.sum_empty, pow_zero, add_zero]
    rw [hone] at hEval ⊢
    have hUnit : IsUnit (germEval n
        (distPoly (dG + dH) (fun j => (distPoly dG αG * distPoly dH αH).coeff j))) := by
      have h1 : IsUnit (germEval n (1 : Polynomial (AnalyticGerm (0 : Fin n → ℂ)))) := by
        rw [map_one]
        exact isUnit_one
      rw [hEval] at h1
      exact isUnit_of_mul_isUnit_left h1
    have hDzero : dG + dH = 0 := by
      by_contra hne
      exact not_isUnit_germEval_distPoly (Nat.pos_of_ne_zero hne) hRzero' hUnit
    rw [hDzero, distPoly, lowDegreePoly, Finset.range_zero, Finset.sum_empty, pow_zero, add_zero]
  · refine distPoly_eq_of_unit_mul hdpos ?_ hzero hRzero' hunit hEval
    by_contra hc
    have hDzero : dG + dH = 0 := by omega
    have hone : distPoly (dG + dH) (fun j => (distPoly dG αG * distPoly dH αH).coeff j) = 1 := by
      rw [hDzero, distPoly, lowDegreePoly, Finset.range_zero, Finset.sum_empty, pow_zero, add_zero]
    rw [hone, map_one, one_mul] at hEval
    refine not_isUnit_germEval_distPoly hdpos hzero ?_
    rw [hEval]
    exact hunit

end GaloisForLFunctions.HTGeometry
