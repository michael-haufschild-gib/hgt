import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal

/-!
# The critical period rescaling is a constraint-preserving diagonal automorphism

Passing from the integral period edge `x_j = T_{τ_j} - 1` to the critically normalised edge
`y_j = x_j / τ_j` is, after complex scalar extension, the diagonal algebra automorphism
`X j ↦ τ_j⁻¹ • X j`.  This file proves that it is an automorphism and that it preserves the
Stanley--Reisner constraint ideal of any facet family: the rescaling compares the physical period
edge with the closed facet edge without moving the constraint locus.

The rescaling is genuinely non-integral — it exists only after adjoining the inverse periods — so
the integral and critical analytic realisations are different objects on the same constraint
scheme.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- The diagonal rescaling endomorphism `X i ↦ c i • X i`. -/
def periodRescalingHom (c : α → ℂ) : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial α ℂ :=
  aeval fun i => c i • (X i : MvPolynomial α ℂ)

omit [DecidableEq α] in
@[simp] theorem periodRescalingHom_X (c : α → ℂ) (i : α) :
    periodRescalingHom c (X i) = c i • (X i : MvPolynomial α ℂ) := by
  simp [periodRescalingHom]

omit [DecidableEq α] in
theorem periodRescalingHom_comp (c d : α → ℂ) :
    (periodRescalingHom c).comp (periodRescalingHom d)
      = periodRescalingHom (fun i => c i * d i) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [periodRescalingHom, smul_smul, mul_comm]

omit [DecidableEq α] in
theorem periodRescalingHom_one : periodRescalingHom (fun _ : α => (1 : ℂ)) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [periodRescalingHom]

/-- **The critical rescaling is an algebra automorphism** once every period is invertible. -/
def periodRescaling (c : α → ℂ) (hc : ∀ i, c i ≠ 0) :
    MvPolynomial α ℂ ≃ₐ[ℂ] MvPolynomial α ℂ :=
  AlgEquiv.ofAlgHom (periodRescalingHom c) (periodRescalingHom fun i => (c i)⁻¹)
    (by
      rw [periodRescalingHom_comp]
      refine Eq.trans ?_ periodRescalingHom_one
      congr 1
      funext i
      exact mul_inv_cancel₀ (hc i))
    (by
      rw [periodRescalingHom_comp]
      refine Eq.trans ?_ periodRescalingHom_one
      congr 1
      funext i
      exact inv_mul_cancel₀ (hc i))

omit [DecidableEq α] in
@[simp] theorem periodRescaling_apply (c : α → ℂ) (hc : ∀ i, c i ≠ 0) (p : MvPolynomial α ℂ) :
    periodRescaling c hc p = periodRescalingHom c p := rfl

/-! ### The rescaling scales every squarefree monomial -/

omit [DecidableEq α] in
theorem periodRescalingHom_monomial (c : α → ℂ) (e : α →₀ ℕ) :
    periodRescalingHom c (monomial e (1 : ℂ))
      = C (∏ i ∈ e.support, c i ^ e i) * monomial e (1 : ℂ) := by
  have hprod : (∏ i ∈ e.support, (c i • (X i : MvPolynomial α ℂ)) ^ e i)
      = C (∏ i ∈ e.support, c i ^ e i) * ∏ i ∈ e.support, (X i : MvPolynomial α ℂ) ^ e i := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [smul_pow, smul_eq_C_mul, map_pow]
  rw [periodRescalingHom, aeval_monomial, map_one, one_mul, Finsupp.prod, hprod,
    monomial_eq, map_one, one_mul, Finsupp.prod]

/-! ### Invariance of the constraint ideal -/

omit [DecidableEq α] in
theorem periodRescalingHom_stanleyReisnerIdeal_le (facets : Finset (Finset α)) (c : α → ℂ) :
    Ideal.map (periodRescalingHom c : MvPolynomial α ℂ →+* MvPolynomial α ℂ)
        (stanleyReisnerIdeal ℂ facets)
      ≤ stanleyReisnerIdeal ℂ facets := by
  rw [stanleyReisnerIdeal, Ideal.map_span, Ideal.span_le]
  rintro q ⟨g, hg, rfl⟩
  obtain ⟨e, he, rfl⟩ := hg
  show periodRescalingHom c (monomial e (1 : ℂ)) ∈ _
  rw [periodRescalingHom_monomial]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e, he, rfl⟩)

omit [DecidableEq α] in
/-- **The critical rescaling preserves the Stanley--Reisner constraint ideal.** -/
theorem periodRescaling_stanleyReisnerIdeal (facets : Finset (Finset α)) (c : α → ℂ)
    (hc : ∀ i, c i ≠ 0) :
    Ideal.map ((periodRescaling c hc : MvPolynomial α ℂ ≃ₐ[ℂ] MvPolynomial α ℂ) :
        MvPolynomial α ℂ →+* MvPolynomial α ℂ) (stanleyReisnerIdeal ℂ facets)
      = stanleyReisnerIdeal ℂ facets := by
  refine le_antisymm (periodRescalingHom_stanleyReisnerIdeal_le facets c) ?_
  intro p hp
  have hinv : periodRescalingHom (fun i => (c i)⁻¹) p ∈ stanleyReisnerIdeal ℂ facets :=
    periodRescalingHom_stanleyReisnerIdeal_le facets (fun i => (c i)⁻¹)
      (Ideal.mem_map_of_mem _ hp)
  have hback : periodRescalingHom c (periodRescalingHom (fun i => (c i)⁻¹) p) = p := by
    have h := periodRescalingHom_comp c (fun i => (c i)⁻¹)
    have hfun : (fun i => c i * (c i)⁻¹) = fun _ : α => (1 : ℂ) := by
      funext i; exact mul_inv_cancel₀ (hc i)
    have : (periodRescalingHom c).comp (periodRescalingHom fun i => (c i)⁻¹)
        = AlgHom.id ℂ _ := by rw [h, hfun, periodRescalingHom_one]
    calc periodRescalingHom c (periodRescalingHom (fun i => (c i)⁻¹) p)
        = ((periodRescalingHom c).comp (periodRescalingHom fun i => (c i)⁻¹)) p := rfl
      _ = p := by rw [this]; rfl
  rw [← hback]
  exact Ideal.mem_map_of_mem _ hinv

end GaloisForLFunctions.HTGeometry
