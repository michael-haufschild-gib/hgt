import GaloisForLFunctions.HTGeometry.EntireCompositionDecomposition
import GaloisForLFunctions.HTGeometry.LinearizedTowerCoherence

/-!
# The composition-decomposition law

If `φ` is nonconstant entire with nonvanishing realized derivative and both `φ` and `g ∘ φ` are
differentially algebraic, then so is `g`.

The witness families of the corpus supply finitely many elements over which every jet of `φ` and of
`g ∘ φ` is algebraic; `EntireCompositionDecomposition.differentiallyAlgebraicOfOrder_of_comp_witness`
then produces an algebraic differential equation for `g` whose order is bounded by the size of the
combined family.  The two instance stacks on the plane — the scoped `UnivMeroFieldInstances` one and
the inline one used by the witness-family theorem — are reconciled by `Algebra.algebra_ext`, since
both send a constant to its constant germ.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances Differential

/-- An algebraic witness extends along any family that restricts to the original one. -/
theorem AlgebraicWitness.extend {L : Type*} [Field L] {K : Type*} [Field K] [Algebra K L]
    {σ σ' : Type*} {b : σ → L} {y : L} (g : σ → σ') (s : σ' → L) (hs : s ∘ g = b)
    (h : AlgebraicWitness K b y) : AlgebraicWitness K s y := by
  obtain ⟨m, P, hlead, hrel⟩ := h
  refine ⟨m, fun i => MvPolynomial.rename g (P i), ?_, ?_⟩
  · rw [MvPolynomial.aeval_rename, hs]
    exact hlead
  · refine Eq.trans ?_ hrel
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.aeval_rename, hs]

set_option synthInstance.maxHeartbeats 800000 in
/-- **The composition-decomposition law.**  If `φ` is nonconstant entire with nonvanishing realized
derivative and both `φ` and `g ∘ φ` are differentially algebraic, then so is `g`. -/
theorem differentiallyAlgebraic_of_comp {g φ : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hφ : Differentiable ℂ φ)
    (hnc : ∀ c : ℂ, ∃ z, φ z ≠ c)
    (hφ' : analyticMeroElement (deriv φ)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hφ).deriv ≠ 0)
    (hφDA : DifferentiallyAlgebraicOn φ (Set.univ : Set ℂ))
    (hcDA : DifferentiallyAlgebraicOn (fun z => g (φ z)) (Set.univ : Set ℂ)) :
    DifferentiallyAlgebraic g := by
  classical
  have hφa : AnalyticOnNhd ℂ φ (Set.univ : Set ℂ) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hφ
  have hca : AnalyticOnNhd ℂ (fun z => g (φ z)) (Set.univ : Set ℂ) :=
    analyticOnNhd_iteratedDeriv_comp hg hφ 0
  obtain ⟨p, bφ, hbφ⟩ := exists_jet_algebraicWitness_family isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ hφa hφDA
  obtain ⟨q, bh, hbh⟩ := exists_jet_algebraicWitness_family isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ hca hcDA
  refine ⟨p + q, ?_⟩
  refine differentiallyAlgebraicOfOrder_of_comp_witness hg hφ hnc hφ'
    (I := Fin p ⊕ Fin q) (M := p + q) (Sum.elim bφ bh) (by simp) ?_
  intro x hx j
  rcases hx with hx | hx
  · subst hx
    have hjet : differentialJet j (analyticMeroElement φ hφa)
        = analyticMeroElement (iteratedDeriv j φ) (analyticOnNhd_iteratedDeriv hφa j) :=
      differentialJet_analyticMeroElement isOpen_univ isPreconnected_univ Set.univ_nonempty
        φ hφa j
    rw [hjet]
    refine AlgebraicWitness.extend Sum.inl (Sum.elim bφ bh) (by funext i; rfl) ?_
    convert hbφ j using 2
    all_goals first
      | rfl
      | exact Algebra.algebra_ext _ _ fun r => (ratfuncToMero_C_eq_constToMero r).symm
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hjet : differentialJet j (analyticMeroElement (fun z => iteratedDeriv 0 g (φ z)) hca)
        = analyticMeroElement (iteratedDeriv j (fun z => g (φ z)))
            (analyticOnNhd_iteratedDeriv hca j) :=
      differentialJet_analyticMeroElement isOpen_univ isPreconnected_univ Set.univ_nonempty
        (fun z => g (φ z)) hca j
    rw [hjet]
    refine AlgebraicWitness.extend Sum.inr (Sum.elim bφ bh) (by funext i; rfl) ?_
    convert hbh j using 2
    all_goals first
      | rfl
      | exact Algebra.algebra_ext _ _ fun r => (ratfuncToMero_C_eq_constToMero r).symm


end GaloisForLFunctions.HTGeometry
