import GaloisForLFunctions.HTGeometry.CompositionShadowLawConsequences

/-!
# The composition is transcendental over the whole jet field of its inner factor

Clunie's composition-growth theorem gives transcendence of `f ∘ g` over each finite jet field of
`g`; the finite jet fields are directed, so an algebraic relation over their union would already be
one over a finite stage.  Hence `f ∘ g` is transcendental over `ℂ(z)⟨g⟩` and, a fortiori, over the
shadow field `ℂ(z)⟨g′⟩`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-- **The composition is transcendental over the full jet field of the inner function.** -/
theorem not_isAlgebraic_comp_over_jetField {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) :
    ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ
      (insert coordElem (Set.range fun k : ℕ => jetElem hg k))) (jetElem hcomp 0) := by
  classical
  have hcompan : AnalyticOnNhd ℂ (fun w => f (g w)) (Set.univ : Set ℂ) :=
    hcomp.differentiableOn.analyticOnNhd isOpen_univ
  have hheq : jetElem hcomp 0 = analyticMeroElement (fun w => f (g w)) hcompan := by
    rw [jetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [iteratedDeriv_zero])
  set St : ℕ → Set (meroField (Set.univ : Set ℂ)) :=
    fun n => insert coordElem (Set.range fun j : Fin (n + 1) => jetElem hg (j : ℕ)) with hSt
  have hmono : Monotone St := by
    intro m n hmn y hy
    rcases hy with rfl | ⟨j, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨⟨(j : ℕ), lt_of_lt_of_le j.2 (by omega)⟩, rfl⟩
  have hunion : (⋃ n, St n)
      = insert coordElem (Set.range fun k : ℕ => jetElem hg k) := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      rcases hn with rfl | ⟨j, rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨(j : ℕ), rfl⟩
    · rintro (rfl | ⟨k, rfl⟩)
      · exact Set.mem_iUnion.mpr ⟨0, Set.mem_insert _ _⟩
      · exact Set.mem_iUnion.mpr ⟨k, Set.mem_insert_of_mem _ ⟨⟨k, by omega⟩, rfl⟩⟩
  intro halg
  rw [← hunion] at halg
  obtain ⟨n, hn⟩ := exists_isAlgebraic_stage hmono halg
  have hle : IntermediateField.adjoin ℂ (St n)
      ≤ IntermediateField.adjoin ℂ (Set.range (jetGen hg n)) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | ⟨j, rfl⟩)
    · exact IntermediateField.subset_adjoin ℂ _ ⟨0, jetGen_zero_eq_coordElem hg n⟩
    · refine IntermediateField.subset_adjoin ℂ _ ⟨(⟨(j : ℕ), j.2⟩ : Fin (n + 1)).succ, ?_⟩
      rw [jetGen_succ]
  rw [hheq] at hn
  exact not_isAlgebraic_comp_over_jetGen hf hg hfnp hgnp n hcompan (isAlgebraic_of_le hle hn)

/-- **The composition is transcendental over the shadow field of the inner function.** -/
theorem not_isAlgebraic_comp_over_shadowField {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) :
    ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ
      (insert coordElem (Set.range fun j : ℕ => jetElem hg (j + 1)))) (jetElem hcomp 0) := by
  intro halg
  refine not_isAlgebraic_comp_over_jetField hf hg hcomp hfnp hgnp (isAlgebraic_of_le ?_ halg)
  rw [IntermediateField.adjoin_le_iff]
  rintro y (rfl | ⟨j, rfl⟩)
  · exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  · exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ⟨j + 1, rfl⟩)

end

end GaloisForLFunctions.HTGeometry
