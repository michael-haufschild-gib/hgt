import GaloisForLFunctions.HTGeometry.CompositionJetBackward
import GaloisForLFunctions.HTGeometry.CompositionJetTrdeg
import GaloisForLFunctions.HTGeometry.TrdegMutuallyAlgebraic

/-!
# The finite-jet shadow law

For an autonomous first-order outer factor the jets of the composition and the coordinate generate a
field of transcendence degree exactly one more than the coordinate together with the *positive*
derivatives of the inner function: the outer cap adds one state and is blind to the primitive state
of its input.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The positive-index generators of the jet family are the jets of the inner function. -/
theorem jetGen_succ {g : ℂ → ℂ} (hg : Differentiable ℂ g) (n : ℕ) (j : Fin (n + 1)) :
    jetGen hg n j.succ = jetElem hg (j : ℕ) := by
  refine analyticMeroElement_congr _ _ ?_
  funext z
  simp [jetGenFun]

/-- Membership in a generated field gives algebraicity when the generators are algebraic. -/
theorem isAlgebraic_of_adjoin_of_generators
    (P : IntermediateField ℂ (meroField (Set.univ : Set ℂ)))
    (S : Set (meroField (Set.univ : Set ℂ))) (hS : ∀ w ∈ S, IsAlgebraic ↥P w)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ IntermediateField.adjoin ℂ S) :
    IsAlgebraic ↥P y := by
  have hle : IntermediateField.adjoin ℂ S
      ≤ (algebraicClosure ↥P (meroField (Set.univ : Set ℂ))).restrictScalars ℂ := by
    rw [IntermediateField.adjoin_le_iff]
    intro w hw
    exact mem_algebraicClosure_iff.mpr (hS w hw)
  exact mem_algebraicClosure_iff.mp (hle hy)

/-- Membership in the graded ring gives algebraicity when the generators are algebraic. -/
theorem isAlgebraic_of_gradedJetRing {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (P : IntermediateField ℂ (meroField (Set.univ : Set ℂ))) (m : ℕ)
    (hcj : ∀ i : ℕ, IsAlgebraic ↥P (compJetElem hf hg i))
    (hgj : ∀ j : ℕ, 1 ≤ j → j ≤ m → IsAlgebraic ↥P (jetElem hg j))
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ gradedJetRing hf hg m) :
    IsAlgebraic ↥P y := by
  have hle : gradedJetRing hf hg m
      ≤ ((algebraicClosure ↥P (meroField (Set.univ : Set ℂ))).restrictScalars ℂ).toSubalgebra := by
    refine Algebra.adjoin_le ?_
    rintro w (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_algebraicClosure_iff.mpr (hcj _)
    · exact mem_algebraicClosure_iff.mpr (hgj _ (by omega) (by omega))
  exact mem_algebraicClosure_iff.mp (hle hy)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The finite-jet shadow law.**  For a transcendental entire `f` satisfying an autonomous
first-order relation and a transcendental entire `g`, the coordinate together with the jets of
`f ∘ g` up to order `n` has transcendence degree one more than the coordinate together with the
derivatives of `g` of order `1` to `n`. -/
theorem trdeg_shadow_law {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (haut : AutonomousFirstOrder f) (hcomp : Differentiable ℂ (fun w => f (g w)))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (n : ℕ) :
    Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ
        (insert (jetGen hg n 0) (Set.range fun k : Fin (n + 1) => jetElem hcomp (k : ℕ))))
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ
        (insert (jetGen hg n 0)
          (Set.range fun j : Fin n => jetElem hg ((j : ℕ) + 1)))) + 1 := by
  classical
  have hcompan : AnalyticOnNhd ℂ (fun w => f (g w)) (Set.univ : Set ℂ) :=
    hcomp.differentiableOn.analyticOnNhd isOpen_univ
  set zE : meroField (Set.univ : Set ℂ) := jetGen hg n 0 with hzE
  set Sg : Set (meroField (Set.univ : Set ℂ)) :=
    insert zE (Set.range fun j : Fin n => jetElem hg ((j : ℕ) + 1)) with hSg
  set Sh : Set (meroField (Set.univ : Set ℂ)) :=
    insert zE (Set.range fun k : Fin (n + 1) => jetElem hcomp (k : ℕ)) with hSh
  set hE : meroField (Set.univ : Set ℂ) := jetElem hcomp 0 with hhE
  set C : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ Sg with hC
  set A : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ Sh with hA
  have hheq : hE = analyticMeroElement (fun w => f (g w)) hcompan := by
    rw [hhE, jetElem]
    exact analyticMeroElement_congr _ _ (by funext z; simp [iteratedDeriv_zero])
  -- the coordinate and the shadow jets sit inside the full jet family
  have hCle : C ≤ IntermediateField.adjoin ℂ (Set.range (jetGen hg n)) := by
    rw [hC, IntermediateField.adjoin_le_iff]
    rintro y (rfl | ⟨j, rfl⟩)
    · exact IntermediateField.subset_adjoin ℂ _ ⟨0, rfl⟩
    · refine IntermediateField.subset_adjoin ℂ _ ⟨(⟨(j : ℕ) + 1, by omega⟩ : Fin (n + 1)).succ, ?_⟩
      rw [jetGen_succ]
  -- the composition is transcendental over the shadow field
  have htrC : ¬ IsAlgebraic ↥C hE := by
    intro halg
    rw [hheq] at halg
    exact not_isAlgebraic_comp_over_jetGen hf hg hfnp hgnp n hcompan (isAlgebraic_of_le hCle halg)
  -- step one: adjoining the composition costs one degree
  have hstep1 : Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (insert hE Sg))
      = Algebra.trdeg ℂ ↥C + 1 := trdeg_adjoin_insert_eq_add_one htrC
  -- the composed jets are algebraic over both fields
  have hcjA : ∀ i : ℕ, IsAlgebraic ↥A (compJetElem hf hg i) := by
    intro i
    have halg := isAlgebraic_compJetElem_of_autonomous hf hg haut hcomp hncomp hncg i
    refine isAlgebraic_of_le ?_ halg
    rw [IntermediateField.adjoin_le_iff]
    rintro y rfl
    rw [hA]
    exact IntermediateField.subset_adjoin ℂ _ (Or.inr ⟨⟨0, by omega⟩, rfl⟩)
  have hcjB : ∀ i : ℕ, IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert hE Sg))
      (compJetElem hf hg i) := by
    intro i
    have halg := isAlgebraic_compJetElem_of_autonomous hf hg haut hcomp hncomp hncg i
    refine isAlgebraic_of_le ?_ halg
    rw [IntermediateField.adjoin_le_iff]
    rintro y rfl
    exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  -- step two: the two fields are mutually algebraic
  have hAB : ∀ y : meroField (Set.univ : Set ℂ), y ∈ A →
      IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert hE Sg)) y := by
    intro y hy
    rw [hA] at hy
    refine isAlgebraic_of_adjoin_of_generators _ Sh ?_ hy
    rintro w (rfl | ⟨k, rfl⟩)
    · refine isAlgebraic_algebraMap (⟨zE, ?_⟩ : ↥(IntermediateField.adjoin ℂ (insert hE Sg)))
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · refine isAlgebraic_of_gradedJetRing hf hg _ (k : ℕ) hcjB ?_
        (jetElem_comp_mem_gradedJetRing hf hg hcomp (k : ℕ))
      intro j hj1 hjk
      refine isAlgebraic_algebraMap
        (⟨jetElem hg j, ?_⟩ : ↥(IntermediateField.adjoin ℂ (insert hE Sg)))
      refine IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ?_)
      refine Set.mem_insert_of_mem _ ⟨⟨j - 1, by omega⟩, ?_⟩
      show jetElem hg ((j - 1) + 1) = jetElem hg j
      congr 1
      omega
  have hBA : ∀ y : meroField (Set.univ : Set ℂ),
      y ∈ IntermediateField.adjoin ℂ (insert hE Sg) → IsAlgebraic ↥A y := by
    intro y hy
    refine isAlgebraic_of_adjoin_of_generators _ (insert hE Sg) ?_ hy
    rintro w (rfl | rfl | ⟨j, rfl⟩)
    · refine isAlgebraic_algebraMap (⟨hE, ?_⟩ : ↥A)
      rw [hA]
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ⟨⟨0, by omega⟩, rfl⟩)
    · refine isAlgebraic_algebraMap (⟨zE, ?_⟩ : ↥A)
      rw [hA]
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
    · refine isAlgebraic_of_le ?_
        (isAlgebraic_jetElem_over_compJets hf hg haut hcomp hfnp hgnp hncomp hncg n
          ((j : ℕ) + 1) (by omega) (by omega))
      rw [hA, hSh]
      exact IntermediateField.adjoin.mono ℂ _ _ (Set.subset_insert _ _)
  have hstep2 : Algebra.trdeg ℂ ↥A
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (insert hE Sg)) :=
    trdeg_eq_of_mutually_algebraic hAB hBA
  rw [hstep2, hstep1]

end

end GaloisForLFunctions.HTGeometry
