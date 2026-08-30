import GaloisForLFunctions.HTGeometry.FirstOrderCompositionRelation
import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed
import GaloisForLFunctions.HTGeometry.AutonomousCompJet
import GaloisForLFunctions.HTGeometry.CompositionShadowLaw
import GaloisForLFunctions.HTGeometry.DifferentialFieldLocus
import GaloisForLFunctions.HTGeometry.GaussianOrderLedger

/-!
# Relative visibility of a composition over the shadow field of its inner factor

Write `K = ℂ(z)⟨g′⟩` for the shadow field of `g`, `L = ℂ(z)⟨f ∘ g⟩` for the jet field of the
composition, and `N = K·L` for the compositum.  Clunie growth makes `f ∘ g` transcendental over `K`,
so `trdeg_K N ≥ 1`; the question is whether the jets of the composition contribute more.

If the derivative `a = f′ ∘ g` is algebraic over a field containing `K` and `f ∘ g`, then every jet
of the composition is algebraic over that field, because the relative algebraic closure of a field
whose elements have algebraic derivatives is closed under the derivation.  An autonomous outer
constraint provides exactly that: `a` is algebraic over `ℂ[f ∘ g]`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### Derivatives inside a relative algebraic closure -/

/-- If the derivative of every element of `P` is algebraic over `P`, so is the derivative of every
element algebraic over `P`. -/
theorem deriv_isAlgebraic_of_isAlgebraic {P : IntermediateField ℂ (meroField (Set.univ : Set ℂ))}
    (hP : ∀ y ∈ P, IsAlgebraic ↥P y′) {x : meroField (Set.univ : Set ℂ)}
    (hx : IsAlgebraic ↥P x) : IsAlgebraic ↥P x′ := by
  have hE : ∀ y : meroField (Set.univ : Set ℂ),
      y ∈ (⊥ : IntermediateField ↥P (meroField (Set.univ : Set ℂ))) →
      y′ ∈ algebraicClosure ↥P (meroField (Set.univ : Set ℂ)) := by
    intro y hy
    rw [IntermediateField.mem_bot] at hy
    obtain ⟨w, rfl⟩ := hy
    exact mem_algebraicClosure_iff.mpr (hP _ w.2)
  exact mem_algebraicClosure_iff.mp
    (deriv_mem_algebraicClosure hE (mem_algebraicClosure_iff.mpr hx))

/-- Generators whose members and derivatives are algebraic make every element of the generated field
have an algebraic derivative. -/
theorem deriv_isAlgebraic_of_generators {S : Set (meroField (Set.univ : Set ℂ))}
    (hgen : ∀ x ∈ S, IsAlgebraic ↥(IntermediateField.adjoin ℂ S) x
      ∧ IsAlgebraic ↥(IntermediateField.adjoin ℂ S) x′) :
    ∀ y ∈ IntermediateField.adjoin ℂ S, IsAlgebraic ↥(IntermediateField.adjoin ℂ S) y′ := by
  set P : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ S with hP
  set M : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    (algebraicClosure ↥P (meroField (Set.univ : Set ℂ))).restrictScalars ℂ with hM
  have hbase : ∀ c : ℂ, (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ ∈ M := by
    intro c
    rw [meroField_deriv_algebraMap_complex_rationalBase]
    exact zero_mem _
  have hgen' : ∀ x ∈ S, x ∈ M ∧ x′ ∈ M := by
    intro x hx
    exact ⟨mem_algebraicClosure_iff.mpr (hgen x hx).1,
      mem_algebraicClosure_iff.mpr (hgen x hx).2⟩
  have hle := adjoin_le_derivStableField (C := ℂ) (L := M) (hbase := hbase) hgen'
  intro y hy
  exact mem_algebraicClosure_iff.mp (mem_derivStableField_iff.mp (hle hy)).2

/-- Every jet of an entire function is algebraic over a field that contains the function itself and
whose elements have algebraic derivatives. -/
theorem forall_isAlgebraic_jetElem {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    {P : IntermediateField ℂ (meroField (Set.univ : Set ℂ))}
    (hP : ∀ y ∈ P, IsAlgebraic ↥P y′) (h0 : jetElem hu 0 ∈ P) (k : ℕ) :
    IsAlgebraic ↥P (jetElem hu k) := by
  induction k with
  | zero => exact isAlgebraic_algebraMap (⟨jetElem hu 0, h0⟩ : ↥P)
  | succ k ih =>
      rw [← deriv_jetElem hu k]
      exact deriv_isAlgebraic_of_isAlgebraic hP ih

/-! ### The generating sets -/

/-- The shadow generating set of the inner function: the coordinate and all derivatives of positive
order. -/
def shadowSet {g : ℂ → ℂ} (hg : Differentiable ℂ g) : Set (meroField (Set.univ : Set ℂ)) :=
  insert coordElem (Set.range fun j : ℕ => jetElem hg (j + 1))

/-- The jet generating set of the composition. -/
def compSet {h : ℂ → ℂ} (hcomp : Differentiable ℂ h) : Set (meroField (Set.univ : Set ℂ)) :=
  insert coordElem (Set.range fun k : ℕ => jetElem hcomp k)

theorem coordElem_mem_shadowSet {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    coordElem ∈ shadowSet hg := Set.mem_insert _ _

theorem jetElem_succ_mem_shadowSet {g : ℂ → ℂ} (hg : Differentiable ℂ g) (j : ℕ) :
    jetElem hg (j + 1) ∈ shadowSet hg := Set.mem_insert_of_mem _ ⟨j, rfl⟩

/-- The compositum of the shadow field of the inner function and the jet field of the
composition. -/
def visibilityField {g h : ℂ → ℂ} (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ h) :
    IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  IntermediateField.adjoin ℂ (shadowSet hg ∪ compSet hcomp)

/-! ### The visibility field is mutually algebraic with `K(h)` -/

/-- Every element of `K(h)` has an algebraic derivative, once the first jet of the composition does.
-/
theorem deriv_isAlgebraic_compAdjoin {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hderiv : IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)))
      (jetElem hcomp 1)) :
    ∀ y ∈ IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)),
      IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg))) y′ := by
  set Kh : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)) with hKh
  have hh0 : jetElem hcomp 0 ∈ Kh := IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  have hcoord : coordElem ∈ Kh :=
    IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hjg : ∀ j : ℕ, jetElem hg (j + 1) ∈ Kh := fun j =>
    IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨j, rfl⟩))
  rw [hKh]
  refine deriv_isAlgebraic_of_generators ?_
  rintro x (rfl | rfl | ⟨j, rfl⟩)
  · exact ⟨isAlgebraic_algebraMap (⟨_, hh0⟩ : ↥Kh), by
      rw [deriv_jetElem hcomp 0]
      exact hderiv⟩
  · refine ⟨isAlgebraic_algebraMap (⟨_, hcoord⟩ : ↥Kh), ?_⟩
    rw [deriv_coordElem]
    exact isAlgebraic_algebraMap (⟨(1 : meroField (Set.univ : Set ℂ)), one_mem _⟩ : ↥Kh)
  · refine ⟨isAlgebraic_algebraMap (⟨_, hjg j⟩ : ↥Kh), ?_⟩
    rw [deriv_jetElem hg (j + 1)]
    exact isAlgebraic_algebraMap (⟨_, hjg (j + 1)⟩ : ↥Kh)

/-- **The visibility field is algebraic over `K(h)`** as soon as the first jet of the composition
is. -/
theorem isAlgebraic_visibilityField_over_compAdjoin {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hderiv : IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)))
      (jetElem hcomp 1)) :
    ∀ y : meroField (Set.univ : Set ℂ), y ∈ visibilityField hg hcomp →
      IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg))) y := by
  set Kh : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)) with hKh
  have hh0 : jetElem hcomp 0 ∈ Kh := IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  have hcoord : coordElem ∈ Kh :=
    IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hjg : ∀ j : ℕ, jetElem hg (j + 1) ∈ Kh := fun j =>
    IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨j, rfl⟩))
  have hPderiv := deriv_isAlgebraic_compAdjoin hg hcomp hderiv
  intro y hy
  refine isAlgebraic_of_adjoin_of_generators Kh (shadowSet hg ∪ compSet hcomp) ?_ hy
  rintro w (hw | hw)
  · rcases hw with rfl | ⟨j, rfl⟩
    · exact isAlgebraic_algebraMap (⟨_, hcoord⟩ : ↥Kh)
    · exact isAlgebraic_algebraMap (⟨_, hjg j⟩ : ↥Kh)
  · rcases hw with rfl | ⟨k, rfl⟩
    · exact isAlgebraic_algebraMap (⟨_, hcoord⟩ : ↥Kh)
    · exact forall_isAlgebraic_jetElem hcomp hPderiv hh0 k

/-- `K(h)` sits inside the visibility field. -/
theorem compAdjoin_le_visibilityField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) :
    IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg))
      ≤ visibilityField hg hcomp := by
  rw [IntermediateField.adjoin_le_iff]
  rintro w (rfl | hw)
  · exact IntermediateField.subset_adjoin ℂ _ (Or.inr (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
  · exact IntermediateField.subset_adjoin ℂ _ (Or.inl hw)

theorem isAlgebraic_compAdjoin_over_visibilityField {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) :
    ∀ y : meroField (Set.univ : Set ℂ),
      y ∈ IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)) →
      IsAlgebraic ↥(visibilityField hg hcomp) y := fun y hy =>
  isAlgebraic_algebraMap (⟨y, compAdjoin_le_visibilityField hg hcomp hy⟩ :
    ↥(visibilityField hg hcomp))

/-- **The compositum collapses to `K(h)` as soon as the outer derivative is algebraic over it.** -/
theorem trdeg_visibilityField_eq_of_isAlgebraic_deriv {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hderiv : IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)))
      (jetElem hcomp 1)) :
    Algebra.trdeg ℂ ↥(visibilityField hg hcomp)
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (shadowSet hg)) + 1 := by
  have htr : ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ (shadowSet hg)) (jetElem hcomp 0) :=
    not_isAlgebraic_comp_over_shadowField hf hg hcomp hfnp hgnp
  have hstep1 : Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ
      (insert (jetElem hcomp 0) (shadowSet hg)))
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (shadowSet hg)) + 1 :=
    trdeg_adjoin_insert_eq_add_one htr
  have hEq := trdeg_eq_of_mutually_algebraic
    (isAlgebraic_visibilityField_over_compAdjoin hg hcomp hderiv)
    (isAlgebraic_compAdjoin_over_visibilityField hg hcomp)
  rw [hEq, hstep1]

/-! ### The autonomous case -/

/-- **An autonomous outer constraint makes the composed derivative algebraic over `K(h)`.** -/
theorem isAlgebraic_jetElem_comp_one_of_autonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c) :
    IsAlgebraic ↥(IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)))
      (jetElem hcomp 1) := by
  set Kh : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ (insert (jetElem hcomp 0) (shadowSet hg)) with hKh
  have hh0 : jetElem hcomp 0 ∈ Kh := IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  have hjg1 : jetElem hg 1 ∈ Kh :=
    IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨0, rfl⟩))
  -- the composed derivative is algebraic over the ring generated by the composition
  have h1 := isAlgebraic_compJetElem_one hf hg haut hcomp hncomp
  have h2 : IsAlgebraic ↥(IntermediateField.adjoin ℂ
      ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ)))) (compJetElem hf hg 1) :=
    GaloisForLFunctions.isAlgebraic_intermediateField_of_isAlgebraic_algebraAdjoin _ h1
  have hle : IntermediateField.adjoin ℂ
      ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ))) ≤ Kh := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y rfl
    exact hh0
  have h3 : IsAlgebraic ↥Kh (compJetElem hf hg 1) := isAlgebraic_of_le hle h2
  -- the chain rule
  have hchain : jetElem hcomp 1 = compJetElem hf hg 1 * jetElem hg 1 := by
    have h := deriv_compJetElem hf hg 0
    rw [compJetElem_zero hf hg hcomp, deriv_jetElem hcomp 0] at h
    exact h
  rw [hchain]
  have hmem : compJetElem hf hg 1 * jetElem hg 1
      ∈ algebraicClosure ↥Kh (meroField (Set.univ : Set ℂ)) :=
    mul_mem (mem_algebraicClosure_iff.mpr h3)
      (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨_, hjg1⟩ : ↥Kh)))
  exact mem_algebraicClosure_iff.mp hmem

/-- **Relative visibility, autonomous case.**  An autonomous first-order outer factor contributes
exactly one transcendence degree over the shadow field of its input. -/
theorem trdeg_visibilityField_autonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c) :
    Algebra.trdeg ℂ ↥(visibilityField hg hcomp)
      = Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ (shadowSet hg)) + 1 :=
  trdeg_visibilityField_eq_of_isAlgebraic_deriv hf hg hcomp hfnp hgnp
    (isAlgebraic_jetElem_comp_one_of_autonomous hf hg haut hcomp hncomp)

end

end GaloisForLFunctions.HTGeometry
