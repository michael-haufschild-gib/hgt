import GaloisForLFunctions.HTGeometry.FirstOrderCompositionDefect

/-!
# The exact two-defect identity for a first-order entire composition

With `K = ℂ(z)⟨g′⟩`, `L = ℂ(z)⟨h⟩` for `h = f ∘ g`, and `N = K·L`, the tower formula splits the
transcendence degree of the compositum in two ways,

`trdeg_ℂ N = trdeg_ℂ L + λ`  and  `trdeg_ℂ N = trdeg_ℂ K + (1 + (1 − aut f)·π(g))`,

where `λ = trdeg_L N` is the shadow-recovery defect.  Equating them gives the two-defect identity of
the card: the differential rank of the composition is the shadow rank of the input plus one, minus
the primitive compression `aut(f)·π(g)` and minus the shadow loss `λ`.

Cardinal arithmetic has no subtraction and no cancellation, so the identity is stated in the
equivalent additive form `daRank h + λ = shadowRank g + (1 or 2)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### The relative transcendence degree -/

/-- The transcendence degree of one intermediate field over a smaller one. -/
def relTrdeg {F L : Type*} [Field F] [Field L] [Algebra F L] {A B : IntermediateField F L}
    (h : A ≤ B) : Cardinal :=
  letI : Algebra ↥A ↥B := (IntermediateField.inclusion h).toRingHom.toAlgebra
  Algebra.trdeg ↥A ↥B

theorem relTrdeg_eq_trdeg_extendScalars {F L : Type*} [Field F] [Field L] [Algebra F L]
    {A B : IntermediateField F L} (h : A ≤ B) :
    relTrdeg h = Algebra.trdeg ↥A ↥(IntermediateField.extendScalars h) := rfl

/-- **The tower formula.** -/
theorem trdeg_add_relTrdeg {F L : Type*} [Field F] [Field L] [Algebra F L]
    {A B : IntermediateField F L} (h : A ≤ B) :
    Algebra.trdeg F ↥A + relTrdeg h = Algebra.trdeg F ↥B := by
  letI : Algebra ↥A ↥B := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥A ↥B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul ↥A ↥B := (faithfulSMul_iff_algebraMap_injective ↥A ↥B).mpr
    (IntermediateField.inclusion h).injective
  exact trdeg_add_eq F ↥A (A := ↥B)

/-- The jet field of the composition sits inside the visibility field. -/
theorem jetField_le_visibilityField {g h : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ h) :
    IntermediateField.adjoin ℂ (compSet hcomp) ≤ visibilityField hg hcomp := by
  rw [IntermediateField.adjoin_le_iff]
  intro y hy
  exact IntermediateField.subset_adjoin ℂ _ (Or.inr hy)

/-- The shadow-recovery defect of a composition: the transcendence degree of the compositum over the
jet field of the composition. -/
def shadowLoss {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) : Cardinal :=
  relTrdeg (jetField_le_visibilityField hg hcomp)

theorem daRank_add_shadowLoss {f g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w)) :
    daRank hcomp + shadowLoss (f := f) hg hcomp
      = Algebra.trdeg ℂ ↥(visibilityField hg hcomp) :=
  trdeg_add_relTrdeg (jetField_le_visibilityField hg hcomp)

/-! ### The three regimes -/

/-- **Two-defect identity, autonomous outer factor.**  An autonomous cap adds exactly one state to
the shadow rank of its input, up to the shadow loss. -/
theorem two_defect_autonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (haut : AutonomousFirstOrder f) (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c) :
    daRank hcomp + shadowLoss (f := f) hg hcomp = shadowRank' hg + 1 :=
  (daRank_add_shadowLoss hg hcomp).trans
    (trdeg_visibilityField_autonomous hf hg haut hcomp hfnp hgnp hncomp)

/-- **Two-defect identity, primitive-rigid input.**  If the input is algebraic over its own shadow
field, a first-order cap again adds exactly one state. -/
theorem two_defect_primitive_rigid {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hfo : FirstOrderDA f)
    (hpi : IsAlgebraic ↥(IntermediateField.adjoin ℂ (shadowSet hg)) (jetElem hg 0)) :
    daRank hcomp + shadowLoss (f := f) hg hcomp = shadowRank' hg + 1 :=
  (daRank_add_shadowLoss hg hcomp).trans
    (trdeg_visibilityField_primitive_rigid hf hg hcomp hfnp hgnp hncg hncomp hfo hpi)

/-- **Two-defect identity, nonautonomous cap on a primitive-free input.**  Breaking autonomy keeps
the primitive state: the cap adds two. -/
theorem two_defect_nonautonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hfo : FirstOrderDA f) (hnaut : ¬ AutonomousFirstOrder f)
    (hpi : ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ (shadowSet hg)) (jetElem hg 0)) :
    daRank hcomp + shadowLoss (f := f) hg hcomp = shadowRank' hg + 2 :=
  (daRank_add_shadowLoss hg hcomp).trans
    (trdeg_visibilityField_nonautonomous hf hg hcomp hfnp hgnp hncg hncomp hfo hnaut hpi)

/-! ### An autonomous cap has no shadow loss -/

/-- **Under an autonomous cap the compositum is algebraic over the jet field of the composition.**
Every derivative of the inner function of positive order is algebraic over the composed jets. -/
theorem isAlgebraic_visibilityField_over_jetField {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c) (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    ∀ y : meroField (Set.univ : Set ℂ), y ∈ visibilityField hg hcomp →
      IsAlgebraic ↥(IntermediateField.adjoin ℂ (compSet hcomp)) y := by
  intro y hy
  refine isAlgebraic_of_adjoin_of_generators _ (shadowSet hg ∪ compSet hcomp) ?_ hy
  rintro w (hw | hw)
  · rcases hw with rfl | ⟨j, rfl⟩
    · exact isAlgebraic_algebraMap (⟨coordElem, IntermediateField.subset_adjoin ℂ _
        (Set.mem_insert _ _)⟩ : ↥(IntermediateField.adjoin ℂ (compSet hcomp)))
    · refine isAlgebraic_of_le ?_
        (isAlgebraic_jetElem_over_compJets hf hg haut hcomp hfnp hgnp hncomp hncg (j + 1)
          (j + 1) (by omega) (by omega))
      rw [IntermediateField.adjoin_le_iff]
      rintro z ⟨k, rfl⟩
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ⟨(k : ℕ), rfl⟩)
  · exact isAlgebraic_algebraMap
      (⟨w, IntermediateField.subset_adjoin ℂ _ hw⟩ :
        ↥(IntermediateField.adjoin ℂ (compSet hcomp)))

/-- **An autonomous cap loses no shadow states.** -/
theorem shadowLoss_eq_zero_of_autonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c) (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    shadowLoss (f := f) hg hcomp = 0 := by
  have halg := isAlgebraic_visibilityField_over_jetField hf hg haut hcomp hfnp hgnp hncomp hncg
  rw [shadowLoss, relTrdeg_eq_trdeg_extendScalars]
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℂ (compSet hcomp))
      ↥(IntermediateField.extendScalars (jetField_le_visibilityField hg hcomp)) := by
    refine ⟨fun x => ?_⟩
    have hx : IsAlgebraic ↥(IntermediateField.adjoin ℂ (compSet hcomp))
        ((x : meroField (Set.univ : Set ℂ))) := halg _ x.2
    have hinj : Function.Injective (algebraMap
        ↥(IntermediateField.extendScalars (jetField_le_visibilityField hg hcomp))
        (meroField (Set.univ : Set ℂ))) := Subtype.val_injective
    obtain ⟨p, hp0, hp⟩ := hx
    refine ⟨p, hp0, hinj ?_⟩
    rw [map_zero, ← hp]
    exact (Polynomial.aeval_algebraMap_apply (meroField (Set.univ : Set ℂ)) x p).symm
  exact trdeg_eq_zero

/-- **The autonomous order law, recovered.**  With no shadow loss the two-defect identity is the
autonomous cap law: the differential rank of the composition is the shadow rank of its input plus
one. -/
theorem daRank_eq_shadowRank_add_one_of_autonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ fun w => f (g w))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c) (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    daRank hcomp = shadowRank' hg + 1 := by
  have h := two_defect_autonomous hf hg haut hcomp hfnp hgnp hncomp
  rw [shadowLoss_eq_zero_of_autonomous hf hg haut hcomp hfnp hgnp hncomp hncg, add_zero] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
