import Mathlib.Algebra.Group.Hom.End
import Mathlib.Tactic.Abel

/-!
# Cohomological degree lowering and exact global recovery

A normalized additive two-cocycle canonically becomes a one-cocycle with values in coinduced
functions modulo constants.  An additive reporter that kills exactly constants, intertwines right
translation, and is onto preserves this degree lowering without information loss: if the reported
one-cocycle is a coboundary, then the original two-cocycle is a coboundary.
-/

namespace GaloisForLFunctions.HTGeometry

variable {G A H : Type*} [AddCommGroup G] [AddCommGroup A] [AddCommGroup H]

/-- Additive two-cocycle law used by cohomological packet formation. -/
def IsCohomologicalFormationTwoCocycle (c : G → G → A) : Prop :=
  ∀ x g h, c x g + c (x + g) h = c g h + c x (g + h)

/-- Left normalization of a formation two-cocycle. -/
def IsCohomologicalLeftNormalized (c : G → G → A) : Prop := ∀ g, c 0 g = 0

/-- Additive two-coboundary with the convention used by the formation law. -/
def cohomologicalFormationTwoCoboundary (φ : G → A) (g h : G) : A :=
  φ h - φ (g + h) + φ g

/-- On an abelian source, every formation two-coboundary is symmetric. -/
theorem cohomologicalFormationTwoCoboundary_comm (φ : G → A) (g h : G) :
    cohomologicalFormationTwoCoboundary φ g h =
      cohomologicalFormationTwoCoboundary φ h g := by
  simp only [cohomologicalFormationTwoCoboundary, add_comm]
  abel

/-- Right translation of a coinduced function. -/
def coinducedFormationRightTranslate (g : G) (f : G → A) : G → A :=
  fun x => f (x + g)

/-- Constant coinduced function. -/
def coinducedFormationConstant (a : A) : G → A := fun _ => a

/-- Canonical degree-lowering transgression of a two-cochain. -/
def coinducedFormationTransgression (c : G → G → A) (g : G) : G → A :=
  fun x => c x g

/-- Left normalization and the cocycle law force right normalization. -/
theorem cohomologicalTwoCocycle_right_normalized_of_left
    {c : G → G → A} (hc : IsCohomologicalFormationTwoCocycle c)
    (hc0 : IsCohomologicalLeftNormalized c) (x : G) :
    c x 0 = 0 := by
  have h := hc x 0 0
  simp only [add_zero] at h
  rw [hc0 0] at h
  apply add_left_cancel (a := c x 0)
  simpa using h

/-- Exact degree-lowering identity: the two-cocycle becomes a one-cocycle modulo constants. -/
theorem coinducedFormationTransgression_add
    {c : G → G → A} (hc : IsCohomologicalFormationTwoCocycle c) (g h : G) :
    coinducedFormationTransgression c (g + h) =
      coinducedFormationTransgression c g +
        coinducedFormationRightTranslate g (coinducedFormationTransgression c h) -
          coinducedFormationConstant (c g h) := by
  funext x
  have hcx := hc x g h
  simp only [coinducedFormationTransgression, coinducedFormationRightTranslate,
    coinducedFormationConstant, Pi.add_apply, Pi.sub_apply]
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using hcx.symm

/-- The degree-two law is reconstructed from the degree-one defect at every basepoint. -/
theorem cohomologicalTwoCocycle_recovered_from_transgression
    {c : G → G → A} (hc : IsCohomologicalFormationTwoCocycle c) (x g h : G) :
    c g h = coinducedFormationTransgression c g x +
      coinducedFormationRightTranslate g (coinducedFormationTransgression c h) x -
        coinducedFormationTransgression c (g + h) x := by
  have hcx := hc x g h
  simp only [coinducedFormationTransgression, coinducedFormationRightTranslate]
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using hcx.symm

/-- A coinduced one-cochain is a coboundary after quotienting by constant functions. -/
def IsCoinducedFormationCoboundaryModuloConstants (b : G → G → A) : Prop :=
  ∃ F k : G → A, ∀ g x, b g x = F (x + g) - F x + k g

/-- Faithfulness of dimension lowering: triviality modulo constants is equivalent to triviality of
the original normalized two-cocycle. -/
theorem coinducedFormationTransgression_coboundary_iff
    {c : G → G → A} (hc0 : IsCohomologicalLeftNormalized c) :
    IsCoinducedFormationCoboundaryModuloConstants (coinducedFormationTransgression c) ↔
      ∃ φ : G → A, c = cohomologicalFormationTwoCoboundary φ := by
  constructor
  · rintro ⟨F, k, hk⟩
    let φ : G → A := fun x => F 0 - F x
    refine ⟨φ, ?_⟩
    funext g h
    have hk0 := hk h 0
    have hkgh := hk h g
    have hc0h := hc0 h
    simp only [coinducedFormationTransgression, zero_add] at hk0
    simp only [coinducedFormationTransgression] at hkgh
    simp only [cohomologicalFormationTwoCoboundary, φ]
    rw [hc0h] at hk0
    have hkval : k h = F 0 - F h := by
      have hneg := eq_neg_of_add_eq_zero_right hk0.symm
      simpa only [neg_sub] using hneg
    rw [hkval] at hkgh
    rw [hkgh]
    abel
  · rintro ⟨φ, rfl⟩
    refine ⟨fun x => -φ x, φ, ?_⟩
    intro g x
    simp only [coinducedFormationTransgression, cohomologicalFormationTwoCoboundary]
    abel

/-- Exact reporter for coinduced histories.  It is a quotient by constants with a represented
translation action and enough range to lift every reported fixed point. -/
structure CohomologicalExactReporter where
  reporter : (G → A) →+ H
  action : G → H ≃+ H
  action_zero : ∀ v, action 0 v = v
  action_add : ∀ g h v, action (g + h) v = action g (action h v)
  kills_constants : ∀ a, reporter (coinducedFormationConstant a) = 0
  intertwines : ∀ g f,
    reporter (coinducedFormationRightTranslate g f) = action g (reporter f)
  exact_kernel : ∀ f, reporter f = 0 → ∃ a, f = coinducedFormationConstant a
  surjective : Function.Surjective reporter

/-- Degree-lowered packet seen by an exact reporter. -/
def cohomologicalLoweredCocycle
    (R : CohomologicalExactReporter (G := G) (A := A) (H := H))
    (c : G → G → A) (g : G) : H :=
  R.reporter (coinducedFormationTransgression c g)

theorem cohomologicalLoweredCocycle_zero
    (R : CohomologicalExactReporter (G := G) (A := A) (H := H))
    {c : G → G → A} (hc : IsCohomologicalFormationTwoCocycle c)
    (hc0 : IsCohomologicalLeftNormalized c) :
    cohomologicalLoweredCocycle R c 0 = 0 := by
  have hfun : coinducedFormationTransgression c 0 = 0 := by
    funext x
    exact cohomologicalTwoCocycle_right_normalized_of_left hc hc0 x
  rw [cohomologicalLoweredCocycle, hfun, R.reporter.map_zero]

/-- Exact global formation: a constant-killing equivariant reporter turns the dimension shift into
a genuine one-cocycle. -/
theorem cohomologicalLoweredCocycle_add
    (R : CohomologicalExactReporter (G := G) (A := A) (H := H))
    {c : G → G → A} (hc : IsCohomologicalFormationTwoCocycle c) (g h : G) :
    cohomologicalLoweredCocycle R c (g + h) =
      cohomologicalLoweredCocycle R c g +
        R.action g (cohomologicalLoweredCocycle R c h) := by
  rw [cohomologicalLoweredCocycle, coinducedFormationTransgression_add hc]
  simp only [map_sub, map_add, R.kills_constants, sub_zero, R.intertwines]
  rfl

/-- Global recovery: if the faithfully lowered one-cocycle is a coboundary, the original normalized
two-cocycle is a coboundary. -/
theorem cohomologicalTwoCocycle_coboundary_of_loweredCocycle_coboundary
    (R : CohomologicalExactReporter (G := G) (A := A) (H := H))
    {c : G → G → A} (hc0 : IsCohomologicalLeftNormalized c)
    (ξ : H) (hξ : ∀ g, cohomologicalLoweredCocycle R c g = R.action g ξ - ξ) :
    ∃ φ : G → A, c = cohomologicalFormationTwoCoboundary φ := by
  obtain ⟨F, hF⟩ := R.surjective ξ
  have hconstant : ∀ g, ∃ k : A,
      coinducedFormationTransgression c g -
          (coinducedFormationRightTranslate g F - F) = coinducedFormationConstant k := by
    intro g
    apply R.exact_kernel
    rw [map_sub, map_sub, R.intertwines, hF]
    change cohomologicalLoweredCocycle R c g - (R.action g ξ - ξ) = 0
    rw [hξ]
    exact sub_self _
  choose k hk using hconstant
  apply (coinducedFormationTransgression_coboundary_iff hc0).mp
  refine ⟨F, k, ?_⟩
  intro g x
  have hx := congrFun (hk g) x
  simp only [Pi.sub_apply, coinducedFormationRightTranslate, coinducedFormationConstant] at hx
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hx)

end GaloisForLFunctions.HTGeometry
