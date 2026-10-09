import GaloisForLFunctions.HTGeometry.OrderedPolynomialRootContinuation

open Polynomial Set Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

abbrev RootFiber {n : ℕ} (v : Parameter n) (w : ℂ) :=
  {z : ℂ // (additivePolynomial v).eval z = w}

/-- The unique root section through a specified sheet at any time. -/
def rootSection {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j)
    (t₀ : I) (z₀ : RootFiber (v t₀) (w t₀)) : C(I, ℂ) :=
  (existsUnique_additivePolynomial_root_interval v w havoid t₀ z₀ z₀.property).choose

theorem rootSection_spec {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j)
    (t₀ : I) (z₀ : RootFiber (v t₀) (w t₀)) :
    rootSection v w havoid t₀ z₀ t₀ = z₀ ∧
      ∀ t, (additivePolynomial (v t)).eval (rootSection v w havoid t₀ z₀ t) = w t :=
  (existsUnique_additivePolynomial_root_interval v w havoid t₀ z₀ z₀.property).choose_spec.1

theorem eq_rootSection {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j)
    (t₀ : I) (z₀ : RootFiber (v t₀) (w t₀)) (u : C(I, ℂ))
    (hu₀ : u t₀ = z₀) (hu : ∀ t, (additivePolynomial (v t)).eval (u t) = w t) :
    u = rootSection v w havoid t₀ z₀ :=
  (existsUnique_additivePolynomial_root_interval v w havoid t₀ z₀ z₀.property).choose_spec.2
    u ⟨hu₀, hu⟩

/-- Transport uses actual polynomial roots without choosing sheet labels. -/
def rootTransport {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j) (t₀ t₁ : I)
    (z₀ : RootFiber (v t₀) (w t₀)) : RootFiber (v t₁) (w t₁) :=
  ⟨rootSection v w havoid t₀ z₀ t₁, (rootSection_spec v w havoid t₀ z₀).2 t₁⟩

theorem rootTransport_of_section {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j) (t₀ t₁ : I)
    (u : C(I, ℂ)) (hu : ∀ t, (additivePolynomial (v t)).eval (u t) = w t) :
    rootTransport v w havoid t₀ t₁ ⟨u t₀, hu t₀⟩ = ⟨u t₁, hu t₁⟩ := by
  apply Subtype.ext
  exact (congrArg (fun f : C(I, ℂ) => f t₁)
    (eq_rootSection v w havoid t₀ ⟨u t₀, hu t₀⟩ u rfl hu)).symm

theorem rootTransport_val_eq_of_section {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j) (t₀ t₁ : I)
    (z₀ : RootFiber (v t₀) (w t₀)) (u : C(I, ℂ)) (hu₀ : u t₀ = z₀)
    (hu : ∀ t, (additivePolynomial (v t)).eval (u t) = w t) :
    (rootTransport v w havoid t₀ t₁ z₀).val = u t₁ :=
  (congrArg (fun f : C(I, ℂ) => f t₁) (eq_rootSection v w havoid t₀ z₀ u hu₀ hu)).symm

theorem bijective_rootTransport {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j) (t₀ t₁ : I) :
    Function.Bijective (rootTransport v w havoid t₀ t₁) := by
  constructor
  · intro a b hab
    have hsa := rootSection_spec v w havoid t₀ a
    have hsb := rootSection_spec v w havoid t₀ b
    have heq : rootSection v w havoid t₀ a = rootSection v w havoid t₀ b :=
      (existsUnique_additivePolynomial_root_interval v w havoid t₁
        (rootSection v w havoid t₀ b t₁) (hsb.2 t₁)).unique
          ⟨congrArg Subtype.val hab, hsa.2⟩ ⟨rfl, hsb.2⟩
    apply Subtype.ext
    exact hsa.1.symm.trans ((congrArg (fun f : C(I, ℂ) => f t₀) heq).trans hsb.1)
  · intro b
    let u := rootSection v w havoid t₁ b
    have hu := rootSection_spec v w havoid t₁ b
    refine ⟨⟨u t₀, hu.2 t₀⟩, ?_⟩
    rw [rootTransport_of_section v w havoid t₀ t₁ u hu.2]
    exact Subtype.ext hu.1

def rootTransportEquiv {n : ℕ} (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j) (t₀ t₁ : I) :
    RootFiber (v t₀) (w t₀) ≃ RootFiber (v t₁) (w t₁) :=
  Equiv.ofBijective _ (bijective_rootTransport v w havoid t₀ t₁)

/-- Both boundary routes in an avoiding deformation square transport every root equally. -/
theorem rootTransport_square {n : ℕ} (v : C(I, Parameter n)) (γ : C(I, ℂ))
    (havoid : ∀ t s j, γ s ≠ valuesWithConstant (v t) j)
    (z₀ : RootFiber (v 0) (γ 0)) :
    rootTransport (ContinuousMap.const I (v 1)) γ (fun s j => havoid 1 s j) 0 1
      (rootTransport v (ContinuousMap.const I (γ 0)) (fun t j => havoid t 0 j) 0 1 z₀) =
    rootTransport v (ContinuousMap.const I (γ 1)) (fun t j => havoid t 1 j) 0 1
      (rootTransport (ContinuousMap.const I (v 0)) γ (fun s j => havoid 0 s j) 0 1 z₀) := by
  obtain ⟨S, ⟨hS₀, hS⟩, _⟩ :=
    existsUnique_additivePolynomial_root_square v γ havoid z₀ z₀.property
  let bottom : C(I, ℂ) := ⟨fun t => S (t, 0),
    S.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let left : C(I, ℂ) := ⟨fun s => S (0, s),
    S.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let right : C(I, ℂ) := ⟨fun s => S (1, s),
    S.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let top : C(I, ℂ) := ⟨fun t => S (t, 1),
    S.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hb : ∀ t, (additivePolynomial (v t)).eval (bottom t) = γ 0 := fun t => hS (t, 0)
  have hl : ∀ s, (additivePolynomial (v 0)).eval (left s) = γ s := fun s => hS (0, s)
  have hr : ∀ s, (additivePolynomial (v 1)).eval (right s) = γ s := fun s => hS (1, s)
  have ht : ∀ t, (additivePolynomial (v t)).eval (top t) = γ 1 := fun t => hS (t, 1)
  have hbottom := rootTransport_val_eq_of_section v (ContinuousMap.const I (γ 0))
    (fun t j => havoid t 0 j) 0 1 z₀ bottom hS₀ hb
  have hleft := rootTransport_val_eq_of_section (ContinuousMap.const I (v 0)) γ
    (fun s j => havoid 0 s j) 0 1 z₀ left hS₀ hl
  have hright := rootTransport_val_eq_of_section (ContinuousMap.const I (v 1)) γ
    (fun s j => havoid 1 s j) 0 1
    (rootTransport v (ContinuousMap.const I (γ 0)) (fun t j => havoid t 0 j) 0 1 z₀)
    right hbottom.symm hr
  have htop := rootTransport_val_eq_of_section v (ContinuousMap.const I (γ 1))
    (fun t j => havoid t 1 j) 0 1
    (rootTransport (ContinuousMap.const I (v 0)) γ (fun s j => havoid 0 s j) 0 1 z₀)
    top hleft.symm ht
  exact Subtype.ext (hright.trans htop.symm)

/-- The square identity as equality of bijections between the corner root fibers. -/
theorem rootTransportEquiv_square {n : ℕ} (v : C(I, Parameter n)) (γ : C(I, ℂ))
    (havoid : ∀ t s j, γ s ≠ valuesWithConstant (v t) j) :
    (rootTransportEquiv v (ContinuousMap.const I (γ 0)) (fun t j => havoid t 0 j) 0 1).trans
      (rootTransportEquiv (ContinuousMap.const I (v 1)) γ (fun s j => havoid 1 s j) 0 1) =
    (rootTransportEquiv (ContinuousMap.const I (v 0)) γ (fun s j => havoid 0 s j) 0 1).trans
      (rootTransportEquiv v (ContinuousMap.const I (γ 1)) (fun t j => havoid t 1 j) 0 1) := by
  apply Equiv.ext
  exact rootTransport_square v γ havoid

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
