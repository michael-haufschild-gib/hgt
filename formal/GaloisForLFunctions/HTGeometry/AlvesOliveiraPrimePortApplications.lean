import GaloisForLFunctions.HTGeometry.AlvesOliveiraScalarProduct
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeAugmentationSymplectic

/-!
# Alves--Oliveira lift ambiguity for prime augmentation ports

The corpus's prime-port coisotropic reduction is an algebraic instance of the generalized
horizontal-lift picture: equal reduced lifts differ by the isotropic constraint, while their
pairing is independent of representatives. The two-prime augmentation gives a closed witness that
horizontal reduction need not have unique lifts.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AlvesOliveiraApplications

open _root_.HTGeometry.ConstraintMotiveRelativity

theorem wtRed_equal_lifts_sub_mem_isotropic
    {P : Type*} [Nonempty P] {c : P → ℂ} (hc : ∀ p, c p ≠ 0) (p₀ : P)
    {u v : PortDouble P}
    (hu : u ∈ portOrth (wtIsotropic c)) (hv : v ∈ portOrth (wtIsotropic c))
    (hred : wtRed c p₀ u = wtRed c p₀ v) :
    u - v ∈ wtIsotropic c := by
  have hmem : u - v ∈
      portOrth (wtIsotropic c) ⊓ LinearMap.ker (wtRed c p₀) := by
    constructor
    · exact sub_mem hu hv
    · exact LinearMap.mem_ker.mpr (by
        rw [map_sub, sub_eq_zero]
        exact hred)
  rw [ker_wtRed_inf hc p₀] at hmem
  exact hmem

theorem wtRed_pairing_independent_of_lifts
    {P : Type*} [Nonempty P] {c : P → ℂ} (hc : ∀ p, c p ≠ 0) (p₀ : P)
    {u₁ u₂ v₁ v₂ : PortDouble P}
    (hu₁ : u₁ ∈ portOrth (wtIsotropic c)) (hu₂ : u₂ ∈ portOrth (wtIsotropic c))
    (hv₁ : v₁ ∈ portOrth (wtIsotropic c)) (hv₂ : v₂ ∈ portOrth (wtIsotropic c))
    (hu : wtRed c p₀ u₁ = wtRed c p₀ u₂)
    (hv : wtRed c p₀ v₁ = wtRed c p₀ v₂) :
    portForm u₁ v₁ = portForm u₂ v₂ := by
  rw [portForm_eq_hyperbolicForm_wt hc p₀ hu₁ hv₁,
    portForm_eq_hyperbolicForm_wt hc p₀ hu₂ hv₂, hu, hv]

def finTwoAugmentationRadical : PortDouble (Fin 2) :=
  (Finsupp.single 0 1 - Finsupp.single 1 1, 0)

theorem finTwoAugmentationRadical_mem_isotropic :
    finTwoAugmentationRadical ∈ augIsotropic := by
  constructor
  · exact sub_single_mem_augIdeal 0 1
  · simp [finTwoAugmentationRadical]

theorem finTwoAugmentationRadical_ne_zero :
    finTwoAugmentationRadical ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun u : PortDouble (Fin 2) => u.1 0) hzero
  norm_num [finTwoAugmentationRadical, Finsupp.single_apply] at hcoord

theorem finTwoAugmentationRadical_mem_horizontal :
    finTwoAugmentationRadical ∈ portOrth (augIsotropic : Submodule ℂ (PortDouble (Fin 2))) := by
  rw [mem_portOrth]
  intro v hv
  exact augIsotropic_isotropic v finTwoAugmentationRadical hv
    finTwoAugmentationRadical_mem_isotropic

theorem portRed_finTwo_radical_eq_zero :
    portRed 0 finTwoAugmentationRadical = 0 := by
  rw [portRed_apply]
  simp [finTwoAugmentationRadical]

/-- Closed two-prime witness for Alves--Oliveira's non-unique-horizontal-lift phenomenon. -/
theorem finTwo_portRed_horizontal_not_injective :
    ¬ Function.Injective
      ((portRed (P := Fin 2) 0).domRestrict
        (portOrth (augIsotropic : Submodule ℂ (PortDouble (Fin 2))))) := by
  intro hinj
  let r : portOrth (augIsotropic : Submodule ℂ (PortDouble (Fin 2))) :=
    ⟨finTwoAugmentationRadical, finTwoAugmentationRadical_mem_horizontal⟩
  have heq :
      (portRed (P := Fin 2) 0).domRestrict
          (portOrth (augIsotropic : Submodule ℂ (PortDouble (Fin 2)))) r =
        (portRed (P := Fin 2) 0).domRestrict
          (portOrth (augIsotropic : Submodule ℂ (PortDouble (Fin 2)))) 0 := by
    change portRed 0 finTwoAugmentationRadical = portRed 0 0
    rw [portRed_finTwo_radical_eq_zero, map_zero]
  have hrzero : r = 0 := hinj heq
  apply finTwoAugmentationRadical_ne_zero
  exact congrArg Subtype.val hrzero

end GaloisForLFunctions.HTGeometry.AlvesOliveiraApplications
