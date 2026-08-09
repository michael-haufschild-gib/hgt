import GaloisForLFunctions.HTGeometry.ConstitutiveReporterMeetPromotion

/-!
# Promotion-observation exchange

Promotion differentiation commutes with additive observation.  Observed associative closure is
therefore genuine exactly when the source associator vanishes rather than merely entering the
observer kernel.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

def observedCompensator {M : Type u} {A : Type v} {B : Type w}
    [AddGroup A] [AddGroup B] (q : A →+ B) (κ : M → M → A) (x y : M) : B :=
  q (κ x y)

/-- Exact exchange law: observe after promotion differentiation or differentiate the observed
compensator; the results agree. -/
theorem promotionAssociator_observed
    {M : Type u} {A : Type v} {B : Type w}
    [Add M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) (x y z : M) :
    PromotionAssociator (observedCompensator q κ) x y z =
      q (PromotionAssociator κ x y z) := by
  simp [PromotionAssociator, observedCompensator]

/-- Observed binary closure means exactly that every source associator migrated into the observer
kernel. -/
theorem observed_promotedBinary_associative_iff_associator_mem_kernel
    {M : Type u} {A : Type v} {B : Type w}
    [AddMonoid M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) :
    (∀ p r s : M × B,
      promotedBinary (observedCompensator q κ)
          (promotedBinary (observedCompensator q κ) p r) s =
        promotedBinary (observedCompensator q κ) p
          (promotedBinary (observedCompensator q κ) r s)) ↔
      ∀ x y z, PromotionAssociator κ x y z ∈ q.ker := by
  rw [promotedBinary_associative_iff_associator_zero]
  constructor
  · intro hzero x y z
    apply AddMonoidHom.mem_ker.mpr
    rw [← promotionAssociator_observed]
    exact hzero x y z
  · intro hker x y z
    rw [promotionAssociator_observed]
    exact AddMonoidHom.mem_ker.mp (hker x y z)

/-- Faithful observation reflects associative promotion closure. -/
theorem observed_promotedBinary_associative_iff_source_of_injective
    {M : Type u} {A : Type v} {B : Type w}
    [AddMonoid M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) (hq : Function.Injective q) :
    (∀ p r s : M × B,
      promotedBinary (observedCompensator q κ)
          (promotedBinary (observedCompensator q κ) p r) s =
        promotedBinary (observedCompensator q κ) p
          (promotedBinary (observedCompensator q κ) r s)) ↔
      ∀ p r s : M × A,
        promotedBinary κ (promotedBinary κ p r) s =
          promotedBinary κ p (promotedBinary κ r s) := by
  rw [observed_promotedBinary_associative_iff_associator_mem_kernel]
  rw [promotedBinary_associative_iff_associator_zero]
  constructor
  · intro hker x y z
    apply hq
    rw [map_zero]
    exact AddMonoidHom.mem_ker.mp (hker x y z)
  · intro hzero x y z
    apply AddMonoidHom.mem_ker.mpr
    rw [hzero x y z, map_zero]

def modTwoObserver : ℤ →+ ZMod 2 :=
  Int.castAddHom (ZMod 2)

theorem cubicPromotionCarry_modTwo_associator_zero (x y z : ℤ) :
    PromotionAssociator (observedCompensator modTwoObserver cubicPromotionCarry) x y z = 0 := by
  rw [promotionAssociator_observed, cubicPromotionCarry_associator_formula]
  change ((2 * x * y * z : ℤ) : ZMod 2) = 0
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  push_cast
  rw [htwo]
  simp

theorem cubicPromotionCarry_modTwo_promotedBinary_associative :
    ∀ p r s : ℤ × ZMod 2,
      promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry)
          (promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry) p r) s =
        promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry) p
          (promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry) r s) := by
  apply (promotedBinary_associative_iff_associator_zero
    (observedCompensator modTwoObserver cubicPromotionCarry)).2
  exact cubicPromotionCarry_modTwo_associator_zero

theorem constitutivePromotionObservationExchangeMechanism_closed :
    (¬ ∀ p r s : ℤ × ℤ,
      promotedBinary cubicPromotionCarry (promotedBinary cubicPromotionCarry p r) s =
        promotedBinary cubicPromotionCarry p (promotedBinary cubicPromotionCarry r s)) ∧
    (∀ p r s : ℤ × ZMod 2,
      promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry)
          (promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry) p r) s =
        promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry) p
          (promotedBinary (observedCompensator modTwoObserver cubicPromotionCarry) r s)) := by
  exact ⟨cubicPromotionCarry_promotedBinary_not_associative,
    cubicPromotionCarry_modTwo_promotedBinary_associative⟩

end GaloisForLFunctions.HTGeometry
