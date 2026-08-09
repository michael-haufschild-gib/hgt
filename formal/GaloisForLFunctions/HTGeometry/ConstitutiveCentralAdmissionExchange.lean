import GaloisForLFunctions.HTGeometry.ConstitutivePromotionObservationExchange

/-!
# Central promotion and admission exchange

A compensator survives an additive admission quotient exactly when it lies in the quotient kernel.
This is equivalent to closure of the admitted promoted carrier and to vanishing of the observed
compensator.  Associativity of the ambient promotion then descends uniquely.

The integer multiplication compensator gives a closed countermodel: ambient promotion is
associative, but reduction modulo two rejects the compensator and the even carrier is not closed.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- A compensator is admitted when all its values lie in the kernel of the admission quotient. -/
def CompensatorAdmitted {M : Type u} {A : Type v} {B : Type w}
    [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) : Prop :=
  ∀ x y, κ x y ∈ q.ker

/-- Closure of the coefficient-restricted carrier under the ambient promoted operation. -/
def AdmittedCarrierClosed {M : Type u} {A : Type v} {B : Type w}
    [Add M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) : Prop :=
  ∀ p r : M × A, p.2 ∈ q.ker → r.2 ∈ q.ker →
    (promotedBinary κ p r).2 ∈ q.ker

/-- Admission of the compensator is exactly closure of the restricted carrier. -/
theorem compensatorAdmitted_iff_carrierClosed
    {M : Type u} {A : Type v} {B : Type w}
    [Add M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) :
    CompensatorAdmitted q κ ↔ AdmittedCarrierClosed q κ := by
  constructor
  · intro hκ p r hp hr
    exact q.ker.add_mem (q.ker.add_mem hp hr) (hκ p.1 r.1)
  · intro hclosed x y
    have h := hclosed (x, 0) (y, 0) (by simp) (by simp)
    simpa [promotedBinary] using h

/-- Admission is also exactly vanishing of the quotient-valued compensator. -/
theorem compensatorAdmitted_iff_observed_zero
    {M : Type u} {A : Type v} {B : Type w}
    [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) :
    CompensatorAdmitted q κ ↔ ∀ x y, observedCompensator q κ x y = 0 := by
  constructor
  · intro h x y
    exact AddMonoidHom.mem_ker.mp (h x y)
  · intro h x y
    exact AddMonoidHom.mem_ker.mpr (h x y)

/-- Promoted carrier whose coefficient is restricted to the admission kernel. -/
abbrev AdmittedPromotedCarrier {M : Type u} {A : Type v} {B : Type w}
    [AddCommGroup A] [AddCommGroup B] (q : A →+ B) :=
  M × q.ker

/-- Forget the proof that a coefficient is admitted. -/
def admittedCarrierInclusion {M : Type u} {A : Type v} {B : Type w}
    [AddCommGroup A] [AddCommGroup B] (q : A →+ B) :
    AdmittedPromotedCarrier (M := M) q → M × A :=
  fun p => (p.1, p.2.1)

theorem admittedCarrierInclusion_injective
    {M : Type u} {A : Type v} {B : Type w}
    [AddCommGroup A] [AddCommGroup B] (q : A →+ B) :
    Function.Injective (admittedCarrierInclusion (M := M) q) := by
  rintro ⟨pm, ⟨pa, hpa⟩⟩ ⟨rm, ⟨ra, hra⟩⟩ h
  simp only [admittedCarrierInclusion, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

/-- The compensator lifted to the admitted coefficient subtype. -/
def admittedCompensator {M : Type u} {A : Type v} {B : Type w}
    [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) (hκ : CompensatorAdmitted q κ)
    (x y : M) : q.ker :=
  ⟨κ x y, hκ x y⟩

/-- Binary promotion restricted to the admitted carrier. -/
def admittedPromotedBinary {M : Type u} {A : Type v} {B : Type w}
    [Add M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) (hκ : CompensatorAdmitted q κ) :
    AdmittedPromotedCarrier (M := M) q →
      AdmittedPromotedCarrier (M := M) q →
      AdmittedPromotedCarrier (M := M) q :=
  promotedBinary (admittedCompensator q κ hκ)

@[simp] theorem admittedCarrierInclusion_promoted
    {M : Type u} {A : Type v} {B : Type w}
    [Add M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) (hκ : CompensatorAdmitted q κ)
    (p r : AdmittedPromotedCarrier (M := M) q) :
    admittedCarrierInclusion q (admittedPromotedBinary q κ hκ p r) =
      promotedBinary κ (admittedCarrierInclusion q p) (admittedCarrierInclusion q r) := by
  rfl

/-- Any restricted operation compatible with ambient promotion is the admitted promotion. -/
theorem admittedPromotedBinary_unique
    {M : Type u} {A : Type v} {B : Type w}
    [Add M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) (hκ : CompensatorAdmitted q κ)
    (star : AdmittedPromotedCarrier (M := M) q →
      AdmittedPromotedCarrier (M := M) q →
      AdmittedPromotedCarrier (M := M) q)
    (hstar : ∀ p r,
      admittedCarrierInclusion q (star p r) =
        promotedBinary κ (admittedCarrierInclusion q p) (admittedCarrierInclusion q r)) :
    star = admittedPromotedBinary q κ hκ := by
  funext p r
  apply admittedCarrierInclusion_injective q
  rw [hstar, admittedCarrierInclusion_promoted]

/-- Associativity descends through an admitted compensator. -/
theorem admittedPromotedBinary_associative_of_ambient
    {M : Type u} {A : Type v} {B : Type w}
    [AddMonoid M] [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (κ : M → M → A) (hκ : CompensatorAdmitted q κ)
    (hassoc : ∀ p r s : M × A,
      promotedBinary κ (promotedBinary κ p r) s =
        promotedBinary κ p (promotedBinary κ r s)) :
    ∀ p r s : AdmittedPromotedCarrier (M := M) q,
      admittedPromotedBinary q κ hκ (admittedPromotedBinary q κ hκ p r) s =
        admittedPromotedBinary q κ hκ p (admittedPromotedBinary q κ hκ r s) := by
  intro p r s
  apply admittedCarrierInclusion_injective q
  simpa only [admittedCarrierInclusion_promoted] using
    hassoc (admittedCarrierInclusion q p) (admittedCarrierInclusion q r)
      (admittedCarrierInclusion q s)

/-- Multiplication is the smallest associative compensator rejected by parity admission. -/
def bilinearPromotionCarry (x y : ℤ) : ℤ := x * y

theorem bilinearPromotionCarry_associator_zero (x y z : ℤ) :
    PromotionAssociator bilinearPromotionCarry x y z = 0 := by
  simp [PromotionAssociator, bilinearPromotionCarry]
  ring

theorem bilinearPromotionCarry_ambient_associative :
    ∀ p r s : ℤ × ℤ,
      promotedBinary bilinearPromotionCarry (promotedBinary bilinearPromotionCarry p r) s =
        promotedBinary bilinearPromotionCarry p (promotedBinary bilinearPromotionCarry r s) := by
  exact (promotedBinary_associative_iff_associator_zero bilinearPromotionCarry).2
    bilinearPromotionCarry_associator_zero

theorem bilinearPromotionCarry_not_modTwo_admitted :
    ¬ CompensatorAdmitted modTwoObserver bilinearPromotionCarry := by
  intro h
  have h11 := AddMonoidHom.mem_ker.mp (h 1 1)
  change (1 : ZMod 2) = 0 at h11
  exact one_ne_zero h11

theorem bilinearPromotionCarry_observed_nonzero :
    observedCompensator modTwoObserver bilinearPromotionCarry 1 1 ≠ 0 := by
  change (1 : ZMod 2) ≠ 0
  exact one_ne_zero

theorem bilinearPromotionCarry_evenCarrier_not_closed :
    ¬ AdmittedCarrierClosed modTwoObserver bilinearPromotionCarry := by
  exact fun hclosed => bilinearPromotionCarry_not_modTwo_admitted
    ((compensatorAdmitted_iff_carrierClosed modTwoObserver bilinearPromotionCarry).2 hclosed)

/-- Closed capstone: exact ambient coherence can coexist with a nonzero admission obstruction. -/
theorem constitutiveCentralAdmissionExchangeMechanism_closed :
    (∀ x y z : ℤ, PromotionAssociator bilinearPromotionCarry x y z = 0) ∧
    (∀ p r s : ℤ × ℤ,
      promotedBinary bilinearPromotionCarry (promotedBinary bilinearPromotionCarry p r) s =
        promotedBinary bilinearPromotionCarry p (promotedBinary bilinearPromotionCarry r s)) ∧
    (¬ CompensatorAdmitted modTwoObserver bilinearPromotionCarry) ∧
    (observedCompensator modTwoObserver bilinearPromotionCarry 1 1 ≠ 0) ∧
    (¬ AdmittedCarrierClosed modTwoObserver bilinearPromotionCarry) := by
  exact ⟨bilinearPromotionCarry_associator_zero,
    bilinearPromotionCarry_ambient_associative,
    bilinearPromotionCarry_not_modTwo_admitted,
    bilinearPromotionCarry_observed_nonzero,
    bilinearPromotionCarry_evenCarrier_not_closed⟩

end GaloisForLFunctions.HTGeometry
