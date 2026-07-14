import GaloisForLFunctions.HTGeometry.FiniteGaugeTailCharge
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Exponent-zero Euler-gauge foliation

This file constructs the canonical summable phase-gauge relation on an arbitrary prime index set.
The formulation first treats any nonnegative family of coordinate weights and then specializes to
the exponent-zero weights `p^(-sigma)` for every `sigma > 0`.

The resulting equivalence classes contain every finite modification of each of their points.
Consequently every class is dense in the full phase product, and the coinduced orbit topology is
indiscrete.  This is the topological group core of the dense isodivisorial Euler-gauge foliation;
analytic divisor preservation is supplied separately by normal convergence of the Euler ratios.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

/-- Pointwise prime phases. -/
abbrev PrimePhase (P : Type*) := P → Circle

/-- Gauges summable for every weight in a prescribed family. -/
def IsWeightedEulerGauge {P Λ : Type*} (weight : Λ → P → ℝ)
    (omega : PrimePhase P) : Prop :=
  ∀ l, Summable (fun p => weight l p * ‖1 - (omega p : ℂ)‖)

theorem isWeightedEulerGauge_one {P Λ : Type*} (weight : Λ → P → ℝ) :
    IsWeightedEulerGauge weight (1 : PrimePhase P) := by
  intro l
  convert (summable_zero : Summable (fun _ : P => (0 : ℝ))) using 1
  funext p
  simp

/-- The phase cost of a product is at most the sum of the two phase costs. -/
theorem norm_one_sub_circle_mul_le (a b : Circle) :
    ‖1 - ((a * b : Circle) : ℂ)‖ ≤ ‖1 - (a : ℂ)‖ + ‖1 - (b : ℂ)‖ := by
  rw [Circle.coe_mul]
  calc
    ‖1 - (a : ℂ) * (b : ℂ)‖ = ‖(1 - (a : ℂ)) + (a : ℂ) * (1 - (b : ℂ))‖ := by ring_nf
    _ ≤ ‖1 - (a : ℂ)‖ + ‖(a : ℂ) * (1 - (b : ℂ))‖ := norm_add_le _ _
    _ = ‖1 - (a : ℂ)‖ + ‖1 - (b : ℂ)‖ := by
      rw [norm_mul, Circle.norm_coe, one_mul]

theorem isWeightedEulerGauge_mul {P Λ : Type*} {weight : Λ → P → ℝ}
    (hweight : ∀ l p, 0 ≤ weight l p) {omega psi : PrimePhase P}
    (homega : IsWeightedEulerGauge weight omega)
    (hpsi : IsWeightedEulerGauge weight psi) :
    IsWeightedEulerGauge weight (omega * psi) := by
  intro l
  apply Summable.of_nonneg_of_le
      (fun p => mul_nonneg (hweight l p) (norm_nonneg _))
      (fun p => ?_)
      ((homega l).add (hpsi l))
  rw [Pi.mul_apply]
  calc
    weight l p * ‖1 - (((omega * psi) p : Circle) : ℂ)‖
        ≤ weight l p * (‖1 - (omega p : ℂ)‖ + ‖1 - (psi p : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_one_sub_circle_mul_le (omega p) (psi p))
        (hweight l p)
    _ = weight l p * ‖1 - (omega p : ℂ)‖ +
        weight l p * ‖1 - (psi p : ℂ)‖ := by ring

/-- Inversion preserves phase cost exactly on the unit circle. -/
theorem norm_one_sub_circle_inv (a : Circle) :
    ‖1 - ((a⁻¹ : Circle) : ℂ)‖ = ‖1 - (a : ℂ)‖ := by
  rw [Circle.coe_inv]
  have ha : (a : ℂ) ≠ 0 := by
    intro h
    have hnorm := Circle.norm_coe a
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  calc
    ‖1 - (a : ℂ)⁻¹‖ = ‖(a : ℂ)⁻¹ * ((a : ℂ) - 1)‖ := by
      congr 1
      field_simp
    _ = ‖(a : ℂ)⁻¹‖ * ‖(a : ℂ) - 1‖ := norm_mul _ _
    _ = ‖1 - (a : ℂ)‖ := by
      rw [norm_inv, Circle.norm_coe, inv_one, one_mul, norm_sub_rev]

theorem isWeightedEulerGauge_inv {P Λ : Type*} {weight : Λ → P → ℝ}
    {omega : PrimePhase P} (homega : IsWeightedEulerGauge weight omega) :
    IsWeightedEulerGauge weight omega⁻¹ := by
  intro l
  simpa only [Pi.inv_apply, norm_one_sub_circle_inv] using homega l

/-- Weighted Euler gauges form a genuine subgroup of the full phase group. -/
def weightedEulerGaugeSubgroup {P Λ : Type*} (weight : Λ → P → ℝ)
    (hweight : ∀ l p, 0 ≤ weight l p) : Subgroup (PrimePhase P) where
  carrier := {omega | IsWeightedEulerGauge weight omega}
  one_mem' := isWeightedEulerGauge_one weight
  mul_mem' := isWeightedEulerGauge_mul hweight
  inv_mem' := isWeightedEulerGauge_inv

/-- Every finite phase modification is a weighted Euler gauge, for arbitrary finite weights. -/
theorem isWeightedEulerGauge_of_finiteModification_one {P Λ : Type*}
    (weight : Λ → P → ℝ) {omega : PrimePhase P}
    (homega : omega ∈ finiteModification (fun _ : P => Circle) 1) :
    IsWeightedEulerGauge weight omega := by
  intro l
  apply summable_of_hasFiniteSupport
  apply homega.subset
  intro p hp heq
  exact hp (by simp [heq])

/-- Two phases are equivalent when their relative phase is a weighted Euler gauge. -/
def weightedEulerGaugeSetoid {P Λ : Type*} (weight : Λ → P → ℝ)
    (hweight : ∀ l p, 0 ≤ weight l p) : Setoid (PrimePhase P) where
  r x y := IsWeightedEulerGauge weight (x⁻¹ * y)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simpa using isWeightedEulerGauge_one weight
    · intro x y hxy
      have hi := isWeightedEulerGauge_inv hxy
      simpa [mul_comm] using hi
    · intro x y z hxy hyz
      have hm := isWeightedEulerGauge_mul hweight hxy hyz
      simpa [mul_assoc, mul_comm, mul_left_comm] using hm

def weightedEulerGaugeQuotient {P Λ : Type*} (weight : Λ → P → ℝ)
    (hweight : ∀ l p, 0 ≤ weight l p) :=
  Quotient (weightedEulerGaugeSetoid weight hweight)

def weightedEulerGaugeClass {P Λ : Type*} (weight : Λ → P → ℝ)
    (hweight : ∀ l p, 0 ≤ weight l p) :
    PrimePhase P → weightedEulerGaugeQuotient weight hweight :=
  Quotient.mk (weightedEulerGaugeSetoid weight hweight)

/-- Equality of gauge classes is exactly membership of the relative phase in the gauge subgroup. -/
theorem weightedEulerGaugeClass_eq_iff {P Λ : Type*}
    (weight : Λ → P → ℝ) (hweight : ∀ l p, 0 ≤ weight l p)
    (x y : PrimePhase P) :
    weightedEulerGaugeClass weight hweight x = weightedEulerGaugeClass weight hweight y ↔
      x⁻¹ * y ∈ weightedEulerGaugeSubgroup weight hweight := by
  exact Quotient.eq

/-- Pointwise multiplication gives a free phase action. -/
theorem primePhase_mul_eq_self_iff {P : Type*} (eta omega : PrimePhase P) :
    eta * omega = eta ↔ omega = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun phase : PrimePhase P => eta⁻¹ * phase) h
    simpa [mul_assoc] using h'
  · rintro rfl
    simp

/-- Every weighted gauge class is dense because it contains every finite modification. -/
theorem weightedEulerGaugeClass_fiber_dense {P Λ : Type*}
    (weight : Λ → P → ℝ) (hweight : ∀ l p, 0 ≤ weight l p)
    (x : PrimePhase P) :
    Dense (weightedEulerGaugeClass weight hweight ⁻¹'
      {weightedEulerGaugeClass weight hweight x}) := by
  apply dense_fiber_of_finiteModification_invariant
  intro a b hab
  apply Quotient.sound
  apply isWeightedEulerGauge_of_finiteModification_one weight
  show {p | (b⁻¹ * a) p ≠ 1}.Finite
  apply hab.subset
  intro p hp
  by_contra hba
  have hEq : b p = a p := not_ne_iff.mp hba
  apply hp
  simp [hEq]

/-- The coinduced topology on the weighted gauge quotient is indiscrete. -/
theorem weightedEulerGaugeQuotient_coinduced_eq_indiscrete {P Λ : Type*}
    (weight : Λ → P → ℝ) (hweight : ∀ l p, 0 ≤ weight l p) :
    TopologicalSpace.coinduced (weightedEulerGaugeClass weight hweight)
      inferInstance = ⊤ := by
  apply coinduced_eq_indiscrete_of_dense_fibers
  · exact Quotient.mk_surjective
  · intro a
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective a
    exact weightedEulerGaugeClass_fiber_dense weight hweight x

/-- Positive exponents indexing the exponent-zero gauge condition. -/
abbrev PositiveExponent := {sigma : ℝ // 0 < sigma}

/-- The prime-decay weights `p^(-sigma)`, written in an everywhere-positive exponential form. -/
noncomputable def exponentZeroWeight {P : Type*} (primeSize : P → ℝ)
    (sigma : PositiveExponent) (p : P) : ℝ :=
  Real.exp (-sigma.1 * Real.log (primeSize p))

theorem exponentZeroWeight_pos {P : Type*} (primeSize : P → ℝ)
    (sigma : PositiveExponent) (p : P) :
    0 < exponentZeroWeight primeSize sigma p :=
  Real.exp_pos _

/-- The canonical exponent-zero Euler gauge condition. -/
def IsExponentZeroEulerGauge {P : Type*} (primeSize : P → ℝ)
    (omega : PrimePhase P) : Prop :=
  IsWeightedEulerGauge (exponentZeroWeight primeSize) omega

/-- The canonical exponent-zero Euler gauges as a subgroup of the prime-phase torus. -/
def exponentZeroEulerGaugeSubgroup {P : Type*} (primeSize : P → ℝ) :
    Subgroup (PrimePhase P) :=
  weightedEulerGaugeSubgroup (exponentZeroWeight primeSize)
    (fun sigma p => (exponentZeroWeight_pos primeSize sigma p).le)

def exponentZeroEulerGaugeSetoid {P : Type*} (primeSize : P → ℝ) :
    Setoid (PrimePhase P) :=
  weightedEulerGaugeSetoid (exponentZeroWeight primeSize)
    (fun sigma p => (exponentZeroWeight_pos primeSize sigma p).le)

def exponentZeroEulerGaugeQuotient {P : Type*} (primeSize : P → ℝ) :=
  Quotient (exponentZeroEulerGaugeSetoid primeSize)

def exponentZeroEulerGaugeClass {P : Type*} (primeSize : P → ℝ) :
    PrimePhase P → exponentZeroEulerGaugeQuotient primeSize :=
  Quotient.mk (exponentZeroEulerGaugeSetoid primeSize)

theorem exponentZeroEulerGaugeClass_eq_iff {P : Type*}
    (primeSize : P → ℝ) (x y : PrimePhase P) :
    exponentZeroEulerGaugeClass primeSize x = exponentZeroEulerGaugeClass primeSize y ↔
      x⁻¹ * y ∈ exponentZeroEulerGaugeSubgroup primeSize := by
  exact Quotient.eq

/-- Every exponent-zero Euler-gauge class is dense in the full prime-phase product. -/
theorem exponentZeroEulerGaugeClass_fiber_dense {P : Type*}
    (primeSize : P → ℝ) (x : PrimePhase P) :
    Dense (exponentZeroEulerGaugeClass primeSize ⁻¹'
      {exponentZeroEulerGaugeClass primeSize x}) := by
  exact weightedEulerGaugeClass_fiber_dense (exponentZeroWeight primeSize)
    (fun sigma p => (exponentZeroWeight_pos primeSize sigma p).le) x

/-- The canonical exponent-zero Euler-gauge quotient has the indiscrete topology. -/
theorem exponentZeroEulerGaugeQuotient_coinduced_eq_indiscrete {P : Type*}
    (primeSize : P → ℝ) :
    TopologicalSpace.coinduced (exponentZeroEulerGaugeClass primeSize)
      inferInstance = ⊤ := by
  exact weightedEulerGaugeQuotient_coinduced_eq_indiscrete
    (exponentZeroWeight primeSize)
    (fun sigma p => (exponentZeroWeight_pos primeSize sigma p).le)

end

end GaloisForLFunctions.HTGeometry
