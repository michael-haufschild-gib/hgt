import GaloisForLFunctions.HTGeometry.ReflectionTateAnomaly
import GaloisForLFunctions.RHTower.CyclicRegularTateBlindness
import GaloisForLFunctions.RHTower.IntegralOrbitTateExtension

/-!
# Integral cyclic/reflection Tate orbit universality

The canonical integral two-torsion extension realizes the abstract fixed-locus parity
classification of reflection Tate cohomology.  Its fixed residue is the `q = 2` cyclic fixed-orbit
charge and represents a nonboundary class; its free two-point residue is a norm, while every
cocycle on the fixed-point-free two-cycle is a boundary.  The same fixed/regular separation holds
for every nontrivial cyclic order.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- The fixed-point-free reflection on a two-element orbit. -/
def finTwoOrbitReflection : Fin 2 ≃ Fin 2 where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem finTwoOrbitReflection_zero :
    finTwoOrbitReflection 0 = 1 := rfl

@[simp] theorem finTwoOrbitReflection_one :
    finTwoOrbitReflection 1 = 0 := rfl

theorem finTwoOrbitReflection_involutive :
    Function.Involutive finTwoOrbitReflection := by
  intro i
  fin_cases i <;> rfl

theorem finTwoOrbitReflection_no_fixed (i : Fin 2) :
    finTwoOrbitReflection i ≠ i := by
  fin_cases i <;> decide

/-- Every reflection Tate cocycle on the free two-cycle is a boundary; its anomaly quotient is
trivial before choosing any particular residue. -/
theorem finTwoOrbitReflection_every_cocycle_is_boundary
    (q : Fin 2 →₀ ℤ) (hq : ReflectionTateCocycle finTwoOrbitReflection q) :
    ∃ g, q = reflectionTateBoundary finTwoOrbitReflection g := by
  apply (reflectionTateCocycle_is_boundary_iff_fixed_even
    finTwoOrbitReflection finTwoOrbitReflection_involutive q hq).2
  intro i hi
  exact (finTwoOrbitReflection_no_fixed i hi).elim

/-- The integral fixed norm and charge are literally the order-two cyclic norm and charge. -/
theorem fixedOrbit_integral_eq_cyclic_orderTwo (n : ℤ) :
    fixedOrbitNorm n = cyclicFixedNorm 2 n ∧
      fixedOrbitTateCharge n = cyclicFixedTateCharge 2 n := by
  constructor <;> simp [fixedOrbitNorm, cyclicFixedNorm,
    fixedOrbitTateCharge, cyclicFixedTateCharge, two_mul]

/-- Unit charge on the one-point fixed reflection orbit. -/
def fixedUnitReflectionCharge : Fin 1 →₀ ℤ :=
  Finsupp.single 0 1

/-- Unit invariant charge on the free two-point reflection orbit. -/
def freeUnitReflectionCharge : Fin 2 →₀ ℤ :=
  Finsupp.single 0 1 + Finsupp.single 1 1

theorem fixedUnitReflectionCharge_cocycle :
    ReflectionTateCocycle (Equiv.refl (Fin 1)) fixedUnitReflectionCharge := by
  exact fixedMirrorCharge_cocycle (Equiv.refl (Fin 1)) rfl 1

theorem fixedUnitReflectionCharge_not_boundary :
    ¬ ∃ g, fixedUnitReflectionCharge =
      reflectionTateBoundary (Equiv.refl (Fin 1)) g := by
  exact fixedMirrorUnit_not_boundary (Equiv.refl (Fin 1))
    (fun _ => rfl) (i := (0 : Fin 1)) rfl

theorem freeUnitReflectionCharge_cocycle :
    ReflectionTateCocycle finTwoOrbitReflection freeUnitReflectionCharge := by
  apply (reflectionTateCocycle_iff finTwoOrbitReflection
    finTwoOrbitReflection_involutive freeUnitReflectionCharge).2
  intro i
  fin_cases i <;> simp [freeUnitReflectionCharge]

theorem freeUnitReflectionCharge_is_boundary :
    ∃ g, freeUnitReflectionCharge =
      reflectionTateBoundary finTwoOrbitReflection g :=
  finTwoOrbitReflection_every_cocycle_is_boundary
    freeUnitReflectionCharge freeUnitReflectionCharge_cocycle

/-- Exact realization certificate for the canonical integral extension, the abstract reflection
parity quotient, and arbitrary cyclic orbit order. -/
def IntegralCyclicReflectionTateOrbitCertificate (m : ℕ) : Prop :=
  (integralUnitTwoTorsionExtension m 0 1).coeff 0 = 1 ∧
  (∀ n : ℤ,
    fixedOrbitNorm n = cyclicFixedNorm 2 n ∧
      fixedOrbitTateCharge n = cyclicFixedTateCharge 2 n) ∧
  (fixedOrbitTateCharge 1 ≠ 0 ↔
    ¬ ∃ g, fixedUnitReflectionCharge =
      reflectionTateBoundary (Equiv.refl (Fin 1)) g) ∧
  ((∃ y : ℤ × ℤ, freeOrbitNorm y = (1, 1)) ↔
    ∃ g, freeUnitReflectionCharge =
      reflectionTateBoundary finTwoOrbitReflection g) ∧
  (∀ q : Fin 2 →₀ ℤ, ReflectionTateCocycle finTwoOrbitReflection q →
    ∃ g, q = reflectionTateBoundary finTwoOrbitReflection g) ∧
  ∀ q : ℕ, 1 < q →
    cyclicFixedTateCharge q 1 ≠ 0 ∧
    IsCyclicRegularInvariant (fun _ : Fin q => (1 : ℤ)) ∧
    ∃ y : Fin q → ℤ, cyclicRegularNorm y = fun _ => (1 : ℤ)

/-- **Integral cyclic/reflection Tate orbit universality law.**  The unit residue of the canonical
integral extension realizes fixed-locus parity exactly: fixed orbits retain the charge, free
orbits kill it, and the fixed/regular dichotomy persists at every nontrivial cyclic order. -/
theorem integralUnitExtension_cyclicReflectionTateOrbitUniversality (m : ℕ) :
    IntegralCyclicReflectionTateOrbitCertificate m := by
  refine ⟨integralUnitTwoTorsionExtension_residue m,
    fixedOrbit_integral_eq_cyclic_orderTwo,
    iff_of_true fixedOrbitTateCharge_one_ne_zero fixedUnitReflectionCharge_not_boundary,
    iff_of_true freeOrbit_unitPair_is_norm freeUnitReflectionCharge_is_boundary,
    finTwoOrbitReflection_every_cocycle_is_boundary, ?_⟩
  intro q hq
  exact cyclicTate_separates_fixed_regular hq

end

end RHTower
