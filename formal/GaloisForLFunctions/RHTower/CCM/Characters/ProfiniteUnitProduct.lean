import GaloisForLFunctions.RHTower.CCM.CCMRationalProfiniteUnitCongruenceLift
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Algebra.Group.Submonoid.Units

/-!
# The actual profinite units as a product of p-adic units

The additive identification of integral finite adeles with `∏ p, ℤ_p`
preserves multiplication. Passing to units gives the literal map into the
finite ideles. That map is continuous; compactness and Hausdorffness give
continuous inverse, hence an isomorphism of topological groups.
-/

noncomputable section
open IsDedekindDomain
open scoped RestrictedProduct Classical
namespace GaloisForLFunctions.RHTower.CCMCharacters

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩
local instance (v : HeightOneSpectrum ℤ) : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
  Ring.toIntAlgebra _

/-- The integral finite adeles with their inherited ring operations. -/
def integralFiniteAdeleSubring : Subring CCMRationalFiniteAdele where
  carrier := ccmRationalIntegralFiniteAdeles
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun hx hy v => add_mem (hx v) (hy v)
  neg_mem' := fun hx v => neg_mem (hx v)
  one_mem' := fun _ => one_mem _
  mul_mem' := fun hx hy v => mul_mem (hx v) (hy v)

/-- The existing additive identification is an isomorphism of actual rings. -/
def integralFiniteAdeleRingEquiv :
    CCMRationalProfiniteIntegers ≃+* integralFiniteAdeleSubring where
  __ := ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles
  map_mul' x y := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    change (((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
      (x (Rat.HeightOneSpectrum.primesEquiv v) * y (Rat.HeightOneSpectrum.primesEquiv v))) :
        v.adicCompletion ℚ) = _
    rw [map_mul]
    rfl

/-- Units of the integral subring are precisely finite ideles integral with integral inverse. -/
def integralUnitsEquiv : integralFiniteAdeleSubringˣ ≃* CCMRationalProfiniteUnit :=
  (integralFiniteAdeleSubring.toSubmonoid.unitsEquivUnitsType).symm

/-- Algebraic product decomposition of the actual profinite-unit subgroup. -/
def profiniteUnitProductMulEquiv :
    (∀ p : Nat.Primes, ℤ_[p]ˣ) ≃* CCMRationalProfiniteUnit :=
  MulEquiv.piUnits.symm.trans
    ((Units.mapEquiv integralFiniteAdeleRingEquiv.toMulEquiv).trans integralUnitsEquiv)

/-- The product equivalence is the coordinatewise profinite-unit construction. -/
theorem profiniteUnitProductMulEquiv_apply (u : ∀ p : Nat.Primes, ℤ_[p]ˣ) :
    profiniteUnitProductMulEquiv u = ccmRationalProfiniteUnitOfPadicUnits u := by
  apply Subtype.ext
  apply Units.ext
  rfl

/-- The literal map from p-adic unit families to finite ideles is continuous. -/
theorem continuous_profiniteUnitProduct : Continuous profiniteUnitProductMulEquiv := by
  have hval : Continuous (fun u : ∀ p : Nat.Primes, ℤ_[p]ˣ =>
      (ccmRationalPadicUnitsIntegralFiniteAdele u : CCMRationalFiniteAdele)) := by
    have hcoord : Continuous (fun u : ∀ p : Nat.Primes, ℤ_[p]ˣ =>
        fun v : HeightOneSpectrum ℤ =>
          (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
            (u (Rat.HeightOneSpectrum.primesEquiv v) : ℤ_[Rat.HeightOneSpectrum.primesEquiv v])) := by
      apply continuous_pi
      intro v
      exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.continuous.comp
        (Units.continuous_val.comp (continuous_apply (Rat.HeightOneSpectrum.primesEquiv v)))
    exact RestrictedProduct.isEmbedding_structureMap.continuous.comp hcoord
  have hu : Continuous ccmRationalProfiniteUnitOfPadicUnits := by
    apply Continuous.subtype_mk
    apply Units.continuous_iff.mpr
    exact ⟨hval, hval.comp continuous_inv⟩
  have heq : (profiniteUnitProductMulEquiv : (∀ p : Nat.Primes, ℤ_[p]ˣ) →
      CCMRationalProfiniteUnit) = ccmRationalProfiniteUnitOfPadicUnits :=
    funext profiniteUnitProductMulEquiv_apply
  rw [heq]
  exact hu

/-- Product decomposition with the actual profinite and finite-idele topologies. -/
def profiniteUnitProductEquiv :
    (∀ p : Nat.Primes, ℤ_[p]ˣ) ≃ₜ* CCMRationalProfiniteUnit where
  toMulEquiv := profiniteUnitProductMulEquiv
  continuous_toFun := continuous_profiniteUnitProduct
  continuous_invFun :=
    (profiniteUnitProductMulEquiv.toEquiv.toHomeomorphOfContinuousClosed
      continuous_profiniteUnitProduct continuous_profiniteUnitProduct.isClosedMap).symm.continuous

#print axioms profiniteUnitProductMulEquiv_apply
#print axioms continuous_profiniteUnitProduct
#print axioms profiniteUnitProductEquiv

end GaloisForLFunctions.RHTower.CCMCharacters
