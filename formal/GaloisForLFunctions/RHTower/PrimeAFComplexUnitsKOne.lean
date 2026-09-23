import GaloisForLFunctions.RHTower.PrimeAFCircleOperatorKOne
import GaloisForLFunctions.HTGeometry.TorusChartFundamentalGroup

/-!
# Fundamental-group model of `K₁(C(S¹))`

The complex exponential universal cover identifies `π₁(ℂˣ)` with its period lattice.
This file computes that lattice as `ℤ` and packages the result additively, matching operator-`K₁`
conventions.  Unlike a winding interface, the carrier is Mathlib's literal fundamental group.
-/

open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

/-- Generator of the exponential period lattice. -/
def complexExponentialPeriodGenerator : ℂ := 2 * Real.pi * Complex.I

theorem complexExponentialPeriodGenerator_ne_zero :
    complexExponentialPeriodGenerator ≠ 0 := by
  simp [complexExponentialPeriodGenerator, Real.pi_ne_zero, Complex.I_ne_zero]

/-- Integer multiples map additively onto the exponential period lattice. -/
def intToComplexExponentialPeriodLattice :
    ℤ →+ ComplexExponentialPeriodLattice where
  toFun z := ⟨z • complexExponentialPeriodGenerator,
    AddSubgroup.mem_zmultiples_iff.mpr ⟨z, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_smul]

theorem intToComplexExponentialPeriodLattice_injective :
    Function.Injective intToComplexExponentialPeriodLattice := by
  intro x y hxy
  have hval := congrArg Subtype.val hxy
  change x • complexExponentialPeriodGenerator =
    y • complexExponentialPeriodGenerator at hval
  simp only [zsmul_eq_mul] at hval
  have hcast : (x : ℂ) = (y : ℂ) :=
    mul_right_cancel₀ complexExponentialPeriodGenerator_ne_zero hval
  exact_mod_cast hcast

theorem intToComplexExponentialPeriodLattice_surjective :
    Function.Surjective intToComplexExponentialPeriodLattice := by
  intro x
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
  refine ⟨z, Subtype.ext ?_⟩
  exact hz

/-- The exponential period lattice is additively `ℤ`. -/
def complexExponentialPeriodLatticeEquivInt :
    ComplexExponentialPeriodLattice ≃+ ℤ :=
  (AddEquiv.ofBijective intToComplexExponentialPeriodLattice
    ⟨intToComplexExponentialPeriodLattice_injective,
      intToComplexExponentialPeriodLattice_surjective⟩).symm

/-- For a commutative group, forgetting the formal opposite is a multiplicative equivalence. -/
def mulOppositeCommEquiv (G : Type*) [CommGroup G] : Gᵐᵒᵖ ≃* G where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    change MulOpposite.unop y * MulOpposite.unop x =
      MulOpposite.unop x * MulOpposite.unop y
    exact mul_comm _ _

/-- Fundamental group of `ℂˣ`, computed first as the multiplicative presentation of `ℤ`. -/
def complexUnitsFundamentalGroupEquivIntMul :
    FundamentalGroup (Units ℂ) 1 ≃* Multiplicative ℤ :=
  (complexExpUnits_isAddQuotientCoveringMap.fundamentalGroupEquiv
      complexExpUnitsBasepoint).trans
    ((mulOppositeCommEquiv (Multiplicative ComplexExponentialPeriodLattice)).trans
      complexExponentialPeriodLatticeEquivInt.toMultiplicative)

/-- Cancel the additive/multiplicative wrapper pair on `ℤ`. -/
def additiveMultiplicativeIntEquiv : Additive (Multiplicative ℤ) ≃+ ℤ where
  toFun z := Multiplicative.toAdd (Additive.toMul z)
  invFun z := Additive.ofMul (Multiplicative.ofAdd z)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Fundamental-group definition of the scalar circle operator-`K₁` group. -/
abbrev ComplexUnitsOperatorKOne := Additive (FundamentalGroup (Units ℂ) 1)

noncomputable local instance primeAFComplexUnitsKOneInst1 : CommGroup (FundamentalGroup (Units ℂ) 1) :=
  fundamentalGroupCommGroup

/-- Exact Bott computation in the literal fundamental-group model. -/
def complexUnitsOperatorKOneEquivInt : ComplexUnitsOperatorKOne ≃+ ℤ :=
  complexUnitsFundamentalGroupEquivIntMul.toAdditive.trans
    additiveMultiplicativeIntEquiv

end

end PrimeQuasiLocalCharge
