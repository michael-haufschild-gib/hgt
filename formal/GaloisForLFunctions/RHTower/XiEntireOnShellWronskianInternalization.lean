import GaloisForLFunctions.HTGeometry.ConstitutiveOnShellWronskianInternalization
import GaloisForLFunctions.RHTower.DeningerArithmeticJetDuality
import GaloisForLFunctions.RHTower.DeningerArithmeticRealStructure
import GaloisForLFunctions.RHTower.XiEdgeLogDerivativeBlindness
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# Actual Xi on-shell Wronskian internalization

Ordinary differentiation makes the entire Xi source algebra a differential ring. Weighting this
derivation by the literal completed Xi equation produces one global current on
`Entire(ℂ)/(XiC)`. Its exact top conormal jet is nonzero at every Xi divisor point, regardless of
multiplicity, and the actual functional-equation Real action reverses its grade.

This is an unconditional actual-Xi instantiation of the universal equation-Wronskian law. The
quotient is Xi-built comparison cohomology; a conservative realization in an independently formed
prime source carrier remains a separate obligation.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Ordinary complex derivative as an endomorphism of the entire source algebra. -/
def deningerEntireDeriv (F : DeningerEntire) : DeningerEntire :=
  ⟨deriv (F : ℂ → ℂ), fun z => (F.2.analyticAt z).deriv.differentiableAt⟩

@[simp]
theorem deningerEntireDeriv_apply (F : DeningerEntire) (z : ℂ) :
    deningerEntireDeriv F z = deriv (F : ℂ → ℂ) z :=
  rfl

@[simp]
theorem deningerEntireDeriv_zero :
    deningerEntireDeriv (0 : DeningerEntire) = 0 := by
  apply DeningerEntire.ext
  intro z
  simp [deningerEntireDeriv]

theorem deningerEntireDeriv_add (F G : DeningerEntire) :
    deningerEntireDeriv (F + G) =
      deningerEntireDeriv F + deningerEntireDeriv G := by
  apply DeningerEntire.ext
  intro z
  change deriv ((F : ℂ → ℂ) + (G : ℂ → ℂ)) z =
    deriv (F : ℂ → ℂ) z + deriv (G : ℂ → ℂ) z
  exact deriv_add (F.2 z) (G.2 z)

theorem deningerEntireDeriv_mul (F G : DeningerEntire) :
    deningerEntireDeriv (F * G) =
      F * deningerEntireDeriv G + G * deningerEntireDeriv F := by
  apply DeningerEntire.ext
  intro z
  change deriv ((F : ℂ → ℂ) * (G : ℂ → ℂ)) z =
    F z * deriv (G : ℂ → ℂ) z + G z * deriv (F : ℂ → ℂ) z
  rw [deriv_mul (F.2 z) (G.2 z)]
  ring

/-- Ordinary differentiation as a `ℤ`-derivation of the entire Xi source algebra. -/
def deningerEntireDerivation :
    Derivation ℤ DeningerEntire DeningerEntire := by
  let D : DeningerEntire →+ DeningerEntire :=
    { toFun := deningerEntireDeriv
      map_zero' := deningerEntireDeriv_zero
      map_add' := deningerEntireDeriv_add }
  exact Derivation.mk' D.toIntLinearMap deningerEntireDeriv_mul

@[simp]
theorem deningerEntireDerivation_apply (F : DeningerEntire) :
    deningerEntireDerivation F = deningerEntireDeriv F :=
  rfl

/-- The source functional-equation Real action, forgetting only its conjugate scalar linearity. -/
def deningerEntireFunctionalEquationRingEquiv :
    DeningerEntire ≃+* DeningerEntire where
  toFun := deningerEntireFunctionalEquationSigma
  invFun := deningerEntireFunctionalEquationSigma
  left_inv := deningerEntireFunctionalEquationSigma_sq
  right_inv := deningerEntireFunctionalEquationSigma_sq
  map_add' := map_add deningerEntireFunctionalEquationSigma
  map_mul' := deningerEntireFunctionalEquationSigma_mul

@[simp]
theorem deningerEntireFunctionalEquationRingEquiv_apply (F : DeningerEntire) :
    deningerEntireFunctionalEquationRingEquiv F =
      deningerEntireFunctionalEquationSigma F :=
  rfl

/-- Ordinary differentiation is odd under the actual functional-equation Real action. -/
theorem deningerEntireDeriv_functionalEquationSigma (F : DeningerEntire) :
    deningerEntireDeriv (deningerEntireFunctionalEquationSigma F) =
      -deningerEntireFunctionalEquationSigma (deningerEntireDeriv F) := by
  apply DeningerEntire.ext
  intro z
  change deriv (fun w => (starRingEnd ℂ) (F (-(starRingEnd ℂ) w))) z =
    -(starRingEnd ℂ) (deriv (F : ℂ → ℂ) (-(starRingEnd ℂ) z))
  let g : ℂ → ℂ := fun w => F (-w)
  have hg : Differentiable ℂ g := F.2.comp differentiable_neg
  rw [show (fun w => (starRingEnd ℂ) (F (-(starRingEnd ℂ) w))) =
      fun w => (starRingEnd ℂ) (g ((starRingEnd ℂ) w)) by rfl,
    deriv_conj_reflect hg z]
  change (starRingEnd ℂ) (deriv (fun w => F (-w)) ((starRingEnd ℂ) z)) = _
  rw [deriv_comp_neg]
  simp

/-- The literal completed-Xi derivative is not Xi-divisible, detected at every divisor point. -/
theorem deningerEntireDeriv_Xi_not_mem_XiIdeal (rho : XiDivisorSupport) :
    deningerEntireDeriv deningerEntireXi ∉ deningerEntireXiIdeal := by
  intro hmem
  let m := xiSupportMultiplicity rho
  have hm : 0 < m := xiSupportMultiplicity_pos rho
  let k := m - 1
  have hk : k < xiSupportMultiplicity rho := by
    dsimp only [k, m]
    omega
  have hzero := deningerEntireJet_eq_zero_of_mem_XiIdeal rho hk hmem
  have hnonzero := iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho
  apply hnonzero
  change iteratedDeriv m XiC (xiSpectralPointSupport rho) = 0
  change iteratedDeriv k (deriv XiC) (xiSpectralPointSupport rho) = 0 at hzero
  rw [show m = k + 1 by dsimp only [k, m]; omega, iteratedDeriv_succ']
  exact hzero

/-- Literal completed-Xi equation Wronskian before passage to the Xi fibre. -/
def xiEntireEquationWronskian : DeningerEntire →+ DeningerEntire :=
  equationWronskian deningerEntireDerivation deningerEntireXi

@[simp]
theorem xiEntireEquationWronskian_apply (F : DeningerEntire) :
    xiEntireEquationWronskian F =
      deningerEntireXi * deningerEntireDeriv F -
        deningerEntireDeriv deningerEntireXi * F :=
  rfl

/-- The actual Xi Wronskian has equation-divisible multiplication defect. -/
theorem xiEntireEquationWronskian_commutator (B F : DeningerEntire) :
    xiEntireEquationWronskian (B * F) - B * xiEntireEquationWronskian F =
      deningerEntireXi * deningerEntireDeriv B * F :=
  equationWronskian_commutator deningerEntireDerivation deningerEntireXi B F

/-- The actual Xi Wronskian sends Xi multiples to Xi-square multiples. -/
theorem xiEntireEquationWronskian_mul_Xi (F : DeningerEntire) :
    xiEntireEquationWronskian (deningerEntireXi * F) =
      deningerEntireXi ^ (2 : ℕ) * deningerEntireDeriv F :=
  equationWronskian_mul_equation deningerEntireDerivation deningerEntireXi F

/-- Canonical actual-Xi conormal current on entire comparison cohomology. -/
def xiEntireConormalCurrent : Module.End DeningerEntireH1 DeningerEntireH1 :=
  equationWronskianQuotient deningerEntireDerivation deningerEntireXi

/-- Exact on-shell reconstruction: the current is multiplication by `-[XiC']`. -/
theorem xiEntireConormalCurrent_apply (z : DeningerEntireH1) :
    xiEntireConormalCurrent z =
      z * (-deningerEntireH1Class (deningerEntireDeriv deningerEntireXi)) := by
  exact equationWronskianQuotient_apply
    deningerEntireDerivation deningerEntireXi z

/-- The current applied to the unit is the literal Xi conormal class. -/
theorem xiEntireConormalCurrent_one :
    xiEntireConormalCurrent (1 : DeningerEntireH1) =
      -deningerEntireH1Class (deningerEntireDeriv deningerEntireXi) := by
  rw [xiEntireConormalCurrent_apply, one_mul]

/-- Local jet index immediately below the exact Xi multiplicity. -/
def xiEntireConormalTopJetIndex (rho : XiDivisorSupport) :
    DeningerArithmeticJetIndex rho :=
  ⟨xiSupportMultiplicity rho - 1, by
    have := xiSupportMultiplicity_pos rho
    omega⟩

/-- At every Xi zero, the current's top conormal jet is the negative exact Xi multiplicity jet. -/
theorem xiEntireConormalCurrent_top_jet (rho : XiDivisorSupport) :
    deningerArithmeticJetCompact rho (xiEntireConormalTopJetIndex rho)
        (xiEntireConormalCurrent (1 : DeningerEntireH1)) =
      -iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho) := by
  rw [xiEntireConormalCurrent_one, map_neg, deningerArithmeticJetCompact_class]
  change -iteratedDeriv (xiSupportMultiplicity rho - 1) (deriv XiC)
      (xiSpectralPointSupport rho) = _
  rw [← iteratedDeriv_succ']
  congr 2
  have := xiSupportMultiplicity_pos rho
  omega

/-- Every Xi divisor point detects the global current by a nonzero multiplicity-adapted jet. -/
theorem xiEntireConormalCurrent_top_jet_ne_zero (rho : XiDivisorSupport) :
    deningerArithmeticJetCompact rho (xiEntireConormalTopJetIndex rho)
        (xiEntireConormalCurrent (1 : DeningerEntireH1)) ≠ 0 := by
  rw [xiEntireConormalCurrent_top_jet]
  exact neg_ne_zero.mpr (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-- Pointwise-strengthened nonvanishing: any Xi divisor point certifies the current is nonzero. -/
theorem xiEntireConormalCurrent_ne_zero_at (rho : XiDivisorSupport) :
    xiEntireConormalCurrent ≠ 0 := by
  intro hzero
  have hone := LinearMap.congr_fun hzero (1 : DeningerEntireH1)
  have hjet := congrArg
    (deningerArithmeticJetCompact rho (xiEntireConormalTopJetIndex rho)) hone
  rw [LinearMap.zero_apply, map_zero] at hjet
  exact xiEntireConormalCurrent_top_jet_ne_zero rho hjet

/-- Unconditional closed nonvanishing of the literal Xi conormal current. -/
theorem xiEntireConormalCurrent_ne_zero :
    xiEntireConormalCurrent ≠ 0 := by
  have hne := xiDivisorSupport_infinite.nonempty
  let rho : XiDivisorSupport := ⟨Classical.choose hne, Classical.choose_spec hne⟩
  exact xiEntireConormalCurrent_ne_zero_at rho

/-- The generic fibre reflection is definitionally the existing Xi cohomology Real action. -/
theorem xiEntireEquationFibreReflection_eq_sigma (z : DeningerEntireH1) :
    equationFibreReflection deningerEntireXi deningerEntireFunctionalEquationRingEquiv
        deningerEntireFunctionalEquationSigma_Xi z =
      deningerArithmeticH1EvenKReal.sigma z := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- The actual Xi conormal current is odd under the functional-equation Real action. -/
theorem xiEntireConormalCurrent_functionalEquation_odd (z : DeningerEntireH1) :
    xiEntireConormalCurrent (deningerArithmeticH1EvenKReal.sigma z) =
      -deningerArithmeticH1EvenKReal.sigma (xiEntireConormalCurrent z) := by
  rw [← xiEntireEquationFibreReflection_eq_sigma z,
    ← xiEntireEquationFibreReflection_eq_sigma (xiEntireConormalCurrent z)]
  exact equationWronskianQuotient_reflection_odd
    deningerEntireDerivation deningerEntireXi deningerEntireFunctionalEquationRingEquiv
    deningerEntireFunctionalEquationSigma_Xi
    (fun F => deningerEntireDeriv_functionalEquationSigma F) z

end

end RHTower
