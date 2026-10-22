import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCochainComplex
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Functional-equation Real structure on source arithmetic cohomology

The centered functional equation and Schwarz reality preserve the entire source through

`F(z) ↦ conj (F(-conj z))`.

This map is conjugate-linear, multiplicative, involutive, fixes `XiC`, and commutes with the
weight-one coordinate `1/2 + I*z`.  It therefore descends to an even `KRealStructure` on
`H¹ = Entire(ℂ)/(XiC)`, commuting with Deninger's Frobenius generator.

This is the unconditional Real coefficient structure forced by the functional equation.  It is
not the odd Hodge star: the latter must square to `-1` and provide positivity, so it still requires
the quaternionic/Morita coefficient construction rather than a declaration on this carrier.
-/

open Complex
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Functional-equation Schwarz reflection on entire source cochains. -/
def deningerEntireFunctionalEquationSigma :
    DeningerEntire →ₗ⋆[ℂ] DeningerEntire where
  toFun F :=
    ⟨fun z => (starRingEnd ℂ) (F (-(starRingEnd ℂ) z)), by
      have hneg : Differentiable ℂ (fun w : ℂ => F (-w)) := by
        simpa only [Function.comp_apply] using!
          F.2.comp differentiable_neg
      simpa only using! differentiable_conj_reflect hneg⟩
  map_add' F G := by
    apply DeningerEntire.ext
    intro z
    simp
  map_smul' c F := by
    apply DeningerEntire.ext
    intro z
    simp

@[simp]
theorem deningerEntireFunctionalEquationSigma_apply
    (F : DeningerEntire) (z : ℂ) :
    deningerEntireFunctionalEquationSigma F z =
      (starRingEnd ℂ) (F (-(starRingEnd ℂ) z)) :=
  rfl

/-- Functional-equation reflection is multiplicative. -/
theorem deningerEntireFunctionalEquationSigma_mul
    (F G : DeningerEntire) :
    deningerEntireFunctionalEquationSigma (F * G) =
      deningerEntireFunctionalEquationSigma F *
        deningerEntireFunctionalEquationSigma G := by
  apply DeningerEntire.ext
  intro z
  simp

/-- Functional-equation reflection is an involution on entire sources. -/
theorem deningerEntireFunctionalEquationSigma_sq
    (F : DeningerEntire) :
    deningerEntireFunctionalEquationSigma
      (deningerEntireFunctionalEquationSigma F) = F := by
  apply DeningerEntire.ext
  intro z
  simp

/-- Centered completed Xi is fixed by the source functional-equation reflection. -/
theorem deningerEntireFunctionalEquationSigma_Xi :
    deningerEntireFunctionalEquationSigma deningerEntireXi =
      deningerEntireXi := by
  apply DeningerEntire.ext
  intro z
  change
    (starRingEnd ℂ) (XiC (-(starRingEnd ℂ) z)) = XiC z
  rw [XiC_even, xiHedenmalm_XiC_conj]
  simp

/-- The weight-one source coordinate is fixed by functional-equation reflection. -/
theorem deningerEntireFunctionalEquationSigma_thetaCoordinate :
    deningerEntireFunctionalEquationSigma deningerEntireThetaCoordinate =
      deningerEntireThetaCoordinate := by
  apply DeningerEntire.ext
  intro z
  simp only [deningerEntireFunctionalEquationSigma_apply,
    deningerEntireThetaCoordinate_apply]
  simp
  exact map_ofNat (starRingEnd ℂ) 2

/-- Functional-equation reflection commutes with the source degree-one Frobenius cochain map. -/
theorem deningerEntireFunctionalEquationSigma_commutes_theta
    (F : DeningerEntire) :
    deningerEntireFunctionalEquationSigma
        (deningerArithmeticThetaC1 F) =
      deningerArithmeticThetaC1
        (deningerEntireFunctionalEquationSigma F) := by
  change
    deningerEntireFunctionalEquationSigma
        (deningerEntireThetaCoordinate * F) =
      deningerEntireThetaCoordinate *
        deningerEntireFunctionalEquationSigma F
  rw [
    deningerEntireFunctionalEquationSigma_mul,
    deningerEntireFunctionalEquationSigma_thetaCoordinate]

/-- Even `K_R` structure on the entire source algebra. -/
def deningerEntireEvenKReal :
    KRealStructure false DeningerEntire where
  sigma := deningerEntireFunctionalEquationSigma
  sq F := by
    simpa [kRealParityAction] using
      deningerEntireFunctionalEquationSigma_sq F

/-- The principal Xi ideal is stable under the source functional-equation Real structure. -/
theorem deningerEntireXiIdeal_stable :
    deningerEntireEvenKReal.StableSubmodule
      (deningerEntireXiIdeal.restrictScalars ℂ) := by
  intro F hF
  change
    deningerEntireFunctionalEquationSigma F ∈
      deningerEntireXiIdeal
  change F ∈ deningerEntireXiIdeal at hF
  rw [deningerEntireXiIdeal, Ideal.mem_span_singleton'] at hF ⊢
  obtain ⟨G, hG⟩ := hF
  refine ⟨deningerEntireFunctionalEquationSigma G, ?_⟩
  calc
    deningerEntireFunctionalEquationSigma G * deningerEntireXi =
        deningerEntireFunctionalEquationSigma G *
          deningerEntireFunctionalEquationSigma deningerEntireXi := by
            rw [deningerEntireFunctionalEquationSigma_Xi]
    _ = deningerEntireFunctionalEquationSigma (G * deningerEntireXi) :=
      (deningerEntireFunctionalEquationSigma_mul G deningerEntireXi).symm
    _ = deningerEntireFunctionalEquationSigma F := by rw [hG]

/-- Even functional-equation `K_R` structure descended to source middle cohomology. -/
def deningerArithmeticH1EvenKReal :
    KRealStructure false DeningerArithmeticH1 :=
  deningerEntireEvenKReal.quotient
    (deningerEntireXiIdeal.restrictScalars ℂ)
    deningerEntireXiIdeal_stable

@[simp]
theorem deningerArithmeticH1EvenKReal_sigma_class
    (F : DeningerEntire) :
    deningerArithmeticH1EvenKReal.sigma
        (deningerEntireH1Class F) =
      deningerEntireH1Class
        (deningerEntireFunctionalEquationSigma F) :=
  rfl

/-- The descended even Real structure commutes with Deninger's source Frobenius generator. -/
theorem deningerArithmeticH1EvenKReal_commutes_theta
    (x : DeningerArithmeticH1) :
    deningerArithmeticH1EvenKReal.sigma
        (deningerEntireTheta x) =
      deningerEntireTheta
        (deningerArithmeticH1EvenKReal.sigma x) := by
  obtain ⟨F, rfl⟩ := Quotient.exists_rep x
  change
    deningerArithmeticH1EvenKReal.sigma
        (deningerEntireTheta (deningerEntireH1Class F)) =
      deningerEntireTheta
        (deningerArithmeticH1EvenKReal.sigma
          (deningerEntireH1Class F))
  rw [deningerArithmeticTheta_H1_class,
    deningerArithmeticH1EvenKReal_sigma_class,
    deningerArithmeticH1EvenKReal_sigma_class,
    deningerArithmeticTheta_H1_class]
  exact congrArg deningerEntireH1Class
    (deningerEntireFunctionalEquationSigma_commutes_theta F)

end

end RHTower
