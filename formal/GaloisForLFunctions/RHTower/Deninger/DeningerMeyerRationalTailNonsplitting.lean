import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerRationalTailCalculus
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# The rational source tail requires spectral gluing

The nonzero rational-function quotient has no generator-compatible section
back into actual arithmetic Meyer cohomology. Every polynomial-linear map from
the tail into the observable source is zero: Cayley--Hamilton annihilates each
finite packet, while every nonzero polynomial is invertible on the tail.

The positive construction is the preceding canonical two-sided finite-defect
calculus. Its rational operations live on an actual, nonzero quotient and lift
with explicit finite spectral defects; they cannot be lifted as a separate
invariant rational summand.
-/

open Polynomial
open scoped Classical

namespace RHTower
noncomputable section

abbrev DeningerMeyerArithmeticPolynomialModule :=
  Module.AEval' deningerMeyerArithmeticSourceGenerator

abbrev DeningerMeyerFinitePacketPolynomialModule (S : Finset XiDivisorSupport) :=
  Module.AEval' (deningerMeyerFiniteXiPacketGenerator S)

local notation "V" => DeningerMeyerArithmeticSource
local notation "MV" => DeningerMeyerArithmeticPolynomialModule
local notation "MT" => DeningerMeyerRationalTailPolynomialModule
local notation "ofSource" => Module.AEval'.of deningerMeyerArithmeticSourceGenerator
local notation "ofTail" => Module.AEval'.of deningerMeyerRationalTailGenerator

def deningerMeyerRationalTailQuotientPolynomial : MV →ₗ[ℂ[X]] MT :=
  LinearMap.ofAEval deningerMeyerArithmeticSourceGenerator
    ((ofTail).toLinearMap.comp DeningerMeyerArithmeticFiniteModes.mkQ)
    (fun u => (Module.AEval'.X_smul_of deningerMeyerRationalTailGenerator
      (Submodule.Quotient.mk u)).symm)

theorem deningerMeyerRationalTailQuotientPolynomial_surjective :
    Function.Surjective deningerMeyerRationalTailQuotientPolynomial := by
  intro u
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective DeningerMeyerArithmeticFiniteModes
    ((ofTail).symm u)
  refine ⟨ofSource v, ?_⟩
  change ofTail (Submodule.Quotient.mk v) = u
  rw [hv, (ofTail).apply_symm_apply]

def deningerMeyerArithmeticPacketPolynomial (S : Finset XiDivisorSupport) :
    MV →ₗ[ℂ[X]] DeningerMeyerFinitePacketPolynomialModule S :=
  LinearMap.ofAEval deningerMeyerArithmeticSourceGenerator
    ((Module.AEval'.of (deningerMeyerFiniteXiPacketGenerator S)).toLinearMap.comp
      (deningerMeyerArithmeticPacketLM S)) (by
        intro u
        change Module.AEval'.of (deningerMeyerFiniteXiPacketGenerator S)
          (deningerMeyerArithmeticPacketLM S (deningerMeyerArithmeticSourceGenerator u)) =
            X • Module.AEval'.of (deningerMeyerFiniteXiPacketGenerator S)
              (deningerMeyerArithmeticPacketLM S u)
        rw [Module.AEval'.X_smul_of]
        congr 1
        exact (deningerMeyerFiniteXiPacketGenerator_jets S u).symm)

theorem deningerMeyerFinitePacketPolynomial_charpoly_zero (S : Finset XiDivisorSupport)
    (u : DeningerMeyerFinitePacketPolynomialModule S) :
    (deningerMeyerFiniteXiPacketGenerator S).charpoly • u = 0 := by
  apply (Module.AEval'.of (deningerMeyerFiniteXiPacketGenerator S)).symm.injective
  rw [Module.AEval.of_symm_smul, LinearMap.aeval_self_charpoly]
  rfl

/-- No nonzero polynomial-linear rational tail can be placed inside the actual
observable source: all its finite jets would vanish. -/
theorem deningerMeyerRationalTail_hom_source_eq_zero (f : MT →ₗ[ℂ[X]] MV) : f = 0 := by
  apply LinearMap.ext
  intro u
  change f u = 0
  apply (ofSource).symm.injective
  change (ofSource).symm (f u) = 0
  apply deningerMeyerArithmeticSource_eq_zero
  apply (mem_deningerMeyerInvisible_iff _).mpr
  intro rho j
  let S : Finset XiDivisorSupport := {rho}
  let p : ℂ[X] := (deningerMeyerFiniteXiPacketGenerator S).charpoly
  have hp : p ≠ 0 := (deningerMeyerFiniteXiPacketGenerator S).charpoly_monic.ne_zero
  obtain ⟨v, hv⟩ := (deningerMeyerRationalTailPolynomial_smul_bijective p hp).2 u
  have hpacket : deningerMeyerArithmeticPacketPolynomial S (f u) = 0 := by
    rw [← hv, map_smul, map_smul]
    exact deningerMeyerFinitePacketPolynomial_charpoly_zero S _
  have h := congrArg (Module.AEval'.of (deningerMeyerFiniteXiPacketGenerator S)).symm hpacket
  change deningerMeyerArithmeticPacketLM S ((ofSource).symm (f u)) = 0 at h
  exact congrFun h ⟨⟨rho, Finset.mem_singleton_self rho⟩, j⟩

/-- The positive rational calculus is an intrinsically nonsplit extension of
actual finite causal modes, not an invariant direct-sum decomposition. -/
theorem deningerMeyerRationalTail_no_polynomial_section :
    ¬ ∃ s : MT →ₗ[ℂ[X]] MV,
      deningerMeyerRationalTailQuotientPolynomial.comp s = LinearMap.id := by
  rintro ⟨s, hs⟩
  have hzero := deningerMeyerRationalTail_hom_source_eq_zero s
  have h := LinearMap.congr_fun hs (ofTail deningerMeyerRationalTailGaussian)
  change deningerMeyerRationalTailQuotientPolynomial
    (s (ofTail deningerMeyerRationalTailGaussian)) = ofTail deningerMeyerRationalTailGaussian at h
  rw [hzero, LinearMap.zero_apply, map_zero] at h
  have hg := congrArg (ofTail).symm h
  rw [map_zero, (ofTail).symm_apply_apply] at hg
  exact deningerMeyerRationalTailGaussian_ne_zero hg.symm

/-- The nonzero rational quotient has empty algebraic spectrum. The original
Xi spectrum is retained by the finite packets and their nonsplit extension. -/
theorem deningerMeyerRationalTail_spectrum :
    spectrum ℂ deningerMeyerRationalTailGenerator = ∅ := by
  ext rho
  rw [spectrum.mem_iff, IsUnit.sub_iff, Algebra.algebraMap_eq_smul_one,
    Module.End.isUnit_iff]
  change (¬ Function.Bijective (deningerMeyerRationalTailShift rho)) ↔ False
  constructor
  · intro h
    exact h (deningerMeyerRationalTailShift_bijective rho)
  · intro h
    exact h.elim

end
end RHTower
