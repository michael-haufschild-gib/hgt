import GaloisForLFunctions.RHTower.SelbergMaassMackeyHeckeAggregation
import GaloisForLFunctions.RHTower.SelbergMaassRationalMackeyProduct

/-!
# Operator Mackey product for principal Maass Hecke traces

The rational trace attached to a positive correspondence is already a genuine endomorphism of
the fixed source Maass eigenspace.  This file lifts the pointwise rational Mackey expansion to
an equality of those endomorphisms.  Its coefficients are the exact finite sums of stabilizer
indices over the Mackey-orbit fibers.

This gives the source-level finite correspondence product.  It does not construct finite local
factors, an adelic representation, or symmetric-power lifts.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators
open Matrix SpecialLinearGroup GeneralLinearGroup

noncomputable section

/-- Evaluation of a descended principal Hecke-coset endomorphism is its descended rational
finite trace. -/
theorem rationalPrincipalHeckeCosetLinear_apply
    (N : ℕ) (lam : ℝ)
    (D : HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N))
    (u : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    (rationalPrincipalHeckeCosetLinear N lam D u).1 =
      rationalPrincipalHeckeCosetTrace N D (maassEigenspaceToInvariant u) := by
  refine Quotient.inductionOn D ?_
  intro d
  rfl

/-- The product of two source-attached positive rational trace operators is the finite
fiberwise Mackey combination of principal Hecke-coset operators. -/
theorem rationalPrincipalTraceLinear_comp_eq_fiberwise_HeckeCosetLinear
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ) :
    letI : DecidableEq (HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N)) := Classical.decEq _
    letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
    (rationalPrincipalTraceLinear N h hh lam).comp
        (rationalPrincipalTraceLinear N g hg lam) =
      ∑ D ∈ Finset.univ.image (rationalMackeyOrbitToHeckeCoset N g h hg hh),
        rationalMackeyHeckeFiberCoefficient N g h hg hh D •
          rationalPrincipalHeckeCosetLinear N lam D := by
  classical
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : (rationalConjugateGroup N h).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N h
  letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
  ext u z
  rw [LinearMap.comp_apply]
  rw [LinearMap.sum_apply]
  rw [Submodule.coe_sum]
  rw [Finset.sum_apply]
  simp only [LinearMap.coe_smul, Pi.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  have hright :
      ∑ D ∈ Finset.univ.image (rationalMackeyOrbitToHeckeCoset N g h hg hh),
        rationalMackeyHeckeFiberCoefficient N g h hg hh D •
          (rationalPrincipalHeckeCosetLinear N lam D u).1 z =
      ∑ D ∈ Finset.univ.image (rationalMackeyOrbitToHeckeCoset N g h hg hh),
        rationalMackeyHeckeFiberCoefficient N g h hg hh D •
          rationalPrincipalHeckeCosetTrace N D (maassEigenspaceToInvariant u) z := by
    apply Finset.sum_congr rfl
    intro D hD
    rw [rationalPrincipalHeckeCosetLinear_apply]
  rw [hright]
  change maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) h
        (maassTraceInvariant (H := principalCongruenceGL N)
          (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g
            (maassEigenspaceToInvariant u)))) z = _
  calc
    _ = ∑ q : rationalMackeyOrbit N g h, rationalMackeyBlockTrace N g h q
        (maassEigenspaceToInvariant u) z := by
      convert congrFun (rationalPrincipalTrace_mackey_baseChange N g h
        (maassEigenspaceToInvariant u)) z using 1
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro q hq
      rfl
    _ = _ := by
      simpa only [Finset.sum_apply, Pi.smul_apply] using
        congrFun (rationalMackeyBlockTrace_sum_eq_fiberwise_HeckeCosetTrace
          N g h hg hh (maassEigenspaceToInvariant u)) z

end

end GaloisForLFunctions.RHTower
