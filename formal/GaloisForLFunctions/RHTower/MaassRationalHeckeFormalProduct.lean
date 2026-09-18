import GaloisForLFunctions.RHTower.SelbergMaassHeckeOperatorConvolution

/-!
# Formal Mackey products of rational Maass correspondences

For two positive rational correspondence representatives, their finite Mackey
expansion is packaged as a formal finitely supported complex combination of
principal Hecke cosets.  Its action on the fixed Maass eigenspace is exactly
the composition of the two rational trace endomorphisms.

The product is deliberately indexed by representatives.  Descent under changing
either representative within its Hecke double coset, and associativity after
that descent, remain the theorems required to construct a Hecke algebra.
-/

namespace GaloisForLFunctions.RHTower

open Complex Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups BigOperators

noncomputable section

/-- The complex-linear action of formal finite combinations of principal positive
rational Hecke cosets on one fixed Maass eigenspace. -/
def rationalPrincipalHeckeCosetFinsuppAction (N : ℕ) (lam : ℝ) :
    (HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N) →₀ ℂ) →ₗ[ℂ]
        Module.End ℂ (glMaassCuspEigenspace (principalCongruenceGL N) lam) :=
  Finsupp.linearCombination ℂ (rationalPrincipalHeckeCosetLinear N lam)

/-- The finite formal Hecke-coset combination produced by the Mackey product
of two positive rational correspondence representatives. -/
noncomputable def rationalMackeyHeckeCosetFormalProduct (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) :
    HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N) →₀ ℂ := by
  classical
  letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
  exact ∑ D ∈ Finset.univ.image (rationalMackeyOrbitToHeckeCoset N g h hg hh),
    Finsupp.single D (rationalMackeyHeckeFiberCoefficient N g h hg hh D)

/-- A single formal Hecke-coset basis vector acts by its descended Maass
endomorphism. -/
@[simp] theorem rationalPrincipalHeckeCosetFinsuppAction_single (N : ℕ) (lam : ℝ)
    (D : HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N)) (c : ℂ) :
    rationalPrincipalHeckeCosetFinsuppAction N lam (Finsupp.single D c) =
      c • rationalPrincipalHeckeCosetLinear N lam D := by
  exact Finsupp.linearCombination_single ℂ c D

/-- The formal Mackey Hecke-coset product acts exactly as the composition of
its two source-attached rational trace operators. -/
theorem rationalMackeyHeckeCosetFormalProduct_action (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ) :
    rationalPrincipalHeckeCosetFinsuppAction N lam
      (rationalMackeyHeckeCosetFormalProduct N g h hg hh) =
      (rationalPrincipalTraceLinear N h hh lam).comp
        (rationalPrincipalTraceLinear N g hg lam) := by
  classical
  letI : Fintype (rationalMackeyOrbit N g h) := rationalMackeyOrbitFintype N g h
  rw [rationalPrincipalTraceLinear_comp_eq_fiberwise_HeckeCosetLinear]
  simp only [rationalPrincipalHeckeCosetFinsuppAction,
    rationalMackeyHeckeCosetFormalProduct]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finsupp.linearCombination_single]

end

end GaloisForLFunctions.RHTower
