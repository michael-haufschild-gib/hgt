import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveDivisorFamilyAlignment

/-!
# Closed CGL positive-window zero-density envelope

This file packages the completed Section-12 primitive-conductor transport into
a single source-facing fixed-modulus count.  The result is an unconditional
envelope for every certified positive centered window at one ambient modulus.
Its constant may depend on that modulus, so it is not Chen--Gupta--Li's
conductor-uniform `7/3` zero-density theorem.
-/

noncomputable section

namespace RHTower

/-- The multiplicity-weighted completed-Dirichlet zero count over every
nonprincipal character at ambient modulus `n + 1` in a certified positive
centered window. -/
def cglNonprincipalFamilyPositiveWindowZeroDensityCount
    (n : ℕ) (W : CGLPositiveZeroDensityVerticalWindow) : ℝ :=
  ∑ χ : NonprincipalDirichletCharacter n,
    completedLFunctionZeroDensityVerticalWindowCount n χ W.sigma W.center W.halfWidth

/-- CGL's finite primitive-conductor reduction bounds the full ambient
nonprincipal positive-window count by the established primitive-divisor
aggregate. -/
theorem cglNonprincipalFamilyPositiveWindowZeroDensityCount_le_primitiveDivisor
    (n : ℕ) (W : CGLPositiveZeroDensityVerticalWindow) :
    cglNonprincipalFamilyPositiveWindowZeroDensityCount n W ≤
      completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount
        (n + 1) W.sigma W.center W.halfWidth :=
  cgl_nonprincipalFamily_zeroDensityVerticalWindowCount_le_existingPrimitiveDivisor n W

/-- Every fixed ambient modulus has a closed positive-window zero-density
envelope after exact primitive-conductor reduction.  The constant is built
inside Lean and has no RH, GRH, or caller-supplied analytic premise. -/
theorem cglNonprincipalFamilyPositiveWindowZeroDensityCount_growth
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ W : CGLPositiveZeroDensityVerticalWindow,
      cglNonprincipalFamilyPositiveWindowZeroDensityCount n W ≤
        C * (5 + |W.sigma| + |W.center| + W.halfWidth) *
          Real.log (6 + |W.sigma| + |W.center| + W.halfWidth) := by
  obtain ⟨C, hC, hbound⟩ :=
    completedLFunction_primitiveDivisor_zeroDensityVerticalWindowCount_growth (n + 1)
  refine ⟨C, hC, fun W => ?_⟩
  exact (cglNonprincipalFamilyPositiveWindowZeroDensityCount_le_primitiveDivisor n W).trans
    (hbound W.sigma W.center W.halfWidth)

end RHTower
