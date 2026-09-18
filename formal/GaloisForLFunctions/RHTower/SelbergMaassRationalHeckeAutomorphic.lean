import GaloisForLFunctions.RHTower.SelbergMaassGLAutomorphicIntertwiner

/-!
# Rational Hecke endomorphisms on the automorphic carrier

A positive rational correspondence is a genuine linear endomorphism of the
principal `GL(2, ℝ)` automorphic carrier: pull back by left multiplication and
then take the finite relative-coset trace.  The endomorphism commutes with the
entire right `SL(2, ℝ)` regular action, without restricting first to one Maass
source.  Its value on every lifted invariant source is exactly the previously
constructed rational finite trace.

This closes the carrier-level correspondence step.  It does not provide an
`L²`-bounded extension, a simultaneous Hecke eigenspace, or finite-place
factorization; those are the remaining arithmetic steps toward a local
parameter bound.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- Pullback by a rational matrix followed by the finite relative-coset trace,
as an endomorphism of the full principal `GL(2, ℝ)` automorphic carrier. -/
noncomputable def rationalPrincipalGLAutomorphicTrace (N : ℕ) (g : GL (Fin 2) ℚ) :
    glAutomorphicFunctionSpace (principalCongruenceGL N) →ₗ[ℂ]
      glAutomorphicFunctionSpace (principalCongruenceGL N) := by
  letI : (rationalPullbackConjugateGroup (principalCongruenceGL N) g).IsFiniteRelIndex
      (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
  exact glAutomorphicTrace.comp
    (glAutomorphicLeftTranslation (g.map (algebraMap ℚ ℝ)) (principalCongruenceGL N))

/-- The carrier-level rational Hecke endomorphism intertwines the complete
right regular `SL(2, ℝ)` action. -/
theorem rationalPrincipalGLAutomorphicTrace_commutes_right
    (N : ℕ) (g : GL (Fin 2) ℚ) (k : SL2R)
    (F : glAutomorphicFunctionSpace (principalCongruenceGL N)) :
    glAutomorphicRightTranslation (principalCongruenceGL N) k
      (rationalPrincipalGLAutomorphicTrace N g F) =
      rationalPrincipalGLAutomorphicTrace N g
        (glAutomorphicRightTranslation (principalCongruenceGL N) k F) := by
  letI : (ConjAct.toConjAct (g.map (algebraMap ℚ ℝ))⁻¹ •
      principalCongruenceGL N).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  unfold rationalPrincipalGLAutomorphicTrace
  change glAutomorphicRightTranslation (principalCongruenceGL N) k
      (glAutomorphicTrace
        (glAutomorphicLeftTranslation (g.map (algebraMap ℚ ℝ))
          (principalCongruenceGL N) F)) =
    glAutomorphicTrace
      (glAutomorphicLeftTranslation (g.map (algebraMap ℚ ℝ))
        (principalCongruenceGL N)
        (glAutomorphicRightTranslation (principalCongruenceGL N) k F))
  rw [glAutomorphicTrace_commutes_right,
    glAutomorphicLeftTranslation_commutes_right]

/-- On lifted upper-half-plane data, the carrier endomorphism is exactly the
literal rational pullback followed by finite trace. -/
theorem rationalPrincipalGLAutomorphicTrace_apply_lift (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalPullbackConjugateGroup (principalCongruenceGL N) g).IsFiniteRelIndex
        (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
    rationalPrincipalGLAutomorphicTrace N g
        (glLiftInvariantFunction (principalCongruenceGL N) f) =
      glLiftInvariantFunction (principalCongruenceGL N)
        (maassTraceInvariant (H := principalCongruenceGL N)
          (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f)) := by
  letI : (rationalPullbackConjugateGroup (principalCongruenceGL N) g).IsFiniteRelIndex
      (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
  letI : (ConjAct.toConjAct (g.map (algebraMap ℚ ℝ))⁻¹ •
      principalCongruenceGL N).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  unfold rationalPrincipalGLAutomorphicTrace
  change glAutomorphicTrace
      (glAutomorphicLeftTranslation (g.map (algebraMap ℚ ℝ))
        (principalCongruenceGL N)
        (glLiftInvariantFunction (principalCongruenceGL N) f)) = _
  rw [← glLift_rationalMaassPullbackInvariant_general,
    ← glLift_maassTraceInvariant]

/-- Restricting the carrier-level Hecke endomorphism recovers its exact action
on the literal principal `SL(2, ℝ)` automorphic source. -/
theorem principalGLAutomorphicRestrictToSL_rationalPrincipalGLAutomorphicTrace_apply_lift
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalPullbackConjugateGroup (principalCongruenceGL N) g).IsFiniteRelIndex
        (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
    principalGLAutomorphicRestrictToSL N
        (rationalPrincipalGLAutomorphicTrace N g
          (glLiftInvariantFunction (principalCongruenceGL N) f)) =
      principalGLAutomorphicRestrictToSL N
        (glLiftInvariantFunction (principalCongruenceGL N)
          (maassTraceInvariant (H := principalCongruenceGL N)
            (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f))) := by
  letI : (rationalPullbackConjugateGroup (principalCongruenceGL N) g).IsFiniteRelIndex
      (principalCongruenceGL N) := rationalConjugateGroup_isFiniteRelIndex N g
  exact congrArg (principalGLAutomorphicRestrictToSL N)
    (rationalPrincipalGLAutomorphicTrace_apply_lift N g f)

end

end GaloisForLFunctions.RHTower
