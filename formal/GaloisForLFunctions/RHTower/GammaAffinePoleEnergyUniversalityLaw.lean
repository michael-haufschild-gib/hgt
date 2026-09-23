import GaloisForLFunctions.HTGeometry.GammaPoleAffineSimpleOrderLaw
import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelBoundaryPole

/-!
# Gamma affine-pole energy universality

For an affine Gamma source, the moving-profile law identifies exact simple order with
nonvanishing of the canonical Gamma coefficient at a branch.  The boundary-pole energy law
identifies the same nonvanishing with divergence of approaching vertical-line `L²` energies.
Consequently local meromorphic order and global failure of uniform line-energy control are
equivalent certificates.
-/

open Complex MeasureTheory Set

namespace GaloisForLFunctions

noncomputable section

/-- A boundary principal part defeats every uniform approaching-line energy bound exactly when
its coefficient is nonzero. -/
theorem boundaryPoleApproachEnergy_unbounded_iff_coefficient_ne_zero
    (gamma : ℝ) (c : ℂ) :
    (¬ ∃ C : ℝ, ∀ m : ℕ,
      (∫ t : ℝ, ‖RHTower.boundaryPoleApproachProfile gamma c m t‖ ^ (2 : ℕ)) ≤ C) ↔
      c ≠ 0 := by
  constructor
  · intro hunbounded hc
    apply hunbounded
    refine ⟨0, fun m => ?_⟩
    rw [RHTower.integral_norm_sq_boundaryPoleApproachProfile, hc]
    simp
  · exact RHTower.not_exists_uniform_boundaryPoleApproachEnergy_bound gamma

/-- **Affine Gamma order--energy equivalence.**  At every Gamma branch, an affine source has exact
simple order precisely when the boundary profile carrying its Gamma coefficient has no uniform
approaching-line `L²` energy bound. -/
theorem gammaPoleAffineSource_simple_iff_boundaryEnergy_unbounded
    (branch n : ℕ) (a b : Polynomial ℂ) :
    meromorphicOrderAt
        (fun x : ℂ => gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)
          (MvPolynomial.C a +
            MvPolynomial.C b * MvPolynomial.X (0 : Fin (n + 1)))) 0 =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ¬ ∃ C : ℝ, ∀ m : ℕ,
        (∫ t : ℝ, ‖RHTower.boundaryPoleApproachProfile 0
          (b.eval (-(branch : ℂ))) m t‖ ^ (2 : ℕ)) ≤ C := by
  rw [gammaPoleAffineSource_order_eq_neg_one_iff,
    boundaryPoleApproachEnergy_unbounded_iff_coefficient_ne_zero]

/-- **Canonical at-most-simple order--energy equivalence.**  For an arbitrary source already
known to lie on the at-most-simple Gamma horizon, the canonical derivative coefficient controls
both exact local order and approaching-line energy blowup. -/
theorem gammaPoleProfileAtMostSimple_simple_iff_boundaryEnergy_unbounded
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)}
    (hprofile : GammaPoleProfileAtMostSimple n P) (branch : ℕ) :
    meromorphicOrderAt
        (fun x : ℂ => gammaPolyJetEval (n + 1)
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x) P) 0 =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ¬ ∃ C : ℝ, ∀ m : ℕ,
        (∫ t : ℝ, ‖RHTower.boundaryPoleApproachProfile 0
          (((MvPolynomial.pderiv (0 : Fin (n + 1)) P).coeff 0).eval
            (-(branch : ℂ))) m t‖ ^ (2 : ℕ)) ≤ C := by
  rw [gammaPoleProfileAtMostSimple_order_eq_neg_one_iff hprofile,
    boundaryPoleApproachEnergy_unbounded_iff_coefficient_ne_zero]

end

end GaloisForLFunctions
