import GaloisForLFunctions.HTGeometry.ProjectiveTailNodalRigidityLaw
import GaloisForLFunctions.RHTower.PrimeEulerOrientationNorm

/-!
# Prime Euler nodal phase barrier

The nonlinear Euler lift detects the two projective tail sheets as finite gauge equality or
cyclotomic-norm complementarity.  If neither Euler mode holds, the orientations lie in distinct
projective tail classes.  Projective nodal rigidity then forces every continuous signed-residue
deformation between them to cross infinitely many coordinate zero walls.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open Set Topology

noncomputable section

/-- **Prime Euler nodal phase-barrier law.**  Absence of both finite Euler lifting modes forces
infinite nodal support along every continuous real residue deformation. -/
theorem residuePathNodalSupport_infinite_of_no_primeEulerMode
    (epsilon delta : ℕ → Bool) (w : ℕ → ℝ) (r : ℝ → ℕ → ℝ)
    (hw : ∀ p, 0 < w p)
    (hr0 : ∀ p, r 0 p = primeDirichletRealSign (epsilon p) * w p)
    (hr1 : ∀ p, r 1 p = primeDirichletRealSign (delta p) * w p)
    (hcontinuous : ∀ p, ContinuousOn (fun t => r t p) (Set.Icc (0 : ℝ) 1))
    (hnoMode : ¬ (PrimeEulerTailGaugeEquivalent epsilon delta ∨
      PrimeEulerTailNormComplementary epsilon delta)) :
    (HTGeometry.residuePathNodalSupport r).Infinite := by
  apply HTGeometry.residuePathNodalSupport_infinite_of_projectiveTailClass_ne
    epsilon delta w r hw hr0 hr1 hcontinuous
  intro hclass
  have htail : BooleanTailEquivalentUpToComplement epsilon delta :=
    (HTGeometry.booleanProjectiveTailClass_eq_iff epsilon delta).1 hclass
  have hprime : PrimeOrientationsEventuallyEqual epsilon delta ∨
      PrimeOrientationsEventuallyOpposite epsilon delta :=
    (HTGeometry.booleanTailEquivalentUpToComplement_iff_primeOrientationRelation
      epsilon delta).1 htail
  have hdependent : PrimeOrientationTailPairDependent epsilon delta :=
    (HTGeometry.primeOrientationTailPairDependent_iff epsilon delta).2 hprime
  exact hnoMode
    ((primeOrientationTailPairDependent_iff_eulerModes epsilon delta).1 hdependent)

end

end GaloisForLFunctions.RHTower
