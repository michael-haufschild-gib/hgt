import GaloisForLFunctions.HTGeometry.RamifiedMultiGradedNewtonModel
import GaloisForLFunctions.HTGeometry.ObservabilityJacobianTransfer

/-!
# Transfer from a selected Puiseux branch to a cascade field

An iterated Puiseux expansion is useful only after its nonzero observability determinant is carried
back to the algebraic function field from which the branch was selected.  This module records that
transfer exactly.  A differential specialization sends the terminal coordinate, time derivation,
and coordinate frame to the ramified Hahn model.  Nonvanishing pulls back along the specialization,
and the domain-valued Jacobian criterion gives independence of the original time jets.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A selected ramified Puiseux specialization intertwines terminal coordinate, time law, and all
coordinate derivations. -/
def IsRamifiedPuiseuxCascadeSpecialization {n : ℕ} {K : Type*}
    [Field K] [Algebra ℂ K]
    (r : Fin (n + 1) → ℕ)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (pi : K →ₐ[ℂ] HahnFraction (mgDeg (n + 1)) ℂ)
    (delta : Derivation ℂ K K) (P : Fin (n + 1) → Derivation ℂ K K) (x : K) : Prop :=
  pi x = hahnFractionRamCoordinate r 0 ∧
  (∀ y, pi (delta y) = hahnFractionRamCascadeDerivation r A (pi y)) ∧
  ∀ j y, pi (P j y) =
    GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j (pi y)

/-- A selected output-linear Puiseux branch forces the source cascade's first full time-jet block
to be algebraically independent. -/
theorem algebraicIndependent_cascadeOutputJets_of_ramifiedPuiseuxSpecialization {n : ℕ}
    {K : Type*} [Field K] [Algebra ℂ K]
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (lambda : Fin (n + 1) → ℂ) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j))
    (pi : K →ₐ[ℂ] HahnFraction (mgDeg (n + 1)) ℂ)
    (delta : Derivation ℂ K K) (P : Fin (n + 1) → Derivation ℂ K K) (x : K)
    (hmodel : IsRamifiedPuiseuxCascadeSpecialization r A pi delta P x) :
    AlgebraicIndependent ℂ (fun i : Fin (n + 1) =>
      ((delta : K → K)^[(i : ℕ)]) x) := by
  let deltaH := hahnFractionRamCascadeDerivation r A
  let PH : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ →
      HahnFraction (mgDeg (n + 1)) ℂ := fun j y =>
    GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y
  let PK : Fin (n + 1) → K → K := fun j y => P j y
  have htarget : (observabilityJacobian (m := n) deltaH PH
      (hahnFractionRamCoordinate r 0)).det ≠ 0 := by
    exact hahnFractionRamCascade_outputJacobian_det_ne_zero
      r hr A lambda hlambda hA
  have hsource : (observabilityJacobian (m := n) delta PK x).det ≠ 0 := by
    apply observabilityJacobian_det_ne_zero_of_map pi hmodel.2.1 hmodel.2.2 x
    rw [hmodel.1]
    exact htarget
  let f := fun i : Fin (n + 1) => ((delta : K → K)^[(i : ℕ)]) x
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.transpose (observabilityJacobian (m := n) delta PK x)
  have hM : M.det ≠ 0 := by
    simpa [M, Matrix.det_transpose] using hsource
  refine algebraicIndependent_of_domain_jacobian f (fun i => P i) ?_ ?_ ?_ M hM ?_
  · intro i a b
    exact map_add (P i) a b
  · intro i a b
    simpa only [smul_eq_mul, add_comm, mul_comm] using (P i).leibniz a b
  · intro i c
    exact (P i).map_algebraMap c
  · intro i j
    simp [M, f, PK, observabilityJacobian]

end GaloisForLFunctions.HTGeometry
