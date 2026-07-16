import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Barnes cotangent singularity threshold

This module formalizes the algebraic half of the Barnes reflection threshold in the actual
normal-crossing coordinate rings. It constructs the canonical quotient restriction, identifies
its kernel with the critical ideal, identifies the gradient presentation Fitting ideal and its
pullback, and proves that the intrinsic critical ideal becomes proper exactly at two coordinates.
-/

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial Finset

noncomputable section

variable {F : Type*} [Field F]

/-- The principal normal-crossing source ideal. -/
def normalCrossingPrincipalIdeal (r : ℕ) :
    Ideal (MvPolynomial (Fin (r + 1)) F) :=
  Ideal.span {normalCrossingPolynomial (F := F) r}

/-- The source equation already belongs to its intrinsic critical ideal. -/
theorem normalCrossingPrincipalIdeal_le_veroneseIdeal (r : ℕ) :
    normalCrossingPrincipalIdeal (F := F) r ≤
      veroneseIdeal F (Fin (r + 1)) r := by
  rw [normalCrossingPrincipalIdeal]
  refine Ideal.span_le.2 ?_
  intro P hP
  simp only [Set.mem_singleton_iff] at hP
  subst P
  rw [normalCrossingPolynomial, ← X_mul_cofaceMonomial r 0]
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨Finset.univ.erase 0, by simp, rfl⟩

/-- The canonical restriction from the normal-crossing hypersurface to its critical scheme. -/
def normalCrossingRestriction (r : ℕ) :
    (MvPolynomial (Fin (r + 1)) F ⧸ normalCrossingPrincipalIdeal (F := F) r) →+*
      (MvPolynomial (Fin (r + 1)) F ⧸ veroneseIdeal F (Fin (r + 1)) r) :=
  Ideal.Quotient.factor (normalCrossingPrincipalIdeal_le_veroneseIdeal r)

/-- The critical ideal inside the normal-crossing hypersurface. -/
def normalCrossingSingularIdeal (r : ℕ) :
    Ideal (MvPolynomial (Fin (r + 1)) F ⧸ normalCrossingPrincipalIdeal (F := F) r) :=
  (veroneseIdeal F (Fin (r + 1)) r).map
    (Ideal.Quotient.mk (normalCrossingPrincipalIdeal (F := F) r))

/-- The restriction to the critical scheme is onto. -/
theorem normalCrossingRestriction_surjective (r : ℕ) :
    Function.Surjective (normalCrossingRestriction (F := F) r) :=
  Ideal.Quotient.factor_surjective (normalCrossingPrincipalIdeal_le_veroneseIdeal r)

/-- Its kernel is exactly the critical ideal in the hypersurface coordinate ring. -/
theorem ker_normalCrossingRestriction (r : ℕ) :
    RingHom.ker (normalCrossingRestriction (F := F) r) =
      normalCrossingSingularIdeal (F := F) r := by
  exact Ideal.Quotient.factor_ker (normalCrossingPrincipalIdeal_le_veroneseIdeal r)

/-- The presentation Fitting ideal: the gradient ideal after restriction to the hypersurface. -/
def normalCrossingCotangentFittingIdeal (r : ℕ) :
    Ideal (MvPolynomial (Fin (r + 1)) F ⧸ normalCrossingPrincipalIdeal (F := F) r) :=
  (normalCrossingJacobianIdeal (F := F) r).map
    (Ideal.Quotient.mk (normalCrossingPrincipalIdeal (F := F) r))

/-- The cotangent presentation Fitting ideal is the singular ideal. -/
theorem normalCrossingCotangentFittingIdeal_eq_singularIdeal (r : ℕ) :
    normalCrossingCotangentFittingIdeal (F := F) r =
      normalCrossingSingularIdeal (F := F) r := by
  rw [normalCrossingCotangentFittingIdeal, normalCrossingSingularIdeal,
    normalCrossingJacobianIdeal_eq_veroneseIdeal]

/-- Pulling the cotangent degeneracy ideal back to the source ring recovers the complete
squarefree critical ideal. -/
theorem comap_normalCrossingCotangentFittingIdeal (r : ℕ) :
    (normalCrossingCotangentFittingIdeal (F := F) r).comap
        (Ideal.Quotient.mk (normalCrossingPrincipalIdeal (F := F) r)) =
      veroneseIdeal F (Fin (r + 1)) r := by
  rw [normalCrossingCotangentFittingIdeal,
    normalCrossingJacobianIdeal_eq_veroneseIdeal]
  rw [Ideal.comap_map_of_surjective
    (Ideal.Quotient.mk (normalCrossingPrincipalIdeal (F := F) r))
    Ideal.Quotient.mk_surjective]
  change veroneseIdeal F (Fin (r + 1)) r ⊔
      RingHom.ker (Ideal.Quotient.mk (normalCrossingPrincipalIdeal (F := F) r)) = _
  rw [Ideal.mk_ker]
  exact sup_eq_left.mpr (normalCrossingPrincipalIdeal_le_veroneseIdeal r)

/-- The intrinsic critical ideal is proper exactly from the two-coordinate crossing onward. -/
theorem normalCrossingCriticalIdeal_ne_top_iff (r : ℕ) :
    derivationalCriticalIdeal (R := F) (normalCrossingPolynomial (F := F) r) ≠ ⊤ ↔
      0 < r := by
  rw [ne_eq, normalCrossingDerivationalCriticalIdeal_eq_top_iff]
  omega

/-- In order notation `N=r+1`, cotangent singularity begins exactly at `N=2`. -/
theorem normalCrossingCotangentSingularityThreshold (r : ℕ) :
    derivationalCriticalIdeal (R := F) (normalCrossingPolynomial (F := F) r) ≠ ⊤ ↔
      2 ≤ r + 1 := by
  rw [normalCrossingCriticalIdeal_ne_top_iff]
  omega

/-- Exact algebraic certificate behind the Barnes restriction law. -/
structure NormalCrossingRestrictionCertificate (r : ℕ) : Prop where
  sourceInCritical : normalCrossingPrincipalIdeal (F := F) r ≤
    veroneseIdeal F (Fin (r + 1)) r
  restrictionSurjective : Function.Surjective (normalCrossingRestriction (F := F) r)
  restrictionKernel : RingHom.ker (normalCrossingRestriction (F := F) r) =
    normalCrossingSingularIdeal (F := F) r
  cotangentFitting : normalCrossingCotangentFittingIdeal (F := F) r =
    normalCrossingSingularIdeal (F := F) r
  pulledBackFitting : (normalCrossingCotangentFittingIdeal (F := F) r).comap
      (Ideal.Quotient.mk (normalCrossingPrincipalIdeal (F := F) r)) =
    veroneseIdeal F (Fin (r + 1)) r

/-- The canonical restriction sequence and cotangent degeneracy identification hold in every
normal-crossing order. -/
theorem normalCrossingRestrictionCertificate (r : ℕ) :
    NormalCrossingRestrictionCertificate (F := F) r where
  sourceInCritical := normalCrossingPrincipalIdeal_le_veroneseIdeal r
  restrictionSurjective := normalCrossingRestriction_surjective r
  restrictionKernel := ker_normalCrossingRestriction r
  cotangentFitting := normalCrossingCotangentFittingIdeal_eq_singularIdeal r
  pulledBackFitting := comap_normalCrossingCotangentFittingIdeal r

end

end GaloisForLFunctions.VeroneseIdeal

