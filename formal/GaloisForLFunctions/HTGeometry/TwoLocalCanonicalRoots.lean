import GaloisForLFunctions.HTGeometry.TwoLocalGenericFamily
import GaloisForLFunctions.HTGeometry.MvPowerSeriesRootFamily

/-!
# The canonical labelled spectrum of the universal transverse family

Taking the transverse couplings as independent variables and reducing them all to zero leaves the
diagonal, whose characteristic polynomial splits with the diagonal energies as its roots.  The
labelled root family in the multivariate power series ring is therefore canonical: the root attached
to a cube point is the unique one whose constant term is that point's unperturbed energy.

## Main results

* `universalTransverseHam`, `universalCharpoly` — the family and its characteristic polynomial.
* `universalCharpoly_residue` — the reduction at zero couplings.
* `exists_canonicalRootFamily` — the canonical labelled root family.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (A : Type) [Field A] (N : ℕ)

/-- The transverse family with the couplings as independent variables. -/
def universalTransverseHam (d : (Fin N → Bool) → A) :
    Matrix (Fin N → Bool) (Fin N → Bool) (MvPolynomial (Fin N) A) :=
  transverseFamilyHam (fun x => MvPolynomial.C (d x)) (fun i => MvPolynomial.X i)

/-- Its characteristic polynomial. -/
def universalCharpoly (d : (Fin N → Bool) → A) : Polynomial (MvPolynomial (Fin N) A) :=
  (universalTransverseHam A N d).charpoly

theorem universalCharpoly_monic (d : (Fin N → Bool) → A) : (universalCharpoly A N d).Monic :=
  (universalTransverseHam A N d).charpoly_monic

variable {A N}

/-- Reducing every transverse coupling to zero leaves the diagonal. -/
theorem universalTransverseHam_map_constantCoeff (d : (Fin N → Bool) → A) :
    (universalTransverseHam A N d).map (MvPolynomial.constantCoeff (σ := Fin N) (R := A))
      = Matrix.diagonal d := by
  classical
  ext x y
  rw [Matrix.map_apply, universalTransverseHam, transverseFamilyHam]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Matrix.diagonal_apply_eq]
    simp
  · rw [if_neg hxy, Matrix.diagonal_apply_ne _ hxy, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : y = boolToggle x i <;> simp [h]

/-- **The residue of the universal characteristic polynomial at zero couplings.** -/
theorem universalCharpoly_residue (d : (Fin N → Bool) → A) :
    (universalCharpoly A N d).map (MvPolynomial.constantCoeff (σ := Fin N) (R := A))
      = ∏ x, (X - C (d x)) := by
  rw [universalCharpoly, ← Matrix.charpoly_map, universalTransverseHam_map_constantCoeff,
    Matrix.charpoly_diagonal]

/-- The universal characteristic polynomial as a polynomial over the power series ring. -/
def universalCharpolySeries (d : (Fin N → Bool) → A) :
    Polynomial (MvPowerSeries (Fin N) A) :=
  (universalCharpoly A N d).map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin N) (R := A))

theorem universalCharpolySeries_monic (d : (Fin N → Bool) → A) :
    (universalCharpolySeries d).Monic :=
  (universalCharpoly_monic A N d).map _

theorem universalCharpolySeries_residue (d : (Fin N → Bool) → A) :
    (universalCharpolySeries d).map (MvPowerSeries.constantCoeff (σ := Fin N) (R := A))
      = ∏ x, (X - C (d x)) := by
  rw [universalCharpolySeries, Polynomial.map_map]
  rw [show (MvPowerSeries.constantCoeff (σ := Fin N) (R := A)).comp
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin N) (R := A))
      = MvPolynomial.constantCoeff from RingHom.ext fun p => by
    rw [RingHom.comp_apply]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff]
    rw [show MvPolynomial.coeToMvPowerSeries.ringHom p
        = (↑p : MvPowerSeries (Fin N) A) from rfl, MvPolynomial.coeff_coe]
    rfl]
  exact universalCharpoly_residue d

/-- **The canonical labelled root family.** -/
theorem exists_canonicalRootFamily (d : (Fin N → Bool) → A) (hd : Function.Injective d) :
    ∃ Θ : (Fin N → Bool) → MvPowerSeries (Fin N) A,
      universalCharpolySeries d = ∏ x, (X - C (Θ x)) ∧
        ∀ x, MvPowerSeries.constantCoeff (Θ x) = d x :=
  exists_mvPowerSeriesRootFamily A d hd (Fin N) (universalCharpolySeries d)
    (universalCharpolySeries_monic d) (universalCharpolySeries_residue d)

end

end GaloisForLFunctions.HTGeometry
