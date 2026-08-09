import GaloisForLFunctions.HTGeometry.MatrixSemicircleDysonFormalBranch
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebraicity of the formal matrix Dyson branch

Zariski's Main Theorem provides an integral multiplier nonvanishing at the infinity point.  Its
formal-branch image has nonzero constant coefficient and is therefore nonzero in the Laurent-series
field.  This makes every Dyson coordinate algebraic over `ℂ(u)`.  A localization denominator is
then cleared to produce an actual polynomial in `ℂ[u,w]` with nonzero leading coefficient.
-/

open scoped BigOperators Matrix LaurentSeries nonZeroDivisors RatFunc
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

theorem matrixDysonFormalBranch_comp_algebraMap (A : K → Matrix I I ℂ) :
    (matrixDysonFormalBranchHom A).comp
        (algebraMap (Polynomial ℂ) (MatrixDysonInfinityCoordinateRing A)) =
      Polynomial.coeToPowerSeries.ringHom := by
  apply DFunLike.ext _ _
  intro r
  change matrixDysonFormalBranchHom A
      (Ideal.Quotient.mk (matrixDysonInfinityRelationIdeal A) (MvPolynomial.C r)) = _
  rw [matrixDysonFormalBranchHom, Ideal.Quotient.lift_mk]
  simp [matrixDysonFormalAmbientEval]

/-- Formal-branch evaluation followed by the power-series embedding into Laurent series. -/
def matrixDysonFormalBranchLaurentHom (A : K → Matrix I I ℂ) :
    MatrixDysonInfinityCoordinateRing A →+* LaurentSeries ℂ :=
  (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)).comp
    (matrixDysonFormalBranchHom A)

theorem matrixDysonFormalBranchLaurent_comp_base (A : K → Matrix I I ℂ) :
    (matrixDysonFormalBranchLaurentHom A).comp
        (algebraMap (Polynomial ℂ) (MatrixDysonInfinityCoordinateRing A)) =
      (algebraMap (RatFunc ℂ) (LaurentSeries ℂ)).comp
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
  rw [matrixDysonFormalBranchLaurentHom, RingHom.comp_assoc,
    matrixDysonFormalBranch_comp_algebraMap]
  apply DFunLike.ext _ _
  intro r
  exact RatFunc.coe_coe r

/-- Every coordinate-ring element evaluated on the formal branch is algebraic over `ℂ(u)`. -/
theorem matrixDysonFormalBranchLaurent_isIntegral
    (A : K → Matrix I I ℂ) (x : MatrixDysonInfinityCoordinateRing A) :
    IsIntegral (RatFunc ℂ) (matrixDysonFormalBranchLaurentHom A x) := by
  obtain ⟨r, hrp, hrInt, hmul⟩ := matrixDysonInfinity_exists_integral_multiplier A
  obtain ⟨m, hmx⟩ := hmul x
  have hrInt' : IsIntegral (RatFunc ℂ) (matrixDysonFormalBranchLaurentHom A r) :=
    IsIntegral.map_of_comp_eq
      (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (matrixDysonFormalBranchLaurentHom A)
      (matrixDysonFormalBranchLaurent_comp_base A).symm hrInt
  have hmx' : IsIntegral (RatFunc ℂ)
      (matrixDysonFormalBranchLaurentHom A (r ^ m * x)) :=
    IsIntegral.map_of_comp_eq
      (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (matrixDysonFormalBranchLaurentHom A)
      (matrixDysonFormalBranchLaurent_comp_base A).symm hmx
  have hr0 : matrixDysonFormalBranchLaurentHom A r ≠ 0 := by
    intro hzero
    have hps : matrixDysonFormalBranchHom A r = 0 := by
      apply HahnSeries.ofPowerSeries_injective (R := ℂ) (Γ := ℤ)
      simpa [matrixDysonFormalBranchLaurentHom] using hzero
    have hconst := congrArg PowerSeries.constantCoeff hps
    rw [constantCoeff_matrixDysonFormalBranchHom, map_zero] at hconst
    exact hrp hconst
  have hsolve : matrixDysonFormalBranchLaurentHom A x =
      matrixDysonFormalBranchLaurentHom A (r ^ m * x) *
        (matrixDysonFormalBranchLaurentHom A r)⁻¹ ^ m := by
    rw [map_mul, map_pow]
    rw [inv_pow, mul_comm ((matrixDysonFormalBranchLaurentHom A r) ^ m), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero m hr0), mul_one]
  rw [hsolve]
  exact hmx'.mul (hrInt'.inv.pow m)

/-- Coordinate class corresponding to one matrix entry. -/
def matrixDysonInfinityCoordinate (A : K → Matrix I I ℂ) (ij : I × I) :
    MatrixDysonInfinityCoordinateRing A :=
  Ideal.Quotient.mk (matrixDysonInfinityRelationIdeal A) (MvPolynomial.X ij)

@[simp]
theorem matrixDysonFormalBranch_coordinate (A : K → Matrix I I ℂ) (ij : I × I) :
    matrixDysonFormalBranchHom A (matrixDysonInfinityCoordinate A ij) =
      matrixDysonFormalSeries A ij.1 ij.2 := by
  simp [matrixDysonInfinityCoordinate, matrixDysonFormalBranchHom,
    matrixDysonFormalAmbientEval]

theorem matrixDysonFormalSeriesLaurent_isIntegral_ratFunc
    (A : K → Matrix I I ℂ) (i j : I) :
    IsIntegral (RatFunc ℂ)
      ((matrixDysonFormalSeries A i j : PowerSeries ℂ) : LaurentSeries ℂ) := by
  simpa [matrixDysonFormalBranchLaurentHom] using
    matrixDysonFormalBranchLaurent_isIntegral A (matrixDysonInfinityCoordinate A (i, j))

/-- Denominator clearing: a power series algebraic over `ℂ(u)` obeys an actual relation in
`(ℂ[u])[w]` whose leading coefficient is nonzero. -/
theorem powerSeries_bivariateRelation_of_ratFuncIntegral
    (f : PowerSeries ℂ)
    (hf : IsIntegral (RatFunc ℂ) (f : LaurentSeries ℂ)) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      P.eval₂ Polynomial.coeToPowerSeries.ringHom f = 0 := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors (Polynomial ℂ)) (f : LaurentSeries ℂ) hf
  obtain ⟨p, hpMonic, hpRoot⟩ := hm
  have hpDegree : p.natDegree ≠ 0 := by
    intro hp0
    have hpOne : p = 1 := by
      apply Polynomial.eq_one_of_monic_natDegree_zero hpMonic hp0
    simp [hpOne] at hpRoot
  let q : Polynomial (Polynomial ℂ) :=
    Polynomial.C (m : Polynomial ℂ) * Polynomial.X
  let P : Polynomial (Polynomial ℂ) := p.comp q
  have hqDegree : q.natDegree ≠ 0 := by
    simp [q]
  have hqLead : q.leadingCoeff = (m : Polynomial ℂ) := by
    simp [q]
  have hPLead : P.leadingCoeff ≠ 0 := by
    simp only [P]
    rw [Polynomial.leadingCoeff_comp hqDegree, hpMonic.leadingCoeff, one_mul, hqLead]
    exact pow_ne_zero _ (nonZeroDivisors.ne_zero m.2)
  refine ⟨P, hPLead, ?_⟩
  apply HahnSeries.ofPowerSeries_injective (R := ℂ) (Γ := ℤ)
  rw [map_zero, Polynomial.hom_eval₂]
  change Polynomial.eval₂ (algebraMap (Polynomial ℂ) (LaurentSeries ℂ))
      (f : LaurentSeries ℂ) P = 0
  simp only [P]
  rw [Polynomial.eval₂_comp]
  rw [show Polynomial.eval₂ (algebraMap (Polynomial ℂ) (LaurentSeries ℂ))
      (f : LaurentSeries ℂ) q =
        (m : Polynomial ℂ) • (f : LaurentSeries ℂ) by
    simp [q, Algebra.smul_def]]
  exact hpRoot

/-- Every entry of the formal rescaled Dyson branch obeys a nontrivial bivariate polynomial
relation with a nonzero leading coefficient in the entry variable. -/
theorem matrixDysonFormalSeries_exists_bivariateRelation
    (A : K → Matrix I I ℂ) (i j : I) :
    ∃ P : Polynomial (Polynomial ℂ), P.leadingCoeff ≠ 0 ∧
      P.eval₂ Polynomial.coeToPowerSeries.ringHom (matrixDysonFormalSeries A i j) = 0 :=
  powerSeries_bivariateRelation_of_ratFuncIntegral _
    (matrixDysonFormalSeriesLaurent_isIntegral_ratFunc A i j)

end

end GaloisForLFunctions.HTGeometry
