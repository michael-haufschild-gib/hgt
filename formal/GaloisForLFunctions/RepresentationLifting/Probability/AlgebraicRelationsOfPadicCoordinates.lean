import GaloisForLFunctions.RepresentationLifting.Probability.PolynomialZeroSetsInProductMeasure
import GaloisForLFunctions.RHTower.FieldOnePadicProductHaarQuadrature
import Mathlib.Data.Finsupp.Encodable
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Algebraic relations of independent p-adic integers

The algebraic exceptional loci in Maktouf's orbit stratification have
Haar measure zero on affine coordinate spaces. For integral coordinates,
countability of integer polynomials makes this simultaneous over every
nonzero integer relation.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory GaloisForLFunctions.RHTower
noncomputable section
variable (p : ℕ) [Fact p.Prime]

private instance coordinateHaarProbability : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

private theorem padic_coordinate_nullSingleton : NullSingletonClass (fieldOnePadicIntNormalizedHaar p) := by
  let μ := fieldOnePadicIntNormalizedHaar p
  have same (x : ℤ_[p]) : μ {x}=μ {(0:ℤ_[p])} := by simp [μ]
  have hz : μ {(0:ℤ_[p])}=0 := by
    by_contra he
    have ht : μ Set.univ=⊤ := (Set.infinite_univ : (Set.univ : Set ℤ_[p]).Infinite).meas_eq_top
      ⟨μ {(0:ℤ_[p])},he,fun x _ => (same x).ge⟩
    exact (measure_ne_top μ Set.univ) ht
  exact ⟨fun x => (same x).trans hz⟩

/-- Independent normalized additive Haar coordinates on the integral box. -/
abbrev integralCoordinateHaar (n : ℕ) : Measure (Fin n → ℤ_[p]) :=
  fieldOnePadicIntProductNormalizedHaar (ι := Fin n) (fun _ => p)

/-- A nonzero p-adic polynomial is nonvanishing outside a null subset
of the integral box, in every finite dimension. -/
theorem padic_polynomial_zero_null (n : ℕ) (P : MvPolynomial (Fin n) ℤ_[p]) (hP : P≠0) :
    integralCoordinateHaar p n {x | MvPolynomial.eval x P=0}=0 := by
  letI := padic_coordinate_nullSingleton p
  exact mvPolynomial_product_null n (fun _ => fieldOnePadicIntNormalizedHaar p) P hP

/-- With Haar probability one there is no nonzero integer polynomial
relation among the sampled coordinates. The exceptional set is shared
by all degrees and all integer coefficients. -/
theorem ae_padic_no_integer_polynomial_relation (n : ℕ) :
    ∀ᵐ x ∂integralCoordinateHaar p n, ∀ P : MvPolynomial (Fin n) ℤ, P≠0 →
      MvPolynomial.eval₂ (Int.castRingHom ℤ_[p]) x P≠0 := by
  letI := padic_coordinate_nullSingleton p
  letI : Countable (MvPolynomial (Fin n) ℤ) := AddMonoidAlgebra.coeff_injective.countable
  let f := Int.castRingHom ℤ_[p]
  let Q (P : {P : MvPolynomial (Fin n) ℤ // P≠0}) := MvPolynomial.map f P.val
  have hQ (P : {P : MvPolynomial (Fin n) ℤ // P≠0}) : Q P≠0 :=
    fun he => P.property ((MvPolynomial.map_injective f Int.cast_injective) (he.trans (map_zero _).symm))
  filter_upwards [ae_avoids_polynomial_family (fun _ : Fin n => fieldOnePadicIntNormalizedHaar p) Q hQ]
    with x hx P hp
  rw [MvPolynomial.eval₂_eq_eval_map]
  exact hx ⟨P,hp⟩

/-- All minors of a polynomial matrix retain their symbolic vanishing
pattern simultaneously at a Haar-random integral specialization. This
also detects every rank drop of a matrix restricted to an affine family. -/
theorem ae_padic_minor_pattern {n a b : ℕ}
    (A : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) ℤ_[p])) :
    ∀ᵐ x ∂integralCoordinateHaar p n, ∀ (r : ℕ) (i : Fin r → Fin a) (j : Fin r → Fin b),
      ((A.map (MvPolynomial.eval x)).submatrix i j).det=0 ↔ (A.submatrix i j).det=0 := by
  classical
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  let P := (A.submatrix i j).det
  have specialize (x : Fin n → ℤ_[p]) :
      ((A.map (MvPolynomial.eval x)).submatrix i j).det=MvPolynomial.eval x P :=
    ((MvPolynomial.eval x).map_det (A.submatrix i j)).symm
  by_cases h : P=0
  · exact Filter.Eventually.of_forall fun x => ⟨fun _ => h,fun _ => by rw [specialize,h,map_zero]⟩
  · have hae : ∀ᵐ x ∂integralCoordinateHaar p n, MvPolynomial.eval x P≠0 := by
      rw [ae_iff]
      simpa using padic_polynomial_zero_null p n P h
    filter_upwards [hae] with x hx
    rw [specialize]
    exact iff_of_false hx h

/-- The polynomial matrix of an affine pencil, including translation
and any linear restrictions on the random coordinates. -/
def affinePadicPencil {n a b : ℕ} (A : Matrix (Fin a) (Fin b) ℤ_[p])
    (B : Fin n → Matrix (Fin a) (Fin b) ℤ_[p]) :
    Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) ℤ_[p]) :=
  fun i j => MvPolynomial.C (A i j) + ∑ k : Fin n, MvPolynomial.X k*MvPolynomial.C (B k i j)

/-- On an affine slice of a coadjoint-form matrix, a minor vanishes
generically precisely when it vanishes identically on the slice. This
applies to arbitrary structure constants and arbitrary affine directions. -/
theorem ae_affine_padic_pencil_minors {n a b : ℕ} (A : Matrix (Fin a) (Fin b) ℤ_[p])
    (B : Fin n → Matrix (Fin a) (Fin b) ℤ_[p]) :
    ∀ᵐ x ∂integralCoordinateHaar p n, ∀ (r : ℕ) (i : Fin r → Fin a) (j : Fin r → Fin b),
      ((A+∑ k : Fin n, x k • B k).submatrix i j).det=0 ↔
      ∀ y : Fin n → ℤ_[p], ((A+∑ k : Fin n, y k • B k).submatrix i j).det=0 := by
  classical
  let C := affinePadicPencil p A B
  have he (x : Fin n → ℤ_[p]) : C.map (MvPolynomial.eval x) = A+∑ k : Fin n, x k • B k := by
    ext i j
    simp [C,affinePadicPencil,Matrix.sum_apply]
  filter_upwards [ae_padic_minor_pattern p C] with x hx r i j
  refine ⟨fun h y => ?_,fun h => h x⟩
  rw [←he x] at h
  have hz := (hx r i j).mp h
  rw [← he y]
  change ((C.submatrix i j).map (MvPolynomial.eval y)).det=0
  exact ((MvPolynomial.eval y).map_det (C.submatrix i j)).symm.trans (by rw [hz,map_zero])

#print axioms ae_padic_minor_pattern
#print axioms ae_affine_padic_pencil_minors

#print axioms padic_polynomial_zero_null
#print axioms ae_padic_no_integer_polynomial_relation
end
end GaloisForLFunctions.RepresentationLifting
