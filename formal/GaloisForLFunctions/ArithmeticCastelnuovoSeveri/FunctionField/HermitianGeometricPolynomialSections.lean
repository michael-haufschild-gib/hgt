import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPoleExpansions
import GaloisForLFunctions.HTGeometry.MvPolynomialProjectiveChartPrime
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Homogeneous polynomial sections on the geometric Hermitian curve

The reduced pole expansion produces a bivariate polynomial of total degree
at most `d`. Homogenizing to degree `d` represents every function whose only
pole is at infinity of order at most `d(Q+1)`, for `d<Q`.
The projective coordinates are `(1,z,y)`, where `y` is the nonzero constant
multiple of the additive Hermitian coordinate.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open scoped BigOperators

private def coefficientMonomial {K : Type*} [Field K] (i j : ℕ) (c : K) : MvPolynomial Bool K :=
  MvPolynomial.C c * MvPolynomial.X false ^ i * MvPolynomial.X true ^ j

private theorem coefficientMonomial_degree {K : Type*} [Field K] (i j : ℕ) (c : K) :
    (coefficientMonomial i j c).totalDegree ≤ i + j := by
  have h₁ := MvPolynomial.totalDegree_mul (MvPolynomial.C c : MvPolynomial Bool K)
    (MvPolynomial.X false ^ i)
  have h₂ := MvPolynomial.totalDegree_mul
    (MvPolynomial.C c * MvPolynomial.X false ^ i : MvPolynomial Bool K)
    (MvPolynomial.X true ^ j)
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, zero_add] at h₁ h₂
  exact h₂.trans (Nat.add_le_add_right h₁ j)

private def coefficientPolynomial {K : Type*} [Field K] {N : ℕ}
    (a : Fin N → Polynomial K) : MvPolynomial Bool K :=
  ∑ i, ∑ j ∈ (a i).support, coefficientMonomial i.val j ((a i).coeff j)

private theorem coefficientPolynomial_degree {K : Type*} [Field K] {N d : ℕ}
    (a : Fin N → Polynomial K) (ha : ∀ i, a i ≠ 0 → i.val + (a i).natDegree ≤ d) :
    (coefficientPolynomial a).totalDegree ≤ d := by
  classical
  unfold coefficientPolynomial
  refine (MvPolynomial.totalDegree_finsetSum (R := K) (σ := Bool) Finset.univ
    (fun i : Fin N => ∑ j ∈ (a i).support,
      coefficientMonomial i.val j ((a i).coeff j))).trans ?_
  apply Finset.sup_le
  intro i _
  refine (MvPolynomial.totalDegree_finsetSum (R := K) (σ := Bool) (a i).support
    (fun j => coefficientMonomial i.val j ((a i).coeff j))).trans ?_
  apply Finset.sup_le
  intro j hj
  have hcoeff : (a i).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hai : a i ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, Polynomial.coeff_zero])
  have hjdeg := Polynomial.le_natDegree_of_ne_zero hcoeff
  exact (coefficientMonomial_degree i.val j ((a i).coeff j)).trans
    ((Nat.add_le_add_left hjdeg i.val).trans (ha i hai))

private theorem coefficientPolynomial_aeval
    {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}
    (a : Fin N → Polynomial K) (z y : L) :
    MvPolynomial.aeval (fun b => Bool.rec z y b) (coefficientPolynomial a) =
      ∑ i, Polynomial.aeval y (a i) * z ^ i.val := by
  classical
  rw [coefficientPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  simp only [coefficientMonomial, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "y" => algebraMap E[X] H X

/-- Evaluation of a projective polynomial in the actual affine chart `(1,z,y)`. -/
def hermitianGeometricSectionValue (F : MvPolynomial (Option Bool) E) : H :=
  MvPolynomial.aeval (fun b => Bool.rec z y b) (optionHeadDehomogenize F)

/-- The zero homogeneous polynomial gives the zero function. -/
theorem hermitianGeometricSectionValue_zero : hermitianGeometricSectionValue p s 0 = 0 := by
  simp only [hermitianGeometricSectionValue, map_zero]

/-- Homogenize the reduced coefficient polynomial to the specified section degree. -/
def hermitianGeometricHomogeneousExpansion (a : Fin (Q + 1) → E[X]) (d : ℕ) :
    MvPolynomial (Option Bool) E := optionHeadHomogenize (coefficientPolynomial a) d

/-- The constructed section is homogeneous of its prescribed degree. -/
theorem hermitianGeometricHomogeneousExpansion_isHomogeneous
    (a : Fin (Q + 1) → E[X]) (d : ℕ) :
    (hermitianGeometricHomogeneousExpansion p s a d).IsHomogeneous d :=
  optionHeadHomogenize_isHomogeneous _ _

/-- A total-degree bound makes homogeneous evaluation recover the original rational function. -/
theorem hermitianGeometricHomogeneousExpansion_value (a : Fin (Q + 1) → E[X]) (d : ℕ)
    (ha : ∀ i, a i ≠ 0 → i.val + (a i).natDegree ≤ d) :
    hermitianGeometricSectionValue p s (hermitianGeometricHomogeneousExpansion p s a d) =
      hermitianGeometricPolynomialExpansion p s a := by
  rw [hermitianGeometricSectionValue, hermitianGeometricHomogeneousExpansion,
    optionHeadDehomogenize_optionHeadHomogenize _ _ (coefficientPolynomial_degree a ha),
    coefficientPolynomial_aeval]
  have hhom : Polynomial.aeval y = IsScalarTower.toAlgHom E E[X] H := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  apply Finset.sum_congr rfl
  intro i _
  have hi : Polynomial.aeval y (a i) = algebraMap E[X] H (a i) :=
    congrArg (fun h : E[X] →ₐ[E] H => h (a i)) hhom
  rw [hi]

/-- Every function with a sole infinity pole bounded by `d(Q+1)`, `d<Q`, is a homogeneous section. -/
theorem hermitianGeometric_exists_homogeneousSection (f : H) (d : ℕ) (hd : d < Q)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hInfinity : hermitianGeometricInfinityValuation p s f ≤
      WithZero.exp ((d * (Q + 1) : ℕ) : ℤ)) :
    ∃ F : MvPolynomial (Option Bool) E, F.IsHomogeneous d ∧
      hermitianGeometricSectionValue p s F = f := by
  obtain ⟨a, ha, hb⟩ := hermitianGeometric_exists_lowDegree_polynomial_expansion p s f d hd hf hInfinity
  exact ⟨hermitianGeometricHomogeneousExpansion p s a d,
    hermitianGeometricHomogeneousExpansion_isHomogeneous p s a d,
    (hermitianGeometricHomogeneousExpansion_value p s a d hb).trans ha.symm⟩

/-- A nonzero bounded-pole function is represented by a nonzero homogeneous polynomial. -/
theorem hermitianGeometric_exists_nonzero_homogeneousSection (f : H) (hzero : f ≠ 0)
    (d : ℕ) (hd : d < Q) (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hInfinity : hermitianGeometricInfinityValuation p s f ≤
      WithZero.exp ((d * (Q + 1) : ℕ) : ℤ)) :
    ∃ F : MvPolynomial (Option Bool) E, F ≠ 0 ∧ F.IsHomogeneous d ∧
      hermitianGeometricSectionValue p s F = f := by
  obtain ⟨F, hF, heq⟩ := hermitianGeometric_exists_homogeneousSection p s f d hd hf hInfinity
  refine ⟨F, ?_, hF, heq⟩
  intro h
  apply hzero
  rw [← heq, h, hermitianGeometricSectionValue_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
