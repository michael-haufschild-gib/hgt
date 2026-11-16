import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusBranchCovariance
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalMobiusCoordinates
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Determinant-one automorphisms of Frobenius radical fields

For a finite field of order `q` inside the constants, the radical equation
of degree `(q²-q)R+q+1` is preserved by every determinant-one substitution
`x↦(ax+b)/(cx+d)`, `z↦z/(cx+d)`. Projective covariance proves the equation;
the inverse rational substitution recovers the base field, and the linear
denominator then recovers the radical. Thus the lift is an automorphism.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial Matrix ArithmeticHarmonicAnalysis
variable (K E : Type*) [Field K] [Fintype K] [Field E] [Algebra K E]

/-- The Frobenius radical degree matched to determinant-one projective covariance. -/
abbrev FrobeniusSpecialLinearField (γ : Eˣ) (R : ℕ) :=
  FrobeniusKummerField γ (Fintype.card K - 2) R
    (((Fintype.card K) ^ 2 - Fintype.card K) * R + Fintype.card K)

omit [Fintype K] in
private theorem matrix_det_one (M : SpecialLinearGroup (Fin 2) K) :
    M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using M.property

/-- The induced Möbius automorphism on the original rational base field. -/
def frobeniusSpecialLinearBaseEquiv (M : SpecialLinearGroup (Fin 2) K) :
    FractionRing E[X] ≃ₐ[E] FractionRing E[X] :=
  fractionRingMobiusEquiv (algebraMap K E (M 0 0)) (algebraMap K E (M 0 1))
    (algebraMap K E (M 1 0)) (algebraMap K E (M 1 1)) (by
      intro h
      have he := congrArg (algebraMap K E) (matrix_det_one K M)
      rw [map_sub, map_mul, map_mul, map_one] at he
      exact zero_ne_one (h.symm.trans he))

variable (γ : Eˣ) (R : ℕ)
local notation "q" => Fintype.card K
local notation "n" => (q ^ 2 - q) * R + q
local notation "F" => FractionRing E[X]
local notation "L" => FrobeniusSpecialLinearField K E γ R
local notation "x" => algebraMap E[X] L X
local notation "z" => AdjoinRoot.root (frobeniusKummerFieldPolynomial γ (q - 2) R n)

/-- The linear denominator, embedded through the stated constant field. -/
def frobeniusSpecialLinearDenominator (M : SpecialLinearGroup (Fin 2) K) : L :=
  algebraMap E L (algebraMap K E (M 1 0)) * x + algebraMap E L (algebraMap K E (M 1 1))

/-- The transformed rational coordinate in the actual radical field. -/
def frobeniusSpecialLinearCoordinate (M : SpecialLinearGroup (Fin 2) K) : L :=
  (algebraMap E L (algebraMap K E (M 0 0)) * x + algebraMap E L (algebraMap K E (M 0 1))) /
    frobeniusSpecialLinearDenominator K E γ R M

/-- A determinant-one matrix cannot have a vanishing denominator at a transcendental coordinate. -/
theorem frobeniusSpecialLinearDenominator_ne_zero (M : SpecialLinearGroup (Fin 2) K) :
    frobeniusSpecialLinearDenominator K E γ R M ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap E[X] L) := by
    rw [IsScalarTower.algebraMap_eq E[X] F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective E[X] F)
  have hC (a : E) : algebraMap E[X] L (C a) = algebraMap E L a :=
    (IsScalarTower.algebraMap_apply E E[X] L a).symm
  have hp : (C (algebraMap K E (M 1 0)) * X + C (algebraMap K E (M 1 1)) : E[X]) = 0 := by
    apply hinj
    rw [map_zero, map_add, map_mul, hC, hC]
    exact h
  have hc : algebraMap K E (M 1 0) = 0 := by
    have hh := congrArg (fun f : E[X] => f.coeff 1) hp
    simpa using hh
  have hd : algebraMap K E (M 1 1) = 0 := by
    have hh := congrArg (fun f : E[X] => f.coeff 0) hp
    simpa using hh
  have he := congrArg (algebraMap K E) (matrix_det_one K M)
  rw [map_sub, map_mul, map_mul, map_one, hc, hd, mul_zero, mul_zero, sub_self] at he
  exact zero_ne_one he

omit [Algebra K E] in
/-- The actual radical equation has the two Frobenius branch factors. -/
theorem frobeniusSpecialLinearField_root_equation :
    z ^ (n + 1) = algebraMap E L γ * (x ^ q - x) * (1 + (x ^ q - x) ^ (q - 1)) ^ R := by
  have hq : 2 ≤ q := Fintype.one_lt_card
  have he := congrArg (fun f : E[X] →ₐ[E] L => f (frobeniusKummerBranch γ (q - 2) R))
    (frobeniusKummerField_aeval_coordinate γ (q - 2) R n)
  calc
    z ^ (n + 1) = algebraMap E[X] L (frobeniusKummerBranch γ (q - 2) R) := by
      rw [frobeniusKummerField_root_pow, ← IsScalarTower.algebraMap_apply]
    _ = aeval x (frobeniusKummerBranch γ (q - 2) R) := he.symm
    _ = _ := by
      rw [frobeniusKummerBranch_aeval, Nat.sub_add_cancel hq,
        show q - 2 + 1 = q - 1 by omega]

omit [Algebra K E] in
/-- The first Frobenius branch factor is nonzero at the actual rational coordinate. -/
theorem frobeniusSpecialLinearField_additive_ne_zero : x ^ q - x ≠ 0 := by
  intro h
  have he := frobeniusSpecialLinearField_root_equation K E γ R
  rw [h, mul_zero, zero_mul] at he
  exact (pow_ne_zero _ (frobeniusKummerField_root_ne_zero γ (q - 2) R n)) he

private theorem lifted_base_coordinate (M : SpecialLinearGroup (Fin 2) K) :
    algebraMap F L (frobeniusSpecialLinearBaseEquiv K E M (algebraMap E[X] F X)) =
      frobeniusSpecialLinearCoordinate K E γ R M := by
  rw [frobeniusSpecialLinearBaseEquiv, fractionRingMobiusEquiv_coordinate]
  simp only [map_div₀, map_add, map_mul,
    ← IsScalarTower.algebraMap_apply E F L, ← IsScalarTower.algebraMap_apply E[X] F L]
  rfl

private theorem transformed_root_eval (M : SpecialLinearGroup (Fin 2) K) :
    (frobeniusKummerFieldPolynomial γ (q - 2) R n).eval₂
      ((IsScalarTower.toAlgHom E F L).comp (frobeniusSpecialLinearBaseEquiv K E M).toAlgHom)
      (z / frobeniusSpecialLinearDenominator K E γ R M) = 0 := by
  let f := (IsScalarTower.toAlgHom E F L).comp (frobeniusSpecialLinearBaseEquiv K E M).toAlgHom
  let D := frobeniusSpecialLinearDenominator K E γ R M
  let u := frobeniusSpecialLinearCoordinate K E γ R M
  have hhom : f.comp (IsScalarTower.toAlgHom E E[X] F) = aeval u := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    exact lifted_base_coordinate K E γ R M
  have hf : f (algebraMap E[X] F (frobeniusKummerBranch γ (q - 2) R)) =
      aeval u (frobeniusKummerBranch γ (q - 2) R) :=
    congrArg (fun g : E[X] →ₐ[E] L => g (frobeniusKummerBranch γ (q - 2) R)) hhom
  letI : Algebra K L := Algebra.compHom L (algebraMap K E)
  have hc := finiteField_frobeniusBranch_covariance (M 0 0) (M 0 1) (M 1 0) (M 1 1)
    (algebraMap E L γ) x R (matrix_det_one K M)
    (frobeniusSpecialLinearField_additive_ne_zero K E γ R) (frobeniusSpecialLinearDenominator_ne_zero K E γ R M)
  change algebraMap E L γ * (u ^ q - u) * (1 + (u ^ q - u) ^ (q - 1)) ^ R =
    (algebraMap E L γ * (x ^ q - x) * (1 + (x ^ q - x) ^ (q - 1)) ^ R) /
      D ^ (q + 1 + (q ^ 2 - q) * R) at hc
  rw [show q + 1 + (q ^ 2 - q) * R = n + 1 by omega,
    ← frobeniusSpecialLinearField_root_equation K E γ R] at hc
  change (X ^ (n + 1) - C (algebraMap E[X] F (frobeniusKummerBranch γ (q - 2) R))).eval₂
    f (z / D) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero, div_pow]
  change z ^ (n + 1) / D ^ (n + 1) =
    f (algebraMap E[X] F (frobeniusKummerBranch γ (q - 2) R))
  rw [hf, frobeniusKummerBranch_aeval, Nat.sub_add_cancel (show 2 ≤ q from Fintype.one_lt_card),
    show q - 2 + 1 = q - 1 by have hq : 2 ≤ q := Fintype.one_lt_card; omega]
  exact hc.symm

/-- Every determinant-one projective substitution lifts to the actual Frobenius radical field. -/
def frobeniusSpecialLinearHom (M : SpecialLinearGroup (Fin 2) K) : L →ₐ[E] L :=
  AdjoinRoot.liftAlgHom _
    ((IsScalarTower.toAlgHom E F L).comp (frobeniusSpecialLinearBaseEquiv K E M).toAlgHom)
    (z / frobeniusSpecialLinearDenominator K E γ R M) (transformed_root_eval K E γ R M)

/-- The lifted map restricts to the prescribed rational-base Möbius automorphism. -/
theorem frobeniusSpecialLinearHom_base (M : SpecialLinearGroup (Fin 2) K) (a : F) :
    frobeniusSpecialLinearHom K E γ R M (algebraMap F L a) =
      algebraMap F L (frobeniusSpecialLinearBaseEquiv K E M a) := by
  rw [AdjoinRoot.algebraMap_eq, frobeniusSpecialLinearHom, AdjoinRoot.liftAlgHom_of]
  rfl

/-- The lifted coordinate is the prescribed fractional-linear expression. -/
theorem frobeniusSpecialLinearHom_coordinate (M : SpecialLinearGroup (Fin 2) K) :
    frobeniusSpecialLinearHom K E γ R M x = frobeniusSpecialLinearCoordinate K E γ R M := by
  rw [IsScalarTower.algebraMap_apply E[X] F L, frobeniusSpecialLinearHom_base]
  exact lifted_base_coordinate K E γ R M

/-- The lifted radical is divided by the linear denominator. -/
theorem frobeniusSpecialLinearHom_root (M : SpecialLinearGroup (Fin 2) K) :
    frobeniusSpecialLinearHom K E γ R M z = z / frobeniusSpecialLinearDenominator K E γ R M :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The inverse base substitution and the nonzero denominator recover both field generators. -/
theorem frobeniusSpecialLinearHom_surjective (M : SpecialLinearGroup (Fin 2) K) :
    Function.Surjective (frobeniusSpecialLinearHom K E γ R M) := by
  let f := frobeniusSpecialLinearHom K E γ R M
  let e := frobeniusSpecialLinearBaseEquiv K E M
  have hbase (a : F) : algebraMap F L a ∈ f.fieldRange := by
    refine ⟨algebraMap F L (e.symm a), ?_⟩
    exact (frobeniusSpecialLinearHom_base K E γ R M (e.symm a)).trans
      (congrArg (algebraMap F L) (e.apply_symm_apply a))
  have hx : x ∈ f.fieldRange := by
    rw [IsScalarTower.algebraMap_apply E[X] F L]
    exact hbase _
  have hD : frobeniusSpecialLinearDenominator K E γ R M ∈ f.fieldRange :=
    f.fieldRange.add_mem (f.fieldRange.mul_mem (f.fieldRange.algebraMap_mem _) hx)
      (f.fieldRange.algebraMap_mem _)
  have hz : z ∈ f.fieldRange := by
    have hquot : z / frobeniusSpecialLinearDenominator K E γ R M ∈ f.fieldRange :=
      ⟨z, frobeniusSpecialLinearHom_root K E γ R M⟩
    have hh := f.fieldRange.mul_mem hquot hD
    rw [div_mul_cancel₀ _ (frobeniusSpecialLinearDenominator_ne_zero K E γ R M)] at hh
    exact hh
  have htop := frobeniusKummerField_eq_top_of_coordinate_root_mem γ (q - 2) R n f.fieldRange hx hz
  intro a
  have ha : a ∈ f.fieldRange := by rw [htop]; trivial
  exact ha

/-- Determinant-one substitutions give actual automorphisms over the specified larger constant field. -/
def frobeniusSpecialLinearAut (M : SpecialLinearGroup (Fin 2) K) : L ≃ₐ[E] L :=
  AlgEquiv.ofBijective (frobeniusSpecialLinearHom K E γ R M)
    ⟨(frobeniusSpecialLinearHom K E γ R M).injective,
      frobeniusSpecialLinearHom_surjective K E γ R M⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
