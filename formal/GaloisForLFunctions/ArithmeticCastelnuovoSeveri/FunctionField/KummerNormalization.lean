import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerCyclicCovers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerPowerSubfields
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Normalization of the Kummer affine line

The integral closure of `k[y]` in the actual radical field
`z^(Q+1)=c y(1-y^(b+1))^R` is a finite free Dedekind domain of rank `Q+1`.
Separability follows from the already established cyclic Galois extension.
The radical is integral and gives an explicit element of the normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K]
/-- The polynomial base acts faithfully through its fraction field. -/
instance kummerBranchField_torsionFree (c : Kˣ) (b R n : ℕ) :
    Module.IsTorsionFree K[X] (KummerBranchField c b R n) :=
  Module.IsTorsionFree.trans (FractionRing K[X])

/-- The radical is integral over the polynomial base by its monic equation. -/
theorem kummerBranchField_root_integral (c : Kˣ) (b R n : ℕ) :
    IsIntegral K[X] (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) := by
  refine ⟨X ^ (n + 1) - C (kummerBranch c b R),
    monic_X_pow_sub_C _ (Nat.succ_ne_zero n), ?_⟩
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply]
  exact sub_self _

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
/-- The actual integral closure of the polynomial ring in the Kummer field. -/
abbrev SquareKummerNormalization :=
  integralClosure (SquareConstantField p s)[X] (SquareKummerField p s c b R)

/-- Finite separable normalization preserves the Dedekind property. -/
instance squareKummerNormalization_dedekind :
    IsDedekindDomain (SquareKummerNormalization p s c b R) := by
  letI := squareKummer_isGalois p s c b R
  infer_instance

/-- The normalization is finite over the polynomial base. -/
instance squareKummerNormalization_finite :
    Module.Finite (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R) := by
  letI := squareKummer_isGalois p s c b R
  exact IsIntegralClosure.finite (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R) _

/-- Torsion-freeness over the polynomial PID makes the normalization free. -/
instance squareKummerNormalization_free :
    Module.Free (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R) := by
  letI := squareKummer_isGalois p s c b R
  exact IsIntegralClosure.module_free (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R) _

/-- The normalization has the original Kummer field as its fraction field. -/
instance squareKummerNormalization_fractionRing :
    IsFractionRing (SquareKummerNormalization p s c b R) (SquareKummerField p s c b R) :=
  IsIntegralClosure.isFractionRing_of_finite_extension (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R) _

/-- The module rank of the normalization equals the covering degree. -/
theorem squareKummerNormalization_finrank :
    Module.finrank (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R) =
      p ^ (s + 1) + 1 := by
  letI := squareKummer_isGalois p s c b R
  rw [IsIntegralClosure.rank (SquareConstantField p s)[X]
    (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R)]
  exact kummerBranchField_finrank c b R _

/-- The canonical radical viewed as an element of the integral closure. -/
def squareKummerIntegralRoot : SquareKummerNormalization p s c b R :=
  ⟨AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1))),
    kummerBranchField_root_integral c b R (p ^ (s + 1))⟩

/-- The integral radical satisfies the defining equation inside the normalization. -/
theorem squareKummerIntegralRoot_pow :
    squareKummerIntegralRoot p s c b R ^ (p ^ (s + 1) + 1) =
      algebraMap (SquareConstantField p s)[X] (SquareKummerNormalization p s c b R)
        (kummerBranch c b R) := by
  apply Subtype.ext
  exact (kummerBranchField_root_pow c b R (p ^ (s + 1))).trans
    (IsScalarTower.algebraMap_apply _ _ _ _).symm

/-- The integral radical is nonzero. -/
theorem squareKummerIntegralRoot_ne_zero : squareKummerIntegralRoot p s c b R ≠ 0 := by
  intro h
  exact kummerBranchField_root_ne_zero c b R (p ^ (s + 1))
    (congrArg Subtype.val h)
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
