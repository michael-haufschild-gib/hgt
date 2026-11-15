import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerGeometricExponentReduction
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Algebraic.Integral

/-!
# A rational parameter for the exponent-zero Kummer model

In `z^(n+1) = c*x`, the radical is transcendental and generates the whole
function field over the constants: `x = c⁻¹*z^(n+1)`. This constructs an
actual rational-function-field isomorphism and, by exponent reduction,
rational parametrizations for every even geometric-sum branch exponent.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K]

/-- The original base coordinate is a polynomial in the radical. -/
theorem kummerZeroExponent_coordinate (c : Kˣ) (b n : ℕ) :
    algebraMap K[X] (KummerBranchField c b 0 n) X =
      algebraMap K (KummerBranchField c b 0 n) (c : K)⁻¹ *
        AdjoinRoot.root (kummerBranchFieldPolynomial c b 0 n) ^ (n + 1) := by
  rw [kummerBranchField_root_pow,
    ← IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) (KummerBranchField c b 0 n)]
  simp only [kummerBranch, pow_zero, mul_one, map_mul]
  change _ = algebraMap K (KummerBranchField c b 0 n) (c : K)⁻¹ *
    (algebraMap K (KummerBranchField c b 0 n) (c : K) * _)
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (Units.ne_zero c), map_one, one_mul]

/-- The radical is transcendental because the original base coordinate is transcendental. -/
theorem kummerZeroExponent_root_transcendental (c : Kˣ) (b n : ℕ) :
    Transcendental K (AdjoinRoot.root (kummerBranchFieldPolynomial c b 0 n)) := by
  have hinj : Function.Injective (algebraMap K[X] (KummerBranchField c b 0 n)) := by
    rw [IsScalarTower.algebraMap_eq K[X] (FractionRing K[X]) (KummerBranchField c b 0 n)]
    exact (algebraMap (FractionRing K[X]) (KummerBranchField c b 0 n)).injective.comp
      (IsFractionRing.injective K[X] (FractionRing K[X]))
  have hx := (transcendental_algebraMap_iff hinj).mpr (Polynomial.transcendental_X K)
  rw [kummerZeroExponent_coordinate c b n] at hx
  have he : Transcendental K (aeval (AdjoinRoot.root (kummerBranchFieldPolynomial c b 0 n))
      (C ((c : K)⁻¹) * X ^ (n + 1))) := by
    simpa only [map_mul, map_pow, aeval_C, aeval_X] using hx
  exact (transcendental_aeval_iff.mp he).1

/-- The radical generates the entire function field over the constants. -/
theorem kummerZeroExponent_adjoin_root (c : Kˣ) (b n : ℕ) :
    IntermediateField.adjoin K {AdjoinRoot.root (kummerBranchFieldPolynomial c b 0 n)} = ⊤ := by
  let S := IntermediateField.adjoin K {AdjoinRoot.root (kummerBranchFieldPolynomial c b 0 n)}
  have hz : AdjoinRoot.root (kummerBranchFieldPolynomial c b 0 n) ∈ S :=
    IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  have hx : algebraMap K[X] (KummerBranchField c b 0 n) X ∈ S := by
    rw [kummerZeroExponent_coordinate]
    exact S.mul_mem (S.algebraMap_mem _) (S.toSubalgebra.pow_mem hz (n + 1))
  have hpoly (P : K[X]) : algebraMap K[X] (KummerBranchField c b 0 n) P ∈ S := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => rw [map_add]; exact S.add_mem hP hQ
    | monomial j a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact S.mul_mem (S.algebraMap_mem a) (S.toSubalgebra.pow_mem hx j)
  have hbase (a : FractionRing K[X]) :
      algebraMap (FractionRing K[X]) (KummerBranchField c b 0 n) a ∈ S := by
    obtain ⟨P, Q, _, rfl⟩ := IsFractionRing.div_surjective K[X] a
    rw [map_div₀, ← IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) (KummerBranchField c b 0 n),
      ← IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) (KummerBranchField c b 0 n)]
    exact S.div_mem (hpoly P) (hpoly Q)
  have hall : ∀ y : KummerBranchField c b 0 n, y ∈ S := by
    intro y
    induction y using AdjoinRoot.induction_on with
    | ih P =>
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ => rw [map_add]; exact S.add_mem hP hQ
      | monomial j a =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X]
        exact S.mul_mem (hbase a) (S.toSubalgebra.pow_mem hz j)
  exact top_unique (fun y _ => hall y)

/-- Evaluation at the radical is a rational-function-field isomorphism. -/
def kummerZeroExponentRationalEquiv (c : Kˣ) (b n : ℕ) :
    RatFunc K ≃ₐ[K] KummerBranchField c b 0 n :=
  (RatFunc.algEquivOfTranscendental _ (kummerZeroExponent_root_transcendental c b n)).trans
    ((IntermediateField.equivOfEq (kummerZeroExponent_adjoin_root c b n)).trans
      IntermediateField.topEquiv)

theorem kummerZeroExponentRationalEquiv_X (c : Kˣ) (b n : ℕ) :
    kummerZeroExponentRationalEquiv c b n RatFunc.X =
      AdjoinRoot.root (kummerBranchFieldPolynomial c b 0 n) := by
  change (RatFunc.algEquivOfTranscendental _ (kummerZeroExponent_root_transcendental c b n)
    RatFunc.X : KummerBranchField c b 0 n) = _
  exact RatFunc.algEquivOfTranscendental_X _ _

theorem kummerZeroExponentRationalEquiv_coordinate (c : Kˣ) (b n : ℕ) :
    kummerZeroExponentRationalEquiv c b n
        (algebraMap K (RatFunc K) (c : K)⁻¹ * RatFunc.X ^ (n + 1)) =
      algebraMap K[X] (KummerBranchField c b 0 n) X := by
  rw [map_mul, map_pow, AlgEquiv.commutes, kummerZeroExponentRationalEquiv_X]
  exact (kummerZeroExponent_coordinate c b n).symm

/-- Even geometric-sum exponents give rational function fields over the original constants. -/
def kummerEvenGeometricRationalEquiv (c : Kˣ) (b q n : ℕ) :
    RatFunc K ≃ₐ[K] KummerBranchField c b (ArithmeticHarmonicAnalysis.kummerExponent q (2 * n)) q :=
  (kummerZeroExponentRationalEquiv c b q).trans
    ((kummerGeometricExponentEvenEquiv c b q n).symm.restrictScalars K)

#print axioms kummerZeroExponentRationalEquiv
#print axioms kummerEvenGeometricRationalEquiv
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
