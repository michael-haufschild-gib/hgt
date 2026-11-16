import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleSpaces
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.AlgebraPointEvaluation
import Mathlib.Data.Int.NatAbs

/-!
# Evaluation and multiplication on Kummer pole spaces

Every affine normalization element has some finite infinity pole bound.
Finite interpolation therefore takes place in a sufficiently large pole
space. Multiplication by a nonzero function injects one pole space into
a shifted space and, at its zeros, into the evaluation kernel.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) R
local notation "A" => SquareKummerNormalization p s c (p ^ (d + 1) - 2) R
local notation "P" => squareKummerPoleSpace p s c d r
local notation "v" => squareKummerInfinityValuation p s c d r

/-- Increasing the allowed pole order enlarges the actual pole space. -/
theorem squareKummerPoleSpace_mono : Monotone P := by
  intro m n hmn x hx
  have hx' := (mem_squareKummerPoleSpace_iff p s c d r m x).mp hx
  apply (mem_squareKummerPoleSpace_iff p s c d r n x).mpr
  exact ⟨hx'.1, hx'.2.trans (WithZero.exp_le_exp.mpr (by exact_mod_cast hmn))⟩

private theorem exists_nat_exp_bound (a : WithZero (Multiplicative ℤ)) :
    ∃ m : ℕ, a ≤ WithZero.exp (m : ℤ) := by
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha]; exact zero_le⟩
  · refine ⟨a.log.natAbs, ?_⟩
    calc
      a = WithZero.exp a.log := (WithZero.exp_log ha).symm
      _ ≤ WithZero.exp (a.log.natAbs : ℤ) := WithZero.exp_le_exp.mpr Int.le_natAbs

/-- The bounded-pole spaces exhaust the affine normalization. -/
theorem squareKummerNormalization_exists_pole_bound (x : A) :
    ∃ m : ℕ, x.val ∈ P m := by
  obtain ⟨m, hm⟩ := exists_nat_exp_bound (v x.val)
  exact ⟨m, (mem_squareKummerPoleSpace_iff p s c d r m x.val).mpr ⟨x.property, hm⟩⟩

/-- A bounded-pole function is an element of the actual affine normalization. -/
def squareKummerPoleNormalizationMap (m : ℕ) : P m →ₗ[K] A where
  toFun x := ⟨x.val, ((mem_squareKummerPoleSpace_iff p s c d r m x.val).mp x.property).1⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

variable {ι : Type*}

/-- Evaluation of bounded-pole functions at a family of rational normalization points. -/
def squareKummerPoleEvaluation (m : ℕ) (φ : ι → A →ₐ[K] K) : P m →ₗ[K] (ι → K) :=
  (Codes.algebraPointEvaluation φ).comp (squareKummerPoleNormalizationMap p s c d r m)

/-- Pole-space evaluation is literal evaluation in the affine normalization. -/
theorem squareKummerPoleEvaluation_apply (m : ℕ) (φ : ι → A →ₐ[K] K) (x : P m) (i : ι) :
    squareKummerPoleEvaluation p s c d r m φ x i =
      φ i (squareKummerPoleNormalizationMap p s c d r m x) := rfl

/-- Every finite set of distinct rational points admits arbitrary interpolation within all sufficiently large pole spaces. -/
theorem squareKummerPoleEvaluation_eventually_surjective [Fintype ι]
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      Function.Surjective (squareKummerPoleEvaluation p s c d r m φ) := by
  classical
  have hsurj := Codes.algebraPointEvaluation_surjective φ hφ
  choose a ha using fun i : ι => hsurj (fun j => if i = j then 1 else 0)
  choose b hb using fun i : ι => squareKummerNormalization_exists_pole_bound p s c d r (a i)
  let M := Finset.univ.sup b
  refine ⟨M, ?_⟩
  intro m hMm z
  have hm (i : ι) : (a i).val ∈ P m := by
    have hbi : b i ≤ M := Finset.le_sup (Finset.mem_univ i)
    exact squareKummerPoleSpace_mono p s c d r (hbi.trans hMm) (hb i)
  let a' (i : ι) : P m := ⟨(a i).val, hm i⟩
  refine ⟨∑ i, z i • a' i, ?_⟩
  ext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, z i * φ j (a i)) = z j
  have hai (i : ι) : φ j (a i) = if i = j then 1 else 0 := congrFun (ha i) j
  simp only [hai, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Multiplication adds the allowed infinity pole orders. -/
def squareKummerPoleMultiplication (m n : ℕ) (f : P m) : P n →ₗ[K] P (m + n) where
  toFun x := ⟨f.val * x.val, by
    have hf := (mem_squareKummerPoleSpace_iff p s c d r m f.val).mp f.property
    have hx := (mem_squareKummerPoleSpace_iff p s c d r n x.val).mp x.property
    apply (mem_squareKummerPoleSpace_iff p s c d r (m + n) (f.val * x.val)).mpr
    refine ⟨hf.1.mul hx.1, ?_⟩
    calc
      v (f.val * x.val) = v f.val * v x.val := map_mul _ _ _
      _ ≤ WithZero.exp (m : ℤ) * WithZero.exp (n : ℤ) := mul_le_mul' hf.2 hx.2
      _ = WithZero.exp ((m + n : ℕ) : ℤ) := by rw [← WithZero.exp_add, Nat.cast_add]⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' t x := Subtype.ext (mul_smul_comm t f.val x.val)

/-- A nonzero bounded-pole function acts injectively by multiplication. -/
theorem squareKummerPoleMultiplication_injective (m n : ℕ) (f : P m) (hf : f.val ≠ 0) :
    Function.Injective (squareKummerPoleMultiplication p s c d r m n f) := by
  intro x y h
  exact Subtype.ext (mul_left_cancel₀ hf (congrArg Subtype.val h))

/-- At zeros of the multiplier, its entire shifted pole-space image has zero evaluation. -/
theorem squareKummerPoleMultiplication_evaluation_zero (m n : ℕ) (f : P m)
    (φ : ι → A →ₐ[K] K)
    (hf : ∀ i, φ i (squareKummerPoleNormalizationMap p s c d r m f) = 0) (x : P n) :
    squareKummerPoleEvaluation p s c d r (m + n) φ
      (squareKummerPoleMultiplication p s c d r m n f x) = 0 := by
  ext i
  change φ i ((squareKummerPoleNormalizationMap p s c d r m f) *
    (squareKummerPoleNormalizationMap p s c d r n x)) = 0
  rw [map_mul, hf i, zero_mul]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
