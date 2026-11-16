import GaloisForLFunctions.RepresentationLifting.Probability.NilpotentReduction
import GaloisForLFunctions.RepresentationLifting.Probability.NilpotentMatrixCardinality
import Mathlib.Algebra.Field.ZMod

/-!
# Nilpotent matrices modulo prime powers

Reduction modulo `p` detects nilpotence over `ZMod (p^(r+1))`: a matrix
in the reduction kernel is a scalar multiple of `p`, so its `(r+1)`st
power vanishes. Equal additive fibers then transfer the finite-field
nilpotent count to every prime-power level.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open OperatorKernels

/-- Reduction from a positive prime-power level to its residue ring. -/
def primePowerResidue (p r : ℕ) : ZMod (p ^ (r + 1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero r)) (ZMod p)

/-- Entrywise reduction of square matrices to the residue ring. -/
def primePowerMatrixReduction (p r : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι (ZMod (p ^ (r + 1))) →+* Matrix ι ι (ZMod p) :=
  (primePowerResidue p r).mapMatrix

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem primePowerResidue_surjective (r : ℕ) : Function.Surjective (primePowerResidue p r) :=
  ZMod.castHom_surjective _

omit [Fact p.Prime] in
theorem primePowerMatrixReduction_surjective (r : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Surjective (primePowerMatrixReduction p r ι) := by
  intro A
  choose B hB using fun i j => primePowerResidue_surjective p r (A i j)
  refine ⟨B, ?_⟩
  ext i j
  exact hB i j

/-- A zero residue means divisibility by `p` in the prime-power ring itself. -/
theorem primePowerResidue_eq_zero_mul (r : ℕ) (a : ZMod (p ^ (r + 1)))
    (ha : primePowerResidue p r a = 0) :
    a = (p : ZMod (p ^ (r + 1))) * (a.val / p : ℕ) := by
  change ZMod.cast a = (0 : ZMod p) at ha
  rw [ZMod.cast_eq_val] at ha
  have hd : p ∣ a.val := (CharP.cast_eq_zero_iff (ZMod p) p a.val).mp ha
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hd, ZMod.natCast_zmod_val]

/-- The entire matrix reduction kernel has a uniform nilpotence exponent. -/
theorem primePowerMatrixReduction_kernel_pow (r : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod (p ^ (r + 1)))) (hA : primePowerMatrixReduction p r ι A = 0) :
    A ^ (r + 1) = 0 := by
  let B : Matrix ι ι (ZMod (p ^ (r + 1))) := fun i j => ((A i j).val / p : ℕ)
  have hB : A = (p : ZMod (p ^ (r + 1))) • B := by
    ext i j
    exact primePowerResidue_eq_zero_mul p r (A i j) (congrFun (congrFun hA i) j)
  have hp : (p : ZMod (p ^ (r + 1))) ^ (r + 1) = 0 := by
    rw [← Nat.cast_pow, CharP.cast_eq_zero]
  rw [hB, smul_pow, hp, zero_smul]

/-- Nilpotence is detected modulo the residue prime, at every finite prime-power level. -/
theorem primePowerMatrix_isNilpotent_iff (r : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod (p ^ (r + 1)))) :
    IsNilpotent A ↔ IsNilpotent (primePowerMatrixReduction p r ι A) :=
  (isNilpotent_map_iff_of_nilpotent_kernel (primePowerMatrixReduction p r ι)
    (fun B hB => ⟨r + 1, primePowerMatrixReduction_kernel_pow p r B hB⟩) A).symm

/-- The exact nilpotent count over `ZMod (p^(r+1))`. -/
theorem card_primePower_nilpotent_matrices (r n : ℕ) :
    Nat.card {A : Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1))) // IsNilpotent A} =
      p ^ (r * (n * n) + n * (n - 1)) := by
  have hc := card_nilpotent_reduction_mul_card (primePowerMatrixReduction p r (Fin n))
    (primePowerMatrixReduction_surjective p r (Fin n))
    (fun B hB => ⟨r + 1, primePowerMatrixReduction_kernel_pow p r B hB⟩)
  have hsize (q : ℕ) : Nat.card (Matrix (Fin n) (Fin n) (ZMod q)) = q ^ (n * n) := by
    simp only [Matrix, Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul]
  rw [hsize, hsize, card_nilpotent_matrices (ZMod p) n, Nat.card_zmod, ← pow_mul] at hc
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos (n * n))
  rw [hc, ← pow_add, ← pow_add]
  congr 1
  ring

/-- The nilpotent fraction is independent of the prime-power thickness. -/
theorem primePower_nilpotent_matrix_density (r n : ℕ) :
    (Nat.card {A : Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1))) // IsNilpotent A} : ℚ) /
      Nat.card (Matrix (Fin n) (Fin n) (ZMod (p ^ (r + 1)))) = 1 / (p : ℚ) ^ n := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : (r + 1) * (n * n) = (r * (n * n) + n * (n - 1)) + n := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  rw [card_primePower_nilpotent_matrices]
  simp only [Matrix, Nat.card_fun, Nat.card_fin, Nat.card_zmod,
    ← pow_mul, Nat.cast_pow]
  rw [Nat.mul_assoc, he]
  simp only [pow_add]
  field_simp

#print axioms primePowerMatrix_isNilpotent_iff
#print axioms card_primePower_nilpotent_matrices
#print axioms primePower_nilpotent_matrix_density

end GaloisForLFunctions.RepresentationLifting
