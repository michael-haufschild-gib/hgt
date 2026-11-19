import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheLowerDiscriminantsOfAHeatCollision
import GaloisForLFunctions.InfiniteRankPurityTheory.AtPositiveWeightIntegralityDoesNotBoundTheRank
import GaloisForLFunctions.InfiniteRankWeilTheory.TheRankBarrier

/-!
# The cyclic spectrum of the collision moments

Zhou's quantum multiplication relation in the proof of Theorem A2
(arXiv:2611.23833) specializes over the complex numbers to X^m = Q.
Its m sheets give a sharp test for collision detection by boundary moments.
Every intermediate principal minor vanishes even when all sheets are distinct.
-/

noncomputable section
open Finset Matrix
open GaloisForLFunctions.InfiniteRankWeilTheory (unitRoot isPrimitiveRoot_unitRoot)
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Centered at z, the sheets satisfy (X-z)^m = r^m. -/
def cyclicSheet (m : ℕ) (z r : ℂ) (i : Fin m) : ℂ := z+r*(unitRoot m)^i.val

theorem cyclicSheet_equation {m : ℕ} (z r : ℂ) (i : Fin m) :
    (cyclicSheet m z r i-z)^m = r^m := by
  have hm : m ≠ 0 := (Nat.zero_lt_of_lt i.isLt).ne'
  simp only [cyclicSheet, add_sub_cancel_left, mul_pow]
  rw [← pow_mul, Nat.mul_comm, pow_mul, (isPrimitiveRoot_unitRoot hm).pow_eq_one, one_pow, mul_one]

/-- All centered moments below degree m vanish, and moment m reads mQ. -/
theorem cyclicSheet_centered_moment {m : ℕ} (hm : 0 < m) (z r : ℂ) (k : ℕ) :
    ∑ i : Fin m, (cyclicSheet m z r i-z)^k =
      if m ∣ k then (m:ℂ)*r^k else 0 := by
  simp only [cyclicSheet,add_sub_cancel_left,mul_pow,← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => (unitRoot m ^ j)^k),
    InfiniteRankPurityTheory.sum_range_root_pow (isPrimitiveRoot_unitRoot hm.ne') k]
  split_ifs <;> ring

private lemma full_minor_eq_square {m : ℕ} (v : Fin m → ℂ) :
    clusterMomentMinor v m = (vandermonde v).det ^ 2 := by
  have he : (Matrix.of fun i j : Fin m => ∑ a : Fin m, v a^(i.val+j.val)) =
      (vandermonde v).transpose * vandermonde v := by
    ext i j
    simp only [Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,vandermonde_apply,pow_add]
  rw [clusterMomentMinor,he,det_mul,det_transpose,pow_two]

/-- A complex regular polygon with positive radius in modulus has no repeated sheets. -/
theorem cyclicSheet_injective {m : ℕ} (z : ℂ) {r : ℂ} (hr : r ≠ 0) :
    Function.Injective (cyclicSheet m z r) := by
  intro i j he
  have hm := (Nat.zero_lt_of_lt i.isLt).ne'
  apply Fin.ext
  exact (isPrimitiveRoot_unitRoot hm).pow_inj i.isLt j.isLt
    (mul_left_cancel₀ hr (add_left_cancel he))

/-- All nontrivial proper principal minors vanish, including away from the branch point. -/
theorem cyclicSheet_proper_minor {m q : ℕ} (h₂ : 2 ≤ q) (hqm : q < m) (z r : ℂ) :
    clusterMomentMinor (cyclicSheet m z r) q = 0 := by
  have hz : clusterMomentMinor (fun i : Fin m => (unitRoot m)^i.val) q = 0 := by
    apply det_eq_zero_of_row_eq_zero (i := (⟨1,by omega⟩ : Fin q))
    intro j
    change (∑ i : Fin m, ((unitRoot m)^i.val)^(1+j.val)) = 0
    rw [Fin.sum_univ_eq_sum_range (fun i => ((unitRoot m)^i)^(1+j.val)),
      InfiniteRankPurityTheory.sum_range_root_pow (isPrimitiveRoot_unitRoot (by omega))]
    exact if_neg (fun hd => (Nat.le_of_dvd (by omega) hd).not_gt (by omega))
  unfold cyclicSheet
  rw [clusterMomentMinor_affine,hz,mul_zero]

/-- The full discriminant distinguishes regular sheets from their coincident
limit, even though every proper minor from order two upwards is zero. -/
theorem cyclicSheet_full_minor_ne_zero {m : ℕ} (z : ℂ) {r : ℂ} (hr : r ≠ 0) :
    clusterMomentMinor (cyclicSheet m z r) m ≠ 0 := by
  rw [full_minor_eq_square]
  exact pow_ne_zero _ (det_vandermonde_ne_zero_iff.mpr (cyclicSheet_injective z hr))

/-- Center and orientation disappear from the normalized top minor. Its
dependence on the deformation parameter Q = r^m is exactly Q^(m−1). -/
theorem cyclicSheet_full_minor_parameter (m : ℕ) (z r : ℂ) :
    clusterMomentMinor (cyclicSheet m z r) m =
      (r^m)^(m-1)*clusterMomentMinor (fun i : Fin m => (unitRoot m)^i.val) m := by
  unfold cyclicSheet
  rw [clusterMomentMinor_affine, ← pow_mul, ← pow_mul]
  congr 2
  cases m with
  | zero => simp
  | succ n =>
    have h := Nat.succ_mul_choose_eq n 1
    simpa [Nat.mul_comm, Nat.mul_left_comm] using h.symm

#print axioms cyclicSheet_proper_minor
#print axioms cyclicSheet_full_minor_parameter
#print axioms cyclicSheet_full_minor_ne_zero

end GaloisForLFunctions.GaloisTheoryOfZeros
