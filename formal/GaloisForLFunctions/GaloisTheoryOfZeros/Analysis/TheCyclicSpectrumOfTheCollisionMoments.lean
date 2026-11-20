import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheLowerDiscriminantsOfAHeatCollision
import GaloisForLFunctions.InfiniteRankPurityTheory.AtPositiveWeightIntegralityDoesNotBoundTheRank
import GaloisForLFunctions.InfiniteRankWeilTheory.TheRankBarrier
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The cyclic spectrum of the collision moments

Zhou's quantum multiplication relation in Theorem A, part (A2)
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

/-- When all previous nonconstant moments vanish, the first row isolates
the mass and reversing the remaining columns gives a triangular matrix.
Its diagonal consists entirely of the next moment. -/
theorem first_surviving_moment_minor {m : ℕ} (v : Fin m → ℂ) (k : ℕ)
    (h : ∀ j, 0<j → j<k+2 → ∑ i, v i^j=0) :
    ((Equiv.Perm.sign (Fin.revPerm (n:=k+1)) : ℤ) : ℂ)*clusterMomentMinor v (k+2) =
      (m:ℂ)*(∑ i, v i^(k+2))^(k+1) := by
  let p := fun j : ℕ => ∑ i, v i^j
  let M : Matrix (Fin (k+2)) (Fin (k+2)) ℂ := Matrix.of fun i j => p (i.val+j.val)
  let B := M.submatrix Fin.succ Fin.succ
  let σ := Fin.revPerm (n:=k+1)
  let A := B.submatrix id σ
  have hm : M.det=(m:ℂ)*B.det := by
    rw [Matrix.det_succ_row_zero,Finset.sum_eq_single 0]
    · simp [M,p,B,Fin.succAbove_zero]
    · intro j _ hj
      have hp : 0<j.val := Nat.pos_of_ne_zero (fun he => hj (Fin.ext he))
      have hz : M 0 j=0 := by
        change p (0+j.val)=0
        rw [zero_add]
        exact h j.val hp j.isLt
      rw [hz,mul_zero,zero_mul]
    · simp
  have ht : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i.val<j.val at hij
    change p ((i.val+1)+((k+1-(j.val+1))+1))=0
    exact h _ (by omega) (by have := j.isLt; omega)
  have hd (i : Fin (k+1)) : A i i=p (k+2) := by
    change p ((i.val+1)+((k+1-(i.val+1))+1))=p (k+2)
    congr 1
    have := i.isLt
    omega
  have he : ((Equiv.Perm.sign σ : ℤ) : ℂ)*B.det=p (k+2)^(k+1) := by
    rw [←Matrix.det_permute' σ B,show B.submatrix id σ=A by rfl,Matrix.det_of_lowerTriangular A ht]
    simp only [hd,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  change ((Equiv.Perm.sign σ : ℤ) : ℂ)*M.det=(m:ℂ)*p (k+2)^(k+1)
  rw [hm,←he]
  ring

private theorem minor_zero_iff_next_moment {m : ℕ} (hm : 0 < m) (v : Fin m → ℂ) (k : ℕ)
    (h : ∀ j, 0<j → j<k+2 → ∑ i, v i^j=0) :
    clusterMomentMinor v (k+2)=0 ↔ ∑ i, v i^(k+2)=0 := by
  have he := first_surviving_moment_minor v k h
  have hs : ((Equiv.Perm.sign (Fin.revPerm (n:=k+1)) : ℤ) : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Equiv.Perm.sign _).ne_zero
  have hmass : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  constructor
  · intro hz
    rw [hz,mul_zero] at he
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp he.symm).resolve_left hmass)
  · intro hz
    rw [hz,zero_pow (Nat.succ_ne_zero _),mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hs

/-- A centered complex cluster loses all its nontrivial proper principal
minors exactly when it is a regular polygon with multiplicities, allowing
zero radius. Its final power sum fixes the branched parameter r^m. -/
theorem proper_minor_vanishing_iff_cyclic {m : ℕ} (hm : 0 < m) (v : Fin m → ℂ)
    (hcenter : ∑ i, v i=0) :
    (∀ q, 2≤q → q < m → clusterMomentMinor v q=0) ↔
      ∃ r : ℂ, r^m=(∑ i, v i^m)/(m:ℂ) ∧
        univ.val.map v=univ.val.map (cyclicSheet m 0 r) := by
  have hmass : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have read (r : ℂ) (j : ℕ) :
      (∑ i, cyclicSheet m 0 r i^j) = if m∣j then (m:ℂ)*r^j else 0 := by
    simpa only [sub_zero] using cyclicSheet_centered_moment hm 0 r j
  constructor
  · intro h
    have vanish (j : ℕ) (h₀ : 0<j) (hj : j < m) : (∑ i, v i^j)=0 := by
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        rcases j with _|j
        · omega
        rcases j with _|k
        · simpa only [pow_one] using hcenter
        apply (minor_zero_iff_next_moment hm v k (fun i hi hij => ih i hij hi (hij.trans hj))).mp
        exact h _ (by omega) hj
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq ((∑ i, v i^m)/(m:ℂ)) hm
    refine ⟨r,hr,GaloisForLFunctions.powerSum_torelli_finite v _ ?_⟩
    intro j hj
    change (∑ i, v i^j)=∑ i, cyclicSheet m 0 r i^j
    rcases Nat.eq_zero_or_pos j with rfl | hp
    · simp
    rw [read]
    rcases hj.eq_or_lt with rfl | hl
    · rw [if_pos (dvd_refl _),hr]
      field_simp [hmass]
    · rw [if_neg (fun h => (Nat.le_of_dvd hp h).not_gt hl),vanish j hp hl]
  · rintro ⟨r,_,he⟩ q hq hqm
    have vanish (j : ℕ) (hj : 0<j) (hjm : j < m) : (∑ i, v i^j)=0 := by
      have h := congrArg (fun s : Multiset ℂ => (s.map (fun z => z^j)).sum) he
      simp only [Multiset.map_map] at h
      change (∑ i, v i^j)=(∑ i, cyclicSheet m 0 r i^j) at h
      rw [h,read,if_neg (fun hd => (Nat.le_of_dvd hj hd).not_gt hjm)]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hq
    rw [Nat.add_comm 2 k] at hqm ⊢
    exact (minor_zero_iff_next_moment hm v k (fun j hj hjk => vanish j hj (hjk.trans hqm))).mpr
      (vanish _ (by omega) hqm)

end GaloisForLFunctions.GaloisTheoryOfZeros
