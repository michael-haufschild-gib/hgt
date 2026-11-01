import GaloisForLFunctions.HeckeKreinToeplitz.Index.NegativeColumnComplement
import Mathlib.Data.Nat.Find

/-!
# Maximal negative frames in the column space

Finite negative index bounds every orthonormal negative column family.
A family of greatest length has a positive definite orthogonal complement:
a negative vector would extend the family, and a null vector would lie in
the radical of the entire column form.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G] {k : G → ℂ}

/-- An orthonormal family for the negative of the column form. -/
def IsNegativeColumnFrame {m : ℕ} (e : Fin m → kernelColumnSpan k) : Prop :=
  ∀ i j, kernelColumnPairing k (e i) (e j) = if i = j then -1 else 0

/-- Every negative column vector can be scaled to square `-1`. -/
theorem exists_normalized_negative_column (hk : IsHermKernel k)
    {v : kernelColumnSpan k} (hv : (kernelColumnPairing k v v).re < 0) :
    ∃ a : ℂ, kernelColumnPairing k (a • v) (a • v) = -1 := by
  have him : (kernelColumnPairing k v v).im = 0 := by
    have h := congrArg Complex.im (kernelColumnPairing_conj_symm hk v v)
    simp only [Complex.conj_im] at h
    linarith only [h]
  let r : ℝ := Real.sqrt (-(kernelColumnPairing k v v).re)
  have hr : 0 < r := Real.sqrt_pos.mpr (neg_pos.mpr hv)
  have hr2 : r ^ 2 = -(kernelColumnPairing k v v).re := Real.sq_sqrt (neg_nonneg.mpr hv.le)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : kernelColumnPairing k v v = -((r : ℂ) ^ 2) := by
    apply Complex.ext
    · rw [← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re]
      linarith only [hr2]
    · rw [← Complex.ofReal_pow, Complex.neg_im, Complex.ofReal_im, neg_zero, him]
  refine ⟨(r : ℂ)⁻¹, ?_⟩
  rw [kernelColumnPairing_smul_left hk, map_smul, smul_eq_mul, map_inv₀,
    Complex.conj_ofReal, he]
  field_simp

/-- Frame length is bounded by the negative index of the kernel. -/
theorem IsNegativeColumnFrame.length_le (hk : IsHermKernel k) {r m : ℕ}
    (hi : negIndex k ≤ r) {e : Fin m → kernelColumnSpan k}
    (he : IsNegativeColumnFrame e) : m ≤ r := by
  have hn (i : Fin m) : (kernelColumnPairing k (e i) (e i)).re < 0 := by
    rw [he i i, if_pos rfl]
    norm_num
  have ho (i j : Fin m) (hij : i ≠ j) : kernelColumnPairing k (e i) (e j) = 0 := by
    rw [he i j, if_neg hij]
  simpa only [Fintype.card_fin] using
    card_le_index_of_orthogonal_negative_columns hk hi e hn ho

/-- An orthogonal vector of square `-1` extends a negative frame. -/
theorem IsNegativeColumnFrame.cons (hk : IsHermKernel k) {m : ℕ}
    {e : Fin m → kernelColumnSpan k} (he : IsNegativeColumnFrame e)
    {v : kernelColumnSpan k} (hv : kernelColumnPairing k v v = -1)
    (ho : ∀ i, kernelColumnPairing k (e i) v = 0) :
    IsNegativeColumnFrame (Fin.cons v e) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.cons_zero, ite_true] using hv
    · have h : kernelColumnPairing k v (e j) = 0 := by
        rw [kernelColumnPairing_conj_symm hk, ho j, map_zero]
      have hne : (0 : Fin (m + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simpa only [Fin.cons_zero, Fin.cons_succ, if_neg hne] using h
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa using ho i
    · simpa only [Fin.cons_succ, Fin.succ_inj] using he i j

/-- A finite-index kernel admits a negative frame with nonnegative orthogonal complement. -/
theorem exists_maximal_negative_column_frame (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) :
    ∃ m ≤ r, ∃ e : Fin m → kernelColumnSpan k, IsNegativeColumnFrame e ∧
      ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
        0 ≤ (kernelColumnPairing k v v).re := by
  classical
  let P : ℕ → Prop := fun m => ∃ e : Fin m → kernelColumnSpan k, IsNegativeColumnFrame e
  have h0 : P 0 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  let m := Nat.findGreatest P r
  obtain ⟨e, he⟩ := Nat.findGreatest_spec (Nat.zero_le r) h0
  refine ⟨m, Nat.findGreatest_le r, e, he, ?_⟩
  intro v ho
  by_contra hv
  obtain ⟨a, ha⟩ := exists_normalized_negative_column hk (lt_of_not_ge hv)
  have hao (i : Fin m) : kernelColumnPairing k (e i) (a • v) = 0 := by
    rw [map_smul, ho i, smul_zero]
  have hnew : IsNegativeColumnFrame (Fin.cons (a • v) e) := he.cons hk ha hao
  have hbound : m + 1 ≤ r := hnew.length_le hk hi
  have hle : m + 1 ≤ m := Nat.le_findGreatest hbound ⟨_, hnew⟩
  omega

/-- Pairing against a frame reads off the negative coordinate of its synthesis. -/
theorem IsNegativeColumnFrame.pairing_sum {m : ℕ}
    {e : Fin m → kernelColumnSpan k} (he : IsNegativeColumnFrame e)
    (c : Fin m → ℂ) (i : Fin m) :
    kernelColumnPairing k (e i) (∑ j, c j • e j) = -c i := by
  classical
  rw [map_sum]
  have hs : (∑ j, kernelColumnPairing k (e i) (c j • e j)) =
      kernelColumnPairing k (e i) (c i • e i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [map_smul, he i j, if_neg hji.symm, smul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hs, map_smul, he i i, if_pos rfl, smul_eq_mul]
  ring

/-- A nonnegative frame complement is definite: its null vectors annihilate the whole form. -/
theorem kernelColumnPairing_definite_on_frame_complement (hk : IsHermKernel k)
    {m : ℕ} {e : Fin m → kernelColumnSpan k} (he : IsNegativeColumnFrame e)
    (hp : ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
      0 ≤ (kernelColumnPairing k v v).re)
    {v : kernelColumnSpan k} (ho : ∀ i, kernelColumnPairing k (e i) v = 0)
    (hv : kernelColumnPairing k v v = 0) : v = 0 := by
  let W : Submodule ℂ (kernelColumnSpan k) := ⨅ i, (kernelColumnPairing k (e i)).ker
  have hW (w : kernelColumnSpan k) : w ∈ W ↔
      ∀ i, kernelColumnPairing k (e i) w = 0 := Submodule.mem_iInf _
  have hpos : ∀ w ∈ W, 0 ≤ (kernelColumnPairing k w w).re :=
    fun w hw => hp w ((hW w).mp hw)
  apply kernelColumnPairing_nondegenerate hk
  intro z
  let w := z + ∑ i, kernelColumnPairing k (e i) z • e i
  have hw : w ∈ W := by
    apply (hW w).mpr
    intro i
    change kernelColumnPairing k (e i) (z + ∑ j, kernelColumnPairing k (e j) z • e j) = 0
    rw [map_add, he.pairing_sum]
    exact add_neg_cancel _
  have hcs := kernelColumnPairing_normSq_le_on_subspace hk W hpos v w ((hW v).mpr ho) hw
  rw [hv, Complex.zero_re, zero_mul] at hcs
  have hzero : kernelColumnPairing k v w = 0 :=
    Complex.normSq_eq_zero.mp (le_antisymm hcs (normSq_nonneg _))
  have hve (i : Fin m) : kernelColumnPairing k v (e i) = 0 := by
    rw [kernelColumnPairing_conj_symm hk, ho i, map_zero]
  change kernelColumnPairing k v (z + ∑ i, kernelColumnPairing k (e i) z • e i) = 0 at hzero
  simp only [map_add, map_sum, map_smul, hve, smul_zero, sum_const_zero, add_zero] at hzero
  rw [kernelColumnPairing_conj_symm hk, hzero, map_zero]

#print axioms exists_maximal_negative_column_frame
#print axioms kernelColumnPairing_definite_on_frame_complement

end GaloisForLFunctions.HeckeKreinToeplitz
