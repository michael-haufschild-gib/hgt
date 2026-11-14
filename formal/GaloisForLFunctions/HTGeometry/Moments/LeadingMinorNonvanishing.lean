import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Nonvanishing leading minors of a finite Hankel matrix

The last independent initial family of Hankel columns has an invertible leading
square block. A dependence of the next column provides a recurrence; a kernel
vector for the leading block would propagate along this recurrence and contradict
column independence. This is the finite algebra behind Fischler–Lai–Sprang–Zudilin,
Lemma 5.3 (https://arxiv.org/abs/2611.16156). No positivity of moments is needed.
-/

open scoped BigOperators Matrix
namespace HTGeometry.FiniteHankel

variable {K : Type*} [Field K]

/-- A column of a finite Hankel window, with its moment offset unrestricted. -/
def column (s : ℕ → K) (N j : ℕ) : Fin N → K := fun i => s (i.val + j)

/-- A finite recurrence propagates a vanishing moment pairing from its initial window. -/
private theorem pairing_zero_of_recurrence (s : ℕ → K) {m N : ℕ}
    (c b : Fin m → K)
    (hrec : ∀ r < N, s (r + m) = ∑ j : Fin m, c j * s (r + j.val))
    (hbase : ∀ i < m, (∑ j : Fin m, b j * s (i + j.val)) = 0) :
    ∀ i < N, (∑ j : Fin m, b j * s (i + j.val)) = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases him : i < m
    · exact hbase i him
    have hstep : (∑ j : Fin m, b j * s (i + j.val)) =
        ∑ k : Fin m, c k * (∑ j : Fin m, b j * s (i - m + k.val + j.val)) := by
      calc
        _ = ∑ j : Fin m, b j *
            (∑ k : Fin m, c k * s (i - m + j.val + k.val)) := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          have hj := j.isLt
          rw [show i + j.val = (i - m + j.val) + m by omega]
          exact hrec _ (by omega)
        _ = _ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro j _
          rw [show i - m + j.val + k.val = i - m + k.val + j.val by omega]
          ring
    rw [hstep]
    apply Finset.sum_eq_zero
    intro k _
    have hk := k.isLt
    rw [ih (i - m + k.val) (by omega) (by omega), mul_zero]

/-- Independence of all columns of a square Hankel block excludes a kernel vector. -/
private theorem det_ne_zero_of_independent (s : ℕ → K) (m : ℕ)
    (h : LinearIndependent K (fun j : Fin m => column s m j.val)) :
    (algebraicHankelMatrix s m).det ≠ 0 := by
  intro hz
  obtain ⟨b, hb, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  apply hb
  funext j
  apply Fintype.linearIndependent_iff.mp h b
  funext i
  have hi := congrFun hker i
  simpa only [Matrix.mulVec, dotProduct, algebraicHankelMatrix, column,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using hi

/-- A dependent next column forces the maximal independent initial block to be invertible. -/
private theorem det_ne_zero_of_next_mem_span (s : ℕ → K) {m N : ℕ}
    (h : LinearIndependent K (fun j : Fin m => column s N j.val))
    (hnext : column s N m ∈ Submodule.span K
      (Set.range (fun j : Fin m => column s N j.val))) :
    (algebraicHankelMatrix s m).det ≠ 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun.mp hnext
  have hrec : ∀ r < N, s (r + m) = ∑ j : Fin m, c j * s (r + j.val) := by
    intro r hr
    have he := congrFun hc ⟨r, hr⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column] using he.symm
  intro hz
  obtain ⟨b, hb, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hbase : ∀ i < m, (∑ j : Fin m, b j * s (i + j.val)) = 0 := by
    intro i hi
    have he := congrFun hker ⟨i, hi⟩
    simpa only [Matrix.mulVec, dotProduct, algebraicHankelMatrix, Pi.zero_apply,
      mul_comm] using he
  have hall := pairing_zero_of_recurrence s c b hrec hbase
  apply hb
  funext j
  apply Fintype.linearIndependent_iff.mp h b
  funext i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column, Pi.zero_apply]
    using hall i.val i.isLt

/-- Enlarging an independent initial family either reaches the square block or a recurrence. -/
private theorem exists_leading_det_ne_zero (s : ℕ → K) (M N : ℕ) (hMN : M ≤ N)
    (h : LinearIndependent K (fun j : Fin M => column s N j.val)) :
    ∃ m, M ≤ m ∧ m ≤ N ∧ (algebraicHankelMatrix s m).det ≠ 0 := by
  by_cases heq : M = N
  · subst M
    exact ⟨N, le_rfl, le_rfl, det_ne_zero_of_independent s N h⟩
  by_cases hsucc : LinearIndependent K (fun j : Fin (M + 1) => column s N j.val)
  · obtain ⟨m, hm, hmN, hdet⟩ := exists_leading_det_ne_zero s (M + 1) N (by omega) hsucc
    exact ⟨m, by omega, hmN, hdet⟩
  · have hnext : column s N M ∈ Submodule.span K
        (Set.range (fun j : Fin M => column s N j.val)) := by
      by_contra hn
      exact hsucc (linearIndependent_finSucc'.mpr ⟨h, hn⟩)
    exact ⟨M, le_rfl, hMN, det_ne_zero_of_next_mem_span s h hnext⟩
termination_by N - M
decreasing_by omega

/-- A nonzero leading determinant remains an independence certificate in any taller window. -/
private theorem independent_of_leading_det_ne_zero (s : ℕ → K) {m N : ℕ}
    (hmN : m ≤ N) (hdet : (algebraicHankelMatrix s m).det ≠ 0) :
    LinearIndependent K (fun j : Fin m => column s N j.val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro b hb j
  have hker : algebraicHankelMatrix s m *ᵥ b = 0 := by
    funext i
    have he := congrFun hb ⟨i.val, lt_of_lt_of_le i.isLt hmN⟩
    simpa only [Matrix.mulVec, dotProduct, algebraicHankelMatrix, column,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using he
  have hb0 : b = 0 := by
    by_contra hn
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨b, hn, hker⟩)
  exact congrFun hb0 j

/-- Initial-column independence is equivalent to a nonzero leading determinant of an
intermediate size. This includes empty windows and signed or complex moments. -/
theorem independent_iff_exists_leading_det (s : ℕ → K) (M N : ℕ) :
    (M ≤ N ∧ LinearIndependent K (fun j : Fin M => column s N j.val)) ↔
      ∃ m, M ≤ m ∧ m ≤ N ∧ (algebraicHankelMatrix s m).det ≠ 0 := by
  constructor
  · rintro ⟨hMN, h⟩
    exact exists_leading_det_ne_zero s M N hMN h
  · rintro ⟨m, hMm, hmN, hdet⟩
    refine ⟨hMm.trans hmN, ?_⟩
    exact (independent_of_leading_det_ne_zero s hmN hdet).comp
      (fun j : Fin M => (⟨j.val, lt_of_lt_of_le j.isLt hMm⟩ : Fin m))
      (fun i j hij => Fin.ext (congrArg Fin.val hij))

#print axioms independent_iff_exists_leading_det

end HTGeometry.FiniteHankel
