/-
# Telescoping and the continuity of power traces

The difference of two `k`-th powers is a sum of `k` products, each containing exactly one copy of
the difference and `k-1` copies of the two operators.  Every such product is a product of `k`
Schatten-`p` operators, hence trace class once `k ≥ p`, and its trace is bounded by its trace norm.
So the power traces are controlled by the Schatten norm of the difference.

Main results:
* `sub_pow_eq_sum_mul_sub_mul` — **the telescoping identity in a ring**.
* `memSchattenClass_one_telescope_term` — each telescoping term is trace class.
* `norm_opTrace_pow_sub_le` — **the power traces are controlled by the telescoping terms**.
-/
import GaloisForLFunctions.HTGeometry.SchattenListProductNorm
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

open Filter ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- **The telescoping identity.** -/
theorem sub_pow_eq_sum_mul_sub_mul {R : Type*} [Ring R] (a b : R) :
    ∀ k : ℕ, a ^ k - b ^ k = ∑ j ∈ Finset.range k, a ^ j * (a - b) * b ^ (k - 1 - j) := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have hshift : ∑ j ∈ Finset.range n, a ^ j * (a - b) * b ^ (n - j)
          = (∑ j ∈ Finset.range n, a ^ j * (a - b) * b ^ (n - 1 - j)) * b := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjn : j < n := Finset.mem_range.mp hj
        have hpow : n - j = (n - 1 - j) + 1 := by omega
        rw [hpow, pow_succ]
        noncomm_ring
      rw [Finset.sum_range_succ]
      have hlast : a ^ n * (a - b) * b ^ (n + 1 - 1 - n) = a ^ n * (a - b) := by
        have : n + 1 - 1 - n = 0 := by omega
        rw [this, pow_zero, mul_one]
      have hmid : ∀ j ∈ Finset.range n,
          a ^ j * (a - b) * b ^ (n + 1 - 1 - j) = a ^ j * (a - b) * b ^ (n - j) := by
        intro j hj
        have : n + 1 - 1 - j = n - j := by omega
        rw [this]
      rw [Finset.sum_congr rfl hmid, hlast, hshift, ← ih]
      have hpa : a ^ (n + 1) = a ^ n * a := pow_succ a n
      have hpb : b ^ (n + 1) = b ^ n * b := pow_succ b n
      rw [hpa, hpb]
      noncomm_ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Each telescoping term is a product of `k` Schatten-`p` operators, hence trace class. -/
theorem memSchattenClass_one_telescope_term {p : ℝ} (hp : 0 < p) {A B : H →L[ℂ] H}
    (hA : MemSchattenClass p A) (hB : MemSchattenClass p B) (hD : MemSchattenClass p (A - B))
    {k j : ℕ} (hj : j < k) (hpk : p ≤ (k : ℝ)) :
    MemSchattenClass 1 (A ^ j * (A - B) * B ^ (k - 1 - j)) := by
  classical
  set L : List (H →L[ℂ] H) :=
    List.replicate j A ++ (A - B) :: List.replicate (k - 1 - j) B with hLdef
  have hLne : L ≠ [] := by
    rw [hLdef]
    intro hcon
    have := congrArg List.length hcon
    simp at this
  have hmem : ∀ X ∈ L, MemSchattenClass p X := by
    intro X hX
    rw [hLdef, List.mem_append] at hX
    rcases hX with hX | hX
    · rw [List.eq_of_mem_replicate hX]; exact hA
    · rcases List.mem_cons.mp hX with hX | hX
      · rw [hX]; exact hD
      · rw [List.eq_of_mem_replicate hX]; exact hB
  have hlen : L.length = k := by
    rw [hLdef]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hprod : L.prod = A ^ j * (A - B) * B ^ (k - 1 - j) := by
    rw [hLdef, List.prod_append, List.prod_replicate, List.prod_cons, List.prod_replicate,
      mul_assoc]
  rw [← hprod]
  refine memSchattenClass_one_list_prod hp L hLne hmem ?_
  rw [hlen]
  exact hpk

/-- The Schatten-1 class is closed under finite sums. -/
theorem memSchattenClass_one_sum {ι : Type*} [DecidableEq ι] :
    ∀ (s : Finset ι) (f : ι → H →L[ℂ] H), (∀ i ∈ s, MemSchattenClass 1 (f i)) →
      MemSchattenClass 1 (∑ i ∈ s, f i) := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro f _
      rw [Finset.sum_empty]
      show Summable fun n : ℕ => approxNumber (0 : H →L[ℂ] H) n ^ (1 : ℝ)
      simp [approxNumber_zero_op]
  | insert x t hx ih =>
      intro f hf
      rw [Finset.sum_insert hx]
      have hx1 : MemSchattenClass 1 (f x) := hf x (Finset.mem_insert_self x t)
      have ht1 : MemSchattenClass 1 (∑ i ∈ t, f i) :=
        ih f fun i hi => hf i (Finset.mem_insert_of_mem hi)
      exact memSchattenClass_one_add (hx1.isCompactOperator one_pos)
        (ht1.isCompactOperator one_pos) hx1 ht1

/-- The trace of a finite sum of trace-class operators is bounded by the sum of the trace norms. -/
theorem norm_opTrace_sum_le {ι : Type*} [DecidableEq ι] :
    ∀ (s : Finset ι) (f : ι → H →L[ℂ] H), (∀ i ∈ s, MemSchattenClass 1 (f i)) →
      ‖opTrace (∑ i ∈ s, f i)‖ ≤ ∑ i ∈ s, traceNorm H (f i) := by
  intro s
  induction s using Finset.induction with
  | empty => intro f _; simp
  | insert x t hx ih =>
      intro f hf
      have hx1 : MemSchattenClass 1 (f x) := hf x (Finset.mem_insert_self x t)
      have hrest : ∀ i ∈ t, MemSchattenClass 1 (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have ht1 : MemSchattenClass 1 (∑ i ∈ t, f i) := memSchattenClass_one_sum t f hrest
      rw [Finset.sum_insert hx, Finset.sum_insert hx,
        opTrace_add_of_memSchattenClass_one hx1 ht1]
      exact le_trans (norm_add_le _ _)
        (add_le_add (norm_opTrace_le_traceNorm hx1) (ih f hrest))

/-- **The power traces are controlled by the telescoping terms.** -/
theorem norm_opTrace_pow_sub_le {p : ℝ} (hp : 0 < p) {A B : H →L[ℂ] H}
    (hA : MemSchattenClass p A) (hB : MemSchattenClass p B) (hD : MemSchattenClass p (A - B))
    {k : ℕ} (hk0 : 0 < k) (hpk : p ≤ (k : ℝ)) :
    ‖opTrace (A ^ k) - opTrace (B ^ k)‖
      ≤ ∑ j ∈ Finset.range k, traceNorm H (A ^ j * (A - B) * B ^ (k - 1 - j)) := by
  classical
  have hAk : MemSchattenClass 1 (A ^ k) := memSchattenClass_one_pow hp hA hk0 hpk
  have hBk : MemSchattenClass 1 (B ^ k) := memSchattenClass_one_pow hp hB hk0 hpk
  have hterm : ∀ j ∈ Finset.range k,
      MemSchattenClass 1 (A ^ j * (A - B) * B ^ (k - 1 - j)) := fun j hj =>
    memSchattenClass_one_telescope_term hp hA hB hD (Finset.mem_range.mp hj) hpk
  have hsub : opTrace (A ^ k) - opTrace (B ^ k) = opTrace (A ^ k - B ^ k) :=
    (opTrace_sub_of_memSchattenClass_one hAk hBk).symm
  rw [hsub, sub_pow_eq_sum_mul_sub_mul A B k]
  exact norm_opTrace_sum_le (Finset.range k)
    (fun j => A ^ j * (A - B) * B ^ (k - 1 - j)) hterm

end

end GaloisForLFunctions.HTGeometry
