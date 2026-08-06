import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Partial sums of the decreasing rearrangement, and majorization

For a real tuple, `topSum k` is the sum of its `k` largest entries.  It dominates the sum over
every `k`-element subset and is attained by one of them.

The majorization step is Karamata's inequality for the square, which is a single Abel summation:
if the partial sums of an antitone tuple `a` are dominated by those of an antitone tuple `v`, with
equal total sums, then `∑ a i ^ 2 ≤ ∑ v i ^ 2`, because the Abel weights `a i + v i` are antitone
and the partial sums of `a - v` are nonpositive with vanishing total.

Combining the two: a tuple whose `k`-largest sums are dominated by the sum of those of two other
tuples, with equal total sums, has Euclidean norm at most the sum of theirs.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-! ## Abel summation -/

/-- **Summation by parts bound.**  An antitone weight against increments whose partial sums are
nonpositive and whose total sum vanishes gives a nonpositive sum. -/
theorem sum_mul_nonpos_of_partialSums (N : ℕ) (c e : ℕ → ℝ)
    (hc : ∀ i, i + 1 < N → c (i + 1) ≤ c i)
    (hE : ∀ m, m ≤ N → ∑ j ∈ Finset.range m, e j ≤ 0)
    (hEN : ∑ j ∈ Finset.range N, e j = 0) :
    ∑ i ∈ Finset.range N, c i * e i ≤ 0 := by
  have h := Finset.sum_range_by_parts c e N
  simp only [smul_eq_mul] at h
  rw [h, hEN, mul_zero, zero_sub, neg_nonpos]
  refine Finset.sum_nonneg fun i hi => ?_
  have hiN : i + 1 < N := by
    have := Finset.mem_range.1 hi
    omega
  have h1 : c (i + 1) - c i ≤ 0 := sub_nonpos.2 (hc i hiN)
  have h2 : ∑ j ∈ Finset.range (i + 1), e j ≤ 0 := hE (i + 1) (le_of_lt hiN)
  nlinarith [h1, h2]

/-! ## The first `k` indices -/

variable {n k : ℕ}

/-- The set of the first `k` indices. -/
def firstIdx (n k : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < k

theorem mem_firstIdx {i : Fin n} : i ∈ firstIdx n k ↔ (i : ℕ) < k := by
  simp [firstIdx]

theorem card_firstIdx (h : k ≤ n) : (firstIdx n k).card = k := by
  have hmap : firstIdx n k = Finset.map (Fin.castLEEmb h) Finset.univ := by
    ext i
    simp only [mem_firstIdx, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact ⟨⟨(i : ℕ), hi⟩, by simp [Fin.castLEEmb]⟩
    · rintro ⟨j, rfl⟩
      simp [Fin.castLEEmb]
  rw [hmap, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem firstIdx_self : firstIdx n n = Finset.univ := by
  ext i
  simp [mem_firstIdx, i.isLt]

/-! ## An antitone tuple is largest on the first indices -/

theorem sum_le_sum_firstIdx {g : Fin n → ℝ} (hg : Antitone g) {t : Finset (Fin n)}
    (hk : k ≤ n) (ht : t.card = k) :
    ∑ i ∈ t, g i ≤ ∑ i ∈ firstIdx n k, g i := by
  classical
  set u := firstIdx n k with hu
  have hcard : (t \ u).card = (u \ t).card := by
    have h1 : (t \ u).card + (t ∩ u).card = k := by
      rw [Finset.card_sdiff_add_card_inter, ht]
    have h2 : (u \ t).card + (u ∩ t).card = k := by
      rw [Finset.card_sdiff_add_card_inter, hu, card_firstIdx hk]
    rw [Finset.inter_comm] at h2
    omega
  have hcmp : ∀ x ∈ t \ u, ∀ y ∈ u \ t, g x ≤ g y := by
    intro x hx y hy
    refine hg (le_of_lt ?_)
    have hx' : ¬ ((x : ℕ) < k) := fun h => (Finset.mem_sdiff.1 hx).2 (mem_firstIdx.2 h)
    have hy' : (y : ℕ) < k := mem_firstIdx.1 (Finset.mem_sdiff.1 hy).1
    exact Fin.lt_def.2 (lt_of_lt_of_le hy' (Nat.not_lt.1 hx'))
  have hdiff : ∑ i ∈ t \ u, g i ≤ ∑ i ∈ u \ t, g i := by
    rcases Finset.eq_empty_or_nonempty (t \ u) with hem | hne
    · have hut : (u \ t) = ∅ := Finset.card_eq_zero.1 (by rw [← hcard, hem, Finset.card_empty])
      simp [hem, hut]
    · obtain ⟨x₀, hx₀, hx₀max⟩ := Finset.exists_max_image (t \ u) g hne
      have hle₁ : ∑ i ∈ t \ u, g i ≤ (t \ u).card • g x₀ :=
        Finset.sum_le_card_nsmul _ _ _ fun x hx => hx₀max x hx
      have hle₂ : (u \ t).card • g x₀ ≤ ∑ i ∈ u \ t, g i :=
        Finset.card_nsmul_le_sum _ _ _ fun y hy => hcmp x₀ hx₀ y hy
      rw [hcard] at hle₁
      exact hle₁.trans hle₂
  have hsplit : ∀ s₁ s₂ : Finset (Fin n),
      ∑ i ∈ s₁ \ s₂, g i + ∑ i ∈ s₁ ∩ s₂, g i = ∑ i ∈ s₁, g i := by
    intro s₁ s₂
    rw [← Finset.sdiff_inter_self_left s₁ s₂]
    exact Finset.sum_sdiff Finset.inter_subset_left
  calc ∑ i ∈ t, g i = ∑ i ∈ t \ u, g i + ∑ i ∈ t ∩ u, g i := (hsplit t u).symm
    _ ≤ ∑ i ∈ u \ t, g i + ∑ i ∈ u ∩ t, g i := by
        rw [Finset.inter_comm]
        exact add_le_add hdiff le_rfl
    _ = ∑ i ∈ u, g i := hsplit u t

/-! ## The decreasing rearrangement -/

/-- The permutation sorting a tuple in decreasing order. -/
noncomputable def descPerm (v : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  (Fin.revPerm).trans (Tuple.sort v)

/-- A tuple rearranged in decreasing order. -/
noncomputable def sortDesc (v : Fin n → ℝ) : Fin n → ℝ := fun i => v (Tuple.sort v i.rev)

theorem sortDesc_eq_comp (v : Fin n → ℝ) : sortDesc v = v ∘ descPerm v := rfl

theorem antitone_sortDesc (v : Fin n → ℝ) : Antitone (sortDesc v) :=
  fun _ _ hij => Tuple.monotone_sort v (Fin.rev_le_rev.2 hij)

theorem sum_sortDesc (v : Fin n → ℝ) : ∑ i, sortDesc v i = ∑ i, v i :=
  Equiv.sum_comp (descPerm v) v

theorem sum_sortDesc_sq (v : Fin n → ℝ) : ∑ i, sortDesc v i ^ 2 = ∑ i, v i ^ 2 :=
  Equiv.sum_comp (descPerm v) fun i => v i ^ 2

/-! ## The sum of the `k` largest entries -/

/-- The sum of the `k` largest entries of a tuple. -/
noncomputable def topSum (k : ℕ) (v : Fin n → ℝ) : ℝ := ∑ i ∈ firstIdx n k, sortDesc v i

theorem sum_le_topSum {v : Fin n → ℝ} {t : Finset (Fin n)} (hk : k ≤ n) (ht : t.card = k) :
    ∑ i ∈ t, v i ≤ topSum k v := by
  classical
  have himg : ∑ i ∈ t, v i = ∑ j ∈ t.image (descPerm v).symm, sortDesc v j := by
    rw [Finset.sum_image fun x _ y _ h => (descPerm v).symm.injective h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [sortDesc_eq_comp]
      simp
  rw [himg]
  exact sum_le_sum_firstIdx (antitone_sortDesc v) hk
    (by rw [Finset.card_image_of_injective _ (descPerm v).symm.injective, ht])

theorem exists_sum_eq_topSum (v : Fin n → ℝ) (hk : k ≤ n) :
    ∃ t : Finset (Fin n), t.card = k ∧ ∑ i ∈ t, v i = topSum k v := by
  classical
  refine ⟨(firstIdx n k).image (descPerm v), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (descPerm v).injective, card_firstIdx hk]
  · rw [Finset.sum_image fun x _ y _ h => (descPerm v).injective h]
    exact Finset.sum_congr rfl fun i _ => rfl

theorem topSum_univ (v : Fin n → ℝ) : topSum n v = ∑ i, v i := by
  rw [topSum, firstIdx_self]
  exact sum_sortDesc v

/-! ## From `Fin n` to ranges -/

/-- A tuple extended by zero to all natural indices. -/
noncomputable def natExt (v : Fin n → ℝ) : ℕ → ℝ := fun m => if h : m < n then v ⟨m, h⟩ else 0

theorem natExt_of_lt (v : Fin n → ℝ) {m : ℕ} (h : m < n) : natExt v m = v ⟨m, h⟩ := dif_pos h

theorem natExt_of_ge (v : Fin n → ℝ) {m : ℕ} (h : n ≤ m) : natExt v m = 0 :=
  dif_neg (Nat.not_lt.2 h)

theorem sum_range_natExt (v : Fin n → ℝ) (hm : k ≤ n) :
    ∑ j ∈ Finset.range k, natExt v j = ∑ i ∈ firstIdx n k, v i := by
  refine Finset.sum_bij (fun j hj => (⟨j, lt_of_lt_of_le (Finset.mem_range.1 hj) hm⟩ : Fin n))
    (fun j hj => mem_firstIdx.2 (Finset.mem_range.1 hj)) (fun _ _ _ _ h => by
      simpa [Fin.ext_iff] using h)
    (fun i hi => ⟨(i : ℕ), Finset.mem_range.2 (mem_firstIdx.1 hi), rfl⟩)
    fun j hj => natExt_of_lt v (lt_of_lt_of_le (Finset.mem_range.1 hj) hm)

theorem sum_range_natExt_univ (v : Fin n → ℝ) :
    ∑ j ∈ Finset.range n, natExt v j = ∑ i, v i := by
  rw [sum_range_natExt v le_rfl, firstIdx_self]

/-! ## Karamata for the square -/

theorem sum_sq_le_of_partialSums {a v : Fin n → ℝ} (ha : Antitone a) (hv : Antitone v)
    (hpart : ∀ m ≤ n, ∑ i ∈ firstIdx n m, a i ≤ ∑ i ∈ firstIdx n m, v i)
    (htot : ∑ i, a i = ∑ i, v i) :
    ∑ i, a i ^ 2 ≤ ∑ i, v i ^ 2 := by
  set c : ℕ → ℝ := fun m => natExt a m + natExt v m with hcdef
  set e : ℕ → ℝ := fun m => natExt a m - natExt v m with hedef
  have hce : ∀ m, c m * e m = natExt (fun i => a i ^ 2 - v i ^ 2) m := by
    intro m
    show (natExt a m + natExt v m) * (natExt a m - natExt v m) = _
    by_cases hm : m < n
    · rw [natExt_of_lt a hm, natExt_of_lt v hm, natExt_of_lt _ hm]
      ring
    · rw [natExt_of_ge a (Nat.not_lt.1 hm), natExt_of_ge v (Nat.not_lt.1 hm),
        natExt_of_ge _ (Nat.not_lt.1 hm)]
      ring
  have hEsum : ∀ m, m ≤ n → ∑ j ∈ Finset.range m, e j
      = (∑ i ∈ firstIdx n m, a i) - ∑ i ∈ firstIdx n m, v i := by
    intro m hm
    show (∑ j ∈ Finset.range m, (natExt a j - natExt v j)) = _
    rw [Finset.sum_sub_distrib, sum_range_natExt a hm, sum_range_natExt v hm]
  have hkey : ∑ i ∈ Finset.range n, c i * e i ≤ 0 := by
    refine sum_mul_nonpos_of_partialSums n c e (fun i hi => ?_) (fun m hm => ?_) ?_
    · have hi1 : i < n := by omega
      show natExt a (i + 1) + natExt v (i + 1) ≤ natExt a i + natExt v i
      rw [natExt_of_lt a hi, natExt_of_lt v hi, natExt_of_lt a hi1, natExt_of_lt v hi1]
      exact add_le_add (ha (by simp [Fin.le_def])) (hv (by simp [Fin.le_def]))
    · rw [hEsum m hm]
      linarith [hpart m hm]
    · rw [hEsum n le_rfl, firstIdx_self]
      linarith [htot]
  have hrw : ∑ i ∈ Finset.range n, c i * e i = (∑ i, a i ^ 2) - ∑ i, v i ^ 2 := by
    rw [Finset.sum_congr rfl fun m _ => hce m, sum_range_natExt_univ, Finset.sum_sub_distrib]
  linarith [hkey, hrw.symm.le, hrw.le]

/-! ## The Euclidean comparison -/

theorem sqrt_sum_sq_add_le (x y : Fin n → ℝ) :
    Real.sqrt (∑ i, (x i + y i) ^ 2)
      ≤ Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2) := by
  have hcs : ∑ i, x i * y i ≤ Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ x y
  have hx : (0:ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy : (0:ℝ) ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hexp : ∑ i, (x i + y i) ^ 2
      = (∑ i, x i ^ 2) + 2 * (∑ i, x i * y i) + ∑ i, y i ^ 2 := by
    rw [Finset.sum_congr rfl fun (i : Fin n) _ =>
        show (x i + y i) ^ 2 = x i ^ 2 + 2 * (x i * y i) + y i ^ 2 from by ring,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hbound : ∑ i, (x i + y i) ^ 2
      ≤ (Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2)) ^ 2 := by
    rw [hexp, add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
    linarith [hcs]
  calc Real.sqrt (∑ i, (x i + y i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- **The Euclidean triangle comparison from dominated top sums.**  If every `k`-largest sum of
`a` is dominated by the sum of the `k`-largest sums of `b` and `c`, and the total sums agree,
then the Euclidean norm of `a` is at most the sum of those of `b` and `c`. -/
theorem sqrt_sum_sq_le_of_topSum_le {a b c : Fin n → ℝ}
    (h : ∀ m ≤ n, topSum m a ≤ topSum m b + topSum m c)
    (htot : ∑ i, a i = (∑ i, b i) + ∑ i, c i) :
    Real.sqrt (∑ i, a i ^ 2)
      ≤ Real.sqrt (∑ i, b i ^ 2) + Real.sqrt (∑ i, c i ^ 2) := by
  have hkey : ∑ i, sortDesc a i ^ 2 ≤ ∑ i, (sortDesc b i + sortDesc c i) ^ 2 := by
    refine sum_sq_le_of_partialSums (antitone_sortDesc a)
      (fun i j hij => add_le_add (antitone_sortDesc b hij) (antitone_sortDesc c hij))
      (fun m hm => ?_) ?_
    · rw [Finset.sum_add_distrib]
      exact h m hm
    · rw [Finset.sum_add_distrib, sum_sortDesc a, sum_sortDesc b, sum_sortDesc c]
      exact htot
  have hA : ∑ i, sortDesc a i ^ 2 = ∑ i, a i ^ 2 := sum_sortDesc_sq a
  have hB : ∑ i, sortDesc b i ^ 2 = ∑ i, b i ^ 2 := sum_sortDesc_sq b
  have hC : ∑ i, sortDesc c i ^ 2 = ∑ i, c i ^ 2 := sum_sortDesc_sq c
  calc Real.sqrt (∑ i, a i ^ 2) = Real.sqrt (∑ i, sortDesc a i ^ 2) := by rw [hA]
    _ ≤ Real.sqrt (∑ i, (sortDesc b i + sortDesc c i) ^ 2) := Real.sqrt_le_sqrt hkey
    _ ≤ Real.sqrt (∑ i, sortDesc b i ^ 2) + Real.sqrt (∑ i, sortDesc c i ^ 2) :=
        sqrt_sum_sq_add_le _ _
    _ = Real.sqrt (∑ i, b i ^ 2) + Real.sqrt (∑ i, c i ^ 2) := by rw [hB, hC]

end GaloisForLFunctions.HTGeometry
