import Mathlib

/-!
# The Hermite contrast ladder is orthogonal and lies in the vanishing-integral hyperplane

For a sequence of nonzero centre values `a 0, a 1, …` put

```text
S k = Σ_{j ≤ k} (a j)² ,
w k = (−a 0, −a 1, …, −a k, S k / a (k+1), 0, 0, …) .
```

Two identities hold for purely algebraic reasons, with no hypothesis on the `a j` beyond
`a (k+1) ≠ 0`:

```text
⟨w k, a⟩ = 0 ,          ⟨w k, w m⟩ = 0   for k ≠ m .
```

The first says every ladder vector lies in the limiting vanishing-integral hyperplane; the second
says the ladder is orthogonal.  Each is a two-term cancellation: the head of the vector contributes
`−S k` and its single tail entry contributes `+S k`.

Both vectors have finite support, so the pairings are stated as finite sums over any range
containing the supports.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RHTower

variable {a : ℕ → ℝ}

/-- The partial sums of the squared centre values. -/
def contrastPartialSum (a : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), a j ^ 2

/-- The `k`-th Hermite contrast ladder vector. -/
def contrastLadder (a : ℕ → ℝ) (k : ℕ) (i : ℕ) : ℝ :=
  if i ≤ k then -(a i) else if i = k + 1 then contrastPartialSum a k / a (k + 1) else 0

theorem contrastLadder_of_le {k i : ℕ} (h : i ≤ k) : contrastLadder a k i = -(a i) := by
  rw [contrastLadder, if_pos h]

theorem contrastLadder_succ (k : ℕ) :
    contrastLadder a k (k + 1) = contrastPartialSum a k / a (k + 1) := by
  rw [contrastLadder, if_neg (by omega), if_pos rfl]

theorem contrastLadder_of_gt {k i : ℕ} (h : k + 1 < i) : contrastLadder a k i = 0 := by
  rw [contrastLadder, if_neg (by omega), if_neg (by omega)]

/-! ## The vanishing-integral relation -/

/-- **Every ladder vector is orthogonal to the centre-value vector.**  The head contributes `−S k`
and the single tail entry contributes `+S k`. -/
theorem contrastLadder_inner_centre {k N : ℕ} (hN : k + 2 ≤ N) (ha : a (k + 1) ≠ 0) :
    ∑ i ∈ range N, contrastLadder a k i * a i = 0 := by
  have hsplit : ∑ i ∈ range N, contrastLadder a k i * a i
      = ∑ i ∈ range (k + 2), contrastLadder a k i * a i := by
    have hsub : range (k + 2) ⊆ range N := Finset.range_subset_range.2 (by omega)
    refine (Finset.sum_subset hsub ?_).symm
    intro i _ hi
    have hge : k + 2 ≤ i := by
      by_contra h
      exact hi (Finset.mem_range.2 (by omega))
    rw [contrastLadder_of_gt (by omega), zero_mul]
  rw [hsplit, Finset.sum_range_succ, contrastLadder_succ]
  have hhead : ∑ i ∈ range (k + 1), contrastLadder a k i * a i
      = -contrastPartialSum a k := by
    have hterm : ∀ i ∈ range (k + 1), contrastLadder a k i * a i = -(a i ^ 2) := by
      intro i hi
      have hle : i ≤ k := by
        have := Finset.mem_range.1 hi
        omega
      rw [contrastLadder_of_le hle]
      ring
    rw [Finset.sum_congr rfl hterm]
    simp [contrastPartialSum]
  rw [hhead]
  field_simp
  ring

/-! ## Orthogonality of the ladder -/

/-- The pairing of two ladder vectors with different indices, the lower one first. -/
theorem contrastLadder_inner_of_lt {k m N : ℕ} (hkm : k < m) (hN : m + 2 ≤ N)
    (ha : a (k + 1) ≠ 0) :
    ∑ i ∈ range N, contrastLadder a k i * contrastLadder a m i = 0 := by
  have hsplit : ∑ i ∈ range N, contrastLadder a k i * contrastLadder a m i
      = ∑ i ∈ range (k + 2), contrastLadder a k i * contrastLadder a m i := by
    have hsub : range (k + 2) ⊆ range N := Finset.range_subset_range.2 (by omega)
    refine (Finset.sum_subset hsub ?_).symm
    intro i _ hi
    have hge : k + 2 ≤ i := by
      by_contra h
      exact hi (Finset.mem_range.2 (by omega))
    rw [contrastLadder_of_gt (by omega), zero_mul]
  rw [hsplit, Finset.sum_range_succ, contrastLadder_succ]
  have hmk : k + 1 ≤ m := by omega
  rw [contrastLadder_of_le hmk]
  have hhead : ∑ i ∈ range (k + 1), contrastLadder a k i * contrastLadder a m i
      = contrastPartialSum a k := by
    rw [contrastPartialSum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle : i ≤ k := by
      have := Finset.mem_range.1 hi
      omega
    have hlem : i ≤ m := by omega
    rw [contrastLadder_of_le hle, contrastLadder_of_le hlem]
    ring
  rw [hhead]
  field_simp
  ring

/-- **The ladder is orthogonal.** -/
theorem contrastLadder_inner_eq_zero {k m N : ℕ} (hkm : k ≠ m)
    (hN : k + 2 ≤ N) (hN' : m + 2 ≤ N) (ha : a (k + 1) ≠ 0) (ha' : a (m + 1) ≠ 0) :
    ∑ i ∈ range N, contrastLadder a k i * contrastLadder a m i = 0 := by
  rcases lt_or_gt_of_ne hkm with h | h
  · exact contrastLadder_inner_of_lt h hN' ha
  · have hsymm : ∑ i ∈ range N, contrastLadder a k i * contrastLadder a m i
        = ∑ i ∈ range N, contrastLadder a m i * contrastLadder a k i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsymm]
    exact contrastLadder_inner_of_lt h hN ha'

/-! ## The head of the ladder is nonzero -/

/-- The ladder vector is not the zero vector: its tail entry is positive as soon as some centre
value below the cut is nonzero. -/
theorem contrastLadder_succ_ne_zero {k : ℕ} (ha : a (k + 1) ≠ 0) (h0 : a 0 ≠ 0) :
    contrastLadder a k (k + 1) ≠ 0 := by
  rw [contrastLadder_succ]
  have hpos : 0 < contrastPartialSum a k := by
    rw [contrastPartialSum]
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨0, Finset.mem_range.2 (by omega), ?_⟩
    positivity
  exact div_ne_zero (ne_of_gt hpos) ha

/-! ## The raw Hermite contrasts -/

/-- The raw contrast `r m = a 0 · e m − a m · e 0`. -/
def rawContrast (a : ℕ → ℝ) (m : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then -(a m) else if i = m then a 0 else 0

theorem rawContrast_zero (a : ℕ → ℝ) (m : ℕ) : rawContrast a m 0 = -(a m) := by
  rw [rawContrast, if_pos rfl]

theorem rawContrast_self {m : ℕ} (hm : m ≠ 0) : rawContrast a m m = a 0 := by
  rw [rawContrast, if_neg hm, if_pos rfl]

theorem rawContrast_of_ne {m i : ℕ} (h0 : i ≠ 0) (hm : i ≠ m) : rawContrast a m i = 0 := by
  rw [rawContrast, if_neg h0, if_neg hm]

/-- The pairing of any vector with a raw contrast collapses to two terms. -/
theorem sum_mul_rawContrast {w : ℕ → ℝ} {m N : ℕ} (hm : m ≠ 0) (hmN : m < N) :
    ∑ i ∈ range N, w i * rawContrast a m i = w 0 * -(a m) + w m * a 0 := by
  have hsub : ({0, m} : Finset ℕ) ⊆ range N := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · exact Finset.mem_range.2 (by omega)
    · rw [Finset.mem_singleton.1 hi']
      exact Finset.mem_range.2 hmN
  have hcollapse : ∑ i ∈ range N, w i * rawContrast a m i
      = ∑ i ∈ ({0, m} : Finset ℕ), w i * rawContrast a m i := by
    refine (Finset.sum_subset hsub ?_).symm
    intro i _ hi
    have h0 : i ≠ 0 := by
      intro h
      exact hi (Finset.mem_insert.2 (Or.inl h))
    have hmi : i ≠ m := by
      intro h
      exact hi (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h)))
    rw [rawContrast_of_ne h0 hmi, mul_zero]
  rw [hcollapse, Finset.sum_pair (Ne.symm hm), rawContrast_zero, rawContrast_self hm]

/-- **The ladder vector is orthogonal to every earlier raw contrast.**  This is the Gram–Schmidt
property: `w k` annihilates `r 1, …, r k`. -/
theorem contrastLadder_inner_rawContrast {k m N : ℕ} (hm : m ≠ 0) (hmk : m ≤ k) (hmN : m < N) :
    ∑ i ∈ range N, contrastLadder a k i * rawContrast a m i = 0 := by
  rw [sum_mul_rawContrast (a := a) hm hmN, contrastLadder_of_le (Nat.zero_le k),
    contrastLadder_of_le hmk]
  ring

/-- **The ladder vector is not orthogonal to the next raw contrast.**  Its pairing is
`a 0 · S (k+1) / a (k+1)`, which is exactly what makes `w k` the `(k+1)`-st Gram–Schmidt vector. -/
theorem contrastLadder_inner_rawContrast_succ {k N : ℕ} (hN : k + 1 < N) (ha : a (k + 1) ≠ 0) :
    ∑ i ∈ range N, contrastLadder a k i * rawContrast a (k + 1) i
      = a 0 * contrastPartialSum a (k + 1) / a (k + 1) := by
  rw [sum_mul_rawContrast (a := a) (by omega) hN, contrastLadder_of_le (Nat.zero_le k),
    contrastLadder_succ]
  have hS : contrastPartialSum a (k + 1) = contrastPartialSum a k + a (k + 1) ^ 2 := by
    rw [contrastPartialSum, contrastPartialSum, Finset.sum_range_succ]
  rw [hS]
  field_simp
  ring

end GaloisForLFunctions.RHTower

end
