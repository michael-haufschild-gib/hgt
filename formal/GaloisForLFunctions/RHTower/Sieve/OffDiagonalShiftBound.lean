import GaloisForLFunctions.RHTower.Sieve.FibreShiftSupport
import GaloisForLFunctions.RHTower.Sieve.OffDiagonalReindex
import GaloisForLFunctions.RHTower.Sieve.ShiftSumBound

/-!
# The off-diagonal, in terms of correlations

Assembling the four pieces.  Reindexing by the shift turns the strict lower triangle into
`∑_{k} ∑_{j} K(j+1+k, j+1)·f(j+1)·f(j+1+k)`; the kernel vanishes for `k > h`, so the shift range is
`[1, ⌊h⌋]`; the kernel splits as a smooth model of variation at most `6h+2` plus an error bounded by
`2` and supported on `j ≤ 3√x`.  Partial summation strips the smooth weight at cost `9h+3`, and the
error is bounded trivially:

```text
| off-diagonal |  ≤  (9h+3)·∑_{k ≤ h} B k  +  2h·(3√x + 1) ,
```

where `B k` bounds every partial correlation sum at shift `k`.  Both terms are `o(h²√x)` as soon as
`∑_{k ≤ h} B k = o(h√x)` — the averaged form of Chowla's conjecture.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The off-diagonal is controlled by the partial correlation sums.** -/
theorem abs_offDiagonal_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 16 ≤ x) (hh1 : 1 ≤ h) (hhx : h ≤ Real.sqrt x)
    {B : ℕ → ℝ} (hB0 : ∀ k, 0 ≤ B k)
    (hB : CorrelationPartialBound (fun i => f (i + 1)) ⌊h⌋₊ B) :
    |∑ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
        ∑ n ∈ (Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊).filter (fun n => n < m),
          f m * f n
            * (((outerBlock x h).filter
                (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℝ)|
      ≤ (9 * h + 3) * (∑ k ∈ Finset.Icc 1 ⌊h⌋₊, B k) + 2 * h * (3 * Real.sqrt x + 1) := by
  classical
  have hh0 : (0 : ℝ) ≤ h := by linarith
  have hx4 : (4 : ℝ) ≤ x := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  set M : ℕ := ⌊x + h * Real.sqrt x⌋₊ with hMdef
  set Kf : ℕ → ℕ → ℝ := fun m n =>
    (((outerBlock x h).filter
      (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℝ) with hKf
  set g : ℕ → ℕ → ℝ := fun k j => (fun i => f (i + 1)) j * (fun i => f (i + 1)) (j + k) with hg
  set w : ℕ → ℕ → ℝ := fun k j => fibreSmooth x h k (j + 1) with hw
  -- the kernel vanishes outside the window
  have hKzero : ∀ m n : ℕ, M < m → Kf m n = 0 := by
    intro m n hm
    have : (outerBlock x h).filter
        (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
      rw [Finset.mem_filter, mem_innerFibre] at ha
      exact absurd ha.2.1.1.2 (by omega)
    rw [hKf]
    simp [this]
  -- reindex, then remove the truncation
  rw [sum_offdiag_eq_shift M (fun m n => f m * f n * Kf m n)]
  have hterm : ∀ k j : ℕ,
      (if j + 1 + k ≤ M then f (j + 1 + k) * f (j + 1) * Kf (j + 1 + k) (j + 1) else 0)
        = Kf (j + 1 + k) (j + 1) * g k j := by
    intro k j
    have hcomm : j + 1 + k = j + k + 1 := by omega
    by_cases hle : j + 1 + k ≤ M
    · rw [if_pos hle, hg, hcomm]
      ring
    · rw [if_neg hle, hKzero _ _ (by omega)]
      ring
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hterm k j]
  -- only shifts up to `h` contribute
  have hfloorM : ⌊h⌋₊ ≤ M := by
    refine Nat.floor_le_floor ?_
    have hsx : Real.sqrt x ≤ x := by nlinarith [Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ x)]
    have : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
    linarith
  have hrestrict : ∑ k ∈ Finset.Icc 1 M, ∑ j ∈ Finset.range M, Kf (j + 1 + k) (j + 1) * g k j
      = ∑ k ∈ Finset.Icc 1 ⌊h⌋₊, ∑ j ∈ Finset.range M, Kf (j + 1 + k) (j + 1) * g k j := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, le_trans hk.2 hfloorM⟩
    · intro k hkM hk
      rw [Finset.mem_Icc] at hkM
      rw [Finset.mem_Icc] at hk
      have hkgt : ⌊h⌋₊ < k := by omega
      have hkR : h < (k : ℝ) := by
        by_contra hcon
        rw [not_lt] at hcon
        exact absurd (Nat.le_floor hcon) (by omega)
      refine Finset.sum_eq_zero fun j _ => ?_
      have : Kf (j + 1 + k) (j + 1) = 0 := by
        rw [hKf]
        simp [fibre_kernel_eq_empty_of_shift (x := x) (h := h) (i := j + 1) (k := k) hx4 hkR]
      rw [this, zero_mul]
  rw [hrestrict]
  -- split the kernel into its smooth model and a bounded error
  set e : ℕ → ℕ → ℝ := fun k j => Kf (j + 1 + k) (j + 1) - w k j with he
  have hsplit : ∑ k ∈ Finset.Icc 1 ⌊h⌋₊, ∑ j ∈ Finset.range M,
        Kf (j + 1 + k) (j + 1) * g k j
      = (∑ k ∈ Finset.Icc 1 ⌊h⌋₊, ∑ j ∈ Finset.range M, w k j * g k j)
        + ∑ k ∈ Finset.Icc 1 ⌊h⌋₊, ∑ j ∈ Finset.range M, e k j * g k j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he]
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · -- the smooth half: partial summation
    refine abs_shift_sum_le (f := fun i => f (i + 1)) (n := M) hB hB0 (w := w) ?_
    intro k hk1 _
    have hval : |w k (M - 1)| ≤ 3 * h + 1 := by
      rw [hw, abs_of_nonneg (fibreSmooth_nonneg x h k (M - 1 + 1))]
      exact fibreSmooth_le hx4 hh0 k (Nat.le_add_left 1 (M - 1))
    have hvar : ∑ i ∈ Finset.range (M - 1), |w k (i + 1) - w k i| ≤ 2 * (3 * h + 1) :=
      fibreSmooth_variation_le hx4 hh0 hk1 (M - 1)
    linarith
  · -- the error half: no cancellation needed
    have hgle : ∀ k j, |g k j| ≤ 1 := by
      intro k j
      rw [hg, abs_mul]
      have h1 := hf (j + 1)
      have h2 := hf (j + k + 1)
      nlinarith [abs_nonneg (f (j + 1)), abs_nonneg (f (j + k + 1))]
    have hele : ∀ k j, |e k j| ≤ 2 := by
      intro k j
      rw [he, hw, hKf]
      exact abs_kernel_sub_fibreSmooth_le hx4 hh0 (Nat.le_add_left 1 j)
    have hsupp : ∀ k j, ⌈3 * Real.sqrt x⌉₊ ≤ j → e k j = 0 := by
      intro k j hj
      have hjR : 3 * Real.sqrt x ≤ ((j + 1 : ℕ) : ℝ) := by
        have h1 : (3 : ℝ) * Real.sqrt x ≤ ((⌈3 * Real.sqrt x⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have h2 : ((⌈3 * Real.sqrt x⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        push_cast
        linarith
      have hK : Kf (j + 1 + k) (j + 1) = 0 := by
        rw [hKf]
        simp [fibre_kernel_eq_empty_of_large (x := x) (h := h) (i := j + 1) (k := k)
          hx4 hhx hjR]
      have hS : w k j = 0 := by
        rw [hw]
        exact fibreSmooth_eq_zero_of_large hx hh0 hhx k hjR
      show Kf (j + 1 + k) (j + 1) - w k j = 0
      rw [hK, hS, sub_zero]
    refine le_trans (abs_error_shift_sum_supported_le hele hsupp hgle ⌊h⌋₊ M) ?_
    have hfl : ((⌊h⌋₊ : ℕ) : ℝ) ≤ h := Nat.floor_le hh0
    have hce : ((⌈3 * Real.sqrt x⌉₊ : ℕ) : ℝ) ≤ 3 * Real.sqrt x + 1 := by
      have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 3 * Real.sqrt x)
      linarith [this]
    have hfl0 : (0 : ℝ) ≤ ((⌊h⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hce0 : (0 : ℝ) ≤ ((⌈3 * Real.sqrt x⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hfl, hce, hfl0, hce0, hs0]

end RHTower.Sieve

end
