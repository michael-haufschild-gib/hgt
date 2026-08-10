import GaloisForLFunctions.RHTower.Sieve.FibreIncrementWindow
import GaloisForLFunctions.RHTower.Sieve.FibreShiftSupport
import GaloisForLFunctions.RHTower.Sieve.OffDiagonalReindex
import GaloisForLFunctions.RHTower.Sieve.ShiftSumUniform

/-!
# The off-diagonal, from correlations bounded uniformly in the initial segment

The same assembly as `abs_offDiagonal_le`, but consuming the shift-uniform interface: a single
bound `P` on `∑_{k ≤ h} |∑_{i < J} f(i)f(i+k)|` valid for every `J ≤ ⌈√x+h⌉ + 5`, rather than a
bound on the maximal partial sum at each shift separately.  Summation by parts is applied with the
shift-sum inside; the weight vanishes at the right end of the range and has no increments beyond the
window, so only partial sums of length `≍ √x` occur, and the cost is `∑_j sup_k |Δ w| ≤ 85h + 14`:

```text
| off-diagonal |  ≤  (85h + 14)·P  +  2h·(3√x + 1) .
```

This is the form the averaged Chowla theorem supplies directly: at length `J ≥ δ√x` it is the
theorem, and at shorter lengths the trivial bound `|∑_{i<J}| ≤ J` already suffices.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The off-diagonal, from shift-uniform correlation bounds.** -/
theorem abs_offDiagonal_uniform_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 64 ≤ x) (hh1 : 1 ≤ h) (hhx : h ≤ Real.sqrt x) {P : ℝ}
    (hP : CorrelationUniformBound (fun i => f (i + 1)) ⌊h⌋₊ (fibreWinHi x h + 2) P) :
    |∑ m ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
        ∑ n ∈ (Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊).filter (fun n => n < m),
          f m * f n
            * (((outerBlock x h).filter
                (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℝ)|
      ≤ (85 * h + 14) * P + 2 * h * (3 * Real.sqrt x + 1) := by
  classical
  have hh0 : (0 : ℝ) ≤ h := by linarith
  have hx4 : (4 : ℝ) ≤ x := by linarith
  have hx16 : (16 : ℝ) ≤ x := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs8 : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hfl1 : 1 ≤ ⌊h⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hflR : ((⌊h⌋₊ : ℕ) : ℝ) ≤ h := Nat.floor_le hh0
  set M : ℕ := ⌊x + h * Real.sqrt x⌋₊ with hMdef
  set Kf : ℕ → ℕ → ℝ := fun m n =>
    (((outerBlock x h).filter
      (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℝ) with hKf
  set g : ℕ → ℕ → ℝ := fun k j => (fun i => f (i + 1)) j * (fun i => f (i + 1)) (j + k) with hg
  set w : ℕ → ℕ → ℝ := fun k j => fibreSmooth x h k (j + 1) with hw
  have hKzero : ∀ m n : ℕ, M < m → Kf m n = 0 := by
    intro m n hm
    have : (outerBlock x h).filter
        (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
      rw [Finset.mem_filter, mem_innerFibre] at ha
      exact absurd ha.2.1.1.2 (by omega)
    rw [hKf]
    simp [this]
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
  · -- the smooth half: summation by parts with the shift-sum inside
    have hwin : fibreWinLo x + fibreWinLen x h = fibreWinHi x h + 1 := by
      rw [fibreWinLen]
      have := fibreWinLo_le_succ_fibreWinHi (x := x) (h := h) hx hh0
      omega
    have hMpos : 1 ≤ M := by
      rw [hMdef]
      refine Nat.le_floor ?_
      have hhs : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
      push_cast
      linarith
    have hMR : Real.sqrt x + h + 5 ≤ ((M : ℕ) : ℝ) := by
      have hfl : x + h * Real.sqrt x - 1 < ((⌊x + h * Real.sqrt x⌋₊ : ℕ) : ℝ) :=
        Nat.sub_one_lt_floor _
      have hhs : (0 : ℝ) ≤ h * Real.sqrt x := by positivity
      rw [hMdef]
      nlinarith [hfl, hhs, hs8, hsq, hhx]
    have hbase := abs_shift_sum_uniform_le (f := fun i => f (i + 1)) (n := M) (K := ⌊h⌋₊)
      (J₀ := fibreWinHi x h + 2) (V := 85 * h + 14) hP
      (w := w) (d := fibreIncr x h ⌊h⌋₊)
      (fun j => fibreIncr_nonneg (by linarith) hh0 _ j)
      (fun k hk1 hk2 j => abs_fibreSmooth_increment_le_fibreIncr hx hh0 hhx hk1 hk2 j)
      (fun j hj => by
        rw [fibreIncr, if_neg]
        rintro ⟨-, hlt⟩
        omega)
      (fun k hk1 _ => by
        show fibreSmooth x h k (M - 1 + 1) = 0
        have hM1 : M - 1 + 1 = M := by omega
        rw [hM1]
        exact fibreSmooth_eq_zero_of_ge hx hh0 hhx hk1 hMR)
      (sum_fibreIncr_le hx hh0 hfl1 hflR (M - 1))
    exact hbase
  · -- the error half: unchanged
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
        exact fibreSmooth_eq_zero_of_large hx16 hh0 hhx k hjR
      show Kf (j + 1 + k) (j + 1) - w k j = 0
      rw [hK, hS, sub_zero]
    refine le_trans (abs_error_shift_sum_supported_le hele hsupp hgle ⌊h⌋₊ M) ?_
    have hce : ((⌈3 * Real.sqrt x⌉₊ : ℕ) : ℝ) ≤ 3 * Real.sqrt x + 1 := by
      have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 3 * Real.sqrt x)
      linarith [this]
    have hfl0 : (0 : ℝ) ≤ ((⌊h⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hce0 : (0 : ℝ) ≤ ((⌈3 * Real.sqrt x⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hflR, hce, hfl0, hce0, hs0]

end RHTower.Sieve

end
