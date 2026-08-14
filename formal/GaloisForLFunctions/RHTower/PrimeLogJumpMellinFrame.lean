import Mathlib

/-!
# The two-prime jump Mellin frame

The two boundary phase channels of the prime-log jump shell are

```text
F_A(s) = H(s) − A^{-s},      F_B(s) = B^{-s} − H(s),
H(s) = (B − A)⁻¹ ∫_A^B x^{-s} dx,
```

the limits of the normalized first Mellin boundary traces along the two source-defined clocks.
They are entire, they both vanish at `s = 0`, and `s = 0` is their **only** common zero: a common
zero forces `A^{-s} = B^{-s}`, hence `H(s) = A^{-s}/(1 − s)` by the closed form of the shell
average, and comparing with `H(s) = A^{-s}` forces `s = 0`.

So no Xi conormal is lost: at every point at least one channel is nonzero.
-/

namespace GaloisForLFunctions.RHTower

open Complex

variable {A B : ℝ}

/-- The shell average of `x^{-s}` over the jump shell `[A, B]`. -/
noncomputable def shellAverage (A B : ℝ) (s : ℂ) : ℂ :=
  (((B : ℂ) - (A : ℂ))⁻¹) * ∫ x in A..B, (x : ℂ) ^ (-s)

/-- **The closed form of the shell average** away from `s = 1`. -/
theorem shellAverage_eq (hA : 0 < A) (hAB : A < B) {s : ℂ} (hs : s ≠ 1) :
    shellAverage A B s
      = (((B : ℂ) ^ (1 - s) - (A : ℂ) ^ (1 - s)) / (1 - s)) * ((B : ℂ) - (A : ℂ))⁻¹ := by
  have hzero : (0 : ℝ) ∉ Set.uIcc A B := by
    rw [Set.uIcc_of_le (le_of_lt hAB)]
    intro hmem
    exact absurd hmem.1 (by linarith)
  have hne : (-s : ℂ) ≠ -1 := fun h => hs (neg_inj.mp h)
  have hint := integral_cpow (a := A) (b := B) (r := -s) (Or.inr ⟨hne, hzero⟩)
  rw [shellAverage, hint]
  rw [show (-s + 1 : ℂ) = 1 - s by ring]
  ring

/-- The first boundary phase channel. -/
noncomputable def channelA (A B : ℝ) (s : ℂ) : ℂ := shellAverage A B s - (A : ℂ) ^ (-s)

/-- The second boundary phase channel. -/
noncomputable def channelB (A B : ℝ) (s : ℂ) : ℂ := (B : ℂ) ^ (-s) - shellAverage A B s

theorem shellAverage_zero (hA : 0 < A) (hAB : A < B) : shellAverage A B 0 = 1 := by
  have hne : (0 : ℂ) ≠ 1 := by norm_num
  rw [shellAverage_eq hA hAB hne]
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hA)
  have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hBA : ((B : ℂ) - (A : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr fun h => absurd (Complex.ofReal_inj.mp h) (by linarith)
  simp only [sub_zero, Complex.cpow_one]
  field_simp

theorem channelA_zero (hA : 0 < A) (hAB : A < B) : channelA A B 0 = 0 := by
  rw [channelA, shellAverage_zero hA hAB]
  simp

theorem channelB_zero (hA : 0 < A) (hAB : A < B) : channelB A B 0 = 0 := by
  rw [channelB, shellAverage_zero hA hAB]
  simp

/-- **The two channels have `s = 0` as their only common zero.** -/
theorem eq_zero_of_channel_common_zero (hA : 0 < A) (hAB : A < B) {s : ℂ}
    (h1 : channelA A B s = 0) (h2 : channelB A B s = 0) : s = 0 := by
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hA)
  have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hBA : ((B : ℂ) - (A : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr fun h => absurd (Complex.ofReal_inj.mp h) (by linarith)
  -- the two endpoint powers agree with the shell average
  have hAeq : (A : ℂ) ^ (-s) = shellAverage A B s := by
    rw [channelA, sub_eq_zero] at h1
    exact h1.symm
  have hBeq : (B : ℂ) ^ (-s) = shellAverage A B s := by
    rw [channelB, sub_eq_zero] at h2
    exact h2
  -- `s = 1` is impossible
  have hζeq : (A : ℂ) ^ (-s) = (B : ℂ) ^ (-s) := by rw [hAeq, hBeq]
  have hs1 : s ≠ 1 := by
    intro hs
    subst hs
    rw [Complex.cpow_neg_one, Complex.cpow_neg_one] at hζeq
    have hAB' : (A : ℂ) = (B : ℂ) := by
      field_simp at hζeq
      exact hζeq.symm
    exact absurd (Complex.ofReal_inj.mp hAB') (by linarith)
  -- the closed form collapses
  have hApow : (A : ℂ) ^ (1 - s) = (A : ℂ) * (A : ℂ) ^ (-s) := by
    rw [show (1 - s : ℂ) = 1 + -s by ring, Complex.cpow_add _ _ hA0, Complex.cpow_one]
  have hBpow : (B : ℂ) ^ (1 - s) = (B : ℂ) * (B : ℂ) ^ (-s) := by
    rw [show (1 - s : ℂ) = 1 + -s by ring, Complex.cpow_add _ _ hB0, Complex.cpow_one]
  have hζ : (A : ℂ) ^ (-s) = (B : ℂ) ^ (-s) := hζeq
  have hζ0 : (A : ℂ) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hA0]
    exact Complex.exp_ne_zero _
  have hs1' : (1 - s : ℂ) ≠ 0 := by
    intro h
    exact hs1 (by linear_combination -h)
  have hclosed := shellAverage_eq hA hAB hs1
  rw [hApow, hBpow, ← hζ] at hclosed
  -- `H(s) = A^{-s} / (1 - s)`
  have hH : shellAverage A B s = (A : ℂ) ^ (-s) / (1 - s) := by
    rw [hclosed]
    field_simp
  rw [← hAeq] at hH
  field_simp at hH
  linear_combination -hH

end GaloisForLFunctions.RHTower
