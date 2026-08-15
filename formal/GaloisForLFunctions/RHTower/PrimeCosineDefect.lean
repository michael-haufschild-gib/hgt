import GaloisForLFunctions.RHTower.EulerTiltCovariance

/-!
# The oscillatory prime defect

Subtracting one inside the cosine splits the oscillatory Euler sum into a quadratic head and a
harmonic tail:

```text
|∑_{p ≤ Y} p^{-σ} (cos(t log p) - 1)|
  ≤ (t²/2) ∑_{p ≤ Z} (log p)²/p + 2 ∑_{Z < p ≤ Y} 1/p,
```

for any split point `Z` with `log Z ≤ 1/t`.  With `Z = e^{1/t}` both pieces are bounded, which is
the cancellation input of the all-cumulant Euler-edge amplitude.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The oscillatory prime defect `∑_{p ≤ Y} p^{-σ}(cos(t log p) - 1)`. -/
def primeCosineDefect (σ t Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-σ) * (Real.cos (t * Real.log p) - 1)

theorem abs_cos_sub_one_le_sq (x : ℝ) : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  have hlow := Real.one_sub_sq_div_two_le_cos (x := x)
  have hup := Real.cos_le_one x
  rw [abs_le]
  constructor <;> linarith

theorem abs_cos_sub_one_le_two (x : ℝ) : |Real.cos x - 1| ≤ 2 := by
  have hlow := Real.neg_one_le_cos x
  have hup := Real.cos_le_one x
  rw [abs_le]
  constructor <;> linarith

theorem primesLE_subset {Z Y : ℝ} (hZY : Z ≤ Y) :
    Nat.primesLE ⌊Z⌋₊ ⊆ Nat.primesLE ⌊Y⌋₊ := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨le_trans hp.1 (Nat.floor_le_floor hZY), hp.2⟩

theorem mertensS_sub_eq_sum_sdiff {Z Y : ℝ} (hZY : Z ≤ Y) :
    Sieve.mertensS ⌊Y⌋₊ - Sieve.mertensS ⌊Z⌋₊
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊Z⌋₊, 1 / (p : ℝ) := by
  have hsub := primesLE_subset hZY
  have h := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) hsub
  rw [Sieve.mertensS, Sieve.mertensS]
  linarith [h]

/-- **The oscillatory defect splits into a quadratic head and a harmonic tail.** -/
theorem abs_primeCosineDefect_le {σ t Y Z : ℝ} (hσ : 1 ≤ σ) (ht0 : 0 < t)
    (hZ2 : 2 ≤ Z) (hZY : Z ≤ Y) :
    |primeCosineDefect σ t Y|
      ≤ t ^ 2 / 2 * primeLogSqSumLE Z
        + 2 * (Sieve.mertensS ⌊Y⌋₊ - Sieve.mertensS ⌊Z⌋₊) := by
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hsub := primesLE_subset hZY
  have hsplit : primeCosineDefect σ t Y
      = ∑ p ∈ Nat.primesLE ⌊Z⌋₊, (p : ℝ) ^ (-σ) * (Real.cos (t * Real.log p) - 1)
        + ∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊Z⌋₊,
          (p : ℝ) ^ (-σ) * (Real.cos (t * Real.log p) - 1) := by
    rw [primeCosineDefect, ← Finset.sum_sdiff hsub]
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hhead : |∑ p ∈ Nat.primesLE ⌊Z⌋₊, (p : ℝ) ^ (-σ) * (Real.cos (t * Real.log p) - 1)|
      ≤ t ^ 2 / 2 * primeLogSqSumLE Z := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [primeLogSqSumLE, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hrp : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
    have hrple : (p : ℝ) ^ (-σ) ≤ ((p : ℝ))⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by linarith)
        (show -σ ≤ -1 by linarith)
      rwa [Real.rpow_neg_one] at h
    have hcos := abs_cos_sub_one_le_sq (t * Real.log p)
    rw [abs_mul, abs_of_pos hrp]
    have hstep : (p : ℝ) ^ (-σ) * |Real.cos (t * Real.log p) - 1|
        ≤ ((p : ℝ))⁻¹ * ((t * Real.log p) ^ 2 / 2) := by
      have h1 : (p : ℝ) ^ (-σ) * |Real.cos (t * Real.log p) - 1|
          ≤ ((p : ℝ))⁻¹ * |Real.cos (t * Real.log p) - 1| :=
        mul_le_mul_of_nonneg_right hrple (abs_nonneg _)
      have h2 : ((p : ℝ))⁻¹ * |Real.cos (t * Real.log p) - 1|
          ≤ ((p : ℝ))⁻¹ * ((t * Real.log p) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      linarith
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have htail : |∑ p ∈ Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊Z⌋₊,
        (p : ℝ) ^ (-σ) * (Real.cos (t * Real.log p) - 1)|
      ≤ 2 * (Sieve.mertensS ⌊Y⌋₊ - Sieve.mertensS ⌊Z⌋₊) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [mertensS_sub_eq_sum_sdiff hZY, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpmem : p ∈ Nat.primesLE ⌊Y⌋₊ := (Finset.mem_sdiff.mp hp).1
    have hprime := Nat.prime_of_mem_primesLE hpmem
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hrp : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
    have hrple : (p : ℝ) ^ (-σ) ≤ ((p : ℝ))⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by linarith)
        (show -σ ≤ -1 by linarith)
      rwa [Real.rpow_neg_one] at h
    have hcos := abs_cos_sub_one_le_two (t * Real.log p)
    rw [abs_mul, abs_of_pos hrp]
    have hstep : (p : ℝ) ^ (-σ) * |Real.cos (t * Real.log p) - 1| ≤ ((p : ℝ))⁻¹ * 2 := by
      have h1 : (p : ℝ) ^ (-σ) * |Real.cos (t * Real.log p) - 1|
          ≤ ((p : ℝ))⁻¹ * |Real.cos (t * Real.log p) - 1| :=
        mul_le_mul_of_nonneg_right hrple (abs_nonneg _)
      have h2 : ((p : ℝ))⁻¹ * |Real.cos (t * Real.log p) - 1| ≤ ((p : ℝ))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      linarith
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  linarith

end

end RHTower
