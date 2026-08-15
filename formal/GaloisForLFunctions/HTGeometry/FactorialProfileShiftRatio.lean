import GaloisForLFunctions.HTGeometry.RegularFactorialProfile

/-!
# Comparing a factorial profile across the shifts of a coefficient recursion

A coefficient recursion read at index `n` compares the profile at `n − μ` with the profile at a
reference shift `n − ν`.  Two forms of the comparison are needed.

* A **power form**, `Θ(n−μ) ≤ (1/c₁)^{μ−ν} (n−μ+1)^{−s(μ−ν)} Θ(n−ν)`, which is what turns the
  degree of a shift polynomial into its weighted level.  It is sharp while `μ` stays well below `n`.
* A **factorial form**, `Θ(n−μ) ≤ (1/c₁)^{μ−ν} ((n−μ)!/(n−ν)!)^{s} Θ(n−ν)`, which stays sharp all
  the way out to `μ = n`, where the power form degenerates to no information at all.

Both come from iterating the single-step ratio, and the opposite direction — for shifts *below* the
reference one, of which there are only finitely many — comes from iterating the other step bound.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

namespace IsRegularFactorialProfile

variable {s c₁ c₂ : ℝ} {Θ : ℕ → ℝ}

/-! ### Factorial ratios against powers -/

theorem pow_le_factorial_div {a b : ℕ} (hab : a ≤ b) :
    (((a : ℝ) + 1)) ^ (b - a) ≤ ((b ! : ℝ)) / ((a ! : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base =>
      have hne : ((a ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
      simp [div_self hne]
  | succ b hb ih =>
      have hcount : b + 1 - a = (b - a) + 1 := by omega
      have hcast : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
        have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hb
        linarith
      rw [hcount, pow_succ, factorial_succ_div_eq]
      calc (((a : ℝ) + 1)) ^ (b - a) * ((a : ℝ) + 1)
          ≤ ((((b ! : ℝ))) / ((a ! : ℝ))) * ((b : ℝ) + 1) :=
            mul_le_mul ih hcast (by positivity) (le_of_lt factorial_div_pos)
        _ = ((b : ℝ) + 1) * ((((b ! : ℝ))) / ((a ! : ℝ))) := by ring

theorem factorial_div_le_pow {a b : ℕ} (hab : a ≤ b) :
    ((b ! : ℝ)) / ((a ! : ℝ)) ≤ (((b : ℝ) + 1)) ^ (b - a) := by
  induction b, hab using Nat.le_induction with
  | base =>
      have hne : ((a ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
      simp [div_self hne]
  | succ b hb ih =>
      have hcount : b + 1 - a = (b - a) + 1 := by omega
      have hcast : ((b : ℝ) + 1) ≤ (((b : ℕ) + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      have hmono : (((b : ℝ) + 1)) ^ (b - a) ≤ ((((b : ℕ) + 1 : ℕ) : ℝ) + 1) ^ (b - a) :=
        pow_le_pow_left₀ (by positivity) hcast _
      rw [hcount, pow_succ, factorial_succ_div_eq]
      calc ((b : ℝ) + 1) * ((((b ! : ℝ))) / ((a ! : ℝ)))
          ≤ ((b : ℝ) + 1) * (((b : ℝ) + 1)) ^ (b - a) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ ((((b : ℕ) + 1 : ℕ) : ℝ) + 1) * ((((b : ℕ) + 1 : ℕ) : ℝ) + 1) ^ (b - a) :=
            mul_le_mul hcast hmono (by positivity) (by positivity)
        _ = ((((b : ℕ) + 1 : ℕ) : ℝ) + 1) ^ (b - a) * ((((b : ℕ) + 1 : ℕ) : ℝ) + 1) := by ring

/-! ### Shifts above the reference one -/

/-- **Factorial form.**  Sharp out to the last shift. -/
theorem shift_above_factorial (h : IsRegularFactorialProfile s c₁ c₂ Θ) {n μ ν : ℕ}
    (hνμ : ν ≤ μ) (hμn : μ ≤ n) :
    Θ (n - μ) * (c₁ ^ (μ - ν) * ((((n - ν)! : ℝ)) / (((n - μ)! : ℝ))) ^ s) ≤ Θ (n - ν) := by
  have hle : n - μ ≤ n - ν := by omega
  have hcount : (n - ν) - (n - μ) = μ - ν := by omega
  have h1 := h.block_lower hle
  rw [hcount] at h1
  linarith [h1]

/-- **Power form.**  Sharp while the shift stays well below the index. -/
theorem shift_above_pow (h : IsRegularFactorialProfile s c₁ c₂ Θ) (hs : 0 ≤ s) {n μ ν : ℕ}
    (hνμ : ν ≤ μ) (hμn : μ ≤ n) :
    Θ (n - μ) * (c₁ ^ (μ - ν) * (((n - μ : ℕ) : ℝ) + 1) ^ (s * ((μ - ν : ℕ) : ℝ)))
      ≤ Θ (n - ν) := by
  have hle : n - μ ≤ n - ν := by omega
  have hbase : (0 : ℝ) < ((n - μ : ℕ) : ℝ) + 1 := by positivity
  have hpow : (((n - μ : ℕ) : ℝ) + 1) ^ (s * ((μ - ν : ℕ) : ℝ))
      ≤ ((((n - ν)! : ℝ)) / (((n - μ)! : ℝ))) ^ s := by
    have hstep : (((n - μ : ℕ) : ℝ) + 1) ^ ((n - ν) - (n - μ))
        ≤ ((((n - ν)! : ℝ)) / (((n - μ)! : ℝ))) := pow_le_factorial_div hle
    have hcount : (n - ν) - (n - μ) = μ - ν := by omega
    rw [hcount] at hstep
    have hrw : (((n - μ : ℕ) : ℝ) + 1) ^ (s * ((μ - ν : ℕ) : ℝ))
        = ((((n - μ : ℕ) : ℝ) + 1) ^ (μ - ν)) ^ s := by
      rw [← Real.rpow_natCast (((n - μ : ℕ) : ℝ) + 1) (μ - ν), ← Real.rpow_mul hbase.le]
      congr 1
      ring
    rw [hrw]
    exact Real.rpow_le_rpow (by positivity) hstep hs
  refine le_trans ?_ (h.shift_above_factorial hνμ hμn)
  refine mul_le_mul_of_nonneg_left ?_ (h.pos (n - μ)).le
  exact mul_le_mul_of_nonneg_left hpow (pow_nonneg h.c₁_pos.le _)

/-! ### Shifts below the reference one -/

theorem shift_below_factorial (h : IsRegularFactorialProfile s c₁ c₂ Θ) {n μ ν : ℕ}
    (hμν : μ ≤ ν) (hνn : ν ≤ n) :
    Θ (n - μ) ≤ Θ (n - ν) * c₂ ^ (ν - μ) * ((((n - μ)! : ℝ)) / (((n - ν)! : ℝ))) ^ s := by
  have hle : n - ν ≤ n - μ := by omega
  have hcount : (n - μ) - (n - ν) = ν - μ := by omega
  have h1 := h.block_upper hle
  rw [hcount] at h1
  exact h1

/-- **Power form below the reference shift.**  The profile can grow, but only by the weight that a
weighted level already accounts for. -/
theorem shift_below_pow (h : IsRegularFactorialProfile s c₁ c₂ Θ) (hs : 0 ≤ s) {n μ ν : ℕ}
    (hμν : μ ≤ ν) (hνn : ν ≤ n) :
    Θ (n - μ) ≤ Θ (n - ν) * c₂ ^ (ν - μ) *
      (((n - μ : ℕ) : ℝ) + 1) ^ (s * ((ν - μ : ℕ) : ℝ)) := by
  have hle : n - ν ≤ n - μ := by omega
  have hbase : (0 : ℝ) < ((n - μ : ℕ) : ℝ) + 1 := by positivity
  have hpow : ((((n - μ)! : ℝ)) / (((n - ν)! : ℝ))) ^ s
      ≤ (((n - μ : ℕ) : ℝ) + 1) ^ (s * ((ν - μ : ℕ) : ℝ)) := by
    have hstep : ((((n - μ)! : ℝ)) / (((n - ν)! : ℝ)))
        ≤ (((n - μ : ℕ) : ℝ) + 1) ^ ((n - μ) - (n - ν)) := factorial_div_le_pow hle
    have hcount : (n - μ) - (n - ν) = ν - μ := by omega
    rw [hcount] at hstep
    have hrw : (((n - μ : ℕ) : ℝ) + 1) ^ (s * ((ν - μ : ℕ) : ℝ))
        = ((((n - μ : ℕ) : ℝ) + 1) ^ (ν - μ)) ^ s := by
      rw [← Real.rpow_natCast (((n - μ : ℕ) : ℝ) + 1) (ν - μ), ← Real.rpow_mul hbase.le]
      congr 1
      ring
    rw [hrw]
    exact Real.rpow_le_rpow (le_of_lt factorial_div_pos) hstep hs
  refine le_trans (h.shift_below_factorial hμν hνn) ?_
  refine mul_le_mul_of_nonneg_left hpow ?_
  exact mul_nonneg (h.pos (n - ν)).le (pow_nonneg h.c₂_pos.le _)

end IsRegularFactorialProfile

end GaloisForLFunctions.HTGeometry
