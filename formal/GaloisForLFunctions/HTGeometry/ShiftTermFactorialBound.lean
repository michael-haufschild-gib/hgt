import GaloisForLFunctions.HTGeometry.ShiftTermPowerBound

/-!
# One term of a coefficient recursion when the shift exceeds half the index

Past the halfway point the power comparison `Θ(n−μ) ≤ (n−μ+1)^{−s(μ−ν)} Θ(n−ν)` carries no
information: `n − μ + 1` is bounded, so its negative power is bounded below by a constant, while the
geometric factors `ρ^μ` and `c₁^{−(μ−ν)}` keep growing.

The factorial form does not degenerate.  Every index between `n − μ` and `n − ν` contributes a factor
to `(n−ν)!/(n−μ)!`, and past the halfway point all the indices above `⌊n/2⌋` are among them, so the
whole range is controlled by the single quantity `(⌊n/2⌋)! / (n−ν)!`, independent of `μ`.  That
quantity is super-exponentially small, which is what absorbs the exponential growth of the geometric
factors and of the number of terms.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- **A shift past half the index contributes at most a `μ`-independent factorial factor.** -/
theorem shiftTerm_le_factorial {Φ : ℕ → Polynomial ℂ} {C ρ s c₁ c₂ : ℝ} {Θ : ℕ → ℝ} {m : ℕ}
    (hC : 0 < C) (hρ : 0 < ρ) (hs : 0 < s)
    (hdeg : ∀ μ, (Φ μ).natDegree ≤ m)
    (hbd : ∀ μ k : ℕ, ‖(Φ μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * (((k : ℝ)) + 1) ^ (Φ μ).natDegree)
    (hprof : IsRegularFactorialProfile s c₁ c₂ Θ) {n μ ν : ℕ}
    (hνμ : ν ≤ μ) (hμn : μ ≤ n) (hhi : n < 2 * μ) :
    ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
      ≤ (C * (max 1 ρ) ^ n * (max 1 (1 / c₁)) ^ n) *
          (((n : ℝ) + 1) ^ m * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
            * Θ (n - ν)) := by
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmax1 : (1 : ℝ) ≤ max 1 ρ := le_max_left _ _
  have hmax2 : (1 : ℝ) ≤ max 1 (1 / c₁) := le_max_left _ _
  -- the polynomial factor
  have hpoly : ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖
      ≤ C * (max 1 ρ) ^ n * ((n : ℝ) + 1) ^ m := by
    refine le_trans (norm_eval_le_index hC hρ hbd n μ) ?_
    have hrpow : ((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ) = ((n : ℝ) + 1) ^ (Φ μ).natDegree :=
      Real.rpow_natCast _ _
    rw [hrpow]
    have hgeo : ρ ^ μ ≤ (max 1 ρ) ^ n :=
      le_trans (pow_le_pow_left₀ hρ.le (le_max_right _ _) μ) (pow_le_pow_right₀ hmax1 hμn)
    have hpowmono : ((n : ℝ) + 1) ^ (Φ μ).natDegree ≤ ((n : ℝ) + 1) ^ m :=
      pow_le_pow_right₀ hbase (hdeg μ)
    calc C * ρ ^ μ * ((n : ℝ) + 1) ^ (Φ μ).natDegree
        ≤ C * (max 1 ρ) ^ n * ((n : ℝ) + 1) ^ (Φ μ).natDegree := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hgeo hC.le
      _ ≤ C * (max 1 ρ) ^ n * ((n : ℝ) + 1) ^ m :=
          mul_le_mul_of_nonneg_left hpowmono (by positivity)
  -- the profile factor, in factorial form
  have hfacpos : (0 : ℝ) < ((((n - ν)! : ℕ) : ℝ)) / ((((n - μ)! : ℕ) : ℝ)) :=
    IsRegularFactorialProfile.factorial_div_pos
  have hinv : (((((n - μ)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
      = ((((((n - ν)! : ℕ) : ℝ)) / ((((n - μ)! : ℕ) : ℝ))) ^ s)⁻¹ := by
    rw [← Real.inv_rpow (le_of_lt hfacpos), inv_div]
  have hstep := hprof.shift_above_factorial hνμ hμn
  have hpos : (0 : ℝ) < c₁ ^ (μ - ν) * (((((n - ν)! : ℕ) : ℝ)) / ((((n - μ)! : ℕ) : ℝ))) ^ s :=
    mul_pos (pow_pos hprof.c₁_pos _) (Real.rpow_pos_of_pos hfacpos _)
  rw [← le_div_iff₀ hpos] at hstep
  have hprofile : Θ (n - μ) ≤ Θ (n - ν) *
      ((1 / c₁) ^ (μ - ν) * (((((n - μ)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s) := by
    refine le_trans hstep (le_of_eq ?_)
    rw [hinv, one_div, inv_pow, ← mul_inv, ← div_eq_mul_inv]
  -- the factorial ratio is dominated by its value at half the index
  have hhalf : n - μ ≤ n / 2 := by omega
  have hfacle : ((((n - μ)! : ℕ) : ℝ)) ≤ ((((n / 2)! : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.factorial_le hhalf)
  have hden : (0 : ℝ) < ((((n - ν)! : ℕ) : ℝ)) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hdivle : ((((n - μ)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))
      ≤ ((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hfacle (le_of_lt (inv_pos.mpr hden))
    rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at hmul
  have hrpowle : (((((n - μ)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
      ≤ (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s :=
    Real.rpow_le_rpow (le_of_lt IsRegularFactorialProfile.factorial_div_pos) hdivle hs.le
  have hc₁inv : (0 : ℝ) ≤ 1 / c₁ := le_of_lt (one_div_pos.mpr hprof.c₁_pos)
  have hgeo2 : (1 / c₁) ^ (μ - ν) ≤ (max 1 (1 / c₁)) ^ n := by
    have h1 : (1 / c₁) ^ (μ - ν) ≤ (max 1 (1 / c₁)) ^ (μ - ν) :=
      pow_le_pow_left₀ hc₁inv (le_max_right _ _) _
    exact le_trans h1 (pow_le_pow_right₀ hmax2 (by omega))
  have hprofile' : Θ (n - μ) ≤ (max 1 (1 / c₁)) ^ n *
      ((((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s * Θ (n - ν)) := by
    refine le_trans hprofile ?_
    have hΘ : (0 : ℝ) ≤ Θ (n - ν) := (hprof.pos (n - ν)).le
    have hmul : (1 / c₁) ^ (μ - ν) *
        (((((n - μ)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
        ≤ (max 1 (1 / c₁)) ^ n * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s :=
      mul_le_mul hgeo2 hrpowle (le_of_lt (Real.rpow_pos_of_pos
        IsRegularFactorialProfile.factorial_div_pos _)) (pow_nonneg (le_trans zero_le_one hmax2) n)
    calc Θ (n - ν) * ((1 / c₁) ^ (μ - ν) *
          (((((n - μ)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s)
        ≤ Θ (n - ν) * ((max 1 (1 / c₁)) ^ n *
            (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s) :=
          mul_le_mul_of_nonneg_left hmul hΘ
      _ = (max 1 (1 / c₁)) ^ n *
            ((((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s * Θ (n - ν)) := by ring
  calc ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
      ≤ (C * (max 1 ρ) ^ n * ((n : ℝ) + 1) ^ m) *
          ((max 1 (1 / c₁)) ^ n *
            ((((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s * Θ (n - ν))) :=
        mul_le_mul hpoly hprofile' (hprof.pos (n - μ)).le (by positivity)
    _ = (C * (max 1 ρ) ^ n * (max 1 (1 / c₁)) ^ n) *
          (((n : ℝ) + 1) ^ m * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
            * Θ (n - ν)) := by ring

end GaloisForLFunctions.HTGeometry
