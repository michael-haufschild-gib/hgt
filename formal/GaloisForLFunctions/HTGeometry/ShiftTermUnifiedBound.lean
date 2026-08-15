import GaloisForLFunctions.HTGeometry.ShiftSumLimits

/-!
# One uniform bound for every shift below the halfway point

Both the shift-below and the shift-above estimates produce the same exponent `λ_s(μ) + s ν`, so
dividing by the leading quantity `(n+1)^{deg Φ_ν} Θ(n−ν)` leaves exactly `(n+1)^{λ_s(μ)−λ_s(ν)}`.

The uniform gap makes that exponent at most `−γ`; the crude bound `λ_s(μ) − λ_s(ν) ≤ m − s(μ−ν)`
makes it decrease in `μ`.  A convex combination of the two, with weight `ε = γ/(2(m+γ))`, produces a
single exponent `−γ/2 − ε s (μ−ν)` that does both jobs, and the geometric factors of the two cases
are both dominated by `a^{μ−ν}` with `a = ρ · max(1, 1/c₁) · 2^s`.  Below the reference shift the
natural subtraction makes `μ − ν = 0`, so the same expression covers that case with no geometric
factor at all.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- **A single bound for every shift at most half the index.** -/
theorem shiftTerm_le_unified {m : ℕ} {Φ : ℕ → Polynomial ℂ} {C ρ s c₁ c₂ γ ε a K₁ : ℝ}
    {Θ : ℕ → ℝ} {ν n μ : ℕ}
    (hC : 0 < C) (hρ : 0 < ρ) (hs : 0 < s)
    (hdeg : ∀ μ, (Φ μ).natDegree ≤ m)
    (hbd : ∀ μ k : ℕ, ‖(Φ μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * (((k : ℝ)) + 1) ^ (Φ μ).natDegree)
    (hprof : IsRegularFactorialProfile s c₁ c₂ Θ)
    (hgap : ∀ μ, Φ μ ≠ 0 → μ ≠ ν → weightedLevel s Φ μ + γ ≤ weightedLevel s Φ ν)
    (hγ : 0 < γ) (hεpos : 0 < ε) (hεle : ε ≤ 1) (hεkey : ε * ((m : ℝ) + γ) = γ / 2)
    (hadef : a = ρ * max 1 (1 / c₁) * (2 : ℝ) ^ s)
    (hK₁def : K₁ = C * max 1 c₂ ^ ν * max 1 a ^ ν)
    (hΦμ : Φ μ ≠ 0) (hμν : μ ≠ ν) (hhalf : 2 * μ ≤ n) (hνn : ν ≤ n) :
    ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
      ≤ K₁ * (a * ((n : ℝ) + 1) ^ (-(ε * s))) ^ (μ - ν) * ((n : ℝ) + 1) ^ (-(γ / 2)) *
        (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hbase0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
  have hmax1c : (1 : ℝ) ≤ max 1 (1 / c₁) := le_max_left _ _
  have hmax1c₂ : (1 : ℝ) ≤ max 1 c₂ := le_max_left _ _
  have hρa : ρ ≤ a := by
    rw [hadef]
    have h1 : ρ ≤ ρ * max 1 (1 / c₁) := le_mul_of_one_le_right hρ.le hmax1c
    have h2 : ρ * max 1 (1 / c₁) ≤ ρ * max 1 (1 / c₁) * (2 : ℝ) ^ s :=
      le_mul_of_one_le_right (mul_nonneg hρ.le (le_trans zero_le_one hmax1c)) h2s
    linarith
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le hρ hρa
  have hamax : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  have hK₁0 : (0 : ℝ) ≤ K₁ := by
    rw [hK₁def]
    exact mul_nonneg (mul_nonneg hC.le (pow_nonneg (le_trans zero_le_one hmax1c₂) ν))
      (pow_nonneg (le_trans zero_le_one hamax) ν)
  have hDpos : (0 : ℝ) < ((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν) :=
    mul_pos (Real.rpow_pos_of_pos hbase0 _) (hprof.pos (n - ν))
  have hlevν : weightedLevel s Φ ν + s * (ν : ℝ) = (((Φ ν).natDegree : ℕ) : ℝ) := by
    rw [weightedLevel]
    ring
  have hsplitD : ((n : ℝ) + 1) ^ (weightedLevel s Φ μ + s * (ν : ℝ)) * Θ (n - ν)
      = ((n : ℝ) + 1) ^ (weightedLevel s Φ μ - weightedLevel s Φ ν) *
        (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
    rw [← mul_assoc, ← Real.rpow_add hbase0, ← hlevν]
    congr 2
    ring
  have hgapμ := hgap μ hΦμ hμν
  rcases le_or_gt μ ν with hcase | hcase
  · have hzero : μ - ν = 0 := by omega
    have hterm := shiftTerm_le_of_lt hC hρ hs hbd hprof hcase hνn
    have hcoef : C * ρ ^ μ * c₂ ^ (ν - μ) ≤ K₁ := by
      have h1 : ρ ^ μ ≤ max 1 a ^ ν :=
        le_trans (pow_le_pow_left₀ hρ.le (le_trans hρa (le_max_right _ _)) μ)
          (pow_le_pow_right₀ hamax hcase)
      have h2 : c₂ ^ (ν - μ) ≤ max 1 c₂ ^ ν :=
        le_trans (pow_le_pow_left₀ hprof.c₂_pos.le (le_max_right _ _) _)
          (pow_le_pow_right₀ hmax1c₂ (by omega))
      rw [hK₁def]
      calc C * ρ ^ μ * c₂ ^ (ν - μ) = C * (ρ ^ μ * c₂ ^ (ν - μ)) := by ring
        _ ≤ C * (max 1 a ^ ν * max 1 c₂ ^ ν) := by
            refine mul_le_mul_of_nonneg_left ?_ hC.le
            exact mul_le_mul h1 h2 (pow_nonneg hprof.c₂_pos.le _)
              (pow_nonneg (le_trans zero_le_one hamax) ν)
        _ = C * max 1 c₂ ^ ν * max 1 a ^ ν := by ring
    have hexpo : ((n : ℝ) + 1) ^ (weightedLevel s Φ μ - weightedLevel s Φ ν)
        ≤ ((n : ℝ) + 1) ^ (-(γ / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    rw [hzero, pow_zero, mul_one]
    refine le_trans hterm ?_
    rw [hsplitD]
    calc (C * ρ ^ μ * c₂ ^ (ν - μ)) *
          (((n : ℝ) + 1) ^ (weightedLevel s Φ μ - weightedLevel s Φ ν) *
            (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)))
        ≤ K₁ * (((n : ℝ) + 1) ^ (-(γ / 2)) *
            (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) := by
          refine mul_le_mul hcoef (mul_le_mul_of_nonneg_right hexpo hDpos.le) ?_ hK₁0
          exact mul_nonneg (Real.rpow_nonneg hbase0.le _) hDpos.le
      _ = K₁ * ((n : ℝ) + 1) ^ (-(γ / 2)) *
            (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by ring
  · have hνμ : ν ≤ μ := le_of_lt hcase
    have hcastj : ((μ - ν : ℕ) : ℝ) = (μ : ℝ) - (ν : ℝ) := by rw [Nat.cast_sub hνμ]
    have hterm := shiftTerm_le_of_gt hC hρ hs hbd hprof hνμ hhalf
    have htwo : (2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ)) = ((2 : ℝ) ^ s) ^ (μ - ν) := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have hcoef : C * ρ ^ μ * (1 / c₁) ^ (μ - ν) * (2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ))
        ≤ K₁ * a ^ (μ - ν) := by
      rw [htwo]
      have hρsplit : ρ ^ μ = ρ ^ ν * ρ ^ (μ - ν) := by
        rw [← pow_add]
        congr 1
        omega
      have hasplit : a ^ (μ - ν)
          = ρ ^ (μ - ν) * max 1 (1 / c₁) ^ (μ - ν) * ((2 : ℝ) ^ s) ^ (μ - ν) := by
        rw [hadef, mul_pow, mul_pow]
      have hc₁le : (1 / c₁) ^ (μ - ν) ≤ max 1 (1 / c₁) ^ (μ - ν) :=
        pow_le_pow_left₀ (le_of_lt (one_div_pos.mpr hprof.c₁_pos)) (le_max_right _ _) _
      have hρν : C * ρ ^ ν ≤ K₁ := by
        rw [hK₁def]
        have h1 : ρ ^ ν ≤ max 1 a ^ ν :=
          pow_le_pow_left₀ hρ.le (le_trans hρa (le_max_right _ _)) ν
        have h2 : (1 : ℝ) ≤ max 1 c₂ ^ ν := one_le_pow₀ hmax1c₂
        calc C * ρ ^ ν ≤ C * max 1 a ^ ν := mul_le_mul_of_nonneg_left h1 hC.le
          _ ≤ C * max 1 c₂ ^ ν * max 1 a ^ ν := by
              have h5 : C ≤ C * max 1 c₂ ^ ν := le_mul_of_one_le_right hC.le h2
              exact mul_le_mul_of_nonneg_right h5 (pow_nonneg (le_trans zero_le_one hamax) ν)
      calc C * ρ ^ μ * (1 / c₁) ^ (μ - ν) * ((2 : ℝ) ^ s) ^ (μ - ν)
          = (C * ρ ^ ν) * (ρ ^ (μ - ν) * (1 / c₁) ^ (μ - ν) * ((2 : ℝ) ^ s) ^ (μ - ν)) := by
            rw [hρsplit]; ring
        _ ≤ (C * ρ ^ ν) *
              (ρ ^ (μ - ν) * max 1 (1 / c₁) ^ (μ - ν) * ((2 : ℝ) ^ s) ^ (μ - ν)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (le_trans zero_le_one h2s) _)
            exact mul_le_mul_of_nonneg_left hc₁le (pow_nonneg hρ.le _)
        _ = (C * ρ ^ ν) * a ^ (μ - ν) := by rw [hasplit]
        _ ≤ K₁ * a ^ (μ - ν) := mul_le_mul_of_nonneg_right hρν (pow_nonneg hapos.le _)
    have hcrude : weightedLevel s Φ μ - weightedLevel s Φ ν
        ≤ (m : ℝ) - s * ((μ - ν : ℕ) : ℝ) := by
      rw [weightedLevel, weightedLevel, hcastj]
      have h1 : (((Φ μ).natDegree : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (hdeg μ)
      have h2 : (0 : ℝ) ≤ (((Φ ν).natDegree : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hA : weightedLevel s Φ μ - weightedLevel s Φ ν ≤ -γ := by linarith
    have hconv : weightedLevel s Φ μ - weightedLevel s Φ ν
        ≤ (1 - ε) * (-γ) + ε * ((m : ℝ) - s * ((μ - ν : ℕ) : ℝ)) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)
          (by linarith : (0 : ℝ) ≤ -γ - (weightedLevel s Φ μ - weightedLevel s Φ ν)),
        mul_nonneg hεpos.le (by linarith :
          (0 : ℝ) ≤ ((m : ℝ) - s * ((μ - ν : ℕ) : ℝ)) -
            (weightedLevel s Φ μ - weightedLevel s Φ ν))]
    have hval : (1 - ε) * (-γ) + ε * ((m : ℝ) - s * ((μ - ν : ℕ) : ℝ))
        = -(γ / 2) + (-(ε * s)) * ((μ - ν : ℕ) : ℝ) := by
      linear_combination hεkey
    have hexpo : weightedLevel s Φ μ - weightedLevel s Φ ν
        ≤ -(γ / 2) + (-(ε * s)) * ((μ - ν : ℕ) : ℝ) := by
      rw [← hval]
      exact hconv
    have hsplitexp : ((n : ℝ) + 1) ^ (-(γ / 2) + (-(ε * s)) * ((μ - ν : ℕ) : ℝ))
        = ((n : ℝ) + 1) ^ (-(γ / 2)) * (((n : ℝ) + 1) ^ (-(ε * s))) ^ (μ - ν) := by
      rw [Real.rpow_add hbase0, Real.rpow_mul hbase0.le, Real.rpow_natCast]
    have hrpowexp : ((n : ℝ) + 1) ^ (weightedLevel s Φ μ - weightedLevel s Φ ν)
        ≤ ((n : ℝ) + 1) ^ (-(γ / 2)) * (((n : ℝ) + 1) ^ (-(ε * s))) ^ (μ - ν) := by
      rw [← hsplitexp]
      exact Real.rpow_le_rpow_of_exponent_le hbase hexpo
    refine le_trans hterm ?_
    rw [hsplitD]
    calc (C * ρ ^ μ * (1 / c₁) ^ (μ - ν) * (2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ))) *
          (((n : ℝ) + 1) ^ (weightedLevel s Φ μ - weightedLevel s Φ ν) *
            (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)))
        ≤ (K₁ * a ^ (μ - ν)) *
            ((((n : ℝ) + 1) ^ (-(γ / 2)) * (((n : ℝ) + 1) ^ (-(ε * s))) ^ (μ - ν)) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) := by
          refine mul_le_mul hcoef (mul_le_mul_of_nonneg_right hrpowexp hDpos.le) ?_
            (mul_nonneg hK₁0 (pow_nonneg hapos.le _))
          exact mul_nonneg (Real.rpow_nonneg hbase0.le _) hDpos.le
      _ = K₁ * (a * ((n : ℝ) + 1) ^ (-(ε * s))) ^ (μ - ν) * ((n : ℝ) + 1) ^ (-(γ / 2)) *
            (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
          rw [mul_pow]
          ring

end GaloisForLFunctions.HTGeometry
