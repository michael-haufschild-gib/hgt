import GaloisForLFunctions.RHTower.MontgomeryPrimeDirichletSeries
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp

/-!
# The mean square of the prime side

`|∫_0^T ‖primeSide x t‖² dt − T Σ_n d_n²| ≤ 104 Σ_n n d_n²`, `d_n = Λ(n)(x/n)^{−1/2}` (`n ≤ x`),
`Λ(n)(x/n)^{3/2}` (`n > x`).

The prime side has the modulus of the Dirichlet series `P(t) = Σ_n d_n e^{it log n}`.  Its
truncations `P_N` are the corpus's `dirPoly`, for which the sharp Montgomery–Vaughan mean value
theorem gives `|∫_0^T |P_N|² − T Σ_{n<N} d_n²| ≤ 104 Σ_{n<N} n d_n²`; the tails
`‖P − P_N‖ ≤ τ_N → 0` are uniform in `t`, so the inequality passes to the limit.
-/

open Complex Filter Topology MeasureTheory

namespace RHTower

/-! ## Truncations are Dirichlet polynomials -/

theorem primePhasePartial_succ_eq_dirPoly (x : ℝ) (N : ℕ) (t : ℝ) :
    primePhasePartial x (N + 1) t
      = Sieve.dirPoly N (fun m : Fin N => (primeAmp x ((m : ℕ) + 1) : ℂ)) t := by
  unfold primePhasePartial Sieve.dirPoly
  rw [Finset.sum_range_succ', Fin.sum_univ_eq_sum_range
    (fun m => (primeAmp x (m + 1) : ℂ) * Complex.exp (((t * Real.log (((m : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I)) N]
  simp only [primeAmp_zero, Complex.ofReal_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast; rfl

/-! ## Summability of the squared amplitudes -/

theorem primeAmp_sq_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    primeAmp x n ^ 2 ≤ 16 * x ^ (3 : ℝ) * ((n : ℝ) ^ ((5 / 2 : ℝ)))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeAmp]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have h := primeAmp_le hx n
  have h0 := primeAmp_nonneg hx0.le n
  calc primeAmp x n ^ 2 ≤ (4 * x ^ ((3 / 2 : ℝ)) * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = 16 * x ^ (3 : ℝ) * ((n : ℝ) ^ ((5 / 2 : ℝ)))⁻¹ := by
        have hx32 : (x ^ ((3 / 2 : ℝ))) ^ 2 = x ^ (3 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
        have hn54 : ((n : ℝ) ^ ((5 / 4 : ℝ))) ^ 2 = (n : ℝ) ^ ((5 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]; norm_num
        rw [mul_pow, mul_pow, inv_pow, hx32, hn54]; norm_num

theorem summable_primeAmp_sq {x : ℝ} (hx : 1 ≤ x) : Summable (fun n : ℕ => primeAmp x n ^ 2) :=
  Summable.of_nonneg_of_le (fun n => sq_nonneg _) (primeAmp_sq_le hx)
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 2)).mul_left _)

theorem summable_mul_primeAmp_sq {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun n : ℕ => (n : ℝ) * primeAmp x n ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    (fun n => ?_) ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left
      (16 * x ^ (3 : ℝ)))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := primeAmp_sq_le hx n
  calc (n : ℝ) * primeAmp x n ^ 2 ≤ (n : ℝ) * (16 * x ^ (3 : ℝ) * ((n : ℝ) ^ ((5 / 2 : ℝ)))⁻¹) := by
        gcongr
    _ = 16 * x ^ (3 : ℝ) * ((n : ℝ) ^ ((3 / 2 : ℝ)))⁻¹ := by
        rw [← Real.rpow_neg hn'.le, ← Real.rpow_neg hn'.le]
        have : (n : ℝ) ^ (-(3 / 2 : ℝ)) = (n : ℝ) * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
          rw [show (-(3 / 2 : ℝ)) = 1 + (-(5 / 2 : ℝ)) by norm_num, Real.rpow_add hn', Real.rpow_one]
        rw [this]; ring

/-! ## The mean square of a truncation -/

theorem sum_range_succ_primeAmp_sq (x : ℝ) (N : ℕ) :
    ∑ m : Fin N, ‖(primeAmp x ((m : ℕ) + 1) : ℂ)‖ ^ 2
      = ∑ n ∈ Finset.range (N + 1), primeAmp x n ^ 2 := by
  rw [Finset.sum_range_succ', Fin.sum_univ_eq_sum_range (fun m => ‖(primeAmp x (m + 1) : ℂ)‖ ^ 2) N]
  simp only [primeAmp_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem sum_range_succ_mul_primeAmp_sq (x : ℝ) (N : ℕ) :
    ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖(primeAmp x ((m : ℕ) + 1) : ℂ)‖ ^ 2
      = ∑ n ∈ Finset.range (N + 1), (n : ℝ) * primeAmp x n ^ 2 := by
  rw [Finset.sum_range_succ', Fin.sum_univ_eq_sum_range
    (fun m => (((m : ℕ) : ℝ) + 1) * ‖(primeAmp x (m + 1) : ℂ)‖ ^ 2) N]
  simp only [primeAmp_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Nat.cast_add, Nat.cast_one, Nat.cast_zero]

/-- The sharp mean value theorem for the truncation `P_{N+1}`. -/
theorem integral_normSq_primePhasePartial_sub_le (x : ℝ) (N : ℕ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖primePhasePartial x (N + 1) t‖ ^ 2)
        - T * ∑ n ∈ Finset.range (N + 1), primeAmp x n ^ 2|
      ≤ 104 * ∑ n ∈ Finset.range (N + 1), (n : ℝ) * primeAmp x n ^ 2 := by
  have h := Sieve.dirichlet_meanValue_sharp N (fun m : Fin N => (primeAmp x ((m : ℕ) + 1) : ℂ)) T
  rw [sum_range_succ_primeAmp_sq, sum_range_succ_mul_primeAmp_sq] at h
  simp_rw [primePhasePartial_succ_eq_dirPoly]
  exact h

/-! ## Comparison of the full series with its truncations -/

/-- `|∫_0^T |P|² − ∫_0^T |P_N|²| ≤ T τ_N (2 S₀ + τ_N)`. -/
theorem abs_integral_normSq_sub_partial_le {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    |(∫ t in (0 : ℝ)..T, ‖primePhaseSum x t‖ ^ 2)
        - ∫ t in (0 : ℝ)..T, ‖primePhasePartial x N t‖ ^ 2|
      ≤ T * (primeAmpTail x N * (2 * primeAmpTotal x + primeAmpTail x N)) := by
  have hcont : Continuous (fun t : ℝ => ‖primePhaseSum x t‖ ^ 2) :=
    (continuous_primePhaseSum hx).norm.pow 2
  have hcontN : Continuous (fun t : ℝ => ‖primePhasePartial x N t‖ ^ 2) := by
    unfold primePhasePartial
    exact (continuous_finsetSum _ fun n _ => by fun_prop).norm.pow 2
  rw [← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) (hcontN.intervalIntegrable _ _)]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) T,
      ‖‖primePhaseSum x t‖ ^ 2 - ‖primePhasePartial x N t‖ ^ 2‖
        ≤ primeAmpTail x N * (2 * primeAmpTotal x + primeAmpTail x N) := by
    intro t _
    rw [Real.norm_eq_abs]
    have hkey := abs_normSq_add_sub_normSq_le (primePhasePartial x N t)
      (primePhaseSum x t - primePhasePartial x N t)
    rw [add_sub_cancel] at hkey
    refine hkey.trans ?_
    have h1 := norm_primePhaseSum_sub_partial_le hx N t
    have h2 := norm_primePhasePartial_le hx N t
    have h0 := norm_nonneg (primePhaseSum x t - primePhasePartial x N t)
    have h0' := norm_nonneg (primePhasePartial x N t)
    exact mul_le_mul h1 (by linarith) (by positivity) (primeAmpTail_nonneg (by linarith) N)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at this
  linarith

/-! ## The limit -/

/-- **The mean square of the prime-side Dirichlet series.**  For `x ≥ 1`, `T ≥ 0`,
`|∫_0^T ‖Σ_n d_n e^{it log n}‖² dt − T Σ_n d_n²| ≤ 104 Σ_n n d_n²`. -/
theorem integral_normSq_primePhaseSum_sub_le {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0 : ℝ)..T, ‖primePhaseSum x t‖ ^ 2) - T * ∑' n : ℕ, primeAmp x n ^ 2|
      ≤ 104 * ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  -- the bound at level `N`
  have hstep : ∀ N : ℕ,
      |(∫ t in (0 : ℝ)..T, ‖primePhaseSum x t‖ ^ 2)
          - T * ∑ n ∈ Finset.range (N + 1), primeAmp x n ^ 2|
        ≤ T * (primeAmpTail x (N + 1) * (2 * primeAmpTotal x + primeAmpTail x (N + 1)))
          + 104 * ∑ n ∈ Finset.range (N + 1), (n : ℝ) * primeAmp x n ^ 2 := by
    intro N
    have h1 := abs_integral_normSq_sub_partial_le hx hT (N + 1)
    have h2 := integral_normSq_primePhasePartial_sub_le x N T
    calc |(∫ t in (0 : ℝ)..T, ‖primePhaseSum x t‖ ^ 2)
          - T * ∑ n ∈ Finset.range (N + 1), primeAmp x n ^ 2|
        ≤ |(∫ t in (0 : ℝ)..T, ‖primePhaseSum x t‖ ^ 2)
            - ∫ t in (0 : ℝ)..T, ‖primePhasePartial x (N + 1) t‖ ^ 2|
          + |(∫ t in (0 : ℝ)..T, ‖primePhasePartial x (N + 1) t‖ ^ 2)
            - T * ∑ n ∈ Finset.range (N + 1), primeAmp x n ^ 2| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2
  -- the limits of the two sides
  have hsq := summable_primeAmp_sq hx
  have hnsq := summable_mul_primeAmp_sq hx
  have hL : Tendsto (fun N : ℕ => |(∫ t in (0 : ℝ)..T, ‖primePhaseSum x t‖ ^ 2)
      - T * ∑ n ∈ Finset.range (N + 1), primeAmp x n ^ 2|) atTop
      (nhds |(∫ t in (0 : ℝ)..T, ‖primePhaseSum x t‖ ^ 2) - T * ∑' n : ℕ, primeAmp x n ^ 2|) := by
    refine Filter.Tendsto.abs ?_
    refine tendsto_const_nhds.sub (tendsto_const_nhds.mul ?_)
    exact hsq.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hR : Tendsto (fun N : ℕ =>
      T * (primeAmpTail x (N + 1) * (2 * primeAmpTotal x + primeAmpTail x (N + 1)))
        + 104 * ∑ n ∈ Finset.range (N + 1), (n : ℝ) * primeAmp x n ^ 2) atTop
      (nhds (T * (0 * (2 * primeAmpTotal x + 0)) + 104 * ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2)) := by
    have hτ : Tendsto (fun N : ℕ => primeAmpTail x (N + 1)) atTop (nhds 0) :=
      (tendsto_primeAmpTail x).comp (Filter.tendsto_add_atTop_nat 1)
    refine Filter.Tendsto.add (tendsto_const_nhds.mul (hτ.mul (tendsto_const_nhds.add hτ)))
      (tendsto_const_nhds.mul ?_)
    exact hnsq.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have := le_of_tendsto_of_tendsto' hL hR hstep
  simpa using this

/-- **The mean square of the prime side of Montgomery's lemma.** -/
theorem integral_normSq_primeSide_sub_le {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0 : ℝ)..T, ‖primeSide x t‖ ^ 2) - T * ∑' n : ℕ, primeAmp x n ^ 2|
      ≤ 104 * ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2 := by
  have : (fun t : ℝ => ‖primeSide x t‖ ^ 2) = fun t => ‖primePhaseSum x t‖ ^ 2 := by
    funext t; rw [norm_primeSide_eq hx]
  rw [this]
  exact integral_normSq_primePhaseSum_sub_le hx hT

end RHTower
