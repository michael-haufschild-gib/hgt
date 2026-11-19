import GaloisForLFunctions.RHTower.PrimeGapDirichletContinuation

/-!
# The gap-weighted prime series is `o(|t|)` on the critical line

Let `θ < ½` be an admissible gap-moment exponent and `D` the continuation of
`Σ_k g_k p_k^{-s}`. Then `|D(½ + it)| = o(|t|)` (`tendsto_norm_gapDirichletCont_critical_div`),
so `|D(½ + it)|` is not of exact order `|t|`: no bound `c|t| ≤ |D(½ + it)|` with `c > 0` holds for
all large `|t|` (`not_exists_linear_lower_bound_gapDirichletCont`).

Proof. `D = 1/(s − 1) + (2^{1−s} − 1)/(s − 1) + Σ_k r_k(s)`; the first two terms are bounded on the
line. Each `r_k(s) = g_k p_k^{−s} − (p_k^{1−s} − p_{k+1}^{1−s})/(s − 1)` is bounded on the line, so
`r_k(s)/s → 0`; and `|r_k(s)/s| ≤ g_k² p_k^{−3/2}` is summable for `θ < ½`. Tannery's theorem gives
`Σ_k r_k(s)/s → 0`.
-/

open Complex Filter Topology

namespace RHTower.PrimeGapDirichlet

noncomputable section

theorem tendsto_abs_cocompact : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop :=
  (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun t => Real.norm_eq_abs t

/-- The critical-line point `½ + it`. -/
def criticalPoint (t : ℝ) : ℂ := 1 / 2 + t * I

theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by simp [criticalPoint]

theorem criticalPoint_im (t : ℝ) : (criticalPoint t).im = t := by simp [criticalPoint]

theorem abs_le_norm_criticalPoint (t : ℝ) : |t| ≤ ‖criticalPoint t‖ := by
  have := Complex.abs_im_le_norm (criticalPoint t)
  rwa [criticalPoint_im] at this

theorem half_le_norm_criticalPoint (t : ℝ) : 1 / 2 ≤ ‖criticalPoint t‖ := by
  have := Complex.abs_re_le_norm (criticalPoint t)
  rwa [criticalPoint_re, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this

theorem criticalPoint_ne_zero (t : ℝ) : criticalPoint t ≠ 0 := fun h => by
  have := half_le_norm_criticalPoint t
  rw [h, norm_zero] at this
  norm_num at this

theorem criticalPoint_ne_one (t : ℝ) : criticalPoint t ≠ 1 := fun h => by
  have := criticalPoint_re t
  rw [h, Complex.one_re] at this
  norm_num at this

theorem half_le_norm_criticalPoint_sub_one (t : ℝ) : 1 / 2 ≤ ‖criticalPoint t - 1‖ := by
  have hr : (criticalPoint t - 1).re = -(1 / 2) := by
    rw [Complex.sub_re, criticalPoint_re, Complex.one_re]; norm_num
  have := Complex.abs_re_le_norm (criticalPoint t - 1)
  rwa [hr, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this

theorem norm_natCast_cpow_criticalPoint {n : ℕ} (hn : 0 < n) (t : ℝ) (c : ℂ) :
    ‖(n : ℂ) ^ (c - criticalPoint t)‖ = (n : ℝ) ^ (c.re - 1 / 2) := by
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.sub_re, criticalPoint_re]

/-- Each remainder is bounded on the critical line, uniformly in `t`. -/
theorem norm_gapRemainder_critical_le (k : ℕ) (t : ℝ) :
    ‖gapRemainder k (criticalPoint t)‖ ≤
      (gap k : ℝ) + 2 * ((prime k : ℝ) ^ (1 / 2 : ℝ) + (prime (k + 1) : ℝ) ^ (1 / 2 : ℝ)) := by
  set s := criticalPoint t
  have hpk := (prime_prime k).pos
  have hpk1 := (prime_prime (k + 1)).pos
  have hterm : ‖gapTerm k s‖ ≤ gap k := by
    rw [gapTerm, norm_mul, Complex.norm_natCast,
      show -s = (0 : ℂ) - s by ring, norm_natCast_cpow_criticalPoint hpk]
    have : (prime k : ℝ) ^ ((0 : ℂ).re - 1 / 2) ≤ 1 := by
      rw [Complex.zero_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_prime_real k) (by norm_num)
    nlinarith [(Nat.cast_nonneg (gap k) : (0 : ℝ) ≤ gap k)]
  have hcell : ‖gapCell k s‖ ≤
      2 * ((prime k : ℝ) ^ (1 / 2 : ℝ) + (prime (k + 1) : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [gapCell_of_ne (criticalPoint_ne_one t), norm_div]
    have hden := half_le_norm_criticalPoint_sub_one t
    rw [div_le_iff₀ (by linarith)]
    have h1 : ‖(prime k : ℂ) ^ (1 - s)‖ = (prime k : ℝ) ^ (1 / 2 : ℝ) := by
      rw [norm_natCast_cpow_criticalPoint hpk, Complex.one_re]; norm_num
    have h2 : ‖(prime (k + 1) : ℂ) ^ (1 - s)‖ = (prime (k + 1) : ℝ) ^ (1 / 2 : ℝ) := by
      rw [norm_natCast_cpow_criticalPoint hpk1, Complex.one_re]; norm_num
    have hnn : 0 ≤ (prime k : ℝ) ^ (1 / 2 : ℝ) + (prime (k + 1) : ℝ) ^ (1 / 2 : ℝ) := by positivity
    calc ‖(prime k : ℂ) ^ (1 - s) - (prime (k + 1) : ℂ) ^ (1 - s)‖
        ≤ ‖(prime k : ℂ) ^ (1 - s)‖ + ‖(prime (k + 1) : ℂ) ^ (1 - s)‖ := norm_sub_le _ _
      _ = (prime k : ℝ) ^ (1 / 2 : ℝ) + (prime (k + 1) : ℝ) ^ (1 / 2 : ℝ) := by rw [h1, h2]
      _ ≤ 2 * ((prime k : ℝ) ^ (1 / 2 : ℝ) + (prime (k + 1) : ℝ) ^ (1 / 2 : ℝ)) *
            ‖s - 1‖ := by nlinarith
  calc ‖gapRemainder k s‖ ≤ ‖gapTerm k s‖ + ‖gapCell k s‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hterm hcell

/-- The normalized remainder `r_k(½ + it)/(½ + it)`. -/
def criticalRemainderRatio (k : ℕ) (t : ℝ) : ℂ := gapRemainder k (criticalPoint t) / criticalPoint t

/-- The normalized remainders are dominated by `g_k² p_k^{−3/2}`. -/
theorem norm_criticalRemainderRatio_le (k : ℕ) (t : ℝ) :
    ‖criticalRemainderRatio k t‖ ≤ ((gap k : ℝ)) ^ 2 * (prime k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hs := half_le_norm_criticalPoint t
  have hb := norm_gapRemainder_le k (s := criticalPoint t) (by rw [criticalPoint_re]; norm_num)
  rw [criticalPoint_re, show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num] at hb
  rw [criticalRemainderRatio, norm_div, div_le_iff₀ (by linarith)]
  linarith [hb]

/-- Each normalized remainder tends to zero as `|t| → ∞`. -/
theorem tendsto_criticalRemainderRatio (k : ℕ) :
    Tendsto (criticalRemainderRatio k) (cocompact ℝ) (𝓝 0) := by
  set C : ℝ := (gap k : ℝ) + 2 * ((prime k : ℝ) ^ (1 / 2 : ℝ) + (prime (k + 1) : ℝ) ^ (1 / 2 : ℝ))
  have hC : 0 ≤ C := by positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hinv : Tendsto (fun t : ℝ => C * |t|⁻¹) (cocompact ℝ) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
      exact tendsto_abs_cocompact
    simpa using (tendsto_inv_atTop_zero.comp h1).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hinv
  have hev : ∀ᶠ t : ℝ in cocompact ℝ, 1 ≤ |t| := by
    have h1 : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
      exact tendsto_abs_cocompact
    exact h1.eventually (eventually_ge_atTop 1)
  filter_upwards [hev] with t ht
  have ha := abs_le_norm_criticalPoint t
  have hpos : 0 < |t| := by linarith
  rw [criticalRemainderRatio, norm_div, div_le_iff₀ (by linarith)]
  calc ‖gapRemainder k (criticalPoint t)‖ ≤ C := norm_gapRemainder_critical_le k t
    _ = C * |t|⁻¹ * |t| := by field_simp
    _ ≤ C * |t|⁻¹ * ‖criticalPoint t‖ :=
        mul_le_mul_of_nonneg_left ha (by positivity)

/-- **The gap-weighted series is `o(|t|)` on the critical line** for admissible `θ < ½`. -/
theorem tendsto_norm_gapDirichletCont_critical_div {θ : ℝ} (h : GapMomentBound θ)
    (hθ : θ < 1 / 2) :
    Tendsto (fun t : ℝ => ‖gapDirichletCont (criticalPoint t)‖ / (1 + |t|)) (cocompact ℝ)
      (𝓝 0) := by
  have hsum := summable_gap_sq_mul_rpow h (τ := 3 / 2) (by linarith)
  -- the regular part, divided by `s`, tends to zero
  have hreg : Tendsto (fun t : ℝ => ∑' k, criticalRemainderRatio k t) (cocompact ℝ) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := cocompact ℝ) hsum
      (fun k => tendsto_criticalRemainderRatio k)
      (Eventually.of_forall fun t k => norm_criticalRemainderRatio_le k t)
    simpa using this
  have hreg' : Tendsto (fun t : ℝ => ‖∑' k, criticalRemainderRatio k t‖) (cocompact ℝ) (𝓝 0) := by
    simpa using hreg.norm
  have hinv : Tendsto (fun t : ℝ => 8 / (1 + |t|)) (cocompact ℝ) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + |t|) (cocompact ℝ) atTop := by
      have : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
        exact tendsto_abs_cocompact
      exact tendsto_atTop_add_const_left _ 1 this
    have h2 := h1.inv_tendsto_atTop.const_mul 8
    rw [mul_zero] at h2
    exact h2.congr fun t => (div_eq_mul_inv 8 _).symm
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) (by simpa using hinv.add hreg')
  set s := criticalPoint t
  have hne := criticalPoint_ne_one t
  have hs0 := criticalPoint_ne_zero t
  have hs1 := half_le_norm_criticalPoint_sub_one t
  have hs1pos : 0 < ‖s - 1‖ := by linarith
  have hA : ‖1 / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ hs1pos]; linarith
  have hB : ‖gapPolar s‖ ≤ 6 := by
    rw [gapPolar, dslope_of_ne _ hne, slope_def_field, sub_self, Complex.cpow_zero, norm_div,
      div_le_iff₀ hs1pos]
    have h2 : ‖(2 : ℂ) ^ (1 - s)‖ ≤ 2 := by
      have e : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
      rw [e, norm_natCast_cpow_criticalPoint (by norm_num), Complex.one_re]
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (2 : ℕ))
        (by norm_num : (1 : ℝ) - 1 / 2 ≤ 1)
      rwa [Real.rpow_one] at this
    calc ‖(2 : ℂ) ^ (1 - s) - 1‖ ≤ ‖(2 : ℂ) ^ (1 - s)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 6 * ‖s - 1‖ := by rw [norm_one]; linarith
  have hsr : gapRegular s = s * ∑' k, criticalRemainderRatio k t := by
    rw [gapRegular, ← tsum_mul_left]
    congr 1
    funext k
    rw [criticalRemainderRatio, mul_div_cancel₀ _ hs0]
  have hnorm : ‖s‖ ≤ 1 + |t| := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [criticalPoint_re, criticalPoint_im, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    linarith
  have hpos : 0 < 1 + |t| := by positivity
  rw [div_le_iff₀ hpos]
  calc ‖gapDirichletCont s‖ ≤ ‖1 / (s - 1)‖ + (‖gapPolar s‖ + ‖gapRegular s‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ 8 + ‖s‖ * ‖∑' k, criticalRemainderRatio k t‖ := by
        rw [hsr, norm_mul]; linarith
    _ ≤ 8 + (1 + |t|) * ‖∑' k, criticalRemainderRatio k t‖ := by
        nlinarith [norm_nonneg (∑' k, criticalRemainderRatio k t)]
    _ = (8 / (1 + |t|) + ‖∑' k, criticalRemainderRatio k t‖) * (1 + |t|) := by
        field_simp

/-- **No linear lower bound**: for admissible `θ < ½` there is no `c > 0` with
`c|t| ≤ |D(½ + it)|` for all large `|t|`. -/
theorem not_exists_linear_lower_bound_gapDirichletCont {θ : ℝ} (h : GapMomentBound θ)
    (hθ : θ < 1 / 2) :
    ¬ ∃ c T : ℝ, 0 < c ∧ ∀ t : ℝ, T ≤ |t| → c * |t| ≤ ‖gapDirichletCont (criticalPoint t)‖ := by
  rintro ⟨c, T, hc, hb⟩
  have ht := tendsto_norm_gapDirichletCont_critical_div h hθ
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < c / 2 by positivity))
  have habs : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
    exact tendsto_abs_cocompact
  obtain ⟨t, ht1, ht2⟩ := (hev.and (habs.eventually (eventually_ge_atTop (max T 1)))).exists
  have hT : T ≤ |t| := (le_max_left _ _).trans ht2
  have h1 : 1 ≤ |t| := (le_max_right _ _).trans ht2
  have hl := hb t hT
  have hpos : 0 < 1 + |t| := by positivity
  rw [div_lt_iff₀ hpos] at ht1
  nlinarith

end

end RHTower.PrimeGapDirichlet
