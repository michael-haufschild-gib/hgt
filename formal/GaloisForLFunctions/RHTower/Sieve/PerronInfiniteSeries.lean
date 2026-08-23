import GaloisForLFunctions.RHTower.Sieve.PerronFiniteSum

/-!
# The truncated Perron formula for an infinite Dirichlet series

The finite Perron formula is a per-term statement: each term contributes
`c_n · perronVertical σ T (x/n)`, and the error is the sum of the individual Perron defects.  Nothing
in that decomposition needs the index set to be finite, so as soon as `∑ ‖c_n‖(x/n)^σ` converges the
series may be summed inside the vertical integral and the same bound holds with `tsum` throughout.
This is the form a contour shift consumes, because the integrand is then the full Dirichlet series
rather than a polynomial.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

/-- The `n`-th Perron term. -/
def perronTerm (c : ℕ → ℂ) (x σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  c n * ((((x / n : ℝ)) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))

theorem norm_perronTerm_le {c : ℕ → ℂ} {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (n : ℕ) (t : ℝ) :
    ‖perronTerm c x σ n t‖ ≤ ‖c n‖ * (x / n) ^ σ / σ := by
  have hden : ‖((σ : ℂ) + (t : ℝ) * I)‖ ≥ σ := by
    have h := Complex.abs_re_le_norm ((σ : ℂ) + (t : ℝ) * I)
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    rw [hre] at h
    exact le_trans (le_abs_self σ) h
  have hdenpos : (0 : ℝ) < ‖((σ : ℂ) + (t : ℝ) * I)‖ := lt_of_lt_of_le hσ hden
  have hsne : ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := by
    intro h
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : (x / ((0 : ℕ) : ℝ)) = 0 := by simp
    rw [perronTerm, hzero]
    simp only [Complex.ofReal_zero, Complex.zero_cpow hsne, zero_div, mul_zero, norm_zero]
    have hz : ((0 : ℝ)) ^ σ = 0 := Real.zero_rpow hσ.ne'
    rw [hz]
    simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hxn : (0 : ℝ) < x / n := div_pos hx hn0
    rw [perronTerm, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxn]
    have hre : (((σ : ℂ) + (t : ℝ) * I)).re = σ := by simp
    rw [hre]
    have hxσ : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg hxn.le σ
    rw [mul_div_assoc]
    gcongr

theorem continuous_perronTerm' {c : ℕ → ℂ} (hc0 : c 0 = 0) {x : ℝ} (hx : 0 < x) {σ : ℝ}
    (hσ : 0 < σ) (n : ℕ) : Continuous (perronTerm c x σ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hfun : perronTerm c x σ 0 = fun _ : ℝ => (0 : ℂ) := by
      funext t
      rw [perronTerm, hc0, zero_mul]
    rw [hfun]
    exact continuous_const
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact continuous_perronTerm (div_pos hx hn0) hσ (c n)

/-- **The truncated Perron formula for an infinite series: the integral.** -/
theorem perron_tsum_integral_eq {c : ℕ → ℂ} (hc0 : c 0 = 0) {x : ℝ} (hx : 0 < x)
    {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hconv : Summable (fun n : ℕ => ‖c n‖ * (x / n) ^ σ)) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        (∑' n : ℕ, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
      = ∑' n : ℕ, c n * perronVertical σ T (x / n) := by
  classical
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hcont : ∀ n : ℕ, Continuous (perronTerm c x σ n) := continuous_perronTerm' hc0 hx hσ
  have hintg : ∀ n : ℕ, Integrable (perronTerm c x σ n) (volume.restrict (Set.Ioc (-T) T)) :=
    fun n => (hcont n).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hnormsum : Summable
      (fun n : ℕ => ∫ t in Set.Ioc (-T) T, ‖perronTerm c x σ n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hconv.mul_left (2 * T / σ))
    have hle : ∀ t : ℝ, ‖perronTerm c x σ n t‖ ≤ ‖c n‖ * (x / n) ^ σ / σ :=
      fun t => norm_perronTerm_le hx hσ n t
    have hb : ∫ t in Set.Ioc (-T) T, ‖perronTerm c x σ n t‖
        ≤ ∫ _t in Set.Ioc (-T) T, ‖c n‖ * (x / n) ^ σ / σ := by
      refine MeasureTheory.setIntegral_mono_on ((hcont n).norm.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self) ?_ measurableSet_Ioc (fun t _ => hle t)
      exact (continuous_const.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    refine hb.trans (le_of_eq ?_)
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    field_simp
    ring
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm hintg hnormsum
  have hpt : ∀ t : ℝ,
      (∑' n : ℕ, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = ∑' n : ℕ, perronTerm c x σ n t := by
    intro t
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [perronTerm, hc0, zero_mul, zero_mul, zero_mul]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [perronTerm, ofReal_div_cpow_eq_mul_cpow_neg hx hn0]
      push_cast
      ring
  rw [intervalIntegral.integral_congr (g := fun t => ∑' n : ℕ, perronTerm c x σ n t)
    (fun t _ => hpt t), intervalIntegral.integral_of_le hTle, ← hsum.tsum_eq]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hint : ∫ t in Set.Ioc (-T) T, perronTerm c x σ n t = ∫ t in (-T)..T, perronTerm c x σ n t :=
    (intervalIntegral.integral_of_le hTle).symm
  rw [hint]
  exact integral_perronTerm_eq (c n)

/-- **The truncated Perron formula for an infinite Dirichlet series.** -/
theorem norm_tsum_lt_sub_perron_integral_le {c : ℕ → ℂ} (hc0 : c 0 = 0) {x : ℝ} (hx : 0 < x)
    (hne : ∀ n : ℕ, (n : ℝ) ≠ x) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hconv : Summable (fun n : ℕ => ‖c n‖ * (x / n) ^ σ))
    (hdef : Summable
      (fun n : ℕ => ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)))) :
    ‖(∑' n : ℕ, (if (n : ℝ) < x then c n else 0))
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            (∑' n : ℕ, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ ∑' n : ℕ, ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [perron_tsum_integral_eq hc0 hx hσ hT hconv]
  set g : ℕ → ℂ := fun n =>
    (if (n : ℝ) < x then c n else 0) - c n * perronVertical σ T (x / n) with hg
  have hgB : ∀ n : ℕ, ‖g n‖
      ≤ ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hlt : ((0 : ℕ) : ℝ) < x := by simpa using hx
      rw [hg]
      simp only [if_pos hlt, hc0, zero_mul, sub_zero, norm_zero]
      positivity
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hxn : (0 : ℝ) < x / n := div_pos hx hn0
      by_cases hlt : (n : ℝ) < x
      · have hy1 : 1 < x / n := (one_lt_div hn0).2 hlt
        have hlogpos : (0 : ℝ) < Real.log (x / n) := Real.log_pos hy1
        rw [hg]
        simp only [if_pos hlt]
        have hstep : ‖c n - c n * perronVertical σ T (x / n)‖
            = ‖c n‖ * ‖perronVertical σ T (x / n) - 1‖ := by
          rw [show c n - c n * perronVertical σ T (x / n)
              = -(c n * (perronVertical σ T (x / n) - 1)) by ring, norm_neg, norm_mul]
        rw [hstep, abs_of_pos hlogpos]
        exact mul_le_mul_of_nonneg_left (norm_perronVertical_sub_one_le hy1 hσ hT)
          (norm_nonneg _)
      · have hgt : x < (n : ℝ) := lt_of_le_of_ne (not_lt.1 hlt) (fun h => hne n h.symm)
        have hy1 : x / n < 1 := (div_lt_one hn0).2 hgt
        rw [hg]
        simp only [if_neg hlt, zero_sub, norm_neg, norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_perronVertical_le hxn hy1 hσ hT) (norm_nonneg _)
  have hgsum : Summable g := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgB hdef)
  have hifsum : Summable (fun n : ℕ => (if (n : ℝ) < x then c n else 0)) := by
    refine summable_of_hasFiniteSupport ?_
    refine Set.Finite.subset (Set.finite_Icc 0 ⌈x⌉₊) ?_
    intro n hn
    simp only [Function.mem_support] at hn
    by_cases hlt : (n : ℝ) < x
    · simp only [Set.mem_Icc]
      refine ⟨Nat.zero_le n, ?_⟩
      have : (n : ℝ) ≤ (⌈x⌉₊ : ℝ) := le_trans hlt.le (Nat.le_ceil x)
      exact_mod_cast this
    · exact absurd (if_neg hlt) hn
  have hpvsum : Summable (fun n : ℕ => c n * perronVertical σ T (x / n)) := by
    have : (fun n : ℕ => c n * perronVertical σ T (x / n))
        = fun n : ℕ => (if (n : ℝ) < x then c n else 0) - g n := by
      funext n
      rw [hg]
      ring
    rw [this]
    exact hifsum.sub hgsum
  rw [← hifsum.tsum_sub hpvsum]
  refine le_trans (norm_tsum_le_tsum_norm
    (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgB hdef)) ?_
  exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgB hdef).tsum_le_tsum hgB hdef

end

end RHTower.Sieve
