import GaloisForLFunctions.HTGeometry.CanonicalEulerLog

/-!
# Riemann's prime-power counting function and its Laplace transform

`Π(x) = Σ_{n ≤ x} Λ(n)/log n = Σ_{p^k ≤ x} 1/k`.  In the logarithmic variable,
`Π(e^t) = Σ_n a_n 1[log n ≤ t]` with `a_n = Λ(n)/log n ∈ [0, 1]`, so for real `σ > 1`

```text
∫_0^∞ Π(e^t) e^{-σt} dt = Σ_n a_n n^{-σ} / σ = log ζ(σ) / σ,
```

the canonical Euler logarithm of `ζ` (`canonicalEulerLogZeta`), whose exponential is `ζ(σ)`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The coefficient `Λ(n)/log n`. -/
def eulerLogCoeffReal (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.log n

theorem eulerLogCoeffReal_nonneg (n : ℕ) : 0 ≤ eulerLogCoeffReal n := by
  unfold eulerLogCoeffReal
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg (by exact_mod_cast hn))

theorem eulerLogCoeffReal_le_one (n : ℕ) : eulerLogCoeffReal n ≤ 1 := by
  unfold eulerLogCoeffReal
  rcases n with _ | _ | n
  · simp
  · simp [ArithmeticFunction.vonMangoldt_apply_one]
  · have h : 0 < Real.log ((n + 2 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
    rw [div_le_one h]; exact ArithmeticFunction.vonMangoldt_le_log

theorem eulerLogDirichletCoeff_eq_ofReal_eulerLogCoeffReal (n : ℕ) :
    eulerLogDirichletCoeff n = (eulerLogCoeffReal n : ℂ) := by
  unfold eulerLogDirichletCoeff eulerLogCoeffReal
  rw [← Complex.natCast_log]
  push_cast
  rfl

/-- Riemann's prime-power counting function `Π(x) = Σ_{n ≤ x} Λ(n)/log n`. -/
def primePowerCount (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, eulerLogCoeffReal n

theorem primePowerCount_nonneg (x : ℝ) : 0 ≤ primePowerCount x :=
  Finset.sum_nonneg fun n _ => eulerLogCoeffReal_nonneg n

theorem primePowerCount_le (x : ℝ) : primePowerCount x ≤ ⌊x⌋₊ := by
  unfold primePowerCount
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, eulerLogCoeffReal n ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => eulerLogCoeffReal_le_one n
    _ = ⌊x⌋₊ := by simp

theorem primePowerCount_mono : Monotone primePowerCount := by
  intro x y hxy
  unfold primePowerCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hxy))
    (fun n _ _ => eulerLogCoeffReal_nonneg n)

/-- `Π(e^t)` as a series of indicators. -/
theorem primePowerCount_exp_eq_tsum (t : ℝ) :
    primePowerCount (Real.exp t)
      = ∑' n : ℕ, eulerLogCoeffReal n * (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t := by
  classical
  unfold primePowerCount
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp t⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hle : (n : ℝ) ≤ Real.exp t := le_trans (by exact_mod_cast hn.2)
      (Nat.floor_le (Real.exp_pos t).le)
    have hlog : Real.log n ≤ t := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact hle
    rw [Set.indicator_of_mem (show t ∈ Ici (Real.log n) from hlog), mul_one]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    rcases hn with h | h
    · have : n = 0 := by omega
      subst this
      simp [eulerLogCoeffReal]
    · have hn1 : 1 ≤ n := by
        by_contra h1
        have : n = 0 := by omega
        subst this; simp at h
      have hgt : Real.exp t < n := by
        by_contra hle
        exact h (Nat.le_floor (le_of_not_gt hle))
      have hlog : t < Real.log n := by
        rw [Real.lt_log_iff_exp_lt (by exact_mod_cast hn1)]; exact hgt
      rw [Set.indicator_of_notMem (show t ∉ Ici (Real.log n) from fun h' => by
        simp only [Set.mem_Ici] at h'; linarith), mul_zero]

/-- The Laplace transform of one indicator. -/
theorem integral_Ioi_indicator_log_mul_exp {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in Ioi (0 : ℝ), (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t * Real.exp (-σ * t)
      = (n : ℝ) ^ (-σ) / σ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have heq : ∀ t, (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t * Real.exp (-σ * t)
      = (Ici (Real.log n)).indicator (fun t => Real.exp (-σ * t)) t := by
    intro t
    by_cases ht : t ∈ Ici (Real.log n)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, one_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  simp_rw [heq]
  rw [setIntegral_indicator measurableSet_Ici]
  have hpow : (n : ℝ) ^ (-σ) = Real.exp (-σ * Real.log n) := by
    rw [Real.rpow_def_of_pos hn0]; ring_nf
  rw [hpow]
  rcases eq_or_lt_of_le hlog0 with h0 | hpos
  · have hset : Ioi (0 : ℝ) ∩ Ici (Real.log n) = Ioi (Real.log n) := by
      rw [← h0]; exact Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self
    rw [hset, integral_exp_mul_Ioi (by linarith)]
    field_simp
  · have hset : Ioi (0 : ℝ) ∩ Ici (Real.log n) = Ici (Real.log n) :=
      Set.inter_eq_right.mpr (fun t ht => lt_of_lt_of_le hpos ht)
    rw [hset, integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith)]
    field_simp

/-- **The Laplace transform of `Π(e^t)`.**  For real `σ > 1`,
`∫_0^∞ Π(e^t) e^{-σt} dt = (Σ_n a_n n^{-σ})/σ`. -/
theorem integral_primePowerCount_exp_mul {σ : ℝ} (hσ : 1 < σ) :
    ∫ t in Ioi (0 : ℝ), primePowerCount (Real.exp t) * Real.exp (-σ * t)
      = (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) / σ := by
  have hσ0 : 0 < σ := by linarith
  set F : ℕ → ℝ → ℝ := fun n t =>
    eulerLogCoeffReal n * ((Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t * Real.exp (-σ * t))
    with hF
  have hpt : ∀ t, primePowerCount (Real.exp t) * Real.exp (-σ * t) = ∑' n, F n t := by
    intro t
    rw [primePowerCount_exp_eq_tsum, ← tsum_mul_right]
    congr 1; funext n; rw [hF]; ring
  have hFint : ∀ n, ∫ t in Ioi (0 : ℝ), F n t = eulerLogCoeffReal n * ((n : ℝ) ^ (-σ) / σ) := by
    intro n
    rw [hF, integral_const_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [eulerLogCoeffReal]
    · rw [integral_Ioi_indicator_log_mul_exp hσ0 hn]
  have hFnn : ∀ n t, 0 ≤ F n t := by
    intro n t; rw [hF]
    exact mul_nonneg (eulerLogCoeffReal_nonneg n) (mul_nonneg
      (Set.indicator_nonneg (fun _ _ => zero_le_one) t) (Real.exp_pos _).le)
  have hFintegrable : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have hexp : IntegrableOn (fun t => Real.exp (-σ * t)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine (hexp.const_mul (eulerLogCoeffReal n)).mono' ?_ ?_
    · rw [hF]
      exact (measurable_const.mul ((measurable_const.indicator measurableSet_Ici).mul
        (Real.measurable_exp.comp (measurable_const.mul measurable_id)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n t), hF]
      have h1 : (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t ≤ 1 := by
        by_cases ht : t ∈ Ici (Real.log n)
        · rw [Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht]; norm_num
      have h2 := eulerLogCoeffReal_nonneg n
      have h3 := Real.exp_pos (-σ * t)
      have h5 : (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t * Real.exp (-σ * t)
          ≤ Real.exp (-σ * t) := by
        have := mul_le_mul_of_nonneg_right h1 h3.le
        linarith
      exact mul_le_mul_of_nonneg_left h5 h2
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    have heq : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ = eulerLogCoeffReal n * ((n : ℝ) ^ (-σ) / σ) := by
      intro n
      rw [← hFint n]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n t)]
    simp_rw [heq]
    have hrp : Summable fun n : ℕ => (n : ℝ) ^ (-σ) := by
      have := Real.summable_nat_rpow_inv.mpr hσ
      refine this.congr fun n => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (eulerLogCoeffReal_nonneg n)
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hσ0.le)) (fun n => ?_)
      (hrp.div_const σ)
    have h1 := eulerLogCoeffReal_le_one n
    have h2 : 0 ≤ (n : ℝ) ^ (-σ) / σ := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hσ0.le
    nlinarith [eulerLogCoeffReal_nonneg n]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t),
    ← integral_tsum_of_summable_integral_norm hFintegrable hsum]
  simp_rw [hFint]
  rw [← tsum_div_const]
  congr 1; funext n; ring

/-- The canonical Euler logarithm on the real axis is the real coefficient series. -/
theorem canonicalEulerLogZeta_ofReal_eq_tsum (σ : ℝ) :
    canonicalEulerLogZeta σ = ((∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  unfold canonicalEulerLogZeta LSeries
  rw [Complex.ofReal_tsum]
  congr 1; funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero, eulerLogCoeffReal]
  · rw [LSeries.term_of_ne_zero hn.ne', eulerLogDirichletCoeff_eq_ofReal_eulerLogCoeffReal]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hn0.le, div_eq_mul_inv]
    congr 1
    push_cast
    rw [Complex.cpow_neg]

/-- `log ζ(σ) = Σ_n a_n n^{-σ}` for real `σ > 1`. -/
theorem log_riemannZeta_ofReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    Real.exp (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) = (riemannZeta σ).re ∧
      (riemannZeta σ).im = 0 := by
  have h := exp_canonicalEulerLogZeta_eq_riemannZeta (s := (σ : ℂ)) (by simpa using hσ)
  rw [canonicalEulerLogZeta_ofReal_eq_tsum σ, ← Complex.ofReal_exp] at h
  rw [← h]
  exact ⟨(Complex.ofReal_re _).symm, Complex.ofReal_im _⟩

end

end RHTower
