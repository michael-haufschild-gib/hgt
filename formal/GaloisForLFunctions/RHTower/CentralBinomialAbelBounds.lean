import GaloisForLFunctions.RHTower.LegendreConvolution

/-!
# Central-binomial bounds and Abel summation against a unimodular geometric sequence

Elementary inputs of the Laplace–Heine asymptotics: `C_k² ≤ 1/(2k+1)`, `C` is antitone with
`Σ_{k<K} C_k ≤ 2√(2K+1)`; Abel summation gives `‖Σ_{i<n} f_i η^i‖ ≤ (2/‖1−η‖)(|f_{n−1}| + Var f)` for
`‖η‖ = 1`, `η ≠ 1`; Dirichlet's bound for antitone `f`; and by Abel's limit theorem the boundary
series `Σ C_k η^k` converges (conditionally) to `(1 − η)^{−1/2}`, with tail `≤ 2 C_K/‖1 − η‖`.
-/

open Finset Filter Topology Complex
open scoped BigOperators

namespace RHTower

namespace LegendreBoost

open RouteJProfile

/-! ## Central-binomial bounds -/

theorem cb_sq_le (k : ℕ) : cb k ^ 2 ≤ 1 / (2 * (k : ℝ) + 1) := by
  induction k with
  | zero => simp [cb_zero]
  | succ k ih =>
      rw [cb_succ, mul_div_assoc, mul_pow, div_pow]
      have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
      push_cast
      calc cb k ^ 2 * ((2 * (k : ℝ) + 1) ^ 2 / (2 * ((k : ℝ) + 1)) ^ 2)
          ≤ (1 / (2 * (k : ℝ) + 1)) * ((2 * (k : ℝ) + 1) ^ 2 / (2 * ((k : ℝ) + 1)) ^ 2) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = (2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1)) ^ 2 := by field_simp
        _ ≤ 1 / (2 * ((k : ℝ) + 1) + 1) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith

theorem cb_le_inv_sqrt (k : ℕ) : cb k ≤ 1 / Real.sqrt (2 * (k : ℝ) + 1) := by
  have h := cb_sq_le k
  have hpos := cb_pos k
  rw [one_div, ← Real.sqrt_inv, ← one_div]
  rw [Real.le_sqrt hpos.le (by positivity)]
  exact h

theorem cb_antitone : Antitone cb := by
  apply antitone_nat_of_succ_le
  intro k
  rw [cb_succ, mul_div_assoc]
  have h := cb_pos k
  calc cb k * ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ≤ cb k * 1 := by
        apply mul_le_mul_of_nonneg_left _ h.le
        rw [div_le_one (by positivity)]
        linarith
    _ = cb k := mul_one _

theorem cb_tendsto_zero : Tendsto cb atTop (𝓝 0) := by
  have hupper : Tendsto (fun k : ℕ => 1 / Real.sqrt (2 * (k : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 2 * (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have h2 : Tendsto (fun k : ℕ => Real.sqrt (2 * (k : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp h1
    refine h2.inv_tendsto_atTop.congr' (Eventually.of_forall fun k => ?_)
    simp [one_div]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun k => (cb_pos k).le) (fun k => cb_le_inv_sqrt k)

theorem cb_sum_inv_sqrt_le (K : ℕ) :
    ∑ k ∈ range K, 1 / Real.sqrt (2 * (k : ℝ) + 1) ≤ 2 * Real.sqrt (2 * (K : ℝ) + 1) - 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [sum_range_succ]
      have hstep : 1 / Real.sqrt (2 * (K : ℝ) + 1) ≤
          2 * Real.sqrt (2 * ((K + 1 : ℕ) : ℝ) + 1) - 2 * Real.sqrt (2 * (K : ℝ) + 1) := by
        push_cast
        have ha : 0 < Real.sqrt (2 * (K : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        have hb : 0 < Real.sqrt (2 * ((K : ℝ) + 1) + 1) := Real.sqrt_pos.mpr (by positivity)
        have hsq : Real.sqrt (2 * ((K : ℝ) + 1) + 1) ^ 2 - Real.sqrt (2 * (K : ℝ) + 1) ^ 2 = 2 := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; ring
        have hle : Real.sqrt (2 * (K : ℝ) + 1) ≤ Real.sqrt (2 * ((K : ℝ) + 1) + 1) :=
          Real.sqrt_le_sqrt (by linarith)
        -- 2(b − a) = 2(b² − a²)/(b + a) = 4/(b+a) ≥ 4/(2b) = 2/b ≥ 1/a  since 4a² ≥ b²
        have h4 : Real.sqrt (2 * ((K : ℝ) + 1) + 1) ^ 2 ≤ 4 * Real.sqrt (2 * (K : ℝ) + 1) ^ 2 := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; linarith
        rw [div_le_iff₀ ha]
        nlinarith [hsq, h4, hle, ha, hb]
      linarith

theorem sum_cb_le (K : ℕ) : ∑ k ∈ range K, cb k ≤ 2 * Real.sqrt (2 * (K : ℝ) + 1) := by
  calc ∑ k ∈ range K, cb k ≤ ∑ k ∈ range K, 1 / Real.sqrt (2 * (k : ℝ) + 1) :=
        sum_le_sum fun k _ => cb_le_inv_sqrt k
    _ ≤ 2 * Real.sqrt (2 * (K : ℝ) + 1) - 2 := cb_sum_inv_sqrt_le K
    _ ≤ 2 * Real.sqrt (2 * (K : ℝ) + 1) := by linarith

/-! ## Abel summation against a unimodular geometric sequence -/

theorem norm_unimodular_geom_sum_le {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) (n : ℕ) :
    ‖∑ i ∈ range n, η ^ i‖ ≤ 2 / ‖1 - η‖ := by
  rw [geom_sum_eq h1, norm_div, norm_sub_rev η 1]
  have hpos : 0 < ‖1 - η‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h1))
  rw [div_le_div_iff_of_pos_right hpos]
  calc ‖η ^ n - 1‖ ≤ ‖η ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hη, one_pow, norm_one]; norm_num

/-- **Abel's bound.** -/
theorem norm_sum_mul_pow_le_abel {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) (f : ℕ → ℝ) (n : ℕ) :
    ‖∑ i ∈ range n, (f i : ℂ) * η ^ i‖ ≤
      2 / ‖1 - η‖ * (|f (n - 1)| + ∑ i ∈ range (n - 1), |f (i + 1) - f i|) := by
  have hparts := Finset.sum_range_by_parts (fun i => (f i : ℂ)) (fun i => η ^ i) n
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have hG : ∀ m, ‖∑ i ∈ range m, η ^ i‖ ≤ 2 / ‖1 - η‖ := norm_unimodular_geom_sum_le hη h1
  have hpos : 0 ≤ 2 / ‖1 - η‖ := by positivity
  calc ‖(f (n - 1) : ℂ) * ∑ i ∈ range n, η ^ i -
        ∑ i ∈ range (n - 1), ((f (i + 1) : ℂ) - f i) * ∑ j ∈ range (i + 1), η ^ j‖
      ≤ ‖(f (n - 1) : ℂ) * ∑ i ∈ range n, η ^ i‖ +
        ‖∑ i ∈ range (n - 1), ((f (i + 1) : ℂ) - f i) * ∑ j ∈ range (i + 1), η ^ j‖ := norm_sub_le _ _
    _ ≤ |f (n - 1)| * (2 / ‖1 - η‖) +
        ∑ i ∈ range (n - 1), |f (i + 1) - f i| * (2 / ‖1 - η‖) := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hG n) (abs_nonneg _)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
          rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hG (i + 1)) (abs_nonneg _)
    _ = 2 / ‖1 - η‖ * (|f (n - 1)| + ∑ i ∈ range (n - 1), |f (i + 1) - f i|) := by
        rw [← sum_mul]; ring

/-- **Dirichlet's bound** for antitone nonnegative coefficients. -/
theorem norm_sum_mul_pow_le_dirichlet {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) {f : ℕ → ℝ}
    (hf : Antitone f) (hf0 : ∀ i, 0 ≤ f i) (n : ℕ) :
    ‖∑ i ∈ range n, (f i : ℂ) * η ^ i‖ ≤ 2 / ‖1 - η‖ * f 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [range_zero, sum_empty, norm_zero]
    exact mul_nonneg (by positivity) (hf0 0)
  have h := norm_sum_mul_pow_le_abel hη h1 f n
  have hvar : ∑ i ∈ range (n - 1), |f (i + 1) - f i| = f 0 - f (n - 1) := by
    have : ∀ i ∈ range (n - 1), |f (i + 1) - f i| = f i - f (i + 1) := by
      intro i _
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hf (Nat.le_succ i)])]
    rw [sum_congr rfl this, sum_range_sub' (fun i => f i)]
  rw [hvar, abs_of_nonneg (hf0 _)] at h
  calc ‖∑ i ∈ range n, (f i : ℂ) * η ^ i‖ ≤ 2 / ‖1 - η‖ * (f (n - 1) + (f 0 - f (n - 1))) := h
    _ = 2 / ‖1 - η‖ * f 0 := by ring

/-- Dirichlet's bound on a block `Ico a b`. -/
theorem norm_sum_Ico_mul_pow_le_dirichlet {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) {f : ℕ → ℝ}
    (hf : Antitone f) (hf0 : ∀ i, 0 ≤ f i) (a b : ℕ) :
    ‖∑ i ∈ Ico a b, (f i : ℂ) * η ^ i‖ ≤ 2 / ‖1 - η‖ * f a := by
  rw [sum_Ico_eq_sum_range]
  have : (∑ k ∈ range (b - a), (f (a + k) : ℂ) * η ^ (a + k)) =
      η ^ a * ∑ k ∈ range (b - a), (f (a + k) : ℂ) * η ^ k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [pow_add]; ring
  rw [this, norm_mul, norm_pow, hη, one_pow, one_mul]
  have h := norm_sum_mul_pow_le_dirichlet hη h1 (f := fun k => f (a + k))
    (fun i j hij => hf (by omega)) (fun i => hf0 _) (b - a)
  simpa using h

/-! ## The boundary central-binomial series -/

theorem cauchySeq_cb_partial {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) :
    CauchySeq (fun n => ∑ i ∈ range n, (cb i : ℂ) * η ^ i) := by
  have h := cb_antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded cb_tendsto_zero
    (b := 2 / ‖1 - η‖) (z := fun i => η ^ i) (fun n => norm_unimodular_geom_sum_le hη h1 n)
  simpa [smul_eq_mul, Complex.real_smul] using h

/-- Along the real radius the series is the binomial series. -/
theorem tsum_cb_mul_pow_real {η : ℂ} (hη : ‖η‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' k : ℕ, (cb k : ℂ) * η ^ k * (r : ℂ) ^ k = (1 - (r : ℂ) * η) ^ (-(1 / 2 : ℂ)) := by
  have hu : ‖(r : ℂ) * η‖ < 1 := by
    rw [norm_mul, hη, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h := hasSum_cb_mul_pow hu
  rw [← h.tsum_eq]
  congr 1
  funext k
  rw [mul_pow]; ring

/-- **Abel's limit theorem for the boundary series:**
`Σ_{k<n} C_k η^k → (1 − η)^{-1/2}` for `‖η‖ = 1`, `η ≠ 1`. -/
theorem tendsto_cb_partial_boundary {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) :
    Tendsto (fun n => ∑ i ∈ range n, (cb i : ℂ) * η ^ i) atTop (𝓝 ((1 - η) ^ (-(1 / 2 : ℂ)))) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_cb_partial hη h1)
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt (f := fun i => (cb i : ℂ) * η ^ i) hL
  -- along real r → 1⁻ the sum is (1 − rη)^{-1/2}, which tends to (1 − η)^{-1/2}
  have hre : 0 < (1 - η).re := by
    have := abs_re_le_norm η
    rw [hη] at this
    simp only [sub_re, one_re]
    rcases (abs_le.mp this).2.lt_or_eq with h | h
    · linarith
    · exfalso
      apply h1
      have him : η.im = 0 := by
        have := Complex.sq_norm η
        rw [hη, Complex.normSq_apply, h] at this
        have h0 : η.im * η.im = 0 := by linarith
        exact mul_self_eq_zero.mp h0
      apply Complex.ext <;> simp [h, him]
  have hslit : 1 - η ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hre)
  have hcont : Tendsto (fun r : ℝ => (1 - (r : ℂ) * η) ^ (-(1 / 2 : ℂ)))
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 ((1 - η) ^ (-(1 / 2 : ℂ)))) := by
    have hd : HasDerivAt (fun z : ℂ => 1 - z * η) (-η) 1 := by
      simpa using ((hasDerivAt_id (1 : ℂ)).mul_const η).const_sub 1
    have hc : ContinuousAt (fun z : ℂ => (1 - z * η) ^ (-(1 / 2 : ℂ))) 1 :=
      (hd.cpow_const (by simpa using hslit)).continuousAt
    have h1' : Tendsto (fun r : ℝ => (r : ℂ)) (nhdsWithin 1 (Set.Iio 1)) (𝓝 (1 : ℂ)) := by
      have := (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto
      rw [Complex.ofReal_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := hc.tendsto.comp h1'
    simp only [Function.comp_def, one_mul] at this
    exact this
  -- identify the limits
  have hmap : Tendsto (fun r : ℝ => ∑' n : ℕ, (cb n : ℂ) * η ^ n * (r : ℂ) ^ n)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) := by
    have := habel
    rw [Filter.tendsto_map'_iff] at this
    exact this
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio 1),
      ∑' n : ℕ, (cb n : ℂ) * η ^ n * (r : ℂ) ^ n = (1 - (r : ℂ) * η) ^ (-(1 / 2 : ℂ)) := by
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
      first
        | exact Ioo_mem_nhdsLT (by norm_num)
        | exact Ioo_mem_nhdsWithin_Iio (by simp)
    filter_upwards [hmem] with r hr
    exact tsum_cb_mul_pow_real hη hr.1.le hr.2
  have hlim := hmap.congr' heq
  have : L = (1 - η) ^ (-(1 / 2 : ℂ)) :=
    tendsto_nhds_unique hlim hcont
  rw [this] at hL
  exact hL

/-- The tail of the boundary series: `‖(1 − η)^{-1/2} − Σ_{i<K} C_i η^i‖ ≤ 2 C_K / ‖1 − η‖`. -/
theorem norm_boundary_tail_le {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) (K : ℕ) :
    ‖(1 - η) ^ (-(1 / 2 : ℂ)) - ∑ i ∈ range K, (cb i : ℂ) * η ^ i‖ ≤ 2 / ‖1 - η‖ * cb K := by
  have hlim := tendsto_cb_partial_boundary hη h1
  have hdiff : Tendsto (fun n => ∑ i ∈ range n, (cb i : ℂ) * η ^ i - ∑ i ∈ range K, (cb i : ℂ) * η ^ i)
      atTop (𝓝 ((1 - η) ^ (-(1 / 2 : ℂ)) - ∑ i ∈ range K, (cb i : ℂ) * η ^ i)) :=
    hlim.sub_const _
  refine le_of_tendsto (tendsto_norm.comp hdiff) ?_
  filter_upwards [eventually_ge_atTop K] with n hn
  simp only [Function.comp]
  rw [← sum_Ico_eq_sub _ hn]
  exact norm_sum_Ico_mul_pow_le_dirichlet hη h1 cb_antitone (fun i => (cb_pos i).le) K n

end LegendreBoost

end RHTower
