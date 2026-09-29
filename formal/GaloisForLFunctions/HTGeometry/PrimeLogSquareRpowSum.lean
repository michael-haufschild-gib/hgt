import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation

/-!
# The asymptotic of `∑_{p ≤ x} p^{a-1} log² p`

For `0 < a < 1` the prime number theorem in Chebyshev form gives

`∑_{p ≤ x} p^{a-1} log² p ~ x^a log x / a`.

Abel summation against `θ` with the weight `f(t) = t^{a-1} log t` gives `f(x)θ(x) - ∫_2^x f'θ`.
Writing `θ(t) = t(1 + g(t))` with `g → 0`, the kernel `t f'(t) = t^{a-1}((a-1) log t + 1)` has the
explicit primitive `t^a((a-1)/a · log t + 1/a²)`, so the main terms combine to
`x^a log x / a - x^a/a² + O(1)`; the `g`-weighted remainder is `o(x^a log x)` because the kernel is
dominated by `t^{a-1} log t`.
-/

open Filter Topology Set MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Abel weight `t^{a-1} log t`. -/
def logRpowWeight (a t : ℝ) : ℝ := t ^ (a - 1) * Real.log t

/-- Its derivative `t^{a-2}((a-1) log t + 1)`. -/
def derivLogRpowWeight (a t : ℝ) : ℝ := t ^ (a - 2) * ((a - 1) * Real.log t + 1)

theorem hasDerivAt_logRpowWeight {a t : ℝ} (ht : 0 < t) :
    HasDerivAt (logRpowWeight a) (derivLogRpowWeight a t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ (a - 1)) ((a - 1) * t ^ (a - 1 - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h := h1.mul h2
  have hpow : t ^ (a - 1) = t ^ (a - 2) * t := by
    rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add_one ht.ne']
  have h' : (a - 1) * t ^ (a - 1 - 1) * Real.log t + t ^ (a - 1) * t⁻¹
      = derivLogRpowWeight a t := by
    rw [derivLogRpowWeight, hpow, show a - 1 - 1 = a - 2 by ring]
    field_simp
  rw [← h']
  exact h

theorem continuousAt_derivLogRpowWeight {a t : ℝ} (ht : 0 < t) :
    ContinuousAt (derivLogRpowWeight a) t :=
  (Real.continuousAt_rpow_const t (a - 2) (Or.inl ht.ne')).mul
    ((continuousAt_const.mul (Real.continuousAt_log ht.ne')).add continuousAt_const)

theorem integrableOn_deriv_logRpowWeight {a x : ℝ} :
    IntegrableOn (deriv (logRpowWeight a)) (Icc 2 x) := by
  have hcont : ContinuousOn (derivLogRpowWeight a) (Icc 2 x) := fun t ht =>
    (continuousAt_derivLogRpowWeight (a := a) (by linarith [ht.1])).continuousWithinAt
  refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
  exact ((hasDerivAt_logRpowWeight (a := a) (by linarith [ht.1])).deriv).symm

/-- The prime sum `∑_{p ≤ x} p^{a-1} log² p`. -/
def primeLogSqRpowSum (a x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, ((p : ℝ)) ^ (a - 1) * Real.log (p : ℝ) ^ 2

theorem logRpowWeight_mul_primeLogWeight (a : ℝ) (k : ℕ) :
    logRpowWeight a (k : ℝ) * RHTower.primeLogWeight_primeRpowAbelSummation k
      = if k.Prime then ((k : ℝ)) ^ (a - 1) * Real.log (k : ℝ) ^ 2 else 0 := by
  rw [RHTower.primeLogWeight_primeRpowAbelSummation, logRpowWeight]
  split_ifs <;> ring

/-- **Abel's identity.**  `∑_{p ≤ x} p^{a-1} log² p = f(x)θ(x) - ∫_2^x f'θ`. -/
theorem primeLogSqRpowSum_eq {a x : ℝ} (hx : 2 ≤ x) :
    primeLogSqRpowSum a x = logRpowWeight a x * Chebyshev.theta x
      - ∫ t in Ioc (2 : ℝ) x, deriv (logRpowWeight a) t * Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ)
    RHTower.primeLogWeight_primeRpowAbelSummation (f := logRpowWeight a)
    (a := (2 : ℝ)) (b := x) (by norm_num) hx
    (fun t ht => (hasDerivAt_logRpowWeight (a := a) (by linarith [ht.1])).differentiableAt)
    integrableOn_deriv_logRpowWeight
  simp only [RHTower.sum_primeLogWeight_eq_theta] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  have hθ2 : Chebyshev.theta 2 = Real.log 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Chebyshev.theta_eq_sum_primesLE_log]
    rw [show Nat.primesLE 2 = {2} by decide]
    simp
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hsum : primeLogSqRpowSum a x
      = logRpowWeight a 2 * Real.log 2 + ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊,
          logRpowWeight a (k : ℝ) * RHTower.primeLogWeight_primeRpowAbelSummation k := by
    rw [primeLogSqRpowSum, Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
    simp_rw [logRpowWeight_mul_primeLogWeight]
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _),
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 2) hN]
    have h02 : Finset.Ioc 0 2 = {1, 2} := by decide
    rw [h02]
    simp [logRpowWeight, Nat.prime_two, Nat.not_prime_one]
    ring
  rw [hsum, habel, hθ2]
  ring

/-- The explicit primitive of the Abel kernel `t f'(t)`. -/
def logRpowKernelPrimitive (a t : ℝ) : ℝ := t ^ a * ((a - 1) / a * Real.log t + 1 / a ^ 2)

theorem integral_mul_deriv_logRpowWeight {a x : ℝ} (ha : 0 < a) (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, t * derivLogRpowWeight a t
      = logRpowKernelPrimitive a x - logRpowKernelPrimitive a 2 := by
  refine integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
  · have ht2 : 2 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact h.1
      · linarith [h.1, h.2]
    have ht0 : 0 < t := by linarith
    have h1 : HasDerivAt (fun s : ℝ => s ^ a) (a * t ^ (a - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have h2 : HasDerivAt (fun s : ℝ => (a - 1) / a * Real.log s + 1 / a ^ 2)
        ((a - 1) / a * t⁻¹) t := by
      have := ((Real.hasDerivAt_log ht0.ne').const_mul ((a - 1) / a)).add_const (1 / a ^ 2)
      simpa using this
    have h := h1.mul h2
    have hpow1 : t ^ a = t ^ (a - 1) * t := by
      rw [show a = (a - 1) + 1 by ring, Real.rpow_add_one ht0.ne']
      ring_nf
    have hpow2 : t ^ (a - 1) = t ^ (a - 2) * t := by
      rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add_one ht0.ne']
    have key : t * derivLogRpowWeight a t
        = a * t ^ (a - 1) * ((a - 1) / a * Real.log t + 1 / a ^ 2)
          + t ^ a * ((a - 1) / a * t⁻¹) := by
      rw [derivLogRpowWeight, hpow1, hpow2]
      field_simp
      ring
    rw [key]
    exact h
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have ht2 : 2 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact h.1
      · linarith [h.1, h.2]
    exact (continuousAt_id.mul
      (continuousAt_derivLogRpowWeight (a := a) (by linarith))).continuousWithinAt

/-- The `g`-weighted remainder is `o(x^a log x)` for a kernel dominated by `t^{a-1} log t`. -/
theorem tendsto_logMulKernelRemainder {a : ℝ} (ha0 : 0 < a) {C : ℝ} (hC0 : 0 ≤ C)
    {g K : ℝ → ℝ} (hgt : Tendsto g atTop (𝓝 0))
    (hKbd : ∀ t : ℝ, 2 ≤ t → |K t| ≤ C * (t ^ (a - 1) * Real.log t))
    (hgint : ∀ x : ℝ, 2 ≤ x → IntervalIntegrable (fun t : ℝ => g t * K t) volume 2 x) :
    Tendsto (fun x : ℝ => (∫ t in (2 : ℝ)..x, g t * K t) / (x ^ a * Real.log x)) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε * a / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hgt δ hδ0)
  set T : ℝ := max T₀ 2 with hTdef
  have hT2 : 2 ≤ T := le_max_right _ _
  set H : ℝ := |∫ t in (2 : ℝ)..T, g t * K t| with hHdef
  have hden : Tendsto (fun x : ℝ => x ^ a * Real.log x) atTop atTop :=
    (tendsto_rpow_atTop ha0).atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hsmall : ∀ᶠ x : ℝ in atTop, H / (x ^ a * Real.log x) < ε / 2 := by
    have h := hden.inv_tendsto_atTop.const_mul H
    rw [mul_zero] at h
    filter_upwards [h.eventually (gt_mem_nhds (half_pos hε))] with x hx
    simpa [div_eq_mul_inv] using hx
  filter_upwards [hsmall, eventually_ge_atTop T, eventually_gt_atTop (1 : ℝ)] with x hxs hxT hx1
  have hx2 : 2 ≤ x := le_trans hT2 hxT
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hden0 : 0 < x ^ a * Real.log x := mul_pos (Real.rpow_pos_of_pos hx0 a) hlogx
  have hsplit : ∫ t in (2 : ℝ)..x, g t * K t
      = (∫ t in (2 : ℝ)..T, g t * K t) + ∫ t in T..x, g t * K t :=
    (integral_add_adjacent_intervals (hgint T hT2)
      ((hgint x hx2).mono_set (by
        rw [uIcc_of_le hx2, uIcc_of_le hxT]
        exact Icc_subset_Icc hT2 le_rfl))).symm
  have htail : |∫ t in T..x, g t * K t| ≤ δ * C * (Real.log x * (x ^ a / a)) := by
    have hbound : ∀ t ∈ Icc T x, ‖g t * K t‖ ≤ δ * C * Real.log x * t ^ (a - 1) := by
      intro t ht
      have ht2 : 2 ≤ t := le_trans hT2 ht.1
      have ht0 : 0 < t := by linarith
      have hgtd : |g t| ≤ δ := by
        have := hT₀ t (le_trans (le_max_left _ _) ht.1)
        rw [Real.dist_eq, sub_zero] at this
        exact this.le
      have hlogt : Real.log t ≤ Real.log x := Real.log_le_log ht0 ht.2
      have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      have hp : 0 ≤ t ^ (a - 1) := Real.rpow_nonneg ht0.le _
      rw [Real.norm_eq_abs, abs_mul]
      calc |g t| * |K t| ≤ δ * (C * (t ^ (a - 1) * Real.log t)) :=
            mul_le_mul hgtd (hKbd t ht2) (abs_nonneg _) hδ0.le
        _ ≤ δ * (C * (t ^ (a - 1) * Real.log x)) := by gcongr
        _ = δ * C * Real.log x * t ^ (a - 1) := by ring
    have hle := norm_integral_le_of_norm_le hxT (Eventually.of_forall fun t ht =>
      hbound t (Ioc_subset_Icc_self ht))
      ((_root_.HTGeometry.intervalIntegrable_rpowSubOne a hT2 hx2).const_mul
        (δ * C * Real.log x))
    rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, _root_.HTGeometry.integral_rpow_sub_one ha0]
    have hTa : 0 ≤ T ^ a := Real.rpow_nonneg (by linarith) a
    have hc : 0 ≤ δ * C * Real.log x := by positivity
    have : (x ^ a - T ^ a) / a ≤ x ^ a / a := by
      apply div_le_div_of_nonneg_right _ ha0.le
      linarith
    calc δ * C * Real.log x * ((x ^ a - T ^ a) / a) ≤ δ * C * Real.log x * (x ^ a / a) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hden0, hsplit]
  have htri := abs_add_le (∫ t in (2 : ℝ)..T, g t * K t) (∫ t in T..x, g t * K t)
  have hfrac : δ * C * (Real.log x * (x ^ a / a)) / (x ^ a * Real.log x) ≤ ε / 2 := by
    have heq : δ * C * (Real.log x * (x ^ a / a)) / (x ^ a * Real.log x) = δ * C / a := by
      field_simp
    rw [heq, hδ]
    rw [div_le_iff₀ ha0]
    have hC1 : 0 < C + 1 := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc |(∫ t in (2 : ℝ)..T, g t * K t) + ∫ t in T..x, g t * K t| / (x ^ a * Real.log x)
      ≤ (H + δ * C * (Real.log x * (x ^ a / a))) / (x ^ a * Real.log x) := by
        apply div_le_div_of_nonneg_right _ hden0.le
        linarith
    _ = H / (x ^ a * Real.log x)
        + δ * C * (Real.log x * (x ^ a / a)) / (x ^ a * Real.log x) := by rw [add_div]
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- The Abel kernel `t f'(t)` is dominated by `(|a-1| + 1/log 2) t^{a-1} log t`. -/
theorem abs_mul_derivLogRpowWeight_le {a t : ℝ} (ht : 2 ≤ t) :
    |t * derivLogRpowWeight a t|
      ≤ (|a - 1| + 1 / Real.log 2) * (t ^ (a - 1) * Real.log t) := by
  have ht0 : 0 < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlogt0 : 0 < Real.log t := by linarith
  have hpow : t * t ^ (a - 2) = t ^ (a - 1) := by
    rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add_one ht0.ne']
    ring
  have hp : 0 < t ^ (a - 1) := Real.rpow_pos_of_pos ht0 _
  rw [derivLogRpowWeight, ← mul_assoc, hpow, abs_mul, abs_of_pos hp]
  have h1 : |(a - 1) * Real.log t + 1| ≤ |a - 1| * Real.log t + 1 := by
    calc |(a - 1) * Real.log t + 1| ≤ |(a - 1) * Real.log t| + |1| := abs_add_le _ _
      _ = |a - 1| * Real.log t + 1 := by rw [abs_mul, abs_of_pos hlogt0, abs_one]
  have h2 : (1 : ℝ) ≤ Real.log t / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
  calc t ^ (a - 1) * |(a - 1) * Real.log t + 1|
      ≤ t ^ (a - 1) * (|a - 1| * Real.log t + Real.log t / Real.log 2) := by
        gcongr
        linarith
    _ = (|a - 1| + 1 / Real.log 2) * (t ^ (a - 1) * Real.log t) := by
        field_simp

/-- **`∑_{p ≤ x} p^{a-1} log² p ~ x^a log x / a`** for `0 < a < 1`. -/
theorem tendsto_primeLogSqRpowSum {a : ℝ} (ha0 : 0 < a) :
    Tendsto (fun x : ℝ => primeLogSqRpowSum a x * a / (x ^ a * Real.log x)) atTop (𝓝 1) := by
  obtain ⟨g, hg, g_int, hθ⟩ := chebyshev_asymptotic''
  have hgt : Tendsto g atTop (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp (hg 1 one_pos)
  set K : ℝ → ℝ := fun t => t * derivLogRpowWeight a t with hKdef
  have hKcont : ∀ t : ℝ, 2 ≤ t → ContinuousAt K t := fun t ht =>
    continuousAt_id.mul (continuousAt_derivLogRpowWeight (a := a) (by linarith))
  have hgint : ∀ x : ℝ, 2 ≤ x → IntervalIntegrable (fun t : ℝ => g t * K t) volume 2 x := by
    intro x hx
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact ((g_int x hx).mul_continuousOn (fun t ht => (hKcont t ht.1).continuousWithinAt)
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hR := tendsto_logMulKernelRemainder ha0
    (C := |a - 1| + 1 / Real.log 2) (by positivity) hgt
    (fun t ht => abs_mul_derivLogRpowWeight_le ht) hgint
  have hden : Tendsto (fun x : ℝ => x ^ a * Real.log x) atTop atTop :=
    (tendsto_rpow_atTop ha0).atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hinvden := hden.inv_tendsto_atTop
  have hinvlog := Real.tendsto_log_atTop.inv_tendsto_atTop
  have hlim : Tendsto (fun x : ℝ => 1 + a * g x - (1 / a) * (Real.log x)⁻¹
      + a * logRpowKernelPrimitive a 2 * (x ^ a * Real.log x)⁻¹
      - a * ((∫ t in (2 : ℝ)..x, g t * K t) / (x ^ a * Real.log x))) atTop (𝓝 1) := by
    have h := ((((tendsto_const_nhds (x := (1 : ℝ))).add (hgt.const_mul a)).sub
      (hinvlog.const_mul (1 / a))).add (hinvden.const_mul (a * logRpowKernelPrimitive a 2))).sub
      (hR.const_mul a)
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hint : ∫ t in Ioc (2 : ℝ) x, deriv (logRpowWeight a) t * Chebyshev.theta t
      = (logRpowKernelPrimitive a x - logRpowKernelPrimitive a 2)
        + ∫ t in (2 : ℝ)..x, g t * K t := by
    rw [← intervalIntegral.integral_of_le hx, ← integral_mul_deriv_logRpowWeight ha0 hx,
      ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun t ht => ?_
      have ht2 : 2 ≤ t := by
        rcases Set.mem_uIcc.mp ht with h | h
        · exact h.1
        · linarith [h.1, h.2]
      have ht0 : 0 < t := by linarith
      simp only [hKdef]
      rw [(hasDerivAt_logRpowWeight (a := a) ht0).deriv, hθ t ht0]
      ring
    · refine ContinuousOn.intervalIntegrable fun t ht => ?_
      have ht2 : 2 ≤ t := by
        rcases Set.mem_uIcc.mp ht with h | h
        · exact h.1
        · linarith [h.1, h.2]
      exact (hKcont t ht2).continuousWithinAt
    · exact hgint x hx
  have hxpow : x ^ (a - 1) * x = x ^ a := by
    rw [show a = (a - 1) + 1 by ring, Real.rpow_add_one hx0.ne']
    ring_nf
  rw [primeLogSqRpowSum_eq hx, hint, hθ x hx0]
  simp only [logRpowWeight, logRpowKernelPrimitive]
  rw [← hxpow]
  have hxa' : 0 < x ^ (a - 1) := Real.rpow_pos_of_pos hx0 _
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
