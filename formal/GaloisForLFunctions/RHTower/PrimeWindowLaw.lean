import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

/-!
# The prime window law

For `a > 0` and `j : ℕ` the prime measure sees the logarithmic window variable
`v = log Y - log p` with the exponential density `e^{-av} dv`:

```text
Y^(-a) ∑_{2 < p ≤ Y} p^(a-1) (log Y - log p)^j log p  →  ∫_0^∞ e^{-av} v^j dv = j!/a^(j+1).
```

Abel summation against the Chebyshev function turns the sum into the window power integrals
`J_{j+1}` and `J_j`, whose normalized limits are `(j+1)!/a^(j+2)` and `j!/a^(j+1)`; the
combination `-(a-1)(j+1)!/a^(j+2) + (j+1)·j!/a^(j+1)` collapses to `(j+1)!/a^(j+2)`.  The error
weighted by `θ(t)/t - 1` vanishes after normalization because the window integrals are uniformly
`O(Y^a)` while the head below any fixed height is `O((log Y)^j)`.
-/

open Filter Topology Set MeasureTheory intervalIntegral Asymptotics

namespace RHTower

noncomputable section

/-! ## The error-weighted window integral -/

/-- The window integral weighted by the relative prime number theorem error. -/
def thetaErrorWindowIntegral (a : ℝ) (j : ℕ) (Y : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..Y, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)

theorem intervalIntegrable_thetaError_window (a : ℝ) (j : ℕ) (Y : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ => thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine ((integrableOn_thetaError x).mul_continuousOn ?_ isCompact_Icc).mono_set
    Ioc_subset_Icc_self
  have h := HTGeometry.continuousOn_windowIntegrand a j Y (le_refl (2 : ℝ)) hx
  rwa [uIcc_of_le hx] at h

/-- **The window remainder vanishes.**  The head below a fixed height is `O((log Y)^j)` and the
tail is `δ` times the uniformly bounded window integral. -/
theorem tendsto_thetaErrorWindowIntegral {a : ℝ} (ha0 : 0 < a) (j : ℕ) :
    Tendsto (fun Y : ℝ => thetaErrorWindowIntegral a j Y / Y ^ a) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by
    have := Nat.factorial_pos j
    exact_mod_cast this
  set M : ℝ := (Nat.factorial j : ℝ) / a ^ (j + 1) with hM
  have hM0 : 0 < M := by
    rw [hM]
    positivity
  set δ : ℝ := ε / (2 * M) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  obtain ⟨T₀, hT₀⟩ :=
    eventually_atTop.mp (NormedAddGroup.tendsto_nhds_zero.mp tendsto_thetaError δ hδ0)
  set T : ℝ := max T₀ 2 with hT
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hTg : ∀ t : ℝ, T ≤ t → |thetaError t| ≤ δ := by
    intro t ht
    have h := hT₀ t (le_trans (le_max_left _ _) ht)
    rw [Real.norm_eq_abs] at h
    exact h.le
  -- the head is a fixed multiple of a logarithmic power
  set K : ℝ := (Real.log 4 + 1) * ((T ^ a - (2 : ℝ) ^ a) / a) with hK
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ Real.log 4 + 1 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      linarith
    have h2 : (2 : ℝ) ^ a ≤ T ^ a := Real.rpow_le_rpow (by norm_num) hT2 ha0.le
    have h3 : (0 : ℝ) ≤ (T ^ a - (2 : ℝ) ^ a) / a := by
      apply div_nonneg _ ha0.le
      linarith
    rw [hK]
    exact mul_nonneg h1 h3
  have hheadlim : Tendsto (fun Y : ℝ => K * ((Real.log Y) ^ j / Y ^ a)) atTop (nhds 0) := by
    have h := (HTGeometry.tendsto_logPow_div_rpow ha0 j).const_mul K
    rwa [mul_zero] at h
  have hsmallhead : ∀ᶠ Y : ℝ in atTop, K * ((Real.log Y) ^ j / Y ^ a) < ε / 2 :=
    (NormedAddGroup.tendsto_nhds_zero.mp hheadlim (ε / 2) (by linarith)).mono fun Y hY => by
      rw [Real.norm_eq_abs] at hY
      exact lt_of_le_of_lt (le_abs_self _) hY
  filter_upwards [eventually_ge_atTop T, hsmallhead, eventually_ge_atTop (2 : ℝ)] with
    Y hY hYhead hY2
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
  have hlogY : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY2
  have hlogY0 : (0 : ℝ) ≤ Real.log Y := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  -- pointwise domination of the window integrand
  have hwin_nonneg : ∀ t ∈ Icc (2 : ℝ) Y,
      0 ≤ t ^ (a - 1) * (Real.log Y - Real.log t) ^ j := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have htY : t ≤ Y := ht.2
    have h1 : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ Real.log Y - Real.log t := by
      have := Real.log_le_log (by linarith : (0 : ℝ) < t) htY
      linarith
    exact mul_nonneg h1 (pow_nonneg h2 j)
  have hsplit : thetaErrorWindowIntegral a j Y
      = (∫ t in (2 : ℝ)..T, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))
        + ∫ t in T..Y, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j) := by
    rw [thetaErrorWindowIntegral]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_thetaError_window a j Y hT2)
      ((intervalIntegrable_thetaError_window a j Y hY2).mono_set (by
        rw [uIcc_of_le hY, uIcc_of_le hY2]
        exact Icc_subset_Icc hT2 le_rfl))).symm
  -- head bound
  have hheadbound :
      |∫ t in (2 : ℝ)..T, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|
        ≤ K * (Real.log Y) ^ j := by
    have hTY : T ≤ Y := hY
    have hmajor : IntervalIntegrable
        (fun t : ℝ => (Real.log 4 + 1) * ((Real.log Y) ^ j * t ^ (a - 1))) volume 2 T := by
      refine (IntervalIntegrable.const_mul ?_ _)
      exact (HTGeometry.intervalIntegrable_rpowSubOne a (le_refl (2 : ℝ)) hT2).const_mul _
    have hpt : ∀ t ∈ Icc (2 : ℝ) T,
        |thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|
          ≤ (Real.log 4 + 1) * ((Real.log Y) ^ j * t ^ (a - 1)) := by
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have htY : t ≤ Y := le_trans ht.2 hTY
      have ht0 : (0 : ℝ) < t := by linarith
      have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hw0 : (0 : ℝ) ≤ Real.log Y - Real.log t := by
        have := Real.log_le_log ht0 htY
        linarith
      have hwle : Real.log Y - Real.log t ≤ Real.log Y := by linarith
      have hrp : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg ht0.le _
      have hpow : (Real.log Y - Real.log t) ^ j ≤ (Real.log Y) ^ j :=
        pow_le_pow_left₀ hw0 hwle j
      rw [abs_mul, abs_of_nonneg (mul_nonneg hrp (pow_nonneg hw0 j))]
      calc |thetaError t| * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)
          ≤ (Real.log 4 + 1) * (t ^ (a - 1) * (Real.log Y) ^ j) := by
            apply mul_le_mul (abs_thetaError_le ht2) _ (by positivity) _
            · exact mul_le_mul_of_nonneg_left hpow hrp
            · have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
              linarith
        _ = (Real.log 4 + 1) * ((Real.log Y) ^ j * t ^ (a - 1)) := by ring
    have hint := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t : ℝ => thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))
      (μ := volume) (a := (2 : ℝ)) (b := T) hT2
    have hmono : (∫ t in (2 : ℝ)..T,
        |thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|)
        ≤ ∫ t in (2 : ℝ)..T, (Real.log 4 + 1) * ((Real.log Y) ^ j * t ^ (a - 1)) :=
      intervalIntegral.integral_mono_on hT2
        ((intervalIntegrable_thetaError_window a j Y hT2).abs) hmajor hpt
    have hval : (∫ t in (2 : ℝ)..T, (Real.log 4 + 1) * ((Real.log Y) ^ j * t ^ (a - 1)))
        = K * (Real.log Y) ^ j := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        HTGeometry.integral_rpow_sub_one ha0, hK]
      ring
    rw [hval] at hmono
    exact le_trans hint hmono
  -- tail bound
  have htailbound :
      |∫ t in T..Y, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|
        ≤ δ * (M * Y ^ a) := by
    have hmajor : IntervalIntegrable
        (fun t : ℝ => δ * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)) volume T Y :=
      (HTGeometry.intervalIntegrable_windowIntegrand a j Y hT2 hY2).const_mul _
    have htail : IntervalIntegrable
        (fun t : ℝ => thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)) volume T Y :=
      (intervalIntegrable_thetaError_window a j Y hY2).mono_set (by
        rw [uIcc_of_le hY, uIcc_of_le hY2]
        exact Icc_subset_Icc hT2 le_rfl)
    have hpt : ∀ t ∈ Icc T Y,
        |thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|
          ≤ δ * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j) := by
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := le_trans hT2 ht.1
      have hnn := hwin_nonneg t ⟨ht2, ht.2⟩
      rw [abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right (hTg t ht.1) hnn
    have hint := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t : ℝ => thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))
      (μ := volume) (a := T) (b := Y) hY
    have hmono : (∫ t in T..Y, |thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|)
        ≤ ∫ t in T..Y, δ * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j) :=
      intervalIntegral.integral_mono_on hY htail.abs hmajor hpt
    have hval : (∫ t in T..Y, δ * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))
        ≤ δ * (M * Y ^ a) := by
      rw [intervalIntegral.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ hδ0.le
      have hle : (∫ t in T..Y, t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)
          ≤ HTGeometry.windowRpowIntegral a j Y := by
        have hhead : 0 ≤ ∫ t in (2 : ℝ)..T, t ^ (a - 1) * (Real.log Y - Real.log t) ^ j := by
          refine intervalIntegral.integral_nonneg hT2 fun u hu => ?_
          exact hwin_nonneg u ⟨hu.1, le_trans hu.2 hY⟩
        have hadd := intervalIntegral.integral_add_adjacent_intervals
          (HTGeometry.intervalIntegrable_windowIntegrand a j Y (le_refl (2 : ℝ)) hT2)
          (HTGeometry.intervalIntegrable_windowIntegrand a j Y hT2 hY2)
        rw [HTGeometry.windowRpowIntegral, ← hadd]
        linarith
      exact le_trans hle (HTGeometry.windowRpowIntegral_le ha0 j hY2)
    exact le_trans (le_trans hint hmono) hval
  -- assemble
  have habs : |thetaErrorWindowIntegral a j Y| ≤ K * (Real.log Y) ^ j + δ * (M * Y ^ a) := by
    rw [hsplit]
    calc |(∫ t in (2 : ℝ)..T, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))
            + ∫ t in T..Y, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|
        ≤ |∫ t in (2 : ℝ)..T, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)|
          + |∫ t in T..Y, thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)| :=
          abs_add_le _ _
      _ ≤ K * (Real.log Y) ^ j + δ * (M * Y ^ a) := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hYa]
  have hdiv : |thetaErrorWindowIntegral a j Y| / Y ^ a
      ≤ (K * (Real.log Y) ^ j + δ * (M * Y ^ a)) / Y ^ a := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right habs (inv_nonneg.mpr hYa.le)
  have hexpand : (K * (Real.log Y) ^ j + δ * (M * Y ^ a)) / Y ^ a
      = K * ((Real.log Y) ^ j / Y ^ a) + δ * M := by
    field_simp
  have hδM : δ * M = ε / 2 := by
    rw [hδ]
    field_simp
  rw [hexpand, hδM] at hdiv
  linarith

/-! ## The prime window sum -/

/-- The prime window sum `∑_{2 < p ≤ Y} p^(a-1) (log Y - log p)^j log p`. -/
def primeWindowSum (a : ℝ) (j : ℕ) (Y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
    (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j * Real.log k else 0)

theorem primeWindowSum_zero (a Y : ℝ) : primeWindowSum a 0 Y = primeRpowLogSumIoc a Y := by
  unfold primeWindowSum primeRpowLogSumIoc
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp, pow_zero, mul_one]
  · rw [if_neg hp, if_neg hp]

theorem windowWeight_mul_primeLogWeight {a Y : ℝ} (j : ℕ) (k : ℕ) :
    ((k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j) * primeLogWeight k =
      (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ j * Real.log k
        else 0) := by
  rw [primeLogWeight]
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, mul_zero]

theorem hasDerivAt_windowWeight {a Y : ℝ} (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => u ^ (a - 1) * (Real.log Y - Real.log u) ^ (j + 1))
      ((a - 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ (j + 1)
        - ((j : ℝ) + 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ j) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hbase : HasDerivAt (fun t : ℝ => Real.log Y - Real.log t) (-x⁻¹) x :=
    (Real.hasDerivAt_log hxne).const_sub (Real.log Y)
  have hout : HasDerivAt (fun s : ℝ => s ^ (j + 1))
      (((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j) (Real.log Y - Real.log x) := by
    simpa using hasDerivAt_pow (j + 1) (Real.log Y - Real.log x)
  have hwin : HasDerivAt (fun t : ℝ => (Real.log Y - Real.log t) ^ (j + 1))
      (((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j * (-x⁻¹)) x := by
    simpa [Function.comp_def] using hout.comp x hbase
  have hpow : HasDerivAt (fun t : ℝ => t ^ (a - 1)) ((a - 1) * x ^ (a - 2)) x :=
    hasDerivAt_rpowSubOne hxne
  have h := hpow.mul hwin
  have hval : (a - 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ (j + 1)
      + x ^ (a - 1) * (((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j * (-x⁻¹))
      = (a - 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ (j + 1)
        - ((j : ℝ) + 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ j := by
    have hrp : x ^ (a - 1) * x⁻¹ = x ^ (a - 2) := by
      have hinv : x⁻¹ = x ^ (-1 : ℝ) := by
        rw [Real.rpow_neg hx.le, Real.rpow_one]
      rw [hinv, ← Real.rpow_add hx]
      congr 1
      ring
    calc (a - 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ (j + 1)
        + x ^ (a - 1) * (((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j * (-x⁻¹))
        = (a - 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ (j + 1)
          - ((j : ℝ) + 1) * (x ^ (a - 1) * x⁻¹) * (Real.log Y - Real.log x) ^ j := by ring
      _ = (a - 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ (j + 1)
          - ((j : ℝ) + 1) * x ^ (a - 2) * (Real.log Y - Real.log x) ^ j := by rw [hrp]
  rwa [hval] at h

theorem integrableOn_deriv_windowWeight {a Y : ℝ} (j : ℕ) {x : ℝ} (_hx : 2 ≤ x) :
    IntegrableOn (deriv fun u : ℝ => u ^ (a - 1) * (Real.log Y - Real.log u) ^ (j + 1))
      (Icc 2 x) := by
  have hcont : ContinuousOn
      (fun t : ℝ => (a - 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ (j + 1)
        - ((j : ℝ) + 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ j) (Icc 2 x) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht2
      linarith
    have hrp : ContinuousAt (fun s : ℝ => s ^ (a - 2)) t :=
      Real.continuousAt_rpow_const t (a - 2) (Or.inl ht0)
    have hlog : ContinuousAt (fun s : ℝ => Real.log Y - Real.log s) t :=
      continuousAt_const.sub (Real.continuousAt_log ht0)
    exact (((continuousAt_const.mul hrp).mul (hlog.pow (j + 1))).sub
      ((continuousAt_const.mul hrp).mul (hlog.pow j))).continuousWithinAt
  refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have ht0 : (0 : ℝ) < t := by linarith
  exact ((hasDerivAt_windowWeight (a := a) (Y := Y) j ht0).deriv).symm

/-- **Abel summation of the prime window sum.** -/
theorem primeWindowSum_succ_eq {a Y : ℝ} (j : ℕ) (hY : 2 ≤ Y) :
    primeWindowSum a (j + 1) Y =
      -((2 : ℝ) ^ (a - 1) * (Real.log Y - Real.log 2) ^ (j + 1) * Chebyshev.theta 2)
        - ∫ t in (2 : ℝ)..Y,
            ((a - 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ (j + 1)
              - ((j : ℝ) + 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ j) *
              Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) primeLogWeight
    (f := fun u : ℝ => u ^ (a - 1) * (Real.log Y - Real.log u) ^ (j + 1))
    (a := (2 : ℝ)) (b := Y) (by norm_num) hY
    (fun t ht => (hasDerivAt_windowWeight (a := a) (Y := Y) j (by
      have h2 := ht.1
      linarith)).differentiableAt)
    (integrableOn_deriv_windowWeight j hY)
  simp only [sum_primeLogWeight_eq_theta] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  have hzero : (Real.log Y - Real.log Y) ^ (j + 1) = 0 := by simp
  rw [hzero, mul_zero, zero_mul] at habel
  have hint : (∫ t in Ioc (2 : ℝ) Y,
      deriv (fun u : ℝ => u ^ (a - 1) * (Real.log Y - Real.log u) ^ (j + 1)) t *
        Chebyshev.theta t)
      = ∫ t in (2 : ℝ)..Y,
          ((a - 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ (j + 1)
            - ((j : ℝ) + 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ j) *
            Chebyshev.theta t := by
    rw [intervalIntegral.integral_of_le hY]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := by
      have h2 := ht.1
      linarith
    rw [(hasDerivAt_windowWeight (a := a) (Y := Y) j ht0).deriv]
  have hlhs : primeWindowSum a (j + 1) Y
      = ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
          ((k : ℝ) ^ (a - 1) * (Real.log Y - Real.log k) ^ (j + 1)) * primeLogWeight k := by
    rw [primeWindowSum]
    exact Finset.sum_congr rfl fun k _ =>
      (windowWeight_mul_primeLogWeight (a := a) (Y := Y) (j + 1) k).symm
  rw [hlhs, habel, hint]
  ring

/-- The Abel integral splits into the two window integrals and their error remainders. -/
theorem integral_derivWindow_mul_theta_eq {a Y : ℝ} (j : ℕ) (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y,
      ((a - 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ (j + 1)
        - ((j : ℝ) + 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ j) * Chebyshev.theta t)
      = (a - 1) * HTGeometry.windowRpowIntegral a (j + 1) Y
        - ((j : ℝ) + 1) * HTGeometry.windowRpowIntegral a j Y
        + ((a - 1) * thetaErrorWindowIntegral a (j + 1) Y
          - ((j : ℝ) + 1) * thetaErrorWindowIntegral a j Y) := by
  have hpt : ∀ t ∈ uIcc (2 : ℝ) Y,
      ((a - 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ (j + 1)
        - ((j : ℝ) + 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ j) * Chebyshev.theta t
      = ((a - 1) * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ (j + 1))
          - ((j : ℝ) + 1) * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))
        + ((a - 1) * (thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ (j + 1)))
          - ((j : ℝ) + 1) * (thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))) := by
    intro t ht
    rw [uIcc_of_le hY] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hrp : t ^ (a - 2) * t = t ^ (a - 1) := by
      nth_rewrite 2 [← Real.rpow_one t]
      rw [← Real.rpow_add ht0, show a - 2 + 1 = a - 1 by ring]
    rw [theta_eq_mul_thetaError ht0]
    calc ((a - 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ (j + 1)
          - ((j : ℝ) + 1) * t ^ (a - 2) * (Real.log Y - Real.log t) ^ j) *
            (t * (1 + thetaError t))
        = ((a - 1) * (t ^ (a - 2) * t) * (Real.log Y - Real.log t) ^ (j + 1)
          - ((j : ℝ) + 1) * (t ^ (a - 2) * t) * (Real.log Y - Real.log t) ^ j) *
            (1 + thetaError t) := by ring
      _ = ((a - 1) * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ (j + 1))
          - ((j : ℝ) + 1) * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))
          + ((a - 1) * (thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ (j + 1)))
            - ((j : ℝ) + 1) *
              (thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j))) := by
          rw [hrp]
          ring
  have hI1 : IntervalIntegrable
      (fun t : ℝ => (a - 1) * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ (j + 1))) volume 2 Y :=
    (HTGeometry.intervalIntegrable_windowIntegrand a (j + 1) Y (le_refl (2 : ℝ)) hY).const_mul _
  have hI2 : IntervalIntegrable
      (fun t : ℝ => ((j : ℝ) + 1) * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)) volume 2 Y :=
    (HTGeometry.intervalIntegrable_windowIntegrand a j Y (le_refl (2 : ℝ)) hY).const_mul _
  have hI3 : IntervalIntegrable
      (fun t : ℝ => (a - 1) * (thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ (j + 1))))
      volume 2 Y := (intervalIntegrable_thetaError_window a (j + 1) Y hY).const_mul _
  have hI4 : IntervalIntegrable
      (fun t : ℝ => ((j : ℝ) + 1) * (thetaError t * (t ^ (a - 1) * (Real.log Y - Real.log t) ^ j)))
      volume 2 Y := (intervalIntegrable_thetaError_window a j Y hY).const_mul _
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (hI1.sub hI2) (hI3.sub hI4),
    intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_sub hI3 hI4,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

/-- **The prime window law.**  The prime measure carries the exponential window density
`e^{-av} dv` in the variable `v = log Y - log p`. -/
theorem tendsto_primeWindowSum {a : ℝ} (ha0 : 0 < a) (j : ℕ) :
    Tendsto (fun Y : ℝ => primeWindowSum a j Y / Y ^ a) atTop
      (nhds ((Nat.factorial j : ℝ) / a ^ (j + 1))) := by
  cases j with
  | zero =>
    have hconst : (Nat.factorial 0 : ℝ) / a ^ (0 + 1) = 1 / a := by
      simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    rw [hconst]
    refine (tendsto_primeRpowLogSumIoc ha0).congr fun Y => ?_
    rw [primeWindowSum_zero]
  | succ j =>
    have hbdry : Tendsto (fun Y : ℝ =>
        (2 : ℝ) ^ (a - 1) * (Real.log Y - Real.log 2) ^ (j + 1) * Chebyshev.theta 2 / Y ^ a)
        atTop (nhds 0) := by
      have h := (HTGeometry.tendsto_logSubPow_div_rpow ha0 (j + 1)).const_mul
        ((2 : ℝ) ^ (a - 1) * Chebyshev.theta 2)
      rw [mul_zero] at h
      refine h.congr fun Y => ?_
      ring
    have hJ1 := HTGeometry.tendsto_windowRpowIntegral ha0 (j + 1)
    have hJ0 := HTGeometry.tendsto_windowRpowIntegral ha0 j
    have hR1 := tendsto_thetaErrorWindowIntegral ha0 (j + 1)
    have hR0 := tendsto_thetaErrorWindowIntegral ha0 j
    have hsum := ((hbdry.neg).sub (((hJ1.const_mul (a - 1)).sub
      (hJ0.const_mul ((j : ℝ) + 1))).add
        ((hR1.const_mul (a - 1)).sub (hR0.const_mul ((j : ℝ) + 1)))))
    have hlim : -(0 : ℝ) - ((a - 1) * ((Nat.factorial (j + 1) : ℝ) / a ^ (j + 1 + 1))
        - ((j : ℝ) + 1) * ((Nat.factorial j : ℝ) / a ^ (j + 1))
        + ((a - 1) * 0 - ((j : ℝ) + 1) * 0))
        = (Nat.factorial (j + 1) : ℝ) / a ^ (j + 1 + 1) := by
      have hane : a ≠ 0 := ne_of_gt ha0
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [hlim] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    rw [primeWindowSum_succ_eq j hY, integral_derivWindow_mul_theta_eq j hY]
    field_simp

end

end RHTower
