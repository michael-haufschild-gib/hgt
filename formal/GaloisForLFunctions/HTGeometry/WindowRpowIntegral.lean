import GaloisForLFunctions.HTGeometry.RpowKernelRemainder

/-!
# The window power integral

For `a > 0` and `j : ℕ` the window integral

```text
J_j(Y) = ∫_2^Y u^(a-1) (log Y - log u)^j du
```

satisfies the exact recursion `J_{j+1} = -2^a(log Y - log 2)^{j+1}/a + ((j+1)/a) J_j`, obtained by
integrating `u^(a-1)` against the window power.  Since `J_0 = (Y^a - 2^a)/a`, the recursion gives
the uniform bound `J_j ≤ (j!/a^(j+1)) Y^a` and the normalized limit `Y^(-a) J_j → j!/a^(j+1)`,
which is the exponential moment `∫_0^∞ e^{-av} v^j dv` of the logarithmic window variable
`v = log Y - log u`.
-/

open Filter Topology Set MeasureTheory intervalIntegral Asymptotics

namespace HTGeometry

noncomputable section

/-! ## Logarithmic powers against a power normalization -/

/-- A fixed power of the logarithm is negligible against any positive power. -/
theorem tendsto_logPow_div_rpow {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun Y : ℝ => (Real.log Y) ^ k / Y ^ a) atTop (nhds 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h : Tendsto (fun Y : ℝ => (1 : ℝ) / Y ^ a) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha)
    exact h.congr fun Y => by rw [pow_zero]
  · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hbase : Tendsto (fun Y : ℝ => Real.log Y / Y ^ (a / (k : ℝ))) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by positivity)).tendsto_div_nhds_zero
    have hpow := hbase.pow k
    rw [zero_pow (by omega)] at hpow
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    rw [div_pow, ← Real.rpow_natCast (Y ^ (a / (k : ℝ))) k, ← Real.rpow_mul hY.le]
    congr 2
    field_simp

/-- The shifted logarithmic power is negligible against any positive power. -/
theorem tendsto_logSubPow_div_rpow {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun Y : ℝ => (Real.log Y - Real.log 2) ^ k / Y ^ a) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_logPow_div_rpow ha k)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    have h1 : (0 : ℝ) ≤ (Real.log Y - Real.log 2) ^ k := pow_nonneg (by linarith) k
    have h2 : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    positivity
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    have h2 : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    have hmono : (Real.log Y - Real.log 2) ^ k ≤ (Real.log Y) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith) k
    exact div_le_div_of_nonneg_right hmono h2.le

/-! ## The window integral -/

/-- The window power integral `∫_2^Y u^(a-1) (log Y - log u)^j du`. -/
def windowRpowIntegral (a : ℝ) (j : ℕ) (Y : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..Y, u ^ (a - 1) * (Real.log Y - Real.log u) ^ j

theorem continuousOn_windowIntegrand (a : ℝ) (j : ℕ) (Y : ℝ) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    ContinuousOn (fun t : ℝ => t ^ (a - 1) * (Real.log Y - Real.log t) ^ j) (uIcc u v) := by
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := two_le_of_mem_uIcc hu hv ht
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht2
    linarith
  exact ((Real.continuousAt_rpow_const t (a - 1) (Or.inl ht0)).mul
    ((continuousAt_const.sub (Real.continuousAt_log ht0)).pow j)).continuousWithinAt

theorem intervalIntegrable_windowIntegrand (a : ℝ) (j : ℕ) (Y : ℝ) {u v : ℝ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * (Real.log Y - Real.log t) ^ j) volume u v :=
  (continuousOn_windowIntegrand a j Y hu hv).intervalIntegrable

theorem windowRpowIntegral_zero {a : ℝ} (ha : 0 < a) (Y : ℝ) :
    windowRpowIntegral a 0 Y = (Y ^ a - (2 : ℝ) ^ a) / a := by
  unfold windowRpowIntegral
  simp only [pow_zero, mul_one]
  exact integral_rpow_sub_one ha 2 Y

/-- **The window recursion.**  Integrating the power against the window logarithm lowers the
window degree by one. -/
theorem windowRpowIntegral_succ {a : ℝ} (ha : 0 < a) (j : ℕ) {Y : ℝ} (hY : 2 ≤ Y) :
    windowRpowIntegral a (j + 1) Y =
      -((2 : ℝ) ^ a * (Real.log Y - Real.log 2) ^ (j + 1) / a)
        + ((j : ℝ) + 1) / a * windowRpowIntegral a j Y := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hU : ∀ x ∈ uIcc (2 : ℝ) Y,
      HasDerivAt (fun t : ℝ => (Real.log Y - Real.log t) ^ (j + 1))
        (((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j * (-x⁻¹)) x := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := two_le_of_mem_uIcc le_rfl hY hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx2
      linarith
    have hbase : HasDerivAt (fun t : ℝ => Real.log Y - Real.log t) (-x⁻¹) x :=
      (Real.hasDerivAt_log hx0).const_sub (Real.log Y)
    have hout : HasDerivAt (fun s : ℝ => s ^ (j + 1))
        (((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j) (Real.log Y - Real.log x) := by
      simpa using hasDerivAt_pow (j + 1) (Real.log Y - Real.log x)
    simpa [Function.comp_def] using hout.comp x hbase
  have hV : ∀ x ∈ uIcc (2 : ℝ) Y, HasDerivAt (fun t : ℝ => t ^ a / a) (x ^ (a - 1)) x := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := two_le_of_mem_uIcc le_rfl hY hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx2
      linarith
    have h := (Real.hasDerivAt_rpow_const (x := x) (p := a) (Or.inl hx0)).div_const a
    have hval : a * x ^ (a - 1) / a = x ^ (a - 1) := by field_simp
    rwa [hval] at h
  have hUint : IntervalIntegrable
      (fun x : ℝ => ((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j * (-x⁻¹)) volume 2 Y := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have ht2 : (2 : ℝ) ≤ t := two_le_of_mem_uIcc le_rfl hY ht
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht2
      linarith
    exact ((continuousAt_const.mul
      ((continuousAt_const.sub (Real.continuousAt_log ht0)).pow j)).mul
        (continuousAt_inv₀ ht0).neg).continuousWithinAt
  have hVint : IntervalIntegrable (fun x : ℝ => x ^ (a - 1)) volume 2 Y :=
    intervalIntegrable_rpowSubOne a le_rfl hY
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hV hUint hVint
  have hlhs : (∫ x in (2 : ℝ)..Y, (Real.log Y - Real.log x) ^ (j + 1) * x ^ (a - 1))
      = windowRpowIntegral a (j + 1) Y := by
    unfold windowRpowIntegral
    exact intervalIntegral.integral_congr fun t _ => by ring
  have hrhs : (∫ x in (2 : ℝ)..Y,
      ((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j * (-x⁻¹) * (x ^ a / a))
      = -(((j : ℝ) + 1) / a) * windowRpowIntegral a j Y := by
    have hcongr : (∫ x in (2 : ℝ)..Y,
        ((j : ℝ) + 1) * (Real.log Y - Real.log x) ^ j * (-x⁻¹) * (x ^ a / a))
        = ∫ x in (2 : ℝ)..Y,
          (-(((j : ℝ) + 1) / a)) * (x ^ (a - 1) * (Real.log Y - Real.log x) ^ j) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht2 : (2 : ℝ) ≤ t := two_le_of_mem_uIcc le_rfl hY ht
      have ht0 : (0 : ℝ) < t := by linarith
      have hrp : t ^ (a - 1) = t ^ a * t⁻¹ := by
        rw [Real.rpow_sub ht0, Real.rpow_one, div_eq_mul_inv]
      rw [hrp]
      field_simp
    rw [hcongr, intervalIntegral.integral_const_mul]
    rfl
  rw [hlhs, hrhs] at hparts
  have hzero : (Real.log Y - Real.log Y) ^ (j + 1) = 0 := by
    simp
  rw [hzero] at hparts
  rw [hparts]
  ring

/-! ## Bound and limit -/

theorem windowRpowIntegral_nonneg (a : ℝ) (j : ℕ) {Y : ℝ} (hY : 2 ≤ Y) :
    0 ≤ windowRpowIntegral a j Y := by
  refine intervalIntegral.integral_nonneg hY fun u hu => ?_
  have hu2 : (2 : ℝ) ≤ u := hu.1
  have huY : u ≤ Y := hu.2
  have h1 : (0 : ℝ) ≤ u ^ (a - 1) := Real.rpow_nonneg (by linarith) _
  have h2 : (0 : ℝ) ≤ Real.log Y - Real.log u := by
    have := Real.log_le_log (by linarith : (0 : ℝ) < u) huY
    linarith
  exact mul_nonneg h1 (pow_nonneg h2 j)

/-- **The uniform window bound** `J_j ≤ (j!/a^(j+1)) Y^a`. -/
theorem windowRpowIntegral_le {a : ℝ} (ha : 0 < a) (j : ℕ) {Y : ℝ} (hY : 2 ≤ Y) :
    windowRpowIntegral a j Y ≤ (Nat.factorial j : ℝ) / a ^ (j + 1) * Y ^ a := by
  induction j with
  | zero =>
    rw [windowRpowIntegral_zero ha]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
    have hstep : (Y ^ a - (2 : ℝ) ^ a) / a ≤ Y ^ a / a :=
      div_le_div_of_nonneg_right (by linarith) ha.le
    have hval : (Nat.factorial 0 : ℝ) / a ^ (0 + 1) * Y ^ a = Y ^ a / a := by
      simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
      ring
    rw [hval]
    exact hstep
  | succ j ih =>
    rw [windowRpowIntegral_succ ha j hY]
    have hlogY : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    have hterm : (0 : ℝ) ≤ (2 : ℝ) ^ a * (Real.log Y - Real.log 2) ^ (j + 1) / a := by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
      have hp : (0 : ℝ) ≤ (Real.log Y - Real.log 2) ^ (j + 1) :=
        pow_nonneg (by linarith) _
      positivity
    have hcoef : (0 : ℝ) ≤ ((j : ℝ) + 1) / a := by positivity
    have hstep : ((j : ℝ) + 1) / a * windowRpowIntegral a j Y ≤
        ((j : ℝ) + 1) / a * ((Nat.factorial j : ℝ) / a ^ (j + 1) * Y ^ a) :=
      mul_le_mul_of_nonneg_left ih hcoef
    have hval : ((j : ℝ) + 1) / a * ((Nat.factorial j : ℝ) / a ^ (j + 1) * Y ^ a)
        = (Nat.factorial (j + 1) : ℝ) / a ^ (j + 2) * Y ^ a := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hval] at hstep
    linarith

/-- **The normalized window limit** `Y^(-a) J_j → j!/a^(j+1)`. -/
theorem tendsto_windowRpowIntegral {a : ℝ} (ha : 0 < a) (j : ℕ) :
    Tendsto (fun Y : ℝ => windowRpowIntegral a j Y / Y ^ a) atTop
      (nhds ((Nat.factorial j : ℝ) / a ^ (j + 1))) := by
  induction j with
  | zero =>
    have hconst : (Nat.factorial 0 : ℝ) / a ^ (0 + 1) = 1 / a := by
      simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    rw [hconst]
    have h2 : Tendsto (fun Y : ℝ => (2 : ℝ) ^ a / a / Y ^ a) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha)
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => 1 / a) atTop (nhds (1 / a))).sub h2
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    rw [windowRpowIntegral_zero ha]
    field_simp
  | succ j ih =>
    have hlogpow : Tendsto
        (fun Y : ℝ => (2 : ℝ) ^ a * (Real.log Y - Real.log 2) ^ (j + 1) / a / Y ^ a) atTop
        (nhds 0) := by
      have h := (tendsto_logSubPow_div_rpow ha (j + 1)).const_mul ((2 : ℝ) ^ a / a)
      rw [mul_zero] at h
      refine h.congr fun Y => ?_
      ring
    have hmain := ih.const_mul (((j : ℝ) + 1) / a)
    have hsum := (hlogpow.neg).add hmain
    rw [neg_zero, zero_add] at hsum
    have hval : ((j : ℝ) + 1) / a * ((Nat.factorial j : ℝ) / a ^ (j + 1))
        = (Nat.factorial (j + 1) : ℝ) / a ^ (j + 2) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hval] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    rw [windowRpowIntegral_succ ha j hY]
    ring

end

end HTGeometry
