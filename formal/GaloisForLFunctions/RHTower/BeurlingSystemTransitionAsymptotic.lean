import GaloisForLFunctions.RHTower.BeurlingSystemPrimeSumAsymptotic
import GaloisForLFunctions.RHTower.BeurlingSystemTransitionKernel

/-!
# The transition asymptotic

The one-large-prime kernel of a Beurling system has a single sign transition `τ_{P,z}`, determined
by `∑_{|p| > z} e^{-(|p|-1)τ} = 1`.  Under the prime number theorem the transition sits at
`log z / z`:

```text
z τ_{P,z} / log z → 1.
```

Both halves are exponential tail estimates for the large-prime sum at `t = c log z / z`.  Partial
summation against the counting function bounds the whole tail by `2(z + 1/t)e^{-(z-1)t}`, which is
`O(z^{1-c})` and hence vanishes for `c > 1`; a single window `(z, Kz]` bounds it below by
`(π_P(Kz) - π_P(z))e^{-(Kz-1)t}`, which is of order `z^{1-cK}/log z` and hence diverges for
`c < 1` once `K` is chosen between `1` and `1/c`.  Strict antitonicity of the tail then pins the
transition between the two.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

namespace BeurlingSystem

variable {B : BeurlingSystem}

/-! ## Two-sided counting bounds from the prime number theorem -/

theorem eventually_primeCount_le (hpnt : B.HasPrimePNT) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, (B.primeCount y : ℝ) ≤ (1 + η) * (y / Real.log y) := by
  filter_upwards [hpnt.eventually (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + η)),
    eventually_gt_atTop (1 : ℝ)] with y hy hy1
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hpos : 0 < y / Real.log y := div_pos hy0 hlog
  have hkey : (B.primeCount y : ℝ) * Real.log y / y * (y / Real.log y)
      = (B.primeCount y : ℝ) := by field_simp
  have h2 := mul_lt_mul_of_pos_right hy hpos
  rw [hkey] at h2
  exact h2.le

theorem eventually_le_primeCount (hpnt : B.HasPrimePNT) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, (1 - η) * (y / Real.log y) ≤ (B.primeCount y : ℝ) := by
  filter_upwards [hpnt.eventually (eventually_gt_nhds (by linarith : (1 : ℝ) - η < 1)),
    eventually_gt_atTop (1 : ℝ)] with y hy hy1
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hpos : 0 < y / Real.log y := div_pos hy0 hlog
  have hkey : (B.primeCount y : ℝ) * Real.log y / y * (y / Real.log y)
      = (B.primeCount y : ℝ) := by field_simp
  have h2 := mul_lt_mul_of_pos_right hy hpos
  rw [hkey] at h2
  exact h2.le

theorem eventually_primeCount_le_two_mul (hpnt : B.HasPrimePNT) :
    ∀ᶠ y : ℝ in atTop, (B.primeCount y : ℝ) ≤ 2 * y := by
  filter_upwards [eventually_primeCount_le hpnt (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (Real.exp 1)] with y hy hye
  have h1 : (1 : ℝ) ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hye)]
    exact hye
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (Real.exp_pos 1) hye
  have hle : y / Real.log y ≤ y := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ## The exponential moment of the linear weight -/

theorem hasDerivAt_expMoment {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    HasDerivAt (fun v : ℝ => -(v / t + 1 / t ^ 2) * Real.exp (-(v - 1) * t))
      (u * Real.exp (-(u - 1) * t)) u := by
  have h1 : HasDerivAt (fun v : ℝ => -(v / t + 1 / t ^ 2)) (-(1 / t)) u :=
    (((hasDerivAt_id u).div_const t).add_const (1 / t ^ 2)).neg
  have hlin : HasDerivAt (fun v : ℝ => -(v - 1) * t) (-t) u := by
    have h : HasDerivAt (fun v : ℝ => -(v - 1) * t) (-1 * t) u :=
      (((hasDerivAt_id u).sub_const 1).neg).mul_const t
    rwa [neg_one_mul] at h
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (-(v - 1) * t))
      (Real.exp (-(u - 1) * t) * (-t)) u := hlin.exp
  have h := h1.mul h2
  have heq : -(1 / t) * Real.exp (-(u - 1) * t)
      + -(u / t + 1 / t ^ 2) * (Real.exp (-(u - 1) * t) * (-t))
      = u * Real.exp (-(u - 1) * t) := by
    field_simp
    ring
  rwa [heq] at h

theorem intervalIntegrable_linear_exp (t : ℝ) (z X : ℝ) :
    IntervalIntegrable (fun u : ℝ => u * Real.exp (-(u - 1) * t)) volume z X := by
  apply Continuous.intervalIntegrable
  exact continuous_id.mul (Real.continuous_exp.comp (by fun_prop))

theorem integral_linear_exp {t : ℝ} (ht : t ≠ 0) (z X : ℝ) :
    (∫ u in z..X, u * Real.exp (-(u - 1) * t))
      = (z / t + 1 / t ^ 2) * Real.exp (-(z - 1) * t)
        - (X / t + 1 / t ^ 2) * Real.exp (-(X - 1) * t) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => -(v / t + 1 / t ^ 2) * Real.exp (-(v - 1) * t))
    (fun u _ => hasDerivAt_expMoment ht u) (intervalIntegrable_linear_exp t z X)
  rw [h]
  ring

/-! ## The upper bound on the large-prime tail -/

theorem sum_primeWindow_exp_le (hdisc : B.IsDiscrete) {z X t : ℝ} (hz : 0 < z) (hzX : z ≤ X)
    (ht : 0 < t) (hbd : ∀ u : ℝ, z ≤ u → (B.primeCount u : ℝ) ≤ 2 * u) :
    ∑ p ∈ (finite_primeWindow hdisc z X).toFinset, Real.exp (-(B.labelNorm p - 1) * t)
      ≤ 2 * (z + 1 / t) * Real.exp (-(z - 1) * t)
        + (B.primeCount X : ℝ) * Real.exp (-(X - 1) * t) := by
  have hderiv : ∀ u ∈ Icc z X,
      HasDerivAt (fun v : ℝ => Real.exp (-(v - 1) * t)) (-t * Real.exp (-(u - 1) * t)) u := by
    intro u _
    have hlin : HasDerivAt (fun v : ℝ => -(v - 1) * t) (-t) u := by
      have h := (((hasDerivAt_id u).sub_const 1).neg).mul_const t
      simpa using h
    have h := hlin.exp
    rw [mul_comm] at h
    exact h
  have hint : IntervalIntegrable (fun u : ℝ => -t * Real.exp (-(u - 1) * t)) volume z X := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (Real.continuous_exp.comp (by fun_prop))
  have habel := sum_primeWindow_eq_sub_sub_integral hdisc hzX hderiv hint
  -- the integral against the counting function
  have hI1 : IntervalIntegrable
      (fun u : ℝ => (-t * Real.exp (-(u - 1) * t)) * (B.primeCount u : ℝ)) volume z X :=
    intervalIntegrable_mul_primeCount hdisc hzX hint
  have hI2 : IntervalIntegrable
      (fun u : ℝ => (-t * Real.exp (-(u - 1) * t)) * (2 * u)) volume z X := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).mul
      (continuous_const.mul continuous_id)
  have hmono : (∫ u in z..X, (-t * Real.exp (-(u - 1) * t)) * (2 * u))
      ≤ ∫ u in z..X, (-t * Real.exp (-(u - 1) * t)) * (B.primeCount u : ℝ) := by
    refine intervalIntegral.integral_mono_on hzX hI2 hI1 fun u hu => ?_
    have hneg : -t * Real.exp (-(u - 1) * t) ≤ 0 := by
      have := Real.exp_pos (-(u - 1) * t)
      nlinarith
    exact mul_le_mul_of_nonpos_left (hbd u hu.1) hneg
  have hval : (∫ u in z..X, (-t * Real.exp (-(u - 1) * t)) * (2 * u))
      = -2 * t * ((z / t + 1 / t ^ 2) * Real.exp (-(z - 1) * t)
        - (X / t + 1 / t ^ 2) * Real.exp (-(X - 1) * t)) := by
    have hrw : (fun u : ℝ => (-t * Real.exp (-(u - 1) * t)) * (2 * u))
        = fun u : ℝ => (-2 * t) * (u * Real.exp (-(u - 1) * t)) := by
      funext u
      ring
    rw [hrw, intervalIntegral.integral_const_mul, integral_linear_exp (ne_of_gt ht)]
  have hzterm : 0 ≤ (B.primeCount z : ℝ) * Real.exp (-(z - 1) * t) := by positivity
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le hz hzX
  have hB : 0 ≤ 2 * t * ((X / t + 1 / t ^ 2) * Real.exp (-(X - 1) * t)) := by
    have h1 : 0 < X / t := div_pos hX0 ht
    have h2 : 0 < 1 / t ^ 2 := by positivity
    have h3 : 0 < Real.exp (-(X - 1) * t) := Real.exp_pos _
    have h4 : 0 < X / t + 1 / t ^ 2 := by linarith
    positivity
  have hz2 : 2 * t * ((z / t + 1 / t ^ 2) * Real.exp (-(z - 1) * t))
      = 2 * (z + 1 / t) * Real.exp (-(z - 1) * t) := by
    field_simp
  have hIle : -(∫ u in z..X, (-t * Real.exp (-(u - 1) * t)) * (B.primeCount u : ℝ))
      ≤ 2 * (z + 1 / t) * Real.exp (-(z - 1) * t) := by
    have h1 := neg_le_neg hmono
    rw [hval] at h1
    linarith
  rw [habel]
  linarith

theorem tendsto_primeCount_mul_exp {z t : ℝ} (ht : 0 < t)
    (hbd : ∀ u : ℝ, z ≤ u → (B.primeCount u : ℝ) ≤ 2 * u) :
    Tendsto (fun X : ℝ => (B.primeCount X : ℝ) * Real.exp (-(X - 1) * t)) atTop (nhds 0) := by
  have hlin : Tendsto (fun X : ℝ => X * t) atTop atTop := tendsto_id.atTop_mul_const ht
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
  have hmaj : Tendsto (fun X : ℝ => 2 * X * Real.exp (-(X - 1) * t)) atTop (nhds 0) := by
    have h := hbase.const_mul (2 * Real.exp t / t)
    rw [mul_zero] at h
    refine h.congr fun X => ?_
    simp only [Function.comp_apply, pow_one]
    rw [show -(X - 1) * t = t + -(X * t) by ring, Real.exp_add]
    field_simp
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with X
    positivity
  · filter_upwards [eventually_ge_atTop z] with X hX
    have h := hbd X hX
    have hE : 0 < Real.exp (-(X - 1) * t) := Real.exp_pos _
    nlinarith

/-- **The large-prime tail is bounded by the partial-summation estimate.** -/
theorem largeTail_le (hdisc : B.IsDiscrete) {z t : ℝ} (hz : 0 < z) (ht : 0 < t)
    (hbd : ∀ u : ℝ, z ≤ u → (B.primeCount u : ℝ) ≤ 2 * u) :
    B.largeTail z t ≤ 2 * (z + 1 / t) * Real.exp (-(z - 1) * t) := by
  classical
  rw [largeTail]
  refine Real.tsum_le_of_sum_le (fun p => (Real.exp_pos _).le) fun S => ?_
  have htend : Tendsto (fun X : ℝ => 2 * (z + 1 / t) * Real.exp (-(z - 1) * t)
      + (B.primeCount X : ℝ) * Real.exp (-(X - 1) * t)) atTop
      (nhds (2 * (z + 1 / t) * Real.exp (-(z - 1) * t))) := by
    have h := (tendsto_primeCount_mul_exp (z := z) ht hbd).const_add
      (2 * (z + 1 / t) * Real.exp (-(z - 1) * t))
    rwa [add_zero] at h
  refine ge_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop z,
    (Filter.eventually_all_finset S).mpr
      (fun p _ => eventually_ge_atTop (B.labelNorm (p : B.Label)))] with X hzX hall
  have hsub : S.image Subtype.val ⊆ (finite_primeWindow hdisc z X).toFinset := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hpS, rfl⟩ := hq
    rw [Set.Finite.mem_toFinset]
    exact ⟨p.2, hall p hpS⟩
  calc ∑ p ∈ S, Real.exp (-(B.labelNorm (p : B.Label) - 1) * t)
      = ∑ q ∈ S.image Subtype.val, Real.exp (-(B.labelNorm q - 1) * t) :=
        (Finset.sum_image (f := fun q : B.Label => Real.exp (-(B.labelNorm q - 1) * t))
          (fun _ _ _ _ h => Subtype.ext h)).symm
    _ ≤ ∑ q ∈ (finite_primeWindow hdisc z X).toFinset, Real.exp (-(B.labelNorm q - 1) * t) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le
    _ ≤ _ := sum_primeWindow_exp_le hdisc hz hzX ht hbd

/-! ## The lower bound on the large-prime tail -/

/-- **A single window bounds the large-prime tail below.** -/
theorem le_largeTail (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C) {z Y t : ℝ}
    (hzY : z ≤ Y) (ht : 0 < t) :
    ((B.primeCount Y : ℝ) - (B.primeCount z : ℝ)) * Real.exp (-(Y - 1) * t)
      ≤ B.largeTail z t := by
  classical
  have hsummable := summable_largeTailTerm hdisc hC z ht
  set T : Finset {p : B.Label // z < B.labelNorm p} :=
    (finite_primeWindow hdisc z Y).toFinset.subtype (fun q => z < B.labelNorm q) with hTdef
  have hmemT : ∀ x : {p : B.Label // z < B.labelNorm p},
      x ∈ T ↔ (x : B.Label) ∈ (finite_primeWindow hdisc z Y).toFinset := by
    intro x
    rw [hTdef, Finset.mem_subtype]
  have hfilter : (finite_primeWindow hdisc z Y).toFinset.filter (fun q => z < B.labelNorm q)
      = (finite_primeWindow hdisc z Y).toFinset := by
    refine Finset.filter_true_of_mem fun q hq => ?_
    rw [Set.Finite.mem_toFinset] at hq
    exact hq.1
  have hcard : (T.card : ℝ) = (B.primeCount Y : ℝ) - (B.primeCount z : ℝ) := by
    have h1 : T.card = (finite_primeWindow hdisc z Y).toFinset.card := by
      rw [hTdef, Finset.card_subtype, hfilter]
    have h2 : B.primeCount Y = B.primeCount z + (B.primeWindow z Y).ncard :=
      primeCount_eq_add_ncard_primeWindow hdisc hzY
    have h3 : (B.primeWindow z Y).ncard = (finite_primeWindow hdisc z Y).toFinset.card :=
      Set.ncard_eq_toFinset_card _ (finite_primeWindow hdisc z Y)
    rw [h1, ← h3]
    have h4 := congrArg (fun n : ℕ => (n : ℝ)) h2
    push_cast at h4
    linarith
  have hterm : ∀ x ∈ T, Real.exp (-(Y - 1) * t)
      ≤ Real.exp (-(B.labelNorm (x : B.Label) - 1) * t) := by
    intro x hx
    rw [hmemT, Set.Finite.mem_toFinset] at hx
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hx.2, ht]
  calc ((B.primeCount Y : ℝ) - (B.primeCount z : ℝ)) * Real.exp (-(Y - 1) * t)
      = (T.card : ℝ) * Real.exp (-(Y - 1) * t) := by rw [hcard]
    _ = ∑ _x ∈ T, Real.exp (-(Y - 1) * t) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ T, Real.exp (-(B.labelNorm (x : B.Label) - 1) * t) := Finset.sum_le_sum hterm
    _ ≤ B.largeTail z t := by
        rw [largeTail]
        exact hsummable.sum_le_tsum T fun _ _ => (Real.exp_pos _).le

/-! ## The two exponential regimes -/

/-- Above the critical rate the partial-summation bound vanishes. -/
theorem tendsto_largeTailBound {c : ℝ} (hc1 : 1 < c) :
    Tendsto (fun z : ℝ => 2 * (z + 1 / (c * Real.log z / z))
      * Real.exp (-(z - 1) * (c * Real.log z / z))) atTop (nhds 0) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hlogz : Tendsto (fun z : ℝ => Real.log z) atTop atTop := Real.tendsto_log_atTop
  have hlogdiv : Tendsto (fun z : ℝ => Real.log z / z) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    refine h.congr fun z => ?_
    rw [Real.rpow_one]
  have hinvlog : Tendsto (fun z : ℝ => 1 / (c * Real.log z)) atTop (nhds 0) := by
    have h := (hlogz.const_mul_atTop hc0).inv_tendsto_atTop
    refine h.congr fun z => ?_
    simp [Pi.inv_apply, one_div]
  have hrpow : Tendsto (fun z : ℝ => z ^ (1 - c)) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (y := c - 1) (by linarith)
    refine h.congr fun z => ?_
    rw [show -(c - 1) = 1 - c by ring]
  have hexp : Tendsto (fun z : ℝ => Real.exp (c * Real.log z / z)) atTop (nhds 1) := by
    have h : Tendsto (fun z : ℝ => c * Real.log z / z) atTop (nhds 0) := by
      have h0 := hlogdiv.const_mul c
      rw [mul_zero] at h0
      refine h0.congr fun z => ?_
      ring
    have h1 := Real.continuous_exp.continuousAt.tendsto.comp h
    simpa [Function.comp_def] using h1
  have hmain : Tendsto (fun z : ℝ => 2 * z ^ (1 - c) * (1 + 1 / (c * Real.log z))
      * Real.exp (c * Real.log z / z)) atTop (nhds 0) := by
    have h1 : Tendsto (fun z : ℝ => 2 * z ^ (1 - c)) atTop (nhds 0) := by
      have h := hrpow.const_mul 2
      rwa [mul_zero] at h
    have h2 : Tendsto (fun z : ℝ => (1 : ℝ) + 1 / (c * Real.log z)) atTop (nhds 1) := by
      have h := hinvlog.const_add 1
      rwa [add_zero] at h
    have h3 := (h1.mul h2).mul hexp
    simpa using h3
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hrw1 : (1 : ℝ) / (c * Real.log z / z) = z / (c * Real.log z) := by
    field_simp
  have hrw2 : -(z - 1) * (c * Real.log z / z) = -(c * Real.log z) + c * Real.log z / z := by
    field_simp
    ring
  have hexpneg : Real.exp (-(c * Real.log z)) = z ^ (-c) := by
    rw [Real.rpow_def_of_pos hz0]
    congr 1
    ring
  have hzz : z * z ^ (-c) = z ^ (1 - c) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz0, show (1 : ℝ) + -c = 1 - c by ring]
  rw [hrw2, Real.exp_add, hexpneg, hrw1,
    show z + z / (c * Real.log z) = z * (1 + 1 / (c * Real.log z)) by field_simp, ← hzz]
  ring

/-- The window count is asymptotically `(K-1) z / log z`. -/
theorem tendsto_primeCountWindow (hpnt : B.HasPrimePNT) {K : ℝ} (hK : 1 < K) :
    Tendsto (fun z : ℝ => ((B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ))
      * Real.log z / z) atTop (nhds (K - 1)) := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hscale : Tendsto (fun z : ℝ => K * z) atTop atTop := tendsto_id.const_mul_atTop hK0
  have h1 : Tendsto
      (fun z : ℝ => (B.primeCount (K * z) : ℝ) * Real.log (K * z) / (K * z)) atTop (nhds 1) :=
    hpnt.comp hscale
  have hlogratio : Tendsto (fun z : ℝ => Real.log z / Real.log (K * z)) atTop (nhds 1) := by
    have hlogz : Tendsto (fun z : ℝ => Real.log z) atTop atTop := Real.tendsto_log_atTop
    have hconst : Tendsto (fun z : ℝ => Real.log K / Real.log z) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlogz
    have hsum : Tendsto (fun z : ℝ => (1 : ℝ) + Real.log K / Real.log z) atTop (nhds 1) := by
      have h := hconst.const_add 1
      rwa [add_zero] at h
    have hinv := hsum.inv₀ (by norm_num)
    rw [inv_one] at hinv
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    have hz0 : (0 : ℝ) < z := by linarith
    have hlog : 0 < Real.log z := Real.log_pos hz
    rw [Real.log_mul (by linarith) (by linarith)]
    field_simp
    ring
  have hbig : Tendsto (fun z : ℝ => (B.primeCount (K * z) : ℝ) * Real.log z / z) atTop
      (nhds K) := by
    have h := (h1.mul hlogratio).const_mul K
    rw [mul_one, mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    have hz0 : (0 : ℝ) < z := by linarith
    have hlog : 0 < Real.log z := Real.log_pos hz
    have hlogK : 0 < Real.log (K * z) := by
      rw [Real.log_mul (by linarith) (by linarith)]
      have : 0 ≤ Real.log K := Real.log_nonneg hK.le
      linarith
    field_simp
  have hsub := hbig.sub hpnt
  refine hsub.congr fun z => ?_
  ring

theorem tendsto_rpow_div_log_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun z : ℝ => z ^ δ / Real.log z) atTop atTop := by
  have h0 : Tendsto (fun z : ℝ => Real.log z / z ^ δ) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    have hz0 : (0 : ℝ) < z := by linarith
    exact div_pos (Real.log_pos hz) (Real.rpow_pos_of_pos hz0 δ)
  have h1 := tendsto_inv_nhdsGT_zero.comp h0
  refine h1.congr fun z => ?_
  simp only [Function.comp_apply]
  rw [inv_div]

/-- Above the critical rate the large-prime tail is eventually below one. -/
theorem eventually_largeTail_lt_one (hdisc : B.IsDiscrete) (hpnt : B.HasPrimePNT) {c : ℝ}
    (hc1 : 1 < c) :
    ∀ᶠ z : ℝ in atTop, B.largeTail z (c * Real.log z / z) < 1 := by
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp (eventually_primeCount_le_two_mul hpnt)
  have hlt : ∀ᶠ z : ℝ in atTop, 2 * (z + 1 / (c * Real.log z / z))
      * Real.exp (-(z - 1) * (c * Real.log z / z)) < 1 :=
    (tendsto_largeTailBound hc1).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlt, eventually_ge_atTop y₀, eventually_gt_atTop (1 : ℝ)] with z hz1 hz2 hz3
  have hz0 : (0 : ℝ) < z := by linarith
  have hlog : 0 < Real.log z := Real.log_pos hz3
  have ht : 0 < c * Real.log z / z := div_pos (mul_pos (by linarith) hlog) hz0
  have hbd : ∀ u : ℝ, z ≤ u → (B.primeCount u : ℝ) ≤ 2 * u := fun u hu =>
    hy₀ u (le_trans hz2 hu)
  exact lt_of_le_of_lt (largeTail_le hdisc hz0 ht hbd) hz1

/-- Below the critical rate the large-prime tail is eventually above one. -/
theorem eventually_one_lt_largeTail (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (hpnt : B.HasPrimePNT) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ᶠ z : ℝ in atTop, 1 < B.largeTail z (c * Real.log z / z) := by
  have hcinv : 1 < 1 / c := by
    rw [lt_div_iff₀ hc0]
    linarith
  set K : ℝ := (1 + 1 / c) / 2 with hKdef
  have hK1 : 1 < K := by
    rw [hKdef]
    linarith
  have hcK : c * K < 1 := by
    rw [hKdef]
    have h : c * (1 / c) = 1 := by field_simp
    nlinarith
  have hbig : ∀ᶠ z : ℝ in atTop,
      1 < (K - 1) / 2 * (z ^ (1 - c * K) / Real.log z) :=
    ((tendsto_rpow_div_log_atTop (by linarith : (0 : ℝ) < 1 - c * K)).const_mul_atTop
      (by linarith : (0 : ℝ) < (K - 1) / 2)).eventually_gt_atTop 1
  have hcount : ∀ᶠ z : ℝ in atTop,
      (K - 1) / 2 < ((B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ)) * Real.log z / z :=
    (tendsto_primeCountWindow hpnt hK1).eventually
      (eventually_gt_nhds (by linarith : (K - 1) / 2 < K - 1))
  filter_upwards [hbig, hcount, eventually_gt_atTop (1 : ℝ)] with z h1 h2 h3
  have hz0 : (0 : ℝ) < z := by linarith
  have hlog : 0 < Real.log z := Real.log_pos h3
  have ht : 0 < c * Real.log z / z := div_pos (mul_pos hc0 hlog) hz0
  have hzKz : z ≤ K * z := by nlinarith
  have hlow := le_largeTail hdisc hC hzKz ht
  have hdiff : (K - 1) / 2 * (z / Real.log z)
      ≤ (B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ) := by
    have hpos : 0 < z / Real.log z := div_pos hz0 hlog
    have h := mul_lt_mul_of_pos_right h2 hpos
    have hid : ((B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ)) * Real.log z / z
        * (z / Real.log z) = (B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ) := by
      field_simp
    rw [hid] at h
    exact h.le
  have hzz : z ^ (1 - c * K) = z * z ^ (-(c * K)) := by
    nth_rewrite 2 [← Real.rpow_one z]
    rw [← Real.rpow_add hz0, show (1 : ℝ) + -(c * K) = 1 - c * K by ring]
  have hrpow_pos : (0 : ℝ) < z ^ (-(c * K)) := Real.rpow_pos_of_pos hz0 _
  have hexp : z ^ (-(c * K)) ≤ Real.exp (-(K * z - 1) * (c * Real.log z / z)) := by
    have heq : -(K * z - 1) * (c * Real.log z / z)
        = -(c * K) * Real.log z + c * Real.log z / z := by
      field_simp
      ring
    have h5 : Real.exp (-(c * K) * Real.log z) = z ^ (-(c * K)) := by
      rw [Real.rpow_def_of_pos hz0]
      congr 1
      ring
    have h6 : (1 : ℝ) ≤ Real.exp (c * Real.log z / z) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr ht.le
    rw [heq, Real.exp_add, h5]
    nlinarith
  have hdpos : (0 : ℝ) ≤ (B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ) := by
    have : (0 : ℝ) < (K - 1) / 2 * (z / Real.log z) := by
      have hpos : 0 < z / Real.log z := div_pos hz0 hlog
      have : (0 : ℝ) < (K - 1) / 2 := by linarith
      positivity
    linarith
  calc (1 : ℝ) < (K - 1) / 2 * (z ^ (1 - c * K) / Real.log z) := h1
    _ = ((K - 1) / 2 * (z / Real.log z)) * z ^ (-(c * K)) := by
        rw [hzz]
        field_simp
    _ ≤ ((B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ)) * z ^ (-(c * K)) :=
        mul_le_mul_of_nonneg_right hdiff hrpow_pos.le
    _ ≤ ((B.primeCount (K * z) : ℝ) - (B.primeCount z : ℝ))
          * Real.exp (-(K * z - 1) * (c * Real.log z / z)) :=
        mul_le_mul_of_nonneg_left hexp hdpos
    _ ≤ B.largeTail z (c * Real.log z / z) := hlow

/-! ## The transition asymptotic -/

/-- The prime number theorem forces arbitrarily large generalized primes. -/
theorem nonempty_largeLabel (hpnt : B.HasPrimePNT) (z : ℝ) :
    Nonempty {p : B.Label // z < B.labelNorm p} := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  have hall : ∀ p : B.Label, B.labelNorm p ≤ z := by
    intro p
    by_contra h
    exact hcon.false ⟨p, not_le.mp h⟩
  have hconst : ∀ y : ℝ, z ≤ y → B.primeCount y = B.primeCount z := by
    intro y hy
    rw [primeCount, primeCount]
    congr 1
    ext p
    simp only [Set.mem_setOf_eq]
    exact ⟨fun _ => hall p, fun h => le_trans h hy⟩
  have hlogdiv : Tendsto (fun y : ℝ => Real.log y / y) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    refine h.congr fun y => ?_
    rw [Real.rpow_one]
  have hzero : Tendsto (fun y : ℝ => (B.primeCount y : ℝ) * Real.log y / y) atTop (nhds 0) := by
    have h := hlogdiv.const_mul ((B.primeCount z : ℝ))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop z] with y hy
    rw [hconst y hy]
    ring
  have huniq := tendsto_nhds_unique hpnt hzero
  norm_num at huniq

/-- **The transition asymptotic `(BF8)`.**  Any choice of transition times satisfies
`z τ_z / log z → 1`. -/
theorem tendsto_transition_ratio (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (hpnt : B.HasPrimePNT) {τ : ℝ → ℝ} (hpos : ∀ z : ℝ, 0 < τ z)
    (hfix : ∀ z : ℝ, B.largeTail z (τ z) = 1) :
    Tendsto (fun z : ℝ => z * τ z / Real.log z) atTop (nhds 1) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
      have hz0 : (0 : ℝ) < z := by linarith
      have hlog : 0 < Real.log z := Real.log_pos hz
      have : 0 < z * τ z / Real.log z := div_pos (mul_pos hz0 (hpos z)) hlog
      linarith
    · filter_upwards [eventually_one_lt_largeTail hdisc hC hpnt hb0 hb,
        eventually_gt_atTop (1 : ℝ)] with z hgt hz
      have hz0 : (0 : ℝ) < z := by linarith
      have hlog : 0 < Real.log z := Real.log_pos hz
      have hne := nonempty_largeLabel hpnt z
      have hcmp : b * Real.log z / z < τ z := by
        by_contra hcon
        rcases eq_or_lt_of_le (not_lt.mp hcon) with heq | hlt2
        · rw [← heq, hfix z] at hgt
          exact absurd hgt (lt_irrefl 1)
        · have hstep := largeTail_strictAnti hdisc hC z (hpos z) hlt2 hne
          rw [hfix z] at hstep
          linarith
      have hposq : 0 < z / Real.log z := div_pos hz0 hlog
      have h := mul_lt_mul_of_pos_right hcmp hposq
      rw [show b * Real.log z / z * (z / Real.log z) = b by field_simp,
        show τ z * (z / Real.log z) = z * τ z / Real.log z by ring] at h
      exact h
  · intro b hb
    filter_upwards [eventually_largeTail_lt_one hdisc hpnt hb,
      eventually_gt_atTop (1 : ℝ)] with z hlt hz
    have hz0 : (0 : ℝ) < z := by linarith
    have hlog : 0 < Real.log z := Real.log_pos hz
    have hne := nonempty_largeLabel hpnt z
    have ht : 0 < b * Real.log z / z := div_pos (mul_pos (by linarith) hlog) hz0
    have hcmp : τ z < b * Real.log z / z := by
      by_contra hcon
      rcases eq_or_lt_of_le (not_lt.mp hcon) with heq | hlt2
      · rw [heq, hfix z] at hlt
        exact absurd hlt (lt_irrefl 1)
      · have hstep := largeTail_strictAnti hdisc hC z ht hlt2 hne
        rw [hfix z] at hstep
        linarith
    have hposq : 0 < z / Real.log z := div_pos hz0 hlog
    have h := mul_lt_mul_of_pos_right hcmp hposq
    rw [show b * Real.log z / z * (z / Real.log z) = b by field_simp,
      show τ z * (z / Real.log z) = z * τ z / Real.log z by ring] at h
    exact h

end BeurlingSystem

end RHTower
