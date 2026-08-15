import GaloisForLFunctions.RHTower.RadialTwoIndexOscillatoryBound
import GaloisForLFunctions.HTGeometry.TwoPhaseOscillatoryProduct

/-!
# The high radial first row: a bounded-variation estimate

For a radial index `r` above the aperture the second factor of a first-row Gram entry is already in
the exterior oscillatory regime, so the entry is a single nonstationary integral

```text
∫ V(x) cos(c ξ_s(r x) + φ) dx
```

whose weight `V` carries the whole first factor.  Nothing about `V` is needed beyond its
**endpoint-plus-total-variation budget**

```text
|V(a)| + |V(b)| + ∫_a^b |V′| ≤ B
```

and its plain mass `∫_a^b |V| ≤ B₁`.  The dilated exterior phase supplies the two facts that turn
these into a decay rate: its speed is at least `r` (`le_dilatedPhaseSpeed`) and its curvature is at
most `(16/9)/(r x³)` (`abs_dilatedRadialPhaseAccel_le`).  The first-derivative test then gives

```text
|∫_a^b V(x) cos(c ξ_s(r x) + φ) dx| ≤ (B/r + 16 B₁/(9 r³))/c ,
```

uniformly in the endpoint, the turning parameter `0 ≤ s ≤ 1/2`, and the bandwidth.  Multiplying by
the `1/r` normalization the exterior expansion puts in front of the second factor turns this into
the `r^{-2}` law of the high radial first row, and the divisor-weighted tail `∑ log r / r²` is a
convergent series whose tails vanish.
-/

open Set MeasureTheory intervalIntegral Filter

open scoped Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- A weight with a finite endpoint-plus-variation budget on `[a,b]`. -/
structure BVWeight (a b B : ℝ) (V V' : ℝ → ℝ) : Prop where
  deriv : ∀ x ∈ Icc a b, HasDerivAt V (V' x) x
  contV : ContinuousOn V (Icc a b)
  contV' : ContinuousOn V' (Icc a b)
  variation : |V a| + |V b| + ∫ x in a..b, |V' x| ≤ B

/-- Beyond the first dilation the curvature of the dilated exterior phase is at most `16/(9r)`, so
the curvature term of the oscillatory budget is controlled by the plain mass of the weight. -/
theorem integral_abs_mul_dilatedRadialPhaseAccel_le {s r a b B₁ : ℝ} {V : ℝ → ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 2 ≤ r) (ha : 1 ≤ a) (hab : a ≤ b)
    (hVc : ContinuousOn V (Icc a b))
    (hmass : ∫ x in a..b, |V x| ≤ B₁) :
    ∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x| ≤ 16 * B₁ / (9 * r) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hVabs : ContinuousOn (fun x => |V x|) (Icc a b) := hVc.abs
  have hAcc : ContinuousOn (fun x => |dilatedRadialPhaseAccel s r x|) (Icc a b) :=
    (continuousOn_dilatedRadialPhaseAccel hs1 hr ha).abs
  have hprodInt : IntervalIntegrable (fun x => |V x| * |dilatedRadialPhaseAccel s r x|)
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact hVabs.mul hAcc
  have hlinInt : IntervalIntegrable (fun x => |V x| * (16 / (9 * r))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact hVabs.mul continuousOn_const
  have hpt : ∀ x ∈ Icc a b,
      |V x| * |dilatedRadialPhaseAccel s r x| ≤ |V x| * (16 / (9 * r)) := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_trans ha hx.1
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hcube : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ hx1
    have hbound := abs_dilatedRadialPhaseAccel_le hs hs1 hr hx1
    have hle : 16 / 9 / (r * x ^ 3) ≤ 16 / (9 * r) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hcube, hr0]
    exact mul_le_mul_of_nonneg_left (hbound.trans hle) (abs_nonneg _)
  have hmono := intervalIntegral.integral_mono_on hab hprodInt hlinInt hpt
  have hval : ∫ x in a..b, |V x| * (16 / (9 * r)) = (∫ x in a..b, |V x|) * (16 / (9 * r)) :=
    intervalIntegral.integral_mul_const _ _
  rw [hval] at hmono
  refine hmono.trans ?_
  have hcoef : (0 : ℝ) ≤ 16 / (9 * r) := by positivity
  have := mul_le_mul_of_nonneg_right hmass hcoef
  refine this.trans (le_of_eq ?_)
  field_simp

/-- **The high radial first row, on a finite interval.**  A weight with endpoint-plus-variation
budget `B` and mass `B₁`, integrated against the dilated exterior oscillation of index `r ≥ 2`,
contributes at most `(B/r + 16 B₁/(9 r³))/c`. -/
theorem abs_integral_highRadial_firstRow_le {s r c φ a b B B₁ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 2 ≤ r) (hc : 0 < c) (ha : 1 ≤ a) (hab : a ≤ b)
    {V V' : ℝ → ℝ} (hV : BVWeight a b B V V')
    (hmass : ∫ x in a..b, |V x| ≤ B₁) :
    |∫ x in a..b, V x * Real.cos (c * dilatedRadialPhase s r x + φ)|
      ≤ (B / r + 16 * B₁ / (9 * r ^ 3)) / c := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hphase : ∀ x ∈ Icc a b,
      HasDerivAt (dilatedRadialPhase s r) (dilatedPhaseSpeed s r x) x := by
    intro x hx
    exact hasDerivAt_dilatedRadialPhase hs (one_lt_mul_of_two_le hr ha hx.1)
  have hspeed : ∀ x ∈ Icc a b,
      HasDerivAt (dilatedPhaseSpeed s r) (dilatedRadialPhaseAccel s r x) x := by
    intro x hx
    exact hasDerivAt_dilatedPhaseSpeed (by linarith) (one_lt_mul_of_two_le hr ha hx.1)
  have hlow : ∀ x ∈ Icc a b, r ≤ |dilatedPhaseSpeed s r x| := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_trans ha hx.1
    have h := le_dilatedPhaseSpeed (s := s) (r := r) (x := x) hs1 hr hx1
    rw [abs_of_nonneg (le_trans hr0.le h)]
    exact h
  have hmain := abs_integral_mul_cos_phase_le_on (a := a) (b := b) (c := c) (φ := φ) (m := r)
    hab hc hr0 hV.deriv hV.contV hV.contV' hphase
    (continuousOn_dilatedPhaseSpeed hr ha) hspeed
    (continuousOn_dilatedRadialPhaseAccel hs1 hr ha) hlow
  refine hmain.trans ?_
  have hVabs : ContinuousOn (fun x => |V x|) (Icc a b) := hV.contV.abs
  have hV'abs : ContinuousOn (fun x => |V' x|) (Icc a b) := hV.contV'.abs
  have hAcc : ContinuousOn (fun x => |dilatedRadialPhaseAccel s r x|) (Icc a b) :=
    (continuousOn_dilatedRadialPhaseAccel hs1 hr ha).abs
  have hint₁ : IntervalIntegrable (fun x => |V' x| / r) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact hV'abs.div_const r
  have hint₂ : IntervalIntegrable
      (fun x => |V x| * |dilatedRadialPhaseAccel s r x| / r ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact (hVabs.mul hAcc).div_const (r ^ 2)
  have hsplit : (∫ x in a..b, (|V' x| / r + |V x| * |dilatedRadialPhaseAccel s r x| / r ^ 2))
      = (∫ x in a..b, |V' x|) / r
        + (∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x|) / r ^ 2 := by
    rw [intervalIntegral.integral_add hint₁ hint₂, intervalIntegral.integral_div,
      intervalIntegral.integral_div]
  rw [hsplit]
  have hcurv := integral_abs_mul_dilatedRadialPhaseAccel_le hs hs1 hr ha hab hV.contV hmass
  have hbudget : |V a| / r + |V b| / r + ((∫ x in a..b, |V' x|) / r
      + (∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x|) / r ^ 2)
      ≤ B / r + 16 * B₁ / (9 * r ^ 3) := by
    have hvar : |V a| / r + |V b| / r + (∫ x in a..b, |V' x|) / r ≤ B / r := by
      have h := div_le_div_of_nonneg_right hV.variation hr0
      calc |V a| / r + |V b| / r + (∫ x in a..b, |V' x|) / r
          = (|V a| + |V b| + ∫ x in a..b, |V' x|) / r := by ring
        _ ≤ B / r := h
    have hsecond : (∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x|) / r ^ 2
        ≤ 16 * B₁ / (9 * r ^ 3) := by
      have h := div_le_div_of_nonneg_right hcurv (by positivity : (0 : ℝ) < r ^ 2)
      refine h.trans (le_of_eq ?_)
      field_simp
      ring
    linarith
  exact div_le_div_of_nonneg_right hbudget hc

/-- **The high radial first row, on the exterior ray.**  The same bound holds for the improper
integral, because it is uniform in the right endpoint. -/
theorem abs_setIntegral_Ioi_highRadial_firstRow_le {s r c φ a B B₁ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 2 ≤ r) (hc : 0 < c) (ha : 1 ≤ a)
    {V V' : ℝ → ℝ}
    (hint : IntegrableOn (fun x => V x * Real.cos (c * dilatedRadialPhase s r x + φ)) (Ioi a))
    (hV : ∀ b, a ≤ b → BVWeight a b B V V')
    (hmass : ∀ b, a ≤ b → ∫ x in a..b, |V x| ≤ B₁) :
    |∫ x in Ioi a, V x * Real.cos (c * dilatedRadialPhase s r x + φ)|
      ≤ (B / r + 16 * B₁ / (9 * r ^ 3)) / c := by
  refine abs_setIntegral_Ioi_le_of_tendsto (L := (B / r + 16 * B₁ / (9 * r ^ 3)) / c)
    (M := fun b => if a ≤ b then (B / r + 16 * B₁ / (9 * r ^ 3)) / c
      else |∫ x in a..b, V x * Real.cos (c * dilatedRadialPhase s r x + φ)|) hint ?_ ?_
  · intro b
    by_cases hb : a ≤ b
    · simp only [hb, if_pos]
      exact abs_integral_highRadial_firstRow_le hs hs1 hr hc ha hb (hV b hb) (hmass b hb)
    · simp only [hb, if_neg, le_refl]
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop a] with b hb
    simp [hb]

/-! ## The divisor-weighted high tail -/

/-- The divisor-weighted high first row is dominated by the tail of `∑ log k / k²`. -/
theorem tsum_weighted_highRadial_le {C d : ℝ} {w G : ℕ → ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hw : ∀ n, 0 ≤ w n) (hwlog : ∀ n, w n ≤ Real.log ((n : ℝ) + 2))
    (hG : ∀ n, |G n| ≤ C * d / ((n : ℝ) + 2) ^ 2) :
    ∑' n : ℕ, w (n + N) * |G (n + N)|
      ≤ C * d * ∑' n : ℕ, Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ 2 := by
  have hmaj : Summable (fun n : ℕ =>
      Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ 2) := by
    have h := (summable_log_shift_div_sq).comp_injective (add_left_injective N)
    refine h.congr fun n => ?_
    push_cast
    ring_nf
  have hbound : ∀ n : ℕ, w (n + N) * |G (n + N)|
      ≤ C * d * (Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ 2) := by
    intro n
    have hcast : ((n + N : ℕ) : ℝ) = (n : ℝ) + (N : ℝ) := by push_cast; ring
    have hpos : (0 : ℝ) < ((n : ℝ) + (N : ℝ) + 2) := by positivity
    have hwn : w (n + N) ≤ Real.log ((n : ℝ) + (N : ℝ) + 2) := by
      have := hwlog (n + N)
      rwa [hcast] at this
    have hGn : |G (n + N)| ≤ C * d / ((n : ℝ) + (N : ℝ) + 2) ^ 2 := by
      have := hG (n + N)
      rwa [hcast] at this
    have hGnn : 0 ≤ |G (n + N)| := abs_nonneg _
    calc w (n + N) * |G (n + N)|
        ≤ Real.log ((n : ℝ) + (N : ℝ) + 2) * (C * d / ((n : ℝ) + (N : ℝ) + 2) ^ 2) := by
          refine mul_le_mul hwn hGn hGnn ?_
          exact Real.log_nonneg (by linarith)
      _ = C * d * (Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ 2) := by ring
  have hnonneg : ∀ n : ℕ, 0 ≤ w (n + N) * |G (n + N)| :=
    fun n => mul_nonneg (hw _) (abs_nonneg _)
  have hsum : Summable (fun n : ℕ => w (n + N) * |G (n + N)|) :=
    Summable.of_nonneg_of_le hnonneg hbound (hmaj.mul_left (C * d))
  refine hsum.tsum_le_tsum hbound (hmaj.mul_left (C * d)) |>.trans (le_of_eq ?_)
  exact (hmaj.tsum_mul_left (C * d)).symm

/-- **The divisor-weighted high first row vanishes.**  The tails of `∑ log k / k²` tend to zero, so
a family of entries obeying `|G(1,k)| ≤ C d / k²` beyond the aperture contributes `o(d)`. -/
theorem tendsto_tsum_log_shift_div_sq_tail :
    Tendsto (fun N : ℕ => ∑' n : ℕ, Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ 2)
      atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun n : ℕ => Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) ^ 2)
  refine h.congr fun N => ?_
  refine tsum_congr fun n => ?_
  push_cast
  ring_nf

end GaloisForLFunctions.RHTower

end
