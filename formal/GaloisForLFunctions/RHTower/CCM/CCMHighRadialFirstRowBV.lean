import GaloisForLFunctions.RHTower.RadialTwoIndexOscillatoryBound
import GaloisForLFunctions.HTGeometry.TwoPhaseOscillatoryProduct
import GaloisForLFunctions.RHTower.RadialGramOffDiagonalDecay

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

/-! ## Two exterior power integrals -/

private theorem hasDerivAt_neg_two_div_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => -(2 * (Real.sqrt t)⁻¹)) (1 / (x * Real.sqrt x)) x := by
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hinv : HasDerivAt (fun t : ℝ => (Real.sqrt t)⁻¹)
      (-(1 / (2 * Real.sqrt x)) / Real.sqrt x ^ (2 : ℕ)) x := hs.inv hsx
  have h := (hinv.const_mul (2 : ℝ)).neg
  refine h.congr_deriv ?_
  rw [Real.sq_sqrt hx.le]
  field_simp

theorem hasDerivAt_neg_inv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => -t⁻¹) (1 / x ^ (2 : ℕ)) x := by
  have h := ((hasDerivAt_id x).inv hx).neg
  refine h.congr_deriv ?_
  simp only [id_eq]
  field_simp

/-- `∫_a^b x^{-3/2} ≤ 2/√a`. -/
theorem integral_one_div_mul_sqrt_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / (x * Real.sqrt x)) ≤ 2 / Real.sqrt a := by
  have hcont : ContinuousOn (fun x : ℝ => 1 / (x * Real.sqrt x)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine ContinuousOn.div continuousOn_const
      (continuous_id.continuousOn.mul Real.continuous_sqrt.continuousOn) ?_
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le ha hy.1
    positivity
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => -(2 * (Real.sqrt t)⁻¹)) (1 / (x * Real.sqrt x)) x := by
    rw [uIcc_of_le hab]
    intro x hx
    exact hasDerivAt_neg_two_div_sqrt (lt_of_lt_of_le ha hx.1)
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable)
  rw [hval]
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hsb : (0 : ℝ) < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsa : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
  have : (0 : ℝ) < 2 * (Real.sqrt b)⁻¹ := by positivity
  rw [div_eq_mul_inv]
  linarith

/-- `∫_a^b x^{-2} ≤ 1/a`. -/
theorem integral_one_div_sq_le' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / x ^ (2 : ℕ)) ≤ 1 / a := by
  have hcont : ContinuousOn (fun x : ℝ => 1 / x ^ (2 : ℕ)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine ContinuousOn.div continuousOn_const (continuousOn_pow 2) ?_
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le ha hy.1
    positivity
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun t : ℝ => -t⁻¹) (1 / x ^ (2 : ℕ)) x := by
    rw [uIcc_of_le hab]
    intro x hx
    exact hasDerivAt_neg_inv (ne_of_gt (lt_of_lt_of_le ha hx.1))
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hval]
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have : (0 : ℝ) < b⁻¹ := by positivity
  rw [one_div]
  linarith

/-- **The BV budget of a half-power symbol.**  A weight obeying `|V| ≤ P x^{-3/2}` and
`|V′| ≤ P′ x^{-2}` beyond the first dilation has endpoint-plus-variation budget `2P + P′` and
mass `2P`.  This is the shape the exterior Bessel envelope of a first-row factor produces, with
`P′` carrying the one power of the bandwidth that the differentiated oscillation contributes. -/
theorem bvWeight_of_symbol {a b P P' : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {V V' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt V (V' x) x)
    (hVc : ContinuousOn V (Icc a b)) (hV'c : ContinuousOn V' (Icc a b))
    (hbound : ∀ x ∈ Icc a b, |V x| ≤ P / (x * Real.sqrt x))
    (hbound' : ∀ x ∈ Icc a b, |V' x| ≤ P' / x ^ (2 : ℕ)) :
    BVWeight a b (2 * P + P') V V' ∧ (∫ x in a..b, |V x|) ≤ 2 * P := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb1 : (1 : ℝ) ≤ b := le_trans ha hab
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb1
  have hsa : (1 : ℝ) ≤ Real.sqrt a := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ha
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hP0 : 0 ≤ P := by
    have h0 := (abs_nonneg (V a)).trans (hbound a ⟨le_refl a, hab⟩)
    have hpos : (0 : ℝ) < a * Real.sqrt a := by positivity
    have := mul_nonneg h0 hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  have hP'0 : 0 ≤ P' := by
    have h0 := (abs_nonneg (V' a)).trans (hbound' a ⟨le_refl a, hab⟩)
    have hpos : (0 : ℝ) < a ^ (2 : ℕ) := by positivity
    have := mul_nonneg h0 hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  -- the two majorant integrals
  have hVabsInt : IntervalIntegrable (fun x => |V x|) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hVc.abs
  have hV'absInt : IntervalIntegrable (fun x => |V' x|) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hV'c.abs
  have hmajInt : IntervalIntegrable (fun x : ℝ => P * (1 / (x * Real.sqrt x))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha0 hx.1
    refine ContinuousAt.continuousWithinAt ?_
    have : ContinuousAt (fun t : ℝ => P * (1 / (t * Real.sqrt t))) x := by
      have hne : x * Real.sqrt x ≠ 0 := by positivity
      fun_prop (disch := assumption)
    exact this
  have hmaj'Int : IntervalIntegrable (fun x : ℝ => P' * (1 / x ^ (2 : ℕ))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha0 hx.1
    refine ContinuousAt.continuousWithinAt ?_
    have hne : x ^ (2 : ℕ) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have hmass : (∫ x in a..b, |V x|) ≤ 2 * P := by
    have hmono : (∫ x in a..b, |V x|) ≤ ∫ x in a..b, P * (1 / (x * Real.sqrt x)) := by
      refine intervalIntegral.integral_mono_on hab hVabsInt hmajInt fun x hx => ?_
      have := hbound x hx
      rw [mul_one_div]
      exact this
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have h := integral_one_div_mul_sqrt_le ha0 hab
    have h2 : (2 : ℝ) / Real.sqrt a ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    nlinarith [h, h2, hP0]
  refine ⟨⟨hderiv, hVc, hV'c, ?_⟩, hmass⟩
  have hvar : (∫ x in a..b, |V' x|) ≤ P' := by
    have hmono : (∫ x in a..b, |V' x|) ≤ ∫ x in a..b, P' * (1 / x ^ (2 : ℕ)) := by
      refine intervalIntegral.integral_mono_on hab hV'absInt hmaj'Int fun x hx => ?_
      rw [mul_one_div]
      exact hbound' x hx
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have h := integral_one_div_sq_le' ha0 hab
    have h2 : (1 : ℝ) / a ≤ 1 := by
      rw [div_le_one ha0]; exact ha
    have hkey : P' * (∫ x in a..b, 1 / x ^ (2 : ℕ)) ≤ P' * 1 :=
      mul_le_mul_of_nonneg_left (h.trans h2) hP'0
    linarith [hkey]
  have hVa : |V a| ≤ P := by
    refine (hbound a ⟨le_refl a, hab⟩).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ a * Real.sqrt a := by nlinarith [ha, hsa]
    have := mul_le_mul_of_nonneg_left h1 hP0
    linarith
  have hVb : |V b| ≤ P := by
    have hsb : (1 : ℝ) ≤ Real.sqrt b := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hb1
    refine (hbound b ⟨hab, le_refl b⟩).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ b * Real.sqrt b := by nlinarith [hb1, hsb]
    have := mul_le_mul_of_nonneg_left h1 hP0
    linarith
  linarith

/-- **The symbol class of a first-row weight.**  The weight of a first-row entry is
`V = U · A / x`, where `U` is the whole first factor and `A` one exterior amplitude of the second.
If `|U| ≤ Q/√x` with `|U′| ≤ Q′/√x` — the derivative carrying the bandwidth of the first factor's
own oscillation — and `|A| ≤ R/√x` with `|A′| ≤ R′/(x√x)`, then `V` lies in the symbol class of
`bvWeight_of_symbol` with `P = QR` and `P′ = Q′R + QR′ + QR`. -/
theorem firstRowWeight_symbol_bounds {Q Q' R R' x : ℝ} {U U' A A' : ℝ → ℝ}
    (hx : 1 ≤ x)
    (hQ : |U x| ≤ Q / Real.sqrt x) (hQ' : |U' x| ≤ Q' / Real.sqrt x)
    (hR : |A x| ≤ R / Real.sqrt x) (hR' : |A' x| ≤ R' / (x * Real.sqrt x)) :
    |U x * A x / x| ≤ Q * R / (x * Real.sqrt x) ∧
      |(U' x * A x + U x * A' x) / x - U x * A x / x ^ (2 : ℕ)|
        ≤ (Q' * R + Q * R' + Q * R) / x ^ (2 : ℕ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx
  have hsx0 : (0 : ℝ) < Real.sqrt x := lt_of_lt_of_le zero_lt_one hsx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  -- the four constants are nonnegative
  have hQ0 : 0 ≤ Q := by
    have h0 := (abs_nonneg (U x)).trans hQ
    have := mul_nonneg h0 hsx0.le
    rwa [div_mul_cancel₀ _ hsx0.ne'] at this
  have hQ'0 : 0 ≤ Q' := by
    have h0 := (abs_nonneg (U' x)).trans hQ'
    have := mul_nonneg h0 hsx0.le
    rwa [div_mul_cancel₀ _ hsx0.ne'] at this
  have hR0 : 0 ≤ R := by
    have h0 := (abs_nonneg (A x)).trans hR
    have := mul_nonneg h0 hsx0.le
    rwa [div_mul_cancel₀ _ hsx0.ne'] at this
  have hR'0 : 0 ≤ R' := by
    have h0 := (abs_nonneg (A' x)).trans hR'
    have hpos : (0 : ℝ) < x * Real.sqrt x := by positivity
    have := mul_nonneg h0 hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  -- the three products
  have hUA : |U x| * |A x| ≤ Q * R / x := by
    have h := mul_le_mul hQ hR (abs_nonneg _) (by positivity)
    refine h.trans (le_of_eq ?_)
    rw [div_mul_div_comm, hsq]
  have hU'A : |U' x| * |A x| ≤ Q' * R / x := by
    have h := mul_le_mul hQ' hR (abs_nonneg _) (by positivity)
    refine h.trans (le_of_eq ?_)
    rw [div_mul_div_comm, hsq]
  have hUA' : |U x| * |A' x| ≤ Q * R' / x ^ (2 : ℕ) := by
    have h := mul_le_mul hQ hR' (abs_nonneg _) (by positivity)
    refine h.trans (le_of_eq ?_)
    rw [div_mul_div_comm]
    congr 1
    rw [show Real.sqrt x * (x * Real.sqrt x) = x * (Real.sqrt x * Real.sqrt x) by ring, hsq]
    ring
  constructor
  · rw [abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 (by positivity), abs_mul]
    have hstep : |U x| * |A x| * (x * Real.sqrt x) ≤ (Q * R / x) * (x * Real.sqrt x) :=
      mul_le_mul_of_nonneg_right hUA (by positivity)
    refine hstep.trans ?_
    have hval : Q * R / x * (x * Real.sqrt x) = Q * R * Real.sqrt x := by
      field_simp
    rw [hval]
    have hsxx : Real.sqrt x ≤ x := by nlinarith [hsq, hsx, hsx0]
    have := mul_le_mul_of_nonneg_left hsxx (mul_nonneg hQ0 hR0)
    linarith
  · have hnum : |U' x * A x + U x * A' x| ≤ |U' x| * |A x| + |U x| * |A' x| := by
      calc |U' x * A x + U x * A' x| ≤ |U' x * A x| + |U x * A' x| := abs_add_le _ _
        _ = |U' x| * |A x| + |U x| * |A' x| := by rw [abs_mul, abs_mul]
    have hsplit : |(U' x * A x + U x * A' x) / x - U x * A x / x ^ (2 : ℕ)|
        ≤ (|U' x| * |A x| + |U x| * |A' x|) / x + |U x| * |A x| / x ^ (2 : ℕ) := by
      refine (abs_sub _ _).trans ?_
      have h1 : |(U' x * A x + U x * A' x) / x| ≤ (|U' x| * |A x| + |U x| * |A' x|) / x := by
        rw [abs_div, abs_of_pos hx0]
        gcongr
      have h2 : |U x * A x / x ^ (2 : ℕ)| ≤ |U x| * |A x| / x ^ (2 : ℕ) := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ (2 : ℕ)), abs_mul]
      linarith
    refine hsplit.trans ?_
    have hb1 : (|U' x| * |A x| + |U x| * |A' x|) / x
        ≤ (Q' * R / x + Q * R' / x ^ (2 : ℕ)) / x := by gcongr
    have hb2 : |U x| * |A x| / x ^ (2 : ℕ) ≤ (Q * R / x) / x ^ (2 : ℕ) := by gcongr
    refine (add_le_add hb1 hb2).trans ?_
    have hcube : x ^ (2 : ℕ) ≤ x ^ (3 : ℕ) := by nlinarith [hx0, hx]
    have hx2pos : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
    have e1 : (Q' * R / x + Q * R' / x ^ (2 : ℕ)) / x = Q' * R / x ^ (2 : ℕ) + Q * R' / x ^ (3 : ℕ) := by
      field_simp
    have e2 : Q * R / x / x ^ (2 : ℕ) = Q * R / x ^ (3 : ℕ) := by
      field_simp
    have e3 : (Q' * R + Q * R' + Q * R) / x ^ (2 : ℕ)
        = Q' * R / x ^ (2 : ℕ) + Q * R' / x ^ (2 : ℕ) + Q * R / x ^ (2 : ℕ) := by
      field_simp
    rw [e1, e2, e3]
    have h1 : Q * R' / x ^ (3 : ℕ) ≤ Q * R' / x ^ (2 : ℕ) := by gcongr
    have h2 : Q * R / x ^ (3 : ℕ) ≤ Q * R / x ^ (2 : ℕ) := by gcongr
    linarith

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
    have hcube : (1 : ℝ) ≤ x ^ (3 : ℕ) := one_le_pow₀ hx1
    have hbound := abs_dilatedRadialPhaseAccel_le hs hs1 hr hx1
    have hle : 16 / 9 / (r * x ^ (3 : ℕ)) ≤ 16 / (9 * r) := by
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
      ≤ (B / r + 16 * B₁ / (9 * r ^ (3 : ℕ))) / c := by
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
      (fun x => |V x| * |dilatedRadialPhaseAccel s r x| / r ^ (2 : ℕ)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact (hVabs.mul hAcc).div_const (r ^ (2 : ℕ))
  have hsplit : (∫ x in a..b, (|V' x| / r + |V x| * |dilatedRadialPhaseAccel s r x| / r ^ (2 : ℕ)))
      = (∫ x in a..b, |V' x|) / r
        + (∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x|) / r ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_add hint₁ hint₂, intervalIntegral.integral_div,
      intervalIntegral.integral_div]
  rw [hsplit]
  have hcurv := integral_abs_mul_dilatedRadialPhaseAccel_le hs hs1 hr ha hab hV.contV hmass
  have hbudget : |V a| / r + |V b| / r + ((∫ x in a..b, |V' x|) / r
      + (∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x|) / r ^ (2 : ℕ))
      ≤ B / r + 16 * B₁ / (9 * r ^ (3 : ℕ)) := by
    have hvar : |V a| / r + |V b| / r + (∫ x in a..b, |V' x|) / r ≤ B / r := by
      calc |V a| / r + |V b| / r + (∫ x in a..b, |V' x|) / r
          = (|V a| + |V b| + ∫ x in a..b, |V' x|) / r := by ring
        _ ≤ B / r := by gcongr; exact hV.variation
    have hsecond : (∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x|) / r ^ (2 : ℕ)
        ≤ 16 * B₁ / (9 * r ^ (3 : ℕ)) := by
      have h : (∫ x in a..b, |V x| * |dilatedRadialPhaseAccel s r x|) / r ^ (2 : ℕ)
          ≤ (16 * B₁ / (9 * r)) / r ^ (2 : ℕ) := by gcongr
      refine h.trans (le_of_eq ?_)
      field_simp
    linarith
  gcongr

/-- **The high radial first row, on the exterior ray.**  The same bound holds for the improper
integral, because it is uniform in the right endpoint. -/
theorem abs_setIntegral_Ioi_highRadial_firstRow_le {s r c φ a B B₁ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 2 ≤ r) (hc : 0 < c) (ha : 1 ≤ a)
    {V V' : ℝ → ℝ}
    (hint : IntegrableOn (fun x => V x * Real.cos (c * dilatedRadialPhase s r x + φ)) (Ioi a))
    (hV : ∀ b, a ≤ b → BVWeight a b B V V')
    (hmass : ∀ b, a ≤ b → ∫ x in a..b, |V x| ≤ B₁) :
    |∫ x in Ioi a, V x * Real.cos (c * dilatedRadialPhase s r x + φ)|
      ≤ (B / r + 16 * B₁ / (9 * r ^ (3 : ℕ))) / c := by
  refine abs_setIntegral_Ioi_le_of_tendsto (L := (B / r + 16 * B₁ / (9 * r ^ (3 : ℕ))) / c)
    (M := fun b => if a ≤ b then (B / r + 16 * B₁ / (9 * r ^ (3 : ℕ))) / c
      else |∫ x in a..b, V x * Real.cos (c * dilatedRadialPhase s r x + φ)|) hint ?_ ?_
  · intro b
    by_cases hb : a ≤ b
    · rw [if_pos hb]
      exact abs_integral_highRadial_firstRow_le hs hs1 hr hc ha hb (hV b hb) (hmass b hb)
    · rw [if_neg hb]
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop a] with b hb
    simp [hb]

/-! ## The divisor-weighted high tail -/

/-- The divisor-weighted majorant of a first row obeying `|G(1,k)| ≤ C d / k²` is summable. -/
theorem summable_highRadial_logMajorant :
    Summable (fun n : ℕ => Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    _root_.RHTower.summable_weighted_rowMajorant
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    positivity
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hpos : (0 : ℝ) < ((n : ℝ) + 2) ^ (2 : ℕ) := by positivity
    rw [div_le_div_iff_of_pos_right hpos]
    nlinarith [hlog]

/-- The divisor-weighted high first row is dominated by the tail of `∑ log k / k²`. -/
theorem tsum_weighted_highRadial_le {C d : ℝ} {w G : ℕ → ℝ} (N : ℕ)
    (hw : ∀ n, 0 ≤ w n) (hwlog : ∀ n, w n ≤ Real.log ((n : ℝ) + 2))
    (hG : ∀ n, |G n| ≤ C * d / ((n : ℝ) + 2) ^ (2 : ℕ)) :
    ∑' n : ℕ, w (n + N) * |G (n + N)|
      ≤ C * d * ∑' n : ℕ, Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ (2 : ℕ) := by
  have hmaj : Summable (fun n : ℕ =>
      Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ (2 : ℕ)) := by
    have h := summable_highRadial_logMajorant.comp_injective (add_left_injective N)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  have hbound : ∀ n : ℕ, w (n + N) * |G (n + N)|
      ≤ C * d * (Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ (2 : ℕ)) := by
    intro n
    have hcast : ((n + N : ℕ) : ℝ) = (n : ℝ) + (N : ℝ) := by push_cast; ring
    have hpos : (0 : ℝ) < ((n : ℝ) + (N : ℝ) + 2) := by positivity
    have hwn : w (n + N) ≤ Real.log ((n : ℝ) + (N : ℝ) + 2) := by
      have := hwlog (n + N)
      rwa [hcast] at this
    have hGn : |G (n + N)| ≤ C * d / ((n : ℝ) + (N : ℝ) + 2) ^ (2 : ℕ) := by
      have := hG (n + N)
      rwa [hcast] at this
    have hGnn : 0 ≤ |G (n + N)| := abs_nonneg _
    calc w (n + N) * |G (n + N)|
        ≤ Real.log ((n : ℝ) + (N : ℝ) + 2) * (C * d / ((n : ℝ) + (N : ℝ) + 2) ^ (2 : ℕ)) := by
          refine mul_le_mul hwn hGn hGnn ?_
          exact Real.log_nonneg (by linarith)
      _ = C * d * (Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ (2 : ℕ)) := by ring
  have hnonneg : ∀ n : ℕ, 0 ≤ w (n + N) * |G (n + N)| :=
    fun n => mul_nonneg (hw _) (abs_nonneg _)
  have hsum : Summable (fun n : ℕ => w (n + N) * |G (n + N)|) :=
    Summable.of_nonneg_of_le hnonneg hbound (hmaj.mul_left (C * d))
  refine hsum.tsum_le_tsum hbound (hmaj.mul_left (C * d)) |>.trans (le_of_eq ?_)
  exact hmaj.tsum_mul_left (C * d)

/-- **The divisor-weighted high first row vanishes.**  The tails of `∑ log k / k²` tend to zero, so
a family of entries obeying `|G(1,k)| ≤ C d / k²` beyond the aperture contributes `o(d)`. -/
theorem tendsto_tsum_log_shift_div_sq_tail :
    Tendsto (fun N : ℕ => ∑' n : ℕ, Real.log ((n : ℝ) + (N : ℝ) + 2) / ((n : ℝ) + (N : ℝ) + 2) ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun n : ℕ => Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) ^ (2 : ℕ))
  refine h.congr fun N => ?_
  refine tsum_congr fun n => ?_
  push_cast
  ring_nf

end GaloisForLFunctions.RHTower

end
