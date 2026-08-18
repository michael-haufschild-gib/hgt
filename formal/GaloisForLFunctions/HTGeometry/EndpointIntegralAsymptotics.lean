import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Endpoint asymptotics of a primitive

Two transfer laws for the antiderivative `x ↦ ∫_x^b f` at an endpoint where the integrand has a
pure power asymptotic.

* Divergent endpoint: if `f y / y^α → L` as `y → 0⁺` with `α < -1`, then the primitive blows up at
  the exact rate `-L/(α+1) · x^{α+1}`.
* Convergent endpoint: if `h y / (b-y)^β → L` as `y → b⁻` with `β > -1`, then the primitive vanishes
  at the exact rate `L/(β+1) · (b-x)^{β+1}`.

Only local interval integrability of the integrand is assumed; the power comparison supplies
everything else.
-/

open MeasureTheory Set Filter Topology

namespace HTGeometry

/-! ## Powers -/

/-- A positive power tends to zero at the origin from the right. -/
theorem tendsto_rpow_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont : ContinuousAt (fun x : ℝ => x ^ c) 0 :=
    Real.continuousAt_rpow_const 0 c (Or.inr hc.le)
  have h0 : (0 : ℝ) ^ c = 0 := Real.zero_rpow (ne_of_gt hc)
  have hres := hcont.tendsto
  rw [h0] at hres
  exact hres.mono_left nhdsWithin_le_nhds

/-- The exact primitive of a power on an interval avoiding the origin. -/
theorem integral_rpow_of_pos {α x y : ℝ} (hα : α ≠ -1) (hx : 0 < x) (hy : 0 < y) :
    ∫ t in x..y, t ^ α = (y ^ (α + 1) - x ^ (α + 1)) / (α + 1) := by
  refine integral_rpow (Or.inr ⟨hα, ?_⟩)
  intro hmem
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hmem
    exact absurd hmem.1 (not_le.2 hx)
  · rw [uIcc_of_ge h] at hmem
    exact absurd hmem.1 (not_le.2 hy)

/-- Interval integrability of a power away from the origin. -/
theorem intervalIntegrable_rpow_of_pos {α x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fun t : ℝ => t ^ α) volume x y := by
  refine (ContinuousOn.intervalIntegrable ?_)
  refine ContinuousOn.rpow_const continuousOn_id fun t ht => ?_
  refine Or.inl (ne_of_gt ?_)
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at ht
    exact lt_of_lt_of_le hx ht.1
  · rw [uIcc_of_ge h] at ht
    exact lt_of_lt_of_le hy ht.1

/-! ## The divergent endpoint at the origin -/

/-- **Little-o transfer at a divergent endpoint.**  If the integrand is `o(y^α)` at the origin with
`α < -1`, then its primitive from `x` to `b` is `o(x^{α+1})`. -/
theorem tendsto_rpow_mul_intervalIntegral_of_isLittleO {φ : ℝ → ℝ} {α b : ℝ}
    (hα : α < -1) (hb : 0 < b)
    (hint : ∀ x ∈ Ioo (0 : ℝ) b, IntervalIntegrable φ volume x b)
    (hlim : Tendsto (fun y => φ y / y ^ α) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun x => x ^ (-(α + 1)) * ∫ y in x..b, φ y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : 0 < -(α + 1) := by linarith
  set c : ℝ := -(α + 1) with hcdef
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε1 : 0 < ε * c / 2 := by positivity
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim (ε * c / 2) hε1
  set δ : ℝ := min δ₀ b with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos hb
  have hδb : δ ≤ b := min_le_right _ _
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hbound : ∀ y ∈ Ioo (0 : ℝ) δ, |φ y| ≤ (ε * c / 2) * y ^ α := by
    intro y hy
    have hy0 : 0 < y := hy.1
    have hyd : dist y 0 < δ₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hy0]
      exact lt_of_lt_of_le hy.2 hδ₀'
    have hval := hδ₀ (mem_Ioi.2 hy0) hyd
    rw [Real.dist_eq, sub_zero] at hval
    have hpow : 0 < y ^ α := Real.rpow_pos_of_pos hy0 α
    rw [abs_div, abs_of_pos hpow, div_lt_iff₀ hpow] at hval
    exact le_of_lt hval
  set C : ℝ := ∫ y in δ..b, φ y with hCdef
  have hfar : Tendsto (fun x : ℝ => x ^ c * |C|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hz := (tendsto_rpow_nhdsGT_zero hc).mul_const |C|
    simpa using hz
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.1 hfar (ε / 2) (by positivity)
  refine ⟨min δ δ₁, lt_min hδpos hδ₁pos, ?_⟩
  intro x hx hxdist
  have hx0 : 0 < x := hx
  have hxdist' : x < min δ δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hxdist
    exact hxdist
  have hxδ : x < δ := lt_of_lt_of_le hxdist' (min_le_left _ _)
  have hxδ₁ : x < δ₁ := lt_of_lt_of_le hxdist' (min_le_right _ _)
  have hxb : x < b := lt_of_lt_of_le hxδ hδb
  have hint1 : IntervalIntegrable φ volume x δ :=
    (hint x ⟨hx0, hxb⟩).mono_set (by
      rw [uIcc_of_le hxδ.le, uIcc_of_le hxb.le]
      exact Icc_subset_Icc le_rfl hδb)
  have hint2 : IntervalIntegrable φ volume δ b :=
    (hint x ⟨hx0, hxb⟩).mono_set (by
      rw [uIcc_of_le hδb, uIcc_of_le hxb.le]
      exact Icc_subset_Icc hxδ.le le_rfl)
  have hsplit : (∫ y in x..b, φ y) = (∫ y in x..δ, φ y) + C := by
    rw [hCdef]
    exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hpowint : IntervalIntegrable (fun t : ℝ => t ^ α) volume x δ :=
    intervalIntegrable_rpow_of_pos hx0 hδpos
  have hnear : |∫ y in x..δ, φ y| ≤ (ε * c / 2) * ((x ^ (α + 1) - δ ^ (α + 1)) / c) := by
    have habs : |∫ y in x..δ, φ y| ≤ ∫ y in x..δ, |φ y| :=
      intervalIntegral.abs_integral_le_integral_abs hxδ.le
    have hmono : (∫ y in x..δ, |φ y|) ≤ ∫ y in x..δ, (ε * c / 2) * y ^ α := by
      refine intervalIntegral.integral_mono_ae_restrict hxδ.le hint1.abs
        (hpowint.const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        MeasureTheory.ae_restrict_of_ae (volume.ae_ne δ)] with y hy hyne
      exact hbound y ⟨lt_of_lt_of_le hx0 hy.1, lt_of_le_of_ne hy.2 hyne⟩
    have hval : (∫ y in x..δ, (ε * c / 2) * y ^ α)
        = (ε * c / 2) * ((δ ^ (α + 1) - x ^ (α + 1)) / (α + 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow_of_pos (ne_of_lt hα) hx0 hδpos]
    have hrw : (δ ^ (α + 1) - x ^ (α + 1)) / (α + 1)
        = (x ^ (α + 1) - δ ^ (α + 1)) / c := by
      rw [hcdef, div_neg, ← neg_div, neg_sub]
    rw [hval, hrw] at hmono
    exact le_trans habs hmono
  have hxpow : x ^ c * x ^ (α + 1) = 1 := by
    rw [← Real.rpow_add hx0, hcdef]
    simp
  have hδpow : 0 < δ ^ (α + 1) := Real.rpow_pos_of_pos hδpos _
  have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx0 c
  have h1 : |x ^ c * ∫ y in x..δ, φ y| ≤ ε * c / 2 / c := by
    rw [abs_mul, abs_of_pos hxc]
    have hstep := mul_le_mul_of_nonneg_left hnear hxc.le
    refine le_trans hstep ?_
    have hxc' : x ^ c * ((ε * c / 2) * ((x ^ (α + 1) - δ ^ (α + 1)) / c))
        ≤ x ^ c * ((ε * c / 2) * (x ^ (α + 1) / c)) := by
      refine mul_le_mul_of_nonneg_left ?_ hxc.le
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hε1)
      exact div_le_div_of_nonneg_right (by linarith) hc.le
    refine le_trans hxc' ?_
    rw [show x ^ c * ((ε * c / 2) * (x ^ (α + 1) / c))
        = (ε * c / 2 / c) * (x ^ c * x ^ (α + 1)) by ring, hxpow, mul_one]
  have h2 : |x ^ c * C| = x ^ c * |C| := by
    rw [abs_mul, abs_of_pos hxc]
  have hfarbound : x ^ c * |C| < ε / 2 := by
    have hval := hδ₁ (mem_Ioi.2 hx0) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
      exact hxδ₁)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hval
    exact hval
  have harith : ε * c / 2 / c = ε / 2 := by
    field_simp
  rw [Real.dist_eq, sub_zero, hsplit, mul_add]
  calc |x ^ c * (∫ y in x..δ, φ y) + x ^ c * C|
      ≤ |x ^ c * ∫ y in x..δ, φ y| + |x ^ c * C| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by rw [h2, ← harith]; linarith
    _ = ε := by ring

/-- **Exact divergence rate of the primitive at the origin.**  If `f y / y^α → L` at the origin
with `α < -1`, then `x^{-(α+1)} ∫_x^b f → -L/(α+1)`. -/
theorem tendsto_rpow_mul_intervalIntegral_nhdsGT_zero {f : ℝ → ℝ} {α L b : ℝ}
    (hα : α < -1) (hb : 0 < b)
    (hint : ∀ x ∈ Ioo (0 : ℝ) b, IntervalIntegrable f volume x b)
    (hlim : Tendsto (fun y => f y / y ^ α) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun x => x ^ (-(α + 1)) * ∫ y in x..b, f y) (𝓝[>] (0 : ℝ))
      (𝓝 (-L / (α + 1))) := by
  have hc : 0 < -(α + 1) := by linarith
  set c : ℝ := -(α + 1) with hcdef
  have hα1 : α + 1 ≠ 0 := by linarith
  set φ : ℝ → ℝ := fun y => f y - L * y ^ α with hφdef
  have hφint : ∀ x ∈ Ioo (0 : ℝ) b, IntervalIntegrable φ volume x b := by
    intro x hx
    exact (hint x hx).sub ((intervalIntegrable_rpow_of_pos hx.1 hb).const_mul L)
  have hφlim : Tendsto (fun y => φ y / y ^ α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcongr : ∀ y ∈ Ioi (0 : ℝ), φ y / y ^ α = f y / y ^ α - L := by
      intro y hy
      have hpow : (0 : ℝ) < y ^ α := Real.rpow_pos_of_pos hy α
      rw [hφdef]
      field_simp
    have hsub := hlim.sub (tendsto_const_nhds (α := ℝ) (x := L) (f := 𝓝[>] (0 : ℝ)))
    rw [sub_self] at hsub
    refine hsub.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hcongr y hy).symm
  have hlittle := tendsto_rpow_mul_intervalIntegral_of_isLittleO hα hb hφint hφlim
  have hpow : Tendsto (fun x : ℝ => x ^ c * (L * ((b ^ (α + 1) - x ^ (α + 1)) / (α + 1))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-L / (α + 1))) := by
    have hsplit : ∀ x ∈ Ioi (0 : ℝ),
        x ^ c * (L * ((b ^ (α + 1) - x ^ (α + 1)) / (α + 1)))
          = (L * b ^ (α + 1) / (α + 1)) * x ^ c - L / (α + 1) := by
      intro x hx
      have hxpow : x ^ c * x ^ (α + 1) = 1 := by
        rw [← Real.rpow_add hx, hcdef]
        simp
      field_simp
      linear_combination (-L) * hxpow
    have hbase : Tendsto (fun x : ℝ => (L * b ^ (α + 1) / (α + 1)) * x ^ c - L / (α + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (-L / (α + 1))) := by
      have h0 := (tendsto_rpow_nhdsGT_zero hc).const_mul (L * b ^ (α + 1) / (α + 1))
      have hsub := h0.sub_const (L / (α + 1))
      simpa [neg_div] using hsub
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hsplit x hx).symm
  have hsum := hlittle.add hpow
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  have hev : Ioo (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hb
  filter_upwards [hev] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hfint := hint x hx
  have hpint : IntervalIntegrable (fun t : ℝ => L * t ^ α) volume x b :=
    (intervalIntegrable_rpow_of_pos hx0 hb).const_mul L
  have hsplit : (∫ y in x..b, φ y)
      = (∫ y in x..b, f y) - L * ((b ^ (α + 1) - x ^ (α + 1)) / (α + 1)) := by
    rw [hφdef, intervalIntegral.integral_sub hfint hpint,
      intervalIntegral.integral_const_mul, integral_rpow_of_pos (ne_of_lt hα) hx0 hb]
  rw [hsplit]
  ring

/-! ## The convergent endpoint on the left of `b` -/

/-- The primitive of the reflected power. -/
theorem integral_sub_rpow {β b x : ℝ} (hβ : -1 < β) :
    ∫ y in x..b, (b - y) ^ β = (b - x) ^ (β + 1) / (β + 1) := by
  have hβ1 : β + 1 ≠ 0 := by linarith
  have hcomp := intervalIntegral.integral_comp_sub_left (a := x) (b := b)
    (fun u : ℝ => u ^ β) b
  rw [hcomp, sub_self, integral_rpow (Or.inl hβ), Real.zero_rpow hβ1, sub_zero]

/-- Interval integrability of the reflected power. -/
theorem intervalIntegrable_sub_rpow {β b x : ℝ} (hβ : -1 < β) :
    IntervalIntegrable (fun y : ℝ => (b - y) ^ β) volume x b := by
  have hbase : IntervalIntegrable (fun u : ℝ => u ^ β) volume (b - b) (b - x) :=
    intervalIntegral.intervalIntegrable_rpow' hβ
  have hcomp := hbase.comp_sub_left b
  have hsym := hcomp.symm
  simpa using hsym

/-- **Exact vanishing rate of the primitive at a convergent endpoint.**  If
`h y / (b-y)^β → L` as `y → b⁻` with `β > -1`, then `(b-x)^{-(β+1)} ∫_x^b h → L/(β+1)`. -/
theorem tendsto_rpow_mul_intervalIntegral_nhdsLT {h : ℝ → ℝ} {β L a b : ℝ}
    (hβ : -1 < β) (hab : a < b)
    (hint : ∀ x ∈ Ioo a b, IntervalIntegrable h volume x b)
    (hlim : Tendsto (fun y => h y / (b - y) ^ β) (𝓝[<] b) (𝓝 L)) :
    Tendsto (fun x => (b - x) ^ (-(β + 1)) * ∫ y in x..b, h y) (𝓝[<] b)
      (𝓝 (L / (β + 1))) := by
  have hβ1 : 0 < β + 1 := by linarith
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε1 : 0 < ε * (β + 1) / 2 := by positivity
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim (ε * (β + 1) / 2) hε1
  refine ⟨min δ₀ (b - a), lt_min hδ₀pos (by linarith), ?_⟩
  intro x hx hxdist
  have hxb : x < b := hx
  have hxdist' : b - x < min δ₀ (b - a) := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub] at hxdist
    exact hxdist
  have hxδ₀ : b - x < δ₀ := lt_of_lt_of_le hxdist' (min_le_left _ _)
  have hxa : a < x := by
    have := lt_of_lt_of_le hxdist' (min_le_right _ _)
    linarith
  have hbx : 0 < b - x := by linarith
  have hbound : ∀ y ∈ Ioo x b, |h y - L * (b - y) ^ β| ≤ (ε * (β + 1) / 2) * (b - y) ^ β := by
    intro y hy
    have hby : 0 < b - y := by linarith [hy.2]
    have hyd : dist y b < δ₀ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.2]), neg_sub]
      have : b - y < b - x := by linarith [hy.1]
      exact lt_trans this hxδ₀
    have hval := hδ₀ (mem_Iio.2 hy.2) hyd
    rw [Real.dist_eq] at hval
    have hpow : 0 < (b - y) ^ β := Real.rpow_pos_of_pos hby β
    have hrw : h y - L * (b - y) ^ β = (h y / (b - y) ^ β - L) * (b - y) ^ β := by
      field_simp
    rw [hrw, abs_mul, abs_of_pos hpow]
    exact mul_le_mul_of_nonneg_right (le_of_lt hval) hpow.le
  have hhint : IntervalIntegrable h volume x b := hint x ⟨hxa, hxb⟩
  have hpint : IntervalIntegrable (fun y : ℝ => (b - y) ^ β) volume x b :=
    intervalIntegrable_sub_rpow hβ
  have hdiff : IntervalIntegrable (fun y : ℝ => h y - L * (b - y) ^ β) volume x b :=
    hhint.sub (hpint.const_mul L)
  have hsplit : (∫ y in x..b, h y)
      = (∫ y in x..b, (h y - L * (b - y) ^ β)) + L * ((b - x) ^ (β + 1) / (β + 1)) := by
    rw [intervalIntegral.integral_sub hhint (hpint.const_mul L),
      intervalIntegral.integral_const_mul, integral_sub_rpow hβ]
    ring
  have hnear : |∫ y in x..b, (h y - L * (b - y) ^ β)|
      ≤ (ε * (β + 1) / 2) * ((b - x) ^ (β + 1) / (β + 1)) := by
    have habs : |∫ y in x..b, (h y - L * (b - y) ^ β)|
        ≤ ∫ y in x..b, |h y - L * (b - y) ^ β| :=
      intervalIntegral.abs_integral_le_integral_abs hxb.le
    have hmono : (∫ y in x..b, |h y - L * (b - y) ^ β|)
        ≤ ∫ y in x..b, (ε * (β + 1) / 2) * (b - y) ^ β := by
      refine intervalIntegral.integral_mono_ae_restrict hxb.le hdiff.abs
        (hpint.const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        MeasureTheory.ae_restrict_of_ae (volume.ae_ne x),
        MeasureTheory.ae_restrict_of_ae (volume.ae_ne b)] with y hy hynex hyneb
      exact hbound y ⟨lt_of_le_of_ne hy.1 (Ne.symm hynex), lt_of_le_of_ne hy.2 hyneb⟩
    have hval : (∫ y in x..b, (ε * (β + 1) / 2) * (b - y) ^ β)
        = (ε * (β + 1) / 2) * ((b - x) ^ (β + 1) / (β + 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_sub_rpow hβ]
    rw [hval] at hmono
    exact le_trans habs hmono
  have hbxpow : 0 < (b - x) ^ (-(β + 1)) := Real.rpow_pos_of_pos hbx _
  have hcancel : (b - x) ^ (-(β + 1)) * (b - x) ^ (β + 1) = 1 := by
    rw [← Real.rpow_add hbx]
    simp
  rw [Real.dist_eq, hsplit, mul_add]
  have hsecond : (b - x) ^ (-(β + 1)) * (L * ((b - x) ^ (β + 1) / (β + 1))) = L / (β + 1) := by
    field_simp
    linear_combination L * hcancel
  rw [hsecond, add_sub_cancel_right, abs_mul, abs_of_pos hbxpow]
  have hstep := mul_le_mul_of_nonneg_left hnear hbxpow.le
  refine lt_of_le_of_lt hstep ?_
  have hrw : (b - x) ^ (-(β + 1)) * ((ε * (β + 1) / 2) * ((b - x) ^ (β + 1) / (β + 1)))
      = (ε / 2) * ((b - x) ^ (-(β + 1)) * (b - x) ^ (β + 1)) := by
    field_simp
  rw [hrw, hcancel, mul_one]
  linarith

end HTGeometry
