import GaloisForLFunctions.RHTower.BaezDuarteGramReduction

/-!
# An exact series for the squared-fractional-part constant

`BaezDuarteGramReduction` reduced the Báez-Duarte Gram diagonal to two scalars, the constant
`fractSqConst = ∫₁^∞ {v}² v^{-2} dv` and the cross tail.  This file evaluates the constant exactly, as a
convergent series, by the only route the tail integral allows: cut the ray at the integers, where the
fractional part is linear, and integrate each piece in closed form.

On `(n+1, n+2)` the fractional part is `v − (n+1)`, so the integrand is
`1 − 2(n+1)/v + (n+1)²/v²`, whose integral over that interval is

`1 + (n+1)/(n+2) − 2(n+1)·log((n+2)/(n+1))`.

Summing over the countable disjoint decomposition of `(1,∞)` gives

**`hasSum_fractSqConst` — `HasSum (fun n => 1 + (n+1)/(n+2) − 2(n+1)·log((n+2)/(n+1))) fractSqConst`.**

The terms are `∼ 1/(3n²)`, so the series converges rapidly; its closed form is the Stirling-type quantity
carrying `log 2π`, which this file does not attempt.  What it does give is the constant as an explicit
elementary object rather than an unevaluated integral — the first of the two scalars named in
`gram-diagonal-reduces-to-two-scalars.md`.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace RHTower

/-- The integer cells of the tail ray. -/
def tailCell (n : ℕ) : Set ℝ := Ioc ((n : ℝ) + 1) ((n : ℝ) + 2)

theorem measurableSet_tailCell (n : ℕ) : MeasurableSet (tailCell n) := measurableSet_Ioc

theorem pairwise_disjoint_tailCell : Pairwise (Function.onFun Disjoint tailCell) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · have hle : (m : ℝ) + 2 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      linarith
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rw [tailCell, mem_Ioc] at hx hx'
    linarith [hx.2, hx'.1]
  · have hle : (n : ℝ) + 2 ≤ (m : ℝ) + 1 := by
      have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      linarith
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rw [tailCell, mem_Ioc] at hx hx'
    linarith [hx.1, hx'.2]

theorem iUnion_tailCell : (⋃ n : ℕ, tailCell n) = Ioi (1 : ℝ) := by
  ext x
  simp only [Set.mem_iUnion, tailCell, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨n, h1, -⟩
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro hx
    have hx0 : (0 : ℝ) < x - 1 := by linarith
    have hm1 : 1 ≤ ⌈x - 1⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      intro h
      rw [Nat.ceil_eq_zero] at h
      linarith)
    refine ⟨⌈x - 1⌉₊ - 1, ?_, ?_⟩
    · have hcast : ((⌈x - 1⌉₊ - 1 : ℕ) : ℝ) + 1 = ((⌈x - 1⌉₊ : ℕ) : ℝ) := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
        ring
      rw [hcast]
      have := Nat.ceil_lt_add_one hx0.le
      linarith
    · have hcast : ((⌈x - 1⌉₊ - 1 : ℕ) : ℝ) + 2 = ((⌈x - 1⌉₊ : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
        ring
      rw [hcast]
      have := Nat.le_ceil (x - 1)
      linarith

/-- On a tail cell the fractional part is linear. -/
theorem fract_eq_sub_of_mem_tailCell {n : ℕ} {v : ℝ} (hv : v ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)) :
    Int.fract v = v - ((n : ℝ) + 1) := by
  have hfloor : ⌊v⌋ = (n : ℤ) + 1 := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · push_cast
      exact hv.1.le
    · push_cast
      linarith [hv.2]
  rw [Int.fract, hfloor]
  push_cast
  ring

/-- **The closed form on one cell.** -/
theorem integral_tailCell_fractSqInvSq (n : ℕ) :
    (∫ v in tailCell n, fractSqInvSq v)
      = 1 + ((n : ℝ) + 1) / ((n : ℝ) + 2)
        - 2 * ((n : ℝ) + 1) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : (0 : ℝ) < a := by rw [ha]; positivity
  have hab : a ≤ a + 1 := by linarith
  have hcongr : ∀ v ∈ Ioo a (a + 1), fractSqInvSq v = 1 - 2 * a * v⁻¹ + a ^ 2 * (v⁻¹) ^ 2 := by
    intro v hv
    have hv0 : (0 : ℝ) < v := lt_trans ha0 hv.1
    have hvne : v ≠ 0 := ne_of_gt hv0
    have hfr : Int.fract v = v - a := by
      refine fract_eq_sub_of_mem_tailCell (n := n) ?_
      rw [← ha]
      exact ⟨hv.1, by linarith [hv.2]⟩
    rw [fractSqInvSq, hfr]
    field_simp
    ring
  have hIcc : tailCell n = Ioc a (a + 1) := by
    rw [tailCell, ha, show ((n : ℝ) + 2) = ((n : ℝ) + 1) + 1 from by ring]
  rw [hIcc, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  have hzero : (0 : ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    intro h
    linarith [h.1]
  have h1 : (∫ v in a..(a + 1), (1 : ℝ)) = 1 := by
    rw [intervalIntegral.integral_const]
    ring
  have h2 : (∫ v in a..(a + 1), v⁻¹) = Real.log ((a + 1) / a) :=
    integral_inv_of_pos ha0 (by linarith)
  have h3 : (∫ v in a..(a + 1), (v⁻¹) ^ 2) = 1 / a - 1 / (a + 1) := by
    have hcongr2 : ∀ v ∈ Set.uIcc a (a + 1), (v⁻¹) ^ 2 = v ^ (-2 : ℤ) := by
      intro v _
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast, ← inv_pow]
    rw [intervalIntegral.integral_congr hcongr2,
      integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    have hane : a ≠ 0 := ne_of_gt ha0
    have hane1 : a + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hpos : ∀ v ∈ Set.uIcc a (a + 1), (0:ℝ) < v := by
    intro v hv
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hv
    linarith [hv.1]
  have hIinv : IntervalIntegrable (fun v : ℝ => v⁻¹) MeasureTheory.volume a (a + 1) :=
    (ContinuousOn.inv₀ continuousOn_id (fun v hv => ne_of_gt (hpos v hv))).intervalIntegrable
  have hIinv2 : IntervalIntegrable (fun v : ℝ => (v⁻¹) ^ 2) MeasureTheory.volume a (a + 1) :=
    ((ContinuousOn.inv₀ continuousOn_id
      (fun v hv => ne_of_gt (hpos v hv))).pow 2).intervalIntegrable
  rw [intervalIntegral.integral_add
      (intervalIntegrable_const.sub (hIinv.const_mul (2 * a))) (hIinv2.const_mul (a ^ 2)),
    intervalIntegral.integral_sub intervalIntegrable_const (hIinv.const_mul (2 * a)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1, h2, h3]
  have hane : a ≠ 0 := ne_of_gt ha0
  have hane1 : a + 1 ≠ 0 := by positivity
  rw [ha]
  field_simp
  ring

/-- **The constant as a convergent series.** -/
theorem hasSum_fractSqConst :
    HasSum (fun n : ℕ => 1 + ((n : ℝ) + 1) / ((n : ℝ) + 2)
      - 2 * ((n : ℝ) + 1) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1))) fractSqConst := by
  have hint : IntegrableOn fractSqInvSq (⋃ n : ℕ, tailCell n) := by
    rw [iUnion_tailCell]
    exact integrableOn_fractSqInvSq_Ioi one_pos
  have h := MeasureTheory.hasSum_integral_iUnion measurableSet_tailCell
    pairwise_disjoint_tailCell hint
  rw [iUnion_tailCell] at h
  have hterm : ∀ n : ℕ, (∫ v in tailCell n, fractSqInvSq v)
      = 1 + ((n : ℝ) + 1) / ((n : ℝ) + 2)
        - 2 * ((n : ℝ) + 1) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) :=
    integral_tailCell_fractSqInvSq
  rw [fractSqConst]
  exact (funext hterm) ▸ h

end RHTower

end
