import GaloisForLFunctions.RHTower.SuzukiCoalescingXiSourceRate
import GaloisForLFunctions.RHTower.SuzukiGroundResiduePolarizationSelection
import Mathlib.Analysis.Calculus.LHopital

/-!
# Coalescing-anchor parity rates and exact endpoint selection

This module upgrades movable-anchor parity purification from a qualitative endpoint limit to the
sharp rate seen by the Xi target.  If the first visible even and odd source degrees are `r` and
`s`, the oriented endpoint gap has order `2|r-s|` with the exact residue ratio as coefficient.
Opposite parity forces `|r-s|` odd, hence the sole quadratic resonance is the adjacent case.

The free interval endpoint is treated at the same scale: `2ac / sinh(2ac)` has normalized gap
`a²/3`.  Combining these exact limits with the theta-source rate gives the strict endpoint
ordering and a dependency-closed intermediate-value selector.  These are the rate-sensitive
parts of Theorems A and B; no open operator-existence or cofinal locking statement is assumed.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- Opposite first-visible parities leave either the adjacent gap or a gap of at least three. -/
theorem suzuki_firstVisibleParity_gap_odd_and_eq_one_or_ge_three
    {r s : ℕ} (hr : Even r) (hs : Odd s) :
    Odd (Nat.dist r s) ∧
      (Nat.dist r s = 1 ∨ 3 ≤ Nat.dist r s) := by
  rcases hr with ⟨r, rfl⟩
  rcases hs with ⟨s, rfl⟩
  constructor
  · rw [Nat.odd_iff]
    unfold Nat.dist
    omega
  · unfold Nat.dist
    omega

private theorem tendsto_real_sinh_div_self_zero :
    Tendsto (fun y : ℝ => Real.sinh y / y) (𝓝[≠] 0) (𝓝 1) := by
  have h := Real.hasDerivAt_sinh 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [Real.cosh_zero] at h
  refine h.congr (fun y => ?_)
  rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]

private theorem tendsto_real_sinh_sub_self_div_cube_zero :
    Tendsto (fun y : ℝ => (Real.sinh y - y) / y ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
  have hbase : Tendsto (fun y : ℝ => Real.sinh y / (y * 6))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    simpa only [div_div] using tendsto_real_sinh_div_self_zero.div_const 6
  have hcosh : Tendsto (fun y : ℝ => (Real.cosh y - 1) / (3 * y ^ 2))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => Real.sinh y) (g' := fun y : ℝ => y * 6)
      ?_ ?_ ?_ ?_ ?_ hbase
    · exact Filter.Eventually.of_forall fun y => (Real.hasDerivAt_cosh y).sub_const 1
    · exact Filter.Eventually.of_forall fun y => by
        exact (((hasDerivAt_id y).pow 2).const_mul 3).congr_deriv (by
          simp only [Function.id_def]
          ring)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      exact mul_ne_zero hy (by norm_num)
    · have hcont : ContinuousAt (fun y : ℝ => Real.cosh y - 1) 0 := by fun_prop
      have ht : Tendsto (fun y : ℝ => Real.cosh y - 1) (𝓝 0) (𝓝 0) := by
        simpa using hcont.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    · have hcont : ContinuousAt (fun y : ℝ => 3 * y ^ 2) 0 := by fun_prop
      have ht : Tendsto (fun y : ℝ => 3 * y ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using hcont.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun y : ℝ => Real.cosh y - 1) (g' := fun y : ℝ => 3 * y ^ 2)
    ?_ ?_ ?_ ?_ ?_ hcosh
  · exact Filter.Eventually.of_forall fun y =>
      (Real.hasDerivAt_sinh y).sub (hasDerivAt_id y)
  · exact Filter.Eventually.of_forall fun y => hasDerivAt_pow 3 y
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
  · have hcont : ContinuousAt (fun y : ℝ => Real.sinh y - y) 0 := by fun_prop
    have ht : Tendsto (fun y : ℝ => Real.sinh y - y) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  · have hcont : ContinuousAt (fun y : ℝ => y ^ 3) 0 := by fun_prop
    have ht : Tendsto (fun y : ℝ => y ^ 3) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto
    exact ht.mono_left nhdsWithin_le_nhds

/-- Free exponential polarization at aperture `a` and movable anchor `c`. -/
def suzukiCoalescingFreeDefect (a c : ℝ) : ℝ :=
  2 * a * c / Real.sinh (2 * a * c)

/-- Sharp quadratic free-endpoint coefficient. -/
theorem tendsto_suzukiCoalescingFreeDefect_rate {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun c : ℝ => (1 - suzukiCoalescingFreeDefect a c) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (a ^ 2 / 3)) := by
  have hscale : Tendsto (fun c : ℝ => 2 * a * c)
      (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : ContinuousAt (fun c : ℝ => 2 * a * c) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') hc.ne'
  have hcube := tendsto_real_sinh_sub_self_div_cube_zero.comp hscale
  have hself := tendsto_real_sinh_div_self_zero.comp hscale
  have hratio := hcube.div hself one_ne_zero
  have hconst : Tendsto (fun _ : ℝ => 2 * a ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * a ^ 2)) := tendsto_const_nhds
  have hmain := hratio.mul hconst
  convert hmain using 1
  · funext c
    change (1 - suzukiCoalescingFreeDefect a c) / (2 * c ^ 2) =
      (((Real.sinh (2 * a * c) - 2 * a * c) / (2 * a * c) ^ 3) /
        (Real.sinh (2 * a * c) / (2 * a * c))) * (2 * a ^ 2)
    by_cases hc : c = 0
    · simp [hc, suzukiCoalescingFreeDefect]
    · have hsinh : Real.sinh (2 * a * c) ≠ 0 := by
        exact Real.sinh_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') hc)
      rw [suzukiCoalescingFreeDefect]
      field_simp [hc, ha.ne', hsinh]
  · ring

/-- The free endpoint converges to pure even polarization. -/
theorem tendsto_suzukiCoalescingFreeDefect_one {a : ℝ} (ha : 0 < a) :
    Tendsto (suzukiCoalescingFreeDefect a)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hscale : Tendsto (fun c : ℝ => 2 * a * c)
      (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : ContinuousAt (fun c : ℝ => 2 * a * c) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') hc.ne'
  have hinv := tendsto_real_sinh_div_self_zero.inv₀ one_ne_zero
  have h := hinv.comp hscale
  have h' : Tendsto
      ((fun y : ℝ => (Real.sinh y / y)⁻¹) ∘ fun c : ℝ => 2 * a * c)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using h
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have harg : 2 * a * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') hc.ne'
  rw [suzukiCoalescingFreeDefect]
  simp only [Function.comp_apply]
  rw [inv_div]

/-- Sharp even-leading ground-polarization rate. -/
theorem tendsto_suzukiDefectAngle_evenLeading_rate
    {evenEnergy oddEnergy : ℝ → ℝ} {r s : ℕ} {A B : ℝ}
    (hrs : r < s) (hA : 0 < A)
    (henergy : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      0 < evenEnergy c + oddEnergy c)
    (heven : Tendsto (fun c : ℝ => evenEnergy c / c ^ (2 * r))
      (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hodd : Tendsto (fun c : ℝ => oddEnergy c / c ^ (2 * s))
      (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    Tendsto
      (fun c : ℝ =>
        (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          (evenEnergy c) (oddEnergy c)) /
            (2 * c ^ (2 * (s - r))))
      (𝓝[>] (0 : ℝ)) (𝓝 (B / A)) := by
  have hpow : Tendsto (fun c : ℝ => c ^ (2 * (s - r)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun c : ℝ => c ^ (2 * (s - r))) 0 := by fun_prop
    have hd : 0 < 2 * (s - r) := by omega
    simpa [zero_pow hd.ne'] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hden := heven.add (hpow.mul hodd)
  have hratio := hodd.div hden (by simpa using hA.ne')
  have hratio' : Tendsto
      ((fun c : ℝ => oddEnergy c / c ^ (2 * s)) /
        (fun c : ℝ => evenEnergy c / c ^ (2 * r) +
          c ^ (2 * (s - r)) * (oddEnergy c / c ^ (2 * s))))
      (𝓝[>] (0 : ℝ)) (𝓝 (B / A)) := by
    simpa using hratio
  apply hratio'.congr'
  filter_upwards [self_mem_nhdsWithin, henergy] with c hc hsum
  have hcne : c ≠ 0 := hc.ne'
  change (oddEnergy c / c ^ (2 * s)) /
      (evenEnergy c / c ^ (2 * r) +
        c ^ (2 * (s - r)) * (oddEnergy c / c ^ (2 * s))) =
    (1 - (evenEnergy c - oddEnergy c) /
      (evenEnergy c + oddEnergy c)) / (2 * c ^ (2 * (s - r)))
  have hpows : c ^ (2 * s) =
      c ^ (2 * r) * c ^ (2 * (s - r)) := by
    rw [show 2 * s = 2 * r + 2 * (s - r) by omega, pow_add]
  rw [hpows]
  field_simp [hcne, hsum.ne']
  ring

/-- Sharp odd-leading ground-polarization rate after the allowed phase reversal. -/
theorem tendsto_suzukiDefectAngle_oddLeading_rate
    {evenEnergy oddEnergy : ℝ → ℝ} {r s : ℕ} {A B : ℝ}
    (hsr : s < r) (hB : 0 < B)
    (henergy : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      0 < evenEnergy c + oddEnergy c)
    (heven : Tendsto (fun c : ℝ => evenEnergy c / c ^ (2 * r))
      (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hodd : Tendsto (fun c : ℝ => oddEnergy c / c ^ (2 * s))
      (𝓝[>] (0 : ℝ)) (𝓝 B)) :
    Tendsto
      (fun c : ℝ =>
        (1 + GaloisForLFunctions.RHTower.suzukiDefectAngle
          (evenEnergy c) (oddEnergy c)) /
            (2 * c ^ (2 * (r - s))))
      (𝓝[>] (0 : ℝ)) (𝓝 (A / B)) := by
  have hpow : Tendsto (fun c : ℝ => c ^ (2 * (r - s)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun c : ℝ => c ^ (2 * (r - s))) 0 := by fun_prop
    have hd : 0 < 2 * (r - s) := by omega
    simpa [zero_pow hd.ne'] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hden := (hpow.mul heven).add hodd
  have hratio := heven.div hden (by simpa using hB.ne')
  have hratio' : Tendsto
      ((fun c : ℝ => evenEnergy c / c ^ (2 * r)) /
        (fun c : ℝ => c ^ (2 * (r - s)) *
          (evenEnergy c / c ^ (2 * r)) + oddEnergy c / c ^ (2 * s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (A / B)) := by
    simpa using hratio
  apply hratio'.congr'
  filter_upwards [self_mem_nhdsWithin, henergy] with c hc hsum
  have hcne : c ≠ 0 := hc.ne'
  change (evenEnergy c / c ^ (2 * r)) /
      (c ^ (2 * (r - s)) * (evenEnergy c / c ^ (2 * r)) +
        oddEnergy c / c ^ (2 * s)) =
    (1 + (evenEnergy c - oddEnergy c) /
      (evenEnergy c + oddEnergy c)) / (2 * c ^ (2 * (r - s)))
  have hpowr : c ^ (2 * r) =
      c ^ (2 * s) * c ^ (2 * (r - s)) := by
    rw [show 2 * r = 2 * s + 2 * (r - s) by omega, pow_add]
  rw [hpowr]
  field_simp [hcne, hsum.ne']
  ring

/-- Any endpoint gap of order at least four has zero quadratic coefficient. -/
theorem tendsto_quadraticDefectRate_zero_of_higherRate
    {defect : ℝ → ℝ} {d : ℕ} {eta : ℝ} (hd : 2 ≤ d)
    (h : Tendsto
      (fun c : ℝ => (1 - defect c) / (2 * c ^ (2 * d)))
      (𝓝[>] (0 : ℝ)) (𝓝 eta)) :
    Tendsto (fun c : ℝ => (1 - defect c) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow : Tendsto (fun c : ℝ => c ^ (2 * d - 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun c : ℝ => c ^ (2 * d - 2)) 0 := by fun_prop
    have hpos : 0 < 2 * d - 2 := by omega
    simpa [zero_pow hpos.ne'] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hmain := h.mul hpow
  have hmain' : Tendsto
      (fun c : ℝ =>
        (1 - defect c) / (2 * c ^ (2 * d)) * c ^ (2 * d - 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hmain
  apply hmain'.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcne : c ≠ 0 := hc.ne'
  have hexp : 2 * d = 2 + (2 * d - 2) := by omega
  rw [hexp, pow_add]
  field_simp [hcne]
  have hsub : 2 + (2 * d - 2) - 2 = 2 * d - 2 := by omega
  rw [hsub]

/-- If a source endpoint has smaller quadratic gap coefficient than Xi, it lies beyond the Xi
target for all sufficiently small anchors. -/
theorem eventually_suzukiXiDefect_lt_of_sourceRate_lt
    {sourceDefect : ℝ → ℝ} {eta : ℝ}
    (hsource : Tendsto
      (fun c : ℝ => (1 - sourceDefect c) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 eta))
    (heta : eta < suzukiXiCoalescingSourceRate) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      suzukiXiCoalescingDefect c < sourceDefect c := by
  let mid := (eta + suzukiXiCoalescingSourceRate) / 2
  have hsourceMid : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      (1 - sourceDefect c) / (2 * c ^ 2) < mid :=
    hsource.eventually (eventually_lt_nhds (by dsimp [mid]; linarith))
  have hxiMid : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      mid < (1 - suzukiXiCoalescingDefect c) / (2 * c ^ 2) :=
    tendsto_suzukiXiCoalescingDefect_rate.eventually
      (eventually_gt_nhds (by dsimp [mid]; linarith))
  filter_upwards [self_mem_nhdsWithin, hsourceMid, hxiMid] with c hc hs hx
  have hcpos : 0 < c := hc
  have hden : 0 < 2 * c ^ 2 := by positivity
  have hs' := (div_lt_iff₀ hden).mp hs
  have hx' := (lt_div_iff₀ hden).mp hx
  linarith

/-- If a source endpoint has larger quadratic gap coefficient than Xi, it lies before the Xi
target for all sufficiently small anchors. -/
theorem eventually_sourceDefect_lt_suzukiXi_of_rate_gt
    {sourceDefect : ℝ → ℝ} {eta : ℝ}
    (hsource : Tendsto
      (fun c : ℝ => (1 - sourceDefect c) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 eta))
    (heta : suzukiXiCoalescingSourceRate < eta) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      sourceDefect c < suzukiXiCoalescingDefect c := by
  let mid := (eta + suzukiXiCoalescingSourceRate) / 2
  have hsourceMid : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      mid < (1 - sourceDefect c) / (2 * c ^ 2) :=
    hsource.eventually (eventually_gt_nhds (by dsimp [mid]; linarith))
  have hxiMid : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      (1 - suzukiXiCoalescingDefect c) / (2 * c ^ 2) < mid :=
    tendsto_suzukiXiCoalescingDefect_rate.eventually
      (eventually_lt_nhds (by dsimp [mid]; linarith))
  filter_upwards [self_mem_nhdsWithin, hsourceMid, hxiMid] with c hc hs hx
  have hcpos : 0 < c := hc
  have hden : 0 < 2 * c ^ 2 := by positivity
  have hs' := (lt_div_iff₀ hden).mp hs
  have hx' := (div_lt_iff₀ hden).mp hx
  linarith

/-- Sufficiently large apertures put the free endpoint strictly before the Xi target. -/
theorem eventually_suzukiCoalescingFreeDefect_lt_xi
    {a : ℝ} (ha : 0 < a)
    (hlarge : 3 * suzukiXiCoalescingSourceRate < a ^ 2) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      suzukiCoalescingFreeDefect a c < suzukiXiCoalescingDefect c := by
  apply eventually_sourceDefect_lt_suzukiXi_of_rate_gt
    (tendsto_suzukiCoalescingFreeDefect_rate ha)
  linarith

/-- Endpoint bracketing lifts pointwise to exact spectral-shift matching.  This is the topological
core used after the rate theorems have supplied both strict inequalities. -/
theorem eventually_exists_suzukiCoalescingMatchingShift
    {angle : ℝ → ℝ → ℝ} {spectralFloor : ℝ}
    {free ground target : ℝ → ℝ}
    (hcont : ∀ c, ContinuousOn (angle c) (Iio spectralFloor))
    (hfree : ∀ c, Tendsto (angle c) atBot (𝓝 (free c)))
    (hground : ∀ c, Tendsto (angle c)
      (𝓝[Iio spectralFloor] spectralFloor) (𝓝 (ground c)))
    (hbracket : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      free c < target c ∧ target c < ground c) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ∃ lambda < spectralFloor, angle c lambda = target c := by
  filter_upwards [hbracket] with c hc
  obtain ⟨lambda, hlambda⟩ :=
    exists_isGreatest_suzukiDefectMatchingShiftSet_of_two_limits
      (hcont c) (hfree c) (hground c) hc.1 hc.2
  exact ⟨lambda, hlambda.1.1, hlambda.1.2⟩

end

end RHTower
