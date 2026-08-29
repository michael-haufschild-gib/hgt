import GaloisForLFunctions.RHTower.RVNormalizedWeight
import GaloisForLFunctions.RHTower.PrimeCountShell
import GaloisForLFunctions.RHTower.SteinhausCumulantSlope
import GaloisForLFunctions.RHTower.SteinhausRatePositive
import GaloisForLFunctions.RHTower.PrimeKaramataBody

/-!
# The prime average of the tilted cumulant

The card's `(12)`.  The head of the average is controlled by `log I₀(x) ≤ x`, which turns it into
the ratio `W_{v₀X}/W_X` of two prime Karamata sums; the body is the Riemann sum of
`v ↦ log I₀(λ w_α(v))`, an antitone function, evaluated through the shell counts.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

noncomputable section

/-- The one-circle cumulant is monotone on the nonnegative ray. -/
theorem steinhausLogLaplace_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    steinhausLogLaplace x ≤ steinhausLogLaplace y := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0, steinhausLogLaplace_zero]
    exact steinhausLogLaplace_nonneg y
  · have hy : 0 < y := lt_of_lt_of_le hpos hxy
    have ht : x / y ≤ 1 := by rw [div_le_one hy]; exact hxy
    have ht0 : (0 : ℝ) ≤ x / y := by positivity
    have hid : x = (x / y) * y := by field_simp
    have hsc : steinhausLogLaplace ((x / y) * y) ≤ (x / y) * steinhausLogLaplace y :=
      steinhausLogLaplace_scale_le ht0 ht
    rw [← hid] at hsc
    have hgy := steinhausLogLaplace_nonneg y
    nlinarith only [hsc, hgy, ht, ht0]

/-- The card's `(12)` averaging functional. -/
def rvCumulantAverage (α : ℝ) (L : ℝ → ℝ) (lam X : ℝ) : ℝ :=
  primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X / rvPrimeCount X

theorem rvNormReal_nonneg {α : ℝ} {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {X t : ℝ}
    (hX : 0 < rvWeightSum α L X) (ht : 1 ≤ t) : 0 ≤ rvNormReal α L X t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hw : 0 ≤ rvPrimeWeight α L t := rvPrimeWeight_nonneg hL ht0
  have hcount : (0 : ℝ) ≤ rvPrimeCount X := Nat.cast_nonneg _
  rw [rvNormReal]
  positivity

/-- **The head of the average.** -/
theorem rvCumulantAverage_head_le {α : ℝ} {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    {lam X Y : ℝ} (hlam : 0 ≤ lam) (hW : 0 < rvWeightSum α L X) :
    primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 Y
      ≤ lam * rvPrimeCount X * primeLogSum (rvPrimeWeight α L) 0 Y / rvWeightSum α L X := by
  have hstep : ∀ p ∈ (Finset.Ioc ⌊(0 : ℝ)⌋₊ ⌊Y⌋₊).filter (fun p => Nat.Prime p),
      steinhausLogLaplace (lam * rvNormReal α L X (p : ℝ))
        ≤ lam * rvPrimeCount X / rvWeightSum α L X * (Real.log p * rvPrimeWeight α L p) := by
    intro p hp
    obtain ⟨hprime, h1, h2⟩ := mem_shell_of_mem_filter le_rfl hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
    have hnn : 0 ≤ rvNormReal α L X (p : ℝ) := rvNormReal_nonneg hL hW hp1
    have hy : 0 ≤ lam * rvNormReal α L X (p : ℝ) := mul_nonneg hlam hnn
    have hg := steinhausLogLaplace_le_abs (lam * rvNormReal α L X (p : ℝ))
    rw [abs_of_nonneg hy] at hg
    refine hg.trans (le_of_eq ?_)
    rw [rvNormReal]
    field_simp
  calc primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 Y
      ≤ ∑ p ∈ (Finset.Ioc ⌊(0 : ℝ)⌋₊ ⌊Y⌋₊).filter (fun p => Nat.Prime p),
          lam * rvPrimeCount X / rvWeightSum α L X * (Real.log p * rvPrimeWeight α L p) :=
        Finset.sum_le_sum hstep
    _ = lam * rvPrimeCount X * primeLogSum (rvPrimeWeight α L) 0 Y / rvWeightSum α L X := by
        rw [← Finset.mul_sum, primeLogSum]
        ring


/-- The Chebyshev mass of a dilated ray. -/
theorem tendsto_chebyshevTheta_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ => Chebyshev.theta (c * X) / X) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hδc : 0 < δ / 2 / c := by positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    ((tendsto_const_mul_atTop_of_pos hc).eventually (chebyshevTheta_eventually_relative hδc))
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
  have h := hX₀ X (le_trans (le_max_left _ _) hX)
  rw [abs_le] at h
  have hscale : δ / 2 / c * (c * X) = δ / 2 * X := by field_simp
  have key : |Chebyshev.theta (c * X) / X - c| ≤ δ / 2 := by
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hX0]
      linarith only [h.1, hscale.le, hscale.ge]
    · rw [sub_le_iff_le_add, div_le_iff₀ hX0]
      linarith only [h.2, hscale.le, hscale.ge]
  rw [Real.dist_eq]
  linarith only [key, hδ]

/-- The logarithmic shift ratio. -/
theorem tendsto_log_shift_ratio (d : ℝ) :
    Tendsto (fun X : ℝ => Real.log X / (Real.log X + d)) atTop (𝓝 1) := by
  have hden : Tendsto (fun X : ℝ => Real.log X + d) atTop atTop :=
    tendsto_atTop_add_const_right atTop d Real.tendsto_log_atTop
  have h1 : Tendsto (fun X : ℝ => d / (Real.log X + d)) atTop (𝓝 0) := hden.const_div_atTop d
  have h2 := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).sub h1
  rw [sub_zero] at h2
  refine Tendsto.congr' ?_ h2
  filter_upwards [hden.eventually_gt_atTop 0] with X hX
  field_simp
  ring

/-- The reciprocal prime-counting ratio. -/
theorem tendsto_rvPrimeCount_ratio_inv :
    Tendsto (fun X : ℝ => (X / Real.log X) / rvPrimeCount X) atTop (𝓝 1) := by
  have h := tendsto_rvPrimeCount_ratio.inv₀ (by norm_num)
  rw [inv_one] at h
  refine Tendsto.congr' ?_ h
  filter_upwards with X
  rw [inv_div]

/-- **The shell density.** -/
theorem tendsto_shell_card_ratio {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun X : ℝ => (primeShellCard (a * X) (b * X) : ℝ) / rvPrimeCount X) atTop
      (𝓝 (b - a)) := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  set Q : ℝ → ℝ := fun X => (X / Real.log X) / rvPrimeCount X with hQ
  set m : ℝ → ℝ := fun X => (primeShellCard (a * X) (b * X) : ℝ) * Real.log X / X with hm
  have hmasslim : Tendsto (fun X : ℝ =>
      (Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) / X) atTop (𝓝 (b - a)) := by
    have := (tendsto_chebyshevTheta_div hb0).sub (tendsto_chebyshevTheta_div ha)
    refine Tendsto.congr' ?_ this
    filter_upwards with X
    ring
  have hUp : Tendsto (fun X : ℝ =>
      ((Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) / X)
        * (Real.log X / (Real.log X + Real.log a))) atTop (𝓝 (b - a)) := by
    have := hmasslim.mul (tendsto_log_shift_ratio (Real.log a))
    rwa [mul_one] at this
  have hLo : Tendsto (fun X : ℝ =>
      ((Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) / X)
        * (Real.log X / (Real.log X + Real.log b))) atTop (𝓝 (b - a)) := by
    have := hmasslim.mul (tendsto_log_shift_ratio (Real.log b))
    rwa [mul_one] at this
  have hev : ∀ᶠ X in atTop, 1 < a * X ∧ 0 < Real.log X + Real.log a
      ∧ 0 < Real.log X + Real.log b ∧ 0 < X ∧ 1 ≤ X := by
    have h1 : ∀ᶠ X in atTop, 1 < a * X :=
      (tendsto_const_mul_atTop_of_pos ha).eventually_gt_atTop 1
    have h2 : ∀ᶠ X in atTop, 0 < Real.log X + Real.log a :=
      (tendsto_atTop_add_const_right atTop (Real.log a) Real.tendsto_log_atTop).eventually_gt_atTop 0
    have h3 : ∀ᶠ X in atTop, 0 < Real.log X + Real.log b :=
      (tendsto_atTop_add_const_right atTop (Real.log b) Real.tendsto_log_atTop).eventually_gt_atTop 0
    filter_upwards [h1, h2, h3, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)]
      with X hX1 hX2 hX3 hX4 hX5
    exact ⟨hX1, hX2, hX3, hX4, hX5⟩
  have hmlim : Tendsto m atTop (𝓝 (b - a)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hUp ?_ ?_
    · filter_upwards [hev] with X hXd
      obtain ⟨hax, hla, hlb, hX0, hX1⟩ := hXd
      have hlogXnn : (0 : ℝ) ≤ Real.log X / X := by
        have : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
        positivity
      have hbx : a * X ≤ b * X := by nlinarith only [hab, hX0.le]
      obtain ⟨hcard1, -⟩ := primeShellCard_bounds hax hbx
      have hlogb : Real.log (b * X) = Real.log X + Real.log b := by
        rw [Real.log_mul hb0.ne' hX0.ne']; ring
      rw [hlogb] at hcard1
      have hmul := mul_le_mul_of_nonneg_right hcard1 hlogXnn
      have hid1 : (Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) / (Real.log X + Real.log b)
          * (Real.log X / X)
          = ((Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) / X)
            * (Real.log X / (Real.log X + Real.log b)) := by
        field_simp
      have hid2 : (primeShellCard (a * X) (b * X) : ℝ) * (Real.log X / X)
          = m X := by rw [hm]; field_simp
      rw [hid1, hid2] at hmul
      exact hmul
    · filter_upwards [hev] with X hXd
      obtain ⟨hax, hla, hlb, hX0, hX1⟩ := hXd
      have hlogXnn : (0 : ℝ) ≤ Real.log X / X := by
        have : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
        positivity
      have hbx : a * X ≤ b * X := by nlinarith only [hab, hX0.le]
      obtain ⟨-, hcard2⟩ := primeShellCard_bounds hax hbx
      have hloga : Real.log (a * X) = Real.log X + Real.log a := by
        rw [Real.log_mul ha.ne' hX0.ne']; ring
      rw [hloga] at hcard2
      have hmul := mul_le_mul_of_nonneg_right hcard2 hlogXnn
      have hid1 : (Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) / (Real.log X + Real.log a)
          * (Real.log X / X)
          = ((Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) / X)
            * (Real.log X / (Real.log X + Real.log a)) := by
        field_simp
      have hid2 : (primeShellCard (a * X) (b * X) : ℝ) * (Real.log X / X)
          = m X := by rw [hm]; field_simp
      rw [hid1, hid2] at hmul
      exact hmul
  have hfin := hmlim.mul tendsto_rvPrimeCount_ratio_inv
  rw [mul_one] at hfin
  refine Tendsto.congr' ?_ hfin
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with X hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  simp only [hm, hQ]
  field_simp


/-- **The Darboux bracket for an antitone integrand.** -/
theorem antitone_darboux {G : ℝ → ℝ} {v₀ : ℝ} (hv₀ : 0 < v₀) (hv₀1 : v₀ < 1) {N : ℕ}
    (hN : 0 < N) (hanti : AntitoneOn G (Set.Icc v₀ 1)) :
    (∑ j ∈ Finset.range N, G (karamataNode v₀ N (j + 1))) * ((1 - v₀) / N)
        ≤ ∫ v in v₀..(1 : ℝ), G v
      ∧ (∫ v in v₀..(1 : ℝ), G v)
        ≤ (∑ j ∈ Finset.range N, G (karamataNode v₀ N j)) * ((1 - v₀) / N) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set h : ℝ := (1 - v₀) / N with hh
  have hh0 : 0 < h := by
    rw [hh]
    have : (0 : ℝ) < 1 - v₀ := by linarith
    positivity
  have hhN : h * (N : ℝ) = 1 - v₀ := by rw [hh]; field_simp
  set H : ℝ → ℝ := fun u : ℝ => G (h * u + v₀) with hH
  have hHanti : AntitoneOn H (Set.Icc (0 : ℝ) (0 + (N : ℝ))) := by
    intro u hu v hv huv
    have hu0 : (0 : ℝ) ≤ u := by simpa using hu.1
    have huN : u ≤ (N : ℝ) := by simpa using hu.2
    have hv0 : (0 : ℝ) ≤ v := by simpa using hv.1
    have hvN : v ≤ (N : ℝ) := by simpa using hv.2
    refine hanti ⟨by nlinarith only [hh0, hu0], by nlinarith only [hhN, huN, hh0]⟩
      ⟨by nlinarith only [hh0, hv0], by nlinarith only [hhN, hvN, hh0]⟩ ?_
    nlinarith only [hh0, huv]
  have hsub : (∫ u in (0 : ℝ)..(N : ℝ), H u) = h⁻¹ * ∫ v in v₀..(1 : ℝ), G v := by
    have hcomp := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := (N : ℝ)) G hh0.ne' v₀
    rw [hH, hcomp]
    have hend : h * (N : ℝ) + v₀ = 1 := by rw [hhN]; ring
    rw [mul_zero, zero_add, hend, smul_eq_mul]
  have hupper := hHanti.integral_le_sum
  have hlower := hHanti.sum_le_integral
  rw [zero_add] at hupper hlower
  rw [hsub] at hupper hlower
  have hnode : ∀ j : ℕ, karamataNode v₀ N j = h * (j : ℝ) + v₀ := by
    intro j
    rw [karamataNode, ← hh]
    ring
  constructor
  · have hL : ∑ i ∈ Finset.range N, H ((0 : ℝ) + ((i + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.range N, G (karamataNode v₀ N (j + 1)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hH, hnode]
      push_cast
      ring_nf
    rw [hL] at hlower
    have hmul := mul_le_mul_of_nonneg_right hlower hh0.le
    have hid : h⁻¹ * (∫ v in v₀..(1 : ℝ), G v) * h = ∫ v in v₀..(1 : ℝ), G v := by field_simp
    rw [hid] at hmul
    exact hmul
  · have hU : ∑ i ∈ Finset.range N, H ((0 : ℝ) + (i : ℝ))
        = ∑ j ∈ Finset.range N, G (karamataNode v₀ N j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hH, hnode]
      push_cast
      ring_nf
    rw [hU] at hupper
    have hmul := mul_le_mul_of_nonneg_right hupper hh0.le
    have hid : h⁻¹ * (∫ v in v₀..(1 : ℝ), G v) * h = ∫ v in v₀..(1 : ℝ), G v := by field_simp
    rw [hid] at hmul
    exact hmul

/-- The profile cumulant integrand. -/
def rvProfileCumulant (α lam v : ℝ) : ℝ := steinhausLogLaplace (lam * weightProfile α v)

theorem antitoneOn_rvProfileCumulant {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {lam : ℝ}
    (hlam : 0 ≤ lam) {v₀ : ℝ} (hv₀ : 0 < v₀) :
    AntitoneOn (rvProfileCumulant α lam) (Set.Icc v₀ 1) := by
  intro u hu v hv huv
  have hu0 : 0 < u := lt_of_lt_of_le hv₀ hu.1
  have hv0 : 0 < v := lt_of_lt_of_le hv₀ hv.1
  have hpow : v ^ (-α) ≤ u ^ (-α) := Real.rpow_le_rpow_of_nonpos hu0 huv (by linarith)
  have hα' : (0 : ℝ) < 1 - α := by linarith
  have hle : lam * weightProfile α v ≤ lam * weightProfile α u := by
    have hmul : (1 - α) * v ^ (-α) ≤ (1 - α) * u ^ (-α) :=
      mul_le_mul_of_nonneg_left hpow hα'.le
    rw [weightProfile, weightProfile]
    exact mul_le_mul_of_nonneg_left hmul hlam
  have hnn : 0 ≤ lam * weightProfile α v := by
    have := weightProfile_nonneg hα1 hv0.le
    exact mul_nonneg hlam this
  exact steinhausLogLaplace_mono hnn hle

/-- Interval integrability of the profile cumulant on an initial segment. -/
theorem intervalIntegrable_rvProfileCumulant {α : ℝ} (hα1 : α < 1) (lam : ℝ) {v₀ : ℝ}
    (hv₀ : 0 ≤ v₀) (hv₀1 : v₀ ≤ 1) :
    IntervalIntegrable (rvProfileCumulant α lam) volume 0 v₀ := by
  have hbase := intervalIntegrable_rvCumulant_integrand (α := α) hα1 lam
  refine hbase.mono_set ?_
  rw [Set.uIcc_of_le hv₀, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact Set.Icc_subset_Icc_right hv₀1

/-- The head of the profile integral. -/
theorem integral_rvProfileCumulant_head_le {α : ℝ} (hα1 : α < 1) {lam v₀ : ℝ}
    (hlam : 0 ≤ lam) (hv₀ : 0 ≤ v₀) (hv₀1 : v₀ ≤ 1) :
    (∫ v in (0 : ℝ)..v₀, rvProfileCumulant α lam v) ≤ lam * v₀ ^ (1 - α) := by
  have hint1 := intervalIntegrable_rvProfileCumulant hα1 lam hv₀ hv₀1
  have hint2 : IntervalIntegrable (fun v : ℝ => lam * weightProfile α v) volume 0 v₀ := by
    refine ((intervalIntegrable_weightProfile hα1).mono_set ?_).const_mul _
    rw [Set.uIcc_of_le hv₀, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc_right hv₀1
  have hpt : ∀ v ∈ Set.Icc (0 : ℝ) v₀,
      rvProfileCumulant α lam v ≤ lam * weightProfile α v := by
    intro v hv
    have hw : 0 ≤ weightProfile α v := weightProfile_nonneg hα1 hv.1
    have hbd := steinhausLogLaplace_le_abs (lam * weightProfile α v)
    rw [abs_mul, abs_of_nonneg hlam, abs_of_nonneg hw] at hbd
    exact hbd
  have hmono := intervalIntegral.integral_mono_on hv₀ hint1 hint2 hpt
  rw [intervalIntegral.integral_const_mul, integral_weightProfile_Icc hα1] at hmono
  exact hmono

/-- The profile cumulant integral splits at `v₀`. -/
theorem integral_rvProfileCumulant_split {α : ℝ} (hα1 : α < 1) (lam : ℝ) {v₀ : ℝ}
    (hv₀ : 0 ≤ v₀) (hv₀1 : v₀ ≤ 1) :
    rvCumulant α lam = (∫ v in (0 : ℝ)..v₀, rvProfileCumulant α lam v)
      + ∫ v in v₀..(1 : ℝ), rvProfileCumulant α lam v := by
  have h1 := intervalIntegrable_rvProfileCumulant hα1 lam hv₀ hv₀1
  have h2 : IntervalIntegrable (rvProfileCumulant α lam) volume v₀ 1 := by
    have hbase := intervalIntegrable_rvCumulant_integrand (α := α) hα1 lam
    refine hbase.mono_set ?_
    rw [Set.uIcc_of_le hv₀1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc_left hv₀
  rw [intervalIntegral.integral_add_adjacent_intervals h1 h2, rvCumulant]
  simp only [rvProfileCumulant]

end

end RHTower
