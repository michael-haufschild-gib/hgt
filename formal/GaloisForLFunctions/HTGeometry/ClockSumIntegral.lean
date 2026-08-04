import GaloisForLFunctions.HTGeometry.ClockStepMajorant
import GaloisForLFunctions.HTGeometry.ClockSeriesIntegral
import GaloisForLFunctions.HTGeometry.ClockStepSeries
import GaloisForLFunctions.HTGeometry.ClockSolution

/-!
# Passing the sum through the inner integration

The recursion is summed by moving the sum through the two integrations. This file does the inner
one: the integrand is continuous in the integration variable for a fixed value of the other, and the
majorant of the previous file dominates it uniformly on the interval.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped Interval

/-- **The sum passes through the inner integration.** -/
theorem tsum_inner_integral {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {s η : ℝ} (hsT : |s| ≤ T) (hηT : |η| ≤ T)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    (∑' m : ℕ, ∫ t in (0 : ℝ)..η, clockStripStep (V s t) (clockIterate V m s t) z)
      = ∫ t in (0 : ℝ)..η, ∑' m : ℕ, clockStripStep (V s t) (clockIterate V m s t) z := by
  have hzmem : z ∈ imStrip ρ₀ := mem_imStrip.mpr (lt_of_le_of_lt hz hρ)
  refine tsum_intervalIntegral_of_bound (M := stepMajorant Mv ρ₀ ρ T) ?_ ?_
    (summable_stepMajorant hMv0 hρ hT hsmall)
  · intro m
    have hslice := continuous_clockStripStep_slice hV m
      (mem_imStrip.mpr (lt_of_le_of_lt hz hρ))
    exact hslice.comp (continuous_const.prodMk continuous_id)
  · intro m t ht
    exact norm_clockStripStep_clockIterate_le hρ₀ hV hMv0 hMv hρ0 hρ m hsT
      (le_trans (abs_le_abs_of_mem_uIoc_zero ht) hηT) hz

/-- **The sum passes through the outer integration.** The inner integral is continuous in the outer
variable and is dominated by the majorant times the length of the inner interval. -/
theorem tsum_outer_integral {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    (∑' m : ℕ, ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        clockStripStep (V s t) (clockIterate V m s t) z)
      = ∫ s in (0 : ℝ)..ξ, ∑' m : ℕ, ∫ t in (0 : ℝ)..η,
        clockStripStep (V s t) (clockIterate V m s t) z := by
  refine tsum_intervalIntegral_of_bound (M := fun m => stepMajorant Mv ρ₀ ρ T m * |η|) ?_ ?_ ?_
  · intro m
    have hjoint := continuous_clockStripStep_slice hV m
      (mem_imStrip.mpr (lt_of_le_of_lt hz hρ))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (s : ℝ) (t : ℝ) => clockStripStep (V s t) (clockIterate V m s t) z) hjoint 0 η
  · intro m s hs
    have hbound : ∀ t ∈ Ι (0 : ℝ) η,
        ‖clockStripStep (V s t) (clockIterate V m s t) z‖ ≤ stepMajorant Mv ρ₀ ρ T m := by
      intro t ht
      exact norm_clockStripStep_clockIterate_le hρ₀ hV hMv0 hMv hρ0 hρ m
        (le_trans (abs_le_abs_of_mem_uIoc_zero hs) hξT)
        (le_trans (abs_le_abs_of_mem_uIoc_zero ht) hηT) hz
    have hcalc := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [sub_zero] at hcalc
    exact hcalc
  · exact (summable_stepMajorant hMv0 hρ hT hsmall).mul_right |η|

/-- **The step operator commutes with the sum of the iterates.** -/
theorem clockStripStep_tsum_clockIterate {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {s t : ℝ} (hsT : |s| ≤ T) (htT : |t| ≤ T)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    clockStripStep (V s t) (clockSolution V s t) z
      = ∑' m : ℕ, clockStripStep (V s t) (clockIterate V m s t) z := by
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  set σ : ℝ := (ρ + ρ₀) / 2 with hσdef
  have hρσ : ρ < σ := by rw [hσdef]; linarith
  have hσρ₀ : σ < ρ₀ := by rw [hσdef]; linarith
  have hσ0 : (0 : ℝ) ≤ σ := le_trans hρ0 hρσ.le
  have hrem : ρ₀ - σ = (ρ₀ - ρ) / 2 := by rw [hσdef]; ring
  set ρ₂ : ℝ := ρ + (σ - ρ) / 4 with hρ₂def
  set ρ₁ : ℝ := ρ + (σ - ρ) / 2 with hρ₁def
  have h2 : ρ < ρ₂ := by rw [hρ₂def]; linarith
  have h21 : ρ₂ < ρ₁ := by rw [hρ₂def, hρ₁def]; linarith
  have h1σ : ρ₁ < σ := by rw [hρ₁def]; linarith
  have hzmem : z ∈ imStrip ρ₂ := mem_imStrip.mpr (lt_of_le_of_lt hz h2)
  -- holomorphy and summable bounds of the iterates on the strip of radius `σ`
  have hholo : ∀ m : ℕ, DifferentiableOn ℂ (clockIterate V m s t) (imStrip σ) := by
    intro m
    obtain ⟨holo, _⟩ := clockIterate_regular hV m
    exact (holo s t).mono (imStrip_mono hσρ₀.le)
  have hbound : ∀ (m : ℕ), ∀ w ∈ imStrip σ, ‖clockIterate V m s t w‖
      ≤ (4 + Mv * ρ₀ ^ 2 / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ 2 * ((ρ₀ - ρ) / 2) ^ (2 * m)) := by
    intro m w hw
    have hbase := clockIterate_norm_le hρ₀ hV hMv0 hMv m σ hσ0 hσρ₀ s t hsT htT w
      (le_of_lt (mem_imStrip.mp hw))
    rw [hrem] at hbase
    refine hbase.trans ?_
    gcongr
  have hK0 : (0 : ℝ) ≤ 4 + Mv * ρ₀ ^ 2 / 4 := by positivity
  have hGhalf : (0 : ℝ) < (ρ₀ - ρ) / 2 := by linarith
  have hMs := summable_ovsyannikov_bound (K := 4 + Mv * ρ₀ ^ 2 / 4) (G := (ρ₀ - ρ) / 2)
    (T := T) hK0 hGhalf hT hsmall
  have hdef : clockSolution V s t = fun w => ∑' m : ℕ, clockIterate V m s t w := rfl
  rw [hdef]
  exact clockStripStep_tsum h21 h1σ hholo hbound hMs hzmem

/-- **The sum of the iterates satisfies the integral equation of the clock problem.** -/
theorem clockSolution_integral_equation {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    clockSolution V ξ η z
      = 1 + ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        clockStripStep (V s t) (clockSolution V s t) z := by
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  -- the weaker smallness condition, for the summability of the iterates
  have hsmall' := ovsyannikov_smallness_of_half hMv0 hρ hsmall
  have hsum := summable_clockIterate hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall' hξT hηT hz
  have hzero : clockIterate V 0 ξ η z = 1 := rfl
  have hrec : ∀ m : ℕ, clockIterate V (m + 1) ξ η z
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        clockStripStep (V s t) (clockIterate V m s t) z := fun m => clockIterate_succ V m ξ η z
  rw [clockSolution, hsum.tsum_eq_zero_add, hzero, tsum_congr hrec,
    tsum_outer_integral hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hηT hz]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hsb : |s| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero hs) hξT
  rw [tsum_inner_integral hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hsb hηT hz]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have htb : |t| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero ht) hηT
  exact (clockStripStep_tsum_clockIterate hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hsb htb hz).symm

/-! ## Continuity of the right-hand side

Differentiating the integral equation needs the integrand to be continuous in the two null
coordinates. It is a series of continuous functions, but the majorant holds only on the rectangle,
so the arguments are first clamped to it; inside the rectangle the clamp is the identity. The
rectangle is the two-sided one `|ξ|, |η| ≤ T`, so an interior point has room on both sides.
-/

/-- Clamp a real number to `[-T, T]`. -/
noncomputable def boxClamp (T x : ℝ) : ℝ := max (-T) (min T x)

theorem continuous_boxClamp (T : ℝ) : Continuous (boxClamp T) := by
  unfold boxClamp
  fun_prop

theorem abs_boxClamp_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |boxClamp T x| ≤ T := by
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem boxClamp_eq_self {T x : ℝ} (h : |x| ≤ T) : boxClamp T x = x := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [boxClamp, min_eq_right h2, max_eq_right h1]

/-- The step operator applied to the solution at clamped null coordinates. -/
noncomputable def clampedStep (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (z : ℂ) (s t : ℝ) : ℂ :=
  clockStripStep (V (boxClamp T s) (boxClamp T t))
    (clockSolution V (boxClamp T s) (boxClamp T t)) z

theorem clampedStep_eq {T : ℝ} {V : ℝ → ℝ → ℂ → ℂ} {z : ℂ} {s t : ℝ}
    (hs : |s| ≤ T) (ht : |t| ≤ T) :
    clampedStep V T z s t = clockStripStep (V s t) (clockSolution V s t) z := by
  rw [clampedStep, boxClamp_eq_self hs, boxClamp_eq_self ht]

/-- **The clamped right-hand side is continuous on the whole plane of null coordinates.** -/
theorem continuous_clampedStep {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    Continuous fun r : ℝ × ℝ => clampedStep V T z r.1 r.2 := by
  have hMs := summable_stepMajorant hMv0 hρ hT hsmall
  have hterm : ∀ m : ℕ, Continuous fun r : ℝ × ℝ =>
      clockStripStep (V (boxClamp T r.1) (boxClamp T r.2))
        (clockIterate V m (boxClamp T r.1) (boxClamp T r.2)) z := by
    intro m
    have hslice := continuous_clockStripStep_slice hV m
      (mem_imStrip.mpr (lt_of_le_of_lt hz hρ))
    exact hslice.comp (((continuous_boxClamp T).comp continuous_fst).prodMk
      ((continuous_boxClamp T).comp continuous_snd))
  have hbnd : ∀ (m : ℕ) (r : ℝ × ℝ),
      ‖clockStripStep (V (boxClamp T r.1) (boxClamp T r.2))
          (clockIterate V m (boxClamp T r.1) (boxClamp T r.2)) z‖
        ≤ stepMajorant Mv ρ₀ ρ T m := fun m r =>
    norm_clockStripStep_clockIterate_le hρ₀ hV hMv0 hMv hρ0 hρ m
      (abs_boxClamp_le hT r.1) (abs_boxClamp_le hT r.2) hz
  refine (continuous_tsum hterm hMs hbnd).congr fun r => ?_
  exact (clockStripStep_tsum_clockIterate hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    (abs_boxClamp_le hT r.1) (abs_boxClamp_le hT r.2) hz).symm

/-- The open rectangle of null coordinates on which the construction is valid. -/
theorem isOpen_absLt (T : ℝ) : IsOpen {x : ℝ | |x| < T} :=
  isOpen_lt continuous_abs continuous_const

theorem isOpen_absLt_prod (T : ℝ) : IsOpen {r : ℝ × ℝ | |r.1| < T ∧ |r.2| < T} := by
  have h1 : IsOpen {r : ℝ × ℝ | |r.1| < T} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsOpen {r : ℝ × ℝ | |r.2| < T} :=
    isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
  simpa [Set.setOf_and] using h1.inter h2

/-- **The right-hand side of the integral equation is continuous in the null coordinates**, at every
interior point of the rectangle. -/
theorem continuousAt_clockStripStep_clockSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z : ℂ} (hz : |z.im| ≤ ρ) {p : ℝ × ℝ} (hp1T : |p.1| < T) (hp2T : |p.2| < T) :
    ContinuousAt (fun r : ℝ × ℝ => clockStripStep (V r.1 r.2) (clockSolution V r.1 r.2) z) p := by
  refine ((continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz).continuousAt).congr ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt_prod T).mem_nhds ⟨hp1T, hp2T⟩) fun r hr => ?_
  exact clampedStep_eq hr.1.le hr.2.le

end GaloisForLFunctions.HTGeometry
