import GaloisForLFunctions.HTGeometry.ClockTubeStepSeries
import GaloisForLFunctions.HTGeometry.ClockSeriesIntegral
import GaloisForLFunctions.HTGeometry.ClockSumIntegral

/-!
# The integral equation on a tube

The recursion is summed by moving the sum through the two integrations. The majorant of the previous
file dominates the integrand uniformly on the rectangle, so both exchanges are dominated convergence
for series, and the step operator itself passes through the sum by slice holomorphy.

The result is that the sum of the iterates satisfies the integral equation of the clock problem with
several coupled transverse coordinates, and that its right-hand side is continuous in the two null
coordinates at every interior point of the rectangle.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped Interval

variable {k : ℕ}

/-- **The sum passes through the inner integration.** -/
theorem tsum_inner_integral_tube {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {s η : ℝ} (hsT : |s| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    (∑' m : ℕ, ∫ t in (0 : ℝ)..η, tubeStep (V s t) (tubeIterate V m s t) z)
      = ∫ t in (0 : ℝ)..η, ∑' m : ℕ, tubeStep (V s t) (tubeIterate V m s t) z := by
  have hzmem : z ∈ tube k ρ₀ := fun i => lt_of_le_of_lt (hz i) hρ
  refine tsum_intervalIntegral_of_bound (M := tubeStepMajorant k Mv ρ₀ ρ T) ?_ ?_
    (summable_tubeStepMajorant hMv0 hρ hT hsmall)
  · intro m
    show Continuous fun t : ℝ => tubeStep (V s t) (tubeIterate V m s t) z
    exact (continuous_tubeStep_slice hρ₀ hV m hzmem).comp
      (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) (continuous_const.prodMk continuous_id)
  · intro m t ht
    exact norm_tubeStep_tubeIterate_le hρ₀ hV hMv0 hMv hρ0 hρ m hsT
      (le_trans (abs_le_abs_of_mem_uIoc_zero ht) hηT) hz

/-- **The sum passes through the outer integration.** -/
theorem tsum_outer_integral_tube {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    (∑' m : ℕ, ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, tubeStep (V s t) (tubeIterate V m s t) z)
      = ∫ s in (0 : ℝ)..ξ, ∑' m : ℕ, ∫ t in (0 : ℝ)..η,
        tubeStep (V s t) (tubeIterate V m s t) z := by
  have hzmem : z ∈ tube k ρ₀ := fun i => lt_of_le_of_lt (hz i) hρ
  refine tsum_intervalIntegral_of_bound (M := fun m => tubeStepMajorant k Mv ρ₀ ρ T m * |η|)
    ?_ ?_ ?_
  · intro m
    show Continuous fun s : ℝ => ∫ t in (0 : ℝ)..η, tubeStep (V s t) (tubeIterate V m s t) z
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (s : ℝ) (t : ℝ) => tubeStep (V s t) (tubeIterate V m s t) z)
      (continuous_tubeStep_slice hρ₀ hV m hzmem) 0 η
  · intro m s hs
    have hbound : ∀ t ∈ Ι (0 : ℝ) η,
        ‖tubeStep (V s t) (tubeIterate V m s t) z‖ ≤ tubeStepMajorant k Mv ρ₀ ρ T m := by
      intro t ht
      exact norm_tubeStep_tubeIterate_le hρ₀ hV hMv0 hMv hρ0 hρ m
        (le_trans (abs_le_abs_of_mem_uIoc_zero hs) hξT)
        (le_trans (abs_le_abs_of_mem_uIoc_zero ht) hηT) hz
    have hcalc := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [sub_zero] at hcalc
    exact hcalc
  · exact (summable_tubeStepMajorant hMv0 hρ hT hsmall).mul_right |η|

/-- **The step operator commutes with the sum of the iterates.** -/
theorem tubeStep_tsum_tubeIterate {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {s t : ℝ} (hsT : |s| ≤ T) (htT : |t| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    tubeStep (V s t) (tubeSolution V s t) z = ∑' m : ℕ, tubeStep (V s t) (tubeIterate V m s t) z := by
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
  have hzmem : z ∈ tube k ρ₂ := fun i => lt_of_le_of_lt (hz i) h2
  -- slice holomorphy and summable bounds of the iterates on the tube of radius `σ`
  have hholo : ∀ m : ℕ, SliceHolo (tubeIterate V m s t) σ := by
    intro m
    obtain ⟨holo, _⟩ := tubeIterate_regular hρ₀ hV m
    exact sliceHolo_mono (holo s t) hσρ₀.le
  have hbound : ∀ (m : ℕ), ∀ w ∈ tube k σ, ‖tubeIterate V m s t w‖
      ≤ (4 * k + Mv * ρ₀ ^ 2 / 4) ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ 2 * ((ρ₀ - ρ) / 2) ^ (2 * m)) := by
    intro m w hw
    have hbase := tubeIterate_norm_le hρ₀ hV hMv0 hMv m σ hσ0 hσρ₀ s t hsT htT w
      fun i => (hw i).le
    rw [hrem] at hbase
    refine hbase.trans ?_
    have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    gcongr
  have hK0 : (0 : ℝ) ≤ 4 * k + Mv * ρ₀ ^ 2 / 4 := by positivity
  have hGhalf : (0 : ℝ) < (ρ₀ - ρ) / 2 := by linarith
  have hMs := summable_ovsyannikov_bound (K := 4 * k + Mv * ρ₀ ^ 2 / 4) (G := (ρ₀ - ρ) / 2)
    (T := T) hK0 hGhalf hT hsmall
  have hdef : tubeSolution V s t = fun w => ∑' m : ℕ, tubeIterate V m s t w := rfl
  rw [hdef]
  exact tubeStep_tsum h21 h1σ hholo hbound hMs hzmem

/-- **The sum of the iterates satisfies the integral equation of the clock problem on a tube.** -/
theorem tubeSolution_integral_equation {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    tubeSolution V ξ η z
      = 1 + ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, tubeStep (V s t) (tubeSolution V s t) z := by
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  have hK0 : (0 : ℝ) ≤ 4 * k + Mv * ρ₀ ^ 2 / 4 := by positivity
  -- the weaker smallness condition, for the summability of the iterates
  have hsmall' := ovsyannikov_smallness_of_half_const hK0 hG hsmall
  have hsum := summable_tubeIterate hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall' hξT hηT hz
  have hzero : tubeIterate V 0 ξ η z = 1 := rfl
  have hrec : ∀ m : ℕ, tubeIterate V (m + 1) ξ η z
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        tubeStep (V s t) (tubeIterate V m s t) z := fun m => tubeIterate_succ V m ξ η z
  rw [tubeSolution, hsum.tsum_eq_zero_add, hzero, tsum_congr hrec,
    tsum_outer_integral_tube hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hηT hz]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hsb : |s| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero hs) hξT
  rw [tsum_inner_integral_tube hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hsb hηT hz]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have htb : |t| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero ht) hηT
  exact (tubeStep_tsum_tubeIterate hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hsb htb hz).symm

/-! ## Continuity of the right-hand side

Differentiating the integral equation needs the integrand to be continuous in the two null
coordinates. It is a series of continuous functions, but the majorant holds only on the rectangle, so
the arguments are first clamped to it; inside the rectangle the clamp is the identity.
-/

/-- The step operator applied to the solution at clamped null coordinates. -/
noncomputable def clampedTubeStep (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (z : Fin k → ℂ)
    (s t : ℝ) : ℂ :=
  tubeStep (V (boxClamp T s) (boxClamp T t)) (tubeSolution V (boxClamp T s) (boxClamp T t)) z

theorem clampedTubeStep_eq {T : ℝ} {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} {z : Fin k → ℂ} {s t : ℝ}
    (hs : |s| ≤ T) (ht : |t| ≤ T) :
    clampedTubeStep V T z s t = tubeStep (V s t) (tubeSolution V s t) z := by
  rw [clampedTubeStep, boxClamp_eq_self hs, boxClamp_eq_self ht]

/-- **The clamped right-hand side is continuous on the whole plane of null coordinates.** -/
theorem continuous_clampedTubeStep {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    Continuous fun r : ℝ × ℝ => clampedTubeStep V T z r.1 r.2 := by
  have hzmem : z ∈ tube k ρ₀ := fun i => lt_of_le_of_lt (hz i) hρ
  have hMs := summable_tubeStepMajorant hMv0 hρ hT hsmall
  have hterm : ∀ m : ℕ, Continuous fun r : ℝ × ℝ =>
      tubeStep (V (boxClamp T r.1) (boxClamp T r.2))
        (tubeIterate V m (boxClamp T r.1) (boxClamp T r.2)) z := fun m =>
    (continuous_tubeStep_slice hρ₀ hV m hzmem).comp
      (f := fun r : ℝ × ℝ => ((boxClamp T r.1, boxClamp T r.2) : ℝ × ℝ))
      (((continuous_boxClamp T).comp (g := boxClamp T) continuous_fst).prodMk
        ((continuous_boxClamp T).comp (g := boxClamp T) continuous_snd))
  have hbnd : ∀ (m : ℕ) (r : ℝ × ℝ),
      ‖tubeStep (V (boxClamp T r.1) (boxClamp T r.2))
          (tubeIterate V m (boxClamp T r.1) (boxClamp T r.2)) z‖
        ≤ tubeStepMajorant k Mv ρ₀ ρ T m := fun m r =>
    norm_tubeStep_tubeIterate_le hρ₀ hV hMv0 hMv hρ0 hρ m
      (abs_boxClamp_le hT r.1) (abs_boxClamp_le hT r.2) hz
  refine (continuous_tsum hterm hMs hbnd).congr fun r => ?_
  exact (tubeStep_tsum_tubeIterate hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    (abs_boxClamp_le hT r.1) (abs_boxClamp_le hT r.2) hz).symm

/-- **The right-hand side of the integral equation is continuous in the null coordinates**, at every
interior point of the rectangle. -/
theorem continuousAt_tubeStep_tubeSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) {p : ℝ × ℝ} (hp1T : |p.1| < T) (hp2T : |p.2| < T) :
    ContinuousAt (fun r : ℝ × ℝ => tubeStep (V r.1 r.2) (tubeSolution V r.1 r.2) z) p := by
  refine ((continuous_clampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz).continuousAt).congr ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt_prod T).mem_nhds ⟨hp1T, hp2T⟩) fun r hr => ?_
  exact clampedTubeStep_eq hr.1.le hr.2.le

end GaloisForLFunctions.HTGeometry
