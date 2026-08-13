import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemmaAd2Pointwise

/-!
# Scalar differentiation of Suzuki's moving aperture cutoff

The sharp family `1_[0,a] f` is not differentiable as an `L¹`-valued curve.  After pairing with
a continuous bounded weight, however, its derivative exists and contains the literal endpoint
trace.  Combining this endpoint derivative with a strongly differentiable `L¹` curve gives the
moving-boundary Leibniz rule needed for Suzuki's compact Mellin transforms.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Pair an interval `L¹` class with a continuous scalar weight. -/
def suzukiIntervalL1ContinuousPairing (B : ℝ)
    (w : C(ClosedInterval 0 B, ℂ)) : IntervalL1 0 B →L[ℂ] ℂ :=
  (complexMulBilinear.lpPairing volume ∞ 1)
    (ContinuousMap.toLp ∞ volume ℂ w)

theorem suzukiIntervalL1ContinuousPairing_eq_integral
    (B : ℝ) (w : C(ClosedInterval 0 B, ℂ)) (f : IntervalL1 0 B) :
    suzukiIntervalL1ContinuousPairing B w f =
      ∫ x : ClosedInterval 0 B, w x * f x ∂volume := by
  rw [suzukiIntervalL1ContinuousPairing,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp
    (𝕜 := ℂ) (p := (∞ : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 B))) w] with x hx
  rw [hx]
  simp [complexMulBilinear]

/-- Pairing the sharp cutoff of a continuous representative is the ordinary interval integral.
This is the finite-window moving-boundary identity before differentiation. -/
theorem suzukiIntervalL1ContinuousPairing_cutoff_toLp
    {B b : ℝ} (hb0 : 0 ≤ b) (hbB : b ≤ B)
    (w f : C(ClosedInterval 0 B, ℂ)) :
    suzukiIntervalL1ContinuousPairing B w
        (suzukiApertureCutoffL1 b B
          (ContinuousMap.toLp 1 volume ℂ f)) =
      ∫ x in (0 : ℝ)..b,
        w (Set.projIcc 0 B (by linarith) x) *
          f (Set.projIcc 0 B (by linarith) x) := by
  rw [suzukiIntervalL1ContinuousPairing_eq_integral]
  have hcut := suzukiApertureCutoffL1_ae b B
    (ContinuousMap.toLp 1 volume ℂ f)
  have hf := ContinuousMap.coeFn_toLp
    (𝕜 := ℂ) (p := (1 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 B))) f
  let F : ℝ → ℂ := fun x =>
    w (Set.projIcc 0 B (by linarith) x) *
      f (Set.projIcc 0 B (by linarith) x)
  calc
    (∫ x : ClosedInterval 0 B,
        w x * suzukiApertureCutoffL1 b B
          (ContinuousMap.toLp 1 volume ℂ f) x ∂volume) =
        ∫ x : ClosedInterval 0 B,
          (suzukiApertureSet b B).indicator (fun x => F (x : ℝ)) x
            ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcut, hf] with x hcutx hfx
      rw [hcutx]
      by_cases hx : x ∈ suzukiApertureSet b B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hfx]
        dsimp only [F]
        rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) x.property]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    _ = ∫ x in (0 : ℝ)..b, F x :=
      integral_subtype_apertureSet_eq_intervalIntegral B b hb0 hbB F
    _ = _ := rfl

/-- **Moving-aperture scalar Leibniz rule.**  If `u(a)` has continuous representative `f`, then
every continuous weighted scalar pairing of `1_[0,b] u(b)` is differentiable at `a`.  Its
derivative is the pairing of the strong `L¹` derivative on `[0,a]` plus the genuine endpoint
term `w(a)f(a)`.  No differentiability of the sharp cutoff as an `L¹` curve is asserted. -/
theorem hasDerivAt_suzukiIntervalL1ContinuousPairing_apertureCutoff
    {B a : ℝ} (ha0 : 0 < a) (haB : a < B)
    {u : ℝ → IntervalL1 0 B} {du : IntervalL1 0 B}
    (hu : HasDerivAt u du a)
    (f w : C(ClosedInterval 0 B, ℂ))
    (huf : u a = ContinuousMap.toLp 1 volume ℂ f) :
    HasDerivAt
      (fun b : ℝ => suzukiIntervalL1ContinuousPairing B w
        (suzukiApertureCutoffL1 b B (u b)))
      (suzukiIntervalL1ContinuousPairing B w
          (suzukiApertureCutoffL1 a B du) +
        w ⟨a, ⟨ha0.le, haB.le⟩⟩ * f ⟨a, ⟨ha0.le, haB.le⟩⟩) a := by
  let L := suzukiIntervalL1ContinuousPairing B w
  let g : ℝ → ℂ := fun x =>
    w (Set.projIcc 0 B (by linarith) x) *
      f (Set.projIcc 0 B (by linarith) x)
  have hcenter := hasDerivAt_suzukiApertureCutoffL1_centered B a hu
  have hfirst : HasDerivAt
      (fun b : ℝ => L (suzukiApertureCutoffL1 b B (u b - u a)))
      (L (suzukiApertureCutoffL1 a B du)) a :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt a hcenter
  have hg : Continuous g := by
    exact (w.continuous.comp continuous_projIcc).mul
      (f.continuous.comp continuous_projIcc)
  have hsecond : HasDerivAt (fun b : ℝ => ∫ x in (0 : ℝ)..b, g x)
      (g a) a := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hg.intervalIntegrable _ _
    · exact hg.aestronglyMeasurable.stronglyMeasurableAtFilter
    · exact hg.continuousAt
  have hsum := hfirst.add hsecond
  have hev :
      (fun b : ℝ => L (suzukiApertureCutoffL1 b B (u b))) =ᶠ[𝓝 a]
        fun b : ℝ =>
          L (suzukiApertureCutoffL1 b B (u b - u a)) +
            ∫ x in (0 : ℝ)..b, g x := by
    filter_upwards [Icc_mem_nhds ha0 haB] with b hb
    have hfixed := suzukiIntervalL1ContinuousPairing_cutoff_toLp
      hb.1 hb.2 w f
    change L (suzukiApertureCutoffL1 b B
        (ContinuousMap.toLp 1 volume ℂ f)) =
      ∫ x in (0 : ℝ)..b, g x at hfixed
    rw [← hfixed, ← huf]
    change L (suzukiApertureCutoffL1 b B (u b)) =
      L (suzukiApertureCutoffL1 b B (u b - u a)) +
        L (suzukiApertureCutoffL1 b B (u a))
    rw [← map_add, ← map_add]
    simp
  have hga : g a =
      w ⟨a, ⟨ha0.le, haB.le⟩⟩ * f ⟨a, ⟨ha0.le, haB.le⟩⟩ := by
    dsimp only [g]
    rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) ⟨ha0.le, haB.le⟩]
  rw [← hga]
  exact hsum.congr_of_eventuallyEq hev

end RHTower
