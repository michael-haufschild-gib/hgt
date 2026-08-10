import GaloisForLFunctions.RHTower.DeningerLogSeries
import GaloisForLFunctions.RHTower.DeningerEvenPreimage

/-!
# The canonical preimage is continuous on the ray

In the logarithmic coordinate the Möbius series is a locally uniformly convergent series of
translates, hence continuous; composing with the logarithm makes the canonical preimage continuous
on the open positive ray.  Two functions continuous on an open set which agree almost everywhere
agree everywhere on it, so an almost-everywhere identification of the preimage is a pointwise one
on the ray.

* `deningerMobiusPreimage_continuousOn` : **`f_h` is continuous on `(0,∞)`.**
* `deningerEqOn_of_ae` : continuous data agreeing a.e. agree on an open set.
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- **The canonical preimage is continuous on the positive ray.** -/
theorem deningerMobiusPreimage_continuousOn {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    ContinuousOn (deningerMobiusPreimage h) (Set.Ioi 0) := by
  have hlog : ContinuousOn Real.log (Set.Ioi (0 : ℝ)) := fun x hx =>
    (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  have hcomp : ContinuousOn (fun x : ℝ => deningerLogSeries h 0 (Real.log x))
      (Set.Ioi (0 : ℝ)) :=
    (deningerLogSeries_continuous hh 0).comp_continuousOn hlog
  refine hcomp.congr fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  show deningerMobiusPreimage h x = deningerLogSeries h 0 (Real.log x)
  rw [deningerLogSeries_zero_eq, Real.exp_log hx0]

/-- The even extension is continuous on the positive ray. -/
theorem deningerEvenPreimage_continuousOn {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    ContinuousOn (deningerEvenPreimage h) (Set.Ioi 0) := by
  refine (deningerMobiusPreimage_continuousOn hh).congr fun x hx => ?_
  exact deningerEvenPreimage_of_pos h hx

/-- **Continuous data agreeing almost everywhere agree on an open set.** -/
theorem deningerEqOn_of_ae {u v : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s)
    (hu : ContinuousOn u s) (hv : ContinuousOn v s) (hae : u =ᵐ[volume] v) :
    Set.EqOn u v s := by
  intro x hx
  by_contra hne
  have hdiff : ContinuousOn (fun y : ℝ => ‖u y - v y‖) s := (hu.sub hv).norm
  have hopen : IsOpen (s ∩ (fun y : ℝ => ‖u y - v y‖) ⁻¹' Set.Ioi 0) :=
    hdiff.isOpen_inter_preimage hs isOpen_Ioi
  have hsub : (s ∩ (fun y : ℝ => ‖u y - v y‖) ⁻¹' Set.Ioi 0) ⊆ {y : ℝ | u y ≠ v y} := by
    intro y hy hcon
    have hzero : ‖u y - v y‖ = 0 := by rw [hcon, sub_self, norm_zero]
    have hlt : (0 : ℝ) < ‖u y - v y‖ := hy.2
    rw [hzero] at hlt
    exact absurd hlt (lt_irrefl 0)
  have hnull : volume (s ∩ (fun y : ℝ => ‖u y - v y‖) ⁻¹' Set.Ioi 0) = 0 :=
    measure_mono_null hsub hae
  have hmem : x ∈ s ∩ (fun y : ℝ => ‖u y - v y‖) ⁻¹' Set.Ioi 0 := by
    refine ⟨hx, ?_⟩
    have : u x - v x ≠ 0 := sub_ne_zero.mpr hne
    exact norm_pos_iff.mpr this
  have hempty : (s ∩ (fun y : ℝ => ‖u y - v y‖) ⁻¹' Set.Ioi 0) = ∅ := by
    by_contra hcon
    have hnonempty := Set.nonempty_iff_ne_empty.mpr hcon
    have hpos := hopen.measure_pos volume hnonempty
    rw [hnull] at hpos
    exact lt_irrefl 0 hpos
  rw [hempty] at hmem
  exact hmem

end

end RHTower
