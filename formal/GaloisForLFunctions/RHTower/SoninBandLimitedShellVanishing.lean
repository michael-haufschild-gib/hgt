import GaloisForLFunctions.RHTower.SoninEvenCarrier
import GaloisForLFunctions.RHTower.L2FourierUncertainty

/-!
# A band-limited even vector vanishing on a physical shell is zero

The Fourier transform squares to reflection, so on the even subspace it is an involution.  A vector
killed by the Fourier transform of a bounded set is therefore the Fourier transform of a boundedly
supported vector, and the one-interval uncertainty principle applies to it: vanishing on any
nondegenerate physical shell already forces it to be zero.

This is the dual of `eq_zero_of_evenIndicatorCutoff_eq_self_of_evenFourierCutoff_eq_self`, and it is
sharper: only one interval of vanishing is assumed, not a whole complementary band.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory ContinuousLinearMap

/-- The Fourier transform is an involution on the even subspace. -/
theorem fourierUnitary_fourierUnitary_of_mem_evenSubspace
    {f : SoninL2} (hf : f ∈ evenSubspace) :
    fourierUnitary (fourierUnitary f) = f := by
  have h := l2_fourier_fourier f
  rw [show l2Reflection f = f from (mem_evenSubspace_iff f).mp hf] at h
  exact h

/-- **Band-limited even vectors cannot vanish on a physical shell.**  If an even vector is fixed by
the Fourier cutoff at some aperture and is annihilated by the physical shell between two smaller
apertures, it is zero. -/
theorem eq_zero_of_evenFourierCutoff_eq_self_of_shell_apply_eq_zero
    {t a b : ℝ} {v : evenSubspace} (ha : 0 ≤ a) (hab : a < b)
    (hR : evenFourierCutoff t v = v)
    (hshell : (evenIndicatorCutoff b - evenIndicatorCutoff a) v = 0) :
    v = 0 := by
  set f : SoninL2 := (v : SoninL2) with hfdef
  set g : SoninL2 := fourierUnitary f with hgdef
  -- `g` is supported in the central interval of radius `t`.
  have h0 :
      fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f = f := by
    have h := congrArg (fun w : evenSubspace => (w : SoninL2)) hR
    simpa using h
  have hfR :
      indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) g = g := by
    have h := congrArg fourierUnitary h0
    simpa only [hgdef, fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply] using h
  have hgsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc (-t) t → (g : ℝ → ℂ) x = 0 := by
    filter_upwards [indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) g]
      with x hx hout
    rw [hfR] at hx
    simpa [centralInterval, hout] using hx
  -- The Fourier transform of `g` is `f` again, by evenness.
  have hFg : fourierUnitary g = f := fourierUnitary_fourierUnitary_of_mem_evenSubspace v.property
  -- `f` vanishes on the physical shell.
  have hshellL2 :
      indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) f -
        indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0 := by
    have h := congrArg (fun w : evenSubspace => (w : SoninL2)) hshell
    simpa using h
  have hfzero : ∀ᵐ x ∂volume, x ∈ Set.Ioo a b → (f : ℝ → ℂ) x = 0 := by
    have hsub :
        (indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) f : ℝ → ℂ)
          =ᵐ[volume]
          (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f : ℝ → ℂ) := by
      have := sub_eq_zero.mp hshellL2
      rw [this]
    filter_upwards [hsub,
      indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b) f,
      indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f]
      with x hx hb hax hmem
    have hxb : x ∈ centralInterval b := by
      refine ⟨by linarith [hmem.1, hmem.2], hmem.2.le⟩
    have hxa : x ∉ centralInterval a := by
      intro hc
      exact absurd hc.2 (not_le.mpr hmem.1)
    rw [hb, Set.indicator_of_mem hxb] at hx
    rw [hax, Set.indicator_of_notMem hxa] at hx
    exact hx
  have hFzero : ∀ᵐ w ∂volume, w ∈ Set.Ioo a b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) w = 0 := by
    rw [hFg]
    exact hfzero
  have hgzero : g = 0 :=
    l2_eq_zero_of_bounded_support_fourier_vanishes_on_Ioo g hgsupp hab hFzero
  have hfzero' : f = 0 := by
    have := congrArg fourierUnitary hgzero
    rw [hFg] at this
    simpa using this
  have hcoe : (v : SoninL2) = ((0 : evenSubspace) : SoninL2) := by
    simpa [hfdef] using hfzero'
  exact Subtype.ext hcoe

end RHTower
