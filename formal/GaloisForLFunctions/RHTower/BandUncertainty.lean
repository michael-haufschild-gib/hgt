import GaloisForLFunctions.RHTower.BandLeakageSpectralTail
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import Mathlib.Analysis.Fourier.Inversion

/-!
# No test function on the band is band-limited

The spectral tail of a test function supported in `[-1, 1]` cannot vanish unless the function does.
The reason is analytic, not measure-theoretic: the spectral amplitude

```text
xi ↦ 𝓕 (trunc Phi) (xi)
```

is the restriction to the real axis of an *entire* function of the frequency, because the amplitude
lives on a compact interval.  If the tail mass vanishes, the amplitude vanishes almost everywhere on
an interval of frequencies beyond the band edge; a null set cannot swallow a punctured interval, so
the identity theorem forces the entire extension to vanish on all of `ℂ`.  Then the whole Fourier
transform is zero, and Fourier inversion returns the truncation at each of its continuity points —
that is, `Phi = 0` on the open band.

This is the qualitative uncertainty principle behind the strict band gap: the largest band eigenvalue
is never `1`, because an eigenfunction at `1` would carry no spectral mass outside the window.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-- The entire extension of the spectral amplitude of a band-truncated test function. -/
def bandFourierEntire (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  HTGeometry.compactFourier (fun x => ((Φ x : ℝ) : ℂ)) (-1) 1 (-(2 * (Real.pi : ℂ) * z))

theorem differentiable_bandFourierEntire {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Differentiable ℂ (bandFourierEntire Φ) := by
  have hcont : Continuous fun x : ℝ => ((Φ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hΦ
  have hinner : Differentiable ℂ fun z : ℂ => -(2 * (Real.pi : ℂ) * z) := by fun_prop
  exact (HTGeometry.differentiable_compactFourier hcont (-1) 1).comp hinner

/-- On the real axis the entire extension is mathlib's Fourier transform of the truncation. -/
theorem bandFourierEntire_ofReal (Φ : ℝ → ℝ) (ξ : ℝ) :
    bandFourierEntire Φ ((ξ : ℝ) : ℂ) = 𝓕 (bandTrunc Φ) ξ := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcast : ((-(2 * Real.pi * ξ) : ℝ) : ℂ) = -(2 * (Real.pi : ℂ) * (ξ : ℂ)) := by
    push_cast
    ring
  have heq : bandFourierEntire Φ ((ξ : ℝ) : ℂ) = bandFourier (-(2 * Real.pi * ξ)) Φ := by
    unfold bandFourierEntire HTGeometry.compactFourier bandFourier
    rw [hcast]
  rw [heq, bandFourier_eq_fourier]
  field_simp

/-- **The qualitative uncertainty principle for the band.**  A continuous test function whose spectral
mass outside the frequency window vanishes is zero on the open band. -/
theorem eqOn_zero_of_spectral_tail_eq_zero {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (htail : (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
        ‖𝓕 (bandTrunc Φ) ξ‖ ^ (2 : ℕ)) = 0) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, Φ x = 0 := by
  have hkpos : 0 < c / (2 * Real.pi) := div_pos hc (by positivity)
  -- the spectral density vanishes almost everywhere outside the window
  have hint : Integrable (fun ξ : ℝ => ‖𝓕 (bandTrunc Φ) ξ‖ ^ (2 : ℕ)) volume :=
    integrable_norm_sq_fourier_bandTrunc hΦ
  have hae : (fun ξ : ℝ => ‖𝓕 (bandTrunc Φ) ξ‖ ^ (2 : ℕ))
      =ᵐ[volume.restrict (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ξ => by positivity) hint.integrableOn).mp htail
  -- so it vanishes almost everywhere on an interval of frequencies beyond the band edge
  have hsub : Ioo (c / (2 * Real.pi) + 1 - 1 / 2) (c / (2 * Real.pi) + 1 + 1 / 2)
      ⊆ (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
    intro _
    linarith [ht.1]
  have hmono : volume.restrict (Ioo (c / (2 * Real.pi) + 1 - 1 / 2) (c / (2 * Real.pi) + 1 + 1 / 2))
      ≤ volume.restrict (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ :=
    Measure.restrict_mono hsub le_rfl
  have hae2 : ∀ᵐ t ∂(volume.restrict
      (Ioo (c / (2 * Real.pi) + 1 - 1 / 2) (c / (2 * Real.pi) + 1 + 1 / 2))),
      bandFourierEntire Φ ((t : ℝ) : ℂ) = 0 := by
    filter_upwards [ae_mono hmono hae] with t ht
    rw [bandFourierEntire_ofReal]
    have hsq : ‖𝓕 (bandTrunc Φ) t‖ ^ (2 : ℕ) = 0 := ht
    have hnorm : ‖𝓕 (bandTrunc Φ) t‖ = 0 := by
      nlinarith [norm_nonneg (𝓕 (bandTrunc Φ) t)]
    exact norm_eq_zero.mp hnorm
  -- the entire extension therefore vanishes identically
  have hzero : ∀ z : ℂ, bandFourierEntire Φ z = 0 :=
    HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval
      (t₀ := c / (2 * Real.pi) + 1) (r := 1 / 2)
      (differentiable_bandFourierEntire hΦ) (by norm_num) hae2
  have hfour : 𝓕 (bandTrunc Φ) = fun _ : ℝ => (0 : ℂ) := by
    funext ξ
    rw [← bandFourierEntire_ofReal]
    exact hzero _
  -- and Fourier inversion returns the truncation at every point of the open band
  have hf : Integrable (bandTrunc Φ) volume := integrable_bandTrunc hΦ
  have hFint : Integrable (𝓕 (bandTrunc Φ)) volume := by
    rw [hfour]
    exact integrable_zero ℝ ℂ volume
  intro x hx
  have hev : bandTrunc Φ =ᶠ[nhds x] fun y => ((Φ y : ℝ) : ℂ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [bandTrunc, Set.indicator_of_mem (Ioo_subset_Icc_self hy)]
  have hcontAt : ContinuousAt (bandTrunc Φ) x :=
    ((Complex.continuous_ofReal.comp hΦ).continuousAt).congr hev.symm
  have hinv := hf.fourierInv_fourier_eq hFint hcontAt
  rw [hfour] at hinv
  have hzero0 : 𝓕⁻ (fun _ : ℝ => (0 : ℂ)) x = 0 := by
    simp [Real.fourierInv_eq]
  rw [hzero0] at hinv
  have hval : bandTrunc Φ x = ((Φ x : ℝ) : ℂ) := by
    rw [bandTrunc, Set.indicator_of_mem (Ioo_subset_Icc_self hx)]
  rw [hval] at hinv
  exact_mod_cast hinv.symm

end GaloisForLFunctions.RHTower

end
