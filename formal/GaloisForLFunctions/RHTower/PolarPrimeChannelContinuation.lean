import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Complex-analytic continuation of the prime-Laplace channel

The Euler-region complex continuation of the von Mangoldt prime channel of
`ccm-polar-prime-critical-mellin-defect-law`.  The card's resolved real channel
`vonMangoldtPrimeLaplaceChannel : ℝ → ℂ` equals `-ζ'/ζ(s+1)` for `s > 0`
(`vonMangoldtPrimeLaplaceChannel_eq_logDeriv`); its natural complex extension is

`vonMangoldtPrimeChannelComplex s = -ζ'(s+1)/ζ(s+1)`,

which agrees with the real channel on `s > 0` and is **holomorphic on the whole right half-plane
`Re s > 0`** (from `differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re`, since `Re(s+1) > 1` puts
`s+1` in `ζ`'s zero-free absolute-convergence region).  This is the analytic backbone of the card's
open "full complex continuation" — the holomorphic Euler-region piece; continuation past `Re s = 0`
(across the critical line) is the distributional/autocorrelation Stieltjes layer that remains open.
-/

open Filter Topology

namespace RHTower

/-- The complex extension of the von Mangoldt prime-Laplace channel: `-ζ'(s+1)/ζ(s+1)`. -/
noncomputable def vonMangoldtPrimeChannelComplex (s : ℂ) : ℂ :=
  -deriv riemannZeta (s + 1) / riemannZeta (s + 1)

/-- The complex channel agrees with the card's resolved real channel on `s > 0`. -/
theorem vonMangoldtPrimeChannelComplex_eq_channel {s : ℝ} (hs : 0 < s) :
    vonMangoldtPrimeChannelComplex (s : ℂ) = vonMangoldtPrimeLaplaceChannel s := by
  rw [vonMangoldtPrimeChannelComplex, vonMangoldtPrimeLaplaceChannel_eq_logDeriv hs]
  push_cast
  ring_nf

/-- **The prime channel is holomorphic at every `s` with `Re s > 0`** — `-ζ'/ζ(s+1)` with `s+1` in the
Euler region `Re > 1`. -/
theorem vonMangoldtPrimeChannelComplex_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ vonMangoldtPrimeChannelComplex s := by
  have hre : 1 < (s + 1).re := by rw [Complex.add_re]; simp; linarith
  exact (differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re hre).comp s
    (differentiableAt_id.add_const 1)

/-- **The prime channel is holomorphic on the right half-plane `Re s > 0`.** -/
theorem vonMangoldtPrimeChannelComplex_differentiableOn :
    DifferentiableOn ℂ vonMangoldtPrimeChannelComplex {s : ℂ | 0 < s.re} :=
  fun _ hs => (vonMangoldtPrimeChannelComplex_differentiableAt hs).differentiableWithinAt

/-- **Closed form of the critical Mellin-defect Laplace channel** (card eq. (22)/(25)).  In the shifted
coordinate `s` (with `z = s + ½`), the signed carrier Laplace transform `∫₀^∞ e^{-zh} dR(h)` is the
completed logarithmic source `1/s + 1/(s+1) + ζ'/ζ(s+1)`: the continuous polar part contributes the two
elementary poles `1/(z-½) + 1/(z+½)`, and the prime part `-ζ'/ζ(z+½)` supplies the divisor-sensitive
term.  A factorization that replaces the carrier by its prime-number-theorem main term deletes exactly
this `ζ'/ζ` pole data. -/
theorem criticalMellinDefectLaplaceChannel_eq {s : ℝ} (hs : 0 < s) :
    criticalMellinDefectLaplaceChannel s
      = 1 / (s : ℂ) + 1 / ((s : ℂ) + 1)
        + deriv riemannZeta ((s + 1 : ℝ) : ℂ) / riemannZeta ((s + 1 : ℝ) : ℂ) := by
  rw [criticalMellinDefectLaplaceChannel, continuousPolarLaplaceChannel_eq hs,
    vonMangoldtPrimeLaplaceChannel_eq_logDeriv hs]
  push_cast
  ring

/-- Complex lift of the critical Mellin-defect carrier Laplace transform: `1/s + 1/(s+1) + ζ'/ζ(s+1)`,
written through the holomorphic prime channel `-ζ'/ζ(s+1)`. -/
noncomputable def criticalMellinDefectChannelComplex (s : ℂ) : ℂ :=
  1 / s + 1 / (s + 1) - vonMangoldtPrimeChannelComplex s

/-- The complex carrier channel agrees with the card's resolved real Laplace channel on `s > 0`. -/
theorem criticalMellinDefectChannelComplex_eq_channel {s : ℝ} (hs : 0 < s) :
    criticalMellinDefectChannelComplex (s : ℂ) = criticalMellinDefectLaplaceChannel s := by
  rw [criticalMellinDefectChannelComplex, criticalMellinDefectLaplaceChannel_eq hs,
    vonMangoldtPrimeChannelComplex]
  push_cast
  ring

/-- **The critical Mellin-defect carrier channel is holomorphic at every `s` with `Re s > 0`.**  The two
elementary polar terms are holomorphic there (`s ≠ 0`, `s + 1 ≠ 0`) and the prime channel `-ζ'/ζ(s+1)` is
holomorphic on `Re s > 0` (`vonMangoldtPrimeChannelComplex_differentiableAt`). -/
theorem criticalMellinDefectChannelComplex_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ criticalMellinDefectChannelComplex s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at hre; linarith
  have d1 : DifferentiableAt ℂ (fun s : ℂ => 1 / s) s :=
    (differentiableAt_const 1).div differentiableAt_id hs0
  have d2 : DifferentiableAt ℂ (fun s : ℂ => 1 / (s + 1)) s :=
    (differentiableAt_const 1).div (differentiableAt_id.add_const 1) hs1
  have d3 : DifferentiableAt ℂ vonMangoldtPrimeChannelComplex s :=
    vonMangoldtPrimeChannelComplex_differentiableAt hs
  exact (d1.add d2).sub d3

/-- **The critical Mellin-defect carrier channel is holomorphic on the right half-plane `Re s > 0`** —
the Euler-region complex continuation of the card's signed boundary-measure Laplace transform `(22)`.
Continuation past `Re s = 0` (across the critical line) is the distributional/autocorrelation Stieltjes
layer that remains open. -/
theorem criticalMellinDefectChannelComplex_differentiableOn :
    DifferentiableOn ℂ criticalMellinDefectChannelComplex {s : ℂ | 0 < s.re} :=
  fun _ hs => (criticalMellinDefectChannelComplex_differentiableAt hs).differentiableWithinAt

/-- **The carrier channel is regular at the critical-line boundary `s = 0` (`z = ½`).**  Although the
polar term `1/s` and the prime term `ζ'/ζ(s+1)` each blow up at `s = 0` (`ζ`'s pole at `1`), their
singularities cancel: writing `ζ'/ζ(s+1) = logDeriv G(s+1) - 1/s` with `G = zetaResidueUnit` the analytic
unit `(s-1)ζ`, the carrier equals `1/(s+1) + logDeriv G(s+1)` off `0`, which extends continuously across
the boundary with finite value `1 + logDeriv G(1)`.  This is the polar–prime cancellation of the window
cards seen at the critical-line boundary of the CCM carrier — the Euler-region continuation reaches the
edge `Re s = 0` regularly, tightening the gap the open across-boundary Stieltjes layer must bridge. -/
theorem criticalMellinDefectChannelComplex_tendsto_at_zero :
    Tendsto criticalMellinDefectChannelComplex (𝓝[≠] 0)
      (𝓝 (1 + (Real.eulerMascheroniConstant : ℂ))) := by
  have hG1ne : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hsd0 : DifferentiableAt ℂ (fun s : ℂ => s + 1) 0 := differentiableAt_id.add_const 1
  have hshift : Tendsto (fun s : ℂ => s + 1) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun s : ℂ => s + 1) (𝓝 0) (𝓝 (0 + 1)) := hsd0.continuousAt
    rwa [zero_add] at h
  have hGne_near : ∀ᶠ s in 𝓝 (0 : ℂ), zetaResidueUnit (s + 1) ≠ 0 :=
    hshift.eventually zetaResidueUnit_ne_zero_eventually
  have hlogGcont : ContinuousAt (logDeriv zetaResidueUnit) 1 :=
    (zetaResidueUnit_analyticAt.deriv.continuousAt).div zetaResidueUnit_analyticAt.continuousAt hG1ne
  have hEq : criticalMellinDefectChannelComplex =ᶠ[𝓝[≠] 0]
      fun s => 1 / (s + 1) + logDeriv zetaResidueUnit (s + 1) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hGne_near] with s hs hGs
    have hs0 : s ≠ 0 := hs
    have hs1 : s + 1 ≠ 1 := fun h => hs0 (by linear_combination h)
    have hlogeq : (-deriv riemannZeta (s + 1)) / riemannZeta (s + 1)
        = -logDeriv zetaResidueUnit (s + 1) + s⁻¹ := by
      rw [neg_div, ← logDeriv_apply, logDeriv_zeta_eq hs1 hGs, show s + 1 - 1 = s by ring]
      ring
    rw [criticalMellinDefectChannelComplex, vonMangoldtPrimeChannelComplex, hlogeq]
    ring
  have hc1 : Tendsto (fun s : ℂ => 1 / (s + 1)) (𝓝[≠] 0) (𝓝 1) := by
    have h : Tendsto (fun s : ℂ => 1 / (s + 1)) (𝓝[≠] 0) (𝓝 (1 / ((0 : ℂ) + 1))) :=
      (continuousAt_const.div hsd0.continuousAt (by norm_num)).mono_left nhdsWithin_le_nhds
    simpa using h
  have hc2 : Tendsto (fun s : ℂ => logDeriv zetaResidueUnit (s + 1)) (𝓝[≠] 0)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    have h : Tendsto (fun s : ℂ => logDeriv zetaResidueUnit (s + 1)) (𝓝[≠] 0)
        (𝓝 (logDeriv zetaResidueUnit 1)) :=
      hlogGcont.tendsto.comp (hshift.mono_left nhdsWithin_le_nhds)
    rwa [logDeriv_zetaResidueUnit_one] at h
  exact (tendsto_congr' hEq).mpr (hc1.add hc2)

/-- **The carrier channel is regular at the critical-line boundary `s = 0` (`z = ½`).**  Although the
polar term `1/s` and the prime term `ζ'/ζ(s+1)` each blow up at `s = 0` (`ζ`'s pole at `1`), their
singularities cancel: writing `ζ'/ζ(s+1) = logDeriv G(s+1) - 1/s` with `G = zetaResidueUnit` the analytic
unit `(s-1)ζ`, the carrier equals `1/(s+1) + logDeriv G(s+1)` off `0`, which extends continuously across
the boundary with finite value `1 + γ` (Euler–Mascheroni), by `criticalMellinDefectChannelComplex_tendsto_at_zero`.
This is the polar–prime cancellation of the window cards seen at the critical-line boundary of the CCM
carrier — the Euler-region continuation reaches the edge `Re s = 0` regularly, tightening the gap the
open across-boundary Stieltjes layer must bridge. -/
theorem criticalMellinDefectChannelComplex_regular_at_zero :
    ∃ M : ℂ, Tendsto criticalMellinDefectChannelComplex (𝓝[≠] 0) (𝓝 M) :=
  ⟨_, criticalMellinDefectChannelComplex_tendsto_at_zero⟩

end RHTower
