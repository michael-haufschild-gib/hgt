import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonMultiplierSymmetry
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandPotential

/-!
# On a frequency-diagonal background the band model is exact

The band programme replaces a potential `W` by `P_R W P_R` and pays an approximation error. For a
background that is diagonal in frequency there is no error to pay on band-limited data: the solution
stays inside the band for all time, and inside the band the truncated potential acts exactly as the
full one, because `P_R` commutes with a diagonal `W` and fixes the solution.

Duhamel uniqueness turns that pointwise identity of source terms into an identity of flows: the band
model reproduces the true solution exactly, for every time, with no error term at all.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandExact

variable {b : ℝ} {w : ℝ → E → ℂ}

/-- On a band-limited state a diagonal potential is unchanged by band truncation. -/
theorem kgSourceOp_kgBandOp_eq {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {R : ℝ} (hcomm : ∀ x : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R (W₀ x) = W₀ (kgLowPassOp R x))
    {v : KGEnergy E} (hv : kgLowPassOp R v.fst = v.fst) :
    kgSourceOp (kgBandOp W₀ R) v = kgSourceOp W₀ v := by
  have hc : kgLowPassOp R (kgFreqInvOp v.fst) = kgFreqInvOp (kgLowPassOp R v.fst) :=
    fourierMulCLM_kgFreqInvOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R) v.fst
  have hinv : kgLowPassOp R (kgFreqInvOp v.fst) = kgFreqInvOp v.fst := by
    rw [hc, hv]
  have hband : kgBandOp W₀ R (kgFreqInvOp v.fst) = W₀ (kgFreqInvOp v.fst) := by
    rw [kgBandOp_apply, hinv, hcomm, hinv]
  have hL : kgSourceOp (kgBandOp W₀ R) v
      = kgPair E (0, kgBandOp W₀ R (kgFreqInvOp v.fst)) := rfl
  have hR : kgSourceOp W₀ v = kgPair E (0, W₀ (kgFreqInvOp v.fst)) := rfl
  rw [hL, hR, hband]

/-- **On a frequency-diagonal background the band model is exact for band-limited data.** -/
theorem kgStateMildT_kgBandOp_eq (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    {R : ℝ} {g h : Lp ℂ 2 (volume : Measure E)} (hg : kgLowPassOp R g = g)
    (hh : kgLowPassOp R h = h) :
    kgStateMildT (fun r : ℝ => kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R) g h
      = kgStateMildT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h := by
  set W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :=
    fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r) with hW
  have hWb : ∀ r : ℝ, ‖W r‖ ≤ b := fun _ => norm_fourierMulCLM_le _ _ _
  have hBb : ∀ r : ℝ, ‖kgBandOp (W r) R‖ ≤ b := fun r => norm_kgBandOp_le hb0 (hWb r) R
  have hBs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgBandOp (W r) R x := fun x =>
    (kgLowPassOp R).continuous.comp (hWs (kgLowPassOp R x))
  have hcont := continuous_kgStateMildT hb0 hWb hWs g h
  have hcomm : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)),
      kgLowPassOp R (W r x) = W r (kgLowPassOp R x) := fun r x =>
    fourierMulCLM_comm (measurable_kgLowPass (E := E) R) (hw r) zero_le_one
      (norm_kgLowPass_le R) hb0 (hwb r) x
  have hfix : ∀ s : ℝ, kgLowPassOp R (kgStateMildT W g h s).fst
      = (kgStateMildT W g h s).fst := by
    intro s
    have hstate := kgFieldStateT_band_invariant hw hb0 hwb hWs hg hh s
    rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs] at hstate
    have hc := congrArg (fun z : KGEnergy E => z.fst) hstate
    simpa [kgDiagOp_apply] using hc
  refine (eq_kgStateMildT_of_duhamel hb0 hBb hBs g h hcont fun t => ?_).symm
  have hI : IntervalIntegrable
      (fun s : ℝ => kgStateKernelT W t s (kgStateMildT W g h s)) volume 0 t :=
    (((strongKernel_kgStateKernelT hWb hWs) _ hcont).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  have hduh := kgStateMildT_eq hb0 hWb hWs g h t
  rw [hduh]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [kgStateKernelT_apply, kgStateKernelT_apply,
    kgSourceOp_kgBandOp_eq (hcomm s) (hfix s)]

/-- The same, in the state register. -/
theorem kgFieldStateT_kgBandOp_eq (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    {R : ℝ} {g h : Lp ℂ 2 (volume : Measure E)} (hg : kgLowPassOp R g = g)
    (hh : kgLowPassOp R h = h) (t : ℝ) :
    kgFieldStateT (fun r : ℝ => kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R) g h t
      = kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t := by
  have hWb : ∀ r : ℝ, ‖fourierMulCLM (hw r) hb0 (hwb r)‖ ≤ b := fun _ =>
    norm_fourierMulCLM_le _ _ _
  have hBb : ∀ r : ℝ, ‖kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R‖ ≤ b := fun r =>
    norm_kgBandOp_le hb0 (hWb r) R
  have hBs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R x := fun x =>
    (kgLowPassOp R).continuous.comp (hWs (kgLowPassOp R x))
  rw [kgFieldStateT_eq_kgStateMildT hb0 hBb hBs, kgFieldStateT_eq_kgStateMildT hb0 hWb hWs,
    kgStateMildT_kgBandOp_eq hw hb0 hwb hWs hg hh]

/-- **The band energy is exact**: on a frequency-diagonal background a band-limited clock loses
nothing to band truncation, at any time. -/
theorem kgFieldEnergyT_kgBandOp_eq (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    {R : ℝ} {g h : Lp ℂ 2 (volume : Measure E)} (hg : kgLowPassOp R g = g)
    (hh : kgLowPassOp R h = h) (t : ℝ) :
    ‖kgFieldGradT (fun r : ℝ => kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R) g h t‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (fun r : ℝ => kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R) g h t‖ ^ (2 : ℕ)
      = ‖kgFieldGradT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t‖ ^ (2 : ℕ) := by
  have hstate := kgFieldStateT_kgBandOp_eq hw hb0 hwb hWs hg hh t
  rw [kgFieldEnergyT_eq_norm_sq, kgFieldEnergyT_eq_norm_sq, hstate]

end BandExact

end GaloisForLFunctions.HTGeometry
