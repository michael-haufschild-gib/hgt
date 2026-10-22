import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinSelectedXiPacket
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullTwoTail

/-!
# Smoothed short-interval prime mass tends to one in Route T

Let `N_X = X^{1000/299}`, `H_X = N_X / X^{999/1000}` (so `H_X = N_X^{701299/1000000}`), and let
`w_X = smoothWeight(N_X + H_X, H_X) - smoothWeight(N_X, H_X)`, a smooth window supported in
`[N_X, N_X + 2H_X]`. This module proves that the normalized smoothed von Mangoldt mass
`H_X⁻¹ ∑ Λ(n) w_X(n)` tends to `1` as `X → ∞`. The proof assembles three limits: the selected
arithmetic edge on `Re s = 2` minus its polar part tends to `0` (from the contour explicit formula
and the vanishing zero packet), the polar edge tends to the residue `2π`, and the tail beyond the
selected height tends to `0`. A Mellin–Perron identity identifies the full edge integral with
`2π H_X⁻¹ ∑ Λ(n) w_X(n)`.

## Main results

- `tendsto_inghamRouteTBufferedFullTwoVonMangoldtEdge_two_pi`: the full edge
  `∫_ℝ (∑ Λ(n) n^{-(2+it)}) K_X(2+it) dt` tends to `2π`.
- `smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_logDeriv_integral`: for `N, H > 0`,
  `2π H⁻¹ ∑ Λ(n) w_{N,H}(n) = ∫_ℝ (-ζ'/ζ)(2+iy) K_{N,H}(2+iy) dy`.
- `inghamRouteTBufferedNormalizedVonMangoldtMass`: the normalized mass `H_X⁻¹ ∑ Λ(n) w_X(n)`.
- `tendsto_inghamRouteTBufferedNormalizedVonMangoldtMass_one`: that mass tends to `1`.

## Hypotheses

The main results are unconditional: no analytic premise appears in any statement. The Perron
identity needs only `0 < N` and `0 < H`, and the edge identity `X ≥ 1`.
-/

open Complex Filter Topology Set Finset
open MeasureTheory ArithmeticFunction
open GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

noncomputable section

/-- The selected von Mangoldt edge on `Re s = 2` minus its polar edge `∫ (s-1)⁻¹ K_X(s)` tends to
`0`, by the explicit formula and the vanishing of the selected zero packet. -/
theorem tendsto_inghamRouteTBufferedSelectedTwoVonMangoldtEdge_sub_pole_zero :
    Tendsto (fun X : ℕ =>
      inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoPoleEdge X) atTop (𝓝 0) := by
  have hsum := tendsto_routeTBufferedNegativeHalf_arithmetic_explicitFormula_zero
  have hzero := tendsto_inghamRouteTBufferedSelectedNegativeHalfZeroPacket_zero
  have hIsmul : Tendsto (fun X : ℕ =>
      I • (inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoPoleEdge X)) atTop (𝓝 0) := by
    apply (tendsto_congr' (Filter.Eventually.of_forall fun X => by
      change I • (inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
          inghamRouteTBufferedSelectedTwoPoleEdge X) =
        (I • (inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
            inghamRouteTBufferedSelectedTwoPoleEdge X) +
          inghamRouteTBufferedSelectedNegativeHalfZeroPacket X) -
            inghamRouteTBufferedSelectedNegativeHalfZeroPacket X
      abel)).mpr
    simpa using hsum.sub hzero
  have hmul := hIsmul.const_mul (-I)
  have hpoint (z : ℂ) : (-I) * (I • z) = z := by
    rw [smul_eq_mul]
    calc
      (-I) * (I * z) = ((-I) * I) * z := by ring
      _ = z := by rw [neg_mul, I_mul_I]; ring
  simpa only [hpoint, mul_zero] using hmul

/-- `i` times the selected von Mangoldt edge tends to the residue value `2πi`. -/
theorem tendsto_inghamRouteTBufferedSelectedTwoVonMangoldtEdge_residue :
    Tendsto (fun X : ℕ => I • inghamRouteTBufferedSelectedTwoVonMangoldtEdge X)
      atTop (𝓝 (2 * Real.pi * I)) := by
  have hdiff : Tendsto (fun X : ℕ =>
      I • (inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoPoleEdge X)) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (I : ℂ)) atTop (𝓝 I)).smul
        tendsto_inghamRouteTBufferedSelectedTwoVonMangoldtEdge_sub_pole_zero
  have hadd := hdiff.add tendsto_inghamRouteTBufferedSelectedTwoPoleEdge_residue
  apply (tendsto_congr' (Filter.Eventually.of_forall fun X => by
    change I • inghamRouteTBufferedSelectedTwoVonMangoldtEdge X =
      I • (inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoPoleEdge X) +
          I • inghamRouteTBufferedSelectedTwoPoleEdge X
    module)).mpr
  simpa using hadd

/-- `i` times the full (untruncated) von Mangoldt edge tends to `2πi`. -/
theorem tendsto_inghamRouteTBufferedFullTwoVonMangoldtEdge_residue :
    Tendsto (fun X : ℕ => I • inghamRouteTBufferedFullTwoVonMangoldtEdge X)
      atTop (𝓝 (2 * Real.pi * I)) := by
  have htail : Tendsto (fun X : ℕ =>
      I • (inghamRouteTBufferedFullTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoVonMangoldtEdge X)) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (I : ℂ)) atTop (𝓝 I)).smul
        tendsto_inghamRouteTBufferedFullTwoVonMangoldtEdge_sub_selected_zero
  have hadd := htail.add
    tendsto_inghamRouteTBufferedSelectedTwoVonMangoldtEdge_residue
  apply (tendsto_congr' (Filter.Eventually.of_forall fun X => by
    change I • inghamRouteTBufferedFullTwoVonMangoldtEdge X =
      I • (inghamRouteTBufferedFullTwoVonMangoldtEdge X -
        inghamRouteTBufferedSelectedTwoVonMangoldtEdge X) +
          I • inghamRouteTBufferedSelectedTwoVonMangoldtEdge X
    module)).mpr
  simpa using hadd

/-- The full von Mangoldt edge `∫_ℝ (∑ Λ(n) n^{-(2+it)}) K_X(2+it) dt` tends to `2π`. -/
theorem tendsto_inghamRouteTBufferedFullTwoVonMangoldtEdge_two_pi :
    Tendsto inghamRouteTBufferedFullTwoVonMangoldtEdge atTop
      (𝓝 ((2 * Real.pi : ℝ) : ℂ)) := by
  have hmul := tendsto_inghamRouteTBufferedFullTwoVonMangoldtEdge_residue.const_mul (-I)
  have hpoint (z : ℂ) : (-I) * (I • z) = z := by
    rw [smul_eq_mul]
    calc
      (-I) * (I * z) = ((-I) * I) * z := by ring
      _ = z := by rw [neg_mul, I_mul_I]; ring
  have htarget : (-I) * (2 * Real.pi * I) = ((2 * Real.pi : ℝ) : ℂ) := by
    calc
      (-I) * (2 * Real.pi * I) = (2 * Real.pi) * ((-I) * I) := by ring
      _ = ((2 * Real.pi : ℝ) : ℂ) := by
        rw [neg_mul, I_mul_I]
        norm_cast
        norm_num
  simpa only [hpoint, htarget] using hmul

/-- For `H > 0`, `n ↦ Λ(n) smoothWeight(N, H, n)` is summable, being supported on `n < N + H`. -/
theorem summable_complex_vonMangoldt_mul_smoothWeight
    {N H : ℝ} (hH : 0 < H) :
    Summable fun n : ℕ => ((vonMangoldt n : ℝ) : ℂ) *
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  refine summable_of_ne_finset_zero
    (s := Finset.range (⌈N + H⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range] at hn
  have hge : N + H ≤ (n : ℝ) := by
    have hceil : N + H ≤ (⌈N + H⌉₊ : ℝ) := Nat.le_ceil _
    have hncast : ((⌈N + H⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_not_lt hn
    push_cast at hncast
    linarith
  have hzero := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH hge
  rw [hzero]
  simp

/-- Mellin–Perron identity for the smooth window: for `N, H > 0`,
`2π H⁻¹ ∑ Λ(n) w_{N,H}(n) = ∫_ℝ (-ζ'/ζ)(2+iy) K_{N,H}(2+iy) dy`. -/
theorem smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_logDeriv_integral
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    (2 * Real.pi : ℝ) • ((H : ℂ)⁻¹ *
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
      ∫ y : ℝ,
        (-(deriv riemannZeta (((2 : ℝ) : ℂ) + (y : ℝ) * I)) /
            riemannZeta (((2 : ℝ) : ℂ) + (y : ℝ) * I)) *
          routeTNormalizedSmoothWindowMellin N H
            (((2 : ℝ) : ℂ) + (y : ℝ) * I) := by
  let F : ℝ → ℂ := fun y =>
    -(deriv riemannZeta (((2 : ℝ) : ℂ) + (y : ℝ) * I)) /
      riemannZeta (((2 : ℝ) : ℂ) + (y : ℝ) * I)
  let Mplus : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
        (((2 : ℝ) : ℂ) + (y : ℝ) * I)
  let Mbase : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
        (((2 : ℝ) : ℂ) + (y : ℝ) * I)
  let Mroute : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ))
      (((2 : ℝ) : ℂ) + (y : ℝ) * I)
  have hplusSum := summable_complex_vonMangoldt_mul_smoothWeight
    (N := N + H) hH
  have hbaseSum := summable_complex_vonMangoldt_mul_smoothWeight
    (N := N) hH
  have hsumRoute :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ)) -
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
    rw [← hplusSum.tsum_sub hbaseSum]
    apply tsum_congr
    intro n
    rw [routeTSmoothWindowWeight]
    push_cast
    ring
  have hFcont : Continuous F := by
    simpa only [F] using (continuous_neg_logDeriv_line (d := 2) (by norm_num))
  have hFbound : ∀ y : ℝ, ‖F y‖ ≤ 8 := by
    intro y
    calc
      ‖F y‖ ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
        simpa only [F] using norm_neg_logDeriv_le_line
          (d := 2) (y := y) (by norm_num)
      _ ≤ 8 := by
        have h := tsum_vonMangoldt_rpow_neg_le
          (d := 2) (by norm_num) (by norm_num)
        convert h using 1 <;> norm_num
  have hMplusInt : Integrable Mplus := by
    simpa only [Mplus, Complex.VerticalIntegrable] using verticalIntegrable_mellin_smoothWeight
      (N := N + H) (H := H) (σ := 2) (by linarith) hH (by norm_num)
  have hMbaseInt : Integrable Mbase := by
    simpa only [Mbase, Complex.VerticalIntegrable] using verticalIntegrable_mellin_smoothWeight
      (N := N) (H := H) (σ := 2) hN hH (by norm_num)
  have hplusInt : Integrable (fun y => F y * Mplus y) :=
    hMplusInt.bdd_mul hFcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hFbound)
  have hbaseInt : Integrable (fun y => F y * Mbase y) :=
    hMbaseInt.bdd_mul hFcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hFbound)
  have hplusPerron := tsum_vonMangoldt_smoothWeight_eq_logDeriv_integral
    (N := N + H) (H := H) (d := 2) (by linarith) hH (by norm_num)
  have hbasePerron := tsum_vonMangoldt_smoothWeight_eq_logDeriv_integral
    (N := N) (H := H) (d := 2) hN hH (by norm_num)
  have hraw :
      (2 * Real.pi : ℝ) •
        (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
        ∫ y : ℝ, F y * Mroute y := by
    calc
      (2 * Real.pi : ℝ) •
          (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
        (2 * Real.pi : ℝ) •
            (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ)) -
          (2 * Real.pi : ℝ) •
            (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
          rw [hsumRoute, smul_sub]
      _ = (∫ y : ℝ, F y * Mplus y) - ∫ y : ℝ, F y * Mbase y := by
        simpa only [F, Mplus, Mbase] using congrArg₂ (· - ·) hplusPerron hbasePerron
      _ = ∫ y : ℝ, (F y * Mplus y - F y * Mbase y) := by
        rw [integral_sub hplusInt hbaseInt]
      _ = ∫ y : ℝ, F y * Mroute y := by
        apply integral_congr_ae
        filter_upwards with y
        have hmellin := mellin_routeTSmoothWindowWeight_eq_sub
          hN.le hH (s := (((2 : ℝ) : ℂ) + (y : ℝ) * I)) (by norm_num)
        dsimp only [Mplus, Mbase, Mroute]
        rw [hmellin]
        ring
  calc
    (2 * Real.pi : ℝ) • ((H : ℂ)⁻¹ *
        (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) =
      (H : ℂ)⁻¹ * ((2 * Real.pi : ℝ) •
        (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))) := by
        exact (mul_smul_comm (2 * Real.pi : ℝ) (H : ℂ)⁻¹ _).symm
    _ = (H : ℂ)⁻¹ * ∫ y : ℝ, F y * Mroute y := by rw [hraw]
    _ = ∫ y : ℝ, (H : ℂ)⁻¹ * (F y * Mroute y) := by
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ y : ℝ,
        (-(deriv riemannZeta (((2 : ℝ) : ℂ) + (y : ℝ) * I)) /
            riemannZeta (((2 : ℝ) : ℂ) + (y : ℝ) * I)) *
          routeTNormalizedSmoothWindowMellin N H
            (((2 : ℝ) : ℂ) + (y : ℝ) * I) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [routeTNormalizedSmoothWindowMellin]
      dsimp only [F, Mroute]
      ring

/-- The normalized smoothed prime mass `H_X⁻¹ ∑ Λ(n) w_X(n)` of Route T's short window. -/
def inghamRouteTBufferedNormalizedVonMangoldtMass (X : ℕ) : ℂ :=
  (inghamRouteTMellinBufferedPhysicalWidth X : ℂ)⁻¹ *
    (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
      ((routeTSmoothWindowWeight
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (n : ℝ) : ℝ) : ℂ))

/-- For `X ≥ 1`, the full von Mangoldt edge equals `2π` times the normalized prime mass. -/
theorem inghamRouteTBufferedFullTwoVonMangoldtEdge_eq_physicalMass
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTBufferedFullTwoVonMangoldtEdge X =
      (2 * Real.pi : ℝ) • inghamRouteTBufferedNormalizedVonMangoldtMass X := by
  have hN := inghamRouteTMellinPhysicalCenter_pos hX
  have hH := inghamRouteTMellinBufferedPhysicalWidth_pos hX
  have hperron :=
    smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_logDeriv_integral
      hN hH
  rw [inghamRouteTBufferedFullTwoVonMangoldtEdge,
    inghamRouteTBufferedNormalizedVonMangoldtMass]
  calc
    (∫ t : ℝ,
        (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X)
            (((2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ,
        (-(deriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X)
            (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rw [tsum_vonMangoldt_cpow_eq (by norm_num)]
    _ = _ := hperron.symm

/-- Short-interval prime mass: `H_X⁻¹ ∑ Λ(n) w_X(n) → 1` as `X → ∞`, where `w_X` is the smooth
window at `N_X = X^{1000/299}` of width `H_X = N_X / X^{999/1000}`. -/
theorem tendsto_inghamRouteTBufferedNormalizedVonMangoldtMass_one :
    Tendsto inghamRouteTBufferedNormalizedVonMangoldtMass atTop (𝓝 1) := by
  have hfull := tendsto_inghamRouteTBufferedFullTwoVonMangoldtEdge_two_pi
  have hscaled : Tendsto (fun X : ℕ =>
      (((2 * Real.pi : ℝ) : ℂ))⁻¹ *
        inghamRouteTBufferedFullTwoVonMangoldtEdge X) atTop (𝓝 1) := by
    have hmul := hfull.const_mul (((2 * Real.pi : ℝ) : ℂ))⁻¹
    have hc : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
    simpa only [inv_mul_cancel₀ hc] using hmul
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  rw [inghamRouteTBufferedFullTwoVonMangoldtEdge_eq_physicalMass hX]
  rw [Complex.real_smul]
  have hc : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  rw [inv_mul_cancel_left₀ hc]

end


end RHTower.Sieve
