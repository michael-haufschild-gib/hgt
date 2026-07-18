import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinAtomicSelection
import GaloisForLFunctions.HTGeometry.ConfocalAbelDefectFlow

/-!
# Inverse-scale transport of atomic Bernstein selection

The generic small-source packet theorem is transported along inverse radial scaling.  Its selected
amplitude is then identified intrinsically with the confocal envelope of the unscaled source.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- At every radius larger than twice the source norm bound, the selected maximal amplitude is
exactly the confocal amplitude envelope of the original source. -/
theorem exists_positive_halfOrder_inverseScaleAtomicPacket
    {I : Type*} (c z : I → ℂ) (hc : Summable c)
    (hz0 : Tendsto z cofinite (nhds 0))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
    {M R : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hR : 2 * M < R)
    (hreal : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    {i0 : I} (hi0 : (z i0).im ≠ 0) :
    ∃ D : Finset I, ∃ B beta L : ℝ,
      B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ∧
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ i ∈ D,
        atomicBernsteinAmplitude (inverseScaleAtomicNode z R) i = B) ∧
      (∀ i ∉ D,
        atomicBernsteinAmplitude (inverseScaleAtomicNode z R) i ≤ beta) ∧
      L = ∑ v ∈ D.image (inverseScaleAtomicNode z R),
        ‖finiteExponentialFiberCoefficient D c (inverseScaleAtomicNode z R) v‖ ^ 2 *
          bernsteinAffineRowHalfOrderConstant v ∧
      0 < L ∧
      Tendsto
        (fun n : ℕ => Real.sqrt n *
          atomicBernsteinPacketSquareEnergy c (inverseScaleAtomicNode z R) n /
            (B ^ 2) ^ n)
        atTop (nhds L) := by
  have hRpos : 0 < R := by linarith
  have hu0 : Tendsto (inverseScaleAtomicNode z R) cofinite (nhds 0) := by
    have hscale : Tendsto (fun _ : I => (R⁻¹ : ℂ)) cofinite (nhds (R⁻¹ : ℂ)) :=
      tendsto_const_nhds
    simpa only [inverseScaleAtomicNode, mul_zero] using hscale.mul hz0
  have huinj : Function.Injective (inverseScaleAtomicNode z R) := by
    intro i j hij
    apply hzinj
    have hscalar : (R⁻¹ : ℂ) ≠ 0 := by
      change (R : ℂ)⁻¹ ≠ 0
      exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hRpos.ne')
    exact mul_left_cancel₀ hscalar hij
  have huhalf : ∀ i, ‖inverseScaleAtomicNode z R i‖ < 1 / 2 := by
    intro i
    rw [inverseScaleAtomicNode_eq_div, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hRpos]
    have hMRhalf : M / R < 1 / 2 := by
      apply (div_lt_iff₀ hRpos).2
      linarith
    exact ((div_le_div_iff_of_pos_right hRpos).2 (hbound i)).trans_lt hMRhalf
  have hureal : ∀ i,
      (inverseScaleAtomicNode z R i).im = 0 →
        0 ≤ (inverseScaleAtomicNode z R i).re := by
    intro i hui
    rw [inverseScaleAtomicNode_eq_div, Complex.div_im] at hui
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.normSq_ofReal] at hui
    have hzim : (z i).im = 0 := by
      have hui' : (z i).im * R / (R * R) = 0 := by
        simpa only [zero_div, sub_zero] using hui
      have hnum : (z i).im * R = 0 :=
        (div_eq_zero_iff.mp hui').resolve_right
          (mul_ne_zero hRpos.ne' hRpos.ne')
      exact (mul_eq_zero.mp hnum).resolve_right hRpos.ne'
    rw [inverseScaleAtomicNode_eq_div, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
      Complex.normSq_ofReal]
    simpa only [zero_div, add_zero] using
      div_nonneg (mul_nonneg (hreal i hzim) hRpos.le)
        (mul_nonneg hRpos.le hRpos.le)
  have hui0 : (inverseScaleAtomicNode z R i0).im ≠ 0 := by
    rw [inverseScaleAtomicNode_eq_div, Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.normSq_ofReal]
    simpa only [zero_div, sub_zero] using
      div_ne_zero (mul_ne_zero hi0 hRpos.ne')
        (mul_ne_zero hRpos.ne' hRpos.ne')
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hhalfOrder⟩ :=
    exists_positive_halfOrder_atomicBernsteinPacket_of_small_source
      c (inverseScaleAtomicNode z R) hc hu0 huinj hcne huhalf hureal hui0
  have hAll : ∀ i,
      atomicBernsteinAmplitude (inverseScaleAtomicNode z R) i ≤ B := by
    intro i
    by_cases hi : i ∈ D
    · exact (hD i hi).le
    · exact (hDsub i hi).trans hbeta.le
  let F : ℂ → ℝ := fun w => ‖w / (R : ℂ)‖ + ‖1 - w / (R : ℂ)‖
  have hupper : ∀ y ∈ F '' Set.range z, y ≤ B := by
    rintro y ⟨w, ⟨i, rfl⟩, rfl⟩
    simpa only [F, inverseScaleAtomicNode_eq_div, atomicBernsteinAmplitude] using hAll i
  have hbdd : BddAbove (F '' Set.range z) := ⟨B, hupper⟩
  have hDne' := hDne
  obtain ⟨iD, hiD⟩ := hDne'
  have hBmem : B ∈ F '' Set.range z := by
    refine ⟨z iD, ⟨iD, rfl⟩, ?_⟩
    simpa only [F, inverseScaleAtomicNode_eq_div, atomicBernsteinAmplitude] using
      hD iD hiD
  have hsup : sSup (F '' Set.range z) = B := by
    apply le_antisymm
    · exact csSup_le ⟨_, hBmem⟩ hupper
    · exact le_csSup hbdd hBmem
  have hconfocal :=
    HTGeometry.sSup_affineAmplitude_eq_confocalAmplitudeEnvelope
      (S := Set.range z) ⟨z i0, ⟨i0, rfl⟩⟩ hM hRpos
      (by rintro w ⟨i, rfl⟩; exact hbound i)
  have hBconf : B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R := by
    rw [← hconfocal]
    exact hsup.symm
  exact ⟨D, B, beta, L, hBconf, hB, hbeta1, hbeta, hDne, hD, hDsub,
    hL, hLpos, hhalfOrder⟩

end

end RHTower
