import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinAtomicSelection
import GaloisForLFunctions.HTGeometry.ConfocalDefectNeutrality

/-!
# Inverse-scale transport of atomic Bernstein selection

The generic small-source packet theorem is transported along inverse radial scaling.  Its selected
amplitude is then identified intrinsically with the confocal envelope of the unscaled source.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- Inverse radial scaling preserves cofinite convergence to the origin. -/
theorem tendsto_inverseScaleAtomicNode_cofinite_zero
    {I : Type*} {z : I → ℂ} (hz0 : Tendsto z cofinite (nhds 0)) (R : ℝ) :
    Tendsto (inverseScaleAtomicNode z R) cofinite (nhds 0) := by
  have hscale : Tendsto (fun _ : I => (R⁻¹ : ℂ)) cofinite (nhds (R⁻¹ : ℂ)) :=
    tendsto_const_nhds
  have h2 : Tendsto (fun i : I => (R⁻¹ : ℂ) * z i) cofinite (nhds 0) := by
    simpa only [mul_zero] using hscale.mul hz0
  exact h2

/-- Nonzero inverse radial scaling preserves injectivity. -/
theorem inverseScaleAtomicNode_injective
    {I : Type*} {z : I → ℂ} (hzinj : Function.Injective z)
    {R : ℝ} (hR : 0 < R) :
    Function.Injective (inverseScaleAtomicNode z R) := by
  intro i j hij
  apply hzinj
  have hscalar : (R⁻¹ : ℂ) ≠ 0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne')
  exact mul_left_cancel₀ hscalar hij

/-- A source in the radius-`M` disk scales into the open half disk once `2M<R`. -/
theorem norm_inverseScaleAtomicNode_lt_half
    {I : Type*} {z : I → ℂ} {M R : ℝ}
    (hbound : ∀ i, ‖z i‖ ≤ M) (hR : 2 * M < R) :
    ∀ i, ‖inverseScaleAtomicNode z R i‖ < 1 / 2 := by
  intro i
  have hM : 0 ≤ M := (norm_nonneg (z i)).trans (hbound i)
  have hRpos : 0 < R := by linarith
  rw [inverseScaleAtomicNode_eq_div, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hRpos]
  have hMRhalf : M / R < 1 / 2 := by
    apply (div_lt_iff₀ hRpos).2
    linarith
  exact ((div_le_div_iff_of_pos_right hRpos).2 (hbound i)).trans_lt hMRhalf

/-- A source in the radius-`M` disk scales into the open unit disk at the sharp radial threshold
`M<R`. -/
theorem norm_inverseScaleAtomicNode_lt_one
    {I : Type*} {z : I → ℂ} {M R : ℝ}
    (hbound : ∀ i, ‖z i‖ ≤ M) (hR : M < R) :
    ∀ i, ‖inverseScaleAtomicNode z R i‖ < 1 := by
  intro i
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg (z i)) ((hbound i).trans_lt hR)
  rw [inverseScaleAtomicNode_eq_div, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hRpos]
  exact (div_lt_one hRpos).2 ((hbound i).trans_lt hR)

/-- Inverse positive radial scaling preserves the nonnegative-real orientation. -/
theorem inverseScaleAtomicNode_re_nonneg_of_im_eq_zero
    {I : Type*} {z : I → ℂ} {R : ℝ} (hR : 0 < R)
    (hreal : ∀ i, (z i).im = 0 → 0 ≤ (z i).re) :
    ∀ i, (inverseScaleAtomicNode z R i).im = 0 →
      0 ≤ (inverseScaleAtomicNode z R i).re := by
  intro i hui
  rw [inverseScaleAtomicNode_eq_div, Complex.div_im] at hui
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    Complex.normSq_ofReal] at hui
  have hzim : (z i).im = 0 := by
    have hui' : (z i).im * R / (R * R) = 0 := by
      simpa only [zero_div, sub_zero] using hui
    have hnum : (z i).im * R = 0 :=
      (div_eq_zero_iff.mp hui').resolve_right
        (mul_ne_zero hR.ne' hR.ne')
    exact (mul_eq_zero.mp hnum).resolve_right hR.ne'
  rw [inverseScaleAtomicNode_eq_div, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    Complex.normSq_ofReal]
  simpa only [zero_div, add_zero] using
    div_nonneg (mul_nonneg (hreal i hzim) hR.le)
      (mul_nonneg hR.le hR.le)

/-- Inverse positive radial scaling preserves a nonzero imaginary coordinate. -/
theorem inverseScaleAtomicNode_im_ne_zero
    {I : Type*} {z : I → ℂ} {R : ℝ} (hR : 0 < R)
    {i : I} (hi : (z i).im ≠ 0) :
    (inverseScaleAtomicNode z R i).im ≠ 0 := by
  rw [inverseScaleAtomicNode_eq_div, Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    Complex.normSq_ofReal]
  simpa only [zero_div, sub_zero] using
    div_ne_zero (mul_ne_zero hi hR.ne') (mul_ne_zero hR.ne' hR.ne')

/-- At every radius larger than the source norm bound, neutral normalized amplitudes select the
confocal amplitude envelope of the original source. -/
theorem exists_positive_halfOrder_inverseScaleAtomicPacket_of_neutral_amplitude
    {I : Type*} (c z : I → ℂ) (hc : Summable c)
    {M R : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hR : M < R)
    (hneutral : Tendsto
      (atomicBernsteinAmplitude (inverseScaleAtomicNode z R)) cofinite (nhds 1))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
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
  have huinj := inverseScaleAtomicNode_injective hzinj hRpos
  have huunit := norm_inverseScaleAtomicNode_lt_one hbound hR
  have hureal := inverseScaleAtomicNode_re_nonneg_of_im_eq_zero hRpos hreal
  have hui0 := inverseScaleAtomicNode_im_ne_zero hRpos hi0
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hhalfOrder⟩ :=
    exists_positive_halfOrder_atomicBernsteinPacket_of_neutral_amplitude
      c (inverseScaleAtomicNode z R) hc hneutral huinj hcne huunit hureal hui0
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
      (S := Set.range z) ⟨z i0, ⟨i0, rfl⟩⟩ hRpos
      (by rintro w ⟨i, rfl⟩; exact hbound i)
  have hBconf : B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R := by
    rw [← hconfocal]
    exact hsup.symm
  exact ⟨D, B, beta, L, hBconf, hB, hbeta1, hbeta, hDne, hD, hDsub,
    hL, hLpos, hhalfOrder⟩

/-- Cofinite convergence to the origin supplies the neutral-amplitude hypothesis of the sharp
inverse-scale selector. -/
theorem exists_positive_halfOrder_inverseScaleAtomicPacket
    {I : Type*} (c z : I → ℂ) (hc : Summable c)
    (hz0 : Tendsto z cofinite (nhds 0))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
    {M R : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hR : M < R)
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
  have hRpos : 0 < R := hM.trans_lt hR
  have hu0 := tendsto_inverseScaleAtomicNode_cofinite_zero hz0 R
  exact exists_positive_halfOrder_inverseScaleAtomicPacket_of_neutral_amplitude
    c z hc hM hbound hR
      (tendsto_atomicBernsteinAmplitude_cofinite_one hu0)
      hzinj hcne hreal hi0

/-- Cofinal vanishing of the intrinsic transverse defect is sufficient for the sharp inverse-scale
selector; the nodes may accumulate anywhere along the nonnegative focal segment. -/
theorem exists_positive_halfOrder_inverseScaleAtomicPacket_of_transverse_neutral
    {I : Type*} (c z : I → ℂ) (hc : Summable c)
    (htrans : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
    {M R : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hR : M < R)
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
  have hRpos : 0 < R := hM.trans_lt hR
  have hconf := HTGeometry.tendsto_confocalDefect_cofinite_zero_of_transverseDefect
    hR hbound htrans
  have hscaled : Tendsto
      (fun i => HTGeometry.confocalDefect R (z i) / R)
      cofinite (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using hconf.mul_const R⁻¹
  have hneutral : Tendsto
      (atomicBernsteinAmplitude (inverseScaleAtomicNode z R))
      cofinite (nhds 1) := by
    have hone : Tendsto (fun _ : I => (1 : ℝ)) cofinite (nhds 1) :=
      tendsto_const_nhds
    have hmodel : Tendsto
        (fun i => 1 + HTGeometry.confocalDefect R (z i) / R)
        cofinite (nhds 1) := by
      simpa using hone.add hscaled
    apply hmodel.congr'
    filter_upwards with i
    rw [atomicBernsteinAmplitude, inverseScaleAtomicNode_eq_div,
      HTGeometry.affineAmplitude_eq_one_add_confocalDefect_div hRpos]
  exact exists_positive_halfOrder_inverseScaleAtomicPacket_of_neutral_amplitude
    c z hc hM hbound hR hneutral hzinj hcne hreal hi0

end

end RHTower
