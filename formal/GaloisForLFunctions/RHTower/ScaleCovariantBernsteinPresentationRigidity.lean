import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinAggregateSource

/-!
# Presentation rigidity of scale-covariant Bernstein tomography

The pointed real moment sequence need not determine an arbitrary complex atomic presentation.
Nevertheless, inside the defect-neutral transverse class it determines the confocal amplitude at
every common admissible scale.  The recession law then makes the limiting transverse-defect
envelope presentation-independent as well.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- **Fixed-scale presentation rigidity.**  Two defect-neutral transverse atomic presentations of
the same pointed real moments have the same confocal amplitude at every radius exceeding both
support bounds.  Thus the positive square-energy growth selects an intrinsic scale even when the
underlying atomic presentation is not known to be unique. -/
theorem confocalAmplitudeEnvelope_eq_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {i0 : I} (hi0 : (z i0).im ≠ 0)
    {j0 : J} (hj0 : (w j0).im ≠ 0) :
    HTGeometry.confocalAmplitudeEnvelope (Set.range z) R =
      HTGeometry.confocalAmplitudeEnvelope (Set.range w) R := by
  have hRpos : 0 < R := hM.trans_lt hRM
  obtain ⟨Bz, hBzConf, hBz, hlimZ⟩ :=
    exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy_of_transverse_neutral
      c z hc htransZ hzinj hcne hM hboundZ hRM (by norm_num : (0 : ℝ) < 2)
      hrealZ hi0
  obtain ⟨Bw, hBwConf, hBw, hlimW⟩ :=
    exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy_of_transverse_neutral
      d w hd htransW hwinj hdne hN hboundW hRN (by norm_num : (0 : ℝ) < 2)
      hrealW hj0
  have hobsZ : Tendsto
      (fun n : ℕ => scaleCovariantBernsteinObservation m n R ^ ((n : ℝ)⁻¹))
      atTop (nhds (Bz ^ (2 : ℝ))) := by
    apply hlimZ.congr'
    filter_upwards with n
    have hobs := scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hc hboundZ hmomentZ hRpos n
    rw [hobs, atomicBernsteinPacketSquareEnergy,
      ← finitePacketRpowEnergy_two_eq_squareEnergy]
  have hobsW : Tendsto
      (fun n : ℕ => scaleCovariantBernsteinObservation m n R ^ ((n : ℝ)⁻¹))
      atTop (nhds (Bw ^ (2 : ℝ))) := by
    apply hlimW.congr'
    filter_upwards with n
    have hobs := scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hd hboundW hmomentW hRpos n
    rw [hobs, atomicBernsteinPacketSquareEnergy,
      ← finitePacketRpowEnergy_two_eq_squareEnergy]
  have hsq : Bz ^ (2 : ℝ) = Bw ^ (2 : ℝ) :=
    tendsto_nhds_unique hobsZ hobsW
  have hsq' : Bz ^ (2 : ℕ) = Bw ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using hsq
  have hBz0 : 0 ≤ Bz := (by norm_num : (0 : ℝ) ≤ 1).trans hBz.le
  have hBw0 : 0 ≤ Bw := (by norm_num : (0 : ℝ) ≤ 1).trans hBw.le
  have hBeq : Bz = Bw := (sq_eq_sq₀ hBz0 hBw0).mp hsq'
  rw [← hBzConf, ← hBwConf, hBeq]

/-- The sharp quadratic coefficient is presentation-rigid as well: the common positive
observation has one common half-order asymptotic, normalized by the common selected amplitude. -/
theorem exists_common_halfOrder_limit_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {i0 : I} (hi0 : (z i0).im ≠ 0)
    {j0 : J} (hj0 : (w j0).im ≠ 0) :
    ∃ B L : ℝ,
      B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ∧
      B = HTGeometry.confocalAmplitudeEnvelope (Set.range w) R ∧
      1 < B ∧ 0 < L ∧
      Tendsto
        (fun n : ℕ => Real.sqrt n *
          scaleCovariantBernsteinObservation m n R / (B ^ 2) ^ n)
        atTop (nhds L) := by
  have hRpos : 0 < R := hM.trans_lt hRM
  obtain ⟨D, B, beta, L, hBz, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hLdef, hL, hhalf⟩ :=
    exists_positive_halfOrder_inverseScaleAtomicPacket_of_transverse_neutral
      c z hc htransZ hzinj hcne hM hboundZ hRM hrealZ hi0
  have hBzw := confocalAmplitudeEnvelope_eq_of_common_pointed_moments
    c z d w m hc hd htransZ htransW hzinj hwinj hcne hdne hM hN
    hboundZ hboundW hRM hRN hrealZ hrealW hmomentZ hmomentW hi0 hj0
  have hobs : Tendsto
      (fun n : ℕ => Real.sqrt n *
        scaleCovariantBernsteinObservation m n R / (B ^ 2) ^ n)
      atTop (nhds L) := by
    apply hhalf.congr'
    filter_upwards with n
    rw [scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
      hc hboundZ hmomentZ hRpos n]
  exact ⟨B, L, hBz, hBz.trans hBzw, hB, hL, hobs⟩

/-- **Recession-level presentation rigidity.**  Under the same admissibility hypotheses, the
transverse-defect envelope is determined by the pointed real moment sequence.  This is the
first-order invariant obtained by letting the common selected confocal amplitude recede to the
boundary at infinity. -/
theorem transverseDefectEnvelope_eq_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    (hzinj : Function.Injective z) (hwinj : Function.Injective w)
    (hcne : ∀ i, c i ≠ 0) (hdne : ∀ j, d j ≠ 0)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {i0 : I} (hi0 : (z i0).im ≠ 0)
    {j0 : J} (hj0 : (w j0).im ≠ 0) :
    HTGeometry.transverseDefectEnvelope (Set.range z) =
      HTGeometry.transverseDefectEnvelope (Set.range w) := by
  have hneZ : (Set.range z).Nonempty := ⟨z i0, ⟨i0, rfl⟩⟩
  have hneW : (Set.range w).Nonempty := ⟨w j0, ⟨j0, rfl⟩⟩
  have hlimZ := HTGeometry.tendsto_mul_confocalAmplitudeEnvelope_sq_sub_one
    hneZ hM (by rintro _ ⟨i, rfl⟩; exact hboundZ i)
  have hlimW := HTGeometry.tendsto_mul_confocalAmplitudeEnvelope_sq_sub_one
    hneW hN (by rintro _ ⟨j, rfl⟩; exact hboundW j)
  have heq :
      (fun R : ℝ => R *
        (HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ^ 2 - 1)) =ᶠ[atTop]
      (fun R : ℝ => R *
        (HTGeometry.confocalAmplitudeEnvelope (Set.range w) R ^ 2 - 1)) := by
    filter_upwards [eventually_gt_atTop (max M N)] with R hR
    have hRM : M < R := (le_max_left M N).trans_lt hR
    have hRN : N < R := (le_max_right M N).trans_lt hR
    rw [confocalAmplitudeEnvelope_eq_of_common_pointed_moments
      c z d w m hc hd htransZ htransW hzinj hwinj hcne hdne hM hN
      hboundZ hboundW hRM hRN hrealZ hrealW hmomentZ hmomentW hi0 hj0]
  have hsame := hlimZ.congr' heq
  have htwice :
      2 * HTGeometry.transverseDefectEnvelope (Set.range z) =
        2 * HTGeometry.transverseDefectEnvelope (Set.range w) :=
    tendsto_nhds_unique hsame hlimW
  linarith

/-- **Raw-source presentation rigidity after canonical aggregation.**  Repeated nodes, zero
fibres, and fibrewise cancellations are allowed in both raw sources.  After passage to their
nonzero aggregate supports, common pointed real moments determine both the selected confocal
amplitude at every common admissible scale and the transverse-defect recession invariant. -/
theorem aggregatePresentationRigidity_of_common_pointed_moments
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    {M N R : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hRM : M < R) (hRN : N < R)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m n : ℂ) = atomicPowerMoment d w n)
    {u0 : AtomicAggregateSupport c z}
    (hu0 : (atomicAggregateNode c z u0).im ≠ 0)
    {v0 : AtomicAggregateSupport d w}
    (hv0 : (atomicAggregateNode d w v0).im ≠ 0) :
    HTGeometry.confocalAmplitudeEnvelope
          (Set.range (atomicAggregateNode c z)) R =
        HTGeometry.confocalAmplitudeEnvelope
          (Set.range (atomicAggregateNode d w)) R ∧
      HTGeometry.transverseDefectEnvelope
          (Set.range (atomicAggregateNode c z)) =
        HTGeometry.transverseDefectEnvelope
          (Set.range (atomicAggregateNode d w)) := by
  let cz := atomicAggregateCoefficient c z
  let zz := atomicAggregateNode c z
  let dw := atomicAggregateCoefficient d w
  let ww := atomicAggregateNode d w
  have hcz : Summable cz := summable_atomicAggregateCoefficient hc
  have hdw : Summable dw := summable_atomicAggregateCoefficient hd
  have htz : Tendsto (fun u => HTGeometry.transverseDefect (zz u))
      cofinite (nhds 0) :=
    tendsto_atomicAggregateNode_transverseDefect_cofinite_zero htransZ
  have htw : Tendsto (fun v => HTGeometry.transverseDefect (ww v))
      cofinite (nhds 0) :=
    tendsto_atomicAggregateNode_transverseDefect_cofinite_zero htransW
  have hbz : ∀ u, ‖zz u‖ ≤ M := norm_atomicAggregateNode_le hboundZ
  have hbw : ∀ v, ‖ww v‖ ≤ N := norm_atomicAggregateNode_le hboundW
  have hrz : ∀ u, (zz u).im = 0 → 0 ≤ (zz u).re :=
    atomicAggregateNode_re_nonneg_of_im_eq_zero hrealZ
  have hrw : ∀ v, (ww v).im = 0 → 0 ≤ (ww v).re :=
    atomicAggregateNode_re_nonneg_of_im_eq_zero hrealW
  have hmz : ∀ n, (m n : ℂ) = atomicPowerMoment cz zz n := by
    intro n
    exact (hmomentZ n).trans
      (atomicPowerMoment_eq_atomicAggregatePowerMoment hc hboundZ n)
  have hmw : ∀ n, (m n : ℂ) = atomicPowerMoment dw ww n := by
    intro n
    exact (hmomentW n).trans
      (atomicPowerMoment_eq_atomicAggregatePowerMoment hd hboundW n)
  constructor
  · exact confocalAmplitudeEnvelope_eq_of_common_pointed_moments
      cz zz dw ww m hcz hdw htz htw
      (atomicAggregateNode_injective c z) (atomicAggregateNode_injective d w)
      (atomicAggregateCoefficient_ne_zero c z) (atomicAggregateCoefficient_ne_zero d w)
      hM hN hbz hbw hRM hRN hrz hrw hmz hmw hu0 hv0
  · exact transverseDefectEnvelope_eq_of_common_pointed_moments
      cz zz dw ww m hcz hdw htz htw
      (atomicAggregateNode_injective c z) (atomicAggregateNode_injective d w)
      (atomicAggregateCoefficient_ne_zero c z) (atomicAggregateCoefficient_ne_zero d w)
      hM hN hbz hbw hrz hrw hmz hmw hu0 hv0

end

end RHTower
