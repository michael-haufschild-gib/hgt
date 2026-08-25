import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyDelayedPumpProbe

/-!
For the Birmingham--Mokhtari/AIME return channel, passive stationary absorbed
mass rescales rather than cancels the theta-reflected chiral defect. Finite local
source packets and finite-energy continuum returns decay, so every tilted fibre
has eventual oriented mixing. Any asymptotic cancellation therefore requires an
explicit nondecaying threshold contribution.
-/
open Complex Real Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

structure D4BMFiniteLocalContinuumReturnData where
  mode : ℕ
  degree : ℕ
  coefficient : Fin mode → Fin degree → ℂ
  headPartner : Fin mode → Bool
  r : Fin mode → ℕ
  s : Fin mode → ℕ
  continuum : D4BMFiniteEnergyContinuumState

def D4BMFiniteLocalContinuumReturnData.response
    (data : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  d4BMFiniteLocalContinuumDelayedSourceRemainder
    data.coefficient data.headPartner data.r data.s data.continuum q delay

theorem D4BMFiniteLocalContinuumReturnData.response_tendsto_zero
    (data : D4BMFiniteLocalContinuumReturnData) (q : XiZeroCopy) :
    Tendsto (data.response q) atTop (nhds 0) := by
  exact d4BMFiniteLocalContinuumDelayedSourceRemainder_tendsto_zero
    data.coefficient data.headPartner data.r data.s data.continuum q

def d4BMXiThetaMirrorTransientChiralDefect
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  forward.response q delay -
    reflected.response (xiZeroCopyReflectEquiv q) delay

theorem d4BMXiThetaMirrorTransientChiralDefect_tendsto_zero
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) :
    Tendsto (d4BMXiThetaMirrorTransientChiralDefect forward reflected q)
      atTop (nhds 0) := by
  change Tendsto
    (fun delay => forward.response q delay -
      reflected.response (xiZeroCopyReflectEquiv q) delay) atTop (nhds 0)
  simpa only [sub_zero] using
    (forward.response_tendsto_zero q).sub
      (reflected.response_tendsto_zero (xiZeroCopyReflectEquiv q))

def d4BMXiThetaMirrorPassiveStationaryProjectedKernel
    (absorbedMass : NNReal) (q : XiZeroCopy) : ℂ :=
  let z := d4BMXiReflectedRealPairMediatorSpectralPoint q
  (d4FundamentalQNMCrossBranchAIMENumerator 1 z +
      d4BMPassiveStationaryMassNumerator absorbedMass z) /
    (4 * (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ))

theorem d4BMXiThetaMirrorPassiveStationaryProjectedKernel_eq
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    d4BMXiThetaMirrorPassiveStationaryProjectedKernel absorbedMass q =
      (((1 : ℝ) + (absorbedMass : ℝ) : ℝ) : ℂ) *
        (d4BMXiThetaMirrorAIMEChiralKernel q : ℂ) := by
  have hQ := d4BMXiReflectedRealPairMediatorAngularQ_ne_zero q
  have hQ2 := d4BMXiReflectedRealPairMediatorAngularQ_add_two_ne_zero q
  unfold d4BMXiThetaMirrorPassiveStationaryProjectedKernel
    d4BMPassiveStationaryMassNumerator
    d4FundamentalQNMCrossBranchAIMENumerator
    d4BMXiThetaMirrorAIMEChiralKernel
  simp only [Complex.normSq_one, Complex.ofReal_one, one_mul]
  rw [d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq]
  unfold d4ThetaTeukolskyAngularQ
  rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularEigenvalue]
  norm_num
  field_simp [hQ, hQ2]
  ring_nf

def d4BMXiThetaMirrorPassiveStationaryAIMEDefect
    (absorbedMass : NNReal) (q : XiZeroCopy) : ℂ :=
  d4BMXiThetaMirrorPassiveStationaryProjectedKernel absorbedMass q -
    d4BMXiThetaMirrorPassiveStationaryProjectedKernel absorbedMass
      (xiZeroCopyReflectEquiv q)

theorem d4BMXiThetaMirrorPassiveStationaryAIMEDefect_eq
    (absorbedMass : NNReal) (q : XiZeroCopy) :
    d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q =
      (((1 : ℝ) + (absorbedMass : ℝ) : ℝ) : ℂ) *
        (d4BMXiThetaMirrorAIMEChiralKernelDefect q : ℂ) := by
  unfold d4BMXiThetaMirrorPassiveStationaryAIMEDefect
    d4BMXiThetaMirrorAIMEChiralKernelDefect
  rw [d4BMXiThetaMirrorPassiveStationaryProjectedKernel_eq,
    d4BMXiThetaMirrorPassiveStationaryProjectedKernel_eq]
  push_cast
  ring_nf

theorem d4BMXiThetaMirrorPassiveStationaryAIMEDefect_ne_zero_of_tilted
    (absorbedMass : NNReal) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q ≠ 0 := by
  rw [d4BMXiThetaMirrorPassiveStationaryAIMEDefect_eq]
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (by positivity :
      (0 : ℝ) < 1 + (absorbedMass : ℝ)))
  · exact_mod_cast
      (d4BMXiThetaMirrorAIMEChiralKernelDefect_ne_zero_iff q).2 htilt

def d4BMXiThetaMirrorPassiveFullChiralDefect
    (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (delay : ℝ) : ℂ :=
  d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q +
    d4BMXiThetaMirrorTransientChiralDefect forward reflected q delay

theorem d4BMXiThetaMirrorPassiveFullChiralDefect_tendsto_stationary
    (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) :
    Tendsto
      (d4BMXiThetaMirrorPassiveFullChiralDefect absorbedMass forward reflected q)
      atTop
      (nhds (d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q)) := by
  change Tendsto
    (fun delay => d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q +
      d4BMXiThetaMirrorTransientChiralDefect forward reflected q delay)
    atTop (nhds (d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q))
  simpa only [add_zero] using
    tendsto_const_nhds.add
      (d4BMXiThetaMirrorTransientChiralDefect_tendsto_zero forward reflected q)

theorem eventually_d4BMXiThetaMirrorPassiveFullChiralDefect_ne_zero_of_tilted
    (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ∀ᶠ delay in atTop,
      d4BMXiThetaMirrorPassiveFullChiralDefect
        absorbedMass forward reflected q delay ≠ 0 := by
  exact (d4BMXiThetaMirrorPassiveFullChiralDefect_tendsto_stationary
    absorbedMass forward reflected q).eventually
      (eventually_ne_nhds
        (d4BMXiThetaMirrorPassiveStationaryAIMEDefect_ne_zero_of_tilted
          absorbedMass q htilt))

theorem d4BMXiThetaMirrorPassiveFullChiralDefect_tendsto_zero_iff
    (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) :
    Tendsto
        (d4BMXiThetaMirrorPassiveFullChiralDefect
          absorbedMass forward reflected q)
        atTop (nhds 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have hstationary :=
      d4BMXiThetaMirrorPassiveFullChiralDefect_tendsto_stationary
        absorbedMass forward reflected q
    have hs : d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q = 0 :=
      tendsto_nhds_unique hstationary hzero
    by_contra htilt
    exact (d4BMXiThetaMirrorPassiveStationaryAIMEDefect_ne_zero_of_tilted
      absorbedMass q htilt) hs
  · intro hline
    have hs : d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q = 0 := by
      rw [d4BMXiThetaMirrorPassiveStationaryAIMEDefect_eq]
      rw [d4BMXiThetaMirrorAIMEChiralKernelDefect_eq, hline]
      norm_num
    rw [← hs]
    exact d4BMXiThetaMirrorPassiveFullChiralDefect_tendsto_stationary
      absorbedMass forward reflected q

def d4BMXiThetaMirrorPassiveStationaryOrientedFlow
    (absorbedMass : NNReal) (q : XiZeroCopy) : ℝ :=
  (1 + (absorbedMass : ℝ)) * ((q.1 : ℂ).re - 1 / 2) *
    d4BMXiThetaMirrorAIMEChiralKernelDefect q

theorem d4BMXiThetaMirrorPassiveStationaryOrientedFlow_pos_of_tilted
    (absorbedMass : NNReal) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiThetaMirrorPassiveStationaryOrientedFlow absorbedMass q := by
  unfold d4BMXiThetaMirrorPassiveStationaryOrientedFlow
  rw [mul_assoc]
  exact mul_pos (by positivity)
    ((d4BMXiThetaMirrorAIMEOrientedFlow_pos_iff q).2 htilt)

def d4BMXiThetaMirrorPassiveFullOrientedFlow
    (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (delay : ℝ) : ℝ :=
  ((q.1 : ℂ).re - 1 / 2) *
    (d4BMXiThetaMirrorPassiveFullChiralDefect
      absorbedMass forward reflected q delay).re

theorem d4BMXiThetaMirrorPassiveFullOrientedFlow_tendsto_stationary
    (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) :
    Tendsto
      (d4BMXiThetaMirrorPassiveFullOrientedFlow absorbedMass forward reflected q)
      atTop
      (nhds (d4BMXiThetaMirrorPassiveStationaryOrientedFlow absorbedMass q)) := by
  have hfull := d4BMXiThetaMirrorPassiveFullChiralDefect_tendsto_stationary
    absorbedMass forward reflected q
  have hre := (Complex.continuous_re.tendsto
    (d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q)).comp hfull
  have hmul : Tendsto
      (fun delay : ℝ => ((q.1 : ℂ).re - 1 / 2) *
        (d4BMXiThetaMirrorPassiveFullChiralDefect
          absorbedMass forward reflected q delay).re)
      atTop
      (nhds (((q.1 : ℂ).re - 1 / 2) *
        (d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q).re)) :=
    tendsto_const_nhds.mul hre
  unfold d4BMXiThetaMirrorPassiveFullOrientedFlow
    d4BMXiThetaMirrorPassiveStationaryOrientedFlow
  convert hmul using 1
  rw [d4BMXiThetaMirrorPassiveStationaryAIMEDefect_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring_nf

theorem eventually_d4BMXiThetaMirrorPassiveFullOrientedFlow_pos_of_tilted
    (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ∀ᶠ delay in atTop,
      0 < d4BMXiThetaMirrorPassiveFullOrientedFlow
        absorbedMass forward reflected q delay := by
  exact (d4BMXiThetaMirrorPassiveFullOrientedFlow_tendsto_stationary
    absorbedMass forward reflected q).eventually
      (eventually_gt_nhds
        (d4BMXiThetaMirrorPassiveStationaryOrientedFlow_pos_of_tilted
          absorbedMass q htilt))

def d4BMXiThetaMirrorCriticalMassPassiveFullMixing
    (n : ℕ) (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (delay : ℝ) : ℂ × ℂ :=
  ((d4BMXiThetaMirrorTopologicalStarobinskyDefect n
      (d4BMXiThetaMirrorCriticalMass q) q : ℂ),
    d4BMXiThetaMirrorPassiveFullChiralDefect
      absorbedMass forward reflected q delay)

theorem eventually_d4BMXiThetaMirrorCriticalMassPassiveFullMixing_ne_zero_of_tilted
    (n : ℕ) (absorbedMass : NNReal)
    (forward reflected : D4BMFiniteLocalContinuumReturnData)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ∀ᶠ delay in atTop,
      d4BMXiThetaMirrorCriticalMassPassiveFullMixing
        n absorbedMass forward reflected q delay ≠ (0, 0) := by
  filter_upwards
    [eventually_d4BMXiThetaMirrorPassiveFullChiralDefect_ne_zero_of_tilted
      absorbedMass forward reflected q htilt] with delay hne
  intro hzero
  exact hne (congrArg Prod.snd hzero)

def d4BMXiThetaMirrorThresholdCancellationValue
    (absorbedMass : NNReal) (q : XiZeroCopy) : ℂ :=
  -d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q

theorem d4BMXiThetaMirrorAsymptoticCancellation_forces_threshold
    (absorbedMass : NNReal) (q : XiZeroCopy) (threshold : ℝ → ℂ)
    (hcancel : Tendsto
      (fun delay =>
        d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q +
          threshold delay)
      atTop (nhds 0)) :
    Tendsto threshold atTop
      (nhds (d4BMXiThetaMirrorThresholdCancellationValue absorbedMass q)) := by
  have h := hcancel.sub_const
    (d4BMXiThetaMirrorPassiveStationaryAIMEDefect absorbedMass q)
  unfold d4BMXiThetaMirrorThresholdCancellationValue
  convert h using 1
  · funext delay
    ring_nf
  · ring_nf

theorem d4BMXiThetaMirrorThresholdCancellationValue_ne_zero_of_tilted
    (absorbedMass : NNReal) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorThresholdCancellationValue absorbedMass q ≠ 0 := by
  unfold d4BMXiThetaMirrorThresholdCancellationValue
  exact neg_ne_zero.mpr
    (d4BMXiThetaMirrorPassiveStationaryAIMEDefect_ne_zero_of_tilted
      absorbedMass q htilt)

end

end RHTower
