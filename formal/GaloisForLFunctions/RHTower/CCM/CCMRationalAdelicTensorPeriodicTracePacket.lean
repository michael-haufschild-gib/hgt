import GaloisForLFunctions.RHTower.CCM.CCMRationalPeriodicResidueSchwartzPeriodRefinement
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPureTensorHaarDualCancellation
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicMoritaMonomial

/-!
# Exact periodic packets for the full adelic tensor core

Pure-tensor Poisson packets do not suffice for the CCM source: the two endpoint
functionals may cancel only after several tensors are added.  This file builds
one residue-Schwartz packet for every element of the algebraic adelic tensor
core.  Tensor addition refines both periods to their product before adding the
residue families.  The resulting packet satisfies two exact conservation laws:

* its physical zero mode is the literal zero-evaluation endpoint;
* the sum of its Fourier zero modes is its period times the literal Haar endpoint.

Consequently global endpoint cancellation, not summandwise cancellation,
implies strong all-derivative/all-weight decay of the genuine rational-unit
trace.
-/

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped RestrictedProduct algebraMap Classical BigOperators FourierTransform

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor

/-- Exact common-period trace packet for an arbitrary algebraic adelic Bruhat
tensor at one profinite class-space coordinate. -/
structure CCMRationalAdelicTensorPeriodicTracePacket
    (x : Core) (b : CCMRationalProfiniteUnit) where
  period : ℕ
  period_neZero : NeZero period
  residueSchwartz : Fin period → CCMRationalArchimedeanSchwartz
  rationalLogTrace_eq :
    (fun t : ℝ => ∑' q : ℚ,
      ccmRationalAdelicBruhatTensorOrbit x (Real.exp t) b.1 q) =
      @ccmRationalPeriodicResidueSchwartzLogTrace
        period period_neZero residueSchwartz
  physicalZeroMode_eq :
    residueSchwartz 0 0 = ccmRationalAdelicBruhatZeroEval x
  dualZeroMode_eq :
    ∑ r, (𝓕 (residueSchwartz r)) 0 =
      period • ccmRationalAdelicBruhatIntegral x

/-- The zero tensor has the zero period-one packet. -/
def ccmRationalAdelicTensorPeriodicTracePacketZero
    (b : CCMRationalProfiniteUnit) :
    CCMRationalAdelicTensorPeriodicTracePacket 0 b where
  period := 1
  period_neZero := inferInstance
  residueSchwartz := 0
  rationalLogTrace_eq := by
    funext t
    simp [ccmRationalPeriodicResidueSchwartzLogTrace,
      ccmRationalPeriodicWeightedLogTrace,
      ccmRationalPeriodicWeightedTrace]
  physicalZeroMode_eq := by simp
  dualZeroMode_eq := by simp

/-- A cyclic Haar packet gives the residue-Schwartz packet of a pure tensor. -/
def ccmRationalAdelicPureTensorTensorPeriodicTracePacket
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit)
    (Q : CCMRationalFiniteBruhatCyclicHaarPacket phi b) :
    CCMRationalAdelicTensorPeriodicTracePacket (f ⊗ₜ[ℂ] phi) b := by
  letI : NeZero Q.period := Q.period_neZero
  let fD := ccmRationalPositiveDenominatorDilation
    f Q.denominator Q.denominator_pos
  let P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b.1 :=
    { denominator := Q.denominator
      denominator_pos := Q.denominator_pos
      period := Q.period
      period_neZero := Q.period_neZero
      weight := Q.weight
      finiteCoefficient := Q.finiteCoefficient
      trace_eq := fun bInf => by
        rw [ccmRationalAdelicBruhatPureTensorOrbitSum_eq_integerSum
          f phi bInf b.1 Q.denominator Q.denominator_pos
          Q.rationalDenominator]
        rw [ccmRationalPeriodicWeightedTrace]
        apply tsum_congr
        intro n
        rw [← Q.finiteCoefficient n]
        rw [ccmRationalPositiveDenominatorDilation_apply]
        rw [mul_comm]
        congr 1
        ring_nf }
  refine
    { period := Q.period
      period_neZero := Q.period_neZero
      residueSchwartz := fun r => Q.weight r • fD
      rationalLogTrace_eq := ?_
      physicalZeroMode_eq := ?_
      dualZeroMode_eq := ?_ }
  · funext t
    calc
      (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
          (f ⊗ₜ[ℂ] phi) (Real.exp t) b.1 q) =
          ccmRationalPeriodicWeightedLogTrace
            Q.period Q.weight fD t := by
        change (∑' q : ℚ, ccmRationalAdelicBruhatPureTensorOrbit
          f phi (Real.exp t) b.1 q) = _
        exact P.trace_eq (Real.exp t)
      _ = ccmRationalPeriodicResidueSchwartzLogTrace Q.period
          (fun r => Q.weight r • fD) t := by
        rw [ccmRationalPeriodicResidueSchwartzLogTrace_rankOne]
  · have hw0 := Q.finiteCoefficient 0
    have hw0' : phi.1 0 = Q.weight
        (@ccmRationalPeriodicResidue Q.period Q.period_neZero 0) := by
      simpa using hw0
    have hw0'' : phi.1 0 = Q.weight 0 := by
      simpa only [ccmRationalPeriodicResidue_zero] using hw0'
    change Q.weight 0 * fD 0 = _
    rw [← hw0'']
    simp [fD, ccmRationalPositiveDenominatorDilation_apply,
      ccmRationalAdelicBruhatZeroEval_tmul, mul_comm]
  · change ∑ r : Fin Q.period,
      ((FourierTransform.fourierCLE ℂ
        CCMRationalArchimedeanSchwartz) (Q.weight r • fD)) 0 = _
    simp_rw [map_smul]
    change (∑ r : Fin Q.period, Q.weight r * (𝓕 fD) 0) = _
    rw [← Finset.sum_mul]
    exact ccmRationalAdelicPureTensor_dualZeroMode_eq_period_nsmul_epsilonOne
      f phi b Q

/-- Product-period sum of two exact tensor packets. -/
def CCMRationalAdelicTensorPeriodicTracePacket.add
    {x y : Core} {b : CCMRationalProfiniteUnit}
    (P : CCMRationalAdelicTensorPeriodicTracePacket x b)
    (Q : CCMRationalAdelicTensorPeriodicTracePacket y b) :
    CCMRationalAdelicTensorPeriodicTracePacket (x + y) b := by
  letI : NeZero P.period := P.period_neZero
  letI : NeZero Q.period := Q.period_neZero
  let gP : Fin (P.period * Q.period) →
      CCMRationalArchimedeanSchwartz :=
    ccmRationalPeriodicResidueSchwartzRefinement
      P.period Q.period P.residueSchwartz
  let gQ : Fin (P.period * Q.period) →
      CCMRationalArchimedeanSchwartz :=
    ccmRationalPeriodicResidueSchwartzLeftRefinement
      Q.period P.period Q.residueSchwartz
  refine
    { period := P.period * Q.period
      period_neZero := inferInstance
      residueSchwartz := gP + gQ
      rationalLogTrace_eq := ?_
      physicalZeroMode_eq := ?_
      dualZeroMode_eq := ?_ }
  · funext t
    have hx := summable_norm_iff.mp
      (ccmRationalAdelicBruhatTensorOrbit_summable x
        (Real.exp_ne_zero t) b.1)
    have hy := summable_norm_iff.mp
      (ccmRationalAdelicBruhatTensorOrbit_summable y
        (Real.exp_ne_zero t) b.1)
    calc
      (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
          (x + y) (Real.exp t) b.1 q) =
          (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
            x (Real.exp t) b.1 q) +
          ∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
            y (Real.exp t) b.1 q := by
        rw [← hx.tsum_add hy]
        apply tsum_congr
        intro q
        rw [ccmRationalAdelicBruhatTensorOrbit_add]
      _ = ccmRationalPeriodicResidueSchwartzLogTrace
            P.period P.residueSchwartz t +
          ccmRationalPeriodicResidueSchwartzLogTrace
            Q.period Q.residueSchwartz t := by
        rw [← P.rationalLogTrace_eq, ← Q.rationalLogTrace_eq]
      _ = ccmRationalPeriodicResidueSchwartzLogTrace
            (P.period * Q.period) gP t +
          ccmRationalPeriodicResidueSchwartzLogTrace
            (P.period * Q.period) gQ t := by
        rw [ccmRationalPeriodicResidueSchwartzLogTrace_refinement,
          ccmRationalPeriodicResidueSchwartzLogTrace_leftRefinement]
      _ = ccmRationalPeriodicResidueSchwartzLogTrace
          (P.period * Q.period) (gP + gQ) t := by
        exact congrFun
          (ccmRationalPeriodicResidueSchwartzLogTrace_add
            (P.period * Q.period) gP gQ).symm t
  · change (gP 0 + gQ 0) 0 = _
    simp only [add_apply]
    change P.residueSchwartz 0 0 + Q.residueSchwartz 0 0 = _
    rw [P.physicalZeroMode_eq, Q.physicalZeroMode_eq, map_add]
  · change ∑ r : Fin (P.period * Q.period),
      ((FourierTransform.fourierCLE ℂ
        CCMRationalArchimedeanSchwartz) (gP r + gQ r)) 0 = _
    simp_rw [map_add]
    change ∑ r : Fin (P.period * Q.period),
      ((𝓕 (gP r)) 0 + (𝓕 (gQ r)) 0) = _
    rw [Finset.sum_add_distrib]
    change
      (∑ r : Fin (P.period * Q.period),
        (𝓕 (ccmRationalPeriodicResidueSchwartzRefinement
          P.period Q.period P.residueSchwartz r)) 0) +
      (∑ r : Fin (P.period * Q.period),
        (𝓕 (ccmRationalPeriodicResidueSchwartzLeftRefinement
          Q.period P.period Q.residueSchwartz r)) 0) = _
    have hP := sum_ccmRationalPeriodicResidueSchwartzRefinement
      P.period Q.period P.residueSchwartz
        (fun f : CCMRationalArchimedeanSchwartz => (𝓕 f) 0)
    have hQ := sum_ccmRationalPeriodicResidueSchwartzLeftRefinement
      Q.period P.period Q.residueSchwartz
        (fun f : CCMRationalArchimedeanSchwartz => (𝓕 f) 0)
    rw [hP, hQ, P.dualZeroMode_eq, Q.dualZeroMode_eq]
    simp only [nsmul_eq_mul]
    push_cast
    ring

/-- Every algebraic adelic Bruhat tensor admits an exact packet preserving
both endpoint cancellations globally. -/
theorem ccmRationalAdelicTensor_exists_periodicTracePacket
    (x : Core) (b : CCMRationalProfiniteUnit) :
    Nonempty (CCMRationalAdelicTensorPeriodicTracePacket x b) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨ccmRationalAdelicTensorPeriodicTracePacketZero b⟩
  | tmul f phi =>
      obtain ⟨Q⟩ := ccmRationalFiniteBruhat_exists_cyclicHaarPacket phi b
      exact ⟨ccmRationalAdelicPureTensorTensorPeriodicTracePacket f phi b Q⟩
  | add x y hx hy =>
      obtain ⟨P⟩ := hx
      obtain ⟨Q⟩ := hy
      exact ⟨P.add Q⟩

/-- At rational coordinate zero, the full tensor orbit is exactly the first
CCM endpoint, independently of the nonzero adelic base. -/
theorem ccmRationalAdelicBruhatTensorOrbit_at_zero
    (x : Core) (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) :
    ccmRationalAdelicBruhatTensorOrbit x bInf b 0 =
      ccmRationalAdelicBruhatZeroEval x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f phi =>
      simp [ccmRationalAdelicBruhatTensorOrbit_tmul,
        ccmRationalAdelicBruhatPureTensorOrbit,
        ccmRationalAdelicBruhatZeroEval_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Endpoint-zero reindexing from the full rational diagonal to genuine
rational units for an arbitrary algebraic tensor. -/
theorem ccmRationalAdelicBruhatTensorOrbitSum_eq_unitOrbitSum
    (x : Core) (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ)
    (hzero : ccmRationalAdelicBruhatZeroEval x = 0) :
    (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit x bInf b q) =
      ∑' q : CCMRationalUnit,
        ccmRationalAdelicBruhatTensorOrbit x bInf b (q : ℚ) := by
  let g : CCMRationalUnit → ℚ := fun q => q
  let F : ℚ → ℂ := fun q =>
    ccmRationalAdelicBruhatTensorOrbit x bInf b q
  have hg : Function.Injective g := Units.val_injective
  have hs : Function.support F ⊆ Set.range g := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro h
      subst q
      apply hq
      simpa [F, ccmRationalAdelicBruhatTensorOrbit_at_zero] using hzero
    exact ⟨Units.mk0 q hq0, rfl⟩
  exact ccmRational_tsum_reindex_of_support_subset_range g hg F hs

/-- **Full algebraic-tensor endpoint landing.** Both literal CCM endpoints
imply strong all-derivative/all-weight decay of the genuine `ℚˣ` orbit trace,
even when cancellation occurs only between tensor summands. -/
theorem ccmRationalAdelicTensor_unitLogTrace_strongLogDecay_of_endpoints
    (x : Core) (b : CCMRationalProfiniteUnit)
    (hzero : ccmRationalAdelicBruhatZeroEval x = 0)
    (hone : ccmRationalAdelicBruhatIntegral x = 0) :
    RHTower.DeningerMeyerStrongLogDecay
      (fun t : ℝ => ∑' q : CCMRationalUnit,
        ccmRationalAdelicBruhatTensorOrbit
          x (Real.exp t) b.1 (q : ℚ)) := by
  obtain ⟨P⟩ := ccmRationalAdelicTensor_exists_periodicTracePacket x b
  letI : NeZero P.period := P.period_neZero
  have hphysical : P.residueSchwartz 0 0 = 0 := by
    rw [P.physicalZeroMode_eq, hzero]
  have hdual : ∑ r, (𝓕 (P.residueSchwartz r)) 0 = 0 := by
    rw [P.dualZeroMode_eq, hone, nsmul_zero]
  have hstrong :=
    ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay
      P.period P.residueSchwartz hphysical hdual
  rw [← P.rationalLogTrace_eq] at hstrong
  have htrace :
      (fun t : ℝ => ∑' q : CCMRationalUnit,
        ccmRationalAdelicBruhatTensorOrbit
          x (Real.exp t) b.1 (q : ℚ)) =
      fun t : ℝ => ∑' q : ℚ,
        ccmRationalAdelicBruhatTensorOrbit
          x (Real.exp t) b.1 q := by
    funext t
    exact (ccmRationalAdelicBruhatTensorOrbitSum_eq_unitOrbitSum
      x (Real.exp t) b.1 hzero).symm
  rwa [htrace]

end RHTower
end GaloisForLFunctions
