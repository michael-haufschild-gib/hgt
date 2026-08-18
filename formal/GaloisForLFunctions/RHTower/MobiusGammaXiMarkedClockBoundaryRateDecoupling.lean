import GaloisForLFunctions.RHTower.MobiusGammaXiMarkedClockSoninProducer
import GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport

/-!
# Marked-clock rate and G-CE boundary transport decouple at zero clock

The moving-boundary rate proposed for the marked higher-dimensional source is
identically zero at the zero-clock node of every canonical finite head: clock
damping is the identity there, so its pure commutator odd port vanishes.

This does not cancel the coupled-error singular debt.  On the same cofinal
finite self-adjoint transport schedule, the actual base response converges to
the complete critical coefficient, whose vanishing is equivalent to RH.
Consequently a pure clock commutator rate cannot supply the missing G-CE
boundary cancellation; a successful producer must carry a nonzero affine
zero-clock charge before scalarization.
-/

open Complex Filter Topology Matrix
open scoped ComplexOrder ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions

/-- The zero arithmetic clock is the identity on the complete Möbius source. -/
theorem mobiusCriticalComplexClockDamping_zero
    (sigma : ℝ) (hsigma : 1 < sigma) :
    mobiusCriticalComplexClockDamping sigma 0 hsigma (by norm_num) =
      ContinuousLinearMap.id ℂ MobiusClockSourceL2 := by
  ext x n
  simp [mobiusCriticalComplexClockDamping_apply,
    mobiusCriticalComplexClockFactor]

/-- A pure marked clock commutator has no zero-clock coordinate. -/
theorem mobiusClockSoninMarkedOddPort_zeroClock
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (hsigma : 1 < sigma) (x : MobiusClockSourceL2) :
    mobiusClockSoninMarkedOddPort
        (mobiusClockSoninMarkedProducer
          a c d r hc hcd hr N sigma 0 hsigma (by norm_num) x) = 0 := by
  rw [mobiusClockSoninMarkedOddPort_producer]
  simp [soninCofinalComplexClockCommutator,
    mobiusCriticalComplexClockDamping_zero]

/-- The squarefree overlap has unit zero-clock value at every safe source point. -/
theorem squarefreeBoundaryOverlap_zeroClock
    {sigma : ℝ} (hsigma : 1 < sigma) :
    squarefreeBoundaryOverlap (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) 0 = 1 := by
  have hpart : squarefreePartition (sigma : ℂ) ≠ 0 :=
    squarefreePartition_ne_zero (by simpa using hsigma)
  simp [squarefreeBoundaryOverlap, hpart]

/-- Requested moving-boundary quotient on the canonical actual source at zero clock. -/
def mobiusGammaXiMarkedZeroClockBoundaryRate (j N : ℕ) : ℝ :=
  let sigma := soninMobiusCriticalSigmaSequence j
  ‖mobiusClockSoninMarkedOddPort
      (mobiusClockSoninMarkedProducer
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num)
        N sigma 0 (soninMobiusCriticalSigmaSequence_gt_one j) (by norm_num)
        (infiniteMobiusSignedWeightLp sigma
          (soninMobiusCriticalSigmaSequence_gt_one j)))‖ /
    ((sigma - 1) *
      ‖squarefreeBoundaryOverlap (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) 0‖)

theorem mobiusGammaXiMarkedZeroClockBoundaryRate_eq_zero (j N : ℕ) :
    mobiusGammaXiMarkedZeroClockBoundaryRate j N = 0 := by
  rw [mobiusGammaXiMarkedZeroClockBoundaryRate]
  rw [mobiusClockSoninMarkedOddPort_zeroClock]
  simp

/-- Every moving depth schedule passes the proposed rate at zero clock. -/
theorem tendsto_mobiusGammaXiMarkedZeroClockBoundaryRate
    (jseq Nseq : ℕ → ℕ) :
    Tendsto (fun n =>
      mobiusGammaXiMarkedZeroClockBoundaryRate (jseq n) (Nseq n))
      atTop (nhds 0) := by
  simpa only [mobiusGammaXiMarkedZeroClockBoundaryRate_eq_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Base node contained in every canonical actual finite head. -/
def mobiusGammaXiCoupledErrorBaseIndex (N : ℕ) : Fin (N + 2) :=
  ⟨0, by omega⟩

theorem mobiusGammaXiCoupledErrorSingularResponse_base (N : ℕ) :
    mobiusGammaXiCoupledErrorSingularResponse N
        (mobiusGammaXiCoupledErrorBaseIndex N) =
      mobiusGammaXiCoupledErrorCriticalCoefficient := by
  simp [mobiusGammaXiCoupledErrorSingularResponse,
    mobiusGammaXiCoupledErrorBaseIndex,
    mobiusGammaXiCoupledErrorHeadNodes,
    mobiusCriticalUniversalFisherScore,
    mobiusCriticalUniversalHardyMassProfile]

/-- Closed decoupling theorem. The same actual cofinal schedule has complete
finite self-adjoint boundary transport and an identically vanishing marked
zero-clock rate, while its base response converges to the full singular debt
coefficient. Vanishing of that surviving coefficient remains exactly RH. -/
theorem exists_mobiusGammaXiMarkedZeroClockRate_boundaryTransport_debt :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      (∀ N,
        (mobiusGammaXiCoupledErrorSourceCompletion (depth N) N).PosSemidef ∧
        IsSelfAdjoint
          (mobiusGammaXiCoupledErrorSourceOperator (depth N) N)) ∧
      Tendsto (fun N =>
        ‖mobiusGammaXiCoupledErrorSourceOperator (depth N) N -
          mobiusGammaXiCoupledErrorSingularOperator N‖)
        atTop (nhds 0) ∧
      Tendsto (fun N =>
        mobiusGammaXiCoupledErrorBoundaryColumnError (depth N) N)
        atTop (nhds 0) ∧
      Tendsto (fun N =>
        mobiusGammaXiMarkedZeroClockBoundaryRate (depth N) N)
        atTop (nhds 0) ∧
      Tendsto (fun N =>
        mobiusGammaXiCoupledErrorSourceResponse (depth N) N
          (mobiusGammaXiCoupledErrorBaseIndex N))
        atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) ∧
      Tendsto (fun N =>
        mobiusGammaXiCoupledErrorSourceBudget (depth N) N)
        atTop
          (nhds (4 + mobiusGammaXiCoupledErrorSingularGraphDebt)) ∧
      (mobiusGammaXiCoupledErrorCriticalCoefficient = 0 ↔
        RiemannHypothesis) := by
  obtain ⟨depth, hdepth, hsource, _hsingular, hop, hcolumn,
      hpoint, hbudget⟩ :=
    exists_mobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport
  have hbaseDiff := hpoint mobiusGammaXiCoupledErrorBaseIndex
  have hbase : Tendsto (fun N =>
      mobiusGammaXiCoupledErrorSourceResponse (depth N) N
        (mobiusGammaXiCoupledErrorBaseIndex N))
      atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [mobiusGammaXiCoupledErrorSingularResponse_base] using hbaseDiff
  refine ⟨depth, hdepth, hsource, hop, hcolumn,
    tendsto_mobiusGammaXiMarkedZeroClockBoundaryRate depth id,
    hbase, hbudget, ?_⟩
  exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh

end RHTower
