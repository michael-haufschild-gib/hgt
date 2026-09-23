import GaloisForLFunctions.RHTower.XiBernsteinPuritySquareRootDecomposition
import GaloisForLFunctions.HTGeometry.HalfOrderMeromorphicObstruction

/-!
# Sharp Abel selection master theorem

The unique susceptibility radius has a complete phase alternative.  In the RH phase it is the
unit endpoint.  In the false phase it is the reciprocal square of a source-attained maximal Xi
packet and carries an exact positive half-order boundary, hence positive radial blow-up.
-/

open Complex Filter Topology
open scoped BigOperators Real Polynomial
open Polynomial

namespace RHTower

noncomputable section

/-- The source-attained sharp false phase at an Abel radius `R`. -/
def PrimeArchEndpointBernsteinAbelSharpFalsePhase (R : ℝ) : Prop :=
  ∃ D : Finset XiZeroCopy, ∃ B beta L : ℝ,
    R = 1 / B ^ (2 : ℕ) ∧
    1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
    (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
    (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
    L = ∑ u ∈ xiEndpointCoordinateSet D,
      ‖xiEndpointCoordinateWeight D u‖ ^ (2 : ℕ) *
        bernsteinAffineRowHalfOrderConstant u ∧
    0 < L ∧ 0 < Real.sqrt Real.pi * L ∧
    Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
        primeArchEndpointBernsteinAbelSusceptibility t)
      (nhdsWithin R (Set.Ico 0 R))
      (nhds (Real.sqrt Real.pi * L)) ∧
    (∀ t : ℝ, 0 < t → t < R →
      HasSum
        (fun n : ℕ => xiEndpointCoordinateDiagonalPurity D n * t ^ n)
        (finiteBernsteinCoordinateDiagonalSquareRootKernel
          (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t)) ∧
    (∀ t : ℝ, 0 < t → t < R →
      primeArchEndpointBernsteinAbelSusceptibility t =
        finiteBernsteinCoordinateDiagonalSquareRootKernel
          (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t +
        primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t) ∧
    Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
        primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t)
      (nhdsWithin R (Set.Ico 0 R)) (nhds 0) ∧
    Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
        xiEndpointCoordinateDiagonalAbelSusceptibility D t)
      (nhdsWithin R (Set.Ico 0 R))
      (nhds (Real.sqrt Real.pi * L)) ∧
    Tendsto primeArchEndpointBernsteinAbelSusceptibility
      (nhdsWithin R (Set.Ico 0 R)) atTop ∧
    (∀ f : ℂ → ℂ, MeromorphicAt f R →
      ¬ (fun t : ℝ => f t) =ᶠ[nhdsWithin R (Set.Ico 0 R)]
        (fun t : ℝ => (primeArchEndpointBernsteinAbelSusceptibility t : ℂ)))

/-- **Sharp finite-to-cofinal Abel selection theorem.**  The completed Xi source has its proven
finite positive chamber, a unique exact susceptibility radius, and an exhaustive phase law at
that radius.  Failure of RH is not recorded merely by `R < 1`: the selected source-attained
maximal packet forces an exact positive square-root boundary and radial blow-up. -/
theorem primeArchEndpointBernsteinAbelSharpSelectionMaster :
    (∀ n i : ℕ, n ≤ 13 →
      0 ≤ bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n i) ∧
    (∀ N : ℕ, N ≤ 12 →
      hausdorffBernsteinNegativeMass
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) N = 0) ∧
    (∀ t : ℝ, 0 ≤ t → t < 250000 / 251001 →
      PrimeArchEndpointBernsteinAbelSusceptibilityFinite t) ∧
    (∃! R : ℝ,
      250000 / 251001 < R ∧ R ≤ 1 ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius R ∧
      ((RiemannHypothesis ∧ R = 1) ∨
        (¬ RiemannHypothesis ∧ R < 1 ∧
          PrimeArchEndpointBernsteinAbelSharpFalsePhase R))) ∧
    (RiemannHypothesis ↔
      ∀ t : ℝ, 0 ≤ t → t < 1 →
        PrimeArchEndpointBernsteinAbelSusceptibilityFinite t) := by
  refine ⟨
    fun n i hn =>
      primeArchEndpointBernsteinCoefficient_nonnegative_of_degree_le_thirteen n i hn,
    fun N hN =>
      primeArchEndpointHausdorffBernsteinNegativeMass_eq_zero_of_degree_le_twelve N hN,
    fun t ht0 ht1 =>
      primeArchEndpointBernsteinAbelSusceptibilityFinite_below_narrowSectorRadius ht0 ht1,
    ?_,
    riemannHypothesis_iff_primeArchEndpointBernsteinAbelSusceptibilityFinite⟩
  obtain ⟨R, hR, hRunique⟩ :=
    existsUnique_primeArchEndpointBernsteinAbelCriticalRadius
  refine ⟨R, ⟨hR.1, hR.2.1, hR.2.2.1, ?_⟩, ?_⟩
  · by_cases hRH : RiemannHypothesis
    · exact Or.inl ⟨hRH, hR.2.2.2.mp hRH⟩
    · obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
          hL, hLpos, hcritical, hdiagExact, hpointDecomp, hremBoundary,
          hdiagBoundary, hboundary⟩ :=
        exists_exact_maximalDiagonalSquareRootDecomposition_of_not_rh hRH
      have hboundaryPos : 0 < Real.sqrt Real.pi * L :=
        mul_pos (Real.sqrt_pos.2 Real.pi_pos) hLpos
      have hblowup :=
        GaloisForLFunctions.HTGeometry.tendsto_atTop_of_positive_sqrt_scaled_boundary
          (lt_trans zero_lt_one hB) hboundaryPos hboundary
      have hReq : R = 1 / B ^ (2 : ℕ) :=
        primeArchEndpointBernsteinAbelCriticalRadius_unique hR.2.2.1 hcritical
      have hRne : R ≠ 1 := fun hEq => hRH (hR.2.2.2.mpr hEq)
      have hRlt : R < 1 := lt_of_le_of_ne hR.2.1 hRne
      have hboundaryR : Tendsto
          (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
            primeArchEndpointBernsteinAbelSusceptibility t)
          (nhdsWithin R (Set.Ico 0 R))
          (nhds (Real.sqrt Real.pi * L)) := by
        rw [hReq]
        exact hboundary
      have hblowupR : Tendsto primeArchEndpointBernsteinAbelSusceptibility
          (nhdsWithin R (Set.Ico 0 R)) atTop := by
        rw [hReq]
        exact hblowup
      have hdiagExactR : ∀ t : ℝ, 0 < t → t < R →
          HasSum
            (fun n : ℕ => xiEndpointCoordinateDiagonalPurity D n * t ^ n)
            (finiteBernsteinCoordinateDiagonalSquareRootKernel
              (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t) := by
        simpa only [hReq] using hdiagExact
      have hpointDecompR : ∀ t : ℝ, 0 < t → t < R →
          primeArchEndpointBernsteinAbelSusceptibility t =
            finiteBernsteinCoordinateDiagonalSquareRootKernel
              (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t +
            primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t := by
        simpa only [hReq] using hpointDecomp
      have hremBoundaryR : Tendsto
          (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
            primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t)
          (nhdsWithin R (Set.Ico 0 R)) (nhds 0) := by
        rw [hReq]
        exact hremBoundary
      have hdiagBoundaryR : Tendsto
          (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
            xiEndpointCoordinateDiagonalAbelSusceptibility D t)
          (nhdsWithin R (Set.Ico 0 R))
          (nhds (Real.sqrt Real.pi * L)) := by
        rw [hReq]
        exact hdiagBoundary
      have hnomero : ∀ f : ℂ → ℂ, MeromorphicAt f R →
          ¬ (fun t : ℝ => f t) =ᶠ[nhdsWithin R (Set.Ico 0 R)]
            (fun t : ℝ =>
              (primeArchEndpointBernsteinAbelSusceptibility t : ℂ)) := by
        intro f hf hagree
        have hf' : MeromorphicAt f (1 / B ^ (2 : ℕ) : ℝ) := by
          simpa only [hReq] using hf
        have hagree' : (fun t : ℝ => f t) =ᶠ[
            nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ)))]
            (fun t : ℝ =>
              (primeArchEndpointBernsteinAbelSusceptibility t : ℂ)) := by
          simpa only [hReq] using hagree
        exact
          GaloisForLFunctions.HTGeometry.false_of_meromorphicAt_of_positive_sqrt_scaled_boundary
            (lt_trans zero_lt_one hB) hboundaryPos hf' hagree' hboundary
      exact Or.inr ⟨hRH, hRlt, D, B, beta, L, hReq, hB, hbeta1, hbeta,
        hDne, hD, hDsub, hL, hLpos, hboundaryPos, hboundaryR, hdiagExactR,
        hpointDecompR, hremBoundaryR, hdiagBoundaryR, hblowupR, hnomero⟩
  · intro S hS
    exact primeArchEndpointBernsteinAbelCriticalRadius_unique hS.2.2.1 hR.2.2.1

/-- Failure of RH uniquely determines the critical radius carrying the complete
source-attained Bernstein--Abel false-phase certificate. Thus the false-phase
interface is produced by the source selection theorem rather than assumed
independently. -/
theorem existsUnique_primeArchEndpointBernsteinAbelSharpFalsePhase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃! R : ℝ,
      250000 / 251001 < R ∧ R < 1 ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius R ∧
      PrimeArchEndpointBernsteinAbelSharpFalsePhase R := by
  obtain ⟨R, hR, hRunique⟩ :=
    primeArchEndpointBernsteinAbelSharpSelectionMaster.2.2.2.1
  rcases hR.2.2.2 with htrue | hfalse
  · exact False.elim (hRH htrue.1)
  · refine ⟨R, ⟨hR.1, hfalse.2.1, hR.2.2.1, hfalse.2.2⟩, ?_⟩
    intro S hS
    apply hRunique S
    exact ⟨hS.1, hS.2.1.le, hS.2.2.1,
      Or.inr ⟨hRH, hS.2.1, hS.2.2.2⟩⟩

end

end RHTower
