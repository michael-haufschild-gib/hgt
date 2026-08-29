import GaloisForLFunctions.RHTower.CoupledFloorMobiusCriticalBoundaryCancellation
import GaloisForLFunctions.RHTower.CCMFUSuzukiCompletedRieszGraphEnergy

/-!
# Affine-Riesz handoff from the coupled floor--Möbius incidence to CCM-FU

The critical CFI carrier is a literal complementary lower-minus-upper shift incidence.  Its
arithmetic normalization had not been connected to the coefficient-faithful CCM-FU endpoint:
sampling the incidence at moving integer logarithmic clocks introduces both a divergent clock and
the critical `1 / ω` affine quotient.

This file performs that normalization before scalarization.  Undoing the common critical clock
recovers Suzuki's coupled error exactly.  The affine quotient plus Gamma boundary, transported by
the square-root Riesz mesh, is therefore exactly the completed Suzuki critical jet.  One positive
cofinal schedule then tracks the literal signed Möbius-divisor Riesz source, and uniform normalized
boundedness of that same incidence readout is equivalent to RH.

Together with `coupledFloorMobiusCriticalBoundary_singularCancellation`, this closes CFI's `ORD`
and `LAND` gates and folds CFI coefficient-faithfully into CCM-FU.  It does not assert the remaining
RH-equivalent boundedness premise.
-/

open Finset ArithmeticFunction Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-- Literal CFI readout: sample the unsplit complementary incidence at integer logarithmic clocks,
undo its common critical clock, take the critical affine quotient, retain the Gamma boundary, and
only then apply the square-root Riesz mesh. -/
def coupledFloorMobiusAffineRieszReadout (ω : ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 1),
    ((1 / 2 : ℝ) *
        ((Real.exp ((1 + ω) * Real.log (k + 1 : ℕ)) *
            (∑' d : ℕ,
              (incidenceLower ω 0 (Real.log (k + 1 : ℕ)) d -
                incidenceUpper ω 0 (Real.log (k + 1 : ℕ)) d)) - 1) / ω) +
      2 * Real.eulerMascheroniConstant) *
      (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))

/-- Exact integer-clock recovery of Suzuki's coupled error from the literal lower-minus-upper
incidence.  No branch is estimated or separated. -/
theorem exp_mul_tsum_coupledFloorMobiusIncidence_eq_coupledError
    {ω : ℝ} (hω : 0 < ω) {X : ℕ} (hX : 1 ≤ X) :
    Real.exp ((1 + ω) * Real.log X) *
        (∑' d : ℕ,
          (incidenceLower ω 0 (Real.log X) d -
            incidenceUpper ω 0 (Real.log X) d)) =
      suzukiCoupledError ω X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  rw [← coupledErrorVector_eq_tsum_zero hω hlog]
  rw [coupledErrorVector]
  rw [show (1 + ω + 0) = 1 + ω by ring]
  rw [Real.exp_log hXR, suzukiCoupledErrorReal_natCast]
  rw [← mul_assoc, ← Real.exp_add]
  rw [show (1 + ω) * Real.log X + -((1 + ω) * Real.log X) = 0 by ring]
  simp

/-- **Finite CFI-to-CCM-FU landing.**  At every positive critical displacement and every finite
aperture, the affine-normalized literal incidence is exactly the completed Suzuki Riesz jet. -/
theorem coupledFloorMobiusAffineRieszReadout_eq_suzukiCompletedRieszCriticalJetApprox
    {ω : ℝ} (hω : 0 < ω) (M : ℕ) :
    coupledFloorMobiusAffineRieszReadout ω M =
      suzukiCompletedRieszCriticalJetApprox ω M := by
  rw [coupledFloorMobiusAffineRieszReadout,
    suzukiCompletedRieszCriticalJetApprox]
  apply Finset.sum_congr rfl
  intro k hk
  rw [exp_mul_tsum_coupledFloorMobiusIncidence_eq_coupledError hω
    (by omega : 1 ≤ k + 1)]

/-- Uniform normalized boundedness of the literal CFI affine-Riesz incidence readout along a
positive critical schedule. -/
def CoupledFloorMobiusAffineRieszCofinalBounded (ω : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 2 ≤ M →
    |coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M / M| ≤ B

/-- The literal CFI incidence has an unconditional cofinal affine normalization which tracks the
completed Möbius-divisor Riesz source before scalarization. -/
theorem exists_coupledFloorMobiusAffineRieszCofinalSchedule :
    ∃ ω : ℕ → ℝ,
      Tendsto ω atTop (nhds 0) ∧
      Tendsto (fun N : ℕ =>
        coupledFloorMobiusAffineRieszReadout (ω N) (N + 1) -
          mobiusDivisorSquareRootAbelMoment (N + 1)) atTop (nhds 0) ∧
      ∀ N : ℕ,
        0 < ω N ∧
        ω N < 1 / ((N : ℝ) + 1) ∧
        |coupledFloorMobiusAffineRieszReadout (ω N) (N + 1) -
          mobiusDivisorSquareRootAbelMoment (N + 1)| <
            1 / ((N : ℝ) + 1) := by
  obtain ⟨ω, hω, hlimit, hpoint⟩ :=
    exists_suzukiCompletedRieszCriticalJetCofinalSchedule
  refine ⟨ω, hω, ?_, ?_⟩
  · apply hlimit.congr'
    exact Filter.Eventually.of_forall fun N => by
      exact congrArg
        (fun x : ℝ => x - mobiusDivisorSquareRootAbelMoment (N + 1))
        (coupledFloorMobiusAffineRieszReadout_eq_suzukiCompletedRieszCriticalJetApprox
          (hpoint N).1 (N + 1)).symm
  · intro N
    refine ⟨(hpoint N).1, (hpoint N).2.1, ?_⟩
    rw [coupledFloorMobiusAffineRieszReadout_eq_suzukiCompletedRieszCriticalJetApprox
      (hpoint N).1]
    exact (hpoint N).2.2

/-- Along any schedule with the coefficient-faithful pointwise landing, boundedness of the literal
incidence readout is exactly boundedness of the Möbius-divisor source. -/
theorem coupledFloorMobiusAffineRieszCofinalBounded_iff_mobiusDivisor
    {ω : ℕ → ℝ}
    (hpoint : ∀ N : ℕ,
      0 < ω N ∧
      |coupledFloorMobiusAffineRieszReadout (ω N) (N + 1) -
        mobiusDivisorSquareRootAbelMoment (N + 1)| <
          1 / ((N : ℝ) + 1)) :
    CoupledFloorMobiusAffineRieszCofinalBounded ω ↔
      MobiusDivisorSquareRootAbelBounded := by
  constructor
  · rintro ⟨B, hB, hreadout⟩
    refine ⟨B + 1, by positivity, ?_⟩
    intro M hM
    have hMR : (0 : ℝ) < M := by positivity
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hindex : M - 1 + 1 = M := by omega
    have hindexR : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast hindex
    have herr := (hpoint (M - 1)).2
    rw [hindex, hindexR] at herr
    have hdiff :
        |(coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
          mobiusDivisorSquareRootAbelMoment M) / M| ≤ 1 := by
      rw [abs_div, abs_of_pos hMR]
      calc
        |coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
            mobiusDivisorSquareRootAbelMoment M| / M ≤
            |coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
              mobiusDivisorSquareRootAbelMoment M| :=
          div_le_self (abs_nonneg _) hMone
        _ ≤ 1 / (M : ℝ) := herr.le
        _ ≤ 1 := div_le_self (by norm_num) hMone
    have hsplit :
        mobiusDivisorSquareRootAbelMoment M / M =
          coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M / M -
            (coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
              mobiusDivisorSquareRootAbelMoment M) / M := by ring
    rw [hsplit]
    exact (abs_sub _ _).trans (add_le_add (hreadout M hM) hdiff)
  · rintro ⟨B, hB, hsource⟩
    refine ⟨B + 1, by positivity, ?_⟩
    intro M hM
    have hMR : (0 : ℝ) < M := by positivity
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hindex : M - 1 + 1 = M := by omega
    have hindexR : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by exact_mod_cast hindex
    have herr := (hpoint (M - 1)).2
    rw [hindex, hindexR] at herr
    have hdiff :
        |(coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
          mobiusDivisorSquareRootAbelMoment M) / M| ≤ 1 := by
      rw [abs_div, abs_of_pos hMR]
      calc
        |coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
            mobiusDivisorSquareRootAbelMoment M| / M ≤
            |coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
              mobiusDivisorSquareRootAbelMoment M| :=
          div_le_self (abs_nonneg _) hMone
        _ ≤ 1 / (M : ℝ) := herr.le
        _ ≤ 1 := div_le_self (by norm_num) hMone
    have hsplit :
        coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M / M =
          mobiusDivisorSquareRootAbelMoment M / M +
            (coupledFloorMobiusAffineRieszReadout (ω (M - 1)) M -
              mobiusDivisorSquareRootAbelMoment M) / M := by ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add (hsource M hM) hdiff)

/-- **Closed CFI-to-CCM-FU handoff.**  One unconditional positive moving affine schedule is
coefficient-faithful, cofinally lands on the literal Möbius-divisor source, and its normalized
boundedness is exactly RH. -/
theorem exists_coupledFloorMobiusAffineRieszHandoff_iff_rh :
    ∃ ω : ℕ → ℝ,
      Tendsto ω atTop (nhds 0) ∧
      (∀ N : ℕ,
        0 < ω N ∧
        ω N < 1 / ((N : ℝ) + 1) ∧
        |coupledFloorMobiusAffineRieszReadout (ω N) (N + 1) -
          mobiusDivisorSquareRootAbelMoment (N + 1)| <
            1 / ((N : ℝ) + 1)) ∧
      (RiemannHypothesis ↔
        CoupledFloorMobiusAffineRieszCofinalBounded ω) := by
  obtain ⟨ω, hω, _hlimit, hpoint⟩ :=
    exists_coupledFloorMobiusAffineRieszCofinalSchedule
  refine ⟨ω, hω, hpoint, ?_⟩
  exact riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded.trans
    (coupledFloorMobiusAffineRieszCofinalBounded_iff_mobiusDivisor
      (fun N => ⟨(hpoint N).1, (hpoint N).2.2⟩)).symm

end

end RHTower
