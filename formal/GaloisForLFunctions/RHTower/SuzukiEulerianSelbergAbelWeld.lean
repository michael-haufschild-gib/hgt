import GaloisForLFunctions.RHTower.SuzukiEulerianSignedGammaCurrent
import GaloisForLFunctions.RHTower.CCMFUSuzukiSelbergSquareRootAbelAction
import GaloisForLFunctions.RHTower.CCMFUSuzukiSelbergOutgoingAbelWeld

/-!
# Exact Selberg--Abel normal form of the SP-E current

The two Gamma corrections entering the signed SP-E current cancel cellwise to a positive,
source-free square-root lattice term.  The resulting current has one arithmetic interior term:
the signed half-order Abel action of `psiRemainder`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open Filter Topology

noncomputable section

/-- Source-free lattice correction left after the two exact Gamma cells cancel in the SP-E
current. -/
def suzukiEulerianSelbergLatticePrefix (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ico 3 (N + 2), (p : ℝ) *
    (2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) -
      1 / Real.sqrt (p : ℝ))

/-- Exact cancellation of signed-curvature Gamma tail with Selberg Gamma remainder. -/
theorem weightedSignedCurvature_add_higherBinetGamma_eq_selbergIncrement_add_eulerianLattice
    (N : ℕ) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N +
        suzukiEulerianHigherBinetGammaPrefix N =
      suzukiCheckpointWeightedSelbergIncrementPrefix N +
        suzukiEulerianSelbergLatticePrefix N := by
  rw [suzukiEulerianHigherBinetGammaPrefix_eq_archTailPrefix,
    weightedSignedCurvaturePrefix_eq_selbergIncrement_add_arch]
  suffices harch :
      suzukiCheckpointWeightedSelbergArchRemainderPrefix N +
        suzukiCheckpointWeightedArchTailPrefix N =
          suzukiEulerianSelbergLatticePrefix N by
    linarith
  rw [suzukiCheckpointWeightedSelbergArchRemainderPrefix,
    suzukiCheckpointWeightedArchTailPrefix, suzukiEulerianSelbergLatticePrefix,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp3 : 3 ≤ p := (Finset.mem_Ico.mp hp).1
  rw [suzukiCheckpointSelbergArchRemainderCell,
    integral_screwRegularKernel_eq_expHalf_sub_archTail hp3]
  have hexp :
      (∫ t in Real.log ((p - 1 : ℕ) : ℝ)..Real.log (p : ℝ),
        Real.exp (t / 2)) =
      2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using
      (integral_exp_half_log_cell (k := p - 1) (by omega : 1 ≤ p - 1))
  rw [hexp]
  ring

/-- The source-free lattice cell has a manifestly positive square-root form. -/
theorem suzukiEulerianSelbergLatticeCell_eq
    {p : ℕ} (hp : 3 ≤ p) :
    (p : ℝ) *
        (2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) -
          1 / Real.sqrt (p : ℝ)) =
      Real.sqrt (p : ℝ) /
        (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpred0 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < p - 1)
  have hroot : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hpredRoot : Real.sqrt ((p - 1 : ℕ) : ℝ) ^ 2 = ((p - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hpred0.le
  have hunit : (p : ℝ) - ((p - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hgap : Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ) =
      (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ))⁻¹ := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using
      (sqrt_nat_succ_sub_eq_inv_add (p - 1))
  have hrootPos : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  have hsumPos : Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  rw [hgap]
  field_simp [hrootPos, hsumPos]
  nlinarith [hroot, hpredRoot, hunit]

/-- Each lattice cell is nonnegative and no larger than the half-order summation kernel. -/
theorem suzukiEulerianSelbergLatticeCell_nonneg_le
    {p : ℕ} (hp : 3 ≤ p) :
    0 ≤ (p : ℝ) *
        (2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) -
          1 / Real.sqrt (p : ℝ)) ∧
      (p : ℝ) *
        (2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) -
          1 / Real.sqrt (p : ℝ)) ≤
        (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [suzukiEulerianSelbergLatticeCell_eq hp]
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hroot0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  have hsum0 : 0 < Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ) := by
    positivity
  constructor
  · positivity
  · rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos hsum0)).2
    rw [show 1 / Real.sqrt (p : ℝ) *
        (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ 2 =
      (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ 2 /
        Real.sqrt (p : ℝ) by ring]
    apply (le_div_iff₀ hroot0).2
    have hmul : 0 ≤ Real.sqrt (p : ℝ) * Real.sqrt ((p - 1 : ℕ) : ℝ) := by
      positivity
    have hsq : 0 ≤ Real.sqrt ((p - 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith

/-- The deterministic lattice correction has fixed sign and only square-root size. -/
theorem suzukiEulerianSelbergLatticePrefix_nonneg_le (N : ℕ) :
    0 ≤ suzukiEulerianSelbergLatticePrefix N ∧
      suzukiEulerianSelbergLatticePrefix N ≤ 2 * Real.sqrt (N + 2 : ℕ) := by
  rw [suzukiEulerianSelbergLatticePrefix]
  have hcell : ∀ p ∈ Finset.Ico 3 (N + 2),
      0 ≤ (p : ℝ) *
          (2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) -
            1 / Real.sqrt (p : ℝ)) ∧
        (p : ℝ) *
          (2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) -
            1 / Real.sqrt (p : ℝ)) ≤
          (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro p hp
    exact suzukiEulerianSelbergLatticeCell_nonneg_le (Finset.mem_Ico.mp hp).1
  constructor
  · exact Finset.sum_nonneg fun p hp => (hcell p hp).1
  · calc
      ∑ p ∈ Finset.Ico 3 (N + 2), (p : ℝ) *
          (2 * (Real.sqrt (p : ℝ) - Real.sqrt ((p - 1 : ℕ) : ℝ)) -
            1 / Real.sqrt (p : ℝ)) ≤
        ∑ p ∈ Finset.Ico 3 (N + 2), (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
          exact Finset.sum_le_sum fun p hp => (hcell p hp).2
      _ ≤ ∑ p ∈ Finset.Icc 1 (N + 2), (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_Ico, Finset.mem_Icc] at hp ⊢
            omega
          · intro p hp _
            positivity
      _ ≤ 2 * Real.sqrt (N + 2 : ℕ) := sum_rpow_neg_half_le (N + 2)

/-- Exact arithmetic normal form of corrected Chebyshev SP-E current.  Sole non-elementary
interior term is signed half-order Abel action of `psiRemainder`. -/
theorem suzukiChebyshevMassErrorCesaroDefect_eq_normalizedError_sub_squareRootAbel_lattice
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiChebyshevMassErrorCesaroDefect N =
      criticalMellinNormalizedChebyshevError (Real.log ((N + 1 : ℕ) : ℝ)) -
        (Real.sqrt 3 * psiRemainder 2 +
          suzukiCheckpointSelbergSquareRootAbelMoment N +
          suzukiEulerianSelbergLatticePrefix N) / (N + 1 : ℕ) := by
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_neg_weightedSignedCurvature_sub_higherBinetGamma hN,
    weightedSignedCurvature_add_higherBinetGamma_eq_selbergIncrement_add_eulerianLattice,
    weightedSelbergIncrement_eq_normalizedErrorBoundary_add_squareRootAbel hN]
  have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- Fixed two-cell anchor converting the checkpoint half-order action to the literal coherent
completed action. -/
def suzukiEulerianCoherentBoundaryAnchor : ℝ :=
  Real.sqrt 2 * psiRemainder 2 -
    (Real.sqrt 2 - 1) * psiRemainder 1

/-- Exact SP-E form with the literal coherent half-order Abel source, rather than its checkpoint
truncation. -/
theorem suzukiChebyshevMassErrorCesaroDefect_eq_normalizedError_sub_coherentSquareRootAbel
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiChebyshevMassErrorCesaroDefect N =
      criticalMellinNormalizedChebyshevError (Real.log ((N + 1 : ℕ) : ℝ)) -
        (coherentSelbergSquareRootAbelMoment (N + 1) +
          suzukiEulerianSelbergLatticePrefix N +
          suzukiEulerianCoherentBoundaryAnchor) / (N + 1 : ℕ) := by
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_normalizedError_sub_squareRootAbel_lattice hN,
    coherentSelbergSquareRootAbelMoment_succ_eq_checkpoint hN]
  simp only [suzukiEulerianCoherentBoundaryAnchor]
  ring

/-- **Direct SP-E source weld.**  Corrected Chebyshev mass error minus terminal normalized error
is the negative literal completed outgoing charge, up to an explicit source-free finite residual. -/
theorem suzukiChebyshevMassErrorCesaroDefect_eq_normalizedError_sub_completedOutgoing
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiChebyshevMassErrorCesaroDefect N =
      criticalMellinNormalizedChebyshevError (Real.log ((N + 1 : ℕ) : ℝ)) -
        unitRieszCoherentCompletedOutgoingCharge (N + 1) +
        (coherentSquareRootPolarLatticeDefect (N + 1) -
          suzukiEulerianSelbergLatticePrefix N -
          suzukiEulerianCoherentBoundaryAnchor) / (N + 1 : ℕ) := by
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_normalizedError_sub_coherentSquareRootAbel hN,
    coherentCompletedOutgoing_eq_abel_add_latticeDefect_div (by omega : 2 ≤ N + 1)]
  have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The deterministic SP-E lattice correction vanishes after the physical aperture
normalization. -/
theorem tendsto_suzukiEulerianSelbergLatticePrefix_div_zero :
    Tendsto (fun N : ℕ => suzukiEulerianSelbergLatticePrefix N / (N + 1 : ℕ))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun N : ℕ =>
      4 * (Real.sqrt ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_sqrt_natCast_div_natCast_atTop_zero.comp
        (Filter.tendsto_add_atTop_nat 1)).const_mul (4 : ℝ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) (by
      filter_upwards with N
      have hden : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have hshift : Real.sqrt ((N + 2 : ℕ) : ℝ) ≤
          2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
        have hnat : ((N + 2 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : N + 2 ≤ 4 * (N + 1))
        calc
          Real.sqrt ((N + 2 : ℕ) : ℝ) ≤
              Real.sqrt (4 * ((N + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hnat
          _ = 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num
      rw [abs_div, abs_of_nonneg (suzukiEulerianSelbergLatticePrefix_nonneg_le N).1,
        abs_of_pos hden]
      calc
        suzukiEulerianSelbergLatticePrefix N / ((N + 1 : ℕ) : ℝ) ≤
            (2 * Real.sqrt ((N + 2 : ℕ) : ℝ)) / ((N + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right
            (suzukiEulerianSelbergLatticePrefix_nonneg_le N).2 hden.le
        _ ≤ 4 * (Real.sqrt ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
          rw [show 4 * (Real.sqrt ((N + 1 : ℕ) : ℝ) /
              ((N + 1 : ℕ) : ℝ)) =
            (4 * Real.sqrt ((N + 1 : ℕ) : ℝ)) / ((N + 1 : ℕ) : ℝ) by ring]
          apply (div_le_div_iff_of_pos_right hden).2
          nlinarith) hsqrt

/-- Cofinal source law: the SP-E defect after terminal normalized Chebyshev error is exactly the
negative completed outgoing source in the limit. -/
theorem tendsto_suzukiChebyshevMassError_sub_normalizedError_add_completedOutgoing_zero :
    Tendsto (fun N : ℕ =>
      suzukiChebyshevMassErrorCesaroDefect N -
        criticalMellinNormalizedChebyshevError (Real.log ((N + 1 : ℕ) : ℝ)) +
        unitRieszCoherentCompletedOutgoingCharge (N + 1))
      atTop (nhds 0) := by
  have hdef := tendsto_coherentSquareRootPolarLatticeDefect_div_zero
  have hlattice := tendsto_suzukiEulerianSelbergLatticePrefix_div_zero
  have hanchor :=
    (tendsto_const_div_atTop_nhds_zero_nat suzukiEulerianCoherentBoundaryAnchor).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hsum := (hdef.sub hlattice).sub hanchor
  have hsum0 : Tendsto (fun N : ℕ =>
      coherentSquareRootPolarLatticeDefect (N + 1) / (N + 1 : ℕ) -
        suzukiEulerianSelbergLatticePrefix N / (N + 1 : ℕ) -
        suzukiEulerianCoherentBoundaryAnchor / (N + 1 : ℕ)) atTop (nhds 0) := by
    convert hsum using 1 <;> norm_num
  apply hsum0.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [suzukiChebyshevMassErrorCesaroDefect_eq_normalizedError_sub_completedOutgoing hN]
  ring

end

end GaloisForLFunctions.RHTower
