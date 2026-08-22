import GaloisForLFunctions.RHTower.CCMFUSuzukiSelbergSquareRootAbelAction
import GaloisForLFunctions.RHTower.SuzukiPrimeOutgoingDilationFlux
import GaloisForLFunctions.RHTower.CCMUnitRieszSuzukiGreenProducerClassification
import GaloisForLFunctions.HTGeometry.DiscreteAbelIcc
import GaloisForLFunctions.RHTower.SuzukiCoupledErrorCriticalDerivative

/-!
# Exact half-order Abel weld for completed coherent charge

Finite Abel summation is performed only after the von Mangoldt and polar channels have been
combined.  The literal completed outgoing charge at integer aperture `M` is exactly the normalized
half-order Abel action of `psiRemainder`, plus one source-free square-root lattice defect.  The
defect has the sharp elementary bracket `-sqrt M <= D_M <= -sqrt M / 3`, hence disappears after
normalization.

This supplies a coefficient-faithful weld among CCM-FU signed curvature, coherent Route-O/HG
outgoing charge, and Suzuki Green.  It also gives an unconditional RH equivalence for uniform
boundedness of the signed Abel action.  No prime and polar absolute values are taken before their
cancellation.
-/

open Filter Topology

noncomputable section

namespace RHTower

open ArithmeticFunction Finset
open GaloisForLFunctions.RHTower

/-- Literal half-order Abel action of the completed discrete Chebyshev remainder. -/
def coherentSelbergSquareRootAbelMoment (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (M - 1),
    (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiRemainder k

/-- Source-free mismatch between the continuous polar mass and its square-root lattice sum. -/
def coherentSquareRootPolarLatticeDefect (M : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 (M - 1),
      (Real.sqrt M - Real.sqrt k)) -
    (M : ℝ) * Real.sqrt M / 3

private theorem sum_Icc_vonMangoldt_sub_one_eq_psiRemainder (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m,
        (ArithmeticFunction.vonMangoldt k - 1) = psiRemainder m := by
  rw [Finset.sum_sub_distrib, sum_Icc_vonMangoldt_eq_psi]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [psiRemainder, chebyshevPsi_eq_psi]
  norm_num

private theorem sum_vonMangoldt_sub_one_mul_sqrtGap_eq_abel
    (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 (M - 1),
        (ArithmeticFunction.vonMangoldt k - 1) *
          (Real.sqrt M - Real.sqrt k) =
      coherentSelbergSquareRootAbelMoment M := by
  have h := HTGeometry.sum_mul_eq_partial_mul_diff
    (fun k : ℕ => ArithmeticFunction.vonMangoldt k - 1)
    (fun k : ℕ => Real.sqrt M - Real.sqrt k) (M - 1)
  simp_rw [sum_Icc_vonMangoldt_sub_one_eq_psiRemainder] at h
  rw [coherentSelbergSquareRootAbelMoment]
  have htop : psiRemainder (M - 1) *
      (Real.sqrt M - Real.sqrt (M - 1 + 1 : ℕ)) = 0 := by
    cases M with
    | zero => simp [psiRemainder, chebyshevPsi]
    | succ M => simp
  rw [htop, add_zero] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem sum_vonMangoldt_mul_sqrtGap_eq_abel_add_lattice
    (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 (M - 1),
        ArithmeticFunction.vonMangoldt k *
          (Real.sqrt M - Real.sqrt k) =
      coherentSelbergSquareRootAbelMoment M +
        ∑ k ∈ Finset.Icc 1 (M - 1),
          (Real.sqrt M - Real.sqrt k) := by
  rw [← sum_vonMangoldt_sub_one_mul_sqrtGap_eq_abel M,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem weightedPrimeGap_eq_Icc_one_pred
    {M : ℕ} (hM : 2 ≤ M) :
    ∑ k ∈ Finset.Icc 2 M,
        ArithmeticFunction.vonMangoldt k *
          (Real.sqrt M - Real.sqrt k) =
      ∑ k ∈ Finset.Icc 1 (M - 1),
        ArithmeticFunction.vonMangoldt k *
          (Real.sqrt M - Real.sqrt k) := by
  rw [show Finset.Icc 2 M = insert M (Finset.Icc 2 (M - 1)) by
    ext k
    simp
    omega]
  have hnot : M ∉ Finset.Icc 2 (M - 1) := by
    simp
    omega
  rw [Finset.sum_insert hnot]
  have hsqrt : Real.sqrt (M : ℝ) - Real.sqrt (M : ℝ) = 0 := sub_self _
  rw [hsqrt, mul_zero, zero_add]
  have hpred : 1 ≤ M - 1 := by omega
  rw [show Finset.Icc 1 (M - 1) = insert 1 (Finset.Icc 2 (M - 1)) by
    ext k
    simp
    omega]
  simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- Exact finite completed-charge law before division by aperture. -/
theorem coherentCompletedOutgoing_mul_eq_abel_add_latticeDefect
    {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) * unitRieszCoherentCompletedOutgoingCharge M =
      coherentSelbergSquareRootAbelMoment M +
        coherentSquareRootPolarLatticeDefect M := by
  have hMR : (0 : ℝ) < M := by positivity
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hMR).ne'
  have hsqrtSq : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) := Real.sq_sqrt hMR.le
  rw [unitRieszCoherentCompletedOutgoingCharge,
    unitRieszCoherentPolarOutgoingCharge_eq,
    unitRieszCoherentPrimeOutgoingCharge_eq_dilation_normalForm]
  have hscale :
      (M : ℝ) *
          (∑ k ∈ Finset.Icc 2 M,
            ArithmeticFunction.vonMangoldt k *
              (1 / Real.sqrt (M : ℝ) - Real.sqrt k / (M : ℝ))) =
        ∑ k ∈ Finset.Icc 2 M,
          ArithmeticFunction.vonMangoldt k *
            (Real.sqrt M - Real.sqrt k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    field_simp [hsqrt]
    calc
      ArithmeticFunction.vonMangoldt k *
            ((M : ℝ) - Real.sqrt M * Real.sqrt k) =
          ArithmeticFunction.vonMangoldt k *
            (Real.sqrt M ^ 2 - Real.sqrt M * Real.sqrt k) := by
              rw [hsqrtSq]
      _ = ArithmeticFunction.vonMangoldt k * Real.sqrt M *
            (Real.sqrt M - Real.sqrt k) := by ring
  rw [mul_sub, hscale, weightedPrimeGap_eq_Icc_one_pred hM,
    sum_vonMangoldt_mul_sqrtGap_eq_abel_add_lattice]
  unfold coherentSquareRootPolarLatticeDefect
  ring

/-- Closed prefix-mass normal form of the source-free lattice defect. -/
theorem coherentSquareRootPolarLatticeDefect_eq_prefixMass
    {M : ℕ} (hM : 1 ≤ M) :
    coherentSquareRootPolarLatticeDefect M =
      ((2 / 3 : ℝ) * M - 1) * Real.sqrt M -
        unitRieszSqrtPrefixMass (M - 1) := by
  rw [coherentSquareRootPolarLatticeDefect,
    show (∑ k ∈ Finset.Icc 1 (M - 1),
        (Real.sqrt M - Real.sqrt k)) =
      (M - 1 : ℕ) * Real.sqrt M -
        ∑ k ∈ Finset.Icc 1 (M - 1), Real.sqrt k by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
        nsmul_eq_mul]
      norm_num]
  rw [← show Finset.Ico 1 (M - 1 + 1) = Finset.Icc 1 (M - 1) by
    ext k
    simp]
  rw [← unitRieszSqrtPrefixMass_eq_sum_Ico_one]
  rw [Nat.cast_sub hM]
  ring

/-- Sharp elementary negative bracket for the square-root polar lattice defect. -/
theorem coherentSquareRootPolarLatticeDefect_bounds
    {M : ℕ} (hM : 1 ≤ M) :
    -Real.sqrt M ≤ coherentSquareRootPolarLatticeDefect M ∧
      coherentSquareRootPolarLatticeDefect M ≤ -(1 / 3 : ℝ) * Real.sqrt M := by
  have hlower := unitRieszSqrtPrefixMass_lower (M - 1)
  have hupper := unitRieszSqrtPrefixMass_upper (M - 1)
  have hcast : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
    rw [Nat.cast_sub hM]
    norm_num
  have hpred : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub hM]
    norm_num
  rw [hcast] at hlower hupper
  rw [hpred] at hlower
  rw [coherentSquareRootPolarLatticeDefect_eq_prefixMass hM]
  norm_num at hlower hupper ⊢
  constructor <;> linarith

/-- Absolute defect is at most one square-root unit. -/
theorem abs_coherentSquareRootPolarLatticeDefect_le
    {M : ℕ} (hM : 1 ≤ M) :
    |coherentSquareRootPolarLatticeDefect M| ≤ Real.sqrt M := by
  have hb := coherentSquareRootPolarLatticeDefect_bounds hM
  rw [abs_le]
  exact ⟨hb.1, hb.2.trans (by
    nlinarith [Real.sqrt_nonneg (M : ℝ)])⟩

/-- Normalized exact completed-charge/Abel weld. -/
theorem coherentCompletedOutgoing_eq_abel_add_latticeDefect_div
    {M : ℕ} (hM : 2 ≤ M) :
    unitRieszCoherentCompletedOutgoingCharge M =
      (coherentSelbergSquareRootAbelMoment M +
        coherentSquareRootPolarLatticeDefect M) / M := by
  apply (eq_div_iff (by positivity : (M : ℝ) ≠ 0)).2
  simpa only [mul_comm] using
    coherentCompletedOutgoing_mul_eq_abel_add_latticeDefect hM

/-- The full coherent Abel action differs from the Suzuki checkpoint action by two fixed cells. -/
theorem coherentSelbergSquareRootAbelMoment_succ_eq_checkpoint
    {N : ℕ} (hN : 2 ≤ N) :
    coherentSelbergSquareRootAbelMoment (N + 1) =
      (Real.sqrt 2 - 1) * psiRemainder 1 +
        (Real.sqrt 3 - Real.sqrt 2) * psiRemainder 2 +
        suzukiCheckpointSelbergSquareRootAbelMoment N := by
  rw [coherentSelbergSquareRootAbelMoment,
    suzukiCheckpointSelbergSquareRootAbelMoment]
  rw [show N + 1 - 1 = N by omega]
  rw [show Finset.Icc 1 N =
      insert 1 (insert 2 (Finset.Ico 3 (N + 1))) by
    ext k
    simp
    omega]
  simp
  norm_num
  ring

/-- Exact Suzuki-Green readout of the signed Abel action with literal polar/arch corrections. -/
theorem unitRieszSuzukiGreen_log_nat_eq_abel_lattice_sub_corrections
    {M : ℕ} (hM : 2 ≤ M) :
    unitRieszSuzukiGreen (Real.log M) =
      (coherentSelbergSquareRootAbelMoment M +
          coherentSquareRootPolarLatticeDefect M) / M -
        unitRieszSuzukiPolarCorrection (Real.log M) +
        unitRieszSuzukiArchCorrection (Real.log M) := by
  have hout := unitRieszSuzuki_outgoing_eq_green hM
  rw [coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM] at hout
  linarith

/-- The source-free square-root lattice defect vanishes after aperture normalization. -/
theorem tendsto_coherentSquareRootPolarLatticeDefect_div_zero :
    Tendsto (fun N : ℕ =>
      coherentSquareRootPolarLatticeDefect (N + 1) / (N + 1 : ℕ))
      atTop (nhds 0) := by
  have hsqrt := tendsto_sqrt_natCast_div_natCast_atTop_zero.comp
    (Filter.tendsto_add_atTop_nat 1)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) (by
      filter_upwards with N
      have hden : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      rw [abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right
        (abs_coherentSquareRootPolarLatticeDefect_le
          (by omega : 1 ≤ N + 1)) hden.le)
      hsqrt

/-- Cofinal completed outgoing charge equals the normalized half-order Abel action. -/
theorem tendsto_outgoing_sub_normalized_coherentSelbergAbel_zero :
    Tendsto (fun N : ℕ =>
      unitRieszCoherentCompletedOutgoingCharge (N + 2) -
        coherentSelbergSquareRootAbelMoment (N + 2) / (N + 2 : ℕ))
      atTop (nhds 0) := by
  have hdef := tendsto_coherentSquareRootPolarLatticeDefect_div_zero.comp
    (Filter.tendsto_add_atTop_nat 1)
  apply hdef.congr'
  exact Eventually.of_forall fun N => by
    simp only [Function.comp_apply]
    rw [coherentCompletedOutgoing_eq_abel_add_latticeDefect_div
      (by omega : 2 ≤ N + 2)]
    ring

/-- Uniform boundedness of the literal, cancellation-preserving half-order Abel action. -/
def CoherentSelbergSquareRootAbelBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 2 ≤ M →
    |coherentSelbergSquareRootAbelMoment M / M| ≤ B

/-- RH is exactly uniform boundedness of the literal signed half-order Abel action. -/
theorem riemannHypothesis_iff_coherentSelbergSquareRootAbelBounded :
    RiemannHypothesis ↔ CoherentSelbergSquareRootAbelBounded := by
  constructor
  · intro hRH
    obtain ⟨B, hB, hres⟩ :=
      riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mp hRH
    refine ⟨B / 2 + 1, by positivity, ?_⟩
    intro M hM
    have hMR : (0 : ℝ) < M := by positivity
    have hsqrtSq : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) :=
      Real.sq_sqrt hMR.le
    have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    have hsqrtLe : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      nlinarith [Real.sqrt_nonneg (M : ℝ)]
    have hdef :
        |coherentSquareRootPolarLatticeDefect M / M| ≤ 1 := by
      rw [abs_div, abs_of_pos hMR]
      calc
        |coherentSquareRootPolarLatticeDefect M| / (M : ℝ) ≤
            Real.sqrt M / M :=
          div_le_div_of_nonneg_right
            (abs_coherentSquareRootPolarLatticeDefect_le (by omega)) hMR.le
        _ ≤ 1 := (div_le_one hMR).2 hsqrtLe
    have hcharge :
        |unitRieszCoherentCompletedOutgoingCharge M| ≤ B / 2 := by
      rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (div_le_div_of_nonneg_right (hres M hM) (by norm_num)).trans_eq rfl
    have hsplit :
        coherentSelbergSquareRootAbelMoment M / M =
          unitRieszCoherentCompletedOutgoingCharge M -
            coherentSquareRootPolarLatticeDefect M / M := by
      rw [coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM]
      ring
    rw [hsplit]
    exact (abs_sub _ _).trans (add_le_add hcharge hdef)
  · rintro ⟨B, hB, habel⟩
    apply riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mpr
    refine ⟨2 * (B + 1), by positivity, ?_⟩
    intro M hM
    have hMR : (0 : ℝ) < M := by positivity
    have hsqrtSq : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) :=
      Real.sq_sqrt hMR.le
    have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    have hsqrtLe : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      nlinarith [Real.sqrt_nonneg (M : ℝ)]
    have hdef :
        |coherentSquareRootPolarLatticeDefect M / M| ≤ 1 := by
      rw [abs_div, abs_of_pos hMR]
      calc
        |coherentSquareRootPolarLatticeDefect M| / (M : ℝ) ≤
            Real.sqrt M / M :=
          div_le_div_of_nonneg_right
            (abs_coherentSquareRootPolarLatticeDefect_le (by omega)) hMR.le
        _ ≤ 1 := (div_le_one hMR).2 hsqrtLe
    have hcharge :
        |unitRieszCoherentCompletedOutgoingCharge M| ≤ B + 1 := by
      rw [coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM]
      rw [add_div]
      exact (abs_add_le _ _).trans (add_le_add (habel M hM) hdef)
    have hrel := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM
    have hresEq :
        criticalMellinChebyshevResolventSource (Real.log M) =
          2 * unitRieszCoherentCompletedOutgoingCharge M := by
      linarith
    rw [hresEq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith

end RHTower
