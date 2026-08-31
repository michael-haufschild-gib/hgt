import GaloisForLFunctions.RHTower.CCMCriticalMellinResolventExponentialWidth
import GaloisForLFunctions.RHTower.SuzukiCanonicalSignedCompensationSaturation

/-!
# Quadratic-contact width loss for Suzuki transition-core compensation

Let `C_N` be the positive Suzuki transition core and `E_N` its aligned Gamma-completed energy.
The first-contact residual `E_N` is already known to be bounded exactly under RH.  This module
studies the first nonlinear alternative `E_N^2 / C_N`.

If that quadratic residual is eventually bounded, the completed Suzuki Green amplitude grows at
most like `N^(1/4)`.  Exact Green/outgoing-charge identities and the logarithmic-lattice handoff
turn this into the resolvent envelope `Q(t) = O(exp(t/4))`.  The quantitative CCM continuation
then places every Xi zero in `Re rho ≤ 3/4`.

Thus quadratic contact spends one quarter-plane of the analytic continuation supplied by the
same compensation mechanism.  All statements are unconditional; boundedness appears only as the
explicit route premise.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def suzukiTransitionCoreQuadraticContactResidual (N : ℕ) : ℝ :=
  if _hC : suzukiNaturalApertureTransitionCoreCauchyEnergy N = 0 then 0
  else suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ 2 /
    suzukiNaturalApertureTransitionCoreCauchyEnergy N

theorem suzukiTransitionCoreQuadraticContactResidual_nonneg (N : ℕ) :
    0 ≤ suzukiTransitionCoreQuadraticContactResidual N := by
  rw [suzukiTransitionCoreQuadraticContactResidual]
  split_ifs with hC
  · exact le_rfl
  · exact div_nonneg
      (sq_nonneg _)
      (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N)

def SuzukiTransitionCoreQuadraticContactResidualEventuallyBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
    suzukiTransitionCoreQuadraticContactResidual N ≤ B

private theorem le_fourth_add_one {x : ℝ} (hx : 0 ≤ x) :
    x ≤ x ^ 4 + 1 := by
  by_cases hx1 : x ≤ 1
  · have hnonneg : 0 ≤ x ^ 4 := by positivity
    linarith
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    have hx2 : x ≤ x ^ 2 := by nlinarith
    have hx2one : 1 ≤ x ^ 2 := by nlinarith
    have hx24 : x ^ 2 ≤ (x ^ 2) ^ 2 := by nlinarith
    calc
      x ≤ x ^ 2 := hx2
      _ ≤ x ^ 4 := by nlinarith
      _ ≤ x ^ 4 + 1 := by linarith

def suzukiTransitionCoreLinearEnvelope : ℝ :=
  18 * (Real.log 4 + 4) ^ 2

theorem suzukiTransitionCoreLinearEnvelope_nonneg :
    0 ≤ suzukiTransitionCoreLinearEnvelope := by
  unfold suzukiTransitionCoreLinearEnvelope
  positivity

theorem eventually_abs_completedLowerHardyAmplitude_le_quarterPower_of_quadraticContactBound
    {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreQuadraticContactResidual N ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        (B * suzukiTransitionCoreLinearEnvelope + 1) *
          Real.exp (Real.log N / 4) := by
  filter_upwards [hbound,
    eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero,
    eventually_completedAnchor_sq_le_suzukiTransitionCoreAlignedEnergy,
    eventually_ge_atTop (2 : ℕ)] with N hres hC hG hN
  have hC0 : 0 < suzukiNaturalApertureTransitionCoreCauchyEnergy N :=
    lt_of_le_of_ne (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N)
      (Ne.symm hC)
  have hE2 : suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ 2 ≤
      B * suzukiNaturalApertureTransitionCoreCauchyEnergy N := by
    rw [suzukiTransitionCoreQuadraticContactResidual, dif_neg hC] at hres
    exact (div_le_iff₀ hC0).mp hres
  have hCupper := suzukiNaturalApertureTransitionCoreCauchyEnergy_le_linear N
  have hG2nonneg : 0 ≤
      suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ 2 := sq_nonneg _
  have hE0 := suzukiTransitionCoreAlignedGammaCompletedEnergy_nonneg N
  have hG4E2 :
      suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ 4 ≤
        suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ 2 := by
    nlinarith [sq_nonneg
      (suzukiTransitionCoreAlignedGammaCompletedEnergy N -
        suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ 2)]
  have hG4 :
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ 4 ≤
        (B * suzukiTransitionCoreLinearEnvelope) * N := by
    have habs4 :
        |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ 4 =
          suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ 4 := by
      rw [show |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ 4 =
        (|suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ 2) ^ 2 by ring,
        sq_abs]
      ring
    rw [habs4]
    unfold suzukiTransitionCoreLinearEnvelope
    calc
      _ ≤ suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ 2 := hG4E2
      _ ≤ B * suzukiNaturalApertureTransitionCoreCauchyEnergy N := hE2
      _ ≤ B * (18 * (Real.log 4 + 4) ^ 2 * N) := by
        exact mul_le_mul_of_nonneg_left hCupper hB0
      _ = _ := by ring
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  let y : ℝ := Real.exp (Real.log N / 4)
  have hy : 0 < y := Real.exp_pos _
  have hy4 : y ^ 4 = (N : ℝ) := by
    dsimp only [y]
    rw [show Real.exp (Real.log N / 4) ^ 4 =
      Real.exp (Real.log N / 4 + Real.log N / 4 +
        Real.log N / 4 + Real.log N / 4) by
      rw [show Real.exp (Real.log N / 4) ^ 4 =
        Real.exp (Real.log N / 4) * Real.exp (Real.log N / 4) *
          Real.exp (Real.log N / 4) * Real.exp (Real.log N / 4) by ring,
        ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]]
    rw [show Real.log N / 4 + Real.log N / 4 +
        Real.log N / 4 + Real.log N / 4 = Real.log N by ring,
      Real.exp_log hNR]
  let z : ℝ := |suzukiNaturalApertureCompletedLowerHardyAmplitude N| / y
  have hz0 : 0 ≤ z := div_nonneg (abs_nonneg _) hy.le
  have hz4 : z ^ 4 ≤ B * suzukiTransitionCoreLinearEnvelope := by
    rw [show z ^ 4 =
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ 4 / y ^ 4 by
      dsimp only [z]
      exact div_pow _ _ 4]
    rw [hy4]
    exact (div_le_iff₀ hNR).2 (by simpa [mul_assoc] using hG4)
  have hz := le_fourth_add_one hz0
  have hzle : z ≤ B * suzukiTransitionCoreLinearEnvelope + 1 :=
    hz.trans (by simpa [add_comm] using add_le_add_right hz4 1)
  have hrecover :
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| = z * y := by
    dsimp only [z]
    field_simp [hy.ne']
  rw [hrecover]
  exact mul_le_mul_of_nonneg_right hzle hy.le

theorem exists_abs_completedLowerHardyAmplitude_le_quarterPower_of_quadraticContactBound
    {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreQuadraticContactResidual N ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        K * Real.exp (Real.log N / 4) := by
  have hevent :=
    eventually_abs_completedLowerHardyAmplitude_le_quarterPower_of_quadraticContactBound
      hB0 hbound
  rw [eventually_atTop] at hevent
  obtain ⟨N₀, hN₀⟩ := hevent
  let K₀ : ℝ := B * suzukiTransitionCoreLinearEnvelope + 1
  let K : ℝ := K₀ + ∑ N ∈ Finset.range N₀,
    |suzukiNaturalApertureCompletedLowerHardyAmplitude N|
  have hK₀ : 0 ≤ K₀ := by
    dsimp only [K₀]
    exact add_nonneg
      (mul_nonneg hB0 suzukiTransitionCoreLinearEnvelope_nonneg) (by norm_num)
  have hsum0 : 0 ≤ ∑ N ∈ Finset.range N₀,
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| := by positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hexp1 : 1 ≤ Real.exp (Real.log N / 4) := by
    rw [Real.one_le_exp_iff]
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
    linarith
  by_cases hlarge : N₀ ≤ N
  · have hmain := hN₀ N hlarge
    exact hmain.trans (mul_le_mul_of_nonneg_right
      (show K₀ ≤ K by
        dsimp only [K]
        linarith) (Real.exp_pos _).le)
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (lt_of_not_ge hlarge)
    have hterm : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        ∑ n ∈ Finset.range N₀,
          |suzukiNaturalApertureCompletedLowerHardyAmplitude n| := by
      exact Finset.single_le_sum
        (fun i _ => abs_nonneg (suzukiNaturalApertureCompletedLowerHardyAmplitude i)) hmem
    calc
      _ ≤ ∑ n ∈ Finset.range N₀,
          |suzukiNaturalApertureCompletedLowerHardyAmplitude n| := hterm
      _ ≤ K := by
        dsimp only [K]
        linarith
      _ ≤ K * Real.exp (Real.log N / 4) := by
        nlinarith [show 0 ≤ K by dsimp only [K]; positivity]

theorem exists_log_nat_bound_criticalMellinChebyshevResolventSource_quarterPower_of_quadraticContactBound
    {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreQuadraticContactResidual N ≤ B) :
    ∃ KQ : ℝ, 0 ≤ KQ ∧ ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤
        KQ * Real.exp (Real.log N / 4) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_abs_completedLowerHardyAmplitude_le_quarterPower_of_quadraticContactBound
      hB0 hbound
  let J : ℝ := unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound
  let KQ : ℝ := 2 * (K + J)
  have hPolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
    unfold unitRieszSuzukiPolarUniformBound
    positivity
  have hArch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
    unfold unitRieszSuzukiArchUniformBound
    exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      unitRieszSuzukiArchDenominator_pos.le
  have hJ0 : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨KQ, by dsimp only [KQ]; positivity, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hH : unitRieszSuzukiBase ≤ Real.log N := by
    exact (unitRieszSuzukiBase_lt_log_two.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hNR
        (by exact_mod_cast hN))).le
  have hGreen : suzukiNaturalApertureCompletedLowerHardyAmplitude N =
      unitRieszSuzukiGreen (Real.log N) := by
    have h := suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green (N - 2)
    simpa [Nat.sub_add_cancel hN] using h
  have hP := abs_unitRieszSuzukiPolarCorrection_le hH
  have hA := abs_unitRieszSuzukiArchCorrection_le hH
  have hout := unitRieszSuzuki_outgoing_eq_green hN
  have hcharge := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN
  have hG := hK N hN
  have hexp1 : 1 ≤ Real.exp (Real.log N / 4) := by
    rw [Real.one_le_exp_iff]
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
    linarith
  have houtAbs : |unitRieszCoherentCompletedOutgoingCharge N| ≤
      (K + J) * Real.exp (Real.log N / 4) := by
    rw [hout]
    calc
      |unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N) -
          unitRieszSuzukiArchCorrection (Real.log N)| ≤
          |unitRieszSuzukiGreen (Real.log N)| +
            |unitRieszSuzukiPolarCorrection (Real.log N)| +
              |unitRieszSuzukiArchCorrection (Real.log N)| := by
        have hs := abs_sub
          (unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N))
          (unitRieszSuzukiArchCorrection (Real.log N))
        have ha := abs_add_le (unitRieszSuzukiGreen (Real.log N))
          (unitRieszSuzukiPolarCorrection (Real.log N))
        linarith
      _ ≤ K * Real.exp (Real.log N / 4) + J := by
        rw [← hGreen]
        dsimp only [J]
        linarith
      _ ≤ (K + J) * Real.exp (Real.log N / 4) := by
        nlinarith
  have hres : criticalMellinChebyshevResolventSource (Real.log N) =
      2 * unitRieszCoherentCompletedOutgoingCharge N := by
    linarith
  rw [hres, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [KQ, mul_assoc] using
    mul_le_mul_of_nonneg_left houtAbs (by norm_num : (0 : ℝ) ≤ 2)

theorem exists_global_quarterExponential_bound_criticalMellinChebyshevResolventSource_of_log_nat
    {K : ℝ} (hK0 : 0 ≤ K)
    (hlog : ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤
        K * Real.exp (Real.log N / 4)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      |criticalMellinChebyshevResolventSource t| ≤
        B * Real.exp ((1 / 4 : ℝ) * t) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    continuous_criticalMellinChebyshevResolventRayRepresentative.norm.continuousOn
  let T : ℝ := K + (Real.log 4 + 5)
  let B : ℝ := max |C| T
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hB0 : 0 ≤ B := (abs_nonneg C).trans (le_max_left _ _)
  refine ⟨B, hB0, ?_⟩
  intro t ht
  by_cases hhead : t ≤ Real.log 2
  · have hcompact := hC (mem_image_of_mem
        (fun u : ℝ => ‖criticalMellinChebyshevResolventRayRepresentative u‖)
        (show t ∈ Icc (0 : ℝ) (Real.log 2) from ⟨ht, hhead⟩))
    have hrep := criticalMellinChebyshevResolventRayRepresentative_eq ht
    rw [Real.norm_eq_abs, hrep] at hcompact
    have hexp1 : 1 ≤ Real.exp ((1 / 4 : ℝ) * t) := by
      rw [Real.one_le_exp_iff]
      positivity
    have hCB : C ≤ B := (le_abs_self C).trans (le_max_left _ _)
    nlinarith
  · have htail : Real.log 2 ≤ t := le_of_not_ge hhead
    let X : ℝ := Real.exp t
    let N : ℕ := ⌊X⌋₊
    have hX2 : (2 : ℝ) ≤ X := by
      rw [show (2 : ℝ) = Real.exp (Real.log 2) by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
      exact Real.exp_le_exp.mpr htail
    have hX0 : 0 ≤ X := (Real.exp_pos t).le
    have hN : 2 ≤ N := Nat.le_floor hX2
    have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0
    have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
    have hcell := abs_criticalMellinChebyshevResolventSource_log_le_nat_add hN hNX hXN
    have hlogX : Real.log X = t := by
      dsimp only [X]
      exact Real.log_exp t
    rw [hlogX] at hcell
    have hlogNle : Real.log (N : ℝ) ≤ t := by
      rw [← hlogX]
      exact Real.strictMonoOn_log.monotoneOn
        (show (N : ℝ) ∈ Ioi 0 by
          show 0 < (N : ℝ)
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN))
        (show X ∈ Ioi 0 by exact Real.exp_pos t) hNX
    have hexpN : Real.exp (Real.log N / 4) ≤
        Real.exp ((1 / 4 : ℝ) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hexp1 : 1 ≤ Real.exp ((1 / 4 : ℝ) * t) := by
      rw [Real.one_le_exp_iff]
      positivity
    have hsample := hlog N hN
    have htailBound :
        |criticalMellinChebyshevResolventSource t| ≤
          T * Real.exp ((1 / 4 : ℝ) * t) := by
      calc
        _ ≤ |criticalMellinChebyshevResolventSource (Real.log N)| +
            (Real.log 4 + 5) := hcell
        _ ≤ K * Real.exp (Real.log N / 4) + (Real.log 4 + 5) := by linarith
        _ ≤ K * Real.exp ((1 / 4 : ℝ) * t) +
            (Real.log 4 + 5) * Real.exp ((1 / 4 : ℝ) * t) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hexpN hK0)
            (by
              have hC0 : 0 ≤ Real.log 4 + 5 := by positivity
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hexp1 hC0)
        _ = T * Real.exp ((1 / 4 : ℝ) * t) := by
          dsimp only [T]
          ring
    exact htailBound.trans (mul_le_mul_of_nonneg_right
      (le_max_right |C| T) (Real.exp_pos _).le)

theorem criticalMellinChebyshevResolventExponentialBounded_quarter_of_quadraticContactBound
    {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreQuadraticContactResidual N ≤ B) :
    CriticalMellinChebyshevResolventExponentialBounded (1 / 4) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_log_nat_bound_criticalMellinChebyshevResolventSource_quarterPower_of_quadraticContactBound
      hB0 hbound
  exact exists_global_quarterExponential_bound_criticalMellinChebyshevResolventSource_of_log_nat
    hK0 hK

theorem xiZeroHalfPlaneBound_quarter_of_suzukiTransitionCoreQuadraticContactResidualEventuallyBounded
    (hquad : SuzukiTransitionCoreQuadraticContactResidualEventuallyBounded) :
    XiZeroHalfPlaneBound (1 / 4) := by
  obtain ⟨B, hB0, hbound⟩ := hquad
  apply xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventExponentialBounded
    (by norm_num) (by norm_num)
  exact criticalMellinChebyshevResolventExponentialBounded_quarter_of_quadraticContactBound
    hB0 hbound

/-- First contact reaches the RH endpoint; quadratic contact, through the same CCM continuation
mechanism, yields the quarter-width zero-free law. -/
theorem suzukiTransitionCore_linear_quadratic_contact_widthClassification :
    (RiemannHypothesis ↔
      SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded) ∧
    (SuzukiTransitionCoreQuadraticContactResidualEventuallyBounded →
      XiZeroHalfPlaneBound (1 / 4)) := by
  exact ⟨
    riemannHypothesis_iff_suzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded,
    xiZeroHalfPlaneBound_quarter_of_suzukiTransitionCoreQuadraticContactResidualEventuallyBounded⟩

end GaloisForLFunctions.RHTower
