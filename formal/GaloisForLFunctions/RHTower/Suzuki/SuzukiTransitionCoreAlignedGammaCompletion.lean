import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreCompletedXiResidueFission
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyReporterSecantPrimeChargeBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWardUnconditionalMassEscape
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelSummation
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Globally aligned Gamma completion of the Suzuki transition core

The positive transition core is a growing-rank atomic Gram, while RH controls the completed
atomic-minus-regular-screw amplitude.  This module proves the missing condition-number bridge.
Chebyshev's unconditional upper bound and discrete Abel summation remove the logarithmic loss:
the critical Mellin prefix is at most a constant times `sqrt N`.  The reporter Gram bound then
gives a linear upper bound for the transition core.  Conversely, the corpus dyadic PNT lower bound
makes the coherent outgoing prime charge at least a constant times `sqrt N`.  Therefore

`A_N^(2 : ℕ) <= C_N <= K A_N^(2 : ℕ)`

eventually, where `A_N` is the coherent atomic amplitude and `C_N` is the positive transition
core.

The globally aligned completion distributes the regular-screw amplitude in the exact atomic
Cartan direction before squaring.  Its energy is

`C_N * ((A_N - R_N) / A_N)^(2 : ℕ)`.

The two-sided condition-number law proves that eventual boundedness of this growing-rank completed
energy is equivalent to boundedness of the completed Suzuki Green amplitude, hence equivalent to
RH.  All theorems are unconditional; the equivalence identifies the remaining producer as an
independent completed-source budget for this literal aligned energy.
-/

open Filter Set
open scoped BigOperators Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower ArithmeticFunction

noncomputable section

def suzukiCriticalMellinWeightPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, criticalMellinAtomWeight n

private theorem sum_range_mul_invSqrt_sub_succ (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)) =
      (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) -
        (N : ℝ) * (Real.sqrt (N : ℝ))⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      push_cast
      ring

private theorem deningerPartialSum_vonMangoldt_eq (N : ℕ) :
    deningerPartialSum (fun n => vonMangoldt n) N =
      ∑ n ∈ Finset.Icc 1 N, vonMangoldt n := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [deningerPartialSum, hset, Finset.sum_insert (by simp)]
  simp

private theorem deningerPartialSum_vonMangoldt_le (N : ℕ) :
    deningerPartialSum (fun n => vonMangoldt n) N ≤
      (Real.log 4 + 4) * N := by
  rw [deningerPartialSum_vonMangoldt_eq]
  exact Mertens.sum_vonMangoldt_Icc_le N

private theorem invSqrt_sub_succ_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hleR : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  rw [sub_nonneg]
  simpa only [one_div] using one_div_le_one_div_of_le
    (Real.sqrt_pos.2 hnR)
    (Real.sqrt_le_sqrt hleR)

theorem suzukiCriticalMellinWeightPrefix_le (N : ℕ) :
    suzukiCriticalMellinWeightPrefix N ≤
      3 * (Real.log 4 + 4) * Real.sqrt N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [suzukiCriticalMellinWeightPrefix]
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hAbel := deningerAbelSummation
    (fun n => vonMangoldt n) (fun n => (Real.sqrt (n : ℝ))⁻¹) N
  have hleft :
      (∑ n ∈ Finset.range (N + 1), vonMangoldt n * (Real.sqrt (n : ℝ))⁻¹) =
        suzukiCriticalMellinWeightPrefix N := by
    calc
      _ = ∑ n ∈ Finset.range (N + 1), criticalMellinAtomWeight n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [criticalMellinAtomWeight_eq_vonMangoldt_div_sqrt]
        ring
      _ = ∑ n ∈ Finset.Icc 2 N, criticalMellinAtomWeight n := by
        symm
        apply Finset.sum_subset
        · intro n hn
          simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
          omega
        · intro n hn hnot
          simp only [Finset.mem_range] at hn
          have hnle : n ≤ 1 := by
            simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
            omega
          interval_cases n <;> simp [criticalMellinAtomWeight]
      _ = _ := rfl
  rw [hleft] at hAbel
  have hboundary :
      deningerPartialSum (fun n => vonMangoldt n) N * (Real.sqrt (N : ℝ))⁻¹ ≤
        (Real.log 4 + 4) * Real.sqrt N := by
    calc
      _ ≤ ((Real.log 4 + 4) * N) * (Real.sqrt N)⁻¹ :=
        mul_le_mul_of_nonneg_right (deningerPartialSum_vonMangoldt_le N)
          (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = (Real.log 4 + 4) * Real.sqrt N := by
        field_simp [hsqrtN.ne']
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
  have hsum :
      (∑ n ∈ Finset.range N,
        deningerPartialSum (fun k => vonMangoldt k) n *
          ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)) ≤
        2 * (Real.log 4 + 4) * Real.sqrt N := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((Real.log 4 + 4) * n) *
            ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        rcases Nat.eq_zero_or_pos n with rfl | hnpos
        · simp
        exact mul_le_mul_of_nonneg_right
          (deningerPartialSum_vonMangoldt_le n)
          (invSqrt_sub_succ_nonneg hnpos)
      _ = (Real.log 4 + 4) *
          ((∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) -
            (N : ℝ) * (Real.sqrt (N : ℝ))⁻¹) := by
        calc
          _ = (Real.log 4 + 4) *
              (∑ n ∈ Finset.range N,
                (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹ -
                  (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = _ := by rw [sum_range_mul_invSqrt_sub_succ]
      _ ≤ (Real.log 4 + 4) *
          (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) := by
        have hC : 0 ≤ Real.log 4 + 4 := by positivity
        exact mul_le_mul_of_nonneg_left (sub_le_self _ (mul_nonneg (by positivity)
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))) hC
      _ ≤ 2 * (Real.log 4 + 4) * Real.sqrt N := by
        have hC : 0 ≤ Real.log 4 + 4 := by positivity
        have h := _root_.RHTower.sum_one_div_sqrt_le N
        simp only [one_div] at h
        nlinarith
  rw [hAbel]
  calc
    _ ≤ (Real.log 4 + 4) * Real.sqrt N +
        2 * (Real.log 4 + 4) * Real.sqrt N := by
          simpa only [Nat.cast_add, Nat.cast_one] using add_le_add hboundary hsum
    _ = 3 * (Real.log 4 + 4) * Real.sqrt N := by ring

theorem suzukiNaturalApertureTransitionCoreCauchyEnergy_le_prefix_sq (N : ℕ) :
    suzukiNaturalApertureTransitionCoreCauchyEnergy N ≤
      2 * suzukiCriticalMellinWeightPrefix N ^ (2 : ℕ) := by
  classical
  rw [suzukiNaturalApertureTransitionCoreCauchyEnergy]
  calc
    (∑ ij ∈ (suzukiNaturalAperturePairSet N).filter
        (fun ij => ¬ suzukiNaturalApertureTransitionSeparated N ij),
        suzukiNaturalApertureCauchyPairTerm N ij) ≤
      ∑ ij ∈ (suzukiNaturalAperturePairSet N).filter
        (fun ij => ¬ suzukiNaturalApertureTransitionSeparated N ij),
        2 * ((suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
          (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro ij hij
      have hwi : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) :=
        (suzukiNaturalAperturePrimeWeight N ij.1).property
      have hwj : 0 ≤ (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
        (suzukiNaturalAperturePrimeWeight N ij.2).property
      have hgram := suzukiReporterSecantCauchyGram_le_two
        (suzukiNaturalApertureLag N ij.1) (suzukiNaturalApertureLag N ij.2)
      rw [suzukiNaturalApertureCauchyPairTerm]
      calc
        _ ≤ (suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) * 2 *
            (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgram hwi) hwj
        _ = _ := by ring
    _ ≤ ∑ ij ∈ suzukiNaturalAperturePairSet N,
        2 * ((suzukiNaturalAperturePrimeWeight N ij.1 : ℝ) *
          (suzukiNaturalAperturePrimeWeight N ij.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro ij hij hnot
        positivity
    _ = 2 * suzukiCriticalMellinWeightPrefix N ^ (2 : ℕ) := by
      rw [suzukiNaturalAperturePairSet, Finset.sum_product,
        suzukiCriticalMellinWeightPrefix]
      change (∑ i ∈ Finset.Icc 2 N, ∑ j ∈ Finset.Icc 2 N,
        2 * (criticalMellinAtomWeight i * criticalMellinAtomWeight j)) = _
      calc
        _ = 2 * (∑ i ∈ Finset.Icc 2 N, criticalMellinAtomWeight i) *
            (∑ j ∈ Finset.Icc 2 N, criticalMellinAtomWeight j) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by ring

theorem suzukiNaturalApertureTransitionCoreCauchyEnergy_le_linear (N : ℕ) :
    suzukiNaturalApertureTransitionCoreCauchyEnergy N ≤
      18 * (Real.log 4 + 4) ^ (2 : ℕ) * N := by
  have hp := suzukiCriticalMellinWeightPrefix_le N
  have hprefix : 0 ≤ suzukiCriticalMellinWeightPrefix N := by
    rw [suzukiCriticalMellinWeightPrefix]
    exact Finset.sum_nonneg fun n hn => criticalMellinAtomWeight_nonneg n
  have hroot : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (N : ℝ) ^ (2 : ℕ) = N := Real.sq_sqrt (by positivity)
  calc
    _ ≤ 2 * suzukiCriticalMellinWeightPrefix N ^ (2 : ℕ) :=
      suzukiNaturalApertureTransitionCoreCauchyEnergy_le_prefix_sq N
    _ ≤ 2 * (3 * (Real.log 4 + 4) * Real.sqrt N) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprefix hp 2) (by norm_num)
    _ = 18 * (Real.log 4 + 4) ^ (2 : ℕ) * Real.sqrt N ^ (2 : ℕ) := by ring
    _ = _ := by rw [hsq]

theorem eventually_unitRieszCoherentPrimeOutgoingCharge_sq_ge_linear :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / 104976 ≤ unitRieszCoherentPrimeOutgoingCharge N ^ (2 : ℕ) := by
  have hdiv : Tendsto (fun N : ℕ => N / 9) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hcast : Tendsto (fun N : ℕ => ((N / 9 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdiv
  have hdyadic := hcast.eventually _root_.RHTower.eventually_dyadicSqrtVonMangoldtMass_ge
  filter_upwards [hdyadic, eventually_ge_atTop (18 : ℕ)] with N hmass hN
  have hcharge := dyadicSqrtVonMangoldtMass_nat_div_nine_div_six_le_outgoingCharge hN
  have hA : Real.sqrt ((N / 9 : ℕ) : ℝ) / 18 ≤
      unitRieszCoherentPrimeOutgoingCharge N := by
    calc
      _ ≤ _root_.RHTower.dyadicSqrtVonMangoldtMass ((N / 9 : ℕ) : ℝ) / 6 := by
        linarith
      _ ≤ _ := hcharge
  have hNM : (N : ℝ) ≤ 18 * (N / 9 : ℕ) := by
    exact_mod_cast (show N ≤ 18 * (N / 9) by omega)
  have hrootNM : Real.sqrt (N : ℝ) ≤
      18 * Real.sqrt ((N / 9 : ℕ) : ℝ) := by
    have hmono := Real.sqrt_le_sqrt hNM
    have hmul : Real.sqrt (18 * ((N / 9 : ℕ) : ℝ)) =
        Real.sqrt 18 * Real.sqrt ((N / 9 : ℕ) : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 18)]
    rw [hmul] at hmono
    have hsqrt18 : Real.sqrt (18 : ℝ) ≤ 18 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 18),
        Real.sqrt_nonneg (18 : ℝ)]
    exact hmono.trans (mul_le_mul_of_nonneg_right hsqrt18 (Real.sqrt_nonneg _))
  have hAlinear : Real.sqrt (N : ℝ) / 324 ≤
      unitRieszCoherentPrimeOutgoingCharge N := by
    calc
      _ ≤ Real.sqrt ((N / 9 : ℕ) : ℝ) / 18 := by linarith
      _ ≤ _ := hA
  have hsqrt : Real.sqrt (N : ℝ) ^ (2 : ℕ) = N := Real.sq_sqrt (by positivity)
  have hsqle : (Real.sqrt (N : ℝ) / 324) ^ (2 : ℕ) ≤
      unitRieszCoherentPrimeOutgoingCharge N ^ (2 : ℕ) :=
    pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hAlinear 2
  calc
    (N : ℝ) / 104976 = (Real.sqrt (N : ℝ) / 324) ^ (2 : ℕ) := by
      rw [div_pow, hsqrt]
      norm_num
    _ ≤ _ := hsqle

def suzukiTransitionCoreAnchorConditionNumberBound : ℝ :=
  1889568 * (Real.log 4 + 4) ^ (2 : ℕ)

theorem eventually_suzukiTransitionCore_le_anchorConditionNumber_mul_sq :
    ∀ᶠ N : ℕ in atTop,
      suzukiNaturalApertureTransitionCoreCauchyEnergy N ≤
        suzukiTransitionCoreAnchorConditionNumberBound *
          unitRieszCoherentPrimeOutgoingCharge N ^ (2 : ℕ) := by
  filter_upwards [eventually_unitRieszCoherentPrimeOutgoingCharge_sq_ge_linear]
    with N hA
  have hcore := suzukiNaturalApertureTransitionCoreCauchyEnergy_le_linear N
  rw [suzukiTransitionCoreAnchorConditionNumberBound]
  have hC : 0 ≤ (Real.log 4 + 4) ^ (2 : ℕ) := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hA
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hC)]

def suzukiTransitionCoreAlignedGammaCompletedEnergy (N : ℕ) : ℝ :=
  if _hA : unitRieszCoherentPrimeOutgoingCharge N = 0 then 0
  else suzukiNaturalApertureTransitionCoreCauchyEnergy N *
    (suzukiNaturalApertureCompletedLowerHardyAmplitude N /
      unitRieszCoherentPrimeOutgoingCharge N) ^ (2 : ℕ)

theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_nonneg (N : ℕ) :
    0 ≤ suzukiTransitionCoreAlignedGammaCompletedEnergy N := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg
      (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N) (sq_nonneg _)

private theorem sq_mul_div_sq_cancel {A x : ℝ} (hA : A ≠ 0) :
    A ^ (2 : ℕ) * (x / A) ^ (2 : ℕ) = x ^ (2 : ℕ) := by
  field_simp [hA]

theorem suzukiCompletedAnchor_sq_le_alignedEnergy
    {N : ℕ} (hN : 2 ≤ N)
    (hA : unitRieszCoherentPrimeOutgoingCharge N ≠ 0) :
    suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) ≤
      suzukiTransitionCoreAlignedGammaCompletedEnergy N := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy, dif_neg hA]
  have hcore := unitRieszCoherentPrimeOutgoingCharge_sq_le_transitionCore hN
  have hq : 0 ≤ (suzukiNaturalApertureCompletedLowerHardyAmplitude N /
      unitRieszCoherentPrimeOutgoingCharge N) ^ (2 : ℕ) := sq_nonneg _
  calc
    _ = unitRieszCoherentPrimeOutgoingCharge N ^ (2 : ℕ) *
        (suzukiNaturalApertureCompletedLowerHardyAmplitude N /
          unitRieszCoherentPrimeOutgoingCharge N) ^ (2 : ℕ) := by
      rw [sq_mul_div_sq_cancel hA]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcore hq

theorem suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq
    {N : ℕ} (hA : unitRieszCoherentPrimeOutgoingCharge N ≠ 0)
    (hcore : suzukiNaturalApertureTransitionCoreCauchyEnergy N ≤
      suzukiTransitionCoreAnchorConditionNumberBound *
        unitRieszCoherentPrimeOutgoingCharge N ^ (2 : ℕ)) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy N ≤
      suzukiTransitionCoreAnchorConditionNumberBound *
        suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy, dif_neg hA]
  have hq : 0 ≤ (suzukiNaturalApertureCompletedLowerHardyAmplitude N /
      unitRieszCoherentPrimeOutgoingCharge N) ^ (2 : ℕ) := sq_nonneg _
  calc
    _ ≤ (suzukiTransitionCoreAnchorConditionNumberBound *
          unitRieszCoherentPrimeOutgoingCharge N ^ (2 : ℕ)) *
        (suzukiNaturalApertureCompletedLowerHardyAmplitude N /
          unitRieszCoherentPrimeOutgoingCharge N) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hcore hq
    _ = _ := by rw [mul_assoc, sq_mul_div_sq_cancel hA]

theorem eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero :
    ∀ᶠ N : ℕ in atTop, unitRieszCoherentPrimeOutgoingCharge N ≠ 0 := by
  filter_upwards [eventually_unitRieszCoherentPrimeOutgoingCharge_sq_ge_linear,
    eventually_ge_atTop (1 : ℕ)] with N hsq hN hzero
  rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at hsq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  linarith

theorem eventually_completedAnchor_sq_le_suzukiTransitionCoreAlignedEnergy :
    ∀ᶠ N : ℕ in atTop,
      suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) ≤
        suzukiTransitionCoreAlignedGammaCompletedEnergy N := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero] with N hN hA
  exact suzukiCompletedAnchor_sq_le_alignedEnergy hN hA

theorem eventually_suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq :
    ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreAlignedGammaCompletedEnergy N ≤
        suzukiTransitionCoreAnchorConditionNumberBound *
          suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) := by
  filter_upwards [eventually_suzukiTransitionCore_le_anchorConditionNumber_mul_sq,
    eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero] with N hcore hA
  exact suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq hA hcore

def SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded : Prop :=
  ∃ B : ℝ, ∀ᶠ N : ℕ in atTop,
    suzukiTransitionCoreAlignedGammaCompletedEnergy N ≤ B

theorem riemannHypothesis_iff_suzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded :
    RiemannHypothesis ↔
      SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded := by
  constructor
  · intro hRH
    obtain ⟨B, hB, hbound⟩ :=
      (riemannHypothesis_iff_suzukiNaturalCauchyCompletedAnchorBounded.mp hRH)
    refine ⟨suzukiTransitionCoreAnchorConditionNumberBound * B ^ (2 : ℕ), ?_⟩
    filter_upwards [eventually_suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq,
      eventually_ge_atTop (2 : ℕ)] with N henergy hN
    have habs : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤ B := by
      simpa [Nat.sub_add_cancel hN] using hbound (N - 2)
    have hsq : suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    exact henergy.trans (mul_le_mul_of_nonneg_left hsq (by
      rw [suzukiTransitionCoreAnchorConditionNumberBound]
      positivity))
  · rintro ⟨E, henergy⟩
    have hsquare : ∀ᶠ N : ℕ in atTop,
        suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) ≤ E := by
      filter_upwards [eventually_completedAnchor_sq_le_suzukiTransitionCoreAlignedEnergy,
        henergy] with N hlower hupper
      exact hlower.trans hupper
    rw [eventually_atTop] at hsquare
    obtain ⟨N₀, hN₀⟩ := hsquare
    let B : ℝ := |E| + 1 +
      ∑ N ∈ Finset.range N₀,
        |suzukiNaturalApertureCompletedLowerHardyAmplitude N|
    have hsum_nonneg : 0 ≤ ∑ N ∈ Finset.range N₀,
        |suzukiNaturalApertureCompletedLowerHardyAmplitude N| := by positivity
    have hB : 0 ≤ B := by
      dsimp only [B]
      positivity
    have hboundAll : ∀ N : ℕ,
        |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤ B := by
      intro N
      by_cases hlarge : N₀ ≤ N
      · have hsquareN := hN₀ N hlarge
        have habs_le_sq_add_one :
            |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
              suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) + 1 := by
          have hnonneg := abs_nonneg
            (suzukiNaturalApertureCompletedLowerHardyAmplitude N)
          rw [← sq_abs]
          nlinarith [sq_nonneg
            (|suzukiNaturalApertureCompletedLowerHardyAmplitude N| - 1 / 2)]
        calc
          _ ≤ suzukiNaturalApertureCompletedLowerHardyAmplitude N ^ (2 : ℕ) + 1 :=
            habs_le_sq_add_one
          _ ≤ E + 1 := by linarith
          _ ≤ |E| + 1 := by linarith [le_abs_self E]
          _ ≤ B := by
            dsimp only [B]
            linarith
      · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (lt_of_not_ge hlarge)
        have hsingle : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
            ∑ n ∈ Finset.range N₀,
              |suzukiNaturalApertureCompletedLowerHardyAmplitude n| := by
          exact Finset.single_le_sum
            (fun n hn => abs_nonneg
              (suzukiNaturalApertureCompletedLowerHardyAmplitude n)) hmem
        calc
          _ ≤ ∑ n ∈ Finset.range N₀,
              |suzukiNaturalApertureCompletedLowerHardyAmplitude n| := hsingle
          _ ≤ B := by
            dsimp only [B]
            linarith [abs_nonneg E]
    apply riemannHypothesis_iff_suzukiNaturalCauchyCompletedAnchorBounded.mpr
    exact ⟨B, hB, fun N => hboundAll (N + 2)⟩

end
end GaloisForLFunctions.RHTower

