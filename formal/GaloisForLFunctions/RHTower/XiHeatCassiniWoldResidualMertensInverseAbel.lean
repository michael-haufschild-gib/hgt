import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelTerminalClassification
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound
import GaloisForLFunctions.RHTower.CCM.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSquareEnergyWidthCollision

/-!
# Wold residual inverse Abel criterion

This module closes the reverse arithmetic transport from the natural-cutoff Route-T Wold
residual to RH.  Exact summation by parts sends every strict half-power residual law through
the weighted Mertens discrepancy to Chebyshev theta, the classical prime-power correction
then reaches the zero-width Chebyshev error spectrum, and the existing square-aperture
endpoint recovers RH.

No mesh-energy, zero-location, or asymptotic hypothesis enters the reverse implication.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact inverse Abel identity recovering `theta(N)` from the weighted Mertens primitive. -/
theorem chebyshevTheta_nat_eq_mertensA_inverseAbel (N : ℕ) :
    Chebyshev.theta (N : ℝ) =
      (N : ℝ) * Sieve.mertensA N -
        ∑ k ∈ Finset.range N, Sieve.mertensA k := by
  have habel := Finset.sum_range_by_parts
    (fun k : ℕ => (k : ℝ)) Sieve.primeLogWeight (N + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at habel
  have hpartial : ∀ k : ℕ,
      ∑ i ∈ Finset.range (k + 1), Sieve.primeLogWeight i =
        Sieve.mertensA k := Sieve.sum_range_primeLogWeight
  simp_rw [hpartial] at habel
  have hdiff : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by
    intro k
    push_cast
    ring
  simp_rw [hdiff, one_mul] at habel
  rw [← habel]
  rw [← Sieve.sum_Icc_primeLogCoeff (N : ℝ)]
  simp only [Nat.floor_natCast, Sieve.Icc_zero_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  unfold Sieve.primeLogCoeff Sieve.primeLogWeight
  split_ifs with hp
  · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp
  · ring

/-- Stirling controls the elementary logarithmic main term left by inverse Abel summation. -/
theorem abs_inverseAbel_log_main_le (N : ℕ) (hN : 1 ≤ N) :
    |(N : ℝ) * Real.log N -
        (∑ k ∈ Finset.range N, Real.log k) - (N : ℝ)| ≤
      Real.log N + 2 := by
  have hdrop :
      ∑ k ∈ Finset.Icc 0 N, Real.log (k : ℝ) =
        ∑ k ∈ Finset.Icc 1 N, Real.log (k : ℝ) := by
    symm
    apply Finset.sum_subset
    · exact Finset.Icc_subset_Icc (by omega) le_rfl
    · intro k hk0 hk1
      simp only [Finset.mem_Icc] at hk0 hk1
      have hk : k = 0 := by omega
      subst k
      simp
  have hsum :
      ∑ k ∈ Finset.range N, Real.log (k : ℝ) =
        (∑ k ∈ Finset.Icc 1 N, Real.log (k : ℝ)) - Real.log N := by
    calc
      ∑ k ∈ Finset.range N, Real.log (k : ℝ) =
          (∑ k ∈ Finset.range (N + 1), Real.log (k : ℝ)) -
            Real.log N := by rw [Finset.sum_range_succ]; ring
      _ = (∑ k ∈ Finset.Icc 0 N, Real.log (k : ℝ)) -
            Real.log N := by rw [Sieve.Icc_zero_eq_range]
      _ = _ := by rw [hdrop]
  let D : ℝ := (N : ℝ) * Real.log N -
    (∑ k ∈ Finset.range N, Real.log (k : ℝ)) - (N : ℝ)
  have hStirLower := stirling_le_sum_log N hN
  have hStirUpper := sum_log_le_stirling N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hlogstep : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / (N : ℝ) := by
    calc
      Real.log ((N : ℝ) + 1) - Real.log N =
          Real.log (((N : ℝ) + 1) / (N : ℝ)) := by
        rw [Real.log_div hN1pos.ne' hNpos.ne']
      _ ≤ ((N : ℝ) + 1) / (N : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hN1pos hNpos)
      _ = 1 / (N : ℝ) := by field_simp; ring
  have hmul := mul_le_mul_of_nonneg_left hlogstep
    (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)
  have hratio : ((N : ℝ) + 1) * (1 / (N : ℝ)) ≤ 2 := by
    rw [one_div, ← div_eq_mul_inv, div_le_iff₀ hNpos]
    linarith
  have hDlower : -2 ≤ D := by
    dsimp only [D]
    rw [hsum]
    have hneg : -2 ≤
        ((N : ℝ) + 1) *
          (Real.log N - Real.log ((N : ℝ) + 1)) := by
      nlinarith [hmul, hratio]
    nlinarith
  have hDupper : D ≤ Real.log N + 2 := by
    dsimp only [D]
    rw [hsum]
    linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  dsimp only [D] at hDlower hDupper ⊢
  rw [abs_le]
  constructor
  · linarith
  · exact hDupper

/-- A power-saving weighted Mertens remainder forces the complementary `theta` power bound. -/
theorem abs_chebyshevTheta_nat_sub_le_of_mertensA_power
    {c B K : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hB : 0 ≤ B)
    (hA : ∀ N : ℕ, 2 ≤ N →
      |Sieve.mertensA N - Real.log N - K| ≤ B * (N : ℝ) ^ (-c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      |Chebyshev.theta (N : ℝ) - (N : ℝ)| ≤
        C * (N : ℝ) ^ (1 - c) := by
  let E : ℕ → ℝ := fun N => Sieve.mertensA N - Real.log N - K
  let C : ℝ := 4 + 1 / (1 - c) + B + B / (1 - c) + 2 * |K|
  have hcGap : 0 < 1 - c := by linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := hN.trans' (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hN1
  have hNbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpowPos : 0 < (N : ℝ) ^ (1 - c) := Real.rpow_pos_of_pos hNpos _
  have hpowOne : 1 ≤ (N : ℝ) ^ (1 - c) := by
    calc
      1 = (1 : ℝ) ^ (1 - c) := (Real.one_rpow _).symm
      _ ≤ (N : ℝ) ^ (1 - c) :=
        Real.rpow_le_rpow zero_le_one hNbase hcGap.le
  have hEN := hA N hN
  have hNEN : (N : ℝ) * |E N| ≤ B * (N : ℝ) ^ (1 - c) := by
    dsimp only [E]
    calc
      (N : ℝ) * |Sieve.mertensA N - Real.log N - K| ≤
          (N : ℝ) * (B * (N : ℝ) ^ (-c)) :=
        mul_le_mul_of_nonneg_left hEN hNpos.le
      _ = B * (N : ℝ) ^ (1 - c) := by
        calc
          (N : ℝ) * (B * (N : ℝ) ^ (-c)) =
              B * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-c)) := by
            rw [Real.rpow_one]
            ring
          _ = B * (N : ℝ) ^ (1 + -c) := by rw [Real.rpow_add hNpos]
          _ = B * (N : ℝ) ^ (1 - c) := by ring_nf
  have hdecomp : 2 + (N - 2) = N := by omega
  have hEsplit :
      ∑ k ∈ Finset.range N, |E k| =
        |E 0| + |E 1| + ∑ j ∈ Finset.range (N - 2), |E (j + 2)| := by
    conv_lhs => rw [← hdecomp, Finset.sum_range_add]
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  have htailA :
      ∑ j ∈ Finset.range (N - 2), |E (j + 2)| ≤
        ∑ j ∈ Finset.range (N - 2), B * ((j : ℝ) + 1) ^ (-c) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj2 : 2 ≤ j + 2 := by omega
    have hEj := hA (j + 2) hj2
    have hmono : (((j : ℝ) + 2) : ℝ) ^ (-c) ≤
        ((j : ℝ) + 1) ^ (-c) := by
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    dsimp only [E]
    calc
      |Sieve.mertensA (j + 2) - Real.log ((j + 2 : ℕ) : ℝ) - K| ≤
          B * ((j + 2 : ℕ) : ℝ) ^ (-c) := hEj
      _ ≤ B * ((j : ℝ) + 1) ^ (-c) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (mul_le_mul_of_nonneg_left hmono hB)
  have hpower := HTGeometry.sum_rpow_sub_one_le hcGap (by linarith) (N - 2)
  have htail :
      ∑ j ∈ Finset.range (N - 2), |E (j + 2)| ≤
        B * ((N : ℝ) ^ (1 - c) / (1 - c)) := by
    calc
      ∑ j ∈ Finset.range (N - 2), |E (j + 2)| ≤
          ∑ j ∈ Finset.range (N - 2), B * ((j : ℝ) + 1) ^ (-c) := htailA
      _ = B * ∑ j ∈ Finset.range (N - 2),
          ((j : ℝ) + 1) ^ ((1 - c) - 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        ring
      _ ≤ B * (((N - 2 : ℕ) : ℝ) ^ (1 - c) / (1 - c)) :=
        mul_le_mul_of_nonneg_left hpower hB
      _ ≤ B * ((N : ℝ) ^ (1 - c) / (1 - c)) := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply div_le_div_of_nonneg_right _ hcGap.le
        apply Real.rpow_le_rpow (by positivity)
        · exact_mod_cast Nat.sub_le N 2
        · exact hcGap.le
  have hE01 : |E 0| + |E 1| = 2 * |K| := by
    simp [E, Sieve.mertensA]
    ring
  have hEsum :
      ∑ k ∈ Finset.range N, |E k| ≤
        (B / (1 - c) + 2 * |K|) * (N : ℝ) ^ (1 - c) := by
    rw [hEsplit, hE01]
    calc
      2 * |K| + ∑ j ∈ Finset.range (N - 2), |E (j + 2)| ≤
          2 * |K| + B * ((N : ℝ) ^ (1 - c) / (1 - c)) :=
        add_le_add le_rfl htail
      _ ≤ (B / (1 - c) + 2 * |K|) * (N : ℝ) ^ (1 - c) := by
        have hK : 2 * |K| ≤ 2 * |K| * (N : ℝ) ^ (1 - c) := by
          calc
            2 * |K| = 2 * |K| * 1 := by ring
            _ ≤ 2 * |K| * (N : ℝ) ^ (1 - c) :=
              mul_le_mul_of_nonneg_left hpowOne (by positivity)
        have hdiv : B * ((N : ℝ) ^ (1 - c) / (1 - c)) =
            (B / (1 - c)) * (N : ℝ) ^ (1 - c) := by
          field_simp
        rw [hdiv]
        linarith
  have hmain := abs_inverseAbel_log_main_le N hN1
  have hlog := Mertens.log_le_rpow hNpos hcGap
  have hmain' :
      |(N : ℝ) * Real.log N -
          (∑ k ∈ Finset.range N, Real.log k) - (N : ℝ)| ≤
        (1 / (1 - c) + 2) * (N : ℝ) ^ (1 - c) := by
    calc
      |(N : ℝ) * Real.log N -
          (∑ k ∈ Finset.range N, Real.log k) - (N : ℝ)| ≤
          Real.log N + 2 := hmain
      _ ≤ (1 / (1 - c)) * (N : ℝ) ^ (1 - c) +
          2 * (N : ℝ) ^ (1 - c) := by
        exact add_le_add hlog (by nlinarith [hpowOne])
      _ = (1 / (1 - c) + 2) * (N : ℝ) ^ (1 - c) := by ring
  rw [chebyshevTheta_nat_eq_mertensA_inverseAbel]
  have hidentity :
      (N : ℝ) * Sieve.mertensA N -
          (∑ k ∈ Finset.range N, Sieve.mertensA k) - (N : ℝ) =
        ((N : ℝ) * Real.log N -
          (∑ k ∈ Finset.range N, Real.log k) - (N : ℝ)) +
        ((N : ℝ) * E N - ∑ k ∈ Finset.range N, E k) := by
    dsimp only [E]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
    ring
  rw [hidentity]
  calc
    |((N : ℝ) * Real.log N -
        (∑ k ∈ Finset.range N, Real.log k) - (N : ℝ)) +
      ((N : ℝ) * E N - ∑ k ∈ Finset.range N, E k)| ≤
        |(N : ℝ) * Real.log N -
          (∑ k ∈ Finset.range N, Real.log k) - (N : ℝ)| +
        ((N : ℝ) * |E N| + ∑ k ∈ Finset.range N, |E k|) := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      calc
        |(N : ℝ) * E N - ∑ k ∈ Finset.range N, E k| ≤
            |(N : ℝ) * E N| + |∑ k ∈ Finset.range N, E k| := abs_sub _ _
        _ ≤ (N : ℝ) * |E N| + ∑ k ∈ Finset.range N, |E k| := by
          rw [abs_mul, abs_of_nonneg hNpos.le]
          exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (1 / (1 - c) + 2) * (N : ℝ) ^ (1 - c) +
        (B * (N : ℝ) ^ (1 - c) +
          (B / (1 - c) + 2 * |K|) * (N : ℝ) ^ (1 - c)) :=
      add_le_add hmain' (add_le_add hNEN hEsum)
    _ ≤ C * (N : ℝ) ^ (1 - c) := by
      dsimp only [C]
      nlinarith [hpowPos]


/-- Natural Wold residual decay recovers the centered weighted Mertens decay at the same rate. -/
theorem exists_mertensA_power_rate_of_woldNatResidual_power_rate
    {eps : ℝ} (heps0 : 0 < eps)
    (hWold : ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(1 / 2 - eps))) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| ≤
        D * (N : ℝ) ^ (-(1 / 2 - eps)) := by
  obtain ⟨B, hB, hWoldRate⟩ := hWold
  let T : ℝ := 3 * (1 / (1 / 2 + eps) + 1)
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨B + T, by positivity, ?_⟩
  filter_upwards [hWoldRate,
    eventually_woldNatTraceCorrection_tail_le_power heps0] with N hRN htraceN
  have htrace0 : 0 ≤
      xiHeatCassiniWoldNatTraceCorrectionMass -
        xiHeatCassiniWoldNatTraceCorrectionSum N :=
    sub_nonneg.mpr (xiHeatCassiniWoldNatTraceCorrectionSum_le_mass N)
  have hsplit : xiHeatCassiniWoldNatResidualLogDiscrepancy N =
      (Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant) +
        (xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N) := by
    rw [xiHeatCassiniWoldNatResidualLogDiscrepancy,
      xiHeatCassiniWoldLogHolonomyConstant,
      ← mertensPrimeWeightSum_eq_sieve_mertensA,
      mertensPrimeWeightSum_eq_wold_add_traceCorrection]
    ring
  have hMertensSplit :
      Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant =
        xiHeatCassiniWoldNatResidualLogDiscrepancy N -
          (xiHeatCassiniWoldNatTraceCorrectionMass -
            xiHeatCassiniWoldNatTraceCorrectionSum N) := by
    rw [hsplit]
    ring
  rw [hMertensSplit]
  calc
    |xiHeatCassiniWoldNatResidualLogDiscrepancy N -
        (xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N)| ≤
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| +
        |xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N| := abs_sub _ _
    _ = |xiHeatCassiniWoldNatResidualLogDiscrepancy N| +
        (xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N) := by
      rw [abs_of_nonneg htrace0]
    _ ≤ B * (N : ℝ) ^ (-(1 / 2 - eps)) +
        T * (N : ℝ) ^ (-(1 / 2 - eps)) :=
      add_le_add hRN (by simpa only [T] using htraceN)
    _ = (B + T) * (N : ℝ) ^ (-(1 / 2 - eps)) := by ring

/-- Absorb a finite prefix into the constant of an eventual weighted Mertens power bound. -/
theorem exists_global_mertensA_power_bound_of_eventually
    {c B K : ℝ} (hB : 0 < B)
    (hA : ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - K| ≤ B * (N : ℝ) ^ (-c)) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N →
      |Sieve.mertensA N - Real.log N - K| ≤ D * (N : ℝ) ^ (-c) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hA
  let E : ℕ → ℝ := fun N => Sieve.mertensA N - Real.log N - K
  let S : ℝ := ∑ k ∈ Finset.range N₀, |E k| * (k : ℝ) ^ c
  let D : ℝ := B + S + 1
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hD : 0 < D := by dsimp only [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hpowNeg0 : 0 ≤ (N : ℝ) ^ (-c) := Real.rpow_nonneg hNpos.le _
  rcases le_or_gt N₀ N with htail | hprefix
  · have hb := hN₀ N htail
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) hpowNeg0)
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.2 hprefix
    have hscaled : |E N| * (N : ℝ) ^ c ≤ S := by
      dsimp only [S]
      exact Finset.single_le_sum
        (s := Finset.range N₀) (f := fun k => |E k| * (k : ℝ) ^ c)
        (fun k _ => by positivity) hmem
    have hcancel : (N : ℝ) ^ c * (N : ℝ) ^ (-c) = 1 := by
      rw [← Real.rpow_add hNpos]
      simp
    dsimp only [E] at hscaled ⊢
    calc
      |Sieve.mertensA N - Real.log N - K| =
          (|Sieve.mertensA N - Real.log N - K| * (N : ℝ) ^ c) *
            (N : ℝ) ^ (-c) := by rw [mul_assoc, hcancel, mul_one]
      _ ≤ S * (N : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_right hscaled hpowNeg0
      _ ≤ D * (N : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) hpowNeg0

/-- Reverse arithmetic transport: Wold residual half-power decay implies a `theta` bound. -/
theorem exists_chebyshevTheta_nat_power_bound_of_woldNatResidual
    {eps : ℝ} (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2)
    (hWold : ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(1 / 2 - eps))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      |Chebyshev.theta (N : ℝ) - (N : ℝ)| ≤
        C * (N : ℝ) ^ (1 / 2 + eps) := by
  obtain ⟨B, hB, hMertens⟩ :=
    exists_mertensA_power_rate_of_woldNatResidual_power_rate
      heps0 hWold
  obtain ⟨D, hD, hMertensGlobal⟩ :=
    exists_global_mertensA_power_bound_of_eventually hB hMertens
  obtain ⟨C, hC, htheta⟩ :=
    abs_chebyshevTheta_nat_sub_le_of_mertensA_power
      (c := 1 / 2 - eps) (B := D)
      (K := xiHeatCassiniMertensLogConstant)
      (by linarith) (by linarith) hD.le hMertensGlobal
  refine ⟨C, hC, ?_⟩
  intro N hN
  simpa only [show (1 : ℝ) - (1 / 2 - eps) = 1 / 2 + eps by ring] using
    htheta N hN

/-- Extend a natural-cutoff `theta` power bound to the real Chebyshev step function. -/
theorem exists_chebyshevTheta_real_power_bound_of_nat
    {q C : ℝ} (hq0 : 0 < q) (hC : 0 < C)
    (hNat : ∀ N : ℕ, 2 ≤ N →
      |Chebyshev.theta (N : ℝ) - (N : ℝ)| ≤ C * (N : ℝ) ^ q) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      |Chebyshev.theta x - x| ≤ D * x ^ q := by
  refine ⟨C + 2, by positivity, ?_⟩
  intro x hx
  have hx0 : (0 : ℝ) < x := by linarith
  let N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff x |>.2 hx
  have hNle : ((N : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxlt : x < ((N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hthetaStep : Chebyshev.theta x = Chebyshev.theta (N : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
    simp only [N, Nat.floor_natCast]
  have hpowOne : (1 : ℝ) ≤ x ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx hq0.le
  rcases eq_or_lt_of_le hN1 with hNOne | hN2
  · have hNEq : N = 1 := hNOne.symm
    have hthetaOne : Chebyshev.theta (1 : ℝ) = 0 := by
      rw [Chebyshev.theta_eq_sum_Icc]
      simp only [Nat.floor_one]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp2 := hp.2.two_le
      simp only [Finset.mem_Icc] at hp
      omega
    have hthetaN : Chebyshev.theta (N : ℝ) = 0 := by
      rw [hNEq]
      simpa only [Nat.cast_one] using hthetaOne
    rw [hthetaStep, hthetaN, zero_sub, abs_neg, abs_of_pos hx0]
    have hxTwo : x < 2 := by
      rw [hNEq] at hxlt
      norm_num at hxlt ⊢
      exact hxlt
    nlinarith [hpowOne, hC]
  · have hN2' : 2 ≤ N := by omega
    have hb := hNat N hN2'
    have hN0 : (0 : ℝ) ≤ (N : ℕ) := by positivity
    have hpowMono : ((N : ℕ) : ℝ) ^ q ≤ x ^ q :=
      Real.rpow_le_rpow hN0 hNle hq0.le
    have hgap : |((N : ℕ) : ℝ) - x| ≤ 1 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    have htri : |Chebyshev.theta x - x| ≤
        |Chebyshev.theta (N : ℝ) - (N : ℝ)| + |((N : ℕ) : ℝ) - x| := by
      rw [hthetaStep]
      exact abs_sub_le _ _ _
    calc
      |Chebyshev.theta x - x| ≤
          |Chebyshev.theta (N : ℝ) - (N : ℝ)| + |((N : ℕ) : ℝ) - x| := htri
      _ ≤ C * (N : ℝ) ^ q + 1 := add_le_add hb hgap
      _ ≤ C * x ^ q + 2 * x ^ q := by
        have hCmono := mul_le_mul_of_nonneg_left hpowMono hC.le
        nlinarith [hpowOne]
      _ = (C + 2) * x ^ q := by ring

/-- The prime-power correction transports a `theta` power bound to `psi` at the same exponent. -/
theorem exists_chebyshevPsiReal_power_bound_of_theta
    {eta C : ℝ} (heta0 : 0 < eta) (hC : 0 < C)
    (htheta : ∀ x : ℝ, 1 ≤ x →
      |Chebyshev.theta x - x| ≤ C * x ^ (1 / 2 + eta)) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      |chebyshevPsiReal x - x| ≤ D * x ^ (1 / 2 + eta) := by
  refine ⟨C + 2 / eta, by positivity, ?_⟩
  intro x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog := Mertens.log_le_rpow hx0 heta0
  have hprimePower : 2 * Real.sqrt x * Real.log x ≤
      (2 / eta) * x ^ (1 / 2 + eta) := by
    calc
      2 * Real.sqrt x * Real.log x ≤
          2 * Real.sqrt x * ((1 / eta) * x ^ eta) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (2 / eta) * (x ^ (1 / 2 : ℝ) * x ^ eta) := by
        rw [Real.sqrt_eq_rpow]
        ring
      _ = (2 / eta) * x ^ ((1 / 2 : ℝ) + eta) := by
        rw [Real.rpow_add hx0]
  have hpsiTheta := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  have hthetaX := htheta x hx
  have htri : |Chebyshev.psi x - x| ≤
      |Chebyshev.psi x - Chebyshev.theta x| +
        |Chebyshev.theta x - x| := abs_sub_le _ _ _
  rw [chebyshevPsiReal_eq_psi]
  calc
    |Chebyshev.psi x - x| ≤
        |Chebyshev.psi x - Chebyshev.theta x| +
          |Chebyshev.theta x - x| := htri
    _ ≤ 2 * Real.sqrt x * Real.log x +
        C * x ^ (1 / 2 + eta) := add_le_add hpsiTheta hthetaX
    _ ≤ (2 / eta) * x ^ (1 / 2 + eta) +
        C * x ^ (1 / 2 + eta) := add_le_add hprimePower le_rfl
    _ = (C + 2 / eta) * x ^ (1 / 2 + eta) := by ring

/-- Every strict half-power rate for the centered natural-cutoff Wold primitive. -/
def WoldNatResidualAllStrictHalfPowerRate : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 2 →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(1 / 2 - eps))

/-- All strict Wold half-power rates force the zero-width Chebyshev source spectrum. -/
theorem chebyshevErrorPowerSpectrum_zero_of_woldNatResidualAllStrictHalfPowerRate
    (hWold : WoldNatResidualAllStrictHalfPowerRate) :
    ChebyshevErrorPowerSpectrum 0 := by
  intro epsilon hepsilon
  let eta : ℝ := min (epsilon / 2) (1 / 4)
  have heta0 : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by linarith) (by norm_num)
  have hetaHalf : eta < 1 / 2 := by
    exact lt_of_le_of_lt (by dsimp only [eta]; exact min_le_right _ _)
      (by norm_num)
  have hetaEpsilon : eta ≤ epsilon := by
    have hle : eta ≤ epsilon / 2 := by
      dsimp only [eta]
      exact min_le_left _ _
    linarith
  obtain ⟨B, hB, hrate⟩ := hWold eta heta0 hetaHalf
  obtain ⟨CthetaNat, hCthetaNat, hthetaNat⟩ :=
    exists_chebyshevTheta_nat_power_bound_of_woldNatResidual
      heta0 hetaHalf ⟨B, hB, hrate⟩
  obtain ⟨Ctheta, hCtheta, htheta⟩ :=
    exists_chebyshevTheta_real_power_bound_of_nat
      (q := 1 / 2 + eta) (by linarith) hCthetaNat hthetaNat
  obtain ⟨Cpsi, hCpsi, hpsi⟩ :=
    exists_chebyshevPsiReal_power_bound_of_theta heta0 hCtheta htheta
  refine ⟨Cpsi, hCpsi.le, ?_⟩
  intro x hx
  rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub]
  have hb := hpsi x hx
  have hpow : x ^ (1 / 2 + eta) ≤ x ^ (1 / 2 + 0 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  exact hb.trans (mul_le_mul_of_nonneg_left hpow hCpsi.le)

/-- Unconditional Route-T classification: natural Wold strict-half decay is equivalent to RH. -/
theorem riemannHypothesis_iff_woldNatResidualAllStrictHalfPowerRate :
    RiemannHypothesis ↔ WoldNatResidualAllStrictHalfPowerRate := by
  constructor
  · intro hRH eps heps0 hepsHalf
    exact exists_woldNatResidual_power_rate_of_riemannHypothesis
      hRH heps0 hepsHalf
  · intro hWold
    exact riemannHypothesis_of_chebyshevErrorPowerSpectrum_zero
      (chebyshevErrorPowerSpectrum_zero_of_woldNatResidualAllStrictHalfPowerRate hWold)

end
end RHTower
