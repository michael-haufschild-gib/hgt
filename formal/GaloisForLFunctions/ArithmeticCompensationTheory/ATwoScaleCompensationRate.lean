import GaloisForLFunctions.ArithmeticCompensationTheory.TheCompensationDefectDecaysFasterThanEveryLogPower
import GaloisForLFunctions.ArithmeticCompensationTheory.TheCompensatingProjectionMovesSummablyAcrossScales

/-!
# A two-scale compensation rate

One decomposition of the damped Möbius–Ramanujan source at cutoff `P²` into its large-prime sector
`L_P` and literal complement `C_P` gives the Pythagorean compensation law
`‖L_P + C_P‖² = (1 − α_P)² ‖L_P‖² + ‖R_P‖²` (`CompensationCoordinates`). Comparing the overlapping
decompositions at two cutoffs `P²` and `Q²` (in particular the dyadic pair `P²` and `(2P)²`) on
their common head `1 ≤ N ≤ P − 1` introduces a second, compatible constraint: both complete prefixes
`S_P = L_P + C_P` and `S_Q = L_Q + C_Q` approximate the **same** cutoff-independent divisor
remainder `R_ε(N) = pmPowerDampedDivisorRemainder ε N`.

### Intended gains

1. **A power-saving two-scale cutoff transition rate on the common head:** while the single-scale
   complete head energy `‖S_P‖²` is `O(P^{1−2ε}/log^m P)`, subtracting `S_P` from `S_Q` (`Q ≥ P`,
   in particular `Q = 2P`) cancels the cutoff-independent divisor remainder `R_ε(N)` identically and
   leaves only the Ramanujan cofactor truncation tails, which decay as a **power** of `P`:
   `twoScaleCompleteShiftEnergy ε P (2P) (P − 1) ≤ C P^{1−3ε}`
   (`exists_twoScaleCompleteShiftEnergy_le_pow_saving`). Relative to the large-prime sector energy
   `‖L_P‖² ≥ c P^{1−2ε}/log² P`, the two-scale shift energy decays **polynomially** as
   `O(P^{−ε} log² P)` (`exists_twoScaleCompleteShiftEnergy_div_sectorEnergy_le_rpow`) — strictly
   stronger than any logarithmic rate — and in the upper critical band `ε > 1/3` the **absolute**
   two-scale shift energy tends to `0` at rate `P^{−(3ε−1)}`
   (`tendsto_twoScaleCompleteShiftEnergy_zero_of_one_third_lt`).
2. **Exact moving-projection connection identities (`transverseRemainder_sub_eq_connection`,
   `transverseRemainder_sub_eq_complete_sub_connection`,
   `pmTransverseRemainderSeq_sub_eq_connection`):** passing from cutoff `P²` to `Q²` moves the
   projection onto the coherent sector and changes the transverse remainder by
   `R_Q − R_P = (C_Q − C_P) + α_Q (L_Q − L_P) + (α_Q − α_P) L_P`
   `= (S_Q − S_P) − (1 − α_Q)(L_Q − L_P) + (α_Q − α_P) L_P`,
   isolating the moving-projection connection term `(α_Q − α_P) L_P` and bounding the common-head
   transverse transition energy by three explicit pieces
   (`twoScale_transverseRemainder_diff_energy_le`).
3. **An all-logarithmic-power rate and polynomial-weight dyadic summability for the coordinate
   mismatch and connection term (`exists_abs_pmCompensationAmplitude_twoScale_sub_le_log_pow`,
   `exists_abs_compensationDefect_twoScale_sub_le_log_pow`,
   `summable_mul_pow_abs_pmCompensationAmplitude_dyadic_sub`,
   `summable_mul_pow_compensationDefect_dyadic`):** the two-scale amplitude step `|α_{2P} − α_P|`,
   the uniform step `sup_{Q ≥ P} |α_Q − α_P|`, the defect step
   `|compensationDefect ε (2P) − compensationDefect ε P|`, and the relative connection energy
   `(α_{2P} − α_P)²` all decay faster than every power `log^{−m} P`, and the dyadic variations
   remain summable against every polynomial weight `k^m`.
-/

open Finset Filter Topology Complex ArithmeticFunction RHTower
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## §1. The two-scale moving-projection connection identity -/

section AbstractTwoScale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The moving-projection connection identity.** Between any two decompositions `(L₁, C₁)` and
`(L₂, C₂)`, the change in the transverse remainder `R = C + α L` splits into the complement step
`C₂ − C₁`, the current projection of the sector step `α₂ (L₂ − L₁)`, and the connection term
`(α₂ − α₁) L₁` of the moving projection. -/
theorem transverseRemainder_sub_eq_connection (L₁ C₁ L₂ C₂ : E) :
    transverseRemainder L₂ C₂ - transverseRemainder L₁ C₁ =
      (C₂ - C₁) + compensationAmplitude L₂ C₂ • (L₂ - L₁) +
        (compensationAmplitude L₂ C₂ - compensationAmplitude L₁ C₁) • L₁ := by
  simp only [transverseRemainder, smul_sub, sub_smul]
  abel

/-- **The two-scale compatibility identity.** Eliminating `C₂ − C₁ = (L₂ + C₂) − (L₁ + C₁) − (L₂ − L₁)`
expresses the transverse remainder step in terms of the complete-sum shift `(L₂ + C₂) − (L₁ + C₁)`,
the residual amplitude mismatch `1 − α₂` on the sector step `L₂ − L₁`, and the moving-projection
connection term `(α₂ − α₁) L₁`. -/
theorem transverseRemainder_sub_eq_complete_sub_connection (L₁ C₁ L₂ C₂ : E) :
    transverseRemainder L₂ C₂ - transverseRemainder L₁ C₁ =
      ((L₂ + C₂) - (L₁ + C₁)) - (1 - compensationAmplitude L₂ C₂) • (L₂ - L₁) +
        (compensationAmplitude L₂ C₂ - compensationAmplitude L₁ C₁) • L₁ := by
  simp only [transverseRemainder, sub_smul, one_smul, smul_sub]
  abel

end AbstractTwoScale

/-- The pointwise transverse remainder sequence `R_P(N) = C_P(N) + α_P L_P(N)` of the actual
damped Möbius–Ramanujan source at cutoff `P²`. -/
def pmTransverseRemainderSeq (ε : ℝ) (P N : ℕ) : ℂ :=
  pmRamanujanLargePrimeComplement ε P N +
    (pmCompensationAmplitude ε P : ℂ) * pmRamanujanLargePrimeSector ε P N

/-- At every cutoff `P ≥ 2`, the complete Ramanujan cumulative prefix `S_P(N)` decomposes pointwise
as `(1 − α_P) L_P(N) + R_P(N)`. -/
theorem pmCompletePrefix_eq_compensationSeq {P : ℕ} (hP : 2 ≤ P) (ε : ℝ) (N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N =
      ((1 - pmCompensationAmplitude ε P : ℝ) : ℂ) * pmRamanujanLargePrimeSector ε P N +
        pmTransverseRemainderSeq ε P N := by
  rw [pmTransverseRemainderSeq, pmRamanujanLargePrimeComplement_eq_sub hP]
  push_cast
  ring

/-- **Pointwise moving-projection connection identity on the actual source.** For any two cutoffs
`P, Q ≥ 2`, the transverse remainder step `R_Q(N) − R_P(N)` equals the complete-prefix cutoff shift
`S_Q(N) − S_P(N)` minus `(1 − α_Q)(L_Q(N) − L_P(N))` plus the moving-projection connection term
`(α_Q − α_P) L_P(N)`. -/
theorem pmTransverseRemainderSeq_sub_eq_connection {P Q : ℕ} (hP : 2 ≤ P) (hQ : 2 ≤ Q)
    (ε : ℝ) (N : ℕ) :
    pmTransverseRemainderSeq ε Q N - pmTransverseRemainderSeq ε P N =
      (pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
        pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N) -
      ((1 - pmCompensationAmplitude ε Q : ℝ) : ℂ) *
        (pmRamanujanLargePrimeSector ε Q N - pmRamanujanLargePrimeSector ε P N) +
      ((pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P : ℝ) : ℂ) *
        pmRamanujanLargePrimeSector ε P N := by
  rw [pmTransverseRemainderSeq, pmTransverseRemainderSeq,
    pmRamanujanLargePrimeComplement_eq_sub hP, pmRamanujanLargePrimeComplement_eq_sub hQ]
  push_cast
  ring

/-! ## §2. Power-saving cutoff shift between overlapping decompositions `P²` and `Q²` -/

/-- The pronic energy on `[1, T]` of the two-scale complete-prefix shift `S_Q − S_P` between cutoffs
`P²` and `Q²`. -/
def twoScaleCompleteShiftEnergy (ε : ℝ) (P Q T : ℕ) : ℝ :=
  ∑ N ∈ Icc 1 T,
    ‖pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
      pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N‖ ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1))

theorem twoScaleCompleteShiftEnergy_nonneg (ε : ℝ) (P Q T : ℕ) :
    0 ≤ twoScaleCompleteShiftEnergy ε P Q T :=
  sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

theorem twoScaleCompleteShiftEnergy_mono (ε : ℝ) (P Q : ℕ) {T₁ T₂ : ℕ} (h : T₁ ≤ T₂) :
    twoScaleCompleteShiftEnergy ε P Q T₁ ≤ twoScaleCompleteShiftEnergy ε P Q T₂ :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun _ _ _ => by positivity

/-- **Exact cancellation of the cutoff-independent divisor remainder between scales.** For
`1 ≤ P ≤ Q` and `N ≤ P²`, subtracting `S_P(N)` from `S_Q(N)` cancels `R_ε(N)` and leaves at most
`2 N P^{−2β} (Σ m^{−(1+ε−β)})²` for every `0 ≤ β < ε`. -/
theorem norm_twoScale_completePrefix_sub_le {ε β : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β) (hβε : β < ε)
    {P Q N : ℕ} (hP : 1 ≤ P) (hPQ : P ≤ Q) (hNP : N ≤ P ^ 2) :
    ‖pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
      pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N‖ ≤
      2 * (N : ℝ) * (P : ℝ) ^ (-2 * β) * (∑' m : ℕ, (m : ℝ) ^ (-(1 + ε - β))) ^ 2 := by
  have hQ : 1 ≤ Q := hP.trans hPQ
  have hP2 : 0 < P ^ 2 := by positivity
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hPQ2 : P ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left hPQ 2
  have hNQ : N ≤ Q ^ 2 := hNP.trans hPQ2
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h1 := norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le hε hβ hβε hQ2 hNQ
  have h2 := norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le hε hβ hβε hP2 hNP
  have hsplit : pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
      pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N =
      (pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
        pmPowerDampedDivisorRemainder ε N) -
      (pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N -
        pmPowerDampedDivisorRemainder ε N) := by ring
  have hQP : ((Q ^ 2 : ℕ) : ℝ) ^ (-β) ≤ ((P ^ 2 : ℕ) : ℝ) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hP2) (by exact_mod_cast hPQ2) (by linarith)
  have hPpow : ((P ^ 2 : ℕ) : ℝ) ^ (-β) = (P : ℝ) ^ (-2 * β) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (P : ℝ) 2, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  set C := (∑' m : ℕ, (m : ℝ) ^ (-(1 + ε - β))) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  have h1' : ‖pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
      pmPowerDampedDivisorRemainder ε N‖ ≤ (N : ℝ) * (P : ℝ) ^ (-2 * β) * C := by
    refine h1.trans ?_
    rw [← hPpow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQP (Nat.cast_nonneg N)) hC
  have h2' : ‖pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N -
      pmPowerDampedDivisorRemainder ε N‖ ≤ (N : ℝ) * (P : ℝ) ^ (-2 * β) * C := by
    rwa [hPpow] at h2
  rw [hsplit]
  calc ‖(pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
          pmPowerDampedDivisorRemainder ε N) -
        (pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N -
          pmPowerDampedDivisorRemainder ε N)‖
      ≤ ‖pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
          pmPowerDampedDivisorRemainder ε N‖ +
        ‖pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N -
          pmPowerDampedDivisorRemainder ε N‖ := norm_sub_le _ _
    _ ≤ (N : ℝ) * (P : ℝ) ^ (-2 * β) * C + (N : ℝ) * (P : ℝ) ^ (-2 * β) * C :=
        add_le_add h1' h2'
    _ = 2 * (N : ℝ) * (P : ℝ) ^ (-2 * β) * C := by ring

/-- **Two-scale shift energy bound on any common head `T ≤ P²`.** For `1 ≤ P ≤ Q` and `0 ≤ β < ε`,
`twoScaleCompleteShiftEnergy ε P Q T ≤ 4 T P^{−4β} (Σ m^{−(1+ε−β)})⁴`. -/
theorem twoScaleCompleteShiftEnergy_le_rpow {ε β : ℝ} (hε : 0 < ε) (hβ : 0 ≤ β) (hβε : β < ε)
    {P Q T : ℕ} (hP : 1 ≤ P) (hPQ : P ≤ Q) (hTP : T ≤ P ^ 2) :
    twoScaleCompleteShiftEnergy ε P Q T ≤
      4 * (T : ℝ) * (P : ℝ) ^ (-4 * β) * (∑' m : ℕ, (m : ℝ) ^ (-(1 + ε - β))) ^ 4 := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  set K : ℝ := ∑' m : ℕ, (m : ℝ) ^ (-(1 + ε - β))
  set D : ℝ := 2 * (P : ℝ) ^ (-2 * β) * K ^ 2
  have hD : 0 ≤ D := by positivity
  have hterm (N : ℕ) (hN : N ∈ Icc 1 T) :
      ‖pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
        pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N‖ ^ 2 /
          ((N : ℝ) * ((N : ℝ) + 1)) ≤ D ^ 2 := by
    have hN1 : 1 ≤ N := (mem_Icc.mp hN).1
    have hNP : N ≤ P ^ 2 := (mem_Icc.mp hN).2.trans hTP
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hb := norm_twoScale_completePrefix_sub_le hε hβ hβε hP hPQ hNP
    have hle : ‖pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
        pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N‖ ≤ D * N := by
      calc _ ≤ 2 * (N : ℝ) * (P : ℝ) ^ (-2 * β) * K ^ 2 := hb
        _ = D * N := by dsimp [D]; ring
    have hsq : ‖pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
        pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N‖ ^ 2 ≤ D ^ 2 * (N : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hle 2
      linarith [ this, show (D * (N : ℝ)) ^ 2 = D ^ 2 * (N : ℝ) ^ 2 by ring ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg D) hN0.le]
  have hpow : ((P : ℝ) ^ (-2 * β)) ^ 2 = (P : ℝ) ^ (-4 * β) := by
    rw [← Real.rpow_natCast ((P : ℝ) ^ (-2 * β)) 2, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  calc twoScaleCompleteShiftEnergy ε P Q T
      ≤ ∑ _N ∈ Icc 1 T, D ^ 2 := sum_le_sum hterm
    _ = (T : ℝ) * D ^ 2 := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = 4 * (T : ℝ) * (P : ℝ) ^ (-4 * β) * K ^ 4 := by
        dsimp [D]
        rw [mul_pow, mul_pow, hpow]
        ring

/-- **Power-saving bound on the common head `T ≤ P`.** At `β = 3ε/4`, for every `ε > 0` there is a
constant `C ≥ 0` such that for all `1 ≤ P ≤ Q`,
`twoScaleCompleteShiftEnergy ε P Q P ≤ C P^{1−3ε}`. -/
theorem exists_twoScaleCompleteShiftEnergy_le_pow_saving {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P Q : ℕ, 1 ≤ P → P ≤ Q →
      twoScaleCompleteShiftEnergy ε P Q P ≤ C * (P : ℝ) ^ (1 - 3 * ε) := by
  let β : ℝ := 3 * ε / 4
  let K : ℝ := ∑' m : ℕ, (m : ℝ) ^ (-(1 + ε - β))
  refine ⟨4 * K ^ 4, by positivity, fun P Q hP hPQ => ?_⟩
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hTP : P ≤ P ^ 2 := by nlinarith
  have hb := twoScaleCompleteShiftEnergy_le_rpow (β := β) hε (by dsimp [β]; positivity)
    (by dsimp [β]; linarith) hP hPQ hTP
  have hexp : (P : ℝ) * (P : ℝ) ^ (-4 * β) = (P : ℝ) ^ (1 - 3 * ε) := by
    calc (P : ℝ) * (P : ℝ) ^ (-4 * β)
        = (P : ℝ) ^ (1 : ℝ) * (P : ℝ) ^ (-4 * β) := by rw [Real.rpow_one]
      _ = (P : ℝ) ^ (1 + -4 * β) := (Real.rpow_add hP0 1 (-4 * β)).symm
      _ = (P : ℝ) ^ (1 - 3 * ε) := by congr 1; dsimp [β]; ring
  calc twoScaleCompleteShiftEnergy ε P Q P
      ≤ 4 * (P : ℝ) * (P : ℝ) ^ (-4 * β) * K ^ 4 := hb
    _ = 4 * K ^ 4 * ((P : ℝ) * (P : ℝ) ^ (-4 * β)) := by ring
    _ = 4 * K ^ 4 * (P : ℝ) ^ (1 - 3 * ε) := by rw [hexp]

/-- **Polynomial decay of the relative two-scale cutoff shift.** For `0 < ε < ½`, relative to the
large-prime sector energy `‖L_P‖²`, the two-scale complete-prefix shift between `P²` and `(2P)²` on
the common head `1 ≤ N ≤ P − 1` decays at the **polynomial** rate `O(P^{−ε} log² P)` — strictly
stronger than any logarithmic power. -/
theorem exists_twoScaleCompleteShiftEnergy_div_sectorEnergy_le_rpow {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ P : ℕ in atTop,
      twoScaleCompleteShiftEnergy ε P (2 * P) (P - 1) /
        pmRamanujanLargePrimeSectorEnergy ε P ≤
        K * (P : ℝ) ^ (-ε) * Real.log (P : ℝ) ^ 2 := by
  obtain ⟨C, hC, hshift⟩ := exists_twoScaleCompleteShiftEnergy_le_pow_saving hε
  obtain ⟨c, hc, hsec⟩ := sectorEnergy_eventually_lower hε
  refine ⟨C / c, by positivity, ?_⟩
  filter_upwards [hsec, eventually_ge_atTop 2] with P hS hP2
  have hP1 : 1 ≤ P := by omega
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP2)
  have hlow : 0 < c * (P : ℝ) ^ (1 - 2 * ε) / Real.log (P : ℝ) ^ 2 := by positivity
  have hsec_pos : 0 < pmRamanujanLargePrimeSectorEnergy ε P := hlow.trans_le hS
  have hle1 : twoScaleCompleteShiftEnergy ε P (2 * P) (P - 1) ≤ C * (P : ℝ) ^ (1 - 3 * ε) :=
    (twoScaleCompleteShiftEnergy_mono ε P (2 * P) (Nat.sub_le P 1)).trans
      (hshift P (2 * P) hP1 (by omega))
  have hexp : (P : ℝ) ^ (1 - 3 * ε) / (P : ℝ) ^ (1 - 2 * ε) = (P : ℝ) ^ (-ε) := by
    rw [← Real.rpow_sub hP0]
    congr 1
    ring
  calc twoScaleCompleteShiftEnergy ε P (2 * P) (P - 1) /
        pmRamanujanLargePrimeSectorEnergy ε P
      ≤ (C * (P : ℝ) ^ (1 - 3 * ε)) / pmRamanujanLargePrimeSectorEnergy ε P :=
        div_le_div_of_nonneg_right hle1 hsec_pos.le
    _ ≤ (C * (P : ℝ) ^ (1 - 3 * ε)) / (c * (P : ℝ) ^ (1 - 2 * ε) / Real.log (P : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hlow hS
    _ = (C / c) * ((P : ℝ) ^ (1 - 3 * ε) / (P : ℝ) ^ (1 - 2 * ε)) * Real.log (P : ℝ) ^ 2 := by
        field_simp
    _ = (C / c) * (P : ℝ) ^ (-ε) * Real.log (P : ℝ) ^ 2 := by rw [hexp]

/-- **Absolute polynomial decay in the upper critical band `ε > 1/3`.** When `ε > 1/3`, the
unnormalized two-scale cutoff shift energy `twoScaleCompleteShiftEnergy ε P (2P) P` tends to `0` as
`P → ∞`. -/
theorem tendsto_twoScaleCompleteShiftEnergy_zero_of_one_third_lt {ε : ℝ} (hε : 1 / 3 < ε) :
    Tendsto (fun P : ℕ => twoScaleCompleteShiftEnergy ε P (2 * P) P) atTop (𝓝 0) := by
  have hε0 : 0 < ε := by linarith
  obtain ⟨C, hC, hshift⟩ := exists_twoScaleCompleteShiftEnergy_le_pow_saving hε0
  have hneg : 0 < 3 * ε - 1 := by linarith
  have hpow : Tendsto (fun P : ℕ => C * (P : ℝ) ^ (1 - 3 * ε)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop).const_mul C
    simpa only [Function.comp_def, neg_sub, mul_zero] using h
  refine squeeze_zero' (Eventually.of_forall fun P =>
    twoScaleCompleteShiftEnergy_nonneg ε P (2 * P) P) ?_ hpow
  filter_upwards [eventually_ge_atTop 1] with P hP
  exact hshift P (2 * P) hP (by omega)

/-! ## §3. All-logarithmic-power two-scale coordinate mismatch and moving-projection bounds -/

/-- **Uniform two-scale amplitude step for all `Q ≥ P`.** For `0 < ε < ½` and every `m ∈ ℕ`, there
is `K ≥ 0` such that for all large `P` and all `Q ≥ P`,
`|pmCompensationAmplitude ε Q − pmCompensationAmplitude ε P| ≤ K / log^m P`. -/
theorem exists_abs_pmCompensationAmplitude_sub_le_log_pow_of_le {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ P : ℕ in atTop, ∀ Q : ℕ, P ≤ Q →
      |pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P| ≤ K / Real.log (P : ℝ) ^ m := by
  obtain ⟨K₀, hK₀, hamp⟩ := exists_abs_one_sub_pmCompensationAmplitude_le_log_pow hε hεhalf m
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hamp
  refine ⟨2 * K₀, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 2)] with P hP Q hPQ
  have hPN₀ : N₀ ≤ P := (le_max_left N₀ 2).trans hP
  have hP2 : 2 ≤ P := (le_max_right N₀ 2).trans hP
  have hQN₀ : N₀ ≤ Q := hPN₀.trans hPQ
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlogPQ : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hP0 (by exact_mod_cast hPQ)
  have hQ_le : K₀ / Real.log (Q : ℝ) ^ m ≤ K₀ / Real.log (P : ℝ) ^ m :=
    div_le_div_of_nonneg_left hK₀ (by positivity) (pow_le_pow_left₀ hlogP.le hlogPQ m)
  have hsplit : pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P =
      (1 - pmCompensationAmplitude ε P) - (1 - pmCompensationAmplitude ε Q) := by ring
  rw [hsplit]
  calc |(1 - pmCompensationAmplitude ε P) - (1 - pmCompensationAmplitude ε Q)|
      ≤ |1 - pmCompensationAmplitude ε P| + |1 - pmCompensationAmplitude ε Q| := abs_sub _ _
    _ ≤ K₀ / Real.log (P : ℝ) ^ m + K₀ / Real.log (Q : ℝ) ^ m :=
        add_le_add (hN₀ P hPN₀) (hN₀ Q hQN₀)
    _ ≤ K₀ / Real.log (P : ℝ) ^ m + K₀ / Real.log (P : ℝ) ^ m := add_le_add le_rfl hQ_le
    _ = 2 * K₀ / Real.log (P : ℝ) ^ m := by ring

/-- **Two-scale amplitude step between `P²` and `(2P)²` at every logarithmic power.** For
`0 < ε < ½` and every `m ∈ ℕ`, there is `K ≥ 0` such that
`|pmCompensationAmplitude ε (2P) − pmCompensationAmplitude ε P| ≤ K / log^m P` for all large `P`. -/
theorem exists_abs_pmCompensationAmplitude_twoScale_sub_le_log_pow {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ P : ℕ in atTop,
      |pmCompensationAmplitude ε (2 * P) - pmCompensationAmplitude ε P| ≤
        K / Real.log (P : ℝ) ^ m := by
  obtain ⟨K, hK, h⟩ := exists_abs_pmCompensationAmplitude_sub_le_log_pow_of_le hε hεhalf m
  refine ⟨K, hK, ?_⟩
  filter_upwards [h] with P hP
  exact hP (2 * P) (by omega)

/-- **Two-scale compensation defect mismatch at every logarithmic power.** For `0 < ε < ½` and
every `m ∈ ℕ`, there is `K ≥ 0` such that for all large `P` and all `Q ≥ P`,
`|compensationDefect ε Q − compensationDefect ε P| ≤ K / log^m P`. -/
theorem exists_abs_compensationDefect_sub_le_log_pow_of_le {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ P : ℕ in atTop, ∀ Q : ℕ, P ≤ Q →
      |compensationDefect ε Q - compensationDefect ε P| ≤ K / Real.log (P : ℝ) ^ m := by
  obtain ⟨K₀, hK₀⟩ := exists_compensationDefect_le_inv_log_pow hε hεhalf m
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hK₀
  set K : ℝ := |K₀|
  have hK : 0 ≤ K := abs_nonneg K₀
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 2)] with P hP Q hPQ
  have hPN₀ : N₀ ≤ P := (le_max_left N₀ 2).trans hP
  have hP2 : 2 ≤ P := (le_max_right N₀ 2).trans hP
  have hQ2 : 2 ≤ Q := hP2.trans hPQ
  have hQN₀ : N₀ ≤ Q := hPN₀.trans hPQ
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlogPQ : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hP0 (by exact_mod_cast hPQ)
  have hdP : |compensationDefect ε P| ≤ K / Real.log (P : ℝ) ^ m := by
    rw [abs_of_nonneg (compensationDefect_nonneg ε hP2)]
    exact (hN₀ P hPN₀).trans (div_le_div_of_nonneg_right (le_abs_self K₀) (by positivity))
  have hdQ : |compensationDefect ε Q| ≤ K / Real.log (P : ℝ) ^ m := by
    rw [abs_of_nonneg (compensationDefect_nonneg ε hQ2)]
    refine (hN₀ Q hQN₀).trans ((div_le_div_of_nonneg_right (le_abs_self K₀) (by positivity)).trans ?_)
    exact div_le_div_of_nonneg_left hK (by positivity) (pow_le_pow_left₀ hlogP.le hlogPQ m)
  calc |compensationDefect ε Q - compensationDefect ε P|
      ≤ |compensationDefect ε Q| + |compensationDefect ε P| := abs_sub _ _
    _ ≤ K / Real.log (P : ℝ) ^ m + K / Real.log (P : ℝ) ^ m := add_le_add hdQ hdP
    _ = 2 * K / Real.log (P : ℝ) ^ m := by ring

/-- **Two-scale compensation defect mismatch between `P²` and `(2P)²`.** -/
theorem exists_abs_compensationDefect_twoScale_sub_le_log_pow {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ P : ℕ in atTop,
      |compensationDefect ε (2 * P) - compensationDefect ε P| ≤ K / Real.log (P : ℝ) ^ m := by
  obtain ⟨K, hK, h⟩ := exists_abs_compensationDefect_sub_le_log_pow_of_le hε hεhalf m
  refine ⟨K, hK, ?_⟩
  filter_upwards [h] with P hP
  exact hP (2 * P) (by omega)

/-- **Polynomial-weight dyadic summability of the moving-projection connection term.** For
`0 < ε < ½` and every weight exponent `m ∈ ℕ`,
`Σ_k k^m |α_{2^{k+1}} − α_{2^k}| < ∞`. -/
theorem summable_mul_pow_abs_pmCompensationAmplitude_dyadic_sub {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (m : ℕ) :
    Summable fun k : ℕ =>
      (k : ℝ) ^ m *
        |pmCompensationAmplitude ε (2 ^ (k + 1)) - pmCompensationAmplitude ε (2 ^ k)| := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_abs_pmCompensationAmplitude_twoScale_sub_le_log_pow hε hεhalf (m + 2)
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun k : ℕ => K / Real.log 2 ^ (m + 2) * (1 / (k : ℝ) ^ 2))
    ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _) ?_
  filter_upwards [h2.eventually hK, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hlog : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by simp [Real.log_pow]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ m),
    abs_abs, hpow]
  have hstep : (k : ℝ) ^ m *
      |pmCompensationAmplitude ε (2 * 2 ^ k) - pmCompensationAmplitude ε (2 ^ k)| ≤
      (k : ℝ) ^ m * (K / ((k : ℝ) * Real.log 2) ^ (m + 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hk' := hk
    rwa [hlog] at hk'
  calc (k : ℝ) ^ m *
        |pmCompensationAmplitude ε (2 * 2 ^ k) - pmCompensationAmplitude ε (2 ^ k)|
      ≤ (k : ℝ) ^ m * (K / ((k : ℝ) * Real.log 2) ^ (m + 2)) := hstep
    _ = K / Real.log 2 ^ (m + 2) * ((k : ℝ) ^ m / ((k : ℝ) ^ m * (k : ℝ) ^ 2)) := by
        rw [mul_pow, pow_add]
        ring
    _ = K / Real.log 2 ^ (m + 2) * (1 / (k : ℝ) ^ 2) := by
        congr 1
        field_simp

/-- **Polynomial-weight dyadic summability of the compensation defect.** For `0 < ε < ½` and every
weight exponent `m ∈ ℕ`, `Σ_k k^m · compensationDefect ε (2^k) < ∞`. -/
theorem summable_mul_pow_compensationDefect_dyadic {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (m : ℕ) :
    Summable fun k : ℕ => (k : ℝ) ^ m * compensationDefect ε (2 ^ k) := by
  obtain ⟨K, hK⟩ := exists_compensationDefect_le_inv_log_pow hε hεhalf (m + 2)
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun k : ℕ => |K| / Real.log 2 ^ (m + 2) * (1 / (k : ℝ) ^ 2))
    ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _) ?_
  filter_upwards [h2.eventually hK, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have hlog : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by simp [Real.log_pow]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ m),
    abs_of_nonneg (compensationDefect_nonneg ε hk2)]
  have hle : compensationDefect ε (2 ^ k) ≤ |K| / ((k : ℝ) * Real.log 2) ^ (m + 2) := by
    have hk' := hk.trans (div_le_div_of_nonneg_right (le_abs_self K) (by positivity))
    rwa [hlog] at hk'
  calc (k : ℝ) ^ m * compensationDefect ε (2 ^ k)
      ≤ (k : ℝ) ^ m * (|K| / ((k : ℝ) * Real.log 2) ^ (m + 2)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = |K| / Real.log 2 ^ (m + 2) * ((k : ℝ) ^ m / ((k : ℝ) ^ m * (k : ℝ) ^ 2)) := by
        rw [mul_pow, pow_add]
        ring
    _ = |K| / Real.log 2 ^ (m + 2) * (1 / (k : ℝ) ^ 2) := by
        congr 1
        field_simp

/-- The pronic energy on the common head `1 ≤ N ≤ P − 1` of the moving-projection connection term
`(α_Q − α_P) L_P`. -/
def pmConnectionEnergy (ε : ℝ) (P Q : ℕ) : ℝ :=
  (pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P) ^ 2 *
    pmRamanujanLargePrimeSectorEnergy ε P

/-- The pronic energy on the common head `1 ≤ N ≤ P − 1` of the inter-scale large-prime shell
`L_Q − L_P`. -/
def pmInterScaleSectorEnergy (ε : ℝ) (P Q : ℕ) : ℝ :=
  ∑ N ∈ Icc 1 (P - 1),
    ‖pmRamanujanLargePrimeSector ε Q N - pmRamanujanLargePrimeSector ε P N‖ ^ 2 /
      ((N : ℝ) * ((N : ℝ) + 1))

/-- The pronic energy on the common head `1 ≤ N ≤ P − 1` of the transverse remainder transition
`R_Q − R_P`. -/
def pmTransverseTransitionEnergy (ε : ℝ) (P Q : ℕ) : ℝ :=
  ∑ N ∈ Icc 1 (P - 1),
    ‖pmTransverseRemainderSeq ε Q N - pmTransverseRemainderSeq ε P N‖ ^ 2 /
      ((N : ℝ) * ((N : ℝ) + 1))

/-- **Three-term energy bound for the two-scale transverse transition.** For `2 ≤ P` and `2 ≤ Q`,
the common-head energy of `R_Q − R_P` is at most three times the power-saving cutoff shift energy
`twoScaleCompleteShiftEnergy ε P Q (P − 1)`, plus `3 (1 − α_Q)²` times the inter-scale prime-shell
energy, plus `3` times the moving-projection connection energy `pmConnectionEnergy ε P Q`. -/
theorem twoScale_transverseRemainder_diff_energy_le {P Q : ℕ} (hP : 2 ≤ P) (hQ : 2 ≤ Q)
    (ε : ℝ) :
    pmTransverseTransitionEnergy ε P Q ≤
      3 * twoScaleCompleteShiftEnergy ε P Q (P - 1) +
        3 * (1 - pmCompensationAmplitude ε Q) ^ 2 * pmInterScaleSectorEnergy ε P Q +
        3 * pmConnectionEnergy ε P Q := by
  unfold pmTransverseTransitionEnergy twoScaleCompleteShiftEnergy pmInterScaleSectorEnergy
    pmConnectionEnergy pmRamanujanLargePrimeSectorEnergy
  rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun N _ => ?_
  rw [pmTransverseRemainderSeq_sub_eq_connection hP hQ]
  set z₁ : ℂ := pmPowerDampedRamanujanCumulativePrefix ε (Q ^ 2 - 1) N -
    pmPowerDampedRamanujanCumulativePrefix ε (P ^ 2 - 1) N
  set z₂ : ℂ := -(((1 - pmCompensationAmplitude ε Q : ℝ) : ℂ) *
    (pmRamanujanLargePrimeSector ε Q N - pmRamanujanLargePrimeSector ε P N))
  set z₃ : ℂ := ((pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P : ℝ) : ℂ) *
    pmRamanujanLargePrimeSector ε P N
  have hsum_eq : z₁ - ((1 - pmCompensationAmplitude ε Q : ℝ) : ℂ) *
      (pmRamanujanLargePrimeSector ε Q N - pmRamanujanLargePrimeSector ε P N) + z₃ =
      z₁ + z₂ + z₃ := by dsimp [z₂]; ring
  rw [hsum_eq]
  have hnorm : ‖z₁ + z₂ + z₃‖ ≤ ‖z₁‖ + ‖z₂‖ + ‖z₃‖ :=
    (norm_add_le (z₁ + z₂) z₃).trans (add_le_add (norm_add_le z₁ z₂) le_rfl)
  have hsq : ‖z₁ + z₂ + z₃‖ ^ 2 ≤ 3 * ‖z₁‖ ^ 2 + 3 * ‖z₂‖ ^ 2 + 3 * ‖z₃‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith [sq_nonneg (‖z₁‖ - ‖z₂‖), sq_nonneg (‖z₁‖ - ‖z₃‖), sq_nonneg (‖z₂‖ - ‖z₃‖)]
  have hz₂ : ‖z₂‖ ^ 2 = (1 - pmCompensationAmplitude ε Q) ^ 2 *
      ‖pmRamanujanLargePrimeSector ε Q N - pmRamanujanLargePrimeSector ε P N‖ ^ 2 := by
    dsimp [z₂]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hz₃ : ‖z₃‖ ^ 2 = (pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P) ^ 2 *
      ‖pmRamanujanLargePrimeSector ε P N‖ ^ 2 := by
    dsimp [z₃]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hz₂, hz₃] at hsq
  have hdiv := div_le_div_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ (N : ℝ) * ((N : ℝ) + 1))
  calc ‖z₁ + z₂ + z₃‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))
      ≤ (3 * ‖z₁‖ ^ 2 +
          3 * ((1 - pmCompensationAmplitude ε Q) ^ 2 *
            ‖pmRamanujanLargePrimeSector ε Q N - pmRamanujanLargePrimeSector ε P N‖ ^ 2) +
          3 * ((pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P) ^ 2 *
            ‖pmRamanujanLargePrimeSector ε P N‖ ^ 2)) /
          ((N : ℝ) * ((N : ℝ) + 1)) := hdiv
    _ = 3 * (‖z₁‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1))) +
        3 * (1 - pmCompensationAmplitude ε Q) ^ 2 *
          (‖pmRamanujanLargePrimeSector ε Q N - pmRamanujanLargePrimeSector ε P N‖ ^ 2 /
            ((N : ℝ) * ((N : ℝ) + 1))) +
        3 * ((pmCompensationAmplitude ε Q - pmCompensationAmplitude ε P) ^ 2 *
          (‖pmRamanujanLargePrimeSector ε P N‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)))) := by ring

end GaloisForLFunctions.ArithmeticCompensationTheory
