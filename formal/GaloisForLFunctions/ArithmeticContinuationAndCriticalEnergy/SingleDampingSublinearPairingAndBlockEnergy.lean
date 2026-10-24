import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePronicDilationContractionAndItsThreshold
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheMajorantSourceIsNeverAdmitted
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationHardyInequalityOnThePronicMeasure
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedAveragedContinuationAndTheZeroWidthBand

/-!
# The One-Sided Sublinear Pairing at a Single Damping, the Majorant Threshold, and Block-Energy Equivalence

This module resolves Open Problem 4 of `ArithmeticContinuationAndCriticalEnergy` (and the third
deliverable in §6.2 on the pronic mean square of the short blocks `(⌊n/q⌋, n]`):

1. **Exact Identification of the Inversion Defect with the Majorant Source (`§1`)**:
   - For every `ε > 0` and `n : ℕ`, the inversion defect `ρ_ε(n) = n − m₀(ε) Φ_ε(n)` is
     `−m₀(ε)` times the centred prefix of the unsigned majorant row `d ↦ d^{-ε}`
     (`inversionDefect_eq_neg_density_mul_majorantCenteredPrefix`), so
     `‖ρ_ε‖_T² = m₀(ε)² E_T^{maj}(ε)` (`pronicNorm_inversionDefect_sq_eq`).
   - Consequently, for `0 < ε ≤ 1/2`, `ρ_ε(n) ≥ m₀(ε) 2^{-(1+ε)} n^{1−ε}` (`inversionDefect_ge_rpow`)
     and `‖ρ_ε‖_T` is unbounded in `T` (`not_bddAbove_pronicNorm_inversionDefect_of_le_half`), so
     Cauchy–Schwarz on `⟪A_ε, ρ_ε⟫_T` or `⟪A_ε⁺, ρ_ε⟫_T` cannot close at or below half damping.

2. **Unconditional One-Sided Sublinear Pairings and Majorant Admission Above Half Damping (`§2`)**:
   - For every `n ≥ 1`, `ρ_ε(n) = A_ε(n) + D^{ζ_ε, ≥ 2} A_ε(n)`
     (`inversionDefect_eq_centeredPrefix_add_offDiagonal`), so
     `‖ρ_ε‖_T ≤ (1 + Σ_{j=2}^T j^{-ε} √(2/j)) √(E_T(ε))`
     (`pronicNorm_inversionDefect_le_mul_sqrt_energy`).
   - For every `ε > 1/2`, the dilation series converges (`exists_sum_dilationSeries_le_of_half_lt`),
     giving an unconditional horizon-uniform bound on `‖ρ_ε‖_T`, unconditional admission of the
     majorant source (`admits_majorantEnergy_of_half_lt`), and thus the exact threshold equivalence
     `Admits majorantEnergy ε ↔ 1 / 2 < ε` (`admits_majorantEnergy_iff_half_lt`).
   - For every `ε > 1/2`, both one-sided sublinear pairings hold unconditionally with `κ' = 0`:
     `⟪A_ε, ρ_ε⟫_T ≤ ⟪A_ε⁺, ρ_ε⟫_T ≤ κ √(E_T(ε))` and
     `|⟪A_ε, D^{ζ_ε, ≥ 2} A_ε⟫_T| ≤ κ √(E_T(ε))`
     (`exists_onesided_sublinear_pairings_of_half_lt`).

3. **Single-Damping Sublinear Pairing and Block-Energy Equivalence (`§3`)**:
   - At any damping `ε > 0` and integer scale `q ≥ 2`, admission `Admits dampedMobiusEnergy ε`,
     membership `ε ∈ receiverDampings`, localized block-energy admission
     `Admits (dampedBlockEnergy q) ε`, and the combined sublinear pairing bound
     `⟪A_ε, ρ_ε⟫_T − ⟪A_ε, D^{ζ_ε, ≥ 2} A_ε⟫_T ≤ κ √(E_T(ε)) + κ'` are four-way equivalent
     (`singleDamping_admission_tfae`).

4. **Unconditional Block-Energy Control Above `Θ − ½` and on the Vinogradov–Korobov Band (`§4`)**:
   - For every `q ≥ 1` and `ε > Θ − ½`, the short-block pronic energy `dampedBlockEnergy q ε T` is
     unconditionally bounded uniformly in `T`
     (`admits_dampedBlockEnergy_of_zetaZeroAbscissa_sub_half_lt`).
   - On the Vinogradov–Korobov band `ε ≥ ½ − κ σ(T)/(480 log T)` above any floor `ε₀ > 0`,
     `dampedBlockEnergy q ε T ≤ 2(1 + 1/q) E` uniformly in `(T, ε)`
     (`exists_dampedBlockEnergy_le_on_vinogradovKorobovBand`), with sub-power saving
     `O_ε(T^{1−2ε} exp(−κ σ(T)/270))` at every fixed `0 < ε < ½`
     (`eventually_dampedBlockEnergy_le_vk_saving`).
-/

open Set Filter Topology Finset RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The Inversion Defect Is `−m₀(ε)` Times the Majorant Centred Prefix -/

/-- **The inversion defect is `−m₀(ε)` times the majorant centred prefix.** -/
theorem inversionDefect_eq_neg_density_mul_majorantCenteredPrefix {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    inversionDefect ε n = -(pmPowerDampedDivisorDensity ε).re * majorantCenteredPrefix ε n := by
  have hm0 := pmPowerDampedDivisorDensity_re_eq hε
  have hZ : realZetaSeries (1 + ε) ≠ 0 := (realZetaSeries_pos (by linarith)).ne'
  rw [inversionDefect, majorantCenteredPrefix, dampedUnitFloorSum, hm0]
  field_simp
  ring

/-- **The pronic norm squared of the inversion defect is `m₀(ε)²` times the majorant energy.** -/
theorem pronicNorm_inversionDefect_sq_eq {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    pronicNorm T (inversionDefect ε) ^ 2 =
      (pmPowerDampedDivisorDensity ε).re ^ 2 * majorantEnergy ε T := by
  have hfun : inversionDefect ε =
      fun n => -(pmPowerDampedDivisorDensity ε).re * majorantCenteredPrefix ε n :=
    funext (inversionDefect_eq_neg_density_mul_majorantCenteredPrefix hε)
  rw [hfun, pronicNorm_const_mul_sq, neg_sq, pronicNorm_sq, majorantEnergy]

/-- **Pointwise lower bound on the inversion defect from the zeta tail.** -/
theorem inversionDefect_ge_rpow {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    (pmPowerDampedDivisorDensity ε).re * (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) ≤
      inversionDefect ε n := by
  have hm0 := pmPowerDampedDivisorDensity_re_pos hε
  have hmaj := majorantCenteredPrefix_le hε hn
  rw [inversionDefect_eq_neg_density_mul_majorantCenteredPrefix hε]
  nlinarith

/-- **At or below half damping, the pronic norm of the inversion defect is unbounded in `T`.**
Consequently, Cauchy–Schwarz on `⟪A_ε, ρ_ε⟫_T` or `⟪A_ε⁺, ρ_ε⟫_T` cannot close for `0 < ε ≤ 1/2`. -/
theorem not_bddAbove_pronicNorm_inversionDefect_of_le_half {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (inversionDefect ε) ≤ B := by
  rintro ⟨B, hB⟩
  have hm0 := pmPowerDampedDivisorDensity_re_pos hε
  have hmaj : ∃ M : ℝ, ∀ T : ℕ, majorantEnergy ε T ≤ M := by
    refine ⟨(max B 0 / (pmPowerDampedDivisorDensity ε).re) ^ 2, fun T => ?_⟩
    have h1 : pronicNorm T (inversionDefect ε) ≤ max B 0 := (hB T).trans (le_max_left B 0)
    have hsq : pronicNorm T (inversionDefect ε) ^ 2 ≤ max B 0 ^ 2 :=
      pow_le_pow_left₀ (pronicNorm_nonneg T _) h1 2
    rw [pronicNorm_inversionDefect_sq_eq hε T] at hsq
    rw [div_pow, le_div_iff₀ (by positivity)]
    linarith
  exact not_admits_majorantEnergy hε hε2 hmaj

/-! ## §2. Unconditional One-Sided Sublinear Pairings and Majorant Admission Above Half Damping -/

/-- **The inversion defect is the source plus its off-diagonal unit dilation.** -/
theorem inversionDefect_eq_centeredPrefix_add_offDiagonal (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    inversionDefect ε n =
      pmPowerDampedCenteredDivisorPrefix ε n + offDiagonalUnitDilation ε n := by
  have hsplit := sum_rpow_mul_centeredPrefix_split ε hn
  rw [sum_rpow_mul_centeredPrefix_eq ε n] at hsplit
  rw [inversionDefect]
  linarith

/-- **Pronic norm bound for the inversion defect in terms of the source energy and dilation
series.** -/
theorem pronicNorm_inversionDefect_le_mul_sqrt_energy (ε : ℝ) (T : ℕ) :
    pronicNorm T (inversionDefect ε) ≤
      (1 + ∑ j ∈ Finset.Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) *
        Real.sqrt (dampedMobiusEnergy ε T) := by
  have hext : ∀ n ∈ Finset.Icc 1 T,
      inversionDefect ε n =
        pmPowerDampedCenteredDivisorPrefix ε n + offDiagonalUnitDilation ε n :=
    fun n hn => inversionDefect_eq_centeredPrefix_add_offDiagonal ε (Finset.mem_Icc.mp hn).1
  rw [pronicNorm_congr hext]
  have htri := pronicNorm_add_le T (pmPowerDampedCenteredDivisorPrefix ε)
    (offDiagonalUnitDilation ε)
  rw [pronicNorm_centeredPrefix] at htri
  have hoff := pronicNorm_offDiagonalUnitDilation_le ε T
  linarith

/-- **Above half damping, the partial dilation series are uniformly bounded.** -/
theorem exists_sum_dilationSeries_le_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ T : ℕ,
      (∑ j ∈ Finset.Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) ≤ S := by
  have hsum := summable_dilationSeries_of_half_lt hε
  refine ⟨∑' j : ℕ, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ)),
    tsum_nonneg (fun j => by positivity), fun T => ?_⟩
  exact hsum.sum_le_tsum (Finset.Icc 2 T) (fun j _ => by positivity)

/-- **Above half damping, the pronic norm of the inversion defect is uniformly bounded.** -/
theorem exists_pronicNorm_inversionDefect_le_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℕ, pronicNorm T (inversionDefect ε) ≤ K := by
  obtain ⟨S, hS0, hS⟩ := exists_sum_dilationSeries_le_of_half_lt hε
  obtain ⟨B, hB⟩ := admits_dampedMobiusEnergy_of_half_le hε.le
  refine ⟨(1 + S) * Real.sqrt (max B 0), by positivity, fun T => ?_⟩
  have h1 := pronicNorm_inversionDefect_le_mul_sqrt_energy ε T
  have h2 : Real.sqrt (dampedMobiusEnergy ε T) ≤ Real.sqrt (max B 0) :=
    Real.sqrt_le_sqrt ((hB T).trans (le_max_left B 0))
  have h3 : (1 + ∑ j ∈ Finset.Icc 2 T, (j : ℝ) ^ (-ε) * Real.sqrt (2 / (j : ℝ))) *
      Real.sqrt (dampedMobiusEnergy ε T) ≤ (1 + S) * Real.sqrt (max B 0) :=
    mul_le_mul (by linarith [hS T]) h2 (Real.sqrt_nonneg _) (by positivity)
  exact h1.trans h3

/-- **The majorant source is admitted for every `ε > 1/2`.** -/
theorem admits_majorantEnergy_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    Admits majorantEnergy ε := by
  have hε0 : 0 < ε := by linarith
  have hm0 := pmPowerDampedDivisorDensity_re_pos hε0
  obtain ⟨K, hK0, hK⟩ := exists_pronicNorm_inversionDefect_le_of_half_lt hε
  refine ⟨(K / (pmPowerDampedDivisorDensity ε).re) ^ 2, fun T => ?_⟩
  have hsq : pronicNorm T (inversionDefect ε) ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (pronicNorm_nonneg T _) (hK T) 2
  rw [pronicNorm_inversionDefect_sq_eq hε0 T] at hsq
  rw [div_pow, le_div_iff₀ (by positivity)]
  linarith

/-- **The exact threshold dichotomy for the majorant source: `Admits majorantEnergy ε ↔ 1/2 < ε`.** -/
theorem admits_majorantEnergy_iff_half_lt {ε : ℝ} (hε : 0 < ε) :
    Admits majorantEnergy ε ↔ 1 / 2 < ε := by
  constructor
  · intro hadm
    by_contra hle
    exact not_admits_majorantEnergy hε (not_lt.mp hle) hadm
  · exact admits_majorantEnergy_of_half_lt

/-- The pronic norm of the positive part of a row never exceeds the pronic norm of the row. -/
theorem pronicNorm_posPart_le (T : ℕ) (u : ℕ → ℝ) :
    pronicNorm T (fun n => max (u n) 0) ≤ pronicNorm T u := by
  unfold pronicNorm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun n _ => ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : 0 ≤ max (u n) 0 := le_max_right _ _
  have h2 : max (u n) 0 ≤ |u n| := max_le (le_abs_self _) (abs_nonneg _)
  calc max (u n) 0 ^ 2 ≤ |u n| ^ 2 := pow_le_pow_left₀ h1 h2 2
    _ = u n ^ 2 := sq_abs (u n)

/-- **Unconditional One-Sided Sublinear Pairings Above Half Damping (`ε > 1/2`).**
For every `ε > 1/2`, there exists `κ ≥ 0` such that for all `T : ℕ`:
1. `⟪A_ε, ρ_ε⟫_T ≤ ⟪A_ε⁺, ρ_ε⟫_T ≤ κ √(E_T(ε))`;
2. `|⟪A_ε, D^{ζ_ε, ≥ 2} A_ε⟫_T| ≤ κ √(E_T(ε))`. -/
theorem exists_onesided_sublinear_pairings_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ T : ℕ,
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) ≤
        pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
          (inversionDefect ε) ∧
      pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
        (inversionDefect ε) ≤ κ * Real.sqrt (dampedMobiusEnergy ε T) ∧
      |pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε)| ≤
        κ * Real.sqrt (dampedMobiusEnergy ε T) := by
  have hε0 : 0 < ε := by linarith
  obtain ⟨K, hK0, hK⟩ := exists_pronicNorm_inversionDefect_le_of_half_lt hε
  obtain ⟨S, hS0, hS⟩ := exists_sum_dilationSeries_le_of_half_lt hε
  obtain ⟨B, hB⟩ := admits_dampedMobiusEnergy_of_half_le hε.le
  refine ⟨max K (S * Real.sqrt (max B 0)), by positivity, fun T => ?_⟩
  have hle_pos : pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) ≤
      pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
        (inversionDefect ε) := by
    have h1 := dampedMobiusEnergy_le_posPart_pairing_sub hε0 T
    have h2 := dampedMobiusEnergy_eq_pairing_sub ε T
    linarith
  have hcs_pos : pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
      (inversionDefect ε) ≤
      Real.sqrt (dampedMobiusEnergy ε T) * pronicNorm T (inversionDefect ε) := by
    have hcs := sum_mul_div_le_pronicNorm T
      (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0) (inversionDefect ε)
    have hpos := pronicNorm_posPart_le T (pmPowerDampedCenteredDivisorPrefix ε)
    rw [pronicNorm_centeredPrefix] at hpos
    exact hcs.trans (mul_le_mul_of_nonneg_right hpos (pronicNorm_nonneg T _))
  have hpos_bound : pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
      (inversionDefect ε) ≤
      max K (S * Real.sqrt (max B 0)) * Real.sqrt (dampedMobiusEnergy ε T) := by
    calc pronicPairing T (fun n => max (pmPowerDampedCenteredDivisorPrefix ε n) 0)
          (inversionDefect ε)
        ≤ Real.sqrt (dampedMobiusEnergy ε T) * K :=
          hcs_pos.trans (mul_le_mul_of_nonneg_left (hK T) (Real.sqrt_nonneg _))
      _ = K * Real.sqrt (dampedMobiusEnergy ε T) := mul_comm _ _
      _ ≤ max K (S * Real.sqrt (max B 0)) * Real.sqrt (dampedMobiusEnergy ε T) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have hoff := abs_pronicPairing_offDiagonalUnitDilation_le ε T
  have hsqrt_le : Real.sqrt (dampedMobiusEnergy ε T) ≤ Real.sqrt (max B 0) :=
    Real.sqrt_le_sqrt ((hB T).trans (le_max_left B 0))
  have hoff_bound : |pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
      (offDiagonalUnitDilation ε)| ≤
      max K (S * Real.sqrt (max B 0)) * Real.sqrt (dampedMobiusEnergy ε T) := by
    calc |pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε)|
        ≤ S * dampedMobiusEnergy ε T :=
          hoff.trans (mul_le_mul_of_nonneg_right (hS T) (dampedMobiusEnergy_nonneg ε T))
      _ = (S * Real.sqrt (dampedMobiusEnergy ε T)) * Real.sqrt (dampedMobiusEnergy ε T) := by
          rw [← Real.sq_sqrt (dampedMobiusEnergy_nonneg ε T)]; ring
      _ ≤ (S * Real.sqrt (max B 0)) * Real.sqrt (dampedMobiusEnergy ε T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le hS0) (Real.sqrt_nonneg _)
      _ ≤ max K (S * Real.sqrt (max B 0)) * Real.sqrt (dampedMobiusEnergy ε T) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  exact ⟨hle_pos, hpos_bound, hoff_bound⟩

/-! ## §3. Single-Damping Sublinear Pairing Equivalence and Block-Energy Equivalence -/

/-- **Block-energy equivalence.** For every integer scale `q ≥ 2` and every damping `ε : ℝ`,
admission of the prefix energy `dampedMobiusEnergy ε` is equivalent to admission of the localized
block energy `dampedBlockEnergy q ε`. -/
theorem admits_dampedMobiusEnergy_iff_admits_blockEnergy {q : ℕ} (hq : 2 ≤ q) (ε : ℝ) :
    Admits dampedMobiusEnergy ε ↔ Admits (dampedBlockEnergy q) ε := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨(2 * (1 + 1 / (q : ℝ))) * max B 0, fun T => ?_⟩
    exact (dampedBlockEnergy_le (by omega) ε T).trans
      (mul_le_mul_of_nonneg_left ((hB T).trans (le_max_left B 0)) (by positivity))
  · rintro ⟨B, hB⟩
    exact admits_of_bounded_blockEnergy hq hB

/-- **Four-Way Single-Damping Equivalence.**
For any damping `ε > 0` and any integer scale `q ≥ 2`, admission `Admits dampedMobiusEnergy ε`,
membership `ε ∈ receiverDampings`, localized block-energy admission `Admits (dampedBlockEnergy q) ε`,
and the combined sublinear pairing bound
`⟪A_ε, ρ_ε⟫_T − ⟪A_ε, D^{ζ_ε, ≥ 2} A_ε⟫_T ≤ κ √(E_T(ε)) + κ'` are all equivalent. -/
theorem singleDamping_admission_tfae {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : 2 ≤ q) :
    List.TFAE
      [ Admits dampedMobiusEnergy ε,
        ε ∈ receiverDampings,
        Admits (dampedBlockEnergy q) ε,
        ∃ κ κ' : ℝ, 0 ≤ κ ∧ 0 ≤ κ' ∧ ∀ T : ℕ,
          pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) -
            pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε) ≤
              κ * Real.sqrt (dampedMobiusEnergy ε T) + κ' ] := by
  tfae_have 1 ↔ 2 := (mem_receiverDampings_iff_admits hε).symm
  tfae_have 1 ↔ 3 := admits_dampedMobiusEnergy_iff_admits_blockEnergy hq ε
  tfae_have 1 ↔ 4 := by
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨0, max B 0, le_rfl, le_max_right B 0, fun T => ?_⟩
      rw [← dampedMobiusEnergy_eq_pairing_sub ε T, zero_mul, zero_add]
      exact (hB T).trans (le_max_left B 0)
    · rintro ⟨κ, κ', hκ, hκ', hpair⟩
      refine ⟨(κ / 2 + Real.sqrt ((κ / 2) ^ 2 + κ')) ^ 2, fun T => ?_⟩
      have hE0 := dampedMobiusEnergy_nonneg ε T
      have hx0 : 0 ≤ Real.sqrt (dampedMobiusEnergy ε T) := Real.sqrt_nonneg _
      have hxx : Real.sqrt (dampedMobiusEnergy ε T) ^ 2 = dampedMobiusEnergy ε T :=
        Real.sq_sqrt hE0
      have hle : dampedMobiusEnergy ε T ≤ κ * Real.sqrt (dampedMobiusEnergy ε T) + κ' := by
        have hid := dampedMobiusEnergy_eq_pairing_sub ε T
        linarith [hpair T]
      have hroot : 0 ≤ (κ / 2) ^ 2 + κ' := by positivity
      have hsq : Real.sqrt ((κ / 2) ^ 2 + κ') ^ 2 = (κ / 2) ^ 2 + κ' := Real.sq_sqrt hroot
      have hsqrt0 : 0 ≤ Real.sqrt ((κ / 2) ^ 2 + κ') := Real.sqrt_nonneg _
      have hbound : Real.sqrt (dampedMobiusEnergy ε T) ≤
          κ / 2 + Real.sqrt ((κ / 2) ^ 2 + κ') := by
        nlinarith [hxx, hsq, hx0, hsqrt0]
      calc dampedMobiusEnergy ε T = Real.sqrt (dampedMobiusEnergy ε T) ^ 2 := hxx.symm
        _ ≤ (κ / 2 + Real.sqrt ((κ / 2) ^ 2 + κ')) ^ 2 := pow_le_pow_left₀ hx0 hbound 2
  tfae_finish

/-! ## §4. Unconditional Block-Energy Control Above `Θ − ½` and on the Vinogradov–Korobov Band -/

/-- **Unconditional admission of the localized block energy `(⌊n/q⌋, n]` above `Θ − ½`.** -/
theorem admits_dampedBlockEnergy_of_zetaZeroAbscissa_sub_half_lt {q : ℕ} (hq : 1 ≤ q) {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) :
    Admits (dampedBlockEnergy q) ε := by
  obtain ⟨B, hB⟩ := admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt hε
  refine ⟨(2 * (1 + 1 / (q : ℝ))) * max B 0, fun T => ?_⟩
  exact (dampedBlockEnergy_le hq ε T).trans
    (mul_le_mul_of_nonneg_left ((hB T).trans (le_max_left B 0)) (by positivity))

/-- **Unconditional Vinogradov–Korobov Band Bound for the Short-Block Pronic Energy.**
For every scale `q ≥ 1` and damping floor `ε₀ > 0`, there exists `E ≥ 0` such that for all `T : ℕ`
and all `ε ∈ [ε₀, 1/2]` in the Vinogradov–Korobov band `ε ≥ 1/2 − κ σ(T)/(480 log T)`,
`dampedBlockEnergy q ε T ≤ 2 (1 + 1/q) E`. -/
theorem exists_dampedBlockEnergy_le_on_vinogradovKorobovBand {q : ℕ} (hq : 1 ≤ q)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
        1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
          dampedBlockEnergy q ε T ≤ (2 * (1 + 1 / (q : ℝ))) * E := by
  obtain ⟨E, hE0, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  refine ⟨E, hE0, fun T ε hε_ge hε2 hband => ?_⟩
  exact (dampedBlockEnergy_le hq ε T).trans
    (mul_le_mul_of_nonneg_left (hE T ε hε_ge hε2 hband) (by positivity))

/-- **Unconditional All-Damping Sub-Power Vinogradov–Korobov Saving for the Short-Block Pronic
Energy.** -/
theorem eventually_dampedBlockEnergy_le_vk_saving {q : ℕ} (hq : 1 ≤ q) {ε : ℝ}
    (hε0 : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop,
      dampedBlockEnergy q ε T ≤
        (2 * (1 + 1 / (q : ℝ))) * C * (T : ℝ) ^ (1 - 2 * ε) *
          Real.exp (-(vkKappa * vkScale T / 270)) := by
  obtain ⟨C, hC0, hev⟩ := eventually_receiver_le_growth_of_pos hε0 hε2
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hev] with T hT
  have h1 := dampedBlockEnergy_le hq ε T
  have h2 : dampedMobiusEnergy ε T ≤
      C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := hT
  have hqpos : (0 : ℝ) ≤ 2 * (1 + 1 / (q : ℝ)) := by positivity
  calc dampedBlockEnergy q ε T
      ≤ (2 * (1 + 1 / (q : ℝ))) * dampedMobiusEnergy ε T := h1
    _ ≤ (2 * (1 + 1 / (q : ℝ))) *
          (C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270))) :=
        mul_le_mul_of_nonneg_left h2 hqpos
    _ = (2 * (1 + 1 / (q : ℝ))) * C * (T : ℝ) ^ (1 - 2 * ε) *
          Real.exp (-(vkKappa * vkScale T / 270)) := by ring

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
