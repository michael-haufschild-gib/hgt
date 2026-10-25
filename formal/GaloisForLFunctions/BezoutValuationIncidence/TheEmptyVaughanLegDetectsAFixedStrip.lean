import GaloisForLFunctions.BezoutValuationIncidence.VaughanReciprocalTailPowerGainsAreFixedStrips
import GaloisForLFunctions.BezoutValuationIncidence.ProductHorizonVaughanGramsHaveZeroTrivialDensity

/-!
# Empty Vaughan legs detect fixed zero-free strips

At a square product horizon, the normalized centered large-leg energy is comparable
to the fourth power of the normalized signed reciprocal tail. Finite Abel inversion
therefore identifies a positive power saving with a fixed zero-free strip.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The normalized empty-leg energy is comparable to the fourth power of the normalized tail. -/
theorem pmPronicVaughanCentredGram_square_scaled_bounds {ε : ℝ} (hε : 0 < ε)
    {N : ℕ} (hN : 1 ≤ N) :
    pmPronicPowerDensity ε ^ 2 / 2 * ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4 ≤
      pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 / ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ∧
    pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 / ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
      pmPronicPowerDensity ε ^ 2 * ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : 0 < ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (pow_pos (by omega : 0 < N) 2)) _
  have hpower : ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) * ((N : ℝ) ^ ε) ^ 4 = (N ^ 2 : ℕ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (1 - 2 * ε) + ε * 4 = 2 by ring, Real.rpow_two]
  have hE := sq_pronicNorm_natCast_bounds (N ^ 2)
  have heq := pmPronicVaughanCentredGram_square_large_eq_tail hε N
  change pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 =
    pmPronicPowerDensity ε ^ 2 * pmPronicVaughanReciprocalTail ε N ^ 4 *
      pronicNorm (fun n : ℕ => (n : ℝ)) (N ^ 2) ^ 2 at heq
  rw [heq, le_div_iff₀ hT0, div_le_iff₀ hT0]
  have hlo := mul_le_mul_of_nonneg_left hE.1
    (mul_nonneg (sq_nonneg (pmPronicPowerDensity ε)) (by positivity : 0 ≤ pmPronicVaughanReciprocalTail ε N ^ 4))
  have hhi := mul_le_mul_of_nonneg_left hE.2
    (mul_nonneg (sq_nonneg (pmPronicPowerDensity ε)) (by positivity : 0 ≤ pmPronicVaughanReciprocalTail ε N ^ 4))
  have hproduct : (pmPronicPowerDensity ε ^ 2 *
      ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4) *
        ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) =
      pmPronicPowerDensity ε ^ 2 * pmPronicVaughanReciprocalTail ε N ^ 4 * (N ^ 2 : ℕ) := by
    rw [mul_pow]
    calc
      _ = pmPronicPowerDensity ε ^ 2 * pmPronicVaughanReciprocalTail ε N ^ 4 *
        (((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) * ((N : ℝ) ^ ε) ^ 4) := by ring
      _ = _ := by rw [hpower]
  constructor
  · convert hlo using 1
    linear_combination hproduct / 2
  · rw [hproduct]
    exact hhi

/-- A signed-tail power rate gives the corresponding power saving for the centered empty leg. -/
theorem pmPronicVaughanCentredGram_square_power_bound_of_tail {ε η K : ℝ}
    (hε : 0 < ε) (_hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N → |pmPronicVaughanReciprocalTail ε N| ≤ K * (N : ℝ) ^ (-ε - η))
    {N : ℕ} (hN : 1 ≤ N) :
    pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 / ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
      (pmPronicPowerDensity ε ^ 2 * K ^ 4) * (N : ℝ) ^ (-(4 * η)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : |(N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N| ≤ K * (N : ℝ) ^ (-η) := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN0 ε)]
    calc
      _ ≤ (N : ℝ) ^ ε * (K * (N : ℝ) ^ (-ε - η)) :=
        mul_le_mul_of_nonneg_left (hF N hN) (Real.rpow_nonneg hN0.le _)
      _ = K * ((N : ℝ) ^ ε * (N : ℝ) ^ (-ε - η)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hN0,
          show ε + (-ε - η) = -η by ring]
  have hpower : ((N : ℝ) ^ (-η)) ^ 4 = (N : ℝ) ^ (-(4 * η)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have h4' : ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4 ≤
      K ^ 4 * (N : ℝ) ^ (-(4 * η)) := by
    calc
      _ = |(N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N| ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ (K * (N : ℝ) ^ (-η)) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hscale 4
      _ = _ := by rw [mul_pow, hpower]
  exact (pmPronicVaughanCentredGram_square_scaled_bounds hε hN).2.trans
    ((mul_le_mul_of_nonneg_left h4' (sq_nonneg _)).trans_eq (by ring))

/-- A power saving in the centered empty leg recovers a signed-tail power saving. -/
theorem abs_pmPronicVaughanReciprocalTail_le_of_square_energy_power {ε δ C : ℝ}
    (hε : 0 < ε) (_hC : 0 ≤ C)
    (hE : ∀ N : ℕ, 1 ≤ N →
      pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 / ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
        C * (N : ℝ) ^ (-δ)) {N : ℕ} (hN : 1 ≤ N) :
    |pmPronicVaughanReciprocalTail ε N| ≤
      Real.sqrt (Real.sqrt (2 * C / pmPronicPowerDensity ε ^ 2)) * (N : ℝ) ^ (-ε - δ / 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hZ : 0 < pmPronicPowerDensity ε := by
    rw [pmPronicPowerDensity_eq_inv_density hε]
    exact inv_pos.mpr (pmPowerDampedDivisorDensity_re_pos hε)
  let t : ℝ := (N : ℝ) ^ (ε + δ / 4) * |pmPronicVaughanReciprocalTail ε N|
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hpow : t ^ 4 = ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4 * (N : ℝ) ^ δ := by
    have hfour (α : ℝ) : ((N : ℝ) ^ α) ^ 4 = (N : ℝ) ^ (α * 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      norm_num only [Nat.cast_ofNat]
    dsimp only [t]
    simp only [mul_pow, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ pmPronicVaughanReciprocalTail ε N ^ 4), hfour]
    rw [show (ε + δ / 4) * 4 = ε * 4 + δ by ring, Real.rpow_add hN0]
    ring
  have hbound := (pmPronicVaughanCentredGram_square_scaled_bounds hε hN).1.trans (hE N hN)
  have hm := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hN0.le δ)
  have hcancel : (N : ℝ) ^ (-δ) * (N : ℝ) ^ δ = 1 := by
    rw [← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have h4 : t ^ 4 ≤ 2 * C / pmPronicPowerDensity ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hZ)).mpr
    have hr : pmPronicPowerDensity ε ^ 2 / 2 * t ^ 4 ≤ C := by
      rw [hpow]
      calc
        _ = (pmPronicPowerDensity ε ^ 2 / 2 *
            ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4) * (N : ℝ) ^ δ := by ring
        _ ≤ (C * (N : ℝ) ^ (-δ)) * (N : ℝ) ^ δ := hm
        _ = C := by rw [mul_assoc, hcancel, mul_one]
    linarith only [hr]
  have hroot := Real.sqrt_le_sqrt h4
  rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg t)] at hroot
  have hroot2 := Real.sqrt_le_sqrt hroot
  rw [Real.sqrt_sq ht0] at hroot2
  have hdiv : |pmPronicVaughanReciprocalTail ε N| ≤
      Real.sqrt (Real.sqrt (2 * C / pmPronicPowerDensity ε ^ 2)) / (N : ℝ) ^ (ε + δ / 4) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hN0 (ε + δ / 4))).mpr
    (by simpa only [t, mul_comm] using hroot2)
  calc
    _ ≤ Real.sqrt (Real.sqrt (2 * C / pmPronicPowerDensity ε ^ 2)) /
      (N : ℝ) ^ (ε + δ / 4) := hdiv
    _ = _ := by rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le]; congr 2; ring

/-- The centered empty-leg power-saving problem is exactly the fixed-strip problem. -/
theorem zetaZeroAbscissa_lt_one_iff_vaughan_square_energy_power {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    zetaZeroAbscissa < 1 ↔ ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N →
        pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 / ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
          C * (N : ℝ) ^ (-δ) := by
  constructor
  · intro hΘ
    obtain ⟨η, K, hη, _, hK, hF⟩ := (zetaZeroAbscissa_lt_one_iff_vaughan_reciprocalTail_power hε hε1).mp hΘ
    exact ⟨4 * η, pmPronicPowerDensity ε ^ 2 * K ^ 4, by positivity, by positivity,
      fun N hN => pmPronicVaughanCentredGram_square_power_bound_of_tail hε hK hF hN⟩
  · rintro ⟨δ, C, hδ, hC, hE⟩
    apply (zetaZeroAbscissa_lt_one_iff_vaughan_reciprocalTail_power hε hε1).mpr
    refine ⟨min (δ / 4) (1 / 2), Real.sqrt (Real.sqrt (2 * C / pmPronicPowerDensity ε ^ 2)),
      lt_min (by positivity) (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
      Real.sqrt_nonneg _, fun N hN => ?_⟩
    refine (abs_pmPronicVaughanReciprocalTail_le_of_square_energy_power hε hC hE hN).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (by linarith only [min_le_left (δ / 4) (1 / 2)])) (Real.sqrt_nonneg _)





end GaloisForLFunctions.BezoutValuationIncidence
