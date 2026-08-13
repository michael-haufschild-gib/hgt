import GaloisForLFunctions.RHTower.Sieve.MaynardPerronAmplitude
import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedWindowedHuxley

/-!
# Amplitude-normalized windowed Huxley

The global amplitude interface in `MaynardPerronAmplitude` assumes square-scale absorption at the
full ordinate height.  Here the same weighted-energy cancellation is applied at a shorter window
length `W`; summing the windows retains the exact loss `huxleyWindowCount T W`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Correct amplitude-normalized Huxley interface below the global square scale. -/
theorem huxley_heathBrown_grouped_large_values_finset_at_amplitude_windowed
    {ι : Type*} [Fintype ι] (L X ell K : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {c alpha : ℝ} (hc : 0 ≤ c)
    (Graw : ℝ) (hGraw : 0 ≤ Graw)
    (henergy : ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤ Graw)
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T W : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hW : 0 < W)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, 0 ≤ lam r ∧ lam r ≤ T)
    (hheight : W ≤ 8 * Real.pi *
      ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ 2)
    (hlarge : ∀ r ∈ S,
      ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (alpha - c) ≤
        ‖(∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖)
    (hscale :
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) ^ 2 * Graw *
          (1 + 256 * (Real.sqrt W +
            8 * Real.sqrt
              ((((groupedDyadicUpper q) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (2 * alpha)) :
    (S.card : ℝ) *
        (((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (alpha - c)) ^ 2 ≤
      (huxleyWindowCount T W : ℝ) *
        (2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
          ∑ r : Fin (Fintype.card ι * ell + 1),
            ((((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^
                (-c)) ^ 2 * Graw *
              (((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) +
                (12 * Real.pi *
                  ((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) /
                    delta) *
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)))) := by
  let A : ℕ := groupedDyadicLower q
  let D : Fin (Fintype.card ι * ell + 1) → ℕ :=
    fun r => A ^ ell * 2 ^ (r : ℕ)
  have hA : 1 ≤ A := by
    simpa only [A] using one_le_groupedDyadicLower q
  have hD1 : ∀ r, 1 ≤ D r := by
    intro r
    dsimp only [D]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ell (by omega)) (pow_ne_zero (r : ℕ) (by norm_num)))
  have hU : ∀ r : Fin (Fintype.card ι * ell + 1),
      0 < maynardHuxleyU (D r) := fun r => maynardHuxleyU_pos (hD1 r)
  have hnear : ∀ r : Fin (Fintype.card ι * ell + 1),
      3 * maynardHuxleyU (D r) ≤ 4 * Real.pi * (D r : ℝ) := fun _ =>
    maynardHuxleyU_near
  have hY_D : ∀ r : Fin (Fintype.card ι * ell + 1),
      ((((A ^ ell : ℕ) : ℝ)) ≤ (D r : ℝ)) := by
    intro r
    dsimp only [D]
    exact_mod_cast Nat.le_mul_of_pos_right (A ^ ell) (pow_pos (by omega) _)
  have hlamW : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicLambda (D r) W ≤ 1 := by
    intro r
    apply logDyadicLambda_le_one_of_height_le (hD1 r)
    have hsquare : ((((A ^ ell : ℕ) : ℝ)) ^ 2) ≤ ((D r : ℝ) ^ 2) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY_D r) 2
    exact hheight.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))
  have hB : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicSecondEnvelope (D r) (maynardHuxleyU (D r)) W ≤
        maynardHuxleyB (D r) W := fun r =>
    logDyadicSecondEnvelope_le_maynardHuxleyB (D r) W
  have hB1 : ∀ r : Fin (Fintype.card ι * ell + 1),
      1 ≤ maynardHuxleyB (D r) W := fun r => one_le_maynardHuxleyB (D r) W
  have hscale' :
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) ^ 2 * Graw *
          (1 + 256 * (Real.sqrt W +
            8 * Real.sqrt
              (((((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (2 * alpha) := by
    rw [← groupedDyadicUpper_eq_lower_mul_twoPow q]
    exact hscale
  have hBmax : ∀ r : Fin (Fintype.card ι * ell + 1),
      0 ≤ maynardHuxleyB (D r) W ∧
      maynardHuxleyB (D r) W ≤
        1 + 256 * (Real.sqrt W +
          8 * Real.sqrt
            (((((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell : ℕ) : ℝ))) := by
    intro r
    constructor
    · exact (one_le_maynardHuxleyB (D r) W).trans' (by norm_num)
    · have hDupper : D r ≤ ((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell := by
        dsimp only [D, A]
        rw [mul_pow, ← pow_mul]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hbase := maynardHuxleyB_le (hD1 r) hW.le
      have hsqrt : Real.sqrt (D r : ℝ) ≤
          Real.sqrt (((((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hDupper)
      exact hbase.trans (by gcongr)
  have hYpos : 0 < (((A ^ ell : ℕ) : ℝ)) := by
    exact_mod_cast pow_pos (by omega : 0 < A) ell
  have habsorb : ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
      ∑ r : Fin (Fintype.card ι * ell + 1),
        ((((D r : ℝ) ^ (-c)) ^ 2 * Graw) * maynardHuxleyB (D r) W) ≤
      ((((A ^ ell : ℕ) : ℝ)) ^ (alpha - c)) ^ 2 / 2 := by
    simpa only [Fintype.card_fin] using
      (weighted_huxley_absorption_at_amplitude D
        (fun r => maynardHuxleyB (D r) W) hYpos hc hY_D hGraw hBmax
          (by simpa only [A, Fintype.card_fin] using hscale'))
  simpa only [A, D] using
    huxley_heathBrown_grouped_large_values_finset_weighted_windowed
      L X ell K kind q hc Graw henergy
      (fun r => maynardHuxleyU (D r))
      (fun r => maynardHuxleyB (D r) W) hS hdelta hT hW
      (Real.rpow_pos_of_pos hYpos _) hU hgap hband hnear hlamW hB hB1
      hlarge habsorb

end RHTower.Sieve
