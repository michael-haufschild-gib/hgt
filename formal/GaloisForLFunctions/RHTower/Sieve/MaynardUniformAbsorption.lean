import GaloisForLFunctions.RHTower.Sieve.MaynardHuxleySchedule

/-!
# Sigma-uniform absorption for the all-short Huxley case

The weighted Huxley block mass contains `D^(-2 sigma)`.  If every block begins above the
raised lower edge `Y` and the selected value threshold is `Y^(1-sigma)`, this weight cancels
the entire sigma-dependence of the absorption inequality.  What remains is the scale condition
`2 Q^2 G B <= Y^2`, uniformly up to `sigma = 1`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **Sigma cancellation in weighted multiblock absorption.** -/
theorem weighted_huxley_absorption_of_common_lower_edge
    {ι : Type*} [Fintype ι] (D : ι → ℕ) (B : ι → ℝ)
    {Y sigma Graw Bmax : ℝ}
    (hY : 0 < Y) (hsigma : 0 ≤ sigma)
    (hD : ∀ r, Y ≤ (D r : ℝ))
    (hGraw : 0 ≤ Graw) (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Bmax)
    (hscale : 2 * (Fintype.card ι : ℝ) ^ 2 * Graw * Bmax ≤ Y ^ 2) :
    (Fintype.card ι : ℝ) *
        ∑ r : ι, ((((D r : ℝ) ^ (-sigma)) ^ 2 * Graw) * B r) ≤
      (Y ^ (1 - sigma)) ^ 2 / 2 := by
  have hweight : ∀ r,
      (D r : ℝ) ^ (-sigma) ≤ Y ^ (-sigma) := by
    intro r
    have hDr : 0 < (D r : ℝ) := hY.trans_le (hD r)
    rw [Real.rpow_neg hDr.le, Real.rpow_neg hY.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hDr sigma)
      (Real.rpow_pos_of_pos hY sigma)).2
        (Real.rpow_le_rpow hY.le (hD r) hsigma)
  have hterm : ∀ r,
      (((D r : ℝ) ^ (-sigma)) ^ 2 * Graw) * B r ≤
        (Y ^ (-sigma)) ^ 2 * Graw * Bmax := by
    intro r
    have hDpow0 : 0 ≤ (D r : ℝ) ^ (-sigma) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hYpow0 : 0 ≤ Y ^ (-sigma) := Real.rpow_nonneg hY.le _
    have hsquare : ((D r : ℝ) ^ (-sigma)) ^ 2 ≤ (Y ^ (-sigma)) ^ 2 :=
      pow_le_pow_left₀ hDpow0 (hweight r) 2
    have hcoeff : ((D r : ℝ) ^ (-sigma)) ^ 2 * Graw ≤
        (Y ^ (-sigma)) ^ 2 * Graw :=
      mul_le_mul_of_nonneg_right hsquare hGraw
    calc
      (((D r : ℝ) ^ (-sigma)) ^ 2 * Graw) * B r
          ≤ ((Y ^ (-sigma)) ^ 2 * Graw) * B r :=
            mul_le_mul_of_nonneg_right hcoeff (hB r).1
      _ ≤ (Y ^ (-sigma)) ^ 2 * Graw * Bmax :=
            mul_le_mul_of_nonneg_left (hB r).2 (mul_nonneg (sq_nonneg _) hGraw)
  have hsum :
      ∑ r : ι, ((((D r : ℝ) ^ (-sigma)) ^ 2 * Graw) * B r) ≤
        (Fintype.card ι : ℝ) * ((Y ^ (-sigma)) ^ 2 * Graw * Bmax) := by
    calc
      ∑ r : ι, ((((D r : ℝ) ^ (-sigma)) ^ 2 * Graw) * B r)
          ≤ ∑ _r : ι, ((Y ^ (-sigma)) ^ 2 * Graw * Bmax) :=
            Finset.sum_le_sum fun r _hr => hterm r
      _ = (Fintype.card ι : ℝ) * ((Y ^ (-sigma)) ^ 2 * Graw * Bmax) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard0 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hsumScaled := mul_le_mul_of_nonneg_left hsum hcard0
  have hscale' :
      (Fintype.card ι : ℝ) ^ 2 * Graw * Bmax ≤ Y ^ 2 / 2 := by
    linarith
  have hweight0 : 0 ≤ (Y ^ (-sigma)) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hscale' hweight0
  have hthreshold :
      (Y ^ (1 - sigma)) ^ 2 = Y ^ 2 * (Y ^ (-sigma)) ^ 2 := by
    rw [show (1 - sigma : ℝ) = 1 + (-sigma) by ring,
      Real.rpow_add hY, Real.rpow_one]
    ring
  calc
    (Fintype.card ι : ℝ) *
        ∑ r : ι, ((((D r : ℝ) ^ (-sigma)) ^ 2 * Graw) * B r)
        ≤ (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) * ((Y ^ (-sigma)) ^ 2 * Graw * Bmax)) :=
            hsumScaled
    _ = (Y ^ (-sigma)) ^ 2 *
        ((Fintype.card ι : ℝ) ^ 2 * Graw * Bmax) := by ring
    _ ≤ (Y ^ (-sigma)) ^ 2 * (Y ^ 2 / 2) := hscaled
    _ = (Y ^ (1 - sigma)) ^ 2 / 2 := by rw [hthreshold]; ring

/-- Canonical fixed-width schedule reduces absorption to one sigma-free scale inequality. -/
theorem maynard_fixedWidth_canonical_absorption
    {A w ell : ℕ} (hA : 1 ≤ A) {sigma T Graw : ℝ}
    (hsigma : 0 ≤ sigma) (hT : 0 ≤ T) (hGraw : 0 ≤ Graw)
    (hscale :
      2 * ((w * ell + 1 : ℕ) : ℝ) ^ 2 * Graw *
          (1 + 256 * (Real.sqrt T +
            8 * Real.sqrt ((((A * 2 ^ w) ^ ell : ℕ) : ℝ)))) ≤
        (((A ^ ell : ℕ) : ℝ)) ^ 2) :
    ((w * ell + 1 : ℕ) : ℝ) *
        ∑ r : Fin (w * ell + 1),
          (((((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 * Graw) *
            maynardHuxleyB (A ^ ell * 2 ^ (r : ℕ)) T ≤
      (((((A ^ ell : ℕ) : ℝ)) ^ (1 - sigma)) ^ 2) / 2 := by
  let D : Fin (w * ell + 1) → ℕ := fun r => A ^ ell * 2 ^ (r : ℕ)
  let Z : ℕ := (A * 2 ^ w) ^ ell
  let Bmax : ℝ := 1 + 256 * (Real.sqrt T + 8 * Real.sqrt (Z : ℝ))
  have hY : 0 < (((A ^ ell : ℕ) : ℝ)) := by
    positivity
  have hDlower : ∀ r, (((A ^ ell : ℕ) : ℝ)) ≤ (D r : ℝ) := by
    intro r
    dsimp [D]
    exact_mod_cast Nat.le_mul_of_pos_right (A ^ ell) (pow_pos (by omega) _)
  have hDupper : ∀ r, D r ≤ Z := by
    intro r
    dsimp [D, Z]
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hBmax : ∀ r, 0 ≤ maynardHuxleyB (D r) T ∧
      maynardHuxleyB (D r) T ≤ Bmax := by
    intro r
    constructor
    · exact (one_le_maynardHuxleyB (D r) T).trans' (by norm_num)
    · have hD1 : 1 ≤ D r := by
        exact Nat.one_le_iff_ne_zero.mpr (by
          dsimp [D]
          exact mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by norm_num)))
      have hbase := maynardHuxleyB_le hD1 hT
      have hsqrt : Real.sqrt (D r : ℝ) ≤ Real.sqrt (Z : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hDupper r)
      exact hbase.trans (by dsimp [Bmax]; gcongr)
  have h := weighted_huxley_absorption_of_common_lower_edge
    D (fun r => maynardHuxleyB (D r) T) hY hsigma hDlower hGraw hBmax
      (by simpa [Bmax, Z] using hscale)
  simpa [D] using h

end RHTower.Sieve
