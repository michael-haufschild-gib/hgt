import GaloisForLFunctions.RHTower.Sieve.MaynardUniformAbsorption

/-!
# Canonical weighted Huxley application

This removes every schedule and absorption placeholder from the fixed-group all-short theorem.
For a raised grouped factor with lower edge `Y=A^ell`, block switch `U=D`, clipped envelope
`maynardHuxleyB D T`, the Huxley hypotheses follow from two transparent conditions: the complete
height lies below `8*pi*Y^(2 : ℕ)`, and the sigma-free energy scale inequality from uniform absorption.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Canonical fixed-group Huxley theorem.**  Schedule and sigma-dependent absorption are
discharged internally. -/
theorem huxley_heathBrown_grouped_large_values_finset_canonical
    {ι : Type*} [Fintype ι] (L X ell K : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (Graw : ℝ) (hGraw : 0 ≤ Graw)
    (henergy : ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤ Graw)
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hheight : T ≤ 8 * Real.pi *
      ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ 2)
    (hlarge : ∀ r ∈ S,
      ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (1 - sigma) ≤
        ‖(∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖)
    (hscale :
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) ^ 2 * Graw *
          (1 + 256 * (Real.sqrt T +
            8 * Real.sqrt
              ((((groupedDyadicUpper q) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ 2) :
    (S.card : ℝ) *
        (((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ (1 - sigma)) ^ 2 ≤
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
        ∑ r : Fin (Fintype.card ι * ell + 1),
          ((((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^
              (-sigma)) ^ 2 * Graw *
            (((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) +
              (12 * Real.pi *
                ((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) /
                  delta) *
                ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  let A : ℕ := groupedDyadicLower q
  let D : Fin (Fintype.card ι * ell + 1) → ℕ :=
    fun r => A ^ ell * 2 ^ (r : ℕ)
  have hA : 1 ≤ A := one_le_groupedDyadicLower q
  have hD1 : ∀ r, 1 ≤ D r := by
    intro r
    dsimp [D]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ell (by omega)) (pow_ne_zero (r : ℕ) (by norm_num)))
  have hU : ∀ r : Fin (Fintype.card ι * ell + 1),
      0 < maynardHuxleyU (D r) := by
    intro r
    exact maynardHuxleyU_pos (hD1 r)
  have hnear : ∀ r : Fin (Fintype.card ι * ell + 1),
      3 * maynardHuxleyU (D r) ≤ 4 * Real.pi * (D r : ℝ) := by
    intro r
    exact maynardHuxleyU_near
  have hY_D : ∀ r : Fin (Fintype.card ι * ell + 1),
      ((((A ^ ell : ℕ) : ℝ)) ≤ (D r : ℝ)) := by
    intro r
    dsimp [D]
    exact_mod_cast Nat.le_mul_of_pos_right (A ^ ell) (pow_pos (by omega) _)
  have hlamT : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicLambda (D r) T ≤ 1 := by
    intro r
    apply logDyadicLambda_le_one_of_height_le (hD1 r)
    have hsquare : ((((A ^ ell : ℕ) : ℝ)) ^ 2) ≤ ((D r : ℝ) ^ 2) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY_D r) 2
    exact hheight.trans (mul_le_mul_of_nonneg_left hsquare (by positivity))
  have hB : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicSecondEnvelope (D r) (maynardHuxleyU (D r)) T ≤
        maynardHuxleyB (D r) T := by
    intro r
    exact logDyadicSecondEnvelope_le_maynardHuxleyB (D r) T
  have hB1 : ∀ r : Fin (Fintype.card ι * ell + 1),
      1 ≤ maynardHuxleyB (D r) T := by
    intro r
    exact one_le_maynardHuxleyB (D r) T
  have hscale' :
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) ^ 2 * Graw *
          (1 + 256 * (Real.sqrt T +
            8 * Real.sqrt
              (((((groupedDyadicLower q) * 2 ^ Fintype.card ι) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower q) ^ ell : ℕ) : ℝ)) ^ 2 := by
    rw [← groupedDyadicUpper_eq_lower_mul_twoPow q]
    exact hscale
  have habsorb : ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
      ∑ r : Fin (Fintype.card ι * ell + 1),
        ((((D r : ℝ) ^ (-sigma)) ^ 2 * Graw) * maynardHuxleyB (D r) T) ≤
      ((((A ^ ell : ℕ) : ℝ)) ^ (1 - sigma)) ^ 2 / 2 := by
    simpa [A, D] using
      (maynard_fixedWidth_canonical_absorption
        (A := groupedDyadicLower q) (w := Fintype.card ι) (ell := ell)
        hA hsigma hT hGraw hscale')
  simpa [A, D] using
    huxley_heathBrown_grouped_large_values_finset_weighted
      L X ell K kind q hsigma Graw henergy
      (fun r => maynardHuxleyU (D r))
      (fun r => maynardHuxleyB (D r) T) hS hdelta
      (Real.rpow_pos_of_pos (by positivity) _) hU hgap hnear hlamT hB hB1
      hdiam hlarge habsorb

end RHTower.Sieve
