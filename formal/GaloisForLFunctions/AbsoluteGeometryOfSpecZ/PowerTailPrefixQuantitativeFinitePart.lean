import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailPrefixFinitePart
import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin

/-!
# A quantitative finite part at every real cutoff

The centered Euler remainder controls integer power prefixes. The
co-Poisson floor estimate transports this bound to arbitrary real cutoffs,
giving error `O(X⁻ᵃ)` after subtracting the power integral and zeta value.
-/

noncomputable section

open Complex Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower.DeletionMixedRefinement

private theorem norm_powerTailPrefix_nat_finitePart_le
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖(powerTailPrefix a N : ℂ) - (N : ℂ) ^ (1 - (a : ℂ)) / (1 - (a : ℂ)) -
      riemannZeta (a : ℂ)‖ ≤
        (‖(a : ℂ) * ((a : ℂ) + 1)‖ / (a + 1) + 1 / 2) * (N : ℝ) ^ (-a) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb := norm_powerSumRemainder_le (s := (a : ℂ))
    (by simpa only [ofReal_re] using (show -1 < a by linarith only [ha]))
    (by exact_mod_cast ha1.ne : (a : ℂ) ≠ 1) hN
  simp only [ofReal_re] at hb
  have hdec : (N : ℝ) ^ (-a - 1) ≤ (N : ℝ) ^ (-a) := by
    rw [Real.rpow_sub hNp, Real.rpow_one, div_le_iff₀ hNp]
    exact le_mul_of_one_le_right (Real.rpow_nonneg hNp.le _) hN1
  have hC : 0 ≤ ‖(a : ℂ) * ((a : ℂ) + 1)‖ / (a + 1) := by positivity
  have he : (powerTailPrefix a N : ℂ) -
      (N : ℂ) ^ (1 - (a : ℂ)) / (1 - (a : ℂ)) - riemannZeta (a : ℂ) =
        powerSumRemainder (a : ℂ) N + (N : ℂ) ^ (-(a : ℂ)) / 2 := by
    rw [ofReal_powerTailPrefix]
    unfold powerSumRemainder kernel
    ring
  have hendpoint : ‖(N : ℂ) ^ (-(a : ℂ)) / 2‖ = (N : ℝ) ^ (-a) / 2 := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]
    norm_num [neg_re, ofReal_re]
  rw [he]
  calc
    _ ≤ ‖powerSumRemainder (a : ℂ) N‖ + ‖(N : ℂ) ^ (-(a : ℂ)) / 2‖ := norm_add_le _ _
    _ ≤ (‖(a : ℂ) * ((a : ℂ) + 1)‖ / (a + 1)) * (N : ℝ) ^ (-a) +
        (N : ℝ) ^ (-a) / 2 :=
      add_le_add (hb.trans (mul_le_mul_of_nonneg_left hdec hC)) hendpoint.le
    _ = _ := by ring

/-- The continued zeta value is the finite part of the literal power
prefix, with power-decaying error at every real cutoff at least one. -/
theorem exists_powerTailPrefix_real_finitePart_bound
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ‖(powerTailPrefix a X : ℂ) - (X : ℂ) ^ (1 - (a : ℂ)) / (1 - (a : ℂ)) -
        riemannZeta (a : ℂ)‖ ≤ C * X ^ (-a) := by
  let D := ‖(a : ℂ) * ((a : ℂ) + 1)‖ / (a + 1) + 1 / 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨(D + 2) * (2 : ℝ) ^ a, by positivity, ?_⟩
  intro X hX
  let N := ⌊X⌋₊
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
  have hhalf : X / 2 ≤ (N : ℝ) := by linarith only [hfloor, hN1]
  have hprefix : powerTailPrefix a X = powerTailPrefix a N := by
    simp only [powerTailPrefix, Nat.floor_natCast, N]
  have hnorm : ‖1 - (a : ℂ)‖ = 1 - a := by
    rw [show (1 : ℂ) - (a : ℂ) = ((1 - a : ℝ) : ℂ) by
        simp only [ofReal_sub, ofReal_one],
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [ha1])]
  have hgap : 0 < 1 - a := by linarith only [ha1]
  have hfp := _root_.RHTower.norm_cpow_natFloor_sub_cpow_le
    (s := 1 - (a : ℂ)) hX (by
      change ‖1 - (a : ℂ)‖ ≤ (N : ℝ)
      rw [hnorm]
      linarith only [ha, hN1])
  have hreal : (1 - (a : ℂ)).re - 1 = -a := by
    simp only [sub_re, one_re, ofReal_re]
    ring
  rw [hreal, hnorm] at hfp
  have hp : ‖((N : ℂ) ^ (1 - (a : ℂ)) - (X : ℂ) ^ (1 - (a : ℂ))) /
      (1 - (a : ℂ))‖ ≤ 2 * (N : ℝ) ^ (-a) := by
    rw [norm_div, hnorm, div_le_iff₀ hgap]
    simpa only [N, Complex.ofReal_natCast, mul_assoc, mul_comm, mul_left_comm] using hfp
  have hsplit : (powerTailPrefix a X : ℂ) -
      (X : ℂ) ^ (1 - (a : ℂ)) / (1 - (a : ℂ)) - riemannZeta (a : ℂ) =
        ((powerTailPrefix a N : ℂ) - (N : ℂ) ^ (1 - (a : ℂ)) /
          (1 - (a : ℂ)) - riemannZeta (a : ℂ)) +
        ((N : ℂ) ^ (1 - (a : ℂ)) - (X : ℂ) ^ (1 - (a : ℂ))) / (1 - (a : ℂ)) := by
    rw [hprefix]
    ring
  have hpow : (N : ℝ) ^ (-a) ≤ (2 : ℝ) ^ a * X ^ (-a) := by
    have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < X / 2)
      hhalf (neg_nonpos.mpr ha.le)
    apply hh.trans_eq
    rw [Real.div_rpow hX0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, inv_inv, mul_comm]
  rw [hsplit]
  calc
    _ ≤ ‖(powerTailPrefix a N : ℂ) - (N : ℂ) ^ (1 - (a : ℂ)) /
          (1 - (a : ℂ)) - riemannZeta (a : ℂ)‖ +
        ‖((N : ℂ) ^ (1 - (a : ℂ)) - (X : ℂ) ^ (1 - (a : ℂ))) /
          (1 - (a : ℂ))‖ := norm_add_le _ _
    _ ≤ D * (N : ℝ) ^ (-a) + 2 * (N : ℝ) ^ (-a) :=
      add_le_add (norm_powerTailPrefix_nat_finitePart_le ha ha1 hN) hp
    _ = (D + 2) * (N : ℝ) ^ (-a) := by ring
    _ ≤ (D + 2) * ((2 : ℝ) ^ a * X ^ (-a)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
