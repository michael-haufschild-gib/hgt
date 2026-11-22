import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.CharacterLocalMoments
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.ExceptionalZeroBounds.NativeRightBound

/-! The local logarithmic derivative bounds multiplicity in shrinking zero disks. -/

open Complex Finset Classical WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

private theorem re_nat_div_eq (m : ℕ) (z : ℂ) :
    ((m : ℂ) / z).re = (m : ℝ) * z.re / ‖z‖ ^ 2 := by
  rw [div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, inv_re,
    normSq_eq_norm_sq, mul_div_assoc]

theorem local_reciprocal_square_mass {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (t r C D : ℝ) (hr : 0 < r) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ ρ ∈ Z, ρ.re < 1)
    (hD : ‖negLD χ ((↑(1 + r) : ℂ) + t * I)‖ ≤ 1 / r + D)
    (hE : ‖negLD χ ((↑(1 + r) : ℂ) + t * I) -
      (if χ = 1 then 1 / (((↑(1 + r) : ℂ) + t * I) - 1) else 0) +
      ∑ ρ ∈ Z, (m ρ : ℂ) / (((↑(1 + r) : ℂ) + t * I) - ρ)‖ ≤ C) :
    (∑ ρ ∈ Z, (m ρ : ℝ) / ‖((↑(1 + r) : ℂ) + t * I) - ρ‖ ^ 2) ≤
      (2 / r + D + C) / r := by
  let s : ℂ := ((1 + r : ℝ) : ℂ) + t * I
  let P : ℂ := if χ = 1 then 1 / (s - 1) else 0
  have hs : s.re = 1 + r := by simp [s]
  have hP : P.re ≤ 1 / r := by
    dsimp only [P]
    split_ifs
    · have hnorm : r ≤ ‖s - 1‖ := by
        have h := re_le_norm (s - 1)
        rw [sub_re, hs, one_re] at h
        linarith only [h]
      exact (re_le_norm _).trans (by
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hr hnorm)
    · rw [zero_re]
      positivity
  have hneg : -(negLD χ s).re ≤ 1 / r + D := by
    have h := re_le_norm (-negLD χ s)
    rw [neg_re, norm_neg] at h
    exact h.trans hD
  have hsum : (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re ≤ 2 / r + D + C := by
    have h := (re_le_norm _).trans hE
    change (negLD χ s - P + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re ≤ C at h
    rw [add_re, sub_re] at h
    rw [show (2 : ℝ) / r = 1 / r + 1 / r by ring]
    linarith only [h, hP, hneg]
  apply (le_div_iff₀ hr).mpr
  rw [mul_comm _ r, mul_sum]
  refine le_trans (sum_le_sum (g := fun ρ => ((m ρ : ℂ) / (s - ρ)).re) ?_) ?_
  · intro ρ hρ
    have hgap : r ≤ (s - ρ).re := by
      rw [sub_re, hs]
      linarith only [hZ ρ hρ]
    rw [re_nat_div_eq, ← mul_div_assoc]
    have hm : (0 : ℝ) ≤ m ρ := Nat.cast_nonneg _
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hgap hm).trans_eq (mul_comm _ _))
      (by positivity)
  · rw [← Complex.re_sum]
    exact hsum

/-- Uniform zero counts with analytic multiplicity in a radius `r` about the one-line. -/
theorem small_disc_zero_count :
    ∃ A : ℝ, 0 < A ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (t r : ℝ),
      0 < r → r ≤ 1 / 25 → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, ‖ρ - (1 + t * I)‖ ≤ r ∧ IsLZero χ ρ) →
      (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
        A * (1 + r * Real.log ((M : ℝ) * (|t| + 2))) := by
  obtain ⟨C, hC, hlocal⟩ := deuring_heilbronn_local
  obtain ⟨D, hD, hderiv⟩ := l_log_deriv_right
  refine ⟨8 + 8 * D + 4 * C, by positivity, ?_⟩
  intro M _ χ t r hr hr' S hS
  let L := Real.log ((M : ℝ) * (|t| + 2))
  let s : ℂ := ((1 + r : ℝ) : ℂ) + t * I
  have hs : s.re = 1 + r := by simp [s]
  have hs₁ : 1 < s.re := by rw [hs]; linarith only [hr]
  obtain ⟨Z, m, hZ, -, horder, hZright, -, hE⟩ := hlocal M χ t
  have hclose : ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 := by
    have he : s - ((26 / 25 : ℂ) + t * I) = ((r - 1 / 25 : ℝ) : ℂ) := by
      dsimp only [s]
      push_cast
      ring
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hr'])]
    linarith only [hr]
  have hsum := local_reciprocal_square_mass χ t r (C * L) D hr Z m hZright
    (by
      have h := hderiv M χ s hs₁
      rw [hs, add_sub_cancel_left] at h
      exact h)
    (by simpa only [zero_add, pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one, div_one,
      one_mul, mul_one, iteratedDeriv_zero] using hE 0 s hs₁ hclose)
  have hZsub : S ⊆ Z := by
    intro ρ hρ
    obtain ⟨hd, hz⟩ := hS ρ hρ
    refine (hZ ρ).mpr ⟨?_, hz⟩
    have he : ρ - ((26 / 25 : ℂ) + t * I) = (ρ - (1 + t * I)) - (1 / 25 : ℂ) := by ring
    rw [he]
    have h := norm_sub_le (ρ - (1 + t * I)) (1 / 25)
    have hn : ‖(1 / 25 : ℂ)‖ = 1 / 25 := by norm_num [norm_div]
    rw [hn] at h
    linarith only [h, hd, hr']
  have hsmall : (∑ ρ ∈ S, (m ρ : ℝ)) ≤
      4 * r ^ 2 * ∑ ρ ∈ Z, (m ρ : ℝ) / ‖s - ρ‖ ^ 2 := by
    rw [mul_sum]
    refine (sum_le_sum (g := fun ρ => 4 * r ^ 2 * ((m ρ : ℝ) / ‖s - ρ‖ ^ 2)) ?_).trans
      (sum_le_sum_of_subset_of_nonneg hZsub (fun _ _ _ => by positivity))
    intro ρ hρ
    have hnorm : ‖s - ρ‖ ≤ 2 * r := by
      have he : s - ρ = (r : ℂ) - (ρ - (1 + t * I)) := by dsimp only [s]; push_cast; ring
      rw [he]
      have h := norm_sub_le ((r : ℝ) : ℂ) (ρ - (1 + t * I))
      rw [norm_real, Real.norm_of_nonneg hr.le] at h
      linarith only [h, (hS ρ hρ).1]
    have hn : 0 < ‖s - ρ‖ := by
      have h := re_le_norm (s - ρ)
      rw [sub_re, hs] at h
      linarith only [h, hr, hZright ρ (hZsub hρ)]
    rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hn)]
    have hsq := pow_le_pow_left₀ hn.le hnorm 2
    nlinarith only [mul_le_mul_of_nonneg_left hsq (show 0 ≤ (m ρ : ℝ) by positivity)]
  have hL : (1 / 2 : ℝ) ≤ L :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (dhl_X M t))
  have hLr : 0 ≤ r * L := mul_nonneg hr.le (by linarith only [hL])
  calc
    _ = ∑ ρ ∈ S, (m ρ : ℝ) := sum_congr rfl fun ρ hρ => by rw [horder ρ (hZsub hρ)]
    _ ≤ 4 * r ^ 2 * ((2 / r + D + C * L) / r) :=
      hsmall.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = 8 + 4 * r * D + 4 * C * (r * L) := by field_simp [hr.ne'] <;> ring
    _ ≤ _ := by
      change 8 + 4 * r * D + 4 * C * (r * L) ≤ (8 + 8 * D + 4 * C) * (1 + r * L)
      nlinarith only [mul_le_mul_of_nonneg_left hL (mul_nonneg hr.le hD),
        mul_nonneg (by positivity : 0 ≤ 8 + 4 * C) hLr, hD, hC.le]

end QH.PrimeProgressions
