import GaloisForLFunctions.RHTower.LiCoefficientXi
import GaloisForLFunctions.RHTower.LiPositivityFails
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
noncomputable section

/-!
# Li's criterion

`RH ↔ 2λ_n ≥ 0 for every n`, where

`2 λ_n = Σ_ρ m_ρ (2 - w_ρⁿ - w_ρ⁻ⁿ)`,  `w_ρ = 1 - 1/ρ`,

the paired form of Li's coefficients `λ_n = Σ_ρ [1 - (1-1/ρ)ⁿ]` (the pairing `ρ ↦ 1-ρ` sends
`w ↦ w⁻¹`, so the paired sum is `2λ_n` and converges absolutely).

The forward direction is `LiCoefficientXi`: under RH every `w_ρ` is unimodular and the summand is
`2 - 2 Re(w_ρⁿ) ≥ 0`.  The converse is the abstract theorem of `LiPositivityFails` applied to the
modulus-`≥1` representative of `{w_ρ, w_ρ⁻¹}`: if some zero is off the critical line then some
`2λ_n` is negative.  No analytic continuation, no Vivanti--Pringsheim, no Hadamard product — only
the size bound of `LiTermBound` and a pigeonhole on a finite product of unit circles.
-/

open Complex
namespace RHTower

/-- The representative of `{w_ρ, w_ρ⁻¹}` of modulus at least one. -/
def xiRootV (ρ : ℂ) : ℂ := if 1 ≤ ‖xiRootW ρ‖ then xiRootW ρ else (xiRootW ρ)⁻¹

theorem liTerm_xiRootV (ρ : ℂ) (n : ℕ) : liTerm (xiRootV ρ) n = liTerm (xiRootW ρ) n := by
  rw [xiRootV]
  split
  · rfl
  · exact liTerm_inv _ n

theorem norm_xiRootV {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    ‖xiRootV ρ‖ = max ‖xiRootW ρ‖ ‖xiRootW ρ‖⁻¹ := by
  have hne : xiRootW ρ ≠ 0 := xiRootW_ne_zero h0 h1
  have hpos : 0 < ‖xiRootW ρ‖ := norm_pos_iff.mpr hne
  rw [xiRootV]
  split
  · rename_i hcase
    rw [max_eq_left]
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  · rename_i hcase
    push Not at hcase
    rw [norm_inv, max_eq_right]
    have hinv : 1 ≤ ‖xiRootW ρ‖⁻¹ := by
      rw [one_le_inv₀ hpos]
      exact hcase.le
    linarith
theorem one_le_norm_xiRootV {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : 1 ≤ ‖xiRootV ρ‖ := by
  have hne : xiRootW ρ ≠ 0 := xiRootW_ne_zero h0 h1
  have hpos : 0 < ‖xiRootW ρ‖ := norm_pos_iff.mpr hne
  rw [norm_xiRootV h0 h1]
  rcases le_or_gt 1 ‖xiRootW ρ‖ with h | h
  · exact le_trans h (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [one_le_inv₀ hpos]
    exact h.le


theorem norm_xiRootV_sub_one_le {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) {M : ℝ} (hM : 1 ≤ M)
    (hb : max ‖xiRootW ρ‖ ‖xiRootW ρ‖⁻¹ ≤ M) :
    ‖xiRootV ρ - 1‖ ≤ M * ‖xiRootW ρ - 1‖ := by
  have hne : xiRootW ρ ≠ 0 := xiRootW_ne_zero h0 h1
  have hpos : 0 < ‖xiRootW ρ‖ := norm_pos_iff.mpr hne
  rw [xiRootV]
  split
  · nlinarith [norm_nonneg (xiRootW ρ - 1)]
  · have hval : (xiRootW ρ)⁻¹ - 1 = -((xiRootW ρ - 1) / xiRootW ρ) := by
      rw [div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hne]
      ring
    rw [hval, norm_neg, norm_div, div_le_iff₀ hpos]
    have hle : ‖xiRootW ρ‖⁻¹ ≤ M := le_trans (le_max_right _ _) hb
    have h1' : 1 ≤ M * ‖xiRootW ρ‖ := by
      have hmul := mul_le_mul_of_nonneg_right hle hpos.le
      rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at hmul
    nlinarith [norm_nonneg (xiRootW ρ - 1)]

/-- **Li's criterion, hard half.**  Nonnegativity of every paired Li coefficient forces RH. -/
theorem riemannHypothesis_of_forall_re_xiLiPaired_nonneg
    (h : ∀ n : ℕ, 0 ≤ (xiLiPaired n).re) : RiemannHypothesis := by
  by_contra hRH
  rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hRH
  push Not at hRH
  obtain ⟨ρ₁, hρ₁zero, hρ₁re⟩ := hRH
  set ρ₀ : XiDivisorSupport := ⟨ρ₁, mem_xi_divisor_support_of_eq_zero hρ₁zero⟩ with hρ₀def
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  -- basic facts about every zero
  have hne0 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 0 := by
    intro ρ h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  have hne1 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 1 := by
    intro ρ h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  have hmult : ∀ ρ : XiDivisorSupport,
      (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    intro ρ
    have := xi_divisor_pos_on_support ρ
    exact_mod_cast this
  have hvnorm : ∀ ρ : XiDivisorSupport, 1 ≤ ‖xiRootV (ρ : ℂ)‖ :=
    fun ρ => one_le_norm_xiRootV (hne0 ρ) (hne1 ρ)
  have hvM : ∀ ρ : XiDivisorSupport, ‖xiRootV (ρ : ℂ)‖ ≤ M := by
    intro ρ
    rw [norm_xiRootV (hne0 ρ) (hne1 ρ)]
    exact hMb ρ
  have hsum : Summable fun ρ : XiDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) := by
    refine Summable.of_nonneg_of_le (fun ρ => by nlinarith [hmult ρ, sq_nonneg ‖xiRootV (ρ:ℂ) - 1‖])
      (fun ρ => ?_) (xi_zero_multiplicity_inv_sq_summable.mul_left (M ^ (2 : ℕ)))
    have hb := norm_xiRootV_sub_one_le (hne0 ρ) (hne1 ρ) hM1 (hMb ρ)
    have hw1 : ‖xiRootW (ρ : ℂ) - 1‖ = 1 / ‖(ρ : ℂ)‖ := norm_xiRootW_sub_one _
    rw [hw1] at hb
    have hnn : (0 : ℝ) ≤ ‖xiRootV (ρ : ℂ) - 1‖ := norm_nonneg _
    have hsq : ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
      have hM0 : (0 : ℝ) ≤ M := by linarith
      have hmul : (M * (1 / ‖(ρ : ℂ)‖)) ^ (2 : ℕ) = M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
        rw [mul_pow, div_pow, one_pow]
      rw [← hmul]
      nlinarith [mul_nonneg hM0 (by positivity : (0:ℝ) ≤ 1 / ‖(ρ : ℂ)‖)]
    calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)
        ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ))) := by
          have := hmult ρ
          nlinarith
      _ = M ^ (2 : ℕ) * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
          ring
  -- the bad zero
  have hbad : 1 < ‖xiRootV ((ρ₀ : XiDivisorSupport) : ℂ)‖ := by
    have hnorm : ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ ≠ 1 := by
      intro hEq
      exact hρ₁re ((norm_xiRootW_eq_one_iff (hne0 ρ₀)).mp hEq)
    have hposw : 0 < ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ :=
      norm_pos_iff.mpr (xiRootW_ne_zero (hne0 ρ₀) (hne1 ρ₀))
    rw [norm_xiRootV (hne0 ρ₀) (hne1 ρ₀)]
    rcases lt_trichotomy ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ 1 with hlt | heq | hgt
    · refine lt_of_lt_of_le ?_ (le_max_right _ _)
      rw [one_lt_inv₀ hposw]
      exact hlt
    · exact absurd heq hnorm
    · exact lt_of_lt_of_le hgt (le_max_left _ _)
  obtain ⟨n, hn⟩ := exists_re_tsum_liTerm_neg hmult hvnorm hvM hsum hbad
  refine absurd (h n) (not_le.mpr ?_)
  have hre : (xiLiPaired n).re
      = ∑' ρ : XiDivisorSupport,
          ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (liTerm (xiRootV (ρ : ℂ)) n).re := by
    rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm n)]
    refine tsum_congr fun ρ => ?_
    rw [xiLiPairedTerm, Complex.re_ofReal_mul, liTerm_xiRootV]
  rw [hre]
  exact hn

/-- **Li's criterion.**  RH is equivalent to nonnegativity of every paired Li coefficient
`2λ_n = Σ_ρ m_ρ (2 - w_ρⁿ - w_ρ⁻ⁿ)`. -/
theorem riemannHypothesis_iff_forall_re_xiLiPaired_nonneg :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (xiLiPaired n).re :=
  ⟨fun hRH n => re_xiLiPaired_nonneg_of_rh hRH n,
    riemannHypothesis_of_forall_re_xiLiPaired_nonneg⟩

end RHTower
