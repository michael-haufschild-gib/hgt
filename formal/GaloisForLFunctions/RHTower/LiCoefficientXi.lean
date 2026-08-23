import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.LiTermBound

noncomputable section

/-!
# The Cayley images of the Xi zeros and the paired Li coefficients

`w_ρ := 1 - 1/ρ` is the Cayley image of a Xi zero: it is unimodular exactly on the critical line,
inside the unit circle to the right of it and outside to the left, and the functional-equation
involution `ρ ↦ 1 - ρ` sends `w ↦ w⁻¹`.

This module records those facts, shows that the `w_ρ` stay in a fixed annulus (the Xi zeros are not
real and are locally finite, so their imaginary parts are bounded away from `0` off a finite set),
and defines the **paired** Li coefficients

`2 λ_n = Σ_ρ m_ρ (2 - w_ρⁿ - w_ρ⁻ⁿ)`,

an absolutely convergent sum by `LiTermBound`.  The easy half of Li's criterion — under RH every
`w_ρ` is unimodular, hence every coefficient is a nonnegative real — is proved here.

A real `w_ρ` would force a real `ρ`, which is impossible for a Xi zero; that is the fact the hard
half of the criterion turns into a contradiction.
-/

open Complex

namespace RHTower

/-- The Cayley image `w_ρ = 1 - 1/ρ` of a point.  On the critical line it is unimodular; to its
right it is inside the unit circle, to its left outside. -/
def xiRootW (ρ : ℂ) : ℂ := 1 - 1 / ρ

theorem xiRootW_sub_one (ρ : ℂ) : xiRootW ρ - 1 = -(1 / ρ) := by
  rw [xiRootW]; ring

theorem norm_xiRootW_sub_one (ρ : ℂ) : ‖xiRootW ρ - 1‖ = 1 / ‖ρ‖ := by
  rw [xiRootW_sub_one, norm_neg, norm_div, norm_one]

theorem xiRootW_eq_div {ρ : ℂ} (h : ρ ≠ 0) : xiRootW ρ = (ρ - 1) / ρ := by
  rw [xiRootW]
  field_simp

theorem norm_xiRootW {ρ : ℂ} (h : ρ ≠ 0) : ‖xiRootW ρ‖ = ‖ρ - 1‖ / ‖ρ‖ := by
  rw [xiRootW_eq_div h, norm_div]

theorem xiRootW_ne_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : xiRootW ρ ≠ 0 := by
  rw [xiRootW_eq_div h0, div_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr h1, h0⟩

theorem xiRootW_one_sub {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    xiRootW (1 - ρ) = (xiRootW ρ)⁻¹ := by
  have hs : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [xiRootW_eq_div hs, xiRootW_eq_div h0, inv_div]
  field_simp
  ring

theorem xiRootW_conj (ρ : ℂ) : xiRootW ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (xiRootW ρ) := by
  rw [xiRootW, xiRootW, map_sub, map_one, map_div₀, map_one]

/-- `‖w_ρ‖ = 1` exactly on the critical line. -/
theorem norm_xiRootW_eq_one_iff {ρ : ℂ} (h : ρ ≠ 0) : ‖xiRootW ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hpos : 0 < ‖ρ‖ := norm_pos_iff.mpr h
  rw [norm_xiRootW h, div_eq_one_iff_eq (ne_of_gt hpos)]
  constructor
  · intro hEq
    have h2 : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by rw [hEq]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
    nlinarith
  · intro hre
    have h2 : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      nlinarith
    have hnn1 : (0:ℝ) ≤ ‖ρ - 1‖ := norm_nonneg _
    have hnn2 : (0:ℝ) ≤ ‖ρ‖ := norm_nonneg _
    nlinarith

/-- A real Cayley image comes only from a real point. -/
theorem im_eq_zero_of_xiRootW_im_eq_zero {ρ : ℂ} (h : ρ ≠ 0) (hw : (xiRootW ρ).im = 0) :
    ρ.im = 0 := by
  have h1 : (1 / ρ).im = 0 := by
    have := congrArg Complex.im (xiRootW_sub_one ρ)
    simp only [Complex.sub_im, Complex.one_im, Complex.neg_im, hw] at this
    linarith
  rw [Complex.div_im] at h1
  simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div] at h1
  have hns : Complex.normSq ρ ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using h
  field_simp at h1
  linarith

theorem finite_xiDivisorSupport_near_half :
    {ρ : XiDivisorSupport | ‖(ρ : ℂ) - 1 / 2‖ ≤ 1}.Finite := by
  refine Set.Finite.subset (xi_central_reciprocal_square_finite_norm_ge (r := 1) one_pos) ?_
  intro ρ hρ
  have hle : ‖(ρ : ℂ) - 1 / 2‖ ≤ 1 := hρ
  have hne : ((ρ : ℂ) - 1 / 2) ≠ 0 := by
    intro h
    exact xi_divisor_support_ne_half ρ (sub_eq_zero.mp h)
  show (1 : ℝ) ≤ ‖xiCentralReciprocalSquare (ρ : ℂ)‖
  rw [xiCentralReciprocalSquare, norm_neg, norm_pow, norm_inv]
  have hpos : 0 < ‖(ρ : ℂ) - 1 / 2‖ := norm_pos_iff.mpr hne
  have h1 : (1 : ℝ) ≤ ‖(ρ : ℂ) - 1 / 2‖⁻¹ := (one_le_inv₀ hpos).mpr hle
  nlinarith

/-- The Cayley images of the Xi zeros stay in a fixed annulus. -/
theorem exists_bound_xiRootW :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ρ : XiDivisorSupport,
      max ‖xiRootW (ρ : ℂ)‖ ‖xiRootW (ρ : ℂ)‖⁻¹ ≤ M := by
  classical
  set f : XiDivisorSupport → ℝ :=
    fun ρ => max ‖xiRootW (ρ : ℂ)‖ ‖xiRootW (ρ : ℂ)‖⁻¹ with hf
  have hS := finite_xiDivisorSupport_near_half
  obtain ⟨B, hB⟩ := (hS.image f).bddAbove
  refine ⟨max (max B 3) 1, le_max_right _ _, fun ρ => ?_⟩
  by_cases hρ : ‖(ρ : ℂ) - 1 / 2‖ ≤ 1
  · have hmem : f ρ ∈ f '' {ρ : XiDivisorSupport | ‖(ρ : ℂ) - 1 / 2‖ ≤ 1} := ⟨ρ, hρ, rfl⟩
    exact le_trans (hB hmem) (le_trans (le_max_left _ _) (le_max_left _ _))
  · push Not at hρ
    have hsq := xi_divisor_support_centered_re_sq_lt_quarter ρ
    have hnorm : ‖(ρ : ℂ) - 1 / 2‖ ^ 2 = ((ρ : ℂ).re - 1 / 2) ^ 2 + (ρ : ℂ).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      norm_num
      ring
    have hgt : (1 : ℝ) < ‖(ρ : ℂ) - 1 / 2‖ ^ 2 := by nlinarith [norm_nonneg ((ρ : ℂ) - 1 / 2)]
    have himsq : (3 : ℝ) / 4 < (ρ : ℂ).im ^ 2 := by linarith [hnorm, hsq]
    have hrho : (1 : ℝ) / 2 < ‖(ρ : ℂ)‖ := by
      have h1 : |(ρ : ℂ).im| ≤ ‖(ρ : ℂ)‖ := Complex.abs_im_le_norm _
      nlinarith [abs_nonneg ((ρ : ℂ).im), sq_abs ((ρ : ℂ).im)]
    have hrho1 : (1 : ℝ) / 2 < ‖(ρ : ℂ) - 1‖ := by
      have h1 : |((ρ : ℂ) - 1).im| ≤ ‖(ρ : ℂ) - 1‖ := Complex.abs_im_le_norm _
      have h2 : ((ρ : ℂ) - 1).im = (ρ : ℂ).im := by simp
      rw [h2] at h1
      nlinarith [abs_nonneg ((ρ : ℂ).im), sq_abs ((ρ : ℂ).im)]
    have h0 : (ρ : ℂ) ≠ 0 := by
      intro h
      rw [h] at hrho
      simp at hrho
      linarith
    have h1 : (ρ : ℂ) ≠ 1 := by
      intro h
      rw [h] at hrho1
      simp at hrho1
      linarith
    have hw : ‖xiRootW (ρ : ℂ)‖ = ‖(ρ : ℂ) - 1‖ / ‖(ρ : ℂ)‖ := norm_xiRootW h0
    have hwinv : ‖xiRootW (ρ : ℂ)‖⁻¹ = ‖(ρ : ℂ)‖ / ‖(ρ : ℂ) - 1‖ := by
      rw [hw, inv_div]
    have hb1 : ‖xiRootW (ρ : ℂ)‖ ≤ 3 := by
      rw [hw, div_le_iff₀ (by linarith)]
      have := norm_sub_le ((ρ : ℂ)) (1 : ℂ)
      simp only [norm_one] at this
      linarith
    have hb2 : ‖xiRootW (ρ : ℂ)‖⁻¹ ≤ 3 := by
      rw [hwinv, div_le_iff₀ (by linarith)]
      have h := norm_sub_le ((ρ : ℂ) - 1) (-1 : ℂ)
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at h
      linarith
    have : f ρ ≤ 3 := max_le hb1 hb2
    exact le_trans this (le_trans (le_max_right _ _) (le_max_left _ _))

/-! ## The paired Li coefficients of the Xi divisor -/

/-- The multiplicity-weighted paired Li summand at a Xi zero. -/
def xiLiPairedTerm (n : ℕ) (ρ : XiDivisorSupport) : ℂ :=
  (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) * liTerm (xiRootW (ρ : ℂ)) n

/-- **Twice Li's coefficient** `2λ_n = Σ_ρ m_ρ (2 - w_ρⁿ - w_ρ⁻ⁿ)`, as an absolutely convergent
sum over the Xi divisor.  The pairing `ρ ↦ 1 - ρ` (which sends `w ↦ w⁻¹`) is what makes the sum
absolute; Li's own `Σ_ρ (1 - w_ρⁿ)` converges only symmetrically. -/
def xiLiPaired (n : ℕ) : ℂ := ∑' ρ : XiDivisorSupport, xiLiPairedTerm n ρ

theorem summable_xiLiPairedTerm (n : ℕ) : Summable (xiLiPairedTerm n) := by
  obtain ⟨M, hM1, hM⟩ := exists_bound_xiRootW
  refine Summable.of_norm_bounded
    (xi_zero_multiplicity_inv_sq_summable.mul_left ((n : ℝ) ^ 2 * M ^ n)) fun ρ => ?_
  have hmult : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast (xi_divisor_pos_on_support ρ).le
  have him : (ρ : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero ρ
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have h1 : (ρ : ℂ) ≠ 1 := by
    intro h
    rw [h] at him
    simp at him
  have hwne : xiRootW (ρ : ℂ) ≠ 0 := xiRootW_ne_zero h0 h1
  have hpos : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.mpr h0
  have hbase := norm_liTerm_le hwne n
  rw [norm_xiRootW_sub_one] at hbase
  have hMn : max ‖xiRootW (ρ : ℂ)‖ ‖xiRootW (ρ : ℂ)‖⁻¹ ^ n ≤ M ^ n :=
    pow_le_pow_left₀ (le_trans (norm_nonneg _) (le_max_left _ _)) (hM ρ) n
  have hsq : (1 / ‖(ρ : ℂ)‖) ^ 2 = 1 / ‖(ρ : ℂ)‖ ^ 2 := by
    rw [div_pow, one_pow]
  rw [xiLiPairedTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmult]
  have hfin : ‖liTerm (xiRootW (ρ : ℂ)) n‖ ≤ (n : ℝ) ^ 2 * M ^ n * (1 / ‖(ρ : ℂ)‖ ^ 2) := by
    refine le_trans hbase ?_
    rw [hsq]
    have hnn : (0 : ℝ) ≤ 1 / ‖(ρ : ℂ)‖ ^ 2 := by positivity
    have hnn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    rw [mul_assoc, mul_assoc]
    gcongr
  calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖liTerm (xiRootW (ρ : ℂ)) n‖
      ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          ((n : ℝ) ^ 2 * M ^ n * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hfin hmult
    _ = (n : ℝ) ^ 2 * M ^ n * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) /
          ‖(ρ : ℂ)‖ ^ 2) := by ring

/-- **The easy half of Li's criterion.**  Under RH every zero has `‖w_ρ‖ = 1`, so every paired Li
coefficient is a nonnegative real. -/
theorem re_xiLiPaired_nonneg_of_rh (hRH : RiemannHypothesis) (n : ℕ) :
    0 ≤ (xiLiPaired n).re := by
  rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm n)]
  refine tsum_nonneg fun ρ => ?_
  have him : (ρ : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero ρ
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have hre : (ρ : ℂ).re = 1 / 2 := xi_divisor_support_re_eq_half_of_rh hRH ρ
  have hw : ‖xiRootW (ρ : ℂ)‖ = 1 := (norm_xiRootW_eq_one_iff h0).mpr hre
  have hmult : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast (xi_divisor_pos_on_support ρ).le
  rw [xiLiPairedTerm, Complex.re_ofReal_mul]
  exact mul_nonneg hmult (re_liTerm_nonneg_of_norm_eq_one hw n)

end RHTower
