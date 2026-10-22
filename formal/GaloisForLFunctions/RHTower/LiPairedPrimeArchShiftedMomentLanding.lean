import GaloisForLFunctions.RHTower.LiPairedEndpointTraceLanding
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingXiSourceRate
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Paired Li coefficients as finite completed-source moment combinations

Let `w = 1 - 1 / rho` be the Li Cayley coordinate and let

`u = lambda / (1 + lambda / 4)`,

where `lambda = -1 / (rho - 1/2)^(2 : ℕ)` is the centered reciprocal-square coordinate.  Direct
Möbius algebra gives

`w + w⁻¹ = 2 - u`.

Therefore the paired Li atom is not merely an infinite raw reciprocal-trace series.  It is the
finite Chebyshev polynomial

`2 - 2 T_d(1 - u/2)`.

Its constant coefficient vanishes.  After proving absolute summability of every positive power,
we may sum this finite polynomial over the multiplicity-exact Xi divisor.  The existing shifted
moment transport at `y = 1/4` then replaces every divisor moment by its convergent completed
prime--Gamma source series.  This gives a source-only finite outer formula for every paired Li
coefficient and a source-only Li criterion.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

private theorem chebyshevT_eval_add_inv_div_two
    (w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval ((w + w⁻¹) / 2) =
      (w ^ n + (w⁻¹) ^ n) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
      have h1' :
          (Polynomial.Chebyshev.T ℂ ((n : ℤ) + 1)).eval ((w + w⁻¹) / 2) =
            (w ^ (n + 1) + (w⁻¹) ^ (n + 1)) / 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using h1
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega]
      rw [Polynomial.Chebyshev.T_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X, h0, h1']
      simp only [pow_succ]
      field_simp [hw]
      ring

/-- Polynomial expressing a paired Li atom in the quarter-shifted reciprocal-square coordinate. -/
def liShiftedMomentPolynomial (d : ℕ) : Polynomial ℂ :=
  C 2 - C 2 * (Polynomial.Chebyshev.T ℂ (d : ℤ)).comp
    (C 1 - C (1 / 2) * X)

theorem liShiftedMomentPolynomial_eval_of_cayleyTrace
    {w u : ℂ} (hw : w ≠ 0) (hwu : w + w⁻¹ = 2 - u) (d : ℕ) :
    (liShiftedMomentPolynomial d).eval u = liTerm w d := by
  rw [liShiftedMomentPolynomial]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_X]
  have harg : 1 - 1 / 2 * u = (w + w⁻¹) / 2 := by
    rw [hwu]
    ring
  rw [harg, chebyshevT_eval_add_inv_div_two w hw d]
  rw [liTerm]
  ring

theorem liShiftedMomentPolynomial_coeff_zero (d : ℕ) :
    (liShiftedMomentPolynomial d).coeff 0 = 0 := by
  have h := liShiftedMomentPolynomial_eval_of_cayleyTrace
    (w := (1 : ℂ)) (u := (0 : ℂ)) one_ne_zero (by norm_num) d
  rw [Polynomial.coeff_zero_eq_eval_zero]
  norm_num [liTerm] at h
  exact h

/-- The quarter-shifted reciprocal square is exactly the Cayley trace defect. -/
theorem xiRootW_add_inv_eq_two_sub_quarterShift (q : XiZeroCopy) :
    xiRootW (q.1 : ℂ) + (xiRootW (q.1 : ℂ))⁻¹ =
      2 - xiShiftedReciprocalSquare (1 / 4) q := by
  have hrho : (q.1 : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.zero_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  have hrhoOne : (q.1 : ℂ) ≠ 1 := by
    intro hone
    have him := congrArg Complex.im hone
    simp only [Complex.one_im] at him
    exact xi_divisor_support_im_ne_zero q.1 him
  have hhalf : (q.1 : ℂ) ≠ 1 / 2 := xi_divisor_support_ne_half q.1
  have hsource :
      1 + (((1 / 4 : ℝ) : ℂ) * xiZeroCopyReciprocalSquare q) ≠ 0 :=
    one_add_mul_xiZeroCopyReciprocalSquare_ne_zero (by norm_num) q
  have hprod : (q.1 : ℂ) * ((q.1 : ℂ) - 1) ≠ 0 :=
    mul_ne_zero hrho (sub_ne_zero.mpr hrhoOne)
  have htwo : 2 * (q.1 : ℂ) - 1 ≠ 0 := by
    intro h
    apply hhalf
    linear_combination h / 2
  have hquad :
      1 - (q.1 : ℂ) * 4 + (q.1 : ℂ) ^ (2 : ℕ) * 4 ≠ 0 := by
    rw [show 1 - (q.1 : ℂ) * 4 + (q.1 : ℂ) ^ (2 : ℕ) * 4 =
      (2 * (q.1 : ℂ) - 1) ^ (2 : ℕ) by ring]
    exact pow_ne_zero 2 htwo
  have hu : xiShiftedReciprocalSquare (1 / 4) q =
      -(1 / ((q.1 : ℂ) * ((q.1 : ℂ) - 1))) := by
    rw [xiShiftedReciprocalSquare, div_eq_iff hsource,
      xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare]
    norm_num
    simp only [inv_eq_one_div]
    field_simp [hhalf, hprod, hquad]
    have hqcancel :
        (1 - (q.1 : ℂ) * 4 + (q.1 : ℂ) ^ (2 : ℕ) * 4)⁻¹ *
          (1 - (q.1 : ℂ) * 4 + (q.1 : ℂ) ^ (2 : ℕ) * 4) = 1 :=
      inv_mul_cancel₀ hquad
    linear_combination 4 * hqcancel
  rw [xiRootW_eq_div hrho, inv_div, hu]
  field_simp [hrho, hrhoOne, hprod]
  ring

theorem liTerm_xiRootW_eq_liShiftedMomentPolynomial (q : XiZeroCopy) (d : ℕ) :
    liTerm (xiRootW (q.1 : ℂ)) d =
      (liShiftedMomentPolynomial d).eval (xiShiftedReciprocalSquare (1 / 4) q) := by
  symm
  apply liShiftedMomentPolynomial_eval_of_cayleyTrace
  · have hrho : (q.1 : ℂ) ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [Complex.zero_im] at him
      exact xi_divisor_support_im_ne_zero q.1 him
    have hrhoOne : (q.1 : ℂ) ≠ 1 := by
      intro hone
      have him := congrArg Complex.im hone
      simp only [Complex.one_im] at him
      exact xi_divisor_support_im_ne_zero q.1 him
    exact xiRootW_ne_zero hrho hrhoOne
  · exact xiRootW_add_inv_eq_two_sub_quarterShift q

/-- Every paired Li coefficient is a finite combination of quarter-shifted Xi reciprocal
moments.  The zero coefficient vanishes, so no divergent zeroth divisor moment occurs. -/
theorem xiLiPaired_eq_finset_liShiftedMomentPolynomial (d : ℕ) :
    xiLiPaired d =
      ∑ k ∈ Finset.range ((liShiftedMomentPolynomial d).natDegree + 1),
        (liShiftedMomentPolynomial d).coeff k *
          xiShiftedReciprocalMoment (1 / 4) (k - 1) := by
  let P : Polynomial ℂ := liShiftedMomentPolynomial d
  have hexpand (q : XiZeroCopy) :
      P.eval (xiShiftedReciprocalSquare (1 / 4) q) =
        ∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k * xiShiftedReciprocalSquare (1 / 4) q ^ k := by
    exact Polynomial.eval_eq_sum_range _
  have hsumm : ∀ k ∈ Finset.range (P.natDegree + 1),
      Summable (fun q : XiZeroCopy =>
        P.coeff k * xiShiftedReciprocalSquare (1 / 4) q ^ k) := by
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hzero : P.coeff 0 = 0 := by
        simpa only [P] using liShiftedMomentPolynomial_coeff_zero d
      simp [hzero]
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
      exact (summable_xiShiftedReciprocalSquare_pow
        (y := (1 / 4 : ℝ)) (by norm_num) j).mul_left _
  calc
    xiLiPaired d = ∑' q : XiZeroCopy,
        liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) d :=
      (hasSum_liTerm_xiZeroCopy d).tsum_eq.symm
    _ = ∑' q : XiZeroCopy,
        P.eval (xiShiftedReciprocalSquare (1 / 4) q) := by
      apply tsum_congr
      intro q
      simpa only [P] using liTerm_xiRootW_eq_liShiftedMomentPolynomial q d
    _ = ∑' q : XiZeroCopy, ∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * xiShiftedReciprocalSquare (1 / 4) q ^ k := by
      apply tsum_congr
      exact hexpand
    _ = ∑ k ∈ Finset.range (P.natDegree + 1), ∑' q : XiZeroCopy,
        P.coeff k * xiShiftedReciprocalSquare (1 / 4) q ^ k := by
      exact Summable.tsum_finsetSum hsumm
    _ = ∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * xiShiftedReciprocalMoment (1 / 4) (k - 1) := by
      apply Finset.sum_congr rfl
      intro k _
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have hzero : P.coeff 0 = 0 := by
          simpa only [P] using liShiftedMomentPolynomial_coeff_zero d
        simp [hzero]
      · rw [tsum_mul_left, xiShiftedReciprocalMoment,
          show k - 1 + 1 = k by omega]
    _ = ∑ k ∈ Finset.range ((liShiftedMomentPolynomial d).natDegree + 1),
        (liShiftedMomentPolynomial d).coeff k *
          xiShiftedReciprocalMoment (1 / 4) (k - 1) := by rfl

/-- Literal completed-source form of the finite Li landing. -/
def liPrimeArchShiftedMomentSource (d : ℕ) : ℂ :=
  ∑ k ∈ Finset.range ((liShiftedMomentPolynomial d).natDegree + 1),
    (liShiftedMomentPolynomial d).coeff k *
      primeArchShiftedReciprocalMoment (1 / 4) (k - 1)

/-- **Finite prime--Gamma landing for every paired Li coefficient.**  The right side is built
from the fixed completed prime--archimedean moment germ, contains no Xi divisor coordinate, and
has finite outer polynomial support. -/
theorem xiLiPaired_eq_liPrimeArchShiftedMomentSource (d : ℕ) :
    xiLiPaired d = liPrimeArchShiftedMomentSource d := by
  rw [xiLiPaired_eq_finset_liShiftedMomentPolynomial,
    liPrimeArchShiftedMomentSource]
  apply Finset.sum_congr rfl
  intro k _
  rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
    (y := (1 / 4 : ℝ)) (by norm_num) (by norm_num)]

/-- Source-only Li criterion: RH is equivalent to nonnegativity of the finite Chebyshev
combinations of the completed prime--Gamma shifted-moment tower. -/
theorem riemannHypothesis_iff_forall_re_liPrimeArchShiftedMomentSource_nonneg :
    RiemannHypothesis ↔
      ∀ d : ℕ, 0 ≤ (liPrimeArchShiftedMomentSource d).re := by
  rw [riemannHypothesis_iff_forall_re_xiLiPaired_nonneg]
  constructor <;> intro h d
  · rw [← xiLiPaired_eq_liPrimeArchShiftedMomentSource]
    exact h d
  · rw [xiLiPaired_eq_liPrimeArchShiftedMomentSource]
    exact h d

end

end RHTower
