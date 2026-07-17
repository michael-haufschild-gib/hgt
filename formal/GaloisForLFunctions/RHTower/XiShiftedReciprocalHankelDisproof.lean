import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovEquivalence

/-!
# Shifted reciprocal Xi Hankel disproof criterion

At a nonnegative squared radial base point `y`, translate a centered reciprocal-square Xi atom
`lambda` by the real Möbius map `lambda / (1 + y * lambda)`.  The unconditional positive real
part of every Xi atom makes this translation contractive, so all translated powers remain
absolutely summable.  Under RH every translated atom is positive real, and consequently every
finite shifted Hankel quadratic is nonnegative.

The contrapositive is the formal RH-false interface: a single strict negative finite quadratic
value for the translated moment tower proves `¬ RiemannHypothesis`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Real-base Möbius translation of one centered reciprocal-square Xi atom. -/
def xiShiftedReciprocalSquare (y : ℝ) (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q /
    (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q)

theorem one_add_mul_xiZeroCopyReciprocalSquare_re_ge_one
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    1 ≤ (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q).re := by
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hreal : 0 < (xiZeroCopyReciprocalSquare q).re := by
    simpa only [xiThermalNode] using xiThermalNode_pos q
  nlinarith

theorem one_add_mul_xiZeroCopyReciprocalSquare_ne_zero
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    1 + (y : ℂ) * xiZeroCopyReciprocalSquare q ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [Complex.zero_re] at hre
  linarith [one_add_mul_xiZeroCopyReciprocalSquare_re_ge_one hy q]

theorem one_le_norm_one_add_mul_xiZeroCopyReciprocalSquare
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    1 ≤ ‖1 + (y : ℂ) * xiZeroCopyReciprocalSquare q‖ := by
  exact (one_add_mul_xiZeroCopyReciprocalSquare_re_ge_one hy q).trans
    (Complex.re_le_norm _)

/-- Translation by a nonnegative real base point does not enlarge an Xi reciprocal atom. -/
theorem norm_xiShiftedReciprocalSquare_le
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    ‖xiShiftedReciprocalSquare y q‖ ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
  rw [xiShiftedReciprocalSquare, norm_div]
  exact div_le_self (norm_nonneg _)
    (one_le_norm_one_add_mul_xiZeroCopyReciprocalSquare hy q)

/-- Every positive power of the shifted reciprocal Xi divisor is absolutely summable. -/
theorem summable_xiShiftedReciprocalSquare_pow
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q ^ (n + 1)) := by
  apply Summable.of_norm_bounded
    (summable_xiZeroCopyReciprocalSquare_pow n).norm
  intro q
  rw [norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_xiShiftedReciprocalSquare_le hy q) (n + 1)

/-- The multiplicity-exact shifted reciprocal moment at squared base point `y`. -/
def xiShiftedReciprocalMoment (y : ℝ) (n : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, xiShiftedReciprocalSquare y q ^ (n + 1)

/-- Under RH a shifted reciprocal atom is still a strictly positive real number. -/
theorem xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    ∃ x : ℝ, 0 < x ∧ xiShiftedReciprocalSquare y q = (x : ℂ) := by
  obtain ⟨x, hx, hcoord⟩ :=
    xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
  have hcopy : xiZeroCopyReciprocalSquare q = (x : ℂ) := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact hcoord
  refine ⟨x / (1 + y * x), div_pos hx (by nlinarith), ?_⟩
  rw [xiShiftedReciprocalSquare, hcopy]
  push_cast
  rfl

/-- RH forces the real part of every individual shifted reciprocal moment to be nonnegative. -/
theorem xiShiftedReciprocalMoment_re_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    0 ≤ (xiShiftedReciprocalMoment y n).re := by
  have hsum := summable_xiShiftedReciprocalSquare_pow hy n
  rw [xiShiftedReciprocalMoment, Complex.re_tsum hsum]
  apply tsum_nonneg
  intro q
  obtain ⟨x, hx, hcoord⟩ :=
    xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis hRH hy q
  rw [hcoord]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- **Scalar formal RH-false endpoint.**  A negative real part of one shifted reciprocal moment
already contradicts RH; no parity adjustment or Hankel embedding is needed. -/
theorem not_riemannHypothesis_of_xiShiftedReciprocalMoment_re_neg
    {y : ℝ} (hy : 0 ≤ y) {n : ℕ}
    (hneg : (xiShiftedReciprocalMoment y n).re < 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact (not_lt_of_ge
    (xiShiftedReciprocalMoment_re_nonneg_of_riemannHypothesis hRH hy n)) hneg

/-- The finite real Hankel quadratic built from the translated reciprocal moments. -/
def xiShiftedReciprocalHankelQuadratic
    (y : ℝ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    c i * c j * (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ))).re

private theorem xiShiftedReciprocalHankelAtom_sum_eq
    {y : ℝ} {N : ℕ} (hRH : RiemannHypothesis) (hy : 0 ≤ y)
    (c : Fin N → ℝ) (q : XiZeroCopy) :
    (∑ i : Fin N, ∑ j : Fin N,
        c i * c j *
          (xiShiftedReciprocalSquare y q ^ ((i : ℕ) + (j : ℕ) + 1)).re) =
      (xiShiftedReciprocalSquare y q).re *
        (∑ i : Fin N, c i * (xiShiftedReciprocalSquare y q).re ^ (i : ℕ)) ^ 2 := by
  obtain ⟨x, hx, hcoord⟩ :=
    xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis hRH hy q
  rw [hcoord]
  simp_rw [← Complex.ofReal_pow, Complex.ofReal_re]
  calc
    (∑ i : Fin N, ∑ j : Fin N,
        c i * c j * x ^ ((i : ℕ) + (j : ℕ) + 1)) =
      ∑ i : Fin N, ∑ j : Fin N,
        (c i * x ^ (i : ℕ)) * (c j * x ^ (j : ℕ)) * x := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_succ, pow_add]
          ring
    _ = x * (∑ i : Fin N, c i * x ^ (i : ℕ)) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- RH forces every finite shifted reciprocal Hankel quadratic to be nonnegative. -/
theorem xiShiftedReciprocalHankelQuadratic_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y)
    {N : ℕ} (c : Fin N → ℝ) :
    0 ≤ xiShiftedReciprocalHankelQuadratic y c := by
  have hmoment (k : ℕ) :
      Summable (fun q : XiZeroCopy =>
        xiShiftedReciprocalSquare y q ^ (k + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy k
  have hmomentRe (k : ℕ) :
      Summable (fun q : XiZeroCopy =>
        (xiShiftedReciprocalSquare y q ^ (k + 1)).re) :=
    Complex.reCLM.summable (hmoment k)
  have hreal (k : ℕ) :
      (xiShiftedReciprocalMoment y k).re =
        ∑' q : XiZeroCopy,
          (xiShiftedReciprocalSquare y q ^ (k + 1)).re := by
    rw [xiShiftedReciprocalMoment, Complex.re_tsum (hmoment k)]
  have hswap :
      (∑' q : XiZeroCopy, ∑ i : Fin N, ∑ j : Fin N,
          c i * c j *
            (xiShiftedReciprocalSquare y q ^ ((i : ℕ) + (j : ℕ) + 1)).re) =
        ∑ i : Fin N, ∑ j : Fin N,
          c i * c j *
            ∑' q : XiZeroCopy,
              (xiShiftedReciprocalSquare y q ^ ((i : ℕ) + (j : ℕ) + 1)).re := by
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [tsum_mul_left]
      · intro j _
        exact (hmomentRe ((i : ℕ) + (j : ℕ))).mul_left (c i * c j)
    · intro i _
      exact summable_sum (fun j _ =>
        (hmomentRe ((i : ℕ) + (j : ℕ))).mul_left (c i * c j))
  rw [xiShiftedReciprocalHankelQuadratic]
  simp_rw [hreal]
  rw [← hswap]
  apply tsum_nonneg
  intro q
  rw [xiShiftedReciprocalHankelAtom_sum_eq hRH hy c q]
  exact mul_nonneg
    (le_of_lt (by
      obtain ⟨x, hx, hcoord⟩ :=
        xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis hRH hy q
      rw [hcoord]
      exact hx))
    (sq_nonneg _)

/-- **Formal RH-false endpoint.**  One strict negative finite quadratic value in the shifted
reciprocal moment tower contradicts RH. -/
theorem not_riemannHypothesis_of_xiShiftedReciprocalHankelQuadratic_neg
    {y : ℝ} (hy : 0 ≤ y) {N : ℕ} {c : Fin N → ℝ}
    (hneg : xiShiftedReciprocalHankelQuadratic y c < 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact (not_lt_of_ge
    (xiShiftedReciprocalHankelQuadratic_nonneg_of_riemannHypothesis
      hRH hy c)) hneg

end

end RHTower
