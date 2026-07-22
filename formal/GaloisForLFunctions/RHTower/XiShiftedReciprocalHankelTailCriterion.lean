import GaloisForLFunctions.RHTower.TraceHankelConverse
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelDisproof
import GaloisForLFunctions.RHTower.XiSquaredSeamTailFromSixtyFour
import GaloisForLFunctions.RHTower.PrimeArchShiftThirteenCircleCone
import GaloisForLFunctions.RHTower.XiEndpointCentralMomentBoundaryValue
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Cofinal fixed-shift Hankel tails already force RH

For every nonnegative real Möbius shift and every finite cutoff, positivity of the shifted
reciprocal Hankel tower after that cutoff is equivalent to RH.  The converse uses the abstract
trace-class principal-ideal separator from `TraceHankelConverse`: deleting the first `2M`
moments is multiplication of every polynomial test by `X^M`, which cannot hide a nonreal,
nonzero atom.

At shift `y = 1` the translated reciprocal atom is exactly the fixed squared-Xi seam coordinate.
Thus any one cofinal shifted Hankel cone discharges the sole remaining dyadic tail from power `64`.
The separate power-32 annulus interface is redundant by the tail-from-64 phase collapse.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Polynomial trace--Hankel term for the Möbius-shifted reciprocal Xi spectrum. -/
def xiShiftedReciprocalTraceHankelTerm (y : ℝ) (p : Polynomial ℝ)
    (q : XiZeroCopy) : ℂ :=
  xiShiftedReciprocalSquare y q *
    evalRealPolynomial p (xiShiftedReciprocalSquare y q) ^ 2

/-- Polynomial trace--Hankel value for the Möbius-shifted reciprocal Xi spectrum. -/
def xiShiftedReciprocalTraceHankel (y : ℝ) (p : Polynomial ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiShiftedReciprocalTraceHankelTerm y p q

/-- Every shifted polynomial trace test is absolutely summable. -/
theorem summable_xiShiftedReciprocalTraceHankelTerm
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) :
    Summable (xiShiftedReciprocalTraceHankelTerm y p) := by
  let lam : XiZeroCopy → ℂ := xiShiftedReciprocalSquare y
  let r : Polynomial ℂ := (p.map (algebraMap ℝ ℂ)) ^ 2
  let moment : ℕ → XiZeroCopy → ℂ := fun k q => lam q ^ (k + 1)
  have hmoment (k : ℕ) : Summable (moment k) := by
    simpa only [lam, moment] using summable_xiShiftedReciprocalSquare_pow hy k
  have hfin : ∀ s : Finset ℕ,
      Summable (fun q => ∑ k ∈ s, r.coeff k * moment k q) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hks ih =>
        simpa only [Finset.sum_insert hks] using
          ((hmoment k).mul_left (r.coeff k)).add ih
  have hsum := hfin (Finset.range (r.natDegree + 1))
  apply hsum.congr
  intro q
  symm
  rw [xiShiftedReciprocalTraceHankelTerm]
  change lam q * evalRealPolynomial p (lam q) ^ 2 = _
  calc
    lam q * evalRealPolynomial p (lam q) ^ 2 = lam q * r.eval (lam q) := by
      simp [r, evalRealPolynomial]
    _ = lam q *
        (∑ k ∈ Finset.range (r.natDegree + 1), r.coeff k * lam q ^ k) := by
      rw [Polynomial.eval_eq_sum_range]
    _ = ∑ k ∈ Finset.range (r.natDegree + 1), r.coeff k * moment k q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [moment]
      ring

/-- Shifted atoms converge to zero off a finite set. -/
theorem xiShiftedReciprocalSquare_finite_norm_ge
    {y r : ℝ} (hy : 0 ≤ y) (hr : 0 < r) :
    {q : XiZeroCopy | r ≤ ‖xiShiftedReciprocalSquare y q‖}.Finite := by
  have hsum : Summable (xiShiftedReciprocalSquare y) := by
    simpa using summable_xiShiftedReciprocalSquare_pow hy 0
  have hevent : ∀ᶠ q : XiZeroCopy in cofinite,
      ‖xiShiftedReciprocalSquare y q‖ < r :=
    hsum.tendsto_cofinite_zero.norm.eventually_lt_const (by simpa using hr)
  rw [Filter.eventually_cofinite] at hevent
  simpa only [not_lt] using hevent

theorem xiShiftedReciprocalSquare_ne_zero
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare y q ≠ 0 := by
  rw [xiShiftedReciprocalSquare, div_ne_zero_iff]
  exact ⟨by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact xiCentralReciprocalSquare_ne_zero q.1,
    one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q⟩

/-- Möbius translation preserves the imaginary coordinate up to a strictly positive factor. -/
theorem xiShiftedReciprocalSquare_im_formula
    {y : ℝ} (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q).im =
      (xiZeroCopyReciprocalSquare q).im /
        Complex.normSq (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q) := by
  rw [xiShiftedReciprocalSquare, Complex.div_im]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im,
    Complex.mul_im, zero_add]
  ring

/-- At every nonnegative shift, a translated Xi atom is real exactly when the original
reciprocal-square atom is real. -/
theorem xiShiftedReciprocalSquare_im_eq_zero_iff
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q).im = 0 ↔
      (xiZeroCopyReciprocalSquare q).im = 0 := by
  rw [xiShiftedReciprocalSquare_im_formula]
  have hden : Complex.normSq
      (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr
      (one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q))
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right hden
  · intro h
    simp [h]

/-- Pointwise negative-binomial transport from centered reciprocal powers to a fixed shifted
atom.  The strong endpoint height law gives the uniform convergence radius `y < 41/2`. -/
theorem hasSum_xiShiftedReciprocalSquare_pow_sourceMoments
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    (q : XiZeroCopy) (m : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
        xiZeroCopyReciprocalSquare q ^ (r + m + 1))
      (xiShiftedReciprocalSquare y q ^ (m + 1)) := by
  let z := xiZeroCopyReciprocalSquare q
  have hz : ‖z‖ < (2 / 41 : ℝ) := by
    simpa only [z] using norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q
  have hyr : y * (2 / 41 : ℝ) < 1 := by
    nlinarith
  have hyz : ‖-((y : ℂ) * z)‖ < 1 := by
    by_cases hy0 : y = 0
    · subst y
      norm_num
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hy]
    calc
      y * ‖z‖ < y * (2 / 41 : ℝ) :=
        mul_lt_mul_of_pos_left hz (lt_of_le_of_ne hy (Ne.symm hy0))
      _ < 1 := hyr
  have hseries := hasSum_choose_mul_geometric_of_norm_lt_one m hyz
  have hmul := hseries.mul_left (z ^ (m + 1))
  rw [xiShiftedReciprocalSquare]
  change HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
        z ^ (r + m + 1))
    ((z / (1 + (y : ℂ) * z)) ^ (m + 1))
  convert hmul using 1
  · funext r
    rw [pow_add]
    ring
  · rw [div_pow]
    ring

/-- Absolute summability of the source transport over expansion order and multiplicity-exact Xi
copies.  This justifies exchanging the two infinite sums. -/
theorem summable_xiShiftedReciprocalSource_double
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2) (m : ℕ) :
    Summable (fun p : ℕ × XiZeroCopy =>
      (-1 : ℂ) ^ p.1 * ((p.1 + m).choose m : ℂ) * (y : ℂ) ^ p.1 *
        xiZeroCopyReciprocalSquare p.2 ^ (p.1 + m + 1)) := by
  let R : ℝ := 2 / 41
  let a : ℕ → ℝ := fun r => ((r + m).choose m : ℝ) * (y * R) ^ r
  let b : XiZeroCopy → ℝ := fun q => ‖xiZeroCopyReciprocalSquare q ^ (m + 1)‖
  have htheta0 : 0 ≤ y * R := by
    dsimp only [R]
    positivity
  have htheta : y * R < 1 := by
    dsimp only [R]
    nlinarith
  have ha : Summable a := by
    apply summable_choose_mul_geometric_of_norm_lt_one m
    rw [Real.norm_eq_abs, abs_of_nonneg htheta0]
    exact htheta
  have hb : Summable b := by
    simpa only [b] using (summable_xiZeroCopyReciprocalSquare_pow m).norm
  have hab : Summable (fun p : ℕ × XiZeroCopy => a p.1 * b p.2) :=
    ha.mul_of_nonneg hb (fun r => by positivity) (fun q => norm_nonneg _)
  apply Summable.of_norm_bounded hab
  rintro ⟨r, q⟩
  have hz : ‖xiZeroCopyReciprocalSquare q‖ ≤ R := by
    exact (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le
  change ‖(-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
      xiZeroCopyReciprocalSquare q ^ (r + m + 1)‖ ≤ a r * b q
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hy, a, b]
  rw [show r + m + 1 = r + (m + 1) by omega, pow_add]
  have hcore : y ^ r * ‖xiZeroCopyReciprocalSquare q‖ ^ r ≤
      (y * R) ^ r := by
    rw [mul_pow]
    gcongr
  calc
    ((r + m).choose m : ℝ) * y ^ r *
          (‖xiZeroCopyReciprocalSquare q‖ ^ r *
            ‖xiZeroCopyReciprocalSquare q‖ ^ (m + 1)) =
        ((r + m).choose m : ℝ) *
          (y ^ r * ‖xiZeroCopyReciprocalSquare q‖ ^ r) *
            ‖xiZeroCopyReciprocalSquare q‖ ^ (m + 1) := by ring
    _ ≤ ((r + m).choose m : ℝ) * (y * R) ^ r *
          ‖xiZeroCopyReciprocalSquare q‖ ^ (m + 1) := by gcongr

/-- Every shifted reciprocal moment inside the endpoint disk is an exact negative-binomial
transform of the centered reciprocal moment tower. -/
theorem xiShiftedReciprocalMoment_eq_centralNegativeBinomial
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2) (m : ℕ) :
    xiShiftedReciprocalMoment y m =
      ∑' r : ℕ, (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
        xiCentralReciprocalMoment (r + m) := by
  let f : ℕ → XiZeroCopy → ℂ := fun r q =>
    (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
      xiZeroCopyReciprocalSquare q ^ (r + m + 1)
  have hf : Summable (Function.uncurry f) :=
    summable_xiShiftedReciprocalSource_double hy hymax m
  have hpoint (q : XiZeroCopy) :
      ∑' r : ℕ, f r q = xiShiftedReciprocalSquare y q ^ (m + 1) :=
    (hasSum_xiShiftedReciprocalSquare_pow_sourceMoments hy hymax q m).tsum_eq
  calc
    xiShiftedReciprocalMoment y m =
        ∑' q : XiZeroCopy, xiShiftedReciprocalSquare y q ^ (m + 1) := rfl
    _ = ∑' q : XiZeroCopy, ∑' r : ℕ, f r q := by
      apply tsum_congr
      exact fun q => (hpoint q).symm
    _ = ∑' r : ℕ, ∑' q : XiZeroCopy, f r q := by
      rw [hf.tsum_comm]
    _ = ∑' r : ℕ, (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
        xiCentralReciprocalMoment (r + m) := by
      apply tsum_congr
      intro r
      rw [← tsum_xiZeroCopyReciprocalSquare_pow (r + m)]
      rw [← tsum_mul_left]

/-- **Prime--Gamma source transport.**  Every shifted moment in the full endpoint window is an
explicit absolutely convergent transform of `normalizedPrimeArchMoment`; no zero location is
present in the right-hand side. -/
theorem xiShiftedReciprocalMoment_eq_primeArchSourceNegativeBinomial
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2) (m : ℕ) :
    xiShiftedReciprocalMoment y m =
      ∑' r : ℕ, (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
        (normalizedPrimeArchMoment (r + m) : ℂ) := by
  rw [xiShiftedReciprocalMoment_eq_centralNegativeBinomial hy hymax]
  apply tsum_congr
  intro r
  rw [ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment]

/-- Source-only shifted reciprocal moment, defined by the convergent negative-binomial transform
of the fixed prime--Gamma moment tower. -/
def primeArchShiftedReciprocalMoment (y : ℝ) (m : ℕ) : ℂ :=
  ∑' r : ℕ, (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
    (normalizedPrimeArchMoment (r + m) : ℂ)

theorem xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2) (m : ℕ) :
    xiShiftedReciprocalMoment y m = primeArchShiftedReciprocalMoment y m := by
  exact xiShiftedReciprocalMoment_eq_primeArchSourceNegativeBinomial hy hymax m

/-- Shifted Hankel positivity after deleting the first `2M` moments. -/
def XiShiftedReciprocalHankelTailNonnegative (y : ℝ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℝ),
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      c i * c j *
        (xiShiftedReciprocalMoment y
          (2 * M + (i : ℕ) + (j : ℕ))).re

/-- At cutoff zero, the tail interface is exactly the existing finite shifted-Hankel API. -/
theorem xiShiftedReciprocalHankelTailNonnegative_zero_iff
    (y : ℝ) :
    XiShiftedReciprocalHankelTailNonnegative y 0 ↔
      ∀ (N : ℕ) (c : Fin N → ℝ),
        0 ≤ xiShiftedReciprocalHankelQuadratic y c := by
  simp only [XiShiftedReciprocalHankelTailNonnegative,
    xiShiftedReciprocalHankelQuadratic, Nat.mul_zero, Nat.zero_add]

/-- Source-only cofinal shifted Hankel cone.  Every entry is constructed solely from
`normalizedPrimeArchMoment`; no Xi zero or divisor coordinate occurs in this proposition. -/
def PrimeArchShiftedReciprocalHankelTailNonnegative (y : ℝ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℝ),
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      c i * c j *
        (primeArchShiftedReciprocalMoment y
          (2 * M + (i : ℕ) + (j : ℕ))).re

/-- Inside the endpoint convergence disk, source-only and zero-side tail cones coincide. -/
theorem primeArchShiftedReciprocalHankelTailNonnegative_iff_xi
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2) (M : ℕ) :
    PrimeArchShiftedReciprocalHankelTailNonnegative y M ↔
      XiShiftedReciprocalHankelTailNonnegative y M := by
  constructor <;> intro h N c
  · simpa only [PrimeArchShiftedReciprocalHankelTailNonnegative,
      XiShiftedReciprocalHankelTailNonnegative,
      xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy hymax] using h N c
  · simpa only [PrimeArchShiftedReciprocalHankelTailNonnegative,
      XiShiftedReciprocalHankelTailNonnegative,
      xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy hymax] using h N c

/-- Exact coefficient-vector expansion after multiplication by the tail generator `X^M`. -/
theorem xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn
    {y : ℝ} (hy : 0 ≤ y) (M N : ℕ) (c : Fin N → ℝ) :
    xiShiftedReciprocalTraceHankel y
        ((Polynomial.X : Polynomial ℝ) ^ M * Polynomial.ofFn N c) =
      ∑ i : Fin N, ∑ j : Fin N,
        ((c i * c j : ℝ) : ℂ) *
          xiShiftedReciprocalMoment y
            (2 * M + (i : ℕ) + (j : ℕ)) := by
  let lam : XiZeroCopy → ℂ := xiShiftedReciprocalSquare y
  let momentTerm : ℕ → XiZeroCopy → ℂ := fun k q => lam q ^ (k + 1)
  have hmoment (k : ℕ) : Summable (momentTerm k) := by
    simpa only [lam, momentTerm] using summable_xiShiftedReciprocalSquare_pow hy k
  have heval (q : XiZeroCopy) :
      evalRealPolynomial
          ((Polynomial.X : Polynomial ℝ) ^ M * Polynomial.ofFn N c) (lam q) =
        lam q ^ M * ∑ i : Fin N, ((c i : ℝ) : ℂ) * lam q ^ (i : ℕ) := by
    rw [evalRealPolynomial_mul, evalRealPolynomial_pow]
    simp [evalRealPolynomial, Polynomial.ofFn_eq_sum_monomial]
  rw [xiShiftedReciprocalTraceHankel]
  calc
    (∑' q, xiShiftedReciprocalTraceHankelTerm y
        ((Polynomial.X : Polynomial ℝ) ^ M * Polynomial.ofFn N c) q) =
        ∑' q : XiZeroCopy, ∑ i : Fin N, ∑ j : Fin N,
          ((c i * c j : ℝ) : ℂ) *
            momentTerm (2 * M + (i : ℕ) + (j : ℕ)) q := by
      apply tsum_congr
      intro q
      rw [xiShiftedReciprocalTraceHankelTerm]
      change lam q *
          evalRealPolynomial
            ((Polynomial.X : Polynomial ℝ) ^ M * Polynomial.ofFn N c) (lam q) ^ 2 = _
      rw [heval, pow_two]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [momentTerm]
      push_cast
      rw [show 2 * M + (i : ℕ) + (j : ℕ) + 1 =
          1 + M + (i : ℕ) + M + (j : ℕ) by omega, pow_add, pow_add,
        pow_add, pow_add]
      ring
    _ = ∑ i : Fin N, ∑ j : Fin N,
        ((c i * c j : ℝ) : ℂ) *
          ∑' q : XiZeroCopy,
            momentTerm (2 * M + (i : ℕ) + (j : ℕ)) q := by
      rw [Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Summable.tsum_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [tsum_mul_left]
        · intro j _
          exact (hmoment (2 * M + (i : ℕ) + (j : ℕ))).mul_left
            (((c i * c j : ℝ) : ℂ))
      · intro i _
        exact summable_sum (fun j _ =>
          (hmoment (2 * M + (i : ℕ) + (j : ℕ))).mul_left
            (((c i * c j : ℝ) : ℂ)))
    _ = ∑ i : Fin N, ∑ j : Fin N,
        ((c i * c j : ℝ) : ℂ) *
          xiShiftedReciprocalMoment y
            (2 * M + (i : ℕ) + (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rfl

/-- Finite tail quadratics supply trace positivity on the principal ideal generated by `X^M`. -/
theorem xiShiftedReciprocalTraceHankel_nonnegative_on_X_pow_ideal
    {y : ℝ} (hy : 0 ≤ y) {M : ℕ}
    (htail : XiShiftedReciprocalHankelTailNonnegative y M) :
    ∀ p : Polynomial ℝ,
      0 ≤ (xiShiftedReciprocalTraceHankel y
        ((Polynomial.X : Polynomial ℝ) ^ M * p)).re := by
  intro p
  let N := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  have hp : Polynomial.ofFn N c = p := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  rw [← hp, xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn hy]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact htail N c

/-- Every cofinal fixed-shift Hankel tail excludes all nonreal translated Xi atoms. -/
theorem xiShiftedReciprocalSquare_real_of_hankelTailNonnegative
    {y : ℝ} (hy : 0 ≤ y) {M : ℕ}
    (htail : XiShiftedReciprocalHankelTailNonnegative y M) :
    ∀ q : XiZeroCopy, (xiShiftedReciprocalSquare y q).im = 0 := by
  let lam : XiZeroCopy → ℂ := xiShiftedReciprocalSquare y
  have hsum : Summable lam := by
    simpa only [lam, Nat.zero_add, pow_one] using
      summable_xiShiftedReciprocalSquare_pow hy 0
  apply traceHankel_nonnegative_on_principalIdeal_implies_real lam
    (fun q => xiShiftedReciprocalSquare_ne_zero hy q)
    (fun hr => xiShiftedReciprocalSquare_finite_norm_ge hy hr)
    hsum ((Polynomial.X : Polynomial ℝ) ^ M)
  · intro q him
    have hne := xiShiftedReciprocalSquare_ne_zero hy q
    simpa only [evalRealPolynomial, Polynomial.eval_map, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_X] using
      (pow_ne_zero M hne)
  · intro p
    simpa only [xiShiftedReciprocalTraceHankel,
      xiShiftedReciprocalTraceHankelTerm, lam] using
      xiShiftedReciprocalTraceHankel_nonnegative_on_X_pow_ideal hy htail p

/-- A cofinal fixed-shift Hankel tail forces RH. -/
theorem riemannHypothesis_of_xiShiftedReciprocalHankelTailNonnegative
    {y : ℝ} (hy : 0 ≤ y) {M : ℕ}
    (htail : XiShiftedReciprocalHankelTailNonnegative y M) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hshift := xiShiftedReciprocalSquare_real_of_hankelTailNonnegative hy htail q
  have hcopy := (xiShiftedReciprocalSquare_im_eq_zero_iff hy q).mp hshift
  have hcentral : (xiCentralReciprocalSquare (q.1 : ℂ)).im = 0 := by
    simpa only [xiZeroCopyReciprocalSquare_eq] using hcopy
  have hre := (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp hcentral
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · rw [xiSpectralPoint_im_eq, hre]
    norm_num

/-- RH makes every shifted Hankel tail nonnegative term by term. -/
theorem xiShiftedReciprocalHankelTailNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 ≤ y) (M : ℕ) :
    XiShiftedReciprocalHankelTailNonnegative y M := by
  intro N c
  -- The direct atomwise proof is represented by the polynomial `X^M * ofFn N c`.
  have hpoly : 0 ≤ (xiShiftedReciprocalTraceHankel y
      ((Polynomial.X : Polynomial ℝ) ^ M * Polynomial.ofFn N c)).re := by
    rw [xiShiftedReciprocalTraceHankel,
      Complex.re_tsum (summable_xiShiftedReciprocalTraceHankelTerm hy _)]
    apply tsum_nonneg
    intro q
    obtain ⟨x, hx, hcoord⟩ :=
      xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis hRH hy q
    rw [xiShiftedReciprocalTraceHankelTerm, hcoord,
      evalRealPolynomial_ofReal]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  rw [xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn hy] at hpoly
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hpoly

/-- **Fixed-shift tail RH law.**  Every finite moment prefix can be discarded. -/
theorem xiShiftedReciprocalHankelTailNonnegative_iff_riemannHypothesis
    {y : ℝ} (hy : 0 ≤ y) (M : ℕ) :
    XiShiftedReciprocalHankelTailNonnegative y M ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiShiftedReciprocalHankelTailNonnegative hy,
    fun hRH => xiShiftedReciprocalHankelTailNonnegative_of_riemannHypothesis
      hRH hy M⟩

/-- **Source-only fixed-shift tail RH law.**  In the endpoint convergence window, every finite
prefix may be deleted from the explicit prime--Gamma negative-binomial Hankel tower. -/
theorem primeArchShiftedReciprocalHankelTailNonnegative_iff_riemannHypothesis
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2) (M : ℕ) :
    PrimeArchShiftedReciprocalHankelTailNonnegative y M ↔ RiemannHypothesis :=
  (primeArchShiftedReciprocalHankelTailNonnegative_iff_xi hy hymax M).trans
    (xiShiftedReciprocalHankelTailNonnegative_iff_riemannHypothesis hy M)

/-- Shift one is a source-defined cofinal-tail RH criterion for every cutoff. -/
theorem primeArchShiftedReciprocalHankelTailNonnegative_one_iff_riemannHypothesis
    (M : ℕ) :
    PrimeArchShiftedReciprocalHankelTailNonnegative 1 M ↔ RiemannHypothesis :=
  primeArchShiftedReciprocalHankelTailNonnegative_iff_riemannHypothesis
    (y := 1) (by norm_num) (by norm_num) M

/-- The shift-one Möbius atom is exactly the fixed squared-Xi seam coordinate. -/
theorem xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate
    (q : XiZeroCopy) :
    xiShiftedReciprocalSquare 1 q = xiSquaredSeamOneCoordinate q := by
  let z := xiZeroCopyReciprocalSquare q
  have hz : z ≠ 0 := by
    dsimp only [z]
    rw [xiZeroCopyReciprocalSquare_eq]
    exact xiCentralReciprocalSquare_ne_zero q.1
  have h1z : 1 + z ≠ 0 := by
    dsimp only [z]
    simpa using one_add_mul_xiZeroCopyReciprocalSquare_ne_zero
      (y := 1) (by norm_num) q
  have hb : (q.1 : ℂ) - 1 / 2 ≠ 0 :=
    sub_ne_zero.mpr (xi_divisor_support_ne_half q.1)
  calc
    xiShiftedReciprocalSquare 1 q = z / (1 + z) := by
      simp only [xiShiftedReciprocalSquare, z, Complex.ofReal_one, one_mul]
    _ = (1 + z⁻¹)⁻¹ := by
      field_simp [hz, h1z]
      rw [show z + 1 = 1 + z by ring, div_self h1z]
    _ = (1 - ((q.1 : ℂ) - 1 / 2) ^ 2)⁻¹ := by
      congr 1
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_eq, xiCentralReciprocalSquare]
      field_simp [hb]
      ring
    _ = xiSquaredSeamOneCoordinate q := by
      congr 1
      unfold xiSquaredSeamOneRadialA xiSquaredSeamTransverseB
      apply Complex.ext <;>
        simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- A shifted Hankel tail directly supplies the sole remaining dyadic tail.  This connector uses
the atomwise reality conclusion of the trace-Hankel converse and does not route through RH. -/
theorem xiSquaredSeamDyadicTailFromSix_of_shiftedHankelTail
    {M : ℕ} (h : XiShiftedReciprocalHankelTailNonnegative 1 M) :
    XiSquaredSeamDyadicTailFromSix := by
  intro q k _
  have him := xiShiftedReciprocalSquare_real_of_hankelTailNonnegative
    (y := 1) (by norm_num) h q
  rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate] at him
  have hdyadic :=
    (GaloisForLFunctions.complexDyadicHalfPlane_iff_nonnegativeReal
      (xiSquaredSeamOneCoordinate q)).mpr
      ⟨him, (xiSquaredSeamOneCoordinate_re_pos q).le⟩
  exact hdyadic k

/-- The source-only negative-binomial tail supplies the dyadic tail through its exact shifted
moment transport. -/
theorem xiSquaredSeamDyadicTailFromSix_of_primeArchShiftedHankelTail
    {M : ℕ} (h : PrimeArchShiftedReciprocalHankelTailNonnegative 1 M) :
    XiSquaredSeamDyadicTailFromSix := by
  apply xiSquaredSeamDyadicTailFromSix_of_shiftedHankelTail
  exact (primeArchShiftedReciprocalHankelTailNonnegative_iff_xi
    (y := 1) (by norm_num) (by norm_num) M).mp h

/-- A fixed-shift Hankel tail discharges both rightmost dyadic interfaces. -/
theorem xiSquaredSeamPowerThirtyTwoAnnulusEmpty_and_tailFromSix_of_shiftedHankelTail
    {M : ℕ} (h : XiShiftedReciprocalHankelTailNonnegative 1 M) :
    XiSquaredSeamPowerThirtyTwoAnnulusEmpty ∧ XiSquaredSeamDyadicTailFromSix := by
  apply xiSquaredSeamPowerThirtyTwoAnnulusEmpty_and_tailFromSix_iff_riemannHypothesis.mpr
  exact riemannHypothesis_of_xiShiftedReciprocalHankelTailNonnegative
    (y := 1) (by norm_num) h

/-- The source-only shift-one tail cone discharges both rightmost dyadic interfaces. -/
theorem xiSquaredSeamPowerThirtyTwoAnnulusEmpty_and_tailFromSix_of_primeArchShiftedHankelTail
    {M : ℕ} (h : PrimeArchShiftedReciprocalHankelTailNonnegative 1 M) :
    XiSquaredSeamPowerThirtyTwoAnnulusEmpty ∧ XiSquaredSeamDyadicTailFromSix := by
  apply xiSquaredSeamPowerThirtyTwoAnnulusEmpty_and_tailFromSix_iff_riemannHypothesis.mpr
  exact (primeArchShiftedReciprocalHankelTailNonnegative_one_iff_riemannHypothesis M).mp h

/-! ## Absolute-Euler value of the first shift-one moment -/

/-- At `z = -I`, the reciprocal-square resolvent atom is exactly the shift-one Möbius atom. -/
theorem xiReciprocalSquareResolventTerm_neg_I_eq_shift_one (q : XiZeroCopy) :
    xiReciprocalSquareResolventTerm (-I) q =
      xiShiftedReciprocalSquare 1 q := by
  simp only [xiReciprocalSquareResolventTerm, xiShiftedReciprocalSquare,
    neg_sq, I_sq, neg_one_mul, sub_neg_eq_add, Complex.ofReal_one, one_mul]

/-- **Right-half-plane predecessor identity.**  The first shift-one reciprocal moment is not
merely a central Taylor coefficient: it is exactly the completed logarithmic derivative at the
absolute-Euler point `s = 3/2`.  Reflection-pair multiplicity is already built into both sides. -/
theorem xiShiftedReciprocalMoment_one_zero_eq_logDeriv_three_halves :
    xiShiftedReciprocalMoment 1 0 = logDeriv xi (3 / 2) := by
  have hXi : XiC (-I) ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hpair := xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi
  have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [logDeriv_XiC_eq_mul_I_logDeriv_xi] at hlog
  have hsum :
      (∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm (-I) q) =
        xiShiftedReciprocalMoment 1 0 := by
    rw [xiShiftedReciprocalMoment]
    apply tsum_congr
    intro q
    rw [xiReciprocalSquareResolventTerm_neg_I_eq_shift_one]
    simp
  rw [hpair, hsum] at hlog
  have hcoord : (1 / 2 : ℂ) + (-I) * I = 3 / 2 := by
    rw [neg_mul, I_mul_I]
    norm_num
  rw [hcoord] at hlog
  apply (mul_left_cancel₀ I_ne_zero)
  simpa only [neg_neg] using hlog.symm

/-- The source-defined first shift-one moment has the same absolute-Euler value. -/
theorem primeArchShiftedReciprocalMoment_one_zero_eq_logDeriv_three_halves :
    primeArchShiftedReciprocalMoment 1 0 = logDeriv xi (3 / 2) := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
    (y := 1) (by norm_num) (by norm_num) 0]
  exact xiShiftedReciprocalMoment_one_zero_eq_logDeriv_three_halves

/-- **Prime--Gamma evaluation.**  The same moment is an absolutely convergent von-Mangoldt value
subtracted from the fixed archimedean logarithmic derivative at `3/2`. -/
theorem primeArchShiftedReciprocalMoment_one_zero_eq_primeGammaValue :
    primeArchShiftedReciprocalMoment 1 0 =
      logDeriv archFactor (3 / 2) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2) := by
  rw [primeArchShiftedReciprocalMoment_one_zero_eq_logDeriv_three_halves]
  have hs : 1 < ((3 / 2 : ℂ).re) := by norm_num
  have hsplit := seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hs] at hsplit
  change -logDeriv xi (3 / 2) =
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2) -
      logDeriv archFactor (3 / 2) at hsplit
  linear_combination -hsplit

end

end RHTower
