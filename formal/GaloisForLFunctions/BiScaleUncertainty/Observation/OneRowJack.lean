import Mathlib.RingTheory.PowerSeries.Binomial
import GaloisForLFunctions.RHTower.MeixnerRootPrimeLaplaceValueFrame
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# One-row Jack observations and prime-Laplace convolution

Multiplicativity of binomial generating series gives the complete one-row Jack binary
specialization. Its rising-factorial ratio is also a ratio of the existing Meixner
prime-Laplace coefficients. Those coefficients form a convolution semigroup in the parameter.
-/

open scoped BigOperators
open PowerSeries Polynomial
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

/-- The complete Jack generating factor `(1 - X)^(-theta)`. -/
def jackFactor (theta : ℝ) : PowerSeries ℝ :=
  rescale (-1 : ℝ) (binomialSeries ℝ (-theta))

theorem jackFactor_coeff (theta : ℝ) (n : ℕ) :
    coeff n (jackFactor theta) = Ring.multichoose theta n := by
  rw [jackFactor, coeff_rescale, binomialSeries_coeff, Ring.choose_neg']
  simp only [smul_eq_mul, mul_one, Units.smul_def, zsmul_eq_mul,
    Int.cast_negOnePow_natCast]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem jackFactor_add (a b : ℝ) : jackFactor (a + b) = jackFactor a * jackFactor b := by
  simp only [jackFactor, neg_add, binomialSeries_add, map_mul]

theorem jackFactor_nat_mul (theta : ℝ) (m : ℕ) :
    jackFactor ((m : ℝ) * theta) = jackFactor theta ^ m := by
  induction m with
  | zero => simp [jackFactor]
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, jackFactor_add, ih, pow_succ]

/-- Normalized one-row Jack polynomial, defined by its complete generating series. -/
def oneRowJack {ι : Type*} [Fintype ι] (theta : ℝ) (n : ℕ) (x : ι → ℝ) : ℝ :=
  coeff n (∏ i, rescale (x i) (jackFactor theta)) / Ring.multichoose theta n

/-- On binary data, every one-row Jack polynomial depends only on the occupied count. -/
theorem oneRowJack_binary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (theta : ℝ) (n : ℕ) (S : Finset ι) :
    oneRowJack theta n (fun i => if i ∈ S then 1 else 0) =
      Ring.multichoose ((S.card : ℝ) * theta) n / Ring.multichoose theta n := by
  have hf : ∀ i : ι, rescale (if i ∈ S then 1 else 0 : ℝ) (jackFactor theta) =
      if i ∈ S then jackFactor theta else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [if_neg hi, rescale_zero, ← coeff_zero_eq_constantCoeff_apply,
        jackFactor_coeff, Ring.multichoose_zero_right, map_one]
  unfold oneRowJack
  simp only [hf]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
    ← jackFactor_nat_mul, jackFactor_coeff]

/-- Multichoose coefficients are rising factorials divided by the degree factorial. -/
theorem jack_multichoose_pochhammer (theta : ℝ) (n : ℕ) :
    Ring.multichoose theta n = (ascPochhammer ℕ n).smeval theta / (n.factorial : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
  simpa only [nsmul_eq_mul, mul_comm] using
    Ring.factorial_nsmul_multichoose_eq_ascPochhammer theta n

/-- The row evaluation is the full rising-factorial ratio `(m theta)_n / (theta)_n`. -/
theorem oneRowJack_binary_pochhammer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (theta : ℝ) (n : ℕ) (S : Finset ι) :
    oneRowJack theta n (fun i => if i ∈ S then 1 else 0) =
      (ascPochhammer ℕ n).smeval ((S.card : ℝ) * theta) /
        (ascPochhammer ℕ n).smeval theta := by
  rw [oneRowJack_binary, jack_multichoose_pochhammer, jack_multichoose_pochhammer,
    div_div_div_cancel_right₀ (by exact_mod_cast Nat.factorial_ne_zero n)]


/-- Positive Jack parameter gives a nonzero normalization in every degree. -/
theorem jack_multichoose_exp_pos (t : ℝ) (n : ℕ) :
    0 < Ring.multichoose (Real.exp t) n := by
  rw [jack_multichoose_pochhammer]
  apply div_pos
  · simpa only [Polynomial.ascPochhammer_smeval_eq_eval] using
      ascPochhammer_pos n (Real.exp t) (Real.exp_pos t)
  · exact_mod_cast Nat.factorial_pos n

/-- Normalization makes the one-variable polynomial exactly the monomial. -/
theorem oneRowJack_single (t x : ℝ) (n : ℕ) :
    oneRowJack (Real.exp t) n (fun _ : Fin 1 => x) = x ^ n := by
  simp only [oneRowJack, Fin.prod_univ_one, coeff_rescale, jackFactor_coeff]
  exact mul_div_cancel_right₀ _ (jack_multichoose_exp_pos t n).ne'


/-- The existing prime-Laplace coefficients form a convolution semigroup in their parameter. -/
theorem meixnerPrimeBinomialCoeff_convolution (a b : ℝ) (n : ℕ) :
    RHTower.meixnerPrimeBinomialCoeff (a + b) n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      RHTower.meixnerPrimeBinomialCoeff a ij.1 * RHTower.meixnerPrimeBinomialCoeff b ij.2 := by
  have h := congrArg (PowerSeries.coeff n) (jackFactor_add (a / 2) (b / 2))
  simp only [PowerSeries.coeff_mul, jackFactor_coeff, Ring.multichoose_eq] at h
  simpa only [RHTower.meixnerPrimeBinomialCoeff, add_div] using h

/-- Binary Jack evaluation is a ratio of the corpus's prime-Laplace coefficients. -/
theorem oneRowJack_binary_meixner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (theta : ℝ) (n : ℕ) (S : Finset ι) :
    oneRowJack (theta / 2) n (fun i => if i ∈ S then 1 else 0) =
      RHTower.meixnerPrimeBinomialCoeff ((S.card : ℝ) * theta) n /
        RHTower.meixnerPrimeBinomialCoeff theta n := by
  rw [oneRowJack_binary]
  simp only [Ring.multichoose_eq, RHTower.meixnerPrimeBinomialCoeff, mul_div_assoc]


/-- The generating coefficient is homogeneous of its declared degree. -/
theorem oneRowJack_homogeneous {ι : Type*} [Fintype ι]
    (theta c : ℝ) (n : ℕ) (x : ι → ℝ) :
    oneRowJack theta n (fun i => c * x i) = c ^ n * oneRowJack theta n x := by
  have hp : (∏ i, rescale (c * x i) (jackFactor theta)) =
      rescale c (∏ i, rescale (x i) (jackFactor theta)) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [rescale_rescale, mul_comm]
  simp only [oneRowJack, hp, coeff_rescale, mul_div_assoc]

/-- Relabeling the coordinates leaves the observation invariant. -/
theorem oneRowJack_permutation {ι : Type*} [Fintype ι]
    (theta : ℝ) (n : ℕ) (x : ι → ℝ) (e : ι ≃ ι) :
    oneRowJack theta n (fun i => x (e i)) = oneRowJack theta n x := by
  unfold oneRowJack
  rw [e.prod_comp (fun i => rescale (x i) (jackFactor theta))]

#print axioms oneRowJack_homogeneous
#print axioms oneRowJack_permutation
#print axioms oneRowJack_binary_pochhammer
#print axioms jack_multichoose_exp_pos
#print axioms oneRowJack_single
#print axioms meixnerPrimeBinomialCoeff_convolution
#print axioms oneRowJack_binary_meixner

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
