import GaloisForLFunctions.RHTower.FiniteFluxPassport
import GaloisForLFunctions.RHTower.SimultaneousFiniteJetFlatness
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.Compact

/-!
# Positive polynomial repair on the imaginary axis

A polynomial of strictly smaller degree than a globally positive polynomial can be shifted into
the positive cone by adding one scalar multiple of the larger polynomial.  The proof uses the
positive denominator to form a continuous quotient, the degree gap to make it tend to zero at both
ends, and the one-point compactification to obtain a global upper bound.

The complex bridge packages restriction to the imaginary axis as an ordinary real polynomial.
Together these results discharge the global positivity-domination interface in the finite quartet
passport realization theorem.
-/

open Polynomial Set Filter Topology Complex

namespace RHTower

noncomputable section

/-- **Positive domination by degree.** If `Q` is positive on the real axis and has strictly larger
degree than `P`, one scalar translate `P + LQ` is positive everywhere. -/
theorem exists_scalar_add_mul_pos_of_degree_lt
    (P Q : Polynomial ℝ)
    (hdegree : P.degree < Q.degree)
    (hQpos : ∀ x : ℝ, 0 < Q.eval x) :
    ∃ L : ℝ, ∀ x : ℝ, 0 < (P + C L * Q).eval x := by
  let f : ℝ → ℝ := fun x => -P.eval x / Q.eval x
  have hQne : ∀ x : ℝ, Q.eval x ≠ 0 := fun x => ne_of_gt (hQpos x)
  have hcont : Continuous f := by
    exact P.continuous.neg.div Q.continuous hQne
  have htop : Tendsto f atTop (𝓝 0) := by
    have heq : f = fun x => (-P).eval x / Q.eval x := by
      funext x
      simp [f]
    rw [heq]
    exact Polynomial.div_tendsto_atTop_zero_of_degree_lt (-P) Q (by simpa using hdegree)
  have hbot : Tendsto f atBot (𝓝 0) := by
    have heq : f = fun x => (-P).eval x / Q.eval x := by
      funext x
      simp [f]
    rw [heq]
    exact Polynomial.div_tendsto_atBot_zero_of_degree_lt (-P) Q (by simpa using hdegree)
  have hcocompact : Tendsto f (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop]
    exact hbot.sup htop
  have hcompact : IsCompact (insert 0 (range f)) :=
    hcocompact.isCompact_insert_range_of_cocompact hcont
  obtain ⟨K, hK⟩ := bddAbove_def.mp hcompact.bddAbove
  refine ⟨K + 1, fun x => ?_⟩
  have hfx : f x ≤ K := hK (f x) (Or.inr ⟨x, rfl⟩)
  have hstrict : f x < K + 1 := lt_of_le_of_lt hfx (by linarith)
  have hmul := (div_lt_iff₀ (hQpos x)).mp hstrict
  simp [eval_add, eval_mul, eval_C]
  nlinarith [hQpos x]

/-- Real polynomial obtained by restricting a complex polynomial to `z = iy` and taking the real
part.  Its `n`-th coefficient is `re(aₙ iⁿ)`. -/
def imaginaryAxisRealPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  P.sum fun n a => monomial n (a * I ^ n).re

theorem eval_imaginaryAxisRealPolynomial (P : Polynomial ℂ) (y : ℝ) :
    (imaginaryAxisRealPolynomial P).eval y = (P.eval ((y : ℂ) * I)).re := by
  classical
  rw [imaginaryAxisRealPolynomial, Polynomial.sum_def, eval_finsetSum,
    eval_eq_sum, Polynomial.sum_def]
  change (∑ n ∈ P.support, (monomial n (P.coeff n * I ^ n).re).eval y) =
    Complex.reCLM (∑ n ∈ P.support, P.coeff n * ((y : ℂ) * I) ^ n)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [eval_monomial, mul_pow]
  rw [show P.coeff n * ((y : ℂ) ^ n * I ^ n) =
    (P.coeff n * I ^ n) * (y : ℂ) ^ n by ring]
  have hpow : (y : ℂ) ^ n = ((y ^ n : ℝ) : ℂ) := by norm_cast
  rw [show (P.coeff n * I ^ n) * (y : ℂ) ^ n =
    (y ^ n : ℝ) • (P.coeff n * I ^ n) by
      rw [hpow]
      simp [mul_comm]]
  change (P.coeff n * I ^ n).re * y ^ n =
    Complex.reCLM ((y ^ n : ℝ) • (P.coeff n * I ^ n))
  rw [map_smul]
  simp [smul_eq_mul, mul_comm]

@[simp] theorem coeff_imaginaryAxisRealPolynomial (P : Polynomial ℂ) (n : ℕ) :
    (imaginaryAxisRealPolynomial P).coeff n = (P.coeff n * I ^ n).re := by
  classical
  rw [imaginaryAxisRealPolynomial, Polynomial.coeff_sum, Polynomial.sum_def]
  by_cases hn : n ∈ P.support
  · simp [Polynomial.coeff_monomial, hn]
  · have hcoeff : P.coeff n = 0 := by
      simpa [Polynomial.mem_support_iff] using hn
    simp [Polynomial.coeff_monomial, hn, hcoeff]

theorem natDegree_imaginaryAxisRealPolynomial_le (P : Polynomial ℂ) :
    (imaginaryAxisRealPolynomial P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_imaginaryAxisRealPolynomial, Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  simp

theorem degree_imaginaryAxisRealPolynomial_le (P : Polynomial ℂ) :
    (imaginaryAxisRealPolynomial P).degree ≤ P.degree := by
  by_cases hP : P = 0
  · subst P
    simp [imaginaryAxisRealPolynomial]
  rw [Polynomial.degree_eq_natDegree hP]
  exact Polynomial.degree_le_natDegree.trans
    (WithBot.coe_le_coe.mpr (natDegree_imaginaryAxisRealPolynomial_le P))

/-- A monic polynomial whose degree is divisible by four retains its full degree after restriction
to the imaginary axis and passage to real parts. -/
theorem degree_imaginaryAxisRealPolynomial_eq_of_monic_four_dvd_natDegree
    {P : Polynomial ℂ} (hP : P.Monic) (hfour : 4 ∣ P.natDegree) :
    (imaginaryAxisRealPolynomial P).degree = P.degree := by
  obtain ⟨k, hk⟩ := hfour
  have hcoeff : (imaginaryAxisRealPolynomial P).coeff P.natDegree = 1 := by
    rw [coeff_imaginaryAxisRealPolynomial, hP.coeff_natDegree, hk]
    simp [pow_mul]
  have himne : imaginaryAxisRealPolynomial P ≠ 0 := by
    intro hzero
    rw [hzero, coeff_zero] at hcoeff
    norm_num at hcoeff
  have hnatle := natDegree_imaginaryAxisRealPolynomial_le P
  have hnatge : P.natDegree ≤ (imaginaryAxisRealPolynomial P).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; norm_num)
  have hnateq : (imaginaryAxisRealPolynomial P).natDegree = P.natDegree :=
    le_antisymm hnatle hnatge
  rw [Polynomial.degree_eq_natDegree himne,
    Polynomial.degree_eq_natDegree hP.ne_zero, hnateq]

/-- **Complex imaginary-axis positive repair.** Real-valued complex polynomials on the imaginary
axis reduce to real polynomials.  A strict degree gap and positivity of the repair polynomial then
produce one real scalar making the complex sum strictly positive real on the entire axis. -/
theorem exists_scalar_add_mul_pos_real_on_imaginaryAxis
    (B R : Polynomial ℂ)
    (hBreal : ∀ y : ℝ, (B.eval ((y : ℂ) * I)).im = 0)
    (hRreal : ∀ y : ℝ, (R.eval ((y : ℂ) * I)).im = 0)
    (hRpos : ∀ y : ℝ, 0 < (R.eval ((y : ℂ) * I)).re)
    (hdegree : (imaginaryAxisRealPolynomial B).degree <
      (imaginaryAxisRealPolynomial R).degree) :
    ∃ L : ℝ, ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧
      (B + C (L : ℂ) * R).eval ((y : ℂ) * I) = (r : ℂ) := by
  obtain ⟨L, hL⟩ := exists_scalar_add_mul_pos_of_degree_lt
    (imaginaryAxisRealPolynomial B) (imaginaryAxisRealPolynomial R) hdegree
    (fun y => by rw [eval_imaginaryAxisRealPolynomial]; exact hRpos y)
  refine ⟨L, fun y => ⟨
    (imaginaryAxisRealPolynomial B + C L * imaginaryAxisRealPolynomial R).eval y,
    hL y, ?_⟩⟩
  have hBeq : B.eval ((y : ℂ) * I) =
      (((imaginaryAxisRealPolynomial B).eval y : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa using (eval_imaginaryAxisRealPolynomial B y).symm
    · simpa using hBreal y
  have hReq : R.eval ((y : ℂ) * I) =
      (((imaginaryAxisRealPolynomial R).eval y : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa using (eval_imaginaryAxisRealPolynomial R y).symm
    · simpa using hRreal y
  rw [eval_add, eval_mul, eval_C, hBeq, hReq]
  norm_cast
  simp [eval_add, eval_mul, eval_C]

/-! ## Quartet-packet specialization -/

/-- Polynomial form of one real-even quartet atom. -/
def quartetFlatPolynomial (α : ℂ) : Polynomial ℂ :=
  (X ^ (2 : ℕ) - C (α ^ (2 : ℕ))) * (X ^ (2 : ℕ) - C (((starRingEnd ℂ) α) ^ (2 : ℕ)))

/-- Polynomial carrying a finite packet of quartet multiplicities. -/
def simultaneousFlatPolynomial {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) : Polynomial ℂ :=
  ∏ i, quartetFlatPolynomial (α i) ^ M i

theorem quartetFlatPolynomial_monic (α : ℂ) : (quartetFlatPolynomial α).Monic := by
  exact (monic_X_pow_sub_C _ (by norm_num)).mul
    (monic_X_pow_sub_C _ (by norm_num))

theorem simultaneousFlatPolynomial_monic {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) : (simultaneousFlatPolynomial M α).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (quartetFlatPolynomial_monic (α i)).pow _

theorem quartetFlatPolynomial_natDegree (α : ℂ) :
    (quartetFlatPolynomial α).natDegree = 4 := by
  rw [quartetFlatPolynomial, Polynomial.Monic.natDegree_mul
    (monic_X_pow_sub_C _ (by norm_num)) (monic_X_pow_sub_C _ (by norm_num)),
    natDegree_X_pow_sub_C, natDegree_X_pow_sub_C]

theorem simultaneousFlatPolynomial_natDegree {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) :
    (simultaneousFlatPolynomial M α).natDegree = 4 * ∑ i, M i := by
  rw [simultaneousFlatPolynomial]
  rw [Polynomial.natDegree_prod Finset.univ _ (fun i hi =>
    ((quartetFlatPolynomial_monic (α i)).pow (M i)).ne_zero)]
  simp_rw [Polynomial.natDegree_pow, quartetFlatPolynomial_natDegree]
  rw [← Finset.sum_mul]
  omega

@[simp] theorem quartetFlatPolynomial_eval (α z : ℂ) :
    (quartetFlatPolynomial α).eval z = quartetFlatAtom α z := by
  simp [quartetFlatPolynomial, quartetFlatAtom]

@[simp] theorem simultaneousFlatPolynomial_eval {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (z : ℂ) :
    (simultaneousFlatPolynomial M α).eval z = simultaneousFlatProduct M α z := by
  rw [simultaneousFlatPolynomial, simultaneousFlatProduct, Polynomial.eval_prod]
  simp

/-- Every local quartet multiplicity divides the full packet polynomial. -/
theorem quartetFlatPolynomial_pow_dvd_simultaneousFlatPolynomial
    {ι : Type*} [Fintype ι] (M : ι → ℕ) (α : ι → ℂ) (i : ι) :
    quartetFlatPolynomial (α i) ^ M i ∣ simultaneousFlatPolynomial M α := by
  exact Finset.dvd_prod_of_mem
    (fun j => quartetFlatPolynomial (α j) ^ M j) (Finset.mem_univ i)

/-- The polynomial packet is strictly positive real on the imaginary axis. -/
theorem simultaneousFlatPolynomial_mul_I_pos_real {ι : Type*} [Fintype ι]
    (M : ι → ℕ) (α : ι → ℂ) (y : ℝ)
    (hne : ∀ i, ((y : ℂ) ^ (2 : ℕ)) + (α i) ^ (2 : ℕ) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (simultaneousFlatPolynomial M α).eval ((y : ℂ) * I) = (r : ℂ) := by
  simpa only [simultaneousFlatPolynomial_eval] using
    simultaneousFlatProduct_mul_I_pos_real M α y hne

theorem degree_imaginaryAxisRealPolynomial_simultaneousFlatPolynomial
    {ι : Type*} [Fintype ι] (M : ι → ℕ) (α : ι → ℂ) :
    (imaginaryAxisRealPolynomial (simultaneousFlatPolynomial M α)).degree =
      (simultaneousFlatPolynomial M α).degree := by
  apply degree_imaginaryAxisRealPolynomial_eq_of_monic_four_dvd_natDegree
    (simultaneousFlatPolynomial_monic M α)
  rw [simultaneousFlatPolynomial_natDegree]
  exact dvd_mul_right 4 _

/-- **Finite-packet positive repair.** Any imaginary-axis-real polynomial of lower degree than the
quartet packet can be made strictly positive real on the whole imaginary axis by adding one scalar
multiple of that packet.  Every packet zero and its full prescribed multiplicity are unchanged. -/
theorem exists_scalar_add_simultaneousFlatPolynomial_pos_real_on_imaginaryAxis
    {ι : Type*} [Fintype ι]
    (B : Polynomial ℂ) (M : ι → ℕ) (α : ι → ℂ)
    (hBreal : ∀ y : ℝ, (B.eval ((y : ℂ) * I)).im = 0)
    (hne : ∀ i y, ((y : ℂ) ^ (2 : ℕ)) + (α i) ^ (2 : ℕ) ≠ 0)
    (hdegree : B.degree < (simultaneousFlatPolynomial M α).degree) :
    ∃ L : ℝ,
      (∀ i, quartetFlatPolynomial (α i) ^ M i ∣
        (B + C (L : ℂ) * simultaneousFlatPolynomial M α) - B) ∧
      ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧
        (B + C (L : ℂ) * simultaneousFlatPolynomial M α).eval ((y : ℂ) * I) =
          (r : ℂ) := by
  obtain ⟨L, hpos⟩ := exists_scalar_add_mul_pos_real_on_imaginaryAxis
    B (simultaneousFlatPolynomial M α) hBreal
    (fun y => by
      obtain ⟨r, hr, heq⟩ :=
        simultaneousFlatPolynomial_mul_I_pos_real M α y (fun i => hne i y)
      rw [heq]
      simp)
    (fun y => by
      obtain ⟨r, hr, heq⟩ :=
        simultaneousFlatPolynomial_mul_I_pos_real M α y (fun i => hne i y)
      rw [heq]
      simpa)
    ((degree_imaginaryAxisRealPolynomial_le B).trans_lt
      (hdegree.trans_eq
        (degree_imaginaryAxisRealPolynomial_simultaneousFlatPolynomial M α).symm))
  refine ⟨L, ?_, hpos⟩
  intro i
  obtain ⟨Q, hQ⟩ :=
    quartetFlatPolynomial_pow_dvd_simultaneousFlatPolynomial M α i
  refine ⟨C (L : ℂ) * Q, ?_⟩
  rw [hQ]
  ring

end

end RHTower
