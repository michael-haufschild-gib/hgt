import Mathlib

/-!
# Binomial tail polynomials: the Hoeffding threshold sandwich and the beta-density identity

For `0 ≤ x ≤ 1` the polynomial

`binomialTail r k x = ∑_{j = k}^{r} C(r, j) x ^ j (1 - x) ^ (r - j)`

is the probability that a binomial variable with `r` trials and success probability `x` reaches at
least `k` successes.  This file develops the two facts a bounded replica threshold test needs.

* A *threshold sandwich*: with `k = ⌈r (a + b) / 2⌉` the polynomial is at most `exp (-r δ² / 2)`
  below `b` and at least `1 - exp (-r δ² / 2)` above `a`, where `δ = a - b`.  The proof is a
  Chernoff bound whose only analytic input is Hoeffding's lemma for a two-point variable, obtained
  here from the Bernoulli measure.
* A *beta-density identity*: the derivative of `binomialTail r k` is exactly the `Beta (k, r-k+1)`
  density `r C(r-1, k-1) u^(k-1) (1-u)^(r-k)`, so the tail polynomial is the integral of one
  unit-mass kernel against the indicator of the threshold, and it is monotone on `[0, 1]`.

Both statements are unconditional polynomial identities and estimates; no probability space is
needed beyond the two-point measure used for Hoeffding's lemma.
-/

open Finset MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Hoeffding's lemma for a two-point variable -/

/-- **Hoeffding's lemma for a Bernoulli variable.**  For `x ∈ [0, 1]` the centred moment
generating function of the two-point variable taking value `1 - x` with probability `x` and `-x`
with probability `1 - x` is dominated by `exp (t² / 8)`.  Equivalently, in uncentred form,
`1 - x + x e^t ≤ exp (t x + t² / 8)`. -/
theorem one_sub_add_mul_exp_le_exp (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (t : ℝ) :
    1 - x + x * Real.exp t ≤ Real.exp (t * x + t ^ 2 / 8) := by
  have hp : x ∈ unitInterval := ⟨hx0, hx1⟩
  set p : unitInterval := ⟨x, hp⟩ with hpdef
  have hpx : (p : ℝ) = x := rfl
  set μ : Measure ℝ := bernoulliMeasure (1 - x) (-x) p with hμ
  have hint : ∀ f : ℝ → ℝ, ∫ z, f z ∂μ = x * f (1 - x) + (1 - x) * f (-x) := by
    intro f
    rw [hμ, integral_bernoulliMeasure, hpx]
    simp [smul_eq_mul]
  have hc : ∫ z, id z ∂μ = 0 := by
    rw [hint]; simp only [id]; ring
  have hb : ∀ᵐ z ∂μ, z ∈ Set.Icc (-x) (1 - x) := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ∈ Set.Icc (-x) (1 - x)} = (Set.Icc (-x) (1 - x))ᶜ := rfl
    rw [hμ, hset]
    refine bernoulliMeasure_apply_of_notMem_of_notMem p measurableSet_Icc.compl ?_ ?_ <;> simp
  have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := id)
      aemeasurable_id hb hc
  have hmg := hsg.mgf_le t
  have hnn : ‖(1 - x) - -x‖₊ = 1 := by
    have h : (1 - x) - -x = (1 : ℝ) := by ring
    rw [h]; simp
  have hcoef : (((‖(1 - x) - -x‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    rw [hnn]; push_cast; norm_num
  rw [ProbabilityTheory.mgf] at hmg
  simp only [id] at hmg
  rw [hint (fun z => Real.exp (t * z)), hcoef] at hmg
  have key : x * Real.exp (t * (1 - x)) + (1 - x) * Real.exp (t * -x)
      ≤ Real.exp (t ^ 2 / 8) := by
    refine hmg.trans_eq ?_
    congr 1; ring
  have h1 : Real.exp (t * x) * Real.exp (t * (1 - x)) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (t * x) * Real.exp (t * -x) = 1 := by
    rw [← Real.exp_add, show t * x + t * -x = 0 by ring, Real.exp_zero]
  have hstep := mul_le_mul_of_nonneg_left key (Real.exp_nonneg (t * x))
  calc 1 - x + x * Real.exp t
      = Real.exp (t * x) * (x * Real.exp (t * (1 - x)) + (1 - x) * Real.exp (t * -x)) := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (Real.exp (t * x)) x,
          mul_comm (Real.exp (t * x)) (1 - x), mul_assoc x, mul_assoc (1 - x), h1, h2]
        ring
    _ ≤ Real.exp (t * x) * Real.exp (t ^ 2 / 8) := hstep
    _ = Real.exp (t * x + t ^ 2 / 8) := (Real.exp_add _ _).symm

/-! ### The binomial head and tail polynomials -/

/-- One binomial term `C(r, j) x^j (1 - x)^(r - j)`. -/
def binomialTerm (r j : ℕ) (x : ℝ) : ℝ := (r.choose j : ℝ) * x ^ j * (1 - x) ^ (r - j)

/-- The lower binomial sum `∑_{j < k} C(r, j) x^j (1 - x)^(r - j)`. -/
def binomialHead (r k : ℕ) (x : ℝ) : ℝ := ∑ j ∈ range k, binomialTerm r j x

/-- The upper binomial tail `∑_{j = k}^{r} C(r, j) x^j (1 - x)^(r - j)`. -/
def binomialTail (r k : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Icc k r, binomialTerm r j x

theorem binomialTerm_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r j : ℕ) :
    0 ≤ binomialTerm r j x := by
  have h1 : (0 : ℝ) ≤ 1 - x := by linarith
  unfold binomialTerm
  positivity

theorem Icc_eq_Ico_succ (k r : ℕ) : Finset.Icc k r = Finset.Ico k (r + 1) := by
  ext j; simp

theorem Icc_subset_range_succ (k r : ℕ) : Finset.Icc k r ⊆ Finset.range (r + 1) := by
  intro j hj
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2)

/-- The full binomial sum is one. -/
theorem sum_binomialTerm_range (r : ℕ) (x : ℝ) :
    ∑ j ∈ range (r + 1), binomialTerm r j x = 1 := by
  have h := add_pow x (1 - x) r
  rw [show x + (1 - x) = (1 : ℝ) by ring, one_pow] at h
  calc ∑ j ∈ range (r + 1), binomialTerm r j x
      = ∑ m ∈ range (r + 1), x ^ m * (1 - x) ^ (r - m) * (r.choose m : ℝ) :=
        Finset.sum_congr rfl fun j _ => by unfold binomialTerm; ring
    _ = 1 := h.symm

/-- The head and the tail decompose the full binomial sum. -/
theorem binomialHead_add_binomialTail (r k : ℕ) (hk : k ≤ r + 1) (x : ℝ) :
    binomialHead r k x + binomialTail r k x = 1 := by
  rw [← sum_binomialTerm_range r x]
  unfold binomialHead binomialTail
  rw [Icc_eq_Ico_succ, Finset.range_eq_Ico, Finset.range_eq_Ico]
  exact Finset.sum_Ico_consecutive _ (Nat.zero_le k) hk

theorem binomialTail_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ) :
    0 ≤ binomialTail r k x :=
  Finset.sum_nonneg fun j _ => binomialTerm_nonneg hx0 hx1 r j

theorem binomialHead_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ) :
    0 ≤ binomialHead r k x :=
  Finset.sum_nonneg fun j _ => binomialTerm_nonneg hx0 hx1 r j

theorem binomialTail_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ) :
    binomialTail r k x ≤ 1 := by
  rw [← sum_binomialTerm_range r x]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_range_succ k r)
    fun j _ _ => binomialTerm_nonneg hx0 hx1 r j

theorem binomialHead_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ) (hk : k ≤ r + 1) :
    binomialHead r k x ≤ 1 := by
  rw [← sum_binomialTerm_range r x]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => binomialTerm_nonneg hx0 hx1 r j
  exact fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)

theorem continuous_binomialTerm (r j : ℕ) : Continuous (binomialTerm r j) := by
  unfold binomialTerm; fun_prop

theorem continuous_binomialTail (r k : ℕ) : Continuous (binomialTail r k) := by
  unfold binomialTail
  exact continuous_finsetSum _ fun j _ => continuous_binomialTerm r j

/-! ### The Chernoff bound -/

/-- The exponential moment of the binomial weights is the `r`-th power of a two-point moment. -/
theorem sum_binomialTerm_mul_exp (r : ℕ) (x c : ℝ) :
    ∑ j ∈ range (r + 1), binomialTerm r j x * Real.exp (c * j)
      = (x * Real.exp c + (1 - x)) ^ r := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold binomialTerm
  rw [mul_pow, mul_comm c (j : ℝ), Real.exp_nat_mul]
  ring

/-- Hoeffding's bound on the binomial exponential moment. -/
theorem sum_binomialTerm_mul_exp_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r : ℕ) (c : ℝ) :
    ∑ j ∈ range (r + 1), binomialTerm r j x * Real.exp (c * j)
      ≤ Real.exp ((r : ℝ) * (c * x + c ^ 2 / 8)) := by
  rw [sum_binomialTerm_mul_exp]
  have hbase : x * Real.exp c + (1 - x) ≤ Real.exp (c * x + c ^ 2 / 8) := by
    have h := one_sub_add_mul_exp_le_exp x hx0 hx1 c
    linarith
  have hpos : (0 : ℝ) ≤ x * Real.exp c + (1 - x) := by
    have : (0 : ℝ) ≤ 1 - x := by linarith
    positivity
  calc (x * Real.exp c + (1 - x)) ^ r ≤ (Real.exp (c * x + c ^ 2 / 8)) ^ r :=
        pow_le_pow_left₀ hpos hbase r
    _ = Real.exp ((r : ℝ) * (c * x + c ^ 2 / 8)) := (Real.exp_nat_mul _ _).symm

/-- Chernoff shift for the upper tail. -/
theorem binomialTail_le_exp_shift {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    binomialTail r k x ≤ Real.exp (-(lam * k) + (r : ℝ) * (lam * x + lam ^ 2 / 8)) := by
  have step1 : binomialTail r k x
      ≤ ∑ j ∈ Icc k r, binomialTerm r j x * Real.exp (lam * j) * Real.exp (-(lam * k)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hone : (1 : ℝ) ≤ Real.exp (lam * j) * Real.exp (-(lam * k)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc binomialTerm r j x = binomialTerm r j x * 1 := (mul_one _).symm
      _ ≤ binomialTerm r j x * (Real.exp (lam * j) * Real.exp (-(lam * k))) :=
          mul_le_mul_of_nonneg_left hone (binomialTerm_nonneg hx0 hx1 r j)
      _ = binomialTerm r j x * Real.exp (lam * j) * Real.exp (-(lam * k)) := by ring
  have step2 : ∑ j ∈ Icc k r, binomialTerm r j x * Real.exp (lam * j) * Real.exp (-(lam * k))
      = (∑ j ∈ Icc k r, binomialTerm r j x * Real.exp (lam * j)) * Real.exp (-(lam * k)) :=
    (Finset.sum_mul _ _ _).symm
  have step3 : ∑ j ∈ Icc k r, binomialTerm r j x * Real.exp (lam * j)
      ≤ ∑ j ∈ range (r + 1), binomialTerm r j x * Real.exp (lam * j) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_range_succ k r) fun j _ _ => ?_
    exact mul_nonneg (binomialTerm_nonneg hx0 hx1 r j) (Real.exp_nonneg _)
  calc binomialTail r k x
      ≤ (∑ j ∈ Icc k r, binomialTerm r j x * Real.exp (lam * j)) * Real.exp (-(lam * k)) := by
        rw [← step2]; exact step1
    _ ≤ Real.exp ((r : ℝ) * (lam * x + lam ^ 2 / 8)) * Real.exp (-(lam * k)) := by
        exact mul_le_mul_of_nonneg_right
          (step3.trans (sum_binomialTerm_mul_exp_le hx0 hx1 r lam)) (Real.exp_nonneg _)
    _ = Real.exp (-(lam * k) + (r : ℝ) * (lam * x + lam ^ 2 / 8)) := by
        rw [← Real.exp_add]; congr 1; ring

/-- Chernoff shift for the lower sum. -/
theorem binomialHead_le_exp_shift {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ)
    (hk : k ≤ r + 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    binomialHead r k x ≤ Real.exp (lam * ((k : ℝ) - 1) + (r : ℝ) * (-lam * x + lam ^ 2 / 8)) := by
  have step1 : binomialHead r k x
      ≤ ∑ j ∈ range k, binomialTerm r j x * Real.exp (-lam * j)
          * Real.exp (lam * ((k : ℝ) - 1)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : (j : ℝ) ≤ (k : ℝ) - 1 := by
      have : j + 1 ≤ k := Finset.mem_range.mp hj
      have : ((j : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast this
      linarith
    have hone : (1 : ℝ) ≤ Real.exp (-lam * j) * Real.exp (lam * ((k : ℝ) - 1)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc binomialTerm r j x = binomialTerm r j x * 1 := (mul_one _).symm
      _ ≤ binomialTerm r j x * (Real.exp (-lam * j) * Real.exp (lam * ((k : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hone (binomialTerm_nonneg hx0 hx1 r j)
      _ = binomialTerm r j x * Real.exp (-lam * j) * Real.exp (lam * ((k : ℝ) - 1)) := by ring
  have step2 : ∑ j ∈ range k, binomialTerm r j x * Real.exp (-lam * j)
        * Real.exp (lam * ((k : ℝ) - 1))
      = (∑ j ∈ range k, binomialTerm r j x * Real.exp (-lam * j))
          * Real.exp (lam * ((k : ℝ) - 1)) :=
    (Finset.sum_mul _ _ _).symm
  have step3 : ∑ j ∈ range k, binomialTerm r j x * Real.exp (-lam * j)
      ≤ ∑ j ∈ range (r + 1), binomialTerm r j x * Real.exp (-lam * j) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hk))
      fun j _ _ => ?_
    exact mul_nonneg (binomialTerm_nonneg hx0 hx1 r j) (Real.exp_nonneg _)
  have hsq : (-lam) ^ 2 / 8 = lam ^ 2 / 8 := by ring
  calc binomialHead r k x
      ≤ (∑ j ∈ range k, binomialTerm r j x * Real.exp (-lam * j))
          * Real.exp (lam * ((k : ℝ) - 1)) := by rw [← step2]; exact step1
    _ ≤ Real.exp ((r : ℝ) * (-lam * x + (-lam) ^ 2 / 8)) * Real.exp (lam * ((k : ℝ) - 1)) := by
        exact mul_le_mul_of_nonneg_right
          (step3.trans (sum_binomialTerm_mul_exp_le hx0 hx1 r (-lam))) (Real.exp_nonneg _)
    _ = Real.exp (lam * ((k : ℝ) - 1) + (r : ℝ) * (-lam * x + lam ^ 2 / 8)) := by
        rw [← Real.exp_add, hsq]; congr 1; ring

/-- **Hoeffding's upper-tail inequality for the binomial tail polynomial.** -/
theorem binomialTail_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hks : (r : ℝ) * x + r * s ≤ k) :
    binomialTail r k x ≤ Real.exp (-(2 * r * s ^ 2)) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simpa using binomialTail_le_one hx0 hx1 0 k
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hu0 : (r : ℝ) * s ≤ (k : ℝ) - r * x := by linarith
  have hu0' : (0 : ℝ) ≤ (k : ℝ) - r * x := le_trans (by positivity) hu0
  have hlam : (0 : ℝ) ≤ 4 * ((k : ℝ) - r * x) / r := by positivity
  have h := binomialTail_le_exp_shift hx0 hx1 r k hlam
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hexp : -(4 * ((k : ℝ) - r * x) / r * k)
      + (r : ℝ) * (4 * ((k : ℝ) - r * x) / r * x + (4 * ((k : ℝ) - r * x) / r) ^ 2 / 8)
      = -(2 * ((k : ℝ) - r * x) ^ 2 / r) := by
    field_simp
    ring
  rw [hexp, neg_le_neg_iff, le_div_iff₀ hrpos]
  have hsq : ((r : ℝ) * s) ^ 2 ≤ ((k : ℝ) - r * x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hu0 2
  nlinarith [hsq]

/-- **Hoeffding's lower-tail inequality for the binomial tail polynomial.** -/
theorem binomialHead_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r k : ℕ) (hk : k ≤ r + 1)
    {s : ℝ} (hs : 0 ≤ s) (hks : ((k : ℝ) - 1) + r * s ≤ r * x) :
    binomialHead r k x ≤ Real.exp (-(2 * r * s ^ 2)) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simpa using binomialHead_le_one hx0 hx1 0 k hk
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hu0 : (r : ℝ) * s ≤ (r : ℝ) * x - ((k : ℝ) - 1) := by linarith
  have hu0' : (0 : ℝ) ≤ (r : ℝ) * x - ((k : ℝ) - 1) := le_trans (by positivity) hu0
  have hlam : (0 : ℝ) ≤ 4 * ((r : ℝ) * x - ((k : ℝ) - 1)) / r := by positivity
  have h := binomialHead_le_exp_shift hx0 hx1 r k hk hlam
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hexp : 4 * ((r : ℝ) * x - ((k : ℝ) - 1)) / r * ((k : ℝ) - 1)
      + (r : ℝ) * (-(4 * ((r : ℝ) * x - ((k : ℝ) - 1)) / r) * x
        + (4 * ((r : ℝ) * x - ((k : ℝ) - 1)) / r) ^ 2 / 8)
      = -(2 * ((r : ℝ) * x - ((k : ℝ) - 1)) ^ 2 / r) := by
    field_simp
    ring
  rw [hexp, neg_le_neg_iff, le_div_iff₀ hrpos]
  have hsq : ((r : ℝ) * s) ^ 2 ≤ ((r : ℝ) * x - ((k : ℝ) - 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hu0 2
  nlinarith [hsq]

/-! ### The beta density and the derivative identity -/

/-- The `Beta (k, r - k + 1)` density in the normalization produced by differentiating the
binomial tail polynomial. -/
def betaKernel (r k : ℕ) (u : ℝ) : ℝ :=
  (r : ℝ) * ((r - 1).choose (k - 1) : ℝ) * u ^ (k - 1) * (1 - u) ^ (r - k)

theorem betaKernel_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (r k : ℕ) : 0 ≤ betaKernel r k u := by
  have h : (0 : ℝ) ≤ 1 - u := by linarith
  unfold betaKernel
  positivity

theorem continuous_betaKernel (r k : ℕ) : Continuous (betaKernel r k) := by
  unfold betaKernel; fun_prop

theorem betaKernel_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (r k : ℕ) :
    betaKernel r k u ≤ (r : ℝ) * ((r - 1).choose (k - 1) : ℝ) := by
  have h1 : (0 : ℝ) ≤ 1 - u := by linarith
  have hp1 : u ^ (k - 1) ≤ 1 := pow_le_one₀ hu0 hu1
  have hp2 : (1 - u) ^ (r - k) ≤ 1 := pow_le_one₀ h1 (by linarith)
  have hc : (0 : ℝ) ≤ (r : ℝ) * ((r - 1).choose (k - 1) : ℝ) := by positivity
  unfold betaKernel
  calc (r : ℝ) * ((r - 1).choose (k - 1) : ℝ) * u ^ (k - 1) * (1 - u) ^ (r - k)
      ≤ (r : ℝ) * ((r - 1).choose (k - 1) : ℝ) * 1 * 1 := by gcongr
    _ = (r : ℝ) * ((r - 1).choose (k - 1) : ℝ) := by ring

/-- The two Pascal-type absorption identities used to telescope the derivative. -/
theorem cast_choose_absorb_left {r j : ℕ} (hr : 1 ≤ r) (hj : 1 ≤ j) :
    (j : ℝ) * (r.choose j : ℝ) = (r : ℝ) * ((r - 1).choose (j - 1) : ℝ) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h : (r' + 1) * r'.choose j' = (r' + 1).choose (j' + 1) * (j' + 1) :=
    Nat.add_one_mul_choose_eq r' j'
  have hR : ((r' + 1 : ℕ) : ℝ) * (r'.choose j' : ℝ)
      = (((r' + 1).choose (j' + 1) : ℕ) : ℝ) * ((j' + 1 : ℕ) : ℝ) := by exact_mod_cast h
  simp only [Nat.add_sub_cancel]
  push_cast at hR ⊢
  linarith

theorem cast_choose_absorb_right {r j : ℕ} (hr : 1 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r) :
    (((r - j : ℕ) : ℝ)) * (r.choose j : ℝ) = (r : ℝ) * ((r - 1).choose j : ℝ) := by
  have hpascal : r.choose j = (r - 1).choose (j - 1) + (r - 1).choose j := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simpa using Nat.choose_succ_succ r' j'
  have hA := cast_choose_absorb_left hr hj
  have hcast : ((r - j : ℕ) : ℝ) = (r : ℝ) - (j : ℝ) := Nat.cast_sub hjr
  have hp : (r.choose j : ℝ) = ((r - 1).choose (j - 1) : ℝ) + ((r - 1).choose j : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hpascal
  rw [hcast]
  linear_combination (r : ℝ) * hp - hA

/-- **The derivative of the binomial tail polynomial is the beta density.** -/
theorem hasDerivAt_binomialTail (r k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) (x : ℝ) :
    HasDerivAt (binomialTail r k) (betaKernel r k x) x := by
  have hr : 1 ≤ r := le_trans hk1 hkr
  let g : ℕ → ℝ := fun j => ((r - 1).choose (j - 1) : ℝ) * x ^ (j - 1) * (1 - x) ^ (r - j)
  have hg : ∀ j : ℕ, g j
      = ((r - 1).choose (j - 1) : ℝ) * x ^ (j - 1) * (1 - x) ^ (r - j) := fun _ => rfl
  have hterm : ∀ j ∈ Finset.Icc k r,
      HasDerivAt (fun y : ℝ => binomialTerm r j y) ((r : ℝ) * (g j - g (j + 1))) x := by
    intro j hj
    obtain ⟨hkj, hjr⟩ := Finset.mem_Icc.mp hj
    have hj1 : 1 ≤ j := le_trans hk1 hkj
    have hd1 : HasDerivAt (fun y : ℝ => y ^ j) ((j : ℝ) * x ^ (j - 1)) x := hasDerivAt_pow j x
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hd2 : HasDerivAt (fun y : ℝ => (1 - y) ^ (r - j))
        (((r - j : ℕ) : ℝ) * (1 - x) ^ (r - j - 1) * (-1)) x :=
      (hasDerivAt_pow (r - j) (1 - x)).comp x hsub
    have hd3 := (hd1.mul hd2).const_mul ((r.choose j : ℝ))
    have hfun : (fun y : ℝ => binomialTerm r j y)
        = fun y : ℝ => (r.choose j : ℝ) * (y ^ j * (1 - y) ^ (r - j)) := by
      funext y; unfold binomialTerm; ring
    have hderiv : (r : ℝ) * (g j - g (j + 1))
        = (r.choose j : ℝ) * ((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (r - j)
            + x ^ j * (((r - j : ℕ) : ℝ) * (1 - x) ^ (r - j - 1) * (-1))) := by
      have hA := cast_choose_absorb_left hr hj1
      have hB := cast_choose_absorb_right hr hj1 hjr
      have he1 : (j + 1) - 1 = j := by omega
      have he2 : r - (j + 1) = r - j - 1 := by omega
      rw [hg j, hg (j + 1), he1, he2]
      linear_combination (-(x ^ (j - 1) * (1 - x) ^ (r - j))) * hA
        + (x ^ j * (1 - x) ^ (r - j - 1)) * hB
    rw [hfun, hderiv]
    exact hd3
  have hfun2 : binomialTail r k = ∑ i ∈ Finset.Icc k r, fun y : ℝ => binomialTerm r i y := by
    funext y
    simp [binomialTail, Finset.sum_apply]
  have hsum : HasDerivAt (binomialTail r k)
      (∑ j ∈ Finset.Icc k r, (r : ℝ) * (g j - g (j + 1))) x := by
    rw [hfun2]; exact HasDerivAt.sum hterm
  have htel : ∑ j ∈ Finset.Icc k r, (r : ℝ) * (g j - g (j + 1)) = betaKernel r k x := by
    rw [← Finset.mul_sum]
    have hIco : Finset.Icc k r = Finset.Ico k (r + 1) := Icc_eq_Ico_succ k r
    rw [hIco, Finset.sum_Ico_eq_sum_range]
    have hshift : ∑ i ∈ range (r + 1 - k), (g (k + i) - g (k + i + 1))
        = g (k + 0) - g (k + (r + 1 - k)) := by
      have := Finset.sum_range_sub' (fun i => g (k + i)) (r + 1 - k)
      simpa [Nat.add_assoc] using this
    rw [hshift]
    have hk' : k + (r + 1 - k) = r + 1 := by omega
    rw [hk']
    have hzero : g (r + 1) = 0 := by
      have hc : (r - 1).choose (r + 1 - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hg (r + 1), hc]
      simp
    rw [hzero, Nat.add_zero, sub_zero]
    unfold betaKernel
    rw [hg k]
    ring
  rw [htel] at hsum
  exact hsum

theorem binomialTail_zero_eq_zero (r k : ℕ) (hk1 : 1 ≤ k) : binomialTail r k 0 = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj1 : 1 ≤ j := le_trans hk1 (Finset.mem_Icc.mp hj).1
  unfold binomialTerm
  rw [zero_pow (by omega)]
  ring

theorem binomialTail_one_eq_one (r k : ℕ) (hkr : k ≤ r) : binomialTail r k 1 = 1 := by
  have hmem : r ∈ Finset.Icc k r := Finset.mem_Icc.mpr ⟨hkr, le_refl r⟩
  unfold binomialTail
  rw [← Finset.add_sum_erase _ _ hmem]
  have hlast : binomialTerm r r 1 = 1 := by
    unfold binomialTerm; simp
  have hrest : ∑ j ∈ (Finset.Icc k r).erase r, binomialTerm r j 1 = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjr : j ≠ r := (Finset.mem_erase.mp hj).1
    have hjle : j ≤ r := (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).2
    unfold binomialTerm
    rw [show (1 : ℝ) - 1 = 0 by ring, zero_pow (by omega)]
    ring
  rw [hlast, hrest, add_zero]

/-- **The beta-coarea representation.**  On `[0, 1]` the binomial tail polynomial is the integral
of the beta density up to the threshold. -/
theorem binomialTail_eq_intervalIntegral (r k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) (x : ℝ) :
    ∫ u in (0 : ℝ)..x, betaKernel r k u = binomialTail r k x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_binomialTail r k hk1 hkr y)
    ((continuous_betaKernel r k).intervalIntegrable _ _)]
  rw [binomialTail_zero_eq_zero r k hk1, sub_zero]

/-- **The beta density has unit mass.** -/
theorem intervalIntegral_betaKernel_eq_one (r k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    ∫ u in (0 : ℝ)..1, betaKernel r k u = 1 := by
  rw [binomialTail_eq_intervalIntegral r k hk1 hkr, binomialTail_one_eq_one r k hkr]

/-- The binomial tail polynomial is monotone on the unit interval. -/
theorem binomialTail_monotoneOn (r k : ℕ) : MonotoneOn (binomialTail r k) (Set.Icc (0 : ℝ) 1) := by
  rcases Nat.lt_or_ge r k with hrk | hkr
  · have hzero : ∀ y : ℝ, binomialTail r k y = 0 := by
      intro y
      refine Finset.sum_eq_zero fun j hj => ?_
      exact absurd (le_trans (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2) (by omega)
    intro u _ v _ _
    rw [hzero u, hzero v]
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have hone : ∀ y : ℝ, binomialTail r 0 y = 1 := by
      intro y
      have := binomialHead_add_binomialTail r 0 (by omega) y
      simpa [binomialHead] using this
    intro u _ v _ _
    rw [hone u, hone v]
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (Continuous.continuousOn (by
      have : ∀ y : ℝ, HasDerivAt (binomialTail r k) (betaKernel r k y) y :=
        fun y => hasDerivAt_binomialTail r k hk1 hkr y
      exact continuous_iff_continuousAt.mpr fun y => (this y).continuousAt))
    (fun y _ => ((hasDerivAt_binomialTail r k hk1 hkr y).differentiableAt).differentiableWithinAt)
    (fun y hy => ?_)
  have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hy
  rw [(hasDerivAt_binomialTail r k hk1 hkr y).deriv]
  exact betaKernel_nonneg (le_of_lt hy'.1) (le_of_lt hy'.2) r k

/-! ### The threshold sandwich -/

/-- The replica threshold `⌈r (a + b) / 2⌉`. -/
def replicaThreshold (r : ℕ) (a b : ℝ) : ℕ := ⌈(r : ℝ) * ((a + b) / 2)⌉₊

theorem replicaThreshold_le {r : ℕ} {a b : ℝ} (hba : b < a) (ha : a < 1) :
    replicaThreshold r a b ≤ r := by
  refine Nat.ceil_le.mpr ?_
  have h1 : (a + b) / 2 ≤ 1 := by linarith
  have h2 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith [h1, h2]

theorem le_replicaThreshold {r : ℕ} {a b : ℝ} :
    (r : ℝ) * ((a + b) / 2) ≤ (replicaThreshold r a b : ℝ) := Nat.le_ceil _

theorem replicaThreshold_lt {r : ℕ} {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    ((replicaThreshold r a b : ℝ)) < (r : ℝ) * ((a + b) / 2) + 1 := by
  refine Nat.ceil_lt_add_one ?_
  have hab : (0 : ℝ) ≤ (a + b) / 2 := by linarith
  exact mul_nonneg (Nat.cast_nonneg r) hab

/-- **Theorem A, upper half.**  Below the lower threshold `b` the bounded replica test is
exponentially small. -/
theorem binomialTail_replicaThreshold_le {r : ℕ} {a b x : ℝ} (hba : b < a)
    (ha : a < 1) (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    binomialTail r (replicaThreshold r a b) x ≤ Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) := by
  have hx1 : x ≤ 1 := by linarith
  have hs : (0 : ℝ) ≤ (a - b) / 2 := by linarith
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hks : (r : ℝ) * x + r * ((a - b) / 2) ≤ (replicaThreshold r a b : ℝ) := by
    refine le_trans ?_ (le_replicaThreshold (r := r) (a := a) (b := b))
    nlinarith
  have h := binomialTail_le_exp hx0 hx1 r (replicaThreshold r a b) hs hks
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hid : 2 * (r : ℝ) * ((a - b) / 2) ^ 2 = (r : ℝ) * (a - b) ^ 2 / 2 := by ring
  linarith

/-- **Theorem A, lower half.**  Above the upper threshold `a` the bounded replica test is
exponentially close to one. -/
theorem one_sub_le_binomialTail_replicaThreshold {r : ℕ} {a b x : ℝ} (hb : 0 < b) (hba : b < a)
    (ha : a < 1) (hax : a ≤ x) (hx1 : x ≤ 1) :
    1 - Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2))
      ≤ binomialTail r (replicaThreshold r a b) x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : (0 : ℝ) ≤ (a - b) / 2 := by linarith
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hkr : replicaThreshold r a b ≤ r := replicaThreshold_le hba ha
  have hks : ((replicaThreshold r a b : ℝ) - 1) + r * ((a - b) / 2) ≤ (r : ℝ) * x := by
    have h1 := replicaThreshold_lt (r := r) (a := a) (b := b) hb hba
    have h2 : (r : ℝ) * a ≤ (r : ℝ) * x := by nlinarith
    nlinarith
  have h := binomialHead_le_exp hx0 hx1 r (replicaThreshold r a b) (by omega) hs hks
  have hsplit := binomialHead_add_binomialTail r (replicaThreshold r a b) (by omega) x
  have hcoef : 2 * (r : ℝ) * ((a - b) / 2) ^ 2 = (r : ℝ) * (a - b) ^ 2 / 2 := by ring
  rw [hcoef] at h
  linarith

/-- **Theorem A, equation (7).**  Once the replica order passes `2 log 2 / δ²` the bounded test
recovers the high-overlap mass up to a factor two. -/
theorem measure_le_two_mul_binomialTail {r : ℕ} {a b x : ℝ} (hb : 0 < b) (hba : b < a)
    (ha : a < 1) (hax : a ≤ x) (hx1 : x ≤ 1)
    (hr : 2 * Real.log 2 / (a - b) ^ 2 ≤ (r : ℝ)) :
    (1 : ℝ) ≤ 2 * binomialTail r (replicaThreshold r a b) x := by
  have hδ : (0 : ℝ) < (a - b) ^ 2 := by positivity
  have hlog : Real.log 2 ≤ (r : ℝ) * (a - b) ^ 2 / 2 := by
    rw [div_le_iff₀ hδ] at hr
    linarith
  have hhalf : Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) ≤ 1 / 2 := by
    have h1 : Real.exp (-((r : ℝ) * (a - b) ^ 2 / 2)) ≤ Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [h2] at h1; exact h1
  have h := one_sub_le_binomialTail_replicaThreshold (r := r) hb hba ha hax hx1
  linarith

end

end GaloisForLFunctions.HTGeometry
