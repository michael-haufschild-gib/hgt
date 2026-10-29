import GaloisForLFunctions.HeckeKreinToeplitz.TheGlobalLawIsTheOneSidedSquareRootCount
import GaloisForLFunctions.RHTower.LiouvilleExponentialSumOneSidedPower

/-!
# The parity form of the global law

Index zero of the Weil kernel is a one-sided square-root count (`global_law_count`). This module
writes that law as counts of the two **parity classes** `{n : λ(n) = +1}` and `{n : λ(n) = −1}` of
the Liouville function, the classes a producer would have to bound. Over `𝔽_q` the corresponding
classes are the points of a curve and of its quadratic twist, and Stepanov bounds both from above.

**Two classes** (`riemannHypothesis_iff_parityClasses_upper`). The classes partition `{1, …, N}`
and differ by the Liouville sum `L(N)`, so upper counts `N/2 + C(N+1)^{½+δ}` for both are
`|L(N)| ≤ 2C(N+1)^{½+δ}`, which is RH.

**One class suffices** (`riemannHypothesis_iff_oddClass_upper`, `negIndex_zetaKernel_eq_zero_iff_oddClass_upper`).
In harmonic–exponential weighting, `O(t) = Σ_{λ(n)=−1} e^{−nt}/n` and `H(t) = Σ e^{−nt}/n`, the
Liouville series is `J = H − 2O` (`liouvilleExpSum_eq_harmonic_sub_oddClass`), and the one-sided law
`J(t) ≥ −C t^{½−ε}` is RH. So the upper count `O(t) ≤ (H(t) + C t^{½−ε})/2` for the odd class alone
(the class that contains the primes) is index zero of `K_ζ`.

**Contrast with `𝔽_q`.** There an upper count is blind to real outer Frobenius eigenvalues, and the
split datum `±2, ±½` shows that the count of a curve together with that of its twist does not
complete (`one_twist_does_not_complete`); the twist tower does. Over `ℤ` the corresponding blind spot
is a real zero of `ζ` in `(½, 1)`, of which there is none, so one parity class carries the whole
law. What is missing over `ℤ` is not a second class but a producer for the first.
-/

open Finset Filter
open GaloisForLFunctions.HeckeKreinToeplitz RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### Two parity classes -/

theorem liouville_eq_one_or_neg_one {n : ℕ} (hn : n ≠ 0) :
    ArithmeticFunction.liouville n = 1 ∨ ArithmeticFunction.liouville n = -1 := by
  rw [ArithmeticFunction.liouville_apply hn]
  exact neg_one_pow_eq_or ℤ _

/-- The parity class `{1 ≤ n ≤ N : λ(n) = ε}`, counted. -/
def parityCount (ε : ℤ) (N : ℕ) : ℕ :=
  ((Icc 1 N).filter fun n => ArithmeticFunction.liouville n = ε).card

theorem parityCount_add (N : ℕ) : (parityCount 1 N : ℝ) + parityCount (-1) N = N := by
  have hdisj : Disjoint ((Icc 1 N).filter fun n => ArithmeticFunction.liouville n = 1)
      ((Icc 1 N).filter fun n => ArithmeticFunction.liouville n = -1) :=
    disjoint_filter.mpr fun n _ h1 h2 => by rw [h1] at h2; exact absurd h2 (by decide)
  have hunion : ((Icc 1 N).filter fun n => ArithmeticFunction.liouville n = 1) ∪
      ((Icc 1 N).filter fun n => ArithmeticFunction.liouville n = -1) = Icc 1 N := by
    ext n
    simp only [mem_union, mem_filter, mem_Icc]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases liouville_eq_one_or_neg_one (by omega : n ≠ 0) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have := card_union_of_disjoint hdisj
  rw [hunion, Nat.card_Icc] at this
  unfold parityCount
  exact_mod_cast (by omega : N + 1 - 1 = _).trans this |>.symm

/-- The two classes differ by the Liouville sum `L(N) = Σ_{n ≤ N} λ(n)`. -/
theorem parityCount_sub (N : ℕ) :
    (parityCount 1 N : ℝ) - parityCount (-1) N = sourcePartialSum liouvilleR N := by
  unfold parityCount sourcePartialSum liouvilleR
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) fun n => ArithmeticFunction.liouville n = 1]
  have h1 : ∑ n ∈ (Icc 1 N).filter (fun n => ArithmeticFunction.liouville n = 1),
      ((ArithmeticFunction.liouville n : ℤ) : ℝ) =
        ((Icc 1 N).filter fun n => ArithmeticFunction.liouville n = 1).card := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    exact sum_congr rfl fun n hn => by rw [(mem_filter.mp hn).2]; simp
  have h2 : ∑ n ∈ (Icc 1 N).filter (fun n => ¬ ArithmeticFunction.liouville n = 1),
      ((ArithmeticFunction.liouville n : ℤ) : ℝ) =
        -((Icc 1 N).filter fun n => ArithmeticFunction.liouville n = -1).card := by
    rw [card_eq_sum_ones, Nat.cast_sum, ← sum_neg_distrib]
    rw [filter_congr (q := fun n => ArithmeticFunction.liouville n = -1) fun n hn => by
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      rcases liouville_eq_one_or_neg_one hn0 with h | h <;> simp [h]]
    exact sum_congr rfl fun n hn => by rw [(mem_filter.mp hn).2]; simp
  rw [h1, h2]; ring

/-- **Two parity classes.** RH holds iff for every `δ > 0` both Liouville parity classes have the
upper count `N/2 + C(N+1)^{½+δ}`. -/
theorem riemannHypothesis_iff_parityClasses_upper :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (parityCount 1 N : ℝ) ≤ N / 2 + C * ((N : ℝ) + 1) ^ (1 / 2 + δ) ∧
        (parityCount (-1) N : ℝ) ≤ N / 2 + C * ((N : ℝ) + 1) ^ (1 / 2 + δ) := by
  rw [riemannHypothesis_iff_forall_liouvilleSummatory_le]
  refine forall₂_congr fun δ _ => ⟨fun ⟨C, hC, h⟩ => ⟨C / 2, by positivity, fun N => ?_⟩,
    fun ⟨C, hC, h⟩ => ⟨2 * C, by positivity, fun N => ?_⟩⟩
  · have hs := parityCount_add N
    have hd := parityCount_sub N
    have hb := abs_le.mp (h N)
    constructor <;> nlinarith
  · have hs := parityCount_add N
    have hd := parityCount_sub N
    obtain ⟨h1, h2⟩ := h N
    rw [abs_le]
    constructor <;> nlinarith

/-! ### One parity class -/

/-- The harmonic–exponential mass of all integers, `H(t) = Σ e^{−nt}/n`. -/
def harmonicExp (t : ℝ) : ℝ := ∑' n : ℕ, (1 / (n : ℝ)) * Real.exp (-(n * t))

/-- The harmonic–exponential mass of the odd class, `O(t) = Σ_{λ(n) = −1} e^{−nt}/n`. -/
def oddClassSum (t : ℝ) : ℝ :=
  ∑' n : ℕ, (if ArithmeticFunction.liouville n = -1 then 1 / (n : ℝ) else 0) * Real.exp (-(n * t))

theorem summable_bounded_mul_exp {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1) :
    Summable fun n : ℕ => a n * Real.exp (-(n * t)) := by
  have hg : Summable fun n : ℕ => Real.exp (n * (-t)) :=
    Real.summable_exp_nat_mul_iff.mpr (by linarith)
  refine Summable.of_norm_bounded hg fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), show -(n * t) = n * (-t) by ring]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (ha n)

theorem abs_one_div_nat_le (n : ℕ) : |1 / (n : ℝ)| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [abs_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ (by exact_mod_cast hn) (by positivity)

/-- **The Liouville series splits by parity**: `J = H − 2O`. -/
theorem liouvilleExpSum_eq_harmonic_sub_oddClass {t : ℝ} (ht : 0 < t) :
    liouvilleExpSum t = harmonicExp t - 2 * oddClassSum t := by
  have hH := summable_bounded_mul_exp ht abs_one_div_nat_le
  have hO := summable_bounded_mul_exp ht (a := fun n =>
    if ArithmeticFunction.liouville n = -1 then 1 / (n : ℝ) else 0) fun n => by
      split_ifs
      · exact abs_one_div_nat_le n
      · simp
  unfold liouvilleExpSum harmonicExp oddClassSum
  rw [← tsum_mul_left, ← hH.tsum_sub (hO.mul_left 2)]
  refine tsum_congr fun n => ?_
  unfold liouvilleExpCoeff
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rcases liouville_eq_one_or_neg_one hn.ne' with h | h
    · simp [h]
    · simp [h]; ring

/-- **One parity class is the global law.** RH holds iff for every `ε ∈ (0, ½)` the odd class has
the upper count `O(t) ≤ (H(t) + C t^{½−ε})/2` for all small `t > 0`. -/
theorem riemannHypothesis_iff_oddClass_upper :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C t₀ : ℝ, 0 < t₀ ∧
      ∀ t, 0 < t → t ≤ t₀ → oddClassSum t ≤ (harmonicExp t + C * t ^ (1 / 2 - ε)) / 2 := by
  rw [riemannHypothesis_iff_forall_liouvilleExpSum_lower]
  refine forall₃_congr fun ε _ _ => exists₂_congr fun C t₀ => and_congr_right fun _ =>
    forall₃_congr fun t ht _ => ?_
  rw [liouvilleExpSum_eq_harmonic_sub_oddClass ht]
  constructor <;> intro h <;> linarith

/-- **Index zero of the Weil kernel is an upper count for one parity class.** -/
theorem negIndex_zetaKernel_eq_zero_iff_oddClass_upper :
    negIndex zetaKernel = 0 ↔ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C t₀ : ℝ, 0 < t₀ ∧
      ∀ t, 0 < t → t ≤ t₀ → oddClassSum t ≤ (harmonicExp t + C * t ^ (1 / 2 - ε)) / 2 := by
  rw [← riemannHypothesis_iff_negIndex_zetaKernel_eq_zero, riemannHypothesis_iff_oddClass_upper]

end GaloisForLFunctions.ArithmeticKreinLangerTheory
