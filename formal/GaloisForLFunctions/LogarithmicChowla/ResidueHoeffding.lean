import Mathlib

/-!
# Hoeffding's inequality on a finite product

Let `y` be uniform on a finite product `Π_i Y_i` and `W_i : Y_i → ℝ` have mean zero and `|W_i| ≤ B`.
Then the number of `y` with `Σ_i W_i(y_i) ≥ t` is at most `exp(−t²/(2|ι|B²))·|Π_i Y_i|`
(`card_sum_ge_le`), and twice that bounds `|Σ_i W_i(y_i)| ≥ t` (`card_abs_sum_ge_le`).

* Hoeffding's lemma: `|w| ≤ B` gives `e^{sw} ≤ ((B−w)e^{−sB} + (B+w)e^{sB})/(2B)` by convexity, so a
  mean-zero `W` has `avg e^{sW} ≤ cosh(sB) ≤ e^{s²B²/2}` (`sum_exp_mul_le`).
* The exponential moment of the sum factors over the product (`Finset.prod_univ_sum`), and Markov
  with `s = t/(|ι|B²)` gives the tail.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Real

noncomputable section

/-- **Hoeffding's lemma** for a uniform finite law. -/
theorem sum_exp_mul_le {Y : Type*} [Fintype Y] (W : Y → ℝ) {B : ℝ} (hB : 0 < B)
    (hW : ∀ y, |W y| ≤ B) (h0 : ∑ y, W y = 0) (s : ℝ) :
    ∑ y, exp (s * W y) ≤ Fintype.card Y * exp (s ^ 2 * B ^ 2 / 2) := by
  have hconv : ∀ y, exp (s * W y)
      ≤ (B - W y) / (2 * B) * exp (-(s * B)) + (B + W y) / (2 * B) * exp (s * B) := by
    intro y
    obtain ⟨hl, hr⟩ := abs_le.mp (hW y)
    have ha : 0 ≤ (B - W y) / (2 * B) := div_nonneg (by linarith) (by linarith)
    have hb : 0 ≤ (B + W y) / (2 * B) := div_nonneg (by linarith) (by linarith)
    have hab : (B - W y) / (2 * B) + (B + W y) / (2 * B) = 1 := by
      field_simp
      ring
    have h := convexOn_exp.2 (Set.mem_univ (-(s * B))) (Set.mem_univ (s * B)) ha hb hab
    simp only [smul_eq_mul] at h
    have harg : (B - W y) / (2 * B) * -(s * B) + (B + W y) / (2 * B) * (s * B) = s * W y := by
      field_simp
      ring
    rwa [harg] at h
  calc ∑ y, exp (s * W y)
      ≤ ∑ y, ((B - W y) / (2 * B) * exp (-(s * B)) + (B + W y) / (2 * B) * exp (s * B)) :=
        sum_le_sum fun y _ => hconv y
    _ = Fintype.card Y * ((exp (-(s * B)) + exp (s * B)) / 2) := by
        have hsplit : ∀ y, (B - W y) / (2 * B) * exp (-(s * B)) + (B + W y) / (2 * B) * exp (s * B)
            = (exp (-(s * B)) + exp (s * B)) / 2
              + W y * ((exp (s * B) - exp (-(s * B))) / (2 * B)) := by
          intro y
          field_simp
          ring
        simp only [hsplit, sum_add_distrib, ← sum_mul, h0, zero_mul, add_zero, sum_const,
          card_univ, nsmul_eq_mul]
    _ = Fintype.card Y * cosh (s * B) := by rw [cosh_eq]; ring
    _ ≤ Fintype.card Y * exp (s ^ 2 * B ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have := cosh_le_exp_half_sq (s * B)
        rwa [mul_pow] at this

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]

/-- **Hoeffding's inequality**, upper tail, for the uniform law on `Π_i Y_i`. -/
theorem card_sum_ge_le (W : ∀ i, Y i → ℝ) {B : ℝ} (hB : 0 < B) (hW : ∀ i y, |W i y| ≤ B)
    (h0 : ∀ i, ∑ y, W i y = 0) {t : ℝ} (ht : 0 ≤ t) :
    ((univ.filter fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i)).card : ℝ)
      ≤ exp (-(t ^ 2 / (2 * Fintype.card ι * B ^ 2))) * Fintype.card (∀ i, Y i) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hι | hι
  · have : (2 * (Fintype.card ι : ℝ) * B ^ 2) = 0 := by rw [hι]; simp
    rw [this, div_zero, neg_zero, exp_zero, one_mul]
    exact_mod_cast card_le_univ _
  have hιR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  set s : ℝ := t / (Fintype.card ι * B ^ 2) with hs
  have hs0 : 0 ≤ s := by positivity
  -- Markov: each counted `y` has `e^{s t} ≤ e^{s Σ W}`
  have hmarkov : ((univ.filter fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i)).card : ℝ) * exp (s * t)
      ≤ ∑ y : (∀ i, Y i), exp (s * ∑ i, W i (y i)) := by
    rw [← nsmul_eq_mul, ← sum_const]
    calc ∑ _y ∈ univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i)), exp (s * t)
        ≤ ∑ y ∈ univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i)),
            exp (s * ∑ i, W i (y i)) :=
          sum_le_sum fun y hy => exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (mem_filter.mp hy).2 hs0)
      _ ≤ ∑ y : (∀ i, Y i), exp (s * ∑ i, W i (y i)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (exp_pos _).le
  -- the exponential moment factors
  have hfactor : ∑ y : (∀ i, Y i), exp (s * ∑ i, W i (y i))
      = ∏ i, ∑ y, exp (s * W i y) := by
    rw [prod_univ_sum]
    simp only [Fintype.piFinset_univ, mul_sum, exp_sum]
  have hprod : ∏ i, ∑ y, exp (s * W i y)
      ≤ ∏ i, ((Fintype.card (Y i) : ℝ) * exp (s ^ 2 * B ^ 2 / 2)) :=
    prod_le_prod (fun i _ => sum_nonneg fun _ _ => (exp_pos _).le)
      fun i _ => sum_exp_mul_le (W i) hB (hW i) (h0 i) s
  have hcard : ∏ i, ((Fintype.card (Y i) : ℝ) * exp (s ^ 2 * B ^ 2 / 2))
      = Fintype.card (∀ i, Y i) * exp (Fintype.card ι * (s ^ 2 * B ^ 2 / 2)) := by
    rw [prod_mul_distrib, prod_const, card_univ, ← exp_nat_mul, Fintype.card_pi]
    push_cast
    ring_nf
  have hexp : s * t - Fintype.card ι * (s ^ 2 * B ^ 2 / 2)
      = t ^ 2 / (2 * Fintype.card ι * B ^ 2) := by
    rw [hs]
    field_simp
    ring
  have hall := hmarkov.trans (hfactor ▸ hprod.trans hcard.le)
  have hpos : 0 < exp (s * t) := exp_pos _
  rw [← le_div_iff₀ hpos, mul_div_assoc, ← exp_sub] at hall
  calc ((univ.filter fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i)).card : ℝ)
      ≤ Fintype.card (∀ i, Y i) * exp (Fintype.card ι * (s ^ 2 * B ^ 2 / 2) - s * t) := hall
    _ = exp (-(t ^ 2 / (2 * Fintype.card ι * B ^ 2))) * Fintype.card (∀ i, Y i) := by
        rw [mul_comm, ← hexp, neg_sub]

/-- **Hoeffding's inequality**, two-sided. -/
theorem card_abs_sum_ge_le (W : ∀ i, Y i → ℝ) {B : ℝ} (hB : 0 < B) (hW : ∀ i y, |W i y| ≤ B)
    (h0 : ∀ i, ∑ y, W i y = 0) {t : ℝ} (ht : 0 ≤ t) :
    ((univ.filter fun y : (∀ i, Y i) => t ≤ |∑ i, W i (y i)|).card : ℝ)
      ≤ 2 * exp (-(t ^ 2 / (2 * Fintype.card ι * B ^ 2))) * Fintype.card (∀ i, Y i) := by
  classical
  have hup := card_sum_ge_le W hB hW h0 ht
  have hdown := card_sum_ge_le (fun i y => -W i y) hB (fun i y => by rw [abs_neg]; exact hW i y)
    (fun i => by rw [sum_neg_distrib, h0 i, neg_zero]) ht
  have hsub : univ.filter (fun y : (∀ i, Y i) => t ≤ |∑ i, W i (y i)|)
      ⊆ univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i))
        ∪ univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, -W i (y i)) := by
    intro y hy
    rw [mem_filter] at hy
    rw [mem_union, mem_filter, mem_filter, sum_neg_distrib]
    rcases le_abs'.mp hy.2 with h | h
    · exact Or.inr ⟨mem_univ _, by linarith⟩
    · exact Or.inl ⟨mem_univ _, h⟩
  calc ((univ.filter fun y : (∀ i, Y i) => t ≤ |∑ i, W i (y i)|).card : ℝ)
      ≤ ((univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i))
          ∪ univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, -W i (y i))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ((univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, W i (y i))).card : ℝ)
          + ((univ.filter (fun y : (∀ i, Y i) => t ≤ ∑ i, -W i (y i))).card : ℝ) := by
        exact_mod_cast card_union_le _ _
    _ ≤ _ := by linarith

end

end GaloisForLFunctions.LogarithmicChowla
