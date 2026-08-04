import GaloisForLFunctions.RHTower.Sieve.MRInterface

/-!
# The fibre decomposition of the balanced pair sum

The balanced pairs `(n₁, n₂)` are those with `x ≤ n₁n₂ ≤ x + h√x` and `√x ≤ n₁ ≤ 2√x`.  Fixing the
outer factor `n₁ = a` leaves for `n₂` an interval determined by `a`, so the pair sum is iterated:

    ∑_{(a,b) balanced} f(a) f(b)  =  ∑_{a ∈ block} f(a) · ∑_{b ∈ fibre(a)} f(b),

with `block` the dyadic range `(√x, 2√x]` and `fibre(a) = {b : x/a ≤ b ≤ (x + h√x)/a}`.  The fibre
is an interval of length `h√x/a`, which for `a` in the block is between `h/2` and `h`: **the inner
sum is a Möbius sum over a short interval, and the outer variable moves its starting point.**

That is the whole structure of the bilinear all-interval theorem: it is not a statement about one
short interval but about the *average* over `√x` of them, which is why an arbitrarily slowly growing
window length is admissible.

This file is combinatorial: the decomposition is an identity of finite sums, and the fibre length is
a floor-and-ceiling count.
-/

namespace RHTower.Sieve

open Finset

/-- The dyadic block of outer factors. -/
noncomputable def outerBlock (x h : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊).filter
    (fun a => Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x)

/-- The fibre of the balanced pair set above an outer factor. -/
noncomputable def innerFibre (x h : ℝ) (a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊).filter
    (fun b => x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x)

theorem mem_outerBlock {x h : ℝ} {a : ℕ} :
    a ∈ outerBlock x h ↔
      (1 ≤ a ∧ a ≤ ⌊x + h * Real.sqrt x⌋₊)
        ∧ Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x := by
  rw [outerBlock, Finset.mem_filter, Finset.mem_Icc]

theorem mem_innerFibre {x h : ℝ} {a b : ℕ} :
    b ∈ innerFibre x h a ↔
      (1 ≤ b ∧ b ≤ ⌊x + h * Real.sqrt x⌋₊)
        ∧ x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x := by
  rw [innerFibre, Finset.mem_filter, Finset.mem_Icc]

/-- **The fibre decomposition.**  The balanced pair sum is an outer sum over the dyadic block of
inner sums over short intervals. -/
theorem pairSum_eq_sum_fibre (f : ℕ → ℝ) (x h : ℝ) :
    pairSum f x h = ∑ a ∈ outerBlock x h, f a * ∑ b ∈ innerFibre x h a, f b := by
  classical
  have hL : pairSum f x h
      = ∑ a ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
          ∑ b ∈ Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊,
            (if x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x
                ∧ Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x
              then f a * f b else 0) := by
    rw [pairSum, balancedPairs, Finset.sum_filter, Finset.sum_product]
  rw [hL, outerBlock, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro a _
  by_cases hblock : Real.sqrt x ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2 * Real.sqrt x
  · rw [if_pos hblock, innerFibre, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro b _
    by_cases hb : x ≤ ((a * b : ℕ) : ℝ) ∧ ((a * b : ℕ) : ℝ) ≤ x + h * Real.sqrt x
    · rw [if_pos ⟨hb.1, hb.2, hblock.1, hblock.2⟩, if_pos hb]
    · rw [if_neg (fun hc => hb ⟨hc.1, hc.2.1⟩), if_neg hb]
  · rw [if_neg hblock]
    refine Finset.sum_eq_zero ?_
    intro b _
    rw [if_neg]
    intro hc
    exact hblock ⟨hc.2.2.1, hc.2.2.2⟩

/-- **The pair sum is dominated by the fibre sums.**  For a unit-bounded weight the outer factor
can only be discarded. -/
theorem abs_pairSum_le_sum_abs_fibre {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (x h : ℝ) :
    |pairSum f x h| ≤ ∑ a ∈ outerBlock x h, |∑ b ∈ innerFibre x h a, f b| := by
  rw [pairSum_eq_sum_fibre]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum ?_
  intro a _
  rw [abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) (hf a)

/-- The fibre is contained in an interval of integers. -/
theorem innerFibre_subset {x h : ℝ} {a : ℕ} (ha : 1 ≤ a) :
    innerFibre x h a
      ⊆ Finset.Icc ⌈x / (a : ℝ)⌉₊ ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ := by
  intro b hb
  rw [mem_innerFibre] at hb
  obtain ⟨-, hlow, hhigh⟩ := hb
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hcast : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; ring
  rw [hcast] at hlow hhigh
  rw [Finset.mem_Icc]
  constructor
  · refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ ha0]
    linarith [hlow]
  · refine Nat.le_floor ?_
    rw [le_div_iff₀ ha0]
    linarith [hhigh]

/-- **The fibre length.**  The fibre above `a` has at most `h√x/a + 1` elements: for `a` in the
dyadic block that is between `h/2 + 1` and `h + 1`. -/
theorem card_innerFibre_le {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {a : ℕ} (ha : 1 ≤ a) :
    ((innerFibre x h a).card : ℝ) ≤ h * Real.sqrt x / (a : ℝ) + 1 := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hmass : (0 : ℝ) ≤ h * Real.sqrt x / (a : ℝ) := by
    have : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    positivity
  rcases Finset.eq_empty_or_nonempty (innerFibre x h a) with hempty | ⟨b₀, hb₀⟩
  · rw [hempty]
    simpa using by linarith
  · set m : ℕ := ⌈x / (a : ℝ)⌉₊ with hm
    set n : ℕ := ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ with hn
    have hsub := innerFibre_subset (x := x) (h := h) ha
    have hb₀' : b₀ ∈ Finset.Icc m n := hsub hb₀
    rw [Finset.mem_Icc] at hb₀'
    have hmn : m ≤ n := le_trans hb₀'.1 hb₀'.2
    have hcard : (innerFibre x h a).card ≤ n + 1 - m :=
      le_trans (Finset.card_le_card hsub) (le_of_eq (Nat.card_Icc m n))
    have hcast : ((n + 1 - m : ℕ) : ℝ) = (n : ℝ) + 1 - (m : ℝ) := by
      have : m ≤ n + 1 := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hstep : ((innerFibre x h a).card : ℝ) ≤ (n : ℝ) + 1 - (m : ℝ) := by
      rw [← hcast]
      exact_mod_cast hcard
    have hnle : (n : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) := Nat.floor_le (by positivity)
    have hmge : x / (a : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
    have hdiff : (n : ℝ) - (m : ℝ) ≤ h * Real.sqrt x / (a : ℝ) := by
      have : (x + h * Real.sqrt x) / (a : ℝ) - x / (a : ℝ) = h * Real.sqrt x / (a : ℝ) := by
        field_simp
        ring
      linarith
    linarith

end RHTower.Sieve
