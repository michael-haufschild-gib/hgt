import Mathlib

/-!
# Jensen's inequality for a monic polynomial against a harmonic majorant

Let `P(z) = Π_{y∈M}(z − y)` and suppose `|P(z)| ≤ B |z − a|^{|M|}` on the circle `|z − c| = R`, with `a`
outside the closed disc. Then

`Π_{y∈M} max(R, |c − y|) ≤ B |c − a|^{|M|}`.

Proof: replace each root `y` inside the disc by the Blaschke-reflected linear factor, which has the
same modulus on the circle and no zero in the disc, divide by `(z − a)^{|M|}`, and apply the maximum
principle at the centre. Compared with `|P(c)| = Π|c − y|`, this bounds the number of roots near `c`;
compared with `1`, it bounds the number of far roots.
-/

open Complex Metric
open scoped ComplexConjugate

namespace FiniteFreeProbability

noncomputable section

/-- The linear factor `z − y`, with `y` reflected in the circle `|z − c| = R` when it lies inside. -/
def blaschkeFactor (c : ℂ) (R : ℝ) (y z : ℂ) : ℂ :=
  if ‖y - c‖ < R then ((R : ℂ) ^ 2 - conj (y - c) * (z - c)) / R else z - y

theorem differentiable_blaschkeFactor (c : ℂ) (R : ℝ) (y : ℂ) :
    Differentiable ℂ (blaschkeFactor c R y) := by
  unfold blaschkeFactor
  split_ifs <;> fun_prop

theorem norm_blaschkeFactor_sphere {c : ℂ} {R : ℝ} (hR : 0 < R) (y : ℂ) {z : ℂ}
    (hz : z ∈ sphere c R) : ‖blaschkeFactor c R y z‖ = ‖z - y‖ := by
  unfold blaschkeFactor
  split_ifs with h
  · have hw : ‖z - c‖ = R := mem_sphere_iff_norm.1 hz
    have hsq : (R : ℂ) ^ 2 = (z - c) * conj (z - c) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
      push_cast
      rfl
    have hfac : (R : ℂ) ^ 2 - conj (y - c) * (z - c) = (z - c) * conj (z - y) := by
      have hc : conj (z - y) = conj (z - c) - conj (y - c) := by
        rw [← map_sub]
        congr 1
        ring
      rw [hsq, hc]
      ring
    rw [hfac, norm_div, norm_mul, Complex.norm_conj, hw, Complex.norm_real, Real.norm_of_nonneg hR.le,
      mul_div_assoc, mul_comm, div_mul_cancel₀ _ hR.ne']
  · rfl

theorem norm_blaschkeFactor_center {c : ℂ} {R : ℝ} (hR : 0 < R) (y : ℂ) :
    ‖blaschkeFactor c R y c‖ = max R ‖c - y‖ := by
  unfold blaschkeFactor
  split_ifs with h
  · have hy : ‖c - y‖ ≤ R := by rw [norm_sub_rev]; exact h.le
    rw [max_eq_left hy, sub_self, mul_zero, sub_zero, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hR.le, pow_two, mul_div_assoc, div_self hR.ne', mul_one]
  · push Not at h
    rw [max_eq_right (by rwa [norm_sub_rev])]

theorem norm_multiset_prod_map (M : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(M.map f).prod‖ = (M.map fun y => ‖f y‖).prod := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih => simp [ih]

theorem differentiable_multiset_prod_blaschke (c : ℂ) (R : ℝ) (M : Multiset ℂ) :
    Differentiable ℂ fun z => (M.map fun y => blaschkeFactor c R y z).prod := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (differentiable_blaschkeFactor c R a).mul ih

/-- **Jensen's inequality against a harmonic majorant.** -/
theorem multiset_prod_max_le {c a : ℂ} {R B : ℝ} (hR : 0 < R) (ha : a ∉ closedBall c R)
    (M : Multiset ℂ)
    (hB : ∀ z ∈ sphere c R, ‖(M.map fun y => z - y).prod‖ ≤ B * ‖z - a‖ ^ Multiset.card M) :
    (M.map fun y => max R ‖c - y‖).prod ≤ B * ‖c - a‖ ^ Multiset.card M := by
  set n := Multiset.card M
  have hne : ∀ z ∈ closedBall c R, z - a ≠ 0 := fun z hz h => ha (by
    rwa [← sub_eq_zero.1 h])
  set Q : ℂ → ℂ := fun z => (M.map fun y => blaschkeFactor c R y z).prod / (z - a) ^ n
  have hQd : DiffContOnCl ℂ Q (ball c R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hR.ne']
    refine DifferentiableOn.div (differentiable_multiset_prod_blaschke c R M).differentiableOn
      (by fun_prop) fun z hz => pow_ne_zero n (hne z hz)
  have hfront : ∀ z ∈ frontier (ball c R), ‖Q z‖ ≤ B := fun z hz => by
    rw [frontier_ball c hR.ne'] at hz
    have hzc : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hpos : 0 < ‖z - a‖ ^ n := pow_pos (norm_pos_iff.2 (hne z hzc)) n
    simp only [Q]
    rw [norm_div, norm_pow, div_le_iff₀ hpos, norm_multiset_prod_map]
    have heq : (M.map fun y => ‖blaschkeFactor c R y z‖) = M.map fun y => ‖z - y‖ :=
      Multiset.map_congr rfl fun y _ => norm_blaschkeFactor_sphere hR y hz
    rw [heq, ← norm_multiset_prod_map]
    exact hB z hz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hQd hfront
    (z := c) (subset_closure (mem_ball_self hR))
  have hcc : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hpos : 0 < ‖c - a‖ ^ n := pow_pos (norm_pos_iff.2 (hne c hcc)) n
  simp only [Q] at hmax
  rw [norm_div, norm_pow, div_le_iff₀ hpos, norm_multiset_prod_map] at hmax
  have heq : (M.map fun y => ‖blaschkeFactor c R y c‖) = M.map fun y => max R ‖c - y‖ :=
    Multiset.map_congr rfl fun y _ => norm_blaschkeFactor_center hR y
  rwa [heq] at hmax

/-- Roots within `r` of the centre gain a factor `R/r`. -/
theorem pow_mul_prod_norm_le (M : Multiset ℂ) (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (R / r) ^ Multiset.card (M.filter fun y => ‖c - y‖ ≤ r) * (M.map fun y => ‖c - y‖).prod ≤
      (M.map fun y => max R ‖c - y‖).prod := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have hA : 0 ≤ (R / r) ^ Multiset.card (M.filter fun y => ‖c - y‖ ≤ r) *
        (M.map fun y => ‖c - y‖).prod := mul_nonneg (by positivity)
      (Multiset.prod_nonneg (by
        intro x hx
        obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
        exact norm_nonneg _))
    simp only [Multiset.map_cons, Multiset.prod_cons]
    by_cases h : ‖c - a‖ ≤ r
    · rw [Multiset.filter_cons_of_pos (p := fun y => ‖c - y‖ ≤ r) M h, Multiset.card_cons, pow_succ]
      have h1 : R / r * ‖c - a‖ ≤ max R ‖c - a‖ := by
        refine le_trans ?_ (le_max_left _ _)
        rw [div_mul_eq_mul_div, div_le_iff₀ hr]
        exact mul_le_mul_of_nonneg_left h hR.le
      calc _ = (R / r * ‖c - a‖) * ((R / r) ^ Multiset.card (M.filter fun y => ‖c - y‖ ≤ r) *
            (M.map fun y => ‖c - y‖).prod) := by ring
        _ ≤ _ := mul_le_mul h1 ih hA (le_trans (norm_nonneg _) (le_max_right _ _))
    · rw [Multiset.filter_cons_of_neg (p := fun y => ‖c - y‖ ≤ r) M h]
      calc _ = ‖c - a‖ * ((R / r) ^ Multiset.card (M.filter fun y => ‖c - y‖ ≤ r) *
            (M.map fun y => ‖c - y‖).prod) := by ring
        _ ≤ _ := mul_le_mul (le_max_right _ _) ih hA (le_trans (norm_nonneg _) (le_max_right _ _))

/-- Roots at distance `≥ T` from the centre contribute a factor `T` each. -/
theorem pow_le_prod_max (M : Multiset ℂ) (c : ℂ) {R T : ℝ} (hR : 1 ≤ R) (hT : 1 ≤ T) :
    T ^ Multiset.card (M.filter fun y => T ≤ ‖c - y‖) ≤ (M.map fun y => max R ‖c - y‖).prod := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have hT0 : 0 ≤ T := by linarith
    have hP : 0 ≤ T ^ Multiset.card (M.filter fun y => T ≤ ‖c - y‖) := by positivity
    have hm : 1 ≤ max R ‖c - a‖ := hR.trans (le_max_left _ _)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    by_cases h : T ≤ ‖c - a‖
    · rw [Multiset.filter_cons_of_pos (p := fun y => T ≤ ‖c - y‖) M h, Multiset.card_cons, pow_succ,
        mul_comm]
      exact mul_le_mul (h.trans (le_max_right _ _)) ih hP (by linarith)
    · rw [Multiset.filter_cons_of_neg (p := fun y => T ≤ ‖c - y‖) M h]
      calc _ = 1 * T ^ Multiset.card (M.filter fun y => T ≤ ‖c - y‖) := (one_mul _).symm
        _ ≤ _ := mul_le_mul hm ih hP (by linarith)

theorem card_filter_le_add (M : Multiset ℂ) {p q s : ℂ → Prop} [DecidablePred p] [DecidablePred q]
    [DecidablePred s] (h : ∀ y ∈ M, p y → q y ∨ s y) :
    Multiset.card (M.filter p) ≤ Multiset.card (M.filter q) + Multiset.card (M.filter s) := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    by_cases hp : p a
    · rw [Multiset.filter_cons_of_pos _ hp, Multiset.card_cons]
      rcases h a (Multiset.mem_cons_self a M) hp with hq | hs
      · rw [Multiset.filter_cons_of_pos _ hq, Multiset.card_cons]
        by_cases hs : s a
        · rw [Multiset.filter_cons_of_pos _ hs, Multiset.card_cons]
          omega
        · rw [Multiset.filter_cons_of_neg _ hs]
          omega
      · rw [Multiset.filter_cons_of_pos _ hs, Multiset.card_cons]
        by_cases hq : q a
        · rw [Multiset.filter_cons_of_pos _ hq, Multiset.card_cons]
          omega
        · rw [Multiset.filter_cons_of_neg _ hq]
          omega
    · rw [Multiset.filter_cons_of_neg _ hp]
      by_cases hq : q a
      · rw [Multiset.filter_cons_of_pos _ hq, Multiset.card_cons]
        by_cases hs : s a
        · rw [Multiset.filter_cons_of_pos _ hs, Multiset.card_cons]
          omega
        · rw [Multiset.filter_cons_of_neg _ hs]
          omega
      · rw [Multiset.filter_cons_of_neg _ hq]
        by_cases hs : s a
        · rw [Multiset.filter_cons_of_pos _ hs, Multiset.card_cons]
          omega
        · rw [Multiset.filter_cons_of_neg _ hs]
          omega

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.multiset_prod_max_le
#print axioms FiniteFreeProbability.pow_mul_prod_norm_le
