import GaloisForLFunctions.RHTower.XiGaussianHeatHankelRootFlip
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLargeTimeDetection

/-!
# Real-node witnesses for the heat Hankel form

Write `P = Q · (X − r)` for a root `r` of `P` and put `Q₁ = Q · (X − Re r)`.  The identity
`(X − r)(X − r̄) = (X − Re r)² + (Im r)²` splits the Hermitian square,
`P P^* = Q₁ Q₁^* + (Im r)² Q Q^*`, so with no hypothesis on the zeros

`Re H_a(P, P) = Re H_a(Q₁, Q₁) + (Im r)² Re H_a(Q, Q)`   (`re_heatHankel_split`).

Both `Q₁` and `Q` have one non-real root fewer than `P` and degree at most `deg P`.  So if the
left side is negative, one of the two is negative, and induction on the number of non-real roots
gives:

**Theorem** (`exists_realNodes_heatHankel_re_neg`).  If `Re H_a(P, P) < 0` for some `a > 0`, then
there are real nodes `x₁, …, x_m` with `m ≤ deg P` such that, for `p = ∏ (X − x_i)`,
`Re H_a(p, p) = Re Σ_q e^{-a w_q} ∏_i (w_q − x_i)² < 0`.

Hence the heat Hankel form is nonnegative iff it is nonnegative on squares of real-rooted
polynomials, and
`RH ⟺ Re Σ_q e^{-a w_q} ∏_i (w_q − x_i)² ≥ 0 for every finite family of real nodes`
(`riemannHypothesis_iff_realNodes_heatHankel_nonneg`).  Without RH a witness with a bounded number
of real nodes exists at every large heat time
(`exists_realNodes_heatHankel_re_neg_of_not_riemannHypothesis`).
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry (conjPoly)

namespace RHTower

noncomputable section

/-! ## Splitting the Hermitian square at a root -/

/-- Termwise splitting `e^{-aw} |P|² = e^{-aw} |Q₁|² + (Im r)² e^{-aw} |Q|²` for `P = Q (X − r)`. -/
theorem heatHankelTermAt_split (a : ℝ) (Q : ℂ[X]) (r w : ℂ) :
    heatHankelTermAt a (Q * (X - C r)) (Q * (X - C r)) w =
      heatHankelTermAt a (Q * (X - C (r.re : ℂ))) (Q * (X - C (r.re : ℂ))) w +
        ((r.im ^ 2 : ℝ) : ℂ) * heatHankelTermAt a Q Q w := by
  have key : (w - r) * (w - (starRingEnd ℂ) r) = (w - (r.re : ℂ)) ^ 2 + (r.im : ℂ) ^ 2 := by
    have h1 := Complex.add_conj r
    have h2 := Complex.mul_conj r
    rw [Complex.normSq_apply] at h2
    push_cast at h1 h2
    linear_combination (-w) * h1 + h2
  simp only [heatHankelTermAt, eval_mul, eval_sub, eval_X, eval_C, map_mul, map_sub,
    Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  linear_combination
    Complex.exp (-(a : ℂ) * w) * Q.eval w * (starRingEnd ℂ) (Q.eval ((starRingEnd ℂ) w)) * key

/-- **Splitting at a root.**  `H_a(Q (X − r)) = H_a(Q (X − Re r)) + (Im r)² H_a(Q)`. -/
theorem heatHankel_split {a : ℝ} (ha : 0 < a) (Q : ℂ[X]) (r : ℂ) :
    heatHankel a (Q * (X - C r)) (Q * (X - C r)) =
      heatHankel a (Q * (X - C (r.re : ℂ))) (Q * (X - C (r.re : ℂ))) +
        ((r.im ^ 2 : ℝ) : ℂ) * heatHankel a Q Q := by
  unfold heatHankel
  rw [← tsum_mul_left, ← (summable_heatHankelTermAt ha _ _).tsum_add
    ((summable_heatHankelTermAt ha Q Q).mul_left _)]
  exact tsum_congr fun q => heatHankelTermAt_split a Q r _

theorem re_heatHankel_split {a : ℝ} (ha : 0 < a) (Q : ℂ[X]) (r : ℂ) :
    (heatHankel a (Q * (X - C r)) (Q * (X - C r))).re =
      (heatHankel a (Q * (X - C (r.re : ℂ))) (Q * (X - C (r.re : ℂ)))).re +
        r.im ^ 2 * (heatHankel a Q Q).re := by
  rw [heatHankel_split ha, add_re, re_ofReal_mul]

/-- Scaling: `H_a(cP, cP) = |c|² H_a(P, P)`. -/
theorem heatHankel_C_mul (a : ℝ) (c : ℂ) (P : ℂ[X]) :
    heatHankel a (C c * P) (C c * P) = (Complex.normSq c : ℂ) * heatHankel a P P := by
  unfold heatHankel
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  simp only [heatHankelTermAt, eval_mul, eval_C, map_mul]
  rw [← Complex.mul_conj]
  ring

/-! ## Induction on the number of non-real roots -/

theorem exists_realRooted_heatHankel_re_neg_aux {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∀ P : ℂ[X], Multiset.countP (fun z : ℂ => z.im ≠ 0) P.roots = n →
      (heatHankel a P P).re < 0 →
      ∃ p : ℂ[X], p ≠ 0 ∧ p.natDegree ≤ P.natDegree ∧ (∀ z ∈ p.roots, z.im = 0) ∧
        (heatHankel a p p).re < 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hneg
  have hP : P ≠ 0 := by
    rintro rfl
    simp [heatHankel, heatHankelTermAt] at hneg
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    exact ⟨P, hP, le_rfl, fun z hz => not_not.1 (Multiset.countP_eq_zero.1 hn z hz), hneg⟩
  obtain ⟨r, hrP, hrim⟩ := Multiset.countP_pos.1 (hn ▸ h0)
  have hr : P.IsRoot r := (mem_roots hP).1 hrP
  have hPQ := eq_mul_divByMonic_of_isRoot hr
  have hQ := divByMonic_ne_zero_of_isRoot hP hr
  set Q := P /ₘ (X - C r)
  have hQ₁ : Q * (X - C (r.re : ℂ)) ≠ 0 := mul_ne_zero hQ (X_sub_C_ne_zero _)
  have hcountQ : Multiset.countP (fun z : ℂ => z.im ≠ 0) Q.roots = n - 1 := by
    have h := hn
    rw [hPQ, roots_mul (hPQ ▸ hP), roots_X_sub_C, Multiset.countP_add,
      ← Multiset.cons_zero, Multiset.countP_cons_of_pos (p := fun z : ℂ => z.im ≠ 0) _ hrim, Multiset.countP_zero] at h
    omega
  have hcountQ₁ :
      Multiset.countP (fun z : ℂ => z.im ≠ 0) (Q * (X - C (r.re : ℂ))).roots = n - 1 := by
    rw [roots_mul hQ₁, roots_X_sub_C, Multiset.countP_add, ← Multiset.cons_zero,
      Multiset.countP_cons_of_neg (p := fun z : ℂ => z.im ≠ 0) _ (by simp), Multiset.countP_zero, add_zero, hcountQ]
  have hdegQ : Q.natDegree + 1 = P.natDegree := by
    conv_rhs => rw [hPQ, natDegree_mul hQ (X_sub_C_ne_zero _), natDegree_X_sub_C]
  have hdegQ₁ : (Q * (X - C (r.re : ℂ))).natDegree = P.natDegree := by
    rw [natDegree_mul hQ (X_sub_C_ne_zero _), natDegree_X_sub_C, hdegQ]
  have hsplit := re_heatHankel_split ha Q r
  rw [← hPQ] at hsplit
  have hlt : n - 1 < n := by omega
  by_cases h₁ : (heatHankel a (Q * (X - C (r.re : ℂ))) (Q * (X - C (r.re : ℂ)))).re < 0
  · obtain ⟨p, hp0, hpdeg, hpr, hpneg⟩ := ih (n - 1) hlt _ hcountQ₁ h₁
    exact ⟨p, hp0, hpdeg.trans hdegQ₁.le, hpr, hpneg⟩
  · have h₂ : (heatHankel a Q Q).re < 0 := by
      by_contra h₂
      nlinarith [mul_nonneg (sq_nonneg r.im) (not_lt.1 h₂), not_lt.1 h₁]
    obtain ⟨p, hp0, hpdeg, hpr, hpneg⟩ := ih (n - 1) hlt Q hcountQ h₂
    exact ⟨p, hp0, by omega, hpr, hpneg⟩

/-- **Real-rooted witnesses.**  A negative direction of the heat Hankel form is witnessed by a
nonzero polynomial with only real roots and no larger degree. -/
theorem exists_realRooted_heatHankel_re_neg {a : ℝ} (ha : 0 < a) {P : ℂ[X]}
    (h : (heatHankel a P P).re < 0) :
    ∃ p : ℂ[X], p ≠ 0 ∧ p.natDegree ≤ P.natDegree ∧ (∀ z ∈ p.roots, z.im = 0) ∧
      (heatHankel a p p).re < 0 :=
  exists_realRooted_heatHankel_re_neg_aux ha _ P rfl h

/-! ## Real nodes -/

/-- The monic polynomial `∏ (X − x_i)` with real nodes `x_i`. -/
def realNodePoly (s : Multiset ℝ) : ℂ[X] := (s.map fun x : ℝ => X - C (x : ℂ)).prod

theorem conjPoly_realNodePoly (s : Multiset ℝ) : conjPoly (realNodePoly s) = realNodePoly s := by
  simp [conjPoly, realNodePoly, Polynomial.map_multiset_prod, Multiset.map_map]

/-- For real nodes the heat Hankel form is the heat trace weighted by `∏ (w − x_i)²`. -/
theorem heatHankel_realNodePoly (a : ℝ) (s : Multiset ℝ) :
    heatHankel a (realNodePoly s) (realNodePoly s) =
      ∑' q : XiZeroCopy, Complex.exp (-(a : ℂ) * xiHeatFrequency q) *
        ((realNodePoly s).eval (xiHeatFrequency q)) ^ 2 := by
  refine tsum_congr fun q => ?_
  rw [heatHankelTermAt_eq_eval_mul_conjPoly, conjPoly_realNodePoly, eval_mul, sq]

/-- **Real-node witnesses.**  If `Re H_a(P, P) < 0`, there are at most `deg P` real nodes `x_i`
with `Re Σ_q e^{-a w_q} ∏ (w_q − x_i)² < 0`. -/
theorem exists_realNodes_heatHankel_re_neg {a : ℝ} (ha : 0 < a) {P : ℂ[X]}
    (h : (heatHankel a P P).re < 0) :
    ∃ s : Multiset ℝ, Multiset.card s ≤ P.natDegree ∧
      (heatHankel a (realNodePoly s) (realNodePoly s)).re < 0 := by
  obtain ⟨p, -, hpdeg, hpr, hpneg⟩ := exists_realRooted_heatHankel_re_neg ha h
  refine ⟨p.roots.map Complex.re, ?_, ?_⟩
  · rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree]
    exact hpdeg
  have hmap : realNodePoly (p.roots.map Complex.re) = (p.roots.map fun z => X - C z).prod := by
    rw [realNodePoly, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun z hz => ?_)
    simp only [Function.comp_apply]
    congr 2
    exact Complex.ext (by simp) (by simp [hpr z hz])
  have hp := (C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := p))).symm
  rw [hmap]
  rw [hp, heatHankel_C_mul, re_ofReal_mul] at hpneg
  exact neg_of_mul_neg_right hpneg (Complex.normSq_nonneg _)

/-! ## RH in real-node form -/

/-- **RH in real-node form.**  For `a > 0`, RH holds iff
`Re Σ_q e^{-a w_q} ∏_i (w_q − x_i)² ≥ 0` for every finite family of real nodes. -/
theorem riemannHypothesis_iff_realNodes_heatHankel_nonneg {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔
      ∀ s : Multiset ℝ, 0 ≤ (heatHankel a (realNodePoly s) (realNodePoly s)).re := by
  rw [riemannHypothesis_iff_heatHankel_nonneg ha]
  refine ⟨fun h s => h _, fun h P => not_lt.1 fun hP => ?_⟩
  obtain ⟨s, -, hs⟩ := exists_realNodes_heatHankel_re_neg ha hP
  exact (h s).not_gt hs

/-- **Large-time real-node witnesses.**  Without RH there are `N` and `A > 0` such that for every
`a ≥ A` some family of fewer than `N` real nodes has
`Re Σ_q e^{-a w_q} ∏ (w_q − x_i)² < 0`. -/
theorem exists_realNodes_heatHankel_re_neg_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ N : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ s : Multiset ℝ, Multiset.card s < N ∧
        (heatHankel a (realNodePoly s) (realNodePoly s)).re < 0 := by
  obtain ⟨N, A, hA, h⟩ := exists_heatHankel_re_neg_of_not_riemannHypothesis hRH
  refine ⟨N, A, hA, fun a haA => ?_⟩
  obtain ⟨P, -, hPdeg, hP⟩ := h a haA
  obtain ⟨s, hs, hneg⟩ := exists_realNodes_heatHankel_re_neg (hA.trans_le haA) hP
  exact ⟨s, hs.trans_lt hPdeg, hneg⟩

end

end RHTower
