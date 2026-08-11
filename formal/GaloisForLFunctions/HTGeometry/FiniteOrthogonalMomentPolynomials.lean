import GaloisForLFunctions.HTGeometry.OrthogonalMomentPolynomials

/-!
# Orthogonal moment polynomials under one finite Hankel hypothesis

The global `PositiveMomentForm` interface is stronger than a finite Hankel-face argument needs.
This module localizes Gram--Schmidt, orthogonality, norm positivity, and the Jacobi recurrence to a
single positive definite `N × N` Hankel block.  All conclusions are explicitly degree-bounded.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-- Positive definiteness of the moment form below one finite degree cutoff. -/
structure PositiveMomentFormBelow (s : ℕ → ℝ) (N : ℕ) : Prop where
  pos_of_ne_zero_of_natDegree_lt :
    ∀ p : Polynomial ℝ, p ≠ 0 → p.natDegree < N → 0 < momentInner s p p

theorem natDegree_monicOrtho_eq (s : ℕ → ℝ) (n : ℕ) :
    (monicOrtho s n).natDegree = n := by
  have hd := monicOrtho_degree s n
  rw [Polynomial.degree_eq_natDegree (monicOrtho_ne_zero s n)] at hd
  exact_mod_cast hd

theorem positiveMomentFormBelow_of_hankelPosDef {s : ℕ → ℝ} {N : ℕ}
    (h : (momentHankelMatrix s N).PosDef) : PositiveMomentFormBelow s N := by
  refine ⟨fun p hp hpdeg => ?_⟩
  let a : Fin N → ℝ := Polynomial.toFn N p
  have hpof : Polynomial.ofFn N a = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hpdeg
  have ha : a ≠ 0 := by
    intro ha
    apply hp
    rw [← hpof, ha, Polynomial.ofFn_zero]
  have hquad := h.dotProduct_mulVec_pos ha
  rw [star_trivial, dotProduct_mulVec_momentHankelMatrix, hpof,
    ← momentInner_self] at hquad
  exact hquad

namespace PositiveMomentFormBelow

variable {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N)
include h

theorem self_pos {p : Polynomial ℝ} (hp : p ≠ 0) (hpdeg : p.natDegree < N) :
    0 < momentInner s p p :=
  PositiveMomentFormBelow.pos_of_ne_zero_of_natDegree_lt h p hp hpdeg

theorem self_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (hpdeg : p.natDegree < N) :
    momentInner s p p ≠ 0 :=
  ne_of_gt (self_pos h hp hpdeg)

end PositiveMomentFormBelow

theorem monicOrtho_inner_lower_below {s : ℕ → ℝ} {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hn : n ≤ N) :
    ∀ m < n, momentInner s (monicOrtho s n) (monicOrtho s m) = 0 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn m hm
    have hmN : m < N := lt_of_lt_of_le hm hn
    have hself : momentInner s (monicOrtho s m) (monicOrtho s m) ≠ 0 :=
      PositiveMomentFormBelow.self_ne_zero h (monicOrtho_ne_zero s m) (by
        rw [natDegree_monicOrtho_eq]
        exact hmN)
    rw [monicOrtho_eq s n, momentInner_sub_left, momentInner_sum_left]
    simp only [momentInner_smul_left]
    rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
    · rw [div_mul_cancel₀ _ hself, sub_self]
    · intro k _ hk
      have hkm : (k : ℕ) ≠ m := fun hEq => hk (Fin.ext hEq)
      have hzero : momentInner s (monicOrtho s k.1) (monicOrtho s m) = 0 := by
        rcases lt_or_gt_of_ne hkm with hlt | hgt
        · rw [momentInner_comm]
          exact ih m hm (le_trans (Nat.le_of_lt hm) hn) k.1 hlt
        · exact ih k.1 k.isLt (le_trans (Nat.le_of_lt k.isLt) hn) m hgt
      rw [hzero, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ (⟨m, hm⟩ : Fin n)) hmem

theorem monicOrtho_inner_eq_zero_below {s : ℕ → ℝ} {N m n : ℕ}
    (h : PositiveMomentFormBelow s N) (hm : m ≤ N) (hn : n ≤ N)
    (hmn : m ≠ n) : momentInner s (monicOrtho s m) (monicOrtho s n) = 0 := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · rw [momentInner_comm]
    exact monicOrtho_inner_lower_below h hn m hlt
  · exact monicOrtho_inner_lower_below h hm n hgt

theorem monicOrtho_inner_eq_zero_of_degree_lt_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N) (hn : n ≤ N)
    {p : Polynomial ℝ} (hp : p.degree < (n : WithBot ℕ)) :
    momentInner s (monicOrtho s n) p = 0 := by
  have hmem := mem_span_monicOrtho (s := s) n p hp
  apply momentInner_eq_zero_of_mem_span (p := p) _ hmem
  intro k hk
  exact monicOrtho_inner_eq_zero_below h hn (le_trans (Nat.le_of_lt hk) hn)
    (by omega)

theorem monicOrtho_inner_self_pos_below {s : ℕ → ℝ} {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hn : n < N) :
    0 < momentInner s (monicOrtho s n) (monicOrtho s n) := by
  apply PositiveMomentFormBelow.self_pos h (monicOrtho_ne_zero s n)
  rwa [natDegree_monicOrtho_eq]

theorem monicOrtho_expansion_below {s : ℕ → ℝ} {N : ℕ}
    (h : PositiveMomentFormBelow s N) {m : ℕ} (hmN : m ≤ N)
    (p : Polynomial ℝ) (hp : p.degree < (m : WithBot ℕ)) :
    p = ∑ k ∈ Finset.range m,
      (momentInner s p (monicOrtho s k) / momentInner s (monicOrtho s k) (monicOrtho s k))
        • monicOrtho s k := by
  set q : Polynomial ℝ := ∑ k ∈ Finset.range m,
    (momentInner s p (monicOrtho s k) / momentInner s (monicOrtho s k) (monicOrtho s k))
      • monicOrtho s k with hq
  have hqdeg : q.degree < (m : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe m)).mpr fun k hk => ?_
    refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _) ?_
    rw [monicOrtho_degree s k]
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk)
  have hproj : ∀ j < m, momentInner s q (monicOrtho s j) =
      momentInner s p (monicOrtho s j) := by
    intro j hj
    rw [hq, momentInner_sum_left, Finset.sum_eq_single j]
    · rw [momentInner_smul_left,
        div_mul_cancel₀ _ (ne_of_gt (monicOrtho_inner_self_pos_below h
          (lt_of_lt_of_le hj hmN)))]
    · intro k hk hkj
      rw [momentInner_smul_left,
        monicOrtho_inner_eq_zero_below h
          (le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hmN)
          (le_trans (Nat.le_of_lt hj) hmN) hkj,
        mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr hj) hnot
  have hrortho : ∀ j < m, momentInner s (p - q) (monicOrtho s j) = 0 := by
    intro j hj
    rw [momentInner_sub_left, hproj j hj, sub_self]
  have hrdeg : (p - q).degree < (m : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hqdeg)
  have hrmem := mem_span_monicOrtho (s := s) m (p - q) hrdeg
  have hrr : momentInner s (p - q) (p - q) = 0 :=
    momentInner_eq_zero_of_mem_span hrortho hrmem
  have hrzero : p - q = 0 := by
    by_contra hrne
    have hrnat : (p - q).natDegree < N := by
      have hrm : (p - q).natDegree < m :=
        (Polynomial.natDegree_lt_iff_degree_lt hrne).mpr hrdeg
      exact lt_of_lt_of_le hrm hmN
    exact (ne_of_gt (PositiveMomentFormBelow.self_pos h hrne hrnat)) hrr
  linear_combination (norm := ring_nf) hrzero

theorem momentInner_monicOrtho_succ_X_mul_below
    {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N) {n : ℕ}
    (hnN : n + 1 ≤ N) :
    momentInner s (monicOrtho s (n + 1)) (Polynomial.X * monicOrtho s n) =
      momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) := by
  have hzero : momentInner s (monicOrtho s (n + 1))
      (Polynomial.X * monicOrtho s n - monicOrtho s (n + 1)) = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt_below h hnN
      (degree_X_mul_monicOrtho_sub_succ_lt s n)
  rw [momentInner_sub_right] at hzero
  linarith

/-- Three-term recurrence localized to one positive finite Hankel block. -/
theorem monicOrtho_three_term_below {s : ℕ → ℝ} {N : ℕ}
    (h : PositiveMomentFormBelow s N) {n : ℕ} (hnN : n + 2 ≤ N) :
    Polynomial.X * monicOrtho s (n + 1) =
      monicOrtho s (n + 2)
        + (momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) • monicOrtho s (n + 1)
        + (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) /
            momentInner s (monicOrtho s n) (monicOrtho s n)) • monicOrtho s n := by
  set p : Polynomial ℝ := Polynomial.X * monicOrtho s (n + 1) - monicOrtho s (n + 2)
    with hpdef
  have hpdeg : p.degree < ((n + 2 : ℕ) : WithBot ℕ) :=
    degree_X_mul_monicOrtho_sub_succ_lt s (n + 1)
  have hexp := monicOrtho_expansion_below h hnN p hpdeg
  have hpk : ∀ k, k < n + 2 → momentInner s p (monicOrtho s k) =
      momentInner s (Polynomial.X * monicOrtho s (n + 1)) (monicOrtho s k) := by
    intro k hk
    rw [hpdef, momentInner_sub_left,
      monicOrtho_inner_eq_zero_below h hnN (le_trans (Nat.le_of_lt hk) hnN) (by omega)]
    ring
  have hsub : ({n, n + 1} : Finset ℕ) ⊆ Finset.range (n + 2) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range]
    omega
  have hvanish : ∀ k ∈ Finset.range (n + 2), k ∉ ({n, n + 1} : Finset ℕ) →
      (momentInner s p (monicOrtho s k) / momentInner s (monicOrtho s k) (monicOrtho s k))
        • monicOrtho s k = 0 := by
    intro k hk hkn
    have hklt : k < n + 2 := Finset.mem_range.mp hk
    have hkne : k ≠ n ∧ k ≠ n + 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkn
      exact hkn
    have hkbelow : k + 1 < n + 1 := by omega
    rw [hpk k hklt, momentInner_X_mul,
      monicOrtho_inner_eq_zero_of_degree_lt_below h
        (by omega : n + 1 ≤ N)]
    · simp
    · have hdeg : (Polynomial.X * monicOrtho s k).degree = ((k + 1 : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_mul, Polynomial.degree_X, monicOrtho_degree s k]
        push_cast
        ring
      rw [hdeg]
      exact WithBot.coe_lt_coe.mpr hkbelow
  rw [← Finset.sum_subset hsub hvanish,
    Finset.sum_pair (by omega : n ≠ n + 1)] at hexp
  rw [hpk n (by omega), hpk (n + 1) (by omega), momentInner_X_mul,
    momentInner_monicOrtho_succ_X_mul_below h (by omega : n + 1 ≤ N)] at hexp
  rw [hpdef] at hexp
  linear_combination (norm := ring_nf) hexp

end HTGeometry
