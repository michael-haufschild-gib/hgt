import GaloisForLFunctions.HTGeometry.WeightedMinimax.Basic

/-!
# Realizing a finite sign pattern by a polynomial of minimal degree

Given finitely many increasing real nodes `x 0 < ⋯ < x L` and nonzero reals `μ i`, there is a
polynomial `g` whose sign at every node agrees with the sign of `μ i`, whose degree is at most the
number of sign changes of `μ`, and an explicit increasing list of `k+1` indices at which `μ`
alternates in sign, with `k` the degree bound. Both data come out of one induction on `L`, which
also maintains the "terminal ray" property needed for the inductive step.

This is the finite combinatorial core of the weighted alternation theorem: it converts a vanishing
linear functional `∑ μ i • (x i)^•` into a lower bound on the number of sign alternations.
-/

namespace GaloisForLFunctions.HTGeometry.WeightedMinimax

noncomputable section
open Polynomial

theorem pos_mul_of_pos_of_pos_mul {c d G : ℝ} (hA : 0 < c * G) (hB : 0 < d * c) :
    0 < d * G := by
  have hc : c ≠ 0 := by
    intro h
    rw [h] at hA
    simp at hA
  have h2 : 0 < c ^ (2 : ℕ) := by positivity
  nlinarith [mul_pos hB hA]

theorem neg_mul_of_pos_of_neg_mul {c d G : ℝ} (hA : 0 < c * G) (hB : d * c < 0) :
    d * G < 0 := by
  have hc : c ≠ 0 := by
    intro h
    rw [h] at hA
    simp at hA
  have h2 : 0 < c ^ (2 : ℕ) := by positivity
  nlinarith [mul_pos_of_neg_of_neg hB (neg_neg_iff_pos.mpr hA)]

theorem step_mono {x : ℕ → ℝ} {L : ℕ} (hx : ∀ i < L, x i < x (i + 1)) :
    ∀ j ≤ L, ∀ i ≤ j, x i ≤ x j := by
  intro j
  induction j with
  | zero => intro _ i hi; simp only [Nat.le_zero] at hi; rw [hi]
  | succ m ih =>
    intro hm i hi
    rcases Nat.lt_or_ge i (m + 1) with h | h
    · have h1 : x i ≤ x m := ih (by omega) i (by omega)
      exact h1.trans (le_of_lt (hx m (by omega)))
    · have : i = m + 1 := by omega
      rw [this]

theorem step_mono_lt {x : ℕ → ℝ} {L : ℕ} (hx : ∀ i < L, x i < x (i + 1)) {i j : ℕ}
    (hij : i < j) (hj : j ≤ L) : x i < x j := by
  have h1 : x i ≤ x (j - 1) := step_mono hx (j - 1) (by omega) i (by omega)
  have h2 : x (j - 1) < x (j - 1 + 1) := hx (j - 1) (by omega)
  have h3 : j - 1 + 1 = j := by omega
  rw [h3] at h2
  linarith

/-- A nonempty finite set of reals has a monotone enumeration by an initial segment of `ℕ`. -/
theorem exists_monotone_enumeration (X : Finset ℝ) (hX : X.Nonempty) :
    ∃ (xx : ℕ → ℝ) (L : ℕ), (∀ i < L, xx i < xx (i + 1)) ∧ (∀ i ≤ L, xx i ∈ X) ∧
      (∀ y ∈ X, ∃ i ≤ L, xx i = y) ∧ L + 1 = X.card := by
  classical
  have hc : 1 ≤ X.card := Finset.card_pos.mpr hX
  refine ⟨fun i => if h : i < X.card then X.orderEmbOfFin rfl ⟨i, h⟩ else 0, X.card - 1, ?_, ?_,
    ?_, by omega⟩
  · intro i hi
    have h1 : i < X.card := by omega
    have h2 : i + 1 < X.card := by omega
    simp only [dif_pos h1, dif_pos h2]
    exact (X.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega))
  · intro i hi
    have h1 : i < X.card := by omega
    simp only [dif_pos h1]
    exact X.orderEmbOfFin_mem rfl ⟨i, h1⟩
  · intro y hy
    have hr : y ∈ Set.range (X.orderEmbOfFin (rfl : X.card = X.card)) := by
      rw [X.range_orderEmbOfFin rfl]
      exact Finset.mem_coe.mpr hy
    obtain ⟨i, hi⟩ := hr
    refine ⟨i.val, by have := i.isLt; omega, ?_⟩
    simp only [dif_pos i.isLt]
    exact hi

/-- The finite sign-realization lemma. `k` bounds both the degree of the realizing polynomial and
the length (minus one) of an increasing chain of indices along which `μ` strictly alternates. -/
theorem exists_sign_realizing (x μ : ℕ → ℝ) :
    ∀ L : ℕ, (∀ i < L, x i < x (i + 1)) → (∀ i ≤ L, μ i ≠ 0) →
      ∃ (k : ℕ) (g : Polynomial ℝ) (idx : ℕ → ℕ),
        g.natDegree ≤ k ∧
        (∀ i ≤ L, 0 < μ i * g.eval (x i)) ∧
        (∀ y, x L ≤ y → 0 < μ L * g.eval y) ∧
        (∀ j < k, idx j < idx (j + 1)) ∧
        (∀ j ≤ k, idx j ≤ L) ∧
        idx k = L ∧
        (∀ j < k, μ (idx j) * μ (idx (j + 1)) < 0) := by
  intro L
  induction L with
  | zero =>
    intro _ hμ
    refine ⟨0, Polynomial.C (if 0 < μ 0 then 1 else -1), fun _ => 0, by simp, ?_, ?_, ?_, ?_, rfl,
      ?_⟩
    · intro i hi
      simp only [Nat.le_zero] at hi
      subst hi
      rcases lt_or_ge 0 (μ 0) with h | h
      · simp [h]
      · have h0 : μ 0 < 0 := lt_of_le_of_ne h (hμ 0 le_rfl)
        simp only [Polynomial.eval_C, if_neg (not_lt.mpr h)]
        nlinarith
    · intro y _
      rcases lt_or_ge 0 (μ 0) with h | h
      · simp [h]
      · have h0 : μ 0 < 0 := lt_of_le_of_ne h (hμ 0 le_rfl)
        simp only [Polynomial.eval_C, if_neg (not_lt.mpr h)]
        nlinarith
    · intro j hj; omega
    · intro j _; exact Nat.le_refl 0
    · intro j hj; omega
  | succ L ih =>
    intro hx hμ
    obtain ⟨k, g, idx, hdeg, hnodes, hray, hmono, hle, hidxk, halt⟩ :=
      ih (fun i hi => hx i (by omega)) (fun i hi => hμ i (by omega))
    have hxL : x L < x (L + 1) := hx L (by omega)
    have hμL : μ L ≠ 0 := hμ L (by omega)
    have hμL1 : μ (L + 1) ≠ 0 := hμ (L + 1) le_rfl
    have hprod : μ (L + 1) * μ L ≠ 0 := mul_ne_zero hμL1 hμL
    rcases lt_or_gt_of_ne hprod with hneg | hpos
    · -- sign change: multiply by a linear factor with its root between `x L` and `x (L+1)`
      refine ⟨k + 1, g * (Polynomial.C ((x L + x (L + 1)) / 2) - Polynomial.X),
        fun j => if j = k + 1 then L + 1 else idx j, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 : (Polynomial.C ((x L + x (L + 1)) / 2) - Polynomial.X).natDegree ≤ 1 := by
          refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
          simp
        omega
      · intro i hi
        rcases Nat.lt_or_ge i (L + 1) with h | h
        · have hxi : x i ≤ x L := step_mono (fun j hj => hx j (by omega)) L le_rfl i (by omega)
          have hpos1 : 0 < (x L + x (L + 1)) / 2 - x i := by linarith
          have := hnodes i (by omega)
          simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
            Polynomial.eval_X]
          nlinarith
        · have hiL : i = L + 1 := by omega
          subst hiL
          have hneg1 : (x L + x (L + 1)) / 2 - x (L + 1) < 0 := by linarith
          have h2 := hray (x (L + 1)) (le_of_lt hxL)
          have h3 : μ (L + 1) * g.eval (x (L + 1)) < 0 :=
            neg_mul_of_pos_of_neg_mul h2 hneg
          simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
            Polynomial.eval_X]
          nlinarith
      · intro y hy
        have hneg1 : (x L + x (L + 1)) / 2 - y < 0 := by linarith
        have h2 := hray y (le_of_lt (lt_of_lt_of_le hxL hy))
        have h3 : μ (L + 1) * g.eval y < 0 := neg_mul_of_pos_of_neg_mul h2 hneg
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
          Polynomial.eval_X]
        nlinarith
      · intro j hj
        rcases Nat.lt_or_ge j k with h | h
        · simp only [if_neg (by omega : j ≠ k + 1), if_neg (by omega : j + 1 ≠ k + 1)]
          exact hmono j h
        · have hjk : j = k := by omega
          have h1 : (if j = k + 1 then L + 1 else idx j) = L := by
            rw [if_neg (by omega : ¬ (j = k + 1)), hjk, hidxk]
          have h2 : (if j + 1 = k + 1 then L + 1 else idx (j + 1)) = L + 1 := by
            rw [if_pos (by omega : j + 1 = k + 1)]
          simp only [h1, h2]
          omega
      · intro j hjk
        by_cases h : j = k + 1
        · simp [h]
        · simp only [if_neg h]
          have := hle j (by omega)
          omega
      · intro j hj
        rcases Nat.lt_or_ge j k with h | h
        · simp only [if_neg (by omega : j ≠ k + 1), if_neg (by omega : j + 1 ≠ k + 1)]
          exact halt j h
        · have hjk : j = k := by omega
          have h1 : (if j = k + 1 then L + 1 else idx j) = L := by
            rw [if_neg (by omega : ¬ (j = k + 1)), hjk, hidxk]
          have h2 : (if j + 1 = k + 1 then L + 1 else idx (j + 1)) = L + 1 := by
            rw [if_pos (by omega : j + 1 = k + 1)]
          simp only [h1, h2]
          rw [mul_comm]
          exact hneg
    · -- no sign change: keep the polynomial and move the last index
      refine ⟨k, g, fun j => if j = k then L + 1 else idx j, hdeg, ?_, ?_, ?_, ?_, by simp, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge i (L + 1) with h | h
        · exact hnodes i (by omega)
        · have hiL : i = L + 1 := by omega
          subst hiL
          exact pos_mul_of_pos_of_pos_mul (hray (x (L + 1)) (le_of_lt hxL)) hpos
      · intro y hy
        exact pos_mul_of_pos_of_pos_mul (hray y (le_of_lt (lt_of_lt_of_le hxL hy))) hpos
      · intro j hj
        simp only [if_neg (by omega : j ≠ k)]
        by_cases h : j + 1 = k
        · simp only [if_pos h]
          have := hle j (by omega)
          omega
        · simp only [if_neg h]
          exact hmono j hj
      · intro j _
        by_cases h : j = k
        · simp [h]
        · simp only [if_neg h]
          have := hle j (by omega)
          omega
      · intro j hj
        simp only [if_neg (by omega : j ≠ k)]
        by_cases h : j + 1 = k
        · simp only [if_pos h]
          have h1 := halt j hj
          rw [show idx (j + 1) = L from by rw [h, hidxk]] at h1
          exact neg_mul_of_pos_of_neg_mul (by rw [mul_comm]; exact hpos) h1
        · simp only [if_neg h]
          exact halt j hj

end
end GaloisForLFunctions.HTGeometry.WeightedMinimax
