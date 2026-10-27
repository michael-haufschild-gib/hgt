import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Quadratic ascent reaches a local maximum

If each upward step pays its squared horizontal displacement from the gain
in squared depth, a sufficiently sparse finite window contains a point with
no further upward step. The window bound and the depth bound are independent.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

private theorem sum_successive_sub (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, (f (j + 1) - f j) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih]
      ring

private theorem sq_sum_le_card_mul_sum_sq (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range n, f j) ^ 2 ≤ (n : ℝ) * ∑ j ∈ range n, f j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun _ => (1 : ℝ)) f
  simpa only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] using h

/-- Squared displacement is paid by the total gain in squared depth. -/
theorem displacement_sq_le_of_quadratic_steps (d t : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ j < n, (t (j + 1) - t j) ^ 2 ≤ d (j + 1) ^ 2 - d j ^ 2) :
    (t n - t 0) ^ 2 ≤ (n : ℝ) * (d n ^ 2 - d 0 ^ 2) := by
  have hcost : ∑ j ∈ range n, (t (j + 1) - t j) ^ 2 ≤
      ∑ j ∈ range n, (d (j + 1) ^ 2 - d j ^ 2) := by
    exact sum_le_sum fun j hj => hstep j (mem_range.mp hj)
  rw [sum_successive_sub (fun j => d j ^ 2)] at hcost
  have hcs := sq_sum_le_card_mul_sum_sq (fun j => t (j + 1) - t j) n
  rw [sum_successive_sub t] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg n))

private theorem ascent_path_inside (d t : ℕ → ℝ) (N : ℕ) {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R)
    (hdepth : ∀ n, 0 ≤ d n ∧ d n ≤ B)
    (hstep : ∀ n < N, |t n - t 0| ≤ R → d 0 ≤ d n →
      d n ^ 2 + (t (n + 1) - t n) ^ 2 < d (n + 1) ^ 2)
    (hsize : (N : ℝ) * B ^ 2 < R ^ 2) :
    ∀ n ≤ N,
      (∀ j < n, d j ^ 2 + (t (j + 1) - t j) ^ 2 < d (j + 1) ^ 2) ∧
      d 0 ≤ d n ∧ |t n - t 0| ≤ R := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨?_, le_rfl, ?_⟩
      · intro j hj
        omega
      · simpa only [sub_self, abs_zero] using hR.le
  | succ n ih =>
      intro hnN
      obtain ⟨hprev, hdeep, hnear⟩ := ih (by omega)
      have hlast := hstep n (by omega) hnear hdeep
      have hsteps : ∀ j < n + 1,
          d j ^ 2 + (t (j + 1) - t j) ^ 2 < d (j + 1) ^ 2 := by
        intro j hj
        by_cases h : j = n
        · simpa only [h] using hlast
        · exact hprev j (by omega)
      have hdeep' : d 0 ≤ d (n + 1) := by
        have ha := (hdepth n).1
        have hb := (hdepth (n + 1)).1
        have hinc : d n < d (n + 1) := by
          nlinarith [sq_nonneg (t (n + 1) - t n)]
        exact hdeep.trans hinc.le
      have hcost : (t (n + 1) - t 0) ^ 2 ≤
          ((n + 1 : ℕ) : ℝ) * (d (n + 1) ^ 2 - d 0 ^ 2) := by
        apply displacement_sq_le_of_quadratic_steps
        intro j hj
        linarith [hsteps j hj]
      have hdB : d (n + 1) ^ 2 - d 0 ^ 2 ≤ B ^ 2 := by
        obtain ⟨ha, hb⟩ := hdepth (n + 1)
        nlinarith [sq_nonneg (d 0)]
      have hncast : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hnN
      have hcostB : (t (n + 1) - t 0) ^ 2 < R ^ 2 := by
        calc
          (t (n + 1) - t 0) ^ 2 ≤
              ((n + 1 : ℕ) : ℝ) * (d (n + 1) ^ 2 - d 0 ^ 2) := hcost
          _ ≤ ((n + 1 : ℕ) : ℝ) * B ^ 2 :=
            mul_le_mul_of_nonneg_left hdB (Nat.cast_nonneg _)
          _ ≤ (N : ℝ) * B ^ 2 :=
            mul_le_mul_of_nonneg_right hncast (sq_nonneg B)
          _ < R ^ 2 := hsize
      have hnear' : |t (n + 1) - t 0| ≤ R := by
        have habs := abs_nonneg (t (n + 1) - t 0)
        have hsq := sq_abs (t (n + 1) - t 0)
        nlinarith
      exact ⟨hsteps, hdeep', hnear'⟩

/-- A finite window whose cardinality is below the quadratic escape cost contains
a point that cannot ascend, and its depth is at least the starting depth. -/
theorem exists_quadratic_ascent_terminal {α : Type*} (depth height : α → ℝ)
    (q : α) (F : Finset α) {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R)
    (hdepth : ∀ x, 0 ≤ depth x ∧ depth x ≤ B)
    (hwindow : ∀ x, |height x - height q| ≤ R → x ∈ F)
    (hcard : (F.card : ℝ) * B ^ 2 < R ^ 2) :
    ∃ x, |height x - height q| ≤ R ∧ depth q ≤ depth x ∧
      ∀ y, depth y ^ 2 ≤ depth x ^ 2 + (height y - height x) ^ 2 := by
  classical
  by_contra hn
  have hexists : ∀ x, |height x - height q| ≤ R → depth q ≤ depth x →
      ∃ y, depth x ^ 2 + (height y - height x) ^ 2 < depth y ^ 2 := by
    intro x hx hd
    by_contra hy
    apply hn
    refine ⟨x, hx, hd, ?_⟩
    intro y
    exact le_of_not_gt (fun h => hy ⟨y, h⟩)
  have hchoice : ∀ x, ∃ y,
      (∃ z, depth x ^ 2 + (height z - height x) ^ 2 < depth z ^ 2) →
      depth x ^ 2 + (height y - height x) ^ 2 < depth y ^ 2 := by
    intro x
    by_cases h : ∃ z, depth x ^ 2 + (height z - height x) ^ 2 < depth z ^ 2
    · exact ⟨Classical.choose h, fun _ => Classical.choose_spec h⟩
    · exact ⟨x, fun hz => (h hz).elim⟩
  choose next hnext using hchoice
  let z : ℕ → α := fun n => Nat.rec q (fun _ x => next x) n
  have hz0 : z 0 = q := rfl
  have hzsucc (n : ℕ) : z (n + 1) = next (z n) := rfl
  let N : ℕ := F.card
  have hstep : ∀ n < N, |height (z n) - height (z 0)| ≤ R →
      depth (z 0) ≤ depth (z n) →
      depth (z n) ^ 2 + (height (z (n + 1)) - height (z n)) ^ 2 <
        depth (z (n + 1)) ^ 2 := by
    intro n _ hnear hdeep
    rw [hz0] at hnear hdeep
    rw [hzsucc]
    exact hnext (z n) (hexists (z n) hnear hdeep)
  have hpath := ascent_path_inside (fun n => depth (z n)) (fun n => height (z n)) N
    hB hR (fun n => hdepth (z n)) hstep hcard
  have hstep_strict : ∀ n < N, depth (z n) < depth (z (n + 1)) := by
    intro n hnN
    have h := (hpath (n + 1) (by omega)).1 n (by omega)
    have ha := (hdepth (z n)).1
    have hb := (hdepth (z (n + 1))).1
    nlinarith [sq_nonneg (height (z (n + 1)) - height (z n))]
  have hmono : ∀ i j, i < j → j ≤ N → depth (z i) < depth (z j) := by
    intro i j hij hjN
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases h : i = j
        · subst i
          exact hstep_strict j (by omega)
        · exact lt_trans (ih (by omega) (by omega)) (hstep_strict j (by omega))
  let v : Fin (N + 1) → {x // x ∈ F} := fun i =>
    ⟨z i, hwindow (z i) (by simpa only [hz0] using (hpath i (by omega)).2.2)⟩
  have hv : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have hz : z i = z j := congrArg Subtype.val hij
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := hmono i j hlt (by omega)
      rw [hz] at h
      exact lt_irrefl _ h
    · have h := hmono j i hgt (by omega)
      rw [hz] at h
      exact lt_irrefl _ h
  have hc := Fintype.card_le_of_injective v hv
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  dsimp only [N] at hc
  omega

end GaloisForLFunctions.HTGeometry
