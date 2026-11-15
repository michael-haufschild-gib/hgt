import GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Finite-divisor rigidity for tropical shift equations

A finite spline is affine beyond its last knot. The centered second-order
recurrence propagates two consecutive values backwards, so an affine tail
determines the whole solution. Nonzero solutions have coefficient `2`
and are globally affine. Thus non-affine solutions in Cao–Korhonen–Wang,
Lemma 5.2, require infinitely many slope changes or discontinuities.
-/

namespace GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
open scoped BigOperators
noncomputable section

private theorem recurrence_tail_zero (f : ℝ → ℝ) (c R : ℝ)
    (hrec : ∀ x, f (x + 1) + f (x - 1) = c * f x)
    (htail : ∀ x, R ≤ x → f x = 0) : f = 0 := by
  have hstep (n : ℕ) (x : ℝ) (hx : R ≤ x + n) : f x = 0 ∧ f (x + 1) = 0 := by
    induction n generalizing x with
    | zero =>
        have hx' : R ≤ x := by simpa only [Nat.cast_zero, add_zero] using hx
        exact ⟨htail x hx', htail (x + 1) (by linarith only [hx'])⟩
    | succ n ih =>
        have hx' : R ≤ (x + 1) + n := by
          push_cast at hx
          linarith only [hx]
        obtain ⟨h1, h2⟩ := ih (x + 1) hx'
        refine ⟨?_, h1⟩
        have h := hrec (x + 1)
        simpa only [h1, h2, add_sub_cancel_right, mul_zero, zero_add] using h
  funext x
  obtain ⟨n, hn⟩ := exists_nat_gt (R - x)
  exact (hstep n x (by linarith only [hn])).1

/-- An affine tail of a centered shift solution extends across the whole real line. -/
theorem recurrence_affine_tail (f : ℝ → ℝ) (c A B R : ℝ)
    (hrec : ∀ x, f (x + 1) + f (x - 1) = c * f x)
    (htail : ∀ x, R ≤ x → f x = A * x + B) :
    f = 0 ∨ c = 2 ∧ f = fun x => A * x + B := by
  by_cases hc : c = 2
  · right
    refine ⟨hc, ?_⟩
    have hz : (fun x => f x - (A * x + B)) = 0 := by
      apply recurrence_tail_zero _ 2 R
      · intro x
        have h := hrec x
        rw [hc] at h
        linear_combination h
      · intro x hx
        rw [htail x hx, sub_self]
    funext x
    exact sub_eq_zero.mp (congrFun hz x)
  · left
    have h1 := hrec (R + 1)
    have h2 := hrec (R + 2)
    rw [htail ((R + 1) + 1) (by linarith only),
      htail ((R + 1) - 1) (by linarith only), htail (R + 1) (by linarith only)] at h1
    rw [htail ((R + 2) + 1) (by linarith only),
      htail ((R + 2) - 1) (by linarith only), htail (R + 2) (by linarith only)] at h2
    have hA : (c - 2) * A = 0 := by linear_combination h1 - h2
    have ha : A = 0 := (mul_eq_zero.mp hA).resolve_left (sub_ne_zero.mpr hc)
    have hB : (c - 2) * B = 0 := by
      rw [ha] at h1
      linear_combination -h1
    have hb : B = 0 := (mul_eq_zero.mp hB).resolve_left (sub_ne_zero.mpr hc)
    apply recurrence_tail_zero f c R hrec
    intro x hx
    simpa only [ha, hb, zero_mul, add_zero] using htail x hx

/-- Beyond the finite knot set, the spline has its total slope and first-moment intercept. -/
theorem spline_right_tail (s : Finset ℝ) (w : ℝ → ℝ) (a b x : ℝ)
    (hx : (∑ t ∈ s, |t|) ≤ x) :
    spline s w a b x = (a + ∑ t ∈ s, w t) * x + (b - ∑ t ∈ s, w t * t) := by
  have hsum : (∑ t ∈ s, w t * |x - t|) =
      (∑ t ∈ s, w t) * x - ∑ t ∈ s, w t * t := by
    calc
      _ = ∑ t ∈ s, w t * (x - t) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : t ≤ x := (le_abs_self t).trans
          ((Finset.single_le_sum (fun u _ => abs_nonneg u) ht).trans hx)
        rw [abs_of_nonneg (sub_nonneg.mpr ht')]
      _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [spline, hsum]
  ring

/-- A finite tropical spline solves the centered shift equation exactly when it is zero,
or is affine with recurrence coefficient two. -/
theorem spline_centered_shift_iff (s : Finset ℝ) (w : ℝ → ℝ) (a b c : ℝ) :
    (∀ x, spline s w a b (x + 1) + spline s w a b (x - 1) = c * spline s w a b x) ↔
      spline s w a b = 0 ∨ c = 2 ∧ ∃ A B : ℝ, spline s w a b = fun x => A * x + B := by
  constructor
  · intro hrec
    rcases recurrence_affine_tail (spline s w a b) c
      (a + ∑ t ∈ s, w t) (b - ∑ t ∈ s, w t * t) (∑ t ∈ s, |t|) hrec
      (fun x hx => spline_right_tail s w a b x hx) with h | ⟨hc, hf⟩
    · exact Or.inl h
    · exact Or.inr ⟨hc, _, _, hf⟩
  · rintro (hf | ⟨rfl, A, B, hf⟩) <;> intro x <;> rw [hf]
    · simp
    · dsimp only
      ring

/-- A nonzero compact tent cannot satisfy any constant-coefficient centered shift equation. -/
theorem tent_centered_shift_iff (a : ℝ) :
    (∃ c : ℝ, ∀ x, tentCount a (x + 1) + tentCount a (x - 1) = c * tentCount a x) ↔
      a = 0 := by
  constructor
  · rintro ⟨c, hrec⟩
    have hz : tentCount a = 0 := by
      apply recurrence_tail_zero (tentCount a) c |a| hrec
      intro x hx
      have hx0 : 0 ≤ x := (abs_nonneg a).trans hx
      simp only [tentCount, abs_of_nonneg hx0, max_eq_left (sub_nonpos.mpr hx)]
    have h0 := congrFun hz 0
    have ha : |a| = 0 := by
      simpa only [tentCount, abs_zero, sub_zero,
        max_eq_right (abs_nonneg a), Pi.zero_apply] using h0
    exact abs_eq_zero.mp ha
  · rintro rfl
    refine ⟨0, fun x => ?_⟩
    have ht (y : ℝ) : tentCount 0 y = 0 := by
      simp only [tentCount, abs_zero, zero_sub, max_eq_left (neg_nonpos.mpr (abs_nonneg y))]
    rw [ht, ht, ht]
    ring

#print axioms tent_centered_shift_iff

#print axioms recurrence_affine_tail
#print axioms spline_right_tail
#print axioms spline_centered_shift_iff

end
end GaloisForLFunctions.BiScaleUncertainty.TropicalJensen
