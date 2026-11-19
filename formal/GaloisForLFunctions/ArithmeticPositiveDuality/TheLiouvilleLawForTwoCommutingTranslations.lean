import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Liouville rigidity for a two-point translation law

For the two-point walk on an abelian group the relative Liouville mechanism
of Wendt and Yamashita (arXiv:2611.24299) has a direct variance proof. Every
step contributes at least the square of the current directional contrast
of a harmonic function. The lower bound uses only its growth on the walk.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticPositiveDuality.TranslationLaw

variable {G : Type*} [AddCommGroup G]

/-- One step with probabilities w and 1−w. -/
def mean (w : ℝ) (a b : G) (f : G → ℝ) (x : G) :=
  w*f (x+a)+(1-w)*f (x+b)

/-- Contrast of the two possible successors. -/
def contrast (a b : G) (f : G → ℝ) (x : G) := f (x+a)-f (x+b)

/-- Expectation after n independent steps. -/
def walk (w : ℝ) (a b : G) : ℕ → (G → ℝ) → G → ℝ
  | 0, f => f
  | n+1, f => mean w a b (walk w a b n f)

/-- Commuting translations preserve harmonicity under directional differencing. -/
theorem mean_contrast (w : ℝ) (a b c d : G) (f : G → ℝ) :
    mean w a b (contrast c d f) = contrast c d (mean w a b f) := by
  funext x
  simp only [mean, contrast, add_right_comm x]
  ring

/-- Exact energy split for one step, without any harmonicity assumption. -/
theorem mean_square (w : ℝ) (a b : G) (f : G → ℝ) (x : G) :
    mean w a b (fun y => f y ^ 2) x =
      mean w a b f x ^ 2 + w*(1-w)*contrast a b f x ^ 2 := by
  unfold mean contrast
  ring

private lemma walk_linear (w r : ℝ) (a b : G) (f g : G → ℝ) (n : ℕ) :
    walk w a b n (fun x => f x+r*g x) =
      fun x => walk w a b n f x+r*walk w a b n g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    simp only [walk, ih, mean]
    ring

private lemma walk_succ_right (w : ℝ) (a b : G) (f : G → ℝ) (n : ℕ) :
    walk w a b (n+1) f = walk w a b n (mean w a b f) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (mean w a b) ih

/-- Exact accumulated Dirichlet energy. Each summand is the transported
square contrast at its own time. -/
theorem harmonic_variance (w : ℝ) (a b : G) {f : G → ℝ} (hf : mean w a b f = f)
    (n : ℕ) (x : G) :
    walk w a b n (fun y => f y ^ 2) x = f x ^ 2 + w*(1-w)*
      ∑ j ∈ range n, walk w a b j (fun y => contrast a b f y ^ 2) x := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    rw [walk_succ_right, show mean w a b (fun y => f y^2) =
        (fun y => f y^2 + (w*(1-w))*contrast a b f y^2) from
          funext fun y => by rw [mean_square, hf], walk_linear, sum_range_succ, ih]
    ring

private lemma walk_le_const (w : ℝ) (hw : w ∈ Set.Icc 0 1) (a b : G) {f : G → ℝ}
    {C : ℝ} (h : ∀ x, f x ≤ C) (n : ℕ) (x : G) : walk w a b n f x ≤ C := by
  induction n generalizing x with
  | zero => exact h x
  | succ n ih =>
    calc walk w a b (n+1) f x ≤ w*C+(1-w)*C :=
          add_le_add (mul_le_mul_of_nonneg_left (ih _) hw.1)
            (mul_le_mul_of_nonneg_left (ih _) (sub_nonneg.mpr hw.2))
      _ = C := by ring

private lemma walk_square_floor (w : ℝ) (hw : w ∈ Set.Icc 0 1) (a b : G)
    {f : G → ℝ} (hf : mean w a b f = f) (n : ℕ) (x : G) :
    f x^2 ≤ walk w a b n (fun y => f y^2) x := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
    calc f x^2 ≤ mean w a b (fun y => f y^2) x := by
            rw [mean_square, hf]
            exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hw.1 (sub_nonneg.mpr hw.2)) (sq_nonneg _))
      _ ≤ walk w a b (n+1) (fun y => f y^2) x :=
            add_le_add (mul_le_mul_of_nonneg_left (ih _) hw.1)
              (mul_le_mul_of_nonneg_left (ih _) (sub_nonneg.mpr hw.2))

/-- A nonzero directional contrast forces at least linear growth of the second moment. -/
theorem contrast_forces_linear_variance (w : ℝ) (hw : w ∈ Set.Icc 0 1) (a b : G)
    {f : G → ℝ} (hf : mean w a b f = f) (n : ℕ) (x : G) :
    f x^2 + w*(1-w)*(n*contrast a b f x^2) ≤ walk w a b n (fun y => f y^2) x := by
  rw [harmonic_variance _ _ _ hf]
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hw.1 (sub_nonneg.mpr hw.2))
  have hd : mean w a b (contrast a b f) = contrast a b f := (mean_contrast ..).trans (by rw [hf])
  simpa only [sum_const, card_range, nsmul_eq_mul] using
    (sum_le_sum (s := range n) (fun j _ => walk_square_floor w hw a b hd j x))

/-- Bounded harmonicity is equivalent to invariance under both translations.
No topological regularity or closed-subgroup assumption is needed. -/
theorem bounded_harmonic_iff (w : ℝ) (hw : w ∈ Set.Ioo 0 1) (a b : G)
    (f : G → ℝ) (hbd : ∃ M : ℝ, ∀ x, f x^2 ≤ M) :
    mean w a b f = f ↔ ∀ x, f (x+a)=f x ∧ f (x+b)=f x := by
  constructor
  · intro hf x
    obtain ⟨M,hM⟩ := hbd
    have hw' : w ∈ Set.Icc 0 1 := ⟨hw.1.le, hw.2.le⟩
    have hzero : contrast a b f x = 0 := by
      by_contra h
      have hpos := mul_pos (mul_pos hw.1 (sub_pos.mpr hw.2)) (sq_pos_of_ne_zero h)
      obtain ⟨n,hn⟩ := exists_nat_gt (M/(w*(1-w)*contrast a b f x^2))
      have hlt := (div_lt_iff₀ hpos).mp hn
      have hle := (contrast_forces_linear_variance w hw' a b hf n x).trans
        (walk_le_const w hw' a b hM n x)
      linarith only [hlt, hle, sq_nonneg (f x)]
    have he := sub_eq_zero.mp hzero
    have hx := congrFun hf x
    simp only [mean, he] at hx
    constructor <;> linarith only [he,hx]
  · intro h
    funext x
    rw [mean, (h x).1, (h x).2]
    ring

#print axioms harmonic_variance
#print axioms bounded_harmonic_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.TranslationLaw
