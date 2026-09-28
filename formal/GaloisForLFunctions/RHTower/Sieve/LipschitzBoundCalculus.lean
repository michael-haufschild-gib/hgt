import Mathlib

/-!
# Explicit Lipschitz bounds on sets

`LipschitzBound g s L` says `|g x - g y| ≤ L |x - y|` on `s`.  Constants, affine maps, sums,
products of bounded functions, `log` and reciprocals of affine maps bounded away from `0`.
-/

namespace RHTower.Sieve

open Real

/-- `g` is `L`-Lipschitz on `s`. -/
def LipschitzBound (g : ℝ → ℝ) (s : Set ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, |g x - g y| ≤ L * |x - y|

theorem LipschitzBound.mono_const {g : ℝ → ℝ} {s : Set ℝ} {L L' : ℝ} (h : LipschitzBound g s L)
    (hL : L ≤ L') : LipschitzBound g s L' := fun x hx y hy =>
  (h x hx y hy).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))

theorem LipschitzBound.mono_set {g : ℝ → ℝ} {s t : Set ℝ} {L : ℝ} (h : LipschitzBound g t L)
    (hst : s ⊆ t) : LipschitzBound g s L := fun x hx y hy => h x (hst hx) y (hst hy)

theorem lipschitzBound_const (c : ℝ) (s : Set ℝ) : LipschitzBound (fun _ => c) s 0 := by
  intro x _ y _; simp

theorem lipschitzBound_affine (p q : ℝ) (s : Set ℝ) :
    LipschitzBound (fun x => p + q * x) s |q| := by
  intro x _ y _
  rw [show p + q * x - (p + q * y) = q * (x - y) by ring, abs_mul]

theorem LipschitzBound.add {f g : ℝ → ℝ} {s : Set ℝ} {Lf Lg : ℝ} (hf : LipschitzBound f s Lf)
    (hg : LipschitzBound g s Lg) : LipschitzBound (fun x => f x + g x) s (Lf + Lg) := by
  intro x hx y hy
  calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
    _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
    _ ≤ Lf * |x - y| + Lg * |x - y| := add_le_add (hf x hx y hy) (hg x hx y hy)
    _ = (Lf + Lg) * |x - y| := by ring

theorem LipschitzBound.neg {f : ℝ → ℝ} {s : Set ℝ} {L : ℝ} (hf : LipschitzBound f s L) :
    LipschitzBound (fun x => -f x) s L := by
  intro x hx y hy
  rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
  exact hf x hx y hy

theorem LipschitzBound.sub {f g : ℝ → ℝ} {s : Set ℝ} {Lf Lg : ℝ} (hf : LipschitzBound f s Lf)
    (hg : LipschitzBound g s Lg) : LipschitzBound (fun x => f x - g x) s (Lf + Lg) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem LipschitzBound.mul {f g : ℝ → ℝ} {s : Set ℝ} {Lf Lg Mf Mg : ℝ}
    (hf : LipschitzBound f s Lf) (hg : LipschitzBound g s Lg) (hMf : ∀ x ∈ s, |f x| ≤ Mf)
    (hMg : ∀ x ∈ s, |g x| ≤ Mg) :
    LipschitzBound (fun x => f x * g x) s (Mf * Lg + Mg * Lf) := by
  intro x hx y hy
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  calc |f x * (g x - g y) + g y * (f x - f y)|
      ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Mf * (Lg * |x - y|) + Mg * (Lf * |x - y|) := by
        gcongr
        · exact (abs_nonneg _).trans (hMf x hx)
        · exact hMf x hx
        · exact hg x hx y hy
        · exact (abs_nonneg _).trans (hMg y hy)
        · exact hMg y hy
        · exact hf x hx y hy
    _ = (Mf * Lg + Mg * Lf) * |x - y| := by ring

theorem LipschitzBound.const_mul {f : ℝ → ℝ} {s : Set ℝ} {L : ℝ} (hf : LipschitzBound f s L)
    (c : ℝ) : LipschitzBound (fun x => c * f x) s (|c| * L) := by
  intro x hx y hy
  rw [show c * f x - c * f y = c * (f x - f y) by ring, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx y hy) (abs_nonneg c)

/-- `log (p + q x)` is `|q|/m`-Lipschitz where `p + q x ≥ m > 0`. -/
theorem lipschitzBound_log_affine {p q m : ℝ} {s : Set ℝ} (hm : 0 < m)
    (h : ∀ x ∈ s, m ≤ p + q * x) : LipschitzBound (fun x => log (p + q * x)) s (|q| / m) := by
  intro x hx y hy
  have hx0 : 0 < p + q * x := hm.trans_le (h x hx)
  have hy0 : 0 < p + q * y := hm.trans_le (h y hy)
  -- `|log a - log b| ≤ |a - b| / min a b`
  have key : ∀ a b : ℝ, 0 < a → 0 < b → m ≤ a → m ≤ b → |log a - log b| ≤ |a - b| / m := by
    intro a b ha hb hma hmb
    rcases le_total a b with hab | hab
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.log_le_log ha hab)), abs_sub_comm,
        abs_of_nonneg (sub_nonneg.2 hab), ← Real.log_div hb.ne' ha.ne']
      calc log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
        _ = (b - a) / a := by field_simp
        _ ≤ (b - a) / m := div_le_div_of_nonneg_left (sub_nonneg.2 hab) hm hma
    · rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hb hab)), abs_of_nonneg (sub_nonneg.2 hab),
        ← Real.log_div ha.ne' hb.ne']
      calc log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
        _ = (a - b) / b := by field_simp
        _ ≤ (a - b) / m := div_le_div_of_nonneg_left (sub_nonneg.2 hab) hm hmb
  calc |log (p + q * x) - log (p + q * y)| ≤ |p + q * x - (p + q * y)| / m :=
        key _ _ hx0 hy0 (h x hx) (h y hy)
    _ = |q| / m * |x - y| := by
        rw [show p + q * x - (p + q * y) = q * (x - y) by ring, abs_mul]; ring

/-- `1/(p + q x)` is `|q|/m²`-Lipschitz where `p + q x ≥ m > 0`. -/
theorem lipschitzBound_inv_affine {p q m : ℝ} {s : Set ℝ} (hm : 0 < m)
    (h : ∀ x ∈ s, m ≤ p + q * x) : LipschitzBound (fun x => 1 / (p + q * x)) s (|q| / m ^ 2) := by
  intro x hx y hy
  have hx0 : 0 < p + q * x := hm.trans_le (h x hx)
  have hy0 : 0 < p + q * y := hm.trans_le (h y hy)
  have e : 1 / (p + q * x) - 1 / (p + q * y) = q * (y - x) / ((p + q * x) * (p + q * y)) := by
    field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm y x]
  have hden : m ^ 2 ≤ (p + q * x) * (p + q * y) := by
    rw [sq]; exact mul_le_mul (h x hx) (h y hy) hm.le hx0.le
  calc |q| * |x - y| / ((p + q * x) * (p + q * y)) ≤ |q| * |x - y| / m ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = |q| / m ^ 2 * |x - y| := by ring

theorem abs_log_le_of_mem {a lo hi : ℝ} (hlo : 0 < lo) (h1 : lo ≤ a) (h2 : a ≤ hi) :
    |log a| ≤ max (log hi) (-log lo) := by
  have ha : 0 < a := hlo.trans_le h1
  rcases le_total a 1 with h | h
  · rw [abs_of_nonpos (Real.log_nonpos ha.le h)]
    exact le_max_of_le_right (neg_le_neg (Real.log_le_log hlo h1))
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    exact le_max_of_le_left (Real.log_le_log ha h2)

end RHTower.Sieve
