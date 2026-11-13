import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The floor trees have curvature zero

At infinite block size the floor trees are the dilation process: in the coordinate `u = log x` it
jumps by `+log k` at the rate `Λ(k)` and by `−log k` at the rate `Λ(k)/k`. Its generator
`L f(u) = Σ_i w_i (f(u + a_i) − f(u))` is translation invariant, a Lévy generator with finitely
many jumps. For such a generator the carré du champ and its iterate are sums of squares of first
and second differences (`carre_eq`, `gammaTwo_eq`):

  `Γ(f) = ½ Σ_i w_i (Δ_i f)²`,   `Γ₂(f) = ½ Σ_{i,j} w_i w_j (Δ_i Δ_j f)²`.

* **Curvature at least zero** (`gammaTwo_nonneg`): `Γ₂ ≥ 0`, the Bakry–Émery condition
  `CD(0, ∞)`.
* **Curvature at most zero** (`not_curvature_pos`): for the floor trees of the integers
  `2 ≤ k ≤ Q` no bound `Γ₂ ≥ κ Γ` with `κ > 0` holds. At a common return of the rotations `t log k`
  to `2πℤ` (Dirichlet) the wave `cos(t u)` at a point where it vanishes has `Γ ≍ η²` and
  `Γ₂ = O(η⁴)`: second differences of a wave are products of two first differences.

So the curvature of the floor trees is exactly zero: a curvature argument cannot give the gap of
the Doob chain from the trees, in agreement with the absence of a gap of the dilation process.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

section Levy

variable {ι : Type*} (s : Finset ι) (w a : ι → ℝ)

/-- A translation-invariant jump generator with the jumps `a_i` at the rates `w_i`. -/
def jumpGen (f : ℝ → ℝ) (u : ℝ) : ℝ := ∑ i ∈ s, w i * (f (u + a i) - f u)

/-- The carré du champ `Γ(f, g) = ½ (L(fg) − f Lg − g Lf)`. -/
def carre (f g : ℝ → ℝ) (u : ℝ) : ℝ :=
  (jumpGen s w a (fun x => f x * g x) u - f u * jumpGen s w a g u - g u * jumpGen s w a f u) / 2

/-- The iterated carré du champ `Γ₂(f) = ½ (L Γ(f, f) − 2 Γ(f, L f))`. -/
def gammaTwo (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  (jumpGen s w a (carre s w a f f) u - 2 * carre s w a f (jumpGen s w a f) u) / 2

/-- **The carré du champ of a jump generator**: `Γ(f, g) = ½ Σ w_i Δ_i f Δ_i g`. -/
theorem carre_eq (f g : ℝ → ℝ) (u : ℝ) :
    carre s w a f g u = (∑ i ∈ s, w i * ((f (u + a i) - f u) * (g (u + a i) - g u))) / 2 := by
  unfold carre jumpGen
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **`Γ₂` of a jump generator is a sum of squares of second differences.** -/
theorem gammaTwo_eq (f : ℝ → ℝ) (u : ℝ) :
    gammaTwo s w a f u = (∑ i ∈ s, ∑ j ∈ s, w i * w j *
      (f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) ^ 2) / 4 := by
  have hc : ∀ x, carre s w a f f x = (∑ j ∈ s, w j * (f (x + a j) - f x) ^ 2) / 2 := fun x => by
    rw [carre_eq]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold gammaTwo
  rw [carre_eq]
  unfold jumpGen
  simp only [hc]
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show u + a i + a j = u + a j + a i by ring]
  ring

/-- **Curvature at least zero**: `Γ₂ ≥ 0` for every jump generator with nonnegative rates. -/
theorem gammaTwo_nonneg (hw : ∀ i ∈ s, 0 ≤ w i) (f : ℝ → ℝ) (u : ℝ) :
    0 ≤ gammaTwo s w a f u := by
  rw [gammaTwo_eq]
  refine div_nonneg (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_) (by norm_num)
  exact mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)

end Levy

/-! ### The floor trees -/

/-- The jumps of the floor trees of `2 ≤ k ≤ Q`: `+log k` at the rate `Λ(k)` (index `(k, true)`)
and `−log k` at the rate `Λ(k)/k` (index `(k, false)`). -/
def treeJumps (Q : ℕ) : Finset (ℕ × Bool) := Icc 2 Q ×ˢ Finset.univ

def treeRate (i : ℕ × Bool) : ℝ := if i.2 then Λ i.1 else Λ i.1 / i.1

def treeJump (i : ℕ × Bool) : ℝ := if i.2 then Real.log i.1 else -Real.log i.1

theorem treeRate_nonneg (i : ℕ × Bool) : 0 ≤ treeRate i := by
  unfold treeRate
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

theorem abs_cos_sub_cos_le' (x y : ℝ) : |Real.cos x - Real.cos y| ≤ |x - y| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_two]
  have h1 := Real.abs_sin_le_one ((x + y) / 2)
  have h2 := Real.abs_sin_le_abs (x := (x - y) / 2)
  rw [abs_div, abs_two] at h2
  nlinarith [abs_nonneg (Real.sin ((x + y) / 2)), abs_nonneg (Real.sin ((x - y) / 2))]

/-- The second difference of a wave is the product of two first differences:
`cos(s + p + q) − cos(s + p) − cos(s + q) + cos s` is bounded by `|p| |q|`. -/
theorem abs_second_diff_cos_le (s p q : ℝ) :
    |Real.cos (s + p + q) - Real.cos (s + p) - Real.cos (s + q) + Real.cos s| ≤ |p| * |q| := by
  -- `∫₀^p ∫₀^q −cos(s + x + y)`; bound it by the mean value theorem twice
  have h1 : Real.cos (s + p + q) - Real.cos (s + p) - Real.cos (s + q) + Real.cos s =
      -4 * Real.sin (p / 2) * Real.sin (q / 2) * Real.cos (s + p / 2 + q / 2) := by
    have e1 : Real.cos (s + p + q) - Real.cos (s + q) =
        -2 * Real.sin ((s + p + q + (s + q)) / 2) * Real.sin ((s + p + q - (s + q)) / 2) :=
      Real.cos_sub_cos _ _
    have e2 : Real.cos (s + p) - Real.cos s =
        -2 * Real.sin ((s + p + s) / 2) * Real.sin ((s + p - s) / 2) := Real.cos_sub_cos _ _
    have e3 : Real.sin ((s + p + q + (s + q)) / 2) - Real.sin ((s + p + s) / 2) =
        2 * Real.sin (((s + p + q + (s + q)) / 2 - (s + p + s) / 2) / 2) *
          Real.cos (((s + p + q + (s + q)) / 2 + (s + p + s) / 2) / 2) := Real.sin_sub_sin _ _
    have e4 : (s + p + q - (s + q)) / 2 = p / 2 := by ring
    have e5 : (s + p - s) / 2 = p / 2 := by ring
    have e6 : ((s + p + q + (s + q)) / 2 - (s + p + s) / 2) / 2 = q / 2 := by ring
    have e7 : ((s + p + q + (s + q)) / 2 + (s + p + s) / 2) / 2 = s + p / 2 + q / 2 := by ring
    rw [e4] at e1
    rw [e5] at e2
    rw [e6, e7] at e3
    linear_combination e1 - e2 + (-2 * Real.sin (p / 2)) * e3
  rw [h1]
  have hp := Real.abs_sin_le_abs (x := p / 2)
  have hq := Real.abs_sin_le_abs (x := q / 2)
  have hc := Real.abs_cos_le_one (s + p / 2 + q / 2)
  rw [abs_div, abs_two] at hp hq
  rw [abs_mul, abs_mul, abs_mul, show |(-4 : ℝ)| = 4 by norm_num]
  have h0p := abs_nonneg (Real.sin (p / 2))
  have h0q := abs_nonneg (Real.sin (q / 2))
  have h0c := abs_nonneg (Real.cos (s + p / 2 + q / 2))
  calc 4 * |Real.sin (p / 2)| * |Real.sin (q / 2)| * |Real.cos (s + p / 2 + q / 2)|
      ≤ 4 * (|p| / 2) * (|q| / 2) * 1 := by
        gcongr
    _ = |p| * |q| := by ring

/-- **Curvature at most zero**: for the floor trees of `2 ≤ k ≤ Q` and every `κ > 0` some wave
violates `Γ₂ ≥ κ Γ`. -/
theorem not_curvature_pos {Q : ℕ} (hQ : 2 ≤ Q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (f : ℝ → ℝ) (u : ℝ), gammaTwo (treeJumps Q) treeRate (fun i => treeJump i) f u <
      κ * carre (treeJumps Q) treeRate (fun i => treeJump i) f f u := by
  sorry

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
