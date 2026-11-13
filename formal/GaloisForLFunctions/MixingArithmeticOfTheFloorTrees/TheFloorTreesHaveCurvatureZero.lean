import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Algebra.BigOperators.Field

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
  beta_reduce
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **`Γ₂` of a jump generator is a sum of squares of second differences.** The cross terms
`w_i w_j Δ_iΔ_j f (Δ_j f − Δ_i f)` cancel under the exchange of `i` and `j`. -/
theorem gammaTwo_eq (f : ℝ → ℝ) (u : ℝ) :
    gammaTwo s w a f u = (∑ i ∈ s, ∑ j ∈ s, w i * w j *
      (f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) ^ 2) / 4 := by
  have hc : ∀ x, carre s w a f f x = (∑ j ∈ s, w j * (f (x + a j) - f x) ^ 2) / 2 := fun x => by
    rw [carre_eq]; congr 1; exact Finset.sum_congr rfl fun j _ => by ring
  -- one row of the double sum
  have hrow : ∀ i, w i * (carre s w a f f (u + a i) - carre s w a f f u) -
      w i * ((f (u + a i) - f u) * (jumpGen s w a f (u + a i) - jumpGen s w a f u)) =
      ∑ j ∈ s, w i * w j * (((f (u + a i + a j) - f (u + a i)) ^ 2 - (f (u + a j) - f u) ^ 2) / 2 -
        (f (u + a i) - f u) * ((f (u + a i + a j) - f (u + a i)) - (f (u + a j) - f u))) := by
    intro i
    rw [hc, hc]
    unfold jumpGen
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hstep : gammaTwo s w a f u = (∑ i ∈ s, (w i * (carre s w a f f (u + a i) -
      carre s w a f f u) - w i * ((f (u + a i) - f u) *
        (jumpGen s w a f (u + a i) - jumpGen s w a f u)))) / 2 := by
    show ((∑ i ∈ s, w i * (carre s w a f f (u + a i) - carre s w a f f u)) -
      2 * carre s w a f (jumpGen s w a f) u) / 2 = _
    rw [carre_eq s w a f (jumpGen s w a f) u, show ∀ x : ℝ, 2 * (x / 2) = x from fun x => by ring,
      ← Finset.sum_sub_distrib]
  rw [hstep]
  simp only [hrow]
  -- split each term into the square and an antisymmetric part
  have hsplit : ∀ i j, w i * w j * (((f (u + a i + a j) - f (u + a i)) ^ 2 -
        (f (u + a j) - f u) ^ 2) / 2 -
        (f (u + a i) - f u) * ((f (u + a i + a j) - f (u + a i)) - (f (u + a j) - f u))) =
      w i * w j * (f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) ^ 2 / 2 +
        (w i * w j * ((f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) *
            (f (u + a j) - f u)) -
          w i * w j * ((f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) *
            (f (u + a i) - f u))) := fun i j => by ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hanti : ∑ i ∈ s, ∑ j ∈ s, w i * w j *
      ((f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) * (f (u + a j) - f u)) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j *
        ((f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) * (f (u + a i) - f u)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show u + a j + a i = u + a i + a j by ring]
    ring
  rw [hanti, sub_self, add_zero]
  have hdiv : ∑ i ∈ s, ∑ j ∈ s, w i * w j *
      (f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) ^ 2 / 2 =
      (∑ i ∈ s, ∑ j ∈ s, w i * w j *
        (f (u + a i + a j) - f (u + a i) - f (u + a j) + f u) ^ 2) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
  rw [hdiv]
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

/-- At common returns of `p` and `q` to `2πℤ` the second difference of the cosine is `O(η²)`. -/
theorem abs_second_diff_cos_return {p q η : ℝ} {m₁ m₂ : ℤ} (hp : |p - m₁ * (2 * π)| ≤ η)
    (hq : |q - m₂ * (2 * π)| ≤ η) :
    |Real.cos (p + q) - Real.cos p - Real.cos q + 1| ≤ η ^ 2 := by
  have e1 : Real.cos (p + q) = Real.cos (0 + (p - m₁ * (2 * π)) + (q - m₂ * (2 * π))) := by
    rw [show 0 + (p - m₁ * (2 * π)) + (q - m₂ * (2 * π)) = p + q - ((m₁ + m₂ : ℤ) : ℝ) * (2 * π) by
      push_cast; ring, Real.cos_sub_int_mul_two_pi]
  have e2 : Real.cos p = Real.cos (0 + (p - m₁ * (2 * π))) := by
    rw [zero_add, Real.cos_sub_int_mul_two_pi]
  have e3 : Real.cos q = Real.cos (0 + (q - m₂ * (2 * π))) := by
    rw [zero_add, Real.cos_sub_int_mul_two_pi]
  have e4 : (1 : ℝ) = Real.cos 0 := Real.cos_zero.symm
  rw [e1, e2, e3, e4]
  have h := abs_second_diff_cos_le 0 (p - m₁ * (2 * π)) (q - m₂ * (2 * π))
  have h0 := abs_nonneg (p - m₁ * (2 * π))
  have h0' := abs_nonneg (q - m₂ * (2 * π))
  calc _ ≤ |p - m₁ * (2 * π)| * |q - m₂ * (2 * π)| := h
    _ ≤ η * η := mul_le_mul hp hq h0' (h0.trans hp)
    _ = η ^ 2 := by ring

/-- **Curvature at most zero**: for the floor trees of `2 ≤ k ≤ Q` and every `κ > 0` the bound
`Γ₂ ≥ κ Γ` fails, on a wave plus a linear function: the linear part keeps `Γ` away from zero and
has no second differences, while the wave at a common return has second differences `O(η²)`. -/
theorem not_curvature_pos {Q : ℕ} (hQ : 2 ≤ Q) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (f : ℝ → ℝ) (u : ℝ), gammaTwo (treeJumps Q) treeRate treeJump f u <
      κ * carre (treeJumps Q) treeRate treeJump f f u := by
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ i ∈ treeJumps Q, treeRate i := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact Finset.sum_nonneg fun i _ => treeRate_nonneg i
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the precision of the return
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (min (Real.log 2 / 2) 1) (κ * Real.log 2 ^ 3 / (4 * (W + 1) ^ 2)) :=
    ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    exact lt_min (lt_min (by linarith) one_pos)
      (div_pos (mul_pos hκ (pow_pos hl2 3)) (mul_pos (by norm_num) (pow_pos (by linarith) 2)))
  have hη1 : η ≤ Real.log 2 / 2 := by rw [hη]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ 1 := by rw [hη]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ κ * Real.log 2 ^ 3 / (4 * (W + 1) ^ 2) := by rw [hη]; exact min_le_right _ _
  have hpi : 0 < 2 * π := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * π / η)
  have hN0 : (0 : ℝ) < N := (div_pos hpi hη0).trans hN
  have hN1 : 1 ≤ N := (by exact_mod_cast hN0 : 0 < N)
  have hNη : 2 * π / N ≤ η := by
    rw [div_le_iff₀ hN0]
    rw [div_lt_iff₀ hη0] at hN
    linarith
  obtain ⟨n, -, -, hn⟩ := HTGeometry.exists_dirichlet_simultaneous
    (ι := Icc 2 Q) (fun k => Real.log (k : ℕ) / (2 * π)) N hN1
  -- every jump returns to `2πℤ` within `η`
  have hret : ∀ i ∈ treeJumps Q, ∃ m : ℤ, |(n : ℝ) * treeJump i - m * (2 * π)| ≤ η := by
    rintro ⟨k, b⟩ hi
    have hk : k ∈ Icc 2 Q := (Finset.mem_product.mp hi).1
    obtain ⟨m, hm⟩ := hn ⟨k, hk⟩
    have h1 : |(n : ℝ) * Real.log k - m * (2 * π)| ≤ η := by
      have e : (n : ℝ) * Real.log k - m * (2 * π) =
          2 * π * ((n : ℝ) * (Real.log (k : ℕ) / (2 * π)) - m) := by
        have h := div_mul_cancel₀ (Real.log (k : ℕ)) hpi.ne'
        linear_combination (-(n : ℝ)) * h
      rw [e, abs_mul, abs_of_pos hpi]
      have := mul_le_mul_of_nonneg_left hm.le hpi.le
      calc 2 * π * |(n : ℝ) * (Real.log (k : ℕ) / (2 * π)) - m| ≤ 2 * π * (1 / N) := this
        _ = 2 * π / N := by ring
        _ ≤ η := hNη
    cases b
    · refine ⟨-m, ?_⟩
      have e : (n : ℝ) * treeJump (k, false) - ((-m : ℤ) : ℝ) * (2 * π) =
          -((n : ℝ) * Real.log k - m * (2 * π)) := by
        show (n : ℝ) * (-Real.log k) - ((-m : ℤ) : ℝ) * (2 * π) = _
        push_cast; ring
      rw [e, abs_neg]; exact h1
    · exact ⟨m, h1⟩
  -- the test function: a wave plus a linear function
  refine ⟨fun u => Real.cos (n * u) + u, 0, ?_⟩
  -- `Γ₂` is `O(η⁴)`
  have hsd : ∀ i ∈ treeJumps Q, ∀ j ∈ treeJumps Q,
      ((Real.cos (n * (0 + treeJump i + treeJump j)) + (0 + treeJump i + treeJump j)) -
        (Real.cos (n * (0 + treeJump i)) + (0 + treeJump i)) -
          (Real.cos (n * (0 + treeJump j)) + (0 + treeJump j)) +
            (Real.cos (n * 0) + 0)) ^ 2 ≤ η ^ 4 := by
    intro i hi j hj
    obtain ⟨m₁, h1⟩ := hret i hi
    obtain ⟨m₂, h2⟩ := hret j hj
    have e : (Real.cos (n * (0 + treeJump i + treeJump j)) + (0 + treeJump i + treeJump j)) -
        (Real.cos (n * (0 + treeJump i)) + (0 + treeJump i)) -
          (Real.cos (n * (0 + treeJump j)) + (0 + treeJump j)) + (Real.cos (n * 0) + 0) =
        Real.cos ((n : ℝ) * treeJump i + n * treeJump j) - Real.cos (n * treeJump i) -
          Real.cos (n * treeJump j) + 1 := by
      rw [show (n : ℝ) * (0 + treeJump i + treeJump j) = n * treeJump i + n * treeJump j by ring,
        show (n : ℝ) * (0 + treeJump i) = n * treeJump i by ring,
        show (n : ℝ) * (0 + treeJump j) = n * treeJump j by ring, mul_zero, Real.cos_zero]
      ring
    rw [e]
    have hb := abs_second_diff_cos_return h1 h2
    have h0 := abs_nonneg (Real.cos ((n : ℝ) * treeJump i + n * treeJump j) -
      Real.cos (n * treeJump i) - Real.cos (n * treeJump j) + 1)
    have := sq_abs (Real.cos ((n : ℝ) * treeJump i + n * treeJump j) -
      Real.cos (n * treeJump i) - Real.cos (n * treeJump j) + 1)
    nlinarith [pow_le_pow_left₀ h0 hb 2]
  have hG2 : gammaTwo (treeJumps Q) treeRate treeJump (fun u => Real.cos (n * u) + u) 0 ≤
      W ^ 2 * η ^ 4 / 4 := by
    rw [gammaTwo_eq, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)]
    calc ∑ i ∈ treeJumps Q, ∑ j ∈ treeJumps Q, treeRate i * treeRate j *
          ((Real.cos (n * (0 + treeJump i + treeJump j)) + (0 + treeJump i + treeJump j)) -
            (Real.cos (n * (0 + treeJump i)) + (0 + treeJump i)) -
              (Real.cos (n * (0 + treeJump j)) + (0 + treeJump j)) +
                (Real.cos (n * 0) + 0)) ^ 2
        ≤ ∑ i ∈ treeJumps Q, ∑ j ∈ treeJumps Q, treeRate i * treeRate j * η ^ 4 :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hsd i hi j hj)
              (mul_nonneg (treeRate_nonneg i) (treeRate_nonneg j))
      _ = W ^ 2 * η ^ 4 := by
          rw [hW, sq, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
  -- `Γ` is at least `(log 2)³/8`, from the jump `+log 2`
  have hmem : ((2 : ℕ), true) ∈ treeJumps Q := Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩, Finset.mem_univ _⟩
  have hG : Real.log 2 ^ 3 / 8 ≤
      carre (treeJumps Q) treeRate treeJump (fun u => Real.cos (n * u) + u)
        (fun u => Real.cos (n * u) + u) 0 := by
    rw [carre_eq]
    have hterm : Real.log 2 ^ 3 / 4 ≤ treeRate (2, true) *
        (((Real.cos (n * (0 + treeJump (2, true))) + (0 + treeJump (2, true))) -
          (Real.cos (n * 0) + 0)) *
        ((Real.cos (n * (0 + treeJump (2, true))) + (0 + treeJump (2, true))) -
          (Real.cos (n * 0) + 0))) := by
      have hr : treeRate (2, true) = Real.log 2 := by
        show Λ 2 = Real.log 2
        rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      have hj : treeJump (2, true) = Real.log 2 := by
        show Real.log ((2 : ℕ) : ℝ) = Real.log 2
        norm_num
      rw [hr, hj, zero_add, mul_zero, Real.cos_zero, add_zero]
      obtain ⟨m, hm⟩ := hret _ hmem
      rw [hj] at hm
      have hc : |Real.cos (n * Real.log 2) - 1| ≤ η := by
        have e : Real.cos (n * Real.log 2) = Real.cos (n * Real.log 2 - m * (2 * π)) :=
          (Real.cos_sub_int_mul_two_pi _ _).symm
        rw [e, ← Real.cos_zero]
        refine (abs_cos_sub_cos_le' _ _).trans ?_
        rw [sub_zero]; exact hm
      have hD : Real.log 2 / 2 ≤ Real.cos (n * Real.log 2) + Real.log 2 - 1 := by
        have := neg_abs_le (Real.cos (n * Real.log 2) - 1)
        linarith
      have hD2 : (Real.log 2 / 2) ^ 2 ≤ (Real.cos (n * Real.log 2) + Real.log 2 - 1) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hD 2
      nlinarith
    have hsum := Finset.single_le_sum (f := fun i => treeRate i *
        (((Real.cos (n * (0 + treeJump i)) + (0 + treeJump i)) - (Real.cos (n * 0) + 0)) *
        ((Real.cos (n * (0 + treeJump i)) + (0 + treeJump i)) - (Real.cos (n * 0) + 0))))
      (fun i _ => mul_nonneg (treeRate_nonneg i) (mul_self_nonneg _)) hmem
    linarith
  -- `W² η⁴/4 < κ (log 2)³/8`
  have hfin : W ^ 2 * η ^ 4 / 4 < κ * (Real.log 2 ^ 3 / 8) := by
    have h4 : η ^ 4 ≤ η := pow_le_of_le_one hη0.le hη2 (by norm_num)
    have hW1 : W ^ 2 ≤ (W + 1) ^ 2 := by nlinarith
    have h5 : W ^ 2 * η ^ 4 ≤ (W + 1) ^ 2 * η :=
      mul_le_mul hW1 h4 (by positivity) (by positivity)
    have h6 : (W + 1) ^ 2 * η ≤ κ * Real.log 2 ^ 3 / 4 := by
      have := mul_le_mul_of_nonneg_left hη3 (by positivity : (0 : ℝ) ≤ (W + 1) ^ 2)
      rw [mul_div_assoc', mul_comm ((W + 1) ^ 2) (κ * Real.log 2 ^ 3),
        mul_div_mul_right _ _ (pow_pos (by linarith : (0 : ℝ) < W + 1) 2).ne'] at this
      exact this
    have h7 : 0 < κ * Real.log 2 ^ 3 := mul_pos hκ (pow_pos hl2 3)
    linarith
  calc gammaTwo (treeJumps Q) treeRate treeJump (fun u => Real.cos (n * u) + u) 0
      ≤ W ^ 2 * η ^ 4 / 4 := hG2
    _ < κ * (Real.log 2 ^ 3 / 8) := hfin
    _ ≤ κ * carre (treeJumps Q) treeRate treeJump (fun u => Real.cos (n * u) + u)
          (fun u => Real.cos (n * u) + u) 0 := mul_le_mul_of_nonneg_left hG hκ.le

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
