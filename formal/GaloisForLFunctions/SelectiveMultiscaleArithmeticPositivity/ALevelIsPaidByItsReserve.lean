import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# A level is paid by its reserve

The complete arithmetic source is a dyadic multiresolution: refining one level adds a block of
details `d` to the coarse part `c`, and the form becomes `Q(c) + 2B(c, d) + E(d)`. Gamma pays the
details, `E(d) ≥ δ|d|²`; the coupling `B` is the only new obstruction. This file is the
renormalization calculus of that step.

* **Paying a coupling** (`two_mul_add_ge_of_reserve`): `|B| ≤ β|c||d|` and `E ≥ δ|d|²` give
  `2B + E ≥ (1 − θ)δ|d|² − (β²/(θδ))|c|²` for every `θ ∈ (0, 1]`. The coupling costs
  `β²/(θδ)` of coarse margin, and a fraction `1 − θ` of the detail reserve survives.
* **One renormalization step** (`rg_step`): a coarse margin `μ` becomes the margin
  `min(μ − β²/(θδ), (1 − θ)δ)` of the refined form.
* **Summable couplings keep a uniform margin** (`rgMargin_ge`, `rgMargin_pos`): iterating, the
  margin after any number of levels is at least `min(μ₀, D) − Σ c_l`, where `c_l` are the coupling
  costs and `D` a uniform lower bound for the surviving detail reserves. Positivity survives infinite
  refinement as soon as the coupling costs are summable below the initial margin.
* **The paid level is transparent** (`fromBlocks_posSemidef_iff_effective`,
  `effectiveCoarse_le`): if the detail block is positive definite, the refined Gram is positive
  semidefinite iff the Schur-corrected coarse Gram `A − B D⁻¹ Bᴴ` is, and the correction only lowers
  the coarse form.
* **Block dominance** (`sum_quadratic_ge_of_blockDominance`): a quadratic form on finitely many
  levels with level reserves `δ_i` and symmetric coupling bounds `b_ij` is at least
  `Σ_i (δ_i − Σ_{j ≠ i} b_ij)|x_i|²`: the Gershgorin criterion for forms.
-/

noncomputable section

open Finset Matrix

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-! ### One level -/

/-- **Paying a coupling from a detail reserve**: for `θ ∈ (0, 1]`, `|b| ≤ β s t` and `e ≥ δ t²`
give `2b + e ≥ (1 − θ)δ t² − (β²/(θδ)) s²`. -/
theorem two_mul_add_ge_of_reserve {b e s t β δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hb : |b| ≤ β * s * t) (he : δ * t ^ 2 ≤ e) :
    (1 - θ) * δ * t ^ 2 - β ^ 2 / (θ * δ) * s ^ 2 ≤ 2 * b + e := by
  have hθδ : 0 < θ * δ := mul_pos hθ hδ
  -- `2βst ≤ θδ t² + β² s²/(θδ)`, from `(θδ t − β s)² ≥ 0`
  have key : 2 * (β * s * t) ≤ θ * δ * t ^ 2 + β ^ 2 / (θ * δ) * s ^ 2 := by
    rw [div_mul_eq_mul_div, ← sub_nonneg]
    have h : θ * δ * t ^ 2 + β ^ 2 * s ^ 2 / (θ * δ) - 2 * (β * s * t) =
        (θ * δ * t - β * s) ^ 2 / (θ * δ) := by
      field_simp
      ring
    rw [h]
    positivity
  have hb' : -(β * s * t) ≤ b := (neg_le_neg hb).trans (neg_abs_le b)
  nlinarith

/-- **One renormalization step**: a coarse margin `μ` (`Q(c) ≥ μ|c|²`) becomes the refined margin
`min(μ − β²/(θδ), (1 − θ)δ)` on `|c|² + |d|²`. -/
theorem rg_step {q b e s t μ β δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) (hb : |b| ≤ β * s * t)
    (he : δ * t ^ 2 ≤ e) (hq : μ * s ^ 2 ≤ q) :
    min (μ - β ^ 2 / (θ * δ)) ((1 - θ) * δ) * (s ^ 2 + t ^ 2) ≤ q + 2 * b + e := by
  have h := two_mul_add_ge_of_reserve hδ hθ hb he
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (μ - β ^ 2 / (θ * δ)) ((1 - θ) * δ))
    (sq_nonneg s)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (μ - β ^ 2 / (θ * δ)) ((1 - θ) * δ))
    (sq_nonneg t)
  nlinarith

/-! ### Many levels -/

/-- The **renormalization margin**: start at `μ₀`; level `l` costs `c l` of the running margin and
caps it by its surviving detail reserve `d l`. -/
def rgMargin (μ₀ : ℝ) (c d : ℕ → ℝ) : ℕ → ℝ
  | 0 => μ₀
  | L + 1 => min (rgMargin μ₀ c d L - c L) (d L)

/-- **Summable couplings keep a uniform margin**: if every surviving detail reserve is at least `D`
and the coupling costs are nonnegative, the margin after `L` levels is at least
`min(μ₀, D) − Σ_{l < L} c_l`. -/
theorem rgMargin_ge (μ₀ D : ℝ) {c d : ℕ → ℝ} (hc : ∀ l, 0 ≤ c l) (hd : ∀ l, D ≤ d l) (L : ℕ) :
    min μ₀ D - ∑ l ∈ range L, c l ≤ rgMargin μ₀ c d L := by
  induction L with
  | zero => simp [rgMargin]
  | succ L ih =>
    rw [rgMargin, sum_range_succ]
    have hs : 0 ≤ ∑ l ∈ range L, c l := sum_nonneg fun l _ => hc l
    refine le_min (by linarith) ?_
    linarith [min_le_right μ₀ D, hd L, hc L]

/-- **Positivity survives infinite refinement**: if the total coupling cost stays below
`min(μ₀, D)`, every level keeps the positive margin `min(μ₀, D) − C`. -/
theorem rgMargin_pos (μ₀ D C : ℝ) {c d : ℕ → ℝ} (hc : ∀ l, 0 ≤ c l) (hd : ∀ l, D ≤ d l)
    (hC : ∀ L, ∑ l ∈ range L, c l ≤ C) (hCD : C < min μ₀ D) (L : ℕ) :
    0 < min μ₀ D - C ∧ min μ₀ D - C ≤ rgMargin μ₀ c d L :=
  ⟨by linarith, (by linarith [hC L] : min μ₀ D - C ≤ min μ₀ D - ∑ l ∈ range L, c l).trans
    (rgMargin_ge μ₀ D hc hd L)⟩

/-! ### The Schur form of a step -/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The paid level is transparent**: with a positive definite detail block `D`, the refined Gram
is positive semidefinite iff the Schur-corrected coarse Gram `A − B D⁻¹ Bᴴ` is. -/
theorem fromBlocks_posSemidef_iff_effective (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    {D : Matrix n n ℝ} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B * D⁻¹ * Bᴴ).PosSemidef :=
  PosDef.fromBlocks₂₂ A B hD

/-- **The correction only lowers the coarse form**: `A − (A − B D⁻¹ Bᴴ) = B D⁻¹ Bᴴ` is positive
semidefinite. -/
theorem effectiveCoarse_le (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) : (A - (A - B * D⁻¹ * Bᴴ)).PosSemidef := by
  rw [sub_sub_cancel]
  exact hD.posSemidef.inv.mul_mul_conjTranspose_same B

/-! ### Block dominance -/

/-- **Block dominance (Gershgorin for forms)**: on finitely many levels with level values
`Q_i ≥ δ_i x_i²` and couplings `c_ij ≥ −b_ij |x_i| |x_j|` (`i ≠ j`, `b` symmetric and nonnegative),
the total form is at least `Σ_i (δ_i − Σ_{j ≠ i} b_ij) x_i²`. -/
theorem sum_quadratic_ge_of_blockDominance {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (Q δ x : ι → ℝ) (c b : ι → ι → ℝ) (hQ : ∀ i ∈ s, δ i * x i ^ 2 ≤ Q i)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → -(b i j * |x i| * |x j|) ≤ c i j)
    (hb : ∀ i j, b i j = b j i) (hb0 : ∀ i j, 0 ≤ b i j) :
    ∑ i ∈ s, (δ i - ∑ j ∈ s, if i = j then 0 else b i j) * x i ^ 2 ≤
      ∑ i ∈ s, Q i + ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else c i j := by
  set P : ι → ι → ℝ := fun i j => if i = j then 0 else b i j * x i ^ 2
  set R : ι → ι → ℝ := fun i j => if i = j then 0 else b i j * x j ^ 2
  -- each coupling is at least `−b_ij (x_i² + x_j²)/2`
  have hpair : ∀ i ∈ s, ∀ j ∈ s, -(P i j + R i j) ≤ 2 * (if i = j then 0 else c i j) := by
    intro i hi j hj
    simp only [P, R]
    split_ifs with h
    · simp
    · have h1 := hc i hi j hj h
      have h2 : |x i| * |x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
        nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
      nlinarith [mul_le_mul_of_nonneg_left h2 (hb0 i j)]
  have hsum := sum_le_sum fun i hi => sum_le_sum fun j hj => hpair i hi j hj
  simp only [neg_add, sum_add_distrib, sum_neg_distrib, ← mul_sum] at hsum
  -- by symmetry the `x_j²` half equals the `x_i²` half
  have hsym : ∑ i ∈ s, ∑ j ∈ s, R i j = ∑ i ∈ s, ∑ j ∈ s, P i j := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [P, R]
    by_cases h : j = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), hb]
  have hrow : ∑ i ∈ s, ∑ j ∈ s, P i j =
      ∑ i ∈ s, (∑ j ∈ s, if i = j then 0 else b i j) * x i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun j _ => by simp only [P]; split_ifs <;> ring
  have hQs := sum_le_sum fun i hi => hQ i hi
  have hlhs : ∑ i ∈ s, (δ i - ∑ j ∈ s, if i = j then 0 else b i j) * x i ^ 2 =
      ∑ i ∈ s, δ i * x i ^ 2 - ∑ i ∈ s, (∑ j ∈ s, if i = j then 0 else b i j) * x i ^ 2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hlhs, ← hrow]
  linarith

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
