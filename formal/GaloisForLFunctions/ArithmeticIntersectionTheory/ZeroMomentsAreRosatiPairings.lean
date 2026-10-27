import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Zero moments are Rosati pairings

The explicit formula computes sums over the zeros of functions holomorphic in `ρ`. For a Dirichlet
polynomial `Q(s) = Σ_{n ∈ S} b_n n^{−(s−½)}` with real coefficients and its dual
`Q̃(s) = Σ b_n n^{s−½}`, the Landau–Gonek formula (`RHTower.exists_zeroSum_dirichletPolynomial_le`)
evaluates `Σ_ρ m_ρ ŵ(γ_ρ/T)(Q Q̃)^k(ρ)` from the primes up to the square-root threshold. This module
identifies what these moments are.

* **Duality** (`dualPoly_eq_conj`): `Q̃(ρ) = conj Q(ρ*)`, `ρ* = 1 − ρ̄`.
* **Collided on the line** (`mul_dualPoly_of_critical`): if `Re ρ = ½`, `(Q Q̃)(ρ) = |Q(ρ)|²`.
* **Rosati off the line** (`pair_pow_eq_two_re`): the pair `{ρ, ρ*}` contributes
  `(Q Q̃)^k(ρ) + (Q Q̃)^k(ρ*) = 2 Re (Q(ρ) conj Q(ρ*))^k`, of either sign.
* **Configurations** (`sum_moment_eq`, `sum_moment_re_nonneg_of_critical`): over a reflection-closed
  finite configuration the moment is real; it is a sum of squares when every point is critical.

So moments over zero ordinates are the reflection (Rosati) pairing, not the collided one: on the line
they coincide with the positive form, off it they pair `ρ` with `ρ*`. Their positivity for all `Q` and
`k` is a Hodge index of the same type as Weil's, read on two-point (and higher) statistics; it is not
an input that could prove it. The two-point form of the missing statement is a sign for the Rosati
products `Q(ρ) conj Q(ρ*)` beyond the square-root threshold (TTPC's coalescent surplus).
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

/-- The reflection `ρ* = 1 − ρ̄` of the functional equation composed with conjugation. -/
def reflectPoint (ρ : ℂ) : ℂ := 1 - conj ρ

theorem reflectPoint_reflectPoint (ρ : ℂ) : reflectPoint (reflectPoint ρ) = ρ := by
  simp [reflectPoint]

theorem reflectPoint_eq_self_iff (ρ : ℂ) : reflectPoint ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp [reflectPoint] at this
    linarith
  · intro h
    apply Complex.ext <;> simp [reflectPoint, h]; norm_num

variable (S : Finset ℕ) (b : ℕ → ℝ)

/-- `Q(s) = Σ_{n ∈ S} b_n n^{−(s−½)}`. -/
def dirichletPoly (s : ℂ) : ℂ := ∑ n ∈ S, (b n : ℂ) * (n : ℂ) ^ (-(s - 1 / 2))

/-- `Q̃(s) = Σ_{n ∈ S} b_n n^{s−½}`. -/
def dualPoly (s : ℂ) : ℂ := ∑ n ∈ S, (b n : ℂ) * (n : ℂ) ^ (s - 1 / 2)

/-- `conj(n^z) = n^{z̄}` for a positive integer `n`. -/
theorem conj_natCast_cpow {n : ℕ} (hn : 0 < n) (z : ℂ) :
    conj ((n : ℂ) ^ z) = (n : ℂ) ^ (conj z) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [cpow_def_of_ne_zero hn0, cpow_def_of_ne_zero hn0, ← exp_conj, map_mul,
    ← ofReal_natCast, ← ofReal_log (Nat.cast_nonneg n), conj_ofReal]

/-- **Duality**: `Q̃(ρ) = conj Q(ρ*)`. -/
theorem dualPoly_eq_conj (hS : ∀ n ∈ S, 0 < n) (ρ : ℂ) :
    dualPoly S b ρ = conj (dirichletPoly S b (reflectPoint ρ)) := by
  rw [dualPoly, dirichletPoly, map_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [map_mul, conj_ofReal, conj_natCast_cpow (hS n hn)]
  congr 2
  apply Complex.ext
  all_goals simp [reflectPoint]
  all_goals ring

/-- **Collided on the line**: `(Q Q̃)(ρ) = |Q(ρ)|²` when `Re ρ = ½`. -/
theorem mul_dualPoly_of_critical (hS : ∀ n ∈ S, 0 < n) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    dirichletPoly S b ρ * dualPoly S b ρ = (normSq (dirichletPoly S b ρ) : ℂ) := by
  rw [dualPoly_eq_conj S b hS, (reflectPoint_eq_self_iff ρ).mpr hρ, mul_conj]

/-- The Rosati product `z_ρ = Q(ρ) conj Q(ρ*)`. -/
def rosatiProduct (ρ : ℂ) : ℂ := dirichletPoly S b ρ * conj (dirichletPoly S b (reflectPoint ρ))

theorem mul_dualPoly_eq_rosatiProduct (hS : ∀ n ∈ S, 0 < n) (ρ : ℂ) :
    dirichletPoly S b ρ * dualPoly S b ρ = rosatiProduct S b ρ := by
  rw [dualPoly_eq_conj S b hS, rosatiProduct]

/-- The reflected point carries the conjugate Rosati product. -/
theorem rosatiProduct_reflectPoint (ρ : ℂ) :
    rosatiProduct S b (reflectPoint ρ) = conj (rosatiProduct S b ρ) := by
  rw [rosatiProduct, rosatiProduct, reflectPoint_reflectPoint, map_mul, conj_conj, mul_comm]

/-- **Rosati off the line**: the pair `{ρ, ρ*}` contributes `2 Re z_ρ^k` to the `k`-th moment. -/
theorem pair_pow_eq_two_re (ρ : ℂ) (k : ℕ) :
    rosatiProduct S b ρ ^ k + rosatiProduct S b (reflectPoint ρ) ^ k =
      ((2 * (rosatiProduct S b ρ ^ k).re : ℝ) : ℂ) := by
  rw [rosatiProduct_reflectPoint, ← map_pow, add_conj]

/-! ### Reflection-closed configurations -/

variable {ι : Type*} [Fintype ι]

/-- **The moment of a reflection-closed configuration is real.** If `σ` is an involution of the
configuration realizing `ρ ↦ ρ*` with equal multiplicities, the `k`-th moment equals its conjugate. -/
theorem sum_moment_eq (z : ι → ℂ) (m : ι → ℝ) (σ : ι ≃ ι) (hσ : ∀ j, z (σ j) = reflectPoint (z j))
    (hm : ∀ j, m (σ j) = m j) (k : ℕ) :
    conj (∑ j, (m j : ℂ) * rosatiProduct S b (z j) ^ k) =
      ∑ j, (m j : ℂ) * rosatiProduct S b (z j) ^ k := by
  rw [map_sum]
  refine (Fintype.sum_equiv σ _ _ fun j => ?_).symm
  rw [hσ, hm, rosatiProduct_reflectPoint, map_mul, conj_ofReal, map_pow, conj_conj]

/-- **On critical configurations the moment is a sum of squares.** -/
theorem sum_moment_re_nonneg_of_critical (hS : ∀ n ∈ S, 0 < n) (z : ι → ℂ) (m : ι → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hcrit : ∀ j, (z j).re = 1 / 2) (k : ℕ) :
    0 ≤ (∑ j, (m j : ℂ) * (dirichletPoly S b (z j) * dualPoly S b (z j)) ^ k).re := by
  rw [re_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [mul_dualPoly_of_critical S b hS (hcrit j), ← ofReal_pow, ← ofReal_mul, ofReal_re]
  exact mul_nonneg (hm j) (pow_nonneg (normSq_nonneg _) k)

end GaloisForLFunctions.ArithmeticIntersectionTheory
