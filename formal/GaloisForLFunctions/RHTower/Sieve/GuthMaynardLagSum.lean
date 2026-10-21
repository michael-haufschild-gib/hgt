import Mathlib

/-!
# The lag sum `R(v) = Σ_{t ∈ W} v^{it}` and the additive energy of a point set

Shared vocabulary of the Guth–Maynard large-values programme (arXiv 2405.20552, §§7–11).
For a finite set `W ⊂ ℝ` of ordinates and `v > 0`,

`R(v) = Σ_{t ∈ W} v^{it} = Σ_{t ∈ W} exp(i t log v)`

is the exponential sum through which the cubic trace of the matrix `(w(n/N) n^{it})` is read
(`|I_m| ≪ N³ ∫ |R(v₁) R(v₂/v₁) R(v₂)| dv₁ dv₂`, Proposition 7.1), and

`E(W) = #{(t₁, t₂, t₃, t₄) ∈ W⁴ : |t₁ + t₂ − t₃ − t₄| ≤ 1}`

is the additive energy that controls its fourth moment (Lemma 8.3). Both are written with
`exp(i t log v)` so that no branch of the complex power enters. This module holds the definitions
and their elementary identities only; the estimates live in the `GuthMaynard*` modules.
-/

open Finset Complex

namespace RHTower.GuthMaynard

noncomputable section

/-- `R(v) = Σ_{t ∈ W} v^{it}`, as `Σ exp(i t log v)`; defined for every real `v`, meaningful for
`v > 0`. -/
def lagSum (W : Finset ℝ) (v : ℝ) : ℂ :=
  ∑ t ∈ W, Complex.exp (Complex.I * t * Real.log v)

/-- The additive energy `E(W) = #{(t₁, t₂, t₃, t₄) ∈ W⁴ : |t₁ + t₂ − t₃ − t₄| ≤ 1}`. -/
def additiveEnergy (W : Finset ℝ) : ℕ := by
  classical
  exact ((W ×ˢ W ×ˢ W ×ˢ W).filter
    fun q : ℝ × ℝ × ℝ × ℝ => |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1).card

/-- `W` is `δ`-separated: distinct points are at distance at least `δ`. -/
def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → δ ≤ |t - t'|

/-- Each summand of `R(v)` is unimodular. -/
theorem norm_exp_mul_log (t v : ℝ) : ‖Complex.exp (Complex.I * t * Real.log v)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The trivial bound `|R(v)| ≤ |W|`. -/
theorem norm_lagSum_le (W : Finset ℝ) (v : ℝ) : ‖lagSum W v‖ ≤ W.card := by
  unfold lagSum
  refine (norm_sum_le _ _).trans ?_
  simp [norm_exp_mul_log]

/-- `R(1) = |W|`. -/
theorem lagSum_one (W : Finset ℝ) : lagSum W 1 = W.card := by
  simp [lagSum]

/-- `R(1/v) = conj R(v)`. -/
theorem lagSum_inv (W : Finset ℝ) (v : ℝ) :
    lagSum W v⁻¹ = (starRingEnd ℂ) (lagSum W v) := by
  unfold lagSum
  rw [map_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [Real.log_inv, ← Complex.exp_conj]
  congr 1
  simp

/-- The additive energy is at most `|W|⁴`. -/
theorem additiveEnergy_le (W : Finset ℝ) : additiveEnergy W ≤ W.card ^ 4 := by
  unfold additiveEnergy
  refine (card_filter_le _ _).trans ?_
  simp only [card_product]
  ring_nf
  exact le_rfl

end

end RHTower.GuthMaynard
