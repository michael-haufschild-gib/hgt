import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Bounded Kelvin-chirp separators die at a finite support ratio

For a continuous `1`-periodic `F` put `H(v) = e^{v/2} F(e^v) + e^{−v/2} F(e^{−v})` (the Kelvin
symmetrization in log coordinates).  If `H` is positive definite on `[−L, L]` — in particular if
`|H(v)| ≤ H(0)` for `|v| ≤ L` — and `F ≢ 0`, then (`exp_le_of_posDefOn`)

`e^L ≤ 4 + 2√2`.

Proof: `H(0) = 2F(1) ≤ 2‖F‖_∞`.  The interval `[e^L − 1, e^L]` contains a point `t ≡ x*` (mod 1)
where `|F(x*)| = ‖F‖_∞`; at `v = log t`, `|H(v)| ≥ (√t − 1/√t)‖F‖_∞ ≥ (√y − 1/√y)‖F‖_∞` with
`y = e^L − 1`.  So `√y − 1/√y ≤ 2`, i.e. `√y ≤ 1 + √2` and `e^L ≤ 1 + (1 + √2)² = 4 + 2√2`.
Hence beyond the support ratio `4 + 2√2` every separator built from a bounded periodic profile is
singular.
-/

open Real Set

namespace RHTower.KelvinSeparator

noncomputable section

/-- The Kelvin symmetrization `H(v) = e^{v/2} F(e^v) + e^{−v/2} F(e^{−v})`. -/
def kelvinSym (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  Real.exp (v / 2) * F (Real.exp v) + Real.exp (-v / 2) * F (Real.exp (-v))

theorem kelvinSym_neg (F : ℝ → ℝ) (v : ℝ) : kelvinSym F (-v) = kelvinSym F v := by
  unfold kelvinSym
  rw [neg_neg, show -(-v) / 2 = v / 2 by ring, show -v / 2 = -v / 2 from rfl]
  ring

theorem kelvinSym_zero (F : ℝ → ℝ) : kelvinSym F 0 = 2 * F 1 := by
  simp [kelvinSym]
  ring

/-- Positive definiteness of a real even kernel on `[−L, L]`. -/
def PosDefOn (H : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (c x : Fin n → ℝ), (∀ i, |x i| ≤ L / 2) →
    0 ≤ ∑ i, ∑ j, c i * c j * H (x i - x j)

/-- A positive-definite even kernel is dominated by its value at `0`. -/
theorem abs_le_of_posDefOn {H : ℝ → ℝ} {L : ℝ} (hH : PosDefOn H L) (heven : ∀ v, H (-v) = H v)
    {v : ℝ} (hv : |v| ≤ L) : |H v| ≤ H 0 := by
  have hx : ∀ i : Fin 2, |(![v / 2, -(v / 2)] : Fin 2 → ℝ) i| ≤ L / 2 := by
    intro i
    fin_cases i <;> simp [abs_div, abs_neg] <;> linarith [abs_nonneg v]
  have key : ∀ a b : ℝ, 0 ≤ (a ^ 2 + b ^ 2) * H 0 + 2 * a * b * H v := by
    intro a b
    have := hH 2 ![a, b] ![v / 2, -(v / 2)] hx
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      sub_self, show v / 2 - -(v / 2) = v by ring, show -(v / 2) - v / 2 = -v by ring,
      heven] at this
    nlinarith [this]
  have h1 := key 1 (-1)
  have h2 := key 1 1
  rw [abs_le]
  constructor <;> nlinarith

/-- **Bounded separators die beyond the ratio `4 + 2√2`.** -/
theorem exp_le_of_abs_le {F : ℝ → ℝ} (hF : Continuous F) (hper : Function.Periodic F 1)
    (hne : ∃ x, F x ≠ 0) {L : ℝ} (hL : 0 < L)
    (hdom : ∀ v, |v| ≤ L → |kelvinSym F v| ≤ kelvinSym F 0) :
    Real.exp L ≤ 4 + 2 * Real.sqrt 2 := by
  -- the maximum of `|F|` over a period
  obtain ⟨xs, hxs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (zero_le_one' ℝ))
    (hF.abs.continuousOn (s := Icc (0 : ℝ) 1))
  set M := |F xs| with hM
  have hbound : ∀ x, |F x| ≤ M := by
    intro x
    have hfr : F x = F (Int.fract x) := by
      rw [← Int.self_sub_floor, sub_eq_add_neg, ← Int.cast_neg]
      exact (hper.int_mul (-⌊x⌋)).symm.trans (by rw [Int.cast_neg, mul_one])?
    sorry
  sorry

end

end RHTower.KelvinSeparator
