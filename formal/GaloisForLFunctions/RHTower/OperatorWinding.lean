/-
# OperatorWinding — the doc 28 operator identities (task #143 / #138 substrate)

Doc 28 (28-operator-winding.md) §1–§4 `[PROVED HERE]`. Flat grading: elementary complex
algebra + a discriminant identity; doc 28 does the derivations, nothing new here.

The pair `(x − τ)(x − τ̄)` acts on the reversed section `Â` as the constant-coefficient damped
oscillator `Ĵ = Â″ − 2aÂ′ + |τ|²Â = (D − τ)(D − τ̄)Â` (τ = a + bi). Formalized here are the
algebraic facts that make the winding formula `Z_c(J) = 2·wind(F_B(ℝ), τ)` and the two-cluster
no-go run:

* `dampedChar_pos` — the characteristic polynomial `x² − 2ax + |τ|² = (x−a)² + b² > 0` has no
  real root (`b ≠ 0`): the operator is a genuine oscillator (§1).
* `fieldTerm_im` — `Im((z − β)⁻¹) = −Im z / ‖z − β‖²` for real `β` (§2a): the log-derivative
  imaginary-part identity that forces UHP-stability of `B = (D − τ̄)Â`.
* `field_im_eq` — summed: `Im Σ_k (z − β_k)⁻¹ = −Im z · Σ_k ‖z − β_k‖⁻²` (real `β_k`).
* `boundaryField_im_pos` — for real `x` and dressed zeros `ρ_j` with `Im ρ_j > 0`, the boundary
  field `F_B(x) = Σ_j (x − ρ_j)⁻¹` has `Im F_B(x) > 0` (§2b): the curve lives in the open UHP
  and closes through `0`, so its winding number is a nonnegative integer.
* `degenerate_disc_neg` — the **two-cluster no-go discriminant** (§4): for the fully degenerate
  cluster `Â = y^d`, the operator output's quadratic factor `|τ|²y² − 2ady + d(d−1)` has
  negative discriminant iff `d > 1 + a²/b²` (the (CPI) dip threshold).
-/
import Mathlib

noncomputable section

namespace RHTower

open Finset

/-- **The oscillator characteristic polynomial has no real root** (§1): `x² − 2ax + (a²+b²)
= (x−a)² + b² > 0` when `b ≠ 0`. The pair operator `(D−τ)(D−τ̄)`, `τ = a+bi`, is a genuine
damped oscillator, not a product of real first-order factors. -/
theorem dampedChar_pos {a b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    0 < x ^ (2 : ℕ) - 2 * a * x + (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  have : x ^ (2 : ℕ) - 2 * a * x + (a ^ (2 : ℕ) + b ^ (2 : ℕ)) = (x - a) ^ (2 : ℕ) + b ^ (2 : ℕ) := by ring
  rw [this]; positivity

/-- **Log-derivative imaginary part** (§2a): for a real pole `β`, `Im((z − β)⁻¹) =
−Im z / ‖z − β‖²`. Summed over a hyperbolic (real-rooted) section this gives
`Im(Â′/Â)(z) = −Im z·Σ‖z−β_k‖⁻²`, the sign that pins the zeros of `B = (D−τ̄)Â` into the UHP. -/
theorem fieldTerm_im (z : ℂ) (β : ℝ) :
    ((z - (β : ℂ))⁻¹).im = -z.im / Complex.normSq (z - (β : ℂ)) := by
  rw [Complex.inv_im]
  congr 1
  simp

/-- Summed log-derivative imaginary part for real poles `β_k`:
`Im Σ_k (z − β_k)⁻¹ = −Im z·Σ_k ‖z − β_k‖⁻²` (§2a). -/
theorem field_im_eq {ι : Type*} (z : ℂ) (β : ι → ℝ) (s : Finset ι) :
    (∑ k ∈ s, (z - (β k : ℂ))⁻¹).im
      = -z.im * ∑ k ∈ s, (Complex.normSq (z - (β k : ℂ)))⁻¹ := by
  rw [Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fieldTerm_im]
  ring

/-- **The boundary field lives in the open UHP** (§2b): for real `x` and dressed zeros `ρ_j`
with `Im ρ_j > 0` (each `≠ x`), the boundary field curve `F_B(x) = Σ_j (x − ρ_j)⁻¹` has
`Im F_B(x) > 0`. Hence the curve closes through `0` in the upper half-plane and its winding
number around `τ` is a nonnegative integer — the winding-count structure of `Z_c(J) = 2·wind`. -/
theorem boundaryField_im_pos {ι : Type*} (x : ℝ) (ρ : ι → ℂ) (s : Finset ι)
    (hne : s.Nonempty) (hpos : ∀ j ∈ s, 0 < (ρ j).im) (hx : ∀ j ∈ s, (x : ℂ) ≠ ρ j) :
    0 < (∑ j ∈ s, ((x : ℂ) - ρ j)⁻¹).im := by
  rw [Complex.im_sum]
  apply Finset.sum_pos _ hne
  intro j hj
  rw [Complex.inv_im]
  have hnz : (x : ℂ) - ρ j ≠ 0 := sub_ne_zero.mpr (hx j hj)
  have hns : 0 < Complex.normSq ((x : ℂ) - ρ j) := Complex.normSq_pos.mpr hnz
  have him : ((x : ℂ) - ρ j).im = -(ρ j).im := by simp
  rw [him, neg_neg]
  exact div_pos (hpos j hj) hns

/-- **The two-cluster no-go discriminant** (§4): for the fully degenerate cluster `Â = y^d`
(`d ≥ 1`), the operator output `y^{d−2}(|τ|²y² − 2ady + d(d−1))` has its quadratic factor with
NEGATIVE discriminant — one conjugate non-real pair — exactly when `d > 1 + a²/b²` (the (CPI)
dip threshold; `disc = 4d(a² + b² − b²d)`). -/
theorem degenerate_disc_neg {a b d : ℝ} (hb : b ≠ 0) (hd : 0 < d) :
    (2 * a * d) ^ (2 : ℕ) - 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) * (d * (d - 1)) < 0 ↔ 1 + a ^ (2 : ℕ) / b ^ (2 : ℕ) < d := by
  have hb2 : 0 < b ^ (2 : ℕ) := by positivity
  have key : (1 + a ^ (2 : ℕ) / b ^ (2 : ℕ) < d) ↔ (b ^ (2 : ℕ) + a ^ (2 : ℕ) < d * b ^ (2 : ℕ)) := by
    rw [show (1 : ℝ) + a ^ (2 : ℕ) / b ^ (2 : ℕ) = (b ^ (2 : ℕ) + a ^ (2 : ℕ)) / b ^ (2 : ℕ) from by field_simp,
      div_lt_iff₀ hb2]
  rw [key, show (2 * a * d) ^ (2 : ℕ) - 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) * (d * (d - 1))
      = 4 * d * (a ^ (2 : ℕ) + b ^ (2 : ℕ) - b ^ (2 : ℕ) * d) from by ring]
  constructor
  · intro h; nlinarith [hd, mul_pos hd hb2]
  · intro h; nlinarith [hd, mul_pos hd hb2]

end RHTower
