/-
# The quartic defect `F = θ₃⁴ − θ₂⁴ − θ₄⁴` and its modular structure

The Jacobi quartic identity `θ₃⁴ = θ₂⁴ + θ₄⁴` — equivalently `F ≡ 0` — is the one theta-side input
that turns the already-proved "`λ` omits `0` on all of `ℍ`" (`modularLambda_ne_zero_of_im_pos`) into
"`λ` omits `1`", via `modularLambda_S : λ(−1/τ) = (θ₄/θ₃)⁴ = 1 − λ(τ)` once `F ≡ 0`.

This file makes `F` precise as a holomorphic **weight-2 modular object** for `Γ(2)`:
* `quarticDefect_add_one : F(τ+1) = −F(τ)` (the `T`-law),
* `quarticDefect_S : F(−1/τ) = −τ²·F(τ)` (the `S`-law) — both derived purely from the theta `S`/`T`
  transformation laws (`thetaThree_S`, …, `thetaTwo_add_one`),
* `hasDerivAt_quarticDefect` — `F′ = 4θ₃³θ₃′ − 4θ₂³θ₂′ − 4θ₄³θ₄′` from the nullwert derivatives.

What remains to conclude `F ≡ 0`: `F` is holomorphic on `ℍ`, weight-2 with the two laws above, and
vanishes at the cusps (`θ₃,θ₄ → 1`, `θ₂ → 0` at `i∞`); a weight-2 `Γ(2)` cusp form is `0`
(`dim S₂(Γ(2)) = 0`, genus-0). That finiteness step needs the compactified modular curve `X(Γ(2))` /
the `Γ(2)` valence formula, absent from mathlib (only the level-one formula exists). Everything feeding
it is now built and axiom-clean.

Consumes `ThetaNullwert` (hence `ThetaHeat` + `ModularLambda`). Mathlib only otherwise.
-/
import GaloisForLFunctions.Bottcher.ThetaNullwert
open Complex
open scoped Real
namespace Bottcher

/-- The **quartic defect** `F(τ) = θ₃⁴ − θ₂⁴ − θ₄⁴`. The Jacobi quartic identity is exactly `F ≡ 0`. -/
noncomputable def quarticDefect (τ : ℂ) : ℂ :=
  thetaThree τ ^ (4 : ℕ) - thetaTwo τ ^ (4 : ℕ) - thetaFour τ ^ (4 : ℕ)

/-- Helper: `(w^(1/2))⁴ = w²` for `w ≠ 0`. -/
private theorem cpow_half_pow_four {w : ℂ} (hw : w ≠ 0) : (w ^ (1/2 : ℂ)) ^ (4 : ℕ) = w ^ (2 : ℕ) := by
  have hsq : (w ^ (1/2 : ℂ)) ^ (2 : ℕ) = w := by
    rw [pow_two, ← Complex.cpow_add _ _ hw, show (1/2 : ℂ) + 1/2 = 1 by norm_num, Complex.cpow_one]
  calc (w ^ (1/2 : ℂ)) ^ (4 : ℕ) = ((w ^ (1/2 : ℂ)) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ = w ^ (2 : ℕ) := by rw [hsq]

/-- **`F(τ+1) = −F(τ)`** — the `T`-transformation of the quartic defect (weight-2 with a sign).
From `θ₃(τ+1)=θ₄`, `θ₄(τ+1)=θ₃`, `θ₂(τ+1)=exp(πi/4)θ₂` (so `θ₂(τ+1)⁴ = −θ₂⁴`). -/
theorem quarticDefect_add_one (τ : ℂ) : quarticDefect (τ + 1) = -quarticDefect τ := by
  unfold quarticDefect
  rw [thetaThree_add_one, thetaFour_add_one, thetaTwo_add_one]
  have hexp : (Complex.exp ((Real.pi : ℂ) * I / 4)) ^ (4 : ℕ) = -1 := by
    rw [← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * I / 4) = (Real.pi : ℂ) * I by
      push_cast; ring]
    exact Complex.exp_pi_mul_I
  rw [mul_pow, hexp]
  ring

/-- **`F(−1/τ) = −τ²·F(τ)`** — the `S`-transformation (weight-2). From the theta `S`-laws: each
nullwert's 4th power picks up `(−Iτ)² = −τ²` (resp. `(I/τ)⁻² = −τ²`), and `θ₂ ↔ θ₄` swap. -/
theorem quarticDefect_S {τ : ℂ} (hτ : 0 < im τ) :
    quarticDefect (-1/τ) = -τ ^ (2 : ℕ) * quarticDefect τ := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hIτ : I / τ ≠ 0 := div_ne_zero Complex.I_ne_zero hτ0
  have hmIτ : -I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0
  have e1 : (-I * τ) ^ (2 : ℕ) = -τ ^ (2 : ℕ) := by rw [mul_pow, neg_sq, Complex.I_sq]; ring
  have e2 : (1 : ℂ) / (I / τ) ^ (2 : ℕ) = -τ ^ (2 : ℕ) := by
    rw [div_pow, Complex.I_sq]; field_simp
  have h3 : thetaThree (-1/τ) ^ (4 : ℕ) = -τ ^ (2 : ℕ) * thetaThree τ ^ (4 : ℕ) := by
    rw [thetaThree_S τ hτ0, mul_pow, cpow_half_pow_four hmIτ, e1]
  have h2 : thetaTwo (-1/τ) ^ (4 : ℕ) = -τ ^ (2 : ℕ) * thetaFour τ ^ (4 : ℕ) := by
    rw [thetaTwo_S τ hτ0, mul_pow, div_pow, one_pow, cpow_half_pow_four hIτ, e2]
  have h4 : thetaFour (-1/τ) ^ (4 : ℕ) = -τ ^ (2 : ℕ) * thetaTwo τ ^ (4 : ℕ) := by
    rw [thetaFour_S τ hτ0, mul_pow, div_pow, one_pow, cpow_half_pow_four hIτ, e2]
  unfold quarticDefect
  rw [h3, h2, h4]; ring

/-- **The derivative of the quartic defect** `F′ = 4θ₃³θ₃′ − 4θ₂³θ₂′ − 4θ₄³θ₄′`, assembled from the
nullwert τ-derivatives (`ThetaNullwert`). With `quarticDefect_add_one`/`_S` this exhibits `F` as a
holomorphic weight-2 modular object whose vanishing `F ≡ 0` is the Jacobi quartic identity; the one
remaining input is the Γ(2) cusp-form finiteness (modular-curve compactness / valence), absent from
mathlib. -/
theorem hasDerivAt_quarticDefect {τ : ℂ} (hτ : 0 < im τ) :
    HasDerivAt quarticDefect
      (4 * thetaThree τ ^ (3 : ℕ) * deriv thetaThree τ - 4 * thetaTwo τ ^ (3 : ℕ) * deriv thetaTwo τ
        - 4 * thetaFour τ ^ (3 : ℕ) * deriv thetaFour τ) τ := by
  unfold quarticDefect
  have d3 := (hasDerivAt_thetaThree hτ).pow 4
  have d2 := (hasDerivAt_thetaTwo hτ).pow 4
  have d4 := (hasDerivAt_thetaFour hτ).pow 4
  apply ((d3.sub d2).sub d4).congr_deriv
  rw [(hasDerivAt_thetaThree hτ).deriv, (hasDerivAt_thetaTwo hτ).deriv,
    (hasDerivAt_thetaFour hτ).deriv]
  push_cast; ring

end Bottcher
