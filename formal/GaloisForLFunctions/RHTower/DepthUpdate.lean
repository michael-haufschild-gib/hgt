/-
Tier (T2) first bricks (doc 53 §5): the per-entry depth update.

* `quadratic_pair_zeros_pos` / `quadratic_pair_zeros_nonpos` — the zeros of
  v² + D are EXACTLY ±i√D (D > 0: off-line conjugate pair of depth √D) or
  ±√(−D) (D ≤ 0: on-line pair — absorption). No approximation.
* `depth_update_exact` — hence in the constant-perturbation model the walk
  update η² ← η² + ε·q₀ of doc 49 §1 is the literal motion of the zeros:
  survive ⟺ 0 < η² + εq₀ with the new depth √(η² + εq₀), absorb ⟺ ≤ 0 with
  the landing points ±√(−(η² + εq₀)) on the line.
* `pair_depth_eq_center_over_cofactor` — the deviation interface for varying
  q (doc 46 §6): in the factored form Z(v) = (v² + d)·h(v), the depth-squared
  reads off the center: d = Z(0)/h(0). The remaining (T2) content is exactly
  the EXISTENCE of the factored form with h(0) controlled — the Rouché/IFT
  hypothesis, named here and consumed nowhere silently.
-/
import Mathlib

namespace RHTower

/-- Zeros of v² + D for D > 0: exactly the conjugate pair ±i√D. -/
theorem quadratic_pair_zeros_pos {D : ℝ} (hD : 0 < D) (v : ℂ) :
    v ^ 2 + (D : ℂ) = 0
      ↔ v = Complex.I * ((Real.sqrt D : ℝ) : ℂ)
        ∨ v = -(Complex.I * ((Real.sqrt D : ℝ) : ℂ)) := by
  set s : ℂ := ((Real.sqrt D : ℝ) : ℂ) with hs
  have hsq : s ^ 2 = (D : ℂ) := by
    rw [hs, ← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hfac : v ^ 2 + (D : ℂ)
      = (v - Complex.I * s) * (v + Complex.I * s) := by
    have : (v - Complex.I * s) * (v + Complex.I * s)
        = v ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
    rw [this, Complex.I_sq, hsq]
    ring
  rw [hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Zeros of v² + D for D ≤ 0: exactly the real (on-line) pair ±√(−D). -/
theorem quadratic_pair_zeros_nonpos {D : ℝ} (hD : D ≤ 0) (v : ℂ) :
    v ^ 2 + (D : ℂ) = 0
      ↔ v = ((Real.sqrt (-D) : ℝ) : ℂ) ∨ v = -((Real.sqrt (-D) : ℝ) : ℂ) := by
  set s : ℂ := ((Real.sqrt (-D) : ℝ) : ℂ) with hs
  have hsq : s ^ 2 = ((-D : ℝ) : ℂ) := by
    rw [hs, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
  have hfac : v ^ 2 + (D : ℂ) = (v - s) * (v + s) := by
    have h1 : (v - s) * (v + s) = v ^ 2 - s ^ 2 := by ring
    rw [h1, hsq]
    push_cast
    ring
  rw [hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- **The exact depth update ((T2), constant model)**: after one entry of
push ε·q₀, the surviving pair sits exactly at ±i√(η² + εq₀) — the cascade
walk of doc 49 §1 is the literal zero motion. -/
theorem depth_update_exact {η ε q₀ : ℝ} (h : 0 < η ^ 2 + ε * q₀) (v : ℂ) :
    v ^ 2 + ((η ^ 2 + ε * q₀ : ℝ) : ℂ) = 0
      ↔ v = Complex.I * ((Real.sqrt (η ^ 2 + ε * q₀) : ℝ) : ℂ)
        ∨ v = -(Complex.I * ((Real.sqrt (η ^ 2 + ε * q₀) : ℝ) : ℂ)) :=
  quadratic_pair_zeros_pos h v

/-- **The exact absorption ((T2), constant model)**: with the push past the
barrier the zeros land ON the line at ±√(−(η² + εq₀)). -/
theorem depth_absorb_exact {η ε q₀ : ℝ} (h : η ^ 2 + ε * q₀ ≤ 0) (v : ℂ) :
    v ^ 2 + ((η ^ 2 + ε * q₀ : ℝ) : ℂ) = 0
      ↔ v = ((Real.sqrt (-(η ^ 2 + ε * q₀)) : ℝ) : ℂ)
        ∨ v = -((Real.sqrt (-(η ^ 2 + ε * q₀)) : ℝ) : ℂ) :=
  quadratic_pair_zeros_nonpos h v

/-- **Center-over-cofactor ((T2) deviation interface, doc 46 §6)**: in the
factored form Z(v) = (v² + d)·h(v) the depth-squared reads off the center
value: d = Z(0)/h(0). The existence of the factored form with h(0)
controlled is the named Rouché/IFT residual of tier (T2). -/
theorem pair_depth_eq_center_over_cofactor {Z h : ℂ → ℂ} {d : ℂ}
    (hfac : ∀ v, Z v = (v ^ 2 + d) * h v) (hh : h 0 ≠ 0) :
    d = Z 0 / h 0 := by
  have h0 := hfac 0
  rw [eq_div_iff hh]
  simpa using h0.symm

/-- The walk-facing corollary: if the center value and cofactor are real and
the ratio positive, the factored carrier's pair depth is exactly
√(Z(0)/h(0)) — the exact bridge from carrier data to the cascade depth. -/
theorem pair_depth_real {Z h : ℂ → ℂ} {dr : ℝ}
    (hfac : ∀ v, Z v = (v ^ 2 + (dr : ℂ)) * h v)
    (hpos : 0 < dr) (v : ℂ) :
    Z v = 0 ↔ v = Complex.I * ((Real.sqrt dr : ℝ) : ℂ)
        ∨ v = -(Complex.I * ((Real.sqrt dr : ℝ) : ℂ)) ∨ h v = 0 := by
  rw [hfac v, mul_eq_zero]
  rw [quadratic_pair_zeros_pos hpos v]
  tauto

end RHTower
