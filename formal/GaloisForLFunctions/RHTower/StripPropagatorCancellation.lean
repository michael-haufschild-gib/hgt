import GaloisForLFunctions.RHTower.StripPropagatorLineDecay
import GaloisForLFunctions.RHTower.SuzukiStripTransportUniform

/-!
# Propagating the boundary term of the integration by parts

The propagator and its inverse cancel in both orders, so pushing the first boundary term of the
two-fold integration by parts back through `H` leaves nothing but the resolvent against the physical
phase:

`H(x+iσ) · e^{-ixL} H(x+iσ)^{-1} S w = e^{-ixL} S w`.

That is why the card's `(20)` is a pure resolvent average and carries no propagator factor at all —
the transport cancels exactly, and the frequency behaviour of the boundary term is governed by the
resolvent alone.

The branch never vanishes on the shifted line, because its square is the Gamma quotient and the
quotient is strictly positive there.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The shifted-line point is nonzero. -/
theorem shift_ne_zero {σ : ℝ} (hσ0 : 0 < σ) (x : ℝ) :
    ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := by
  intro hcon
  have him := congrArg Complex.im hcon
  simp at him
  linarith

/-- The branch does not vanish on the shifted line. -/
theorem branch_ne_zero (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    E ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := by
  set z : ℂ := (x : ℂ) + (σ : ℂ) * Complex.I with hz
  have hzim : z.im = σ := by rw [hz]; simp
  have hzre : z.re = x := by rw [hz]; simp
  have hstrip : z ∈ imStrip (-1) 1 := by
    constructor <;> rw [hzim] <;> linarith
  intro hcon
  have hsq : gammaRatio z = 0 := by
    rw [← hE z hstrip, hcon]
    ring
  have hpos : 0 < gammaRatioPair (z.im, z.re) := by
    refine gammaRatioPair_pos (σ₁ := σ) hσ1 ?_
    rw [hzim]
    exact ⟨hσ0.le, le_rfl⟩
  have hnorm : ‖gammaRatio z‖ = gammaRatioPair (z.im, z.re) := norm_gammaRatio_eq_pair z
  rw [hsq, norm_zero] at hnorm
  linarith

omit [Nontrivial X] in
/-- **The propagator inverts its inverse.** -/
theorem stripPropagator_stripPropagatorInv {z : ℂ} (hz : z ≠ 0) (hEz : E z ≠ 0) (v : X) :
    stripPropagator E T z (stripPropagatorInv E T z v) = v := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  set a : ℂ := z ^ (-(1 : ℂ) / 2)
      * (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z) with hadef
  have hane : a ≠ 0 := by
    rw [hadef]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hz))
      (mul_ne_zero (Complex.exp_ne_zero _) hEz)
  have hcomm : Commute ((-(Complex.I / 2) * z) • T) (((Complex.I / 2) * z) • T) := by
    have h : ((-(Complex.I / 2) * z) • T) = -(((Complex.I / 2) * z) • T) := by
      rw [← neg_smul]
      congr 1
      ring
    rw [h]
    exact (Commute.refl _).neg_left
  have hprod : NormedSpace.exp ((-(Complex.I / 2) * z) • T)
      * NormedSpace.exp (((Complex.I / 2) * z) • T) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hcomm, ← add_smul,
      show (-(Complex.I / 2) * z) + (Complex.I / 2) * z = 0 by ring, zero_smul,
      NormedSpace.exp_zero]
  have hstep : stripPropagatorInv E T z v = a⁻¹ • NormedSpace.exp (((Complex.I / 2) * z) • T) v := by
    rw [stripPropagatorInv, smul_apply, hadef]
  rw [hstep, stripPropagator, smul_apply, stripTransport_apply,
    map_smul, smul_smul, smul_smul, ← hadef, mul_inv_cancel₀ hane, one_smul]
  exact congrFun (congrArg (fun S : X →L[ℂ] X => (S : X → X)) hprod) v

omit [Nontrivial X] in
/-- **`(20)`: the transport cancels in the boundary term.** -/
theorem stripPropagator_phase_inv (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) (c : ℂ) (w : X) :
    stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (c • stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I) w)
      = c • w := by
  rw [map_smul, stripPropagator_stripPropagatorInv (shift_ne_zero hσ0 x)
    (branch_ne_zero hE hσ0 hσ1 x)]

end GaloisForLFunctions.RHTower
