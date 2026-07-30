import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact interaction-picture amplitudes for the radial PSWF equation

Dunster's Liouville transform puts the exterior radial prolate equation in the form

`W'' + c^2 W = psi W`.

The useful oscillatory decomposition is not obtained by factoring a big-`O` remainder out of an
exponential.  It is an exact consequence of the differential equation.  This file defines the two
interaction-picture amplitudes and proves their reconstruction and first-order transport laws.
These identities are unconditional algebraic infrastructure; estimates on `psi` and the resulting
bounded variation are separate analytic inputs.
-/

namespace RHTower

noncomputable section

/-- The positive-frequency interaction amplitude for `W'' + c^2 W = psi W`. -/
def radialInteractionPlus (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) *
    (W x + V x / (Complex.I * (c : ℂ)))

/-- The negative-frequency interaction amplitude for `W'' + c^2 W = psi W`. -/
def radialInteractionMinus (c : ℝ) (W V : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
    (W x - V x / (Complex.I * (c : ℂ)))

/-- The interaction amplitudes reconstruct the original solution exactly. -/
theorem radialInteraction_reconstruct {c x : ℝ} (hc : c ≠ 0) (W V : ℝ → ℂ) :
    radialInteractionPlus c W V x *
        Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) +
      radialInteractionMinus c W V x *
        Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) = W x := by
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hpos : Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) *
      Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hneg : Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
      Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  rw [radialInteractionPlus, radialInteractionMinus]
  calc
    (1 / 2 : ℂ) * Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) *
          (W x + V x / (Complex.I * (c : ℂ))) *
          Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) +
        (1 / 2 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
          (W x - V x / (Complex.I * (c : ℂ))) *
          Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) =
        (1 / 2 : ℂ) *
            (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) *
              Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))) *
            (W x + V x / (Complex.I * (c : ℂ))) +
          (1 / 2 : ℂ) *
            (Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) *
              Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))) *
            (W x - V x / (Complex.I * (c : ℂ))) := by ring
    _ = W x := by rw [hpos, hneg]; ring

/-- Exact transport of the positive-frequency amplitude.  Here `V = W'` and
`V' = (psi - c^2) W`. -/
theorem hasDerivAt_radialInteractionPlus {c x : ℝ} (hc : c ≠ 0)
    {W V psi : ℝ → ℂ}
    (hW : HasDerivAt W (V x) x)
    (hV : HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x) :
    HasDerivAt (radialInteractionPlus c W V)
      (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
        (2 * Complex.I * (c : ℂ))) x := by
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hx : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x :=
    (hasDerivAt_id x).ofReal_comp
  have hphase : HasDerivAt
      (fun y : ℝ ↦ -Complex.I * (c : ℂ) * (y : ℂ))
      (-Complex.I * (c : ℂ)) x := by
    simpa using hx.const_mul (-Complex.I * (c : ℂ))
  have hexp := hphase.cexp
  have hsum := hW.add (hV.div_const (Complex.I * (c : ℂ)))
  have hprod := hexp.mul hsum
  have hfull := hprod.const_mul (1 / 2 : ℂ)
  have hfun : radialInteractionPlus c W V =
      fun y : ℝ => (1 / 2 : ℂ) *
        (Complex.exp (-Complex.I * (c : ℂ) * (y : ℂ)) *
          (W y + V y / (Complex.I * (c : ℂ)))) := by
    funext y
    simp only [radialInteractionPlus, mul_assoc]
  rw [hfun]
  apply hfull.congr_deriv
  simp only [Pi.add_apply]
  field_simp [hcℂ, Complex.I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact transport of the negative-frequency amplitude. -/
theorem hasDerivAt_radialInteractionMinus {c x : ℝ} (hc : c ≠ 0)
    {W V psi : ℝ → ℂ}
    (hW : HasDerivAt W (V x) x)
    (hV : HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x) :
    HasDerivAt (radialInteractionMinus c W V)
      (-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
        (2 * Complex.I * (c : ℂ))) x := by
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hx : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x :=
    (hasDerivAt_id x).ofReal_comp
  have hphase : HasDerivAt
      (fun y : ℝ ↦ Complex.I * (c : ℂ) * (y : ℂ))
      (Complex.I * (c : ℂ)) x := by
    simpa using hx.const_mul (Complex.I * (c : ℂ))
  have hexp := hphase.cexp
  have hdiff := hW.sub (hV.div_const (Complex.I * (c : ℂ)))
  have hprod := hexp.mul hdiff
  have hfull := hprod.const_mul (1 / 2 : ℂ)
  have hfun : radialInteractionMinus c W V =
      fun y : ℝ => (1 / 2 : ℂ) *
        (Complex.exp (Complex.I * (c : ℂ) * (y : ℂ)) *
          (W y - V y / (Complex.I * (c : ℂ)))) := by
    funext y
    simp only [radialInteractionMinus, mul_assoc]
  rw [hfun]
  apply hfull.congr_deriv
  simp only [Pi.sub_apply]
  field_simp [hcℂ, Complex.I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end RHTower
