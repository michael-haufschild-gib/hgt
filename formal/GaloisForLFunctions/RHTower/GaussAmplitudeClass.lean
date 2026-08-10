import GaloisForLFunctions.RHTower.GaussQuasiInnerBlocks
import GaloisForLFunctions.HTGeometry.PiecewiseExponentialFourier

/-!
# The prime scale as a piecewise exponential

The prime-scale amplitude and its reciprocal square are single-piece exponentials on the period:

`b_p(x) = √p · e^{-(log p/2)x)`,   `b_p(x)^{-2} = p^{-1} · e^{(log p)x}`.

Multiplying an amplitude by either of them therefore keeps the partition and the number of pieces,
shifts the exponent by `∓ log p / 2` respectively `+ log p`, and rescales the coefficients by a
factor of modulus `√p` respectively `1/p`.  So the decay constant of
`norm_fourierCoeff_of_isExpPiecewise` changes by an explicit factor and, in particular, never
depends on where the breakpoints are.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions

noncomputable section

theorem gaussPrimeScale_eq_expPiece {p : ℝ} (hp : 0 < p) (x : ℝ) :
    (gaussPrimeScale p x : ℂ)
      = (Real.sqrt p : ℂ) * Complex.exp ((-(Real.log p / 2) : ℝ) * (x : ℂ)) := by
  have hs : (Real.sqrt p : ℂ) = ((Real.exp (Real.log p / 2) : ℝ) : ℂ) := by
    rw [GaloisForLFunctions.RHTower.exp_log_div_two p hp]
  have hcast : ((-(Real.log p / 2) : ℝ) : ℂ) * (x : ℂ)
      = ((-(Real.log p / 2) * x : ℝ) : ℂ) := by push_cast; ring
  rw [hs, hcast, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add, gaussPrimeScale]
  congr 2
  ring

theorem gaussPrimeScaleInvSq_eq_expPiece {p : ℝ} (hp : 0 < p) (x : ℝ) :
    (gaussPrimeScaleInvSq p x : ℂ)
      = ((p⁻¹ : ℝ) : ℂ) * Complex.exp ((Real.log p : ℝ) * (x : ℂ)) := by
  have hlog : Real.exp (-Real.log p) = p⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hp]
  have hcast : ((Real.log p : ℝ) : ℂ) * (x : ℂ) = ((Real.log p * x : ℝ) : ℂ) := by
    push_cast; ring
  rw [← hlog, hcast, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add,
    gaussPrimeScaleInvSq]
  congr 2
  ring

/-! ## Closure under the two multiplications -/

theorem IsExpPiecewise.mul_gaussPrimeScale {p : ℝ} (hp : 0 < p) {α : ℝ} {n : ℕ}
    {t : ℕ → ℝ} {c : ℕ → ℂ} {f : AddCircle (1 : ℝ) → ℂ}
    (h : IsExpPiecewise α n t c f) :
    IsExpPiecewise (α - Real.log p / 2) n t (fun i => (Real.sqrt p : ℂ) * c i)
      (fun z => gaussPrimeScaleCircle p z * f z) where
  base := h.base
  top := h.top
  mono := h.mono
  nonneg := h.nonneg
  le_one := h.le_one
  eq := by
    intro i hi x hx
    have hx0 : 0 < x := lt_of_le_of_lt (h.nonneg i hi) hx.1
    have hx1 : x ≤ 1 := le_trans hx.2.le (h.le_one i hi)
    have hval : gaussPrimeScaleCircle p ((x : ℝ) : AddCircle (1 : ℝ))
        = (gaussPrimeScale p x : ℂ) := gaussPrimeScaleCircle_coe ⟨hx0, hx1⟩
    have hmul : Complex.exp (((-(Real.log p / 2) : ℝ) : ℂ) * (x : ℂ)) *
        Complex.exp ((α : ℂ) * (x : ℂ))
        = Complex.exp (((α - Real.log p / 2 : ℝ) : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hval, h.eq i hi x hx, gaussPrimeScale_eq_expPiece hp,
      show (Real.sqrt p : ℂ) * Complex.exp (((-(Real.log p / 2) : ℝ) : ℂ) * (x : ℂ)) *
          (c i * Complex.exp ((α : ℂ) * (x : ℂ)))
          = (Real.sqrt p : ℂ) * c i *
            (Complex.exp (((-(Real.log p / 2) : ℝ) : ℂ) * (x : ℂ)) *
              Complex.exp ((α : ℂ) * (x : ℂ))) from by ring, hmul]

theorem IsExpPiecewise.mul_gaussPrimeScaleInvSq {p : ℝ} (hp : 0 < p) {α : ℝ} {n : ℕ}
    {t : ℕ → ℝ} {c : ℕ → ℂ} {f : AddCircle (1 : ℝ) → ℂ}
    (h : IsExpPiecewise α n t c f) :
    IsExpPiecewise (α + Real.log p) n t (fun i => ((p⁻¹ : ℝ) : ℂ) * c i)
      (fun z => gaussPrimeScaleInvSqCircle p z * f z) where
  base := h.base
  top := h.top
  mono := h.mono
  nonneg := h.nonneg
  le_one := h.le_one
  eq := by
    intro i hi x hx
    have hx0 : 0 < x := lt_of_le_of_lt (h.nonneg i hi) hx.1
    have hx1 : x ≤ 1 := le_trans hx.2.le (h.le_one i hi)
    have hval : gaussPrimeScaleInvSqCircle p ((x : ℝ) : AddCircle (1 : ℝ))
        = (gaussPrimeScaleInvSq p x : ℂ) :=
      AddCircle.liftIoc_coe_apply (by simpa using ⟨hx0, hx1⟩)
    have hmul : Complex.exp (((Real.log p : ℝ) : ℂ) * (x : ℂ)) *
        Complex.exp ((α : ℂ) * (x : ℂ))
        = Complex.exp (((α + Real.log p : ℝ) : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hval, h.eq i hi x hx, gaussPrimeScaleInvSq_eq_expPiece hp,
      show ((p⁻¹ : ℝ) : ℂ) * Complex.exp (((Real.log p : ℝ) : ℂ) * (x : ℂ)) *
          (c i * Complex.exp ((α : ℂ) * (x : ℂ)))
          = ((p⁻¹ : ℝ) : ℂ) * c i *
            (Complex.exp (((Real.log p : ℝ) : ℂ) * (x : ℂ)) *
              Complex.exp ((α : ℂ) * (x : ℂ))) from by ring, hmul]

end

end RHTower
