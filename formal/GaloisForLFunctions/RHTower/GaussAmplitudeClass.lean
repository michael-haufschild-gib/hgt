import GaloisForLFunctions.RHTower.GaussMovingAmplitudeOperator
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

/-! ## The moving amplitude is piecewise constant -/

theorem gaussPrimeScaleInvSqCircle_coe {p x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    gaussPrimeScaleInvSqCircle p ((x : ℝ) : AddCircle (1 : ℝ))
      = (gaussPrimeScaleInvSq p x : ℂ) :=
  AddCircle.liftIoc_coe_apply (by simpa using hx)

/-- On the first piece the moving amplitude is the constant `p^s`. -/
theorem gaussMovingAmplitudeCircle_of_lt {p : ℝ} {s x : ℝ}
    (hs0 : 0 ≤ s) (hx0 : 0 < x) (hx : x + s ≤ 1) :
    gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)) ((x : ℝ) : AddCircle (1 : ℝ))
      = ((Real.exp (s * Real.log p) : ℝ) : ℂ) := by
  have hx1 : x ≤ 1 := by linarith
  have hxs : (0 : ℝ) < x + s := by linarith
  have hcoe : ((x : ℝ) : AddCircle (1 : ℝ)) + ((s : ℝ) : AddCircle (1 : ℝ))
      = ((x + s : ℝ) : AddCircle (1 : ℝ)) := rfl
  rw [gaussMovingAmplitudeCircle, hcoe, gaussPrimeScaleCircle_coe ⟨hx0, hx1⟩,
    gaussPrimeScaleInvSqCircle_coe ⟨hxs, hx⟩, gaussPrimeScale, gaussPrimeScaleInvSq]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- After the wrap the moving amplitude is the constant `p^(s-1)`. -/
theorem gaussMovingAmplitudeCircle_of_ge {p : ℝ} {s x : ℝ}
    (hs1 : s < 1) (hx0 : 0 < x) (hx1 : x ≤ 1) (hx : 1 < x + s) :
    gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)) ((x : ℝ) : AddCircle (1 : ℝ))
      = ((Real.exp ((s - 1) * Real.log p) : ℝ) : ℂ) := by
  have hxs0 : (0 : ℝ) < x + s - 1 := by linarith
  have hxs1 : x + s - 1 ≤ 1 := by linarith
  have hcoe : ((x : ℝ) : AddCircle (1 : ℝ)) + ((s : ℝ) : AddCircle (1 : ℝ))
      = ((x + s - 1 : ℝ) : AddCircle (1 : ℝ)) := by
    have hper : ((x + s - 1 + 1 : ℝ) : AddCircle (1 : ℝ))
        = ((x + s - 1 : ℝ) : AddCircle (1 : ℝ)) := AddCircle.coe_add_period 1 _
    rw [← hper, show (x + s - 1 + 1 : ℝ) = x + s from by ring]
    rfl
  rw [gaussMovingAmplitudeCircle, hcoe, gaussPrimeScaleCircle_coe ⟨hx0, hx1⟩,
    gaussPrimeScaleInvSqCircle_coe ⟨hxs0, hxs1⟩, gaussPrimeScale, gaussPrimeScaleInvSq]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- **The moving amplitude is a two-piece constant.** -/
theorem isExpPiecewise_gaussMovingAmplitudeCircle {p : ℝ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IsExpPiecewise 0 2 (fun i => if i = 0 then 0 else if i = 1 then 1 - s else 1)
      (fun i => if i = 0 then ((Real.exp (s * Real.log p) : ℝ) : ℂ)
        else ((Real.exp ((s - 1) * Real.log p) : ℝ) : ℂ))
      (gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ))) where
  base := by norm_num
  top := by norm_num
  mono := by
    intro i hi
    interval_cases i <;> (norm_num; try linarith)
  nonneg := by
    intro i hi
    interval_cases i <;> (norm_num; try linarith)
  le_one := by
    intro i hi
    interval_cases i <;> (norm_num; try linarith)
  eq := by
    intro i hi x hx
    interval_cases i
    · have hx0 : 0 < x := by simpa using hx.1
      have hxr : x < 1 - s := by simpa using hx.2
      have hxs : x + s ≤ 1 := by linarith
      rw [gaussMovingAmplitudeCircle_of_lt hs0 hx0 hxs]
      norm_num
    · have hxl : 1 - s < x := by simpa using hx.1
      have hxr : x < 1 := by simpa using hx.2
      have hx0 : 0 < x := by linarith
      have hxs : 1 < x + s := by linarith
      rw [gaussMovingAmplitudeCircle_of_ge hs1 hx0 hxr.le hxs]
      norm_num

end

end RHTower
