import GaloisForLFunctions.HTGeometry.PiecewiseExponentialFourier

/-!
# The piecewise-exponential class is a graded algebra on a fixed partition

Two piecewise exponentials sharing a partition multiply within the class: the exponents add and the
coefficients multiply, while the partition is untouched.  Consequently every power of a piecewise
exponential is again one, with exponent scaled by the power and coefficients raised to it.

This is what makes a fixed number of iterations of a multiplication operator stay inside one decay
constant: no refinement of the partition ever occurs, so the piece count in
`norm_fourierCoeff_of_isExpPiecewise` does not grow.
-/

namespace GaloisForLFunctions

/-- Piecewise exponentials on a common partition multiply. -/
theorem IsExpPiecewise.mul {α β : ℝ} {n : ℕ} {t : ℕ → ℝ} {c d : ℕ → ℂ}
    {f g : AddCircle (1 : ℝ) → ℂ} (hf : IsExpPiecewise α n t c f)
    (hg : IsExpPiecewise β n t d g) :
    IsExpPiecewise (α + β) n t (fun i => c i * d i) (fun z => f z * g z) where
  base := hf.base
  top := hf.top
  mono := hf.mono
  nonneg := hf.nonneg
  le_one := hf.le_one
  eq := by
    intro i hi x hx
    rw [hf.eq i hi x hx, hg.eq i hi x hx]
    have hexp : Complex.exp ((α : ℂ) * (x : ℂ)) * Complex.exp ((β : ℂ) * (x : ℂ))
        = Complex.exp (((α + β : ℝ) : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc c i * Complex.exp ((α : ℂ) * (x : ℂ)) * (d i * Complex.exp ((β : ℂ) * (x : ℂ)))
        = c i * d i * (Complex.exp ((α : ℂ) * (x : ℂ)) * Complex.exp ((β : ℂ) * (x : ℂ))) := by
          ring
      _ = c i * d i * Complex.exp (((α + β : ℝ) : ℂ) * (x : ℂ)) := by rw [hexp]

/-- The zeroth power of a piecewise exponential: the constant function `1`, on the same
partition. -/
theorem IsExpPiecewise.one {α : ℝ} {n : ℕ} {t : ℕ → ℝ} {c : ℕ → ℂ}
    {f : AddCircle (1 : ℝ) → ℂ} (h : IsExpPiecewise α n t c f) :
    IsExpPiecewise 0 n t (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) where
  base := h.base
  top := h.top
  mono := h.mono
  nonneg := h.nonneg
  le_one := h.le_one
  eq := by
    intro i hi x hx
    simp

/-- Powers of a piecewise exponential stay in the class, with the exponent scaled by the power. -/
theorem IsExpPiecewise.pow {α : ℝ} {n : ℕ} {t : ℕ → ℝ} {c : ℕ → ℂ}
    {f : AddCircle (1 : ℝ) → ℂ} (h : IsExpPiecewise α n t c f) (r : ℕ) :
    IsExpPiecewise ((r : ℝ) * α) n t (fun i => c i ^ r) (fun z => f z ^ r) := by
  induction r with
  | zero => simpa using h.one
  | succ r ih =>
      have hmul := ih.mul h
      have hα : ((r : ℝ) * α + α) = ((r + 1 : ℕ) : ℝ) * α := by push_cast; ring
      have hc : (fun i => c i ^ r * c i) = fun i => c i ^ (r + 1) := by
        funext i
        rw [pow_succ]
      have hf : (fun z => f z ^ r * f z) = fun z => f z ^ (r + 1) := by
        funext z
        rw [pow_succ]
      rw [← hα, ← hc, ← hf]
      exact hmul

end GaloisForLFunctions
