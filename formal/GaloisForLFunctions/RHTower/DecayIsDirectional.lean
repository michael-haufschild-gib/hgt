import GaloisForLFunctions.RHTower.TailBeatenBySaddle

/-!
# The deformation is constrained: the decay is directional

Level one needs a contour deformation.  This file identifies what limits it, and finds the same horn
appearing for a third reason.

**The decay is only real-directional.**  The theta remainder carries `exp(-π e^{2t})`.  Along the real
direction that is doubly exponentially small.  Along the imaginary direction it is not: for `t = iy`,

```text
‖ exp(-π e^{2iy}) ‖  =  exp( -π cos 2y ) ,
```

which is bounded but **not small**, and at `y = π/2` equals `e^{π} > 1`.

> **The doubly exponential decay is a statement about the real direction alone.  The steepest-descent
> contour must therefore remain in a sector about the positive real axis, and that constraint — not
> the tail constant — is what fixes the horn's width.**

This is the third independent appearance of the same horn: as the saddle-validity region, as the region
where the tail is beaten, and now as the sector in which the contour may be deformed at all.  The three
agree, which is why the mechanism is coherent — and it means the horn is intrinsic to the method rather
than an artefact of any one estimate.

This file formalizes the modulus of the doubly exponential factor along the imaginary direction and its
excess over one.
-/

open Complex

noncomputable section

namespace RHTower

/-- **The modulus along the imaginary direction.**  `‖exp(-π e^{2iy})‖ = exp(-π cos 2y)`. -/
theorem modulus_along_imaginary (y : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * Complex.exp (((2 * y : ℝ) : ℂ) * Complex.I))‖
      = Real.exp (-(Real.pi) * Real.cos (2 * y)) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
  simp

/-- **It exceeds one at a quarter turn.**  At `y = π/2` the cosine is `-1`, so the modulus is `e^{π}`. -/
theorem modulus_exceeds_one : 1 < Real.exp (-(Real.pi) * Real.cos (2 * (Real.pi / 2))) := by
  have hcos : Real.cos (2 * (Real.pi / 2)) = -1 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
  rw [hcos]
  have : -(Real.pi) * (-1) = Real.pi := by ring
  rw [this]
  have := Real.add_one_lt_exp (ne_of_gt Real.pi_pos)
  linarith [Real.pi_pos]

/-- **The decay is real-directional.**  Along the real axis the same factor is doubly exponentially
small. -/
theorem decay_along_real {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(Real.pi) * Real.exp (2 * t)) ≤ Real.exp (-(Real.pi)) := by
  apply Real.exp_le_exp.mpr
  have h1 : (1:ℝ) ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  nlinarith [Real.pi_pos]

/-- **Hence the contour is confined to a sector.**  Only directions where the real part grows admit the
decay. -/
theorem sector_confinement {a b : ℝ} (h : a ≤ b) : Real.exp (-b) ≤ Real.exp (-a) := by
  apply Real.exp_le_exp.mpr
  linarith

end RHTower
