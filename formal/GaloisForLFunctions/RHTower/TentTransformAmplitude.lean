import Mathlib

/-!
# The tent transform is the squared screw amplitude

The rectangular two-edge autocorrelation is built from tents `v ↦ max(0, L − |v|)`.  Its exponential
transform is

```text
∫_{−L}^{L} (L − |v|) e^{s v} dv  =  2(cosh(sL) − 1)/s²  =  4·(sinh(sL/2)/s)² .
```

The right-hand side is exactly four times the square of `sinh(sL/2)/s` — the amplitude appearing in
the sum-of-squares factorization of the rectangular Weil carrier, where the carrier is
`16 ∑_ρ (sinh(Lw/2)·cosh((x−L)w/2)/w)²` with `w` the spectral variable.

So the two descriptions of the same window are transform duals of one another: the tent picture on
the prime side and the squared-amplitude picture on the zero side carry the same function, read in
the two conjugate variables.  That the amplitude enters *squared* on the zero side is the transform
image of the fact that the tent is an **autocorrelation** — a self-convolution — on the prime side.

The identity is proved by the fundamental theorem of calculus with the explicit antiderivative
`v ↦ (L−v)·sinh(sv)/s + cosh(sv)/s²`.
-/

open intervalIntegral

namespace RHTower

/-- The antiderivative of `v ↦ (L − v)·cosh(s v)`. -/
noncomputable def tentPrimitive (L s v : ℝ) : ℝ :=
  (L - v) * Real.sinh (s * v) / s + Real.cosh (s * v) / s ^ (2 : ℕ)

theorem hasDerivAt_tentPrimitive {s : ℝ} (hs : s ≠ 0) (L v : ℝ) :
    HasDerivAt (tentPrimitive L s) ((L - v) * Real.cosh (s * v)) v := by
  have hsv : HasDerivAt (fun v : ℝ => s * v) s v := by
    simpa using (hasDerivAt_id v).const_mul s
  have hsinh : HasDerivAt (fun v : ℝ => Real.sinh (s * v)) (Real.cosh (s * v) * s) v :=
    (Real.hasDerivAt_sinh (s * v)).comp v hsv
  have hcosh : HasDerivAt (fun v : ℝ => Real.cosh (s * v)) (Real.sinh (s * v) * s) v :=
    (Real.hasDerivAt_cosh (s * v)).comp v hsv
  have hlin : HasDerivAt (fun v : ℝ => L - v) (-1) v := by
    have hsub := (hasDerivAt_const v L).sub (hasDerivAt_id v)
    rw [show ((fun _ : ℝ => L) - id) = (fun y : ℝ => L - y) by
      funext y
      rfl] at hsub
    simpa only [zero_sub] using! hsub
  have h1 : HasDerivAt (fun v : ℝ => (L - v) * Real.sinh (s * v) / s)
      ((-1 * Real.sinh (s * v) + (L - v) * (Real.cosh (s * v) * s)) / s) v :=
    (hlin.mul hsinh).div_const s
  have h2 : HasDerivAt (fun v : ℝ => Real.cosh (s * v) / s ^ (2 : ℕ))
      (Real.sinh (s * v) * s / s ^ (2 : ℕ)) v := hcosh.div_const (s ^ (2 : ℕ))
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  field_simp
  ring

/-- **The tent transform.**  For `s ≠ 0`, `∫₀^L (L − v)·cosh(s v) dv = (cosh(sL) − 1)/s²`. -/
theorem integral_tent_cosh {s : ℝ} (hs : s ≠ 0) (L : ℝ) :
    (∫ v in (0 : ℝ)..L, (L - v) * Real.cosh (s * v)) = (Real.cosh (s * L) - 1) / s ^ (2 : ℕ) := by
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_tentPrimitive hs L v)]
  · unfold tentPrimitive
    simp
    field_simp
  · apply Continuous.intervalIntegrable
    fun_prop

/-- **The symmetric tent transform, in squared-amplitude form.**  The full two-sided integral is
four times the square of `sinh(sL/2)/s`. -/
theorem integral_tent_symmetric {s : ℝ} (hs : s ≠ 0) (L : ℝ) :
    2 * (∫ v in (0 : ℝ)..L, (L - v) * Real.cosh (s * v))
      = 4 * (Real.sinh (s * L / 2) / s) ^ (2 : ℕ) := by
  rw [integral_tent_cosh hs L]
  have hhalf : Real.cosh (s * L) = 2 * Real.sinh (s * L / 2) ^ (2 : ℕ) + 1 := by
    have h := Real.cosh_two_mul (s * L / 2)
    have h2 : 2 * (s * L / 2) = s * L := by ring
    rw [h2] at h
    have hpy := Real.cosh_sq_sub_sinh_sq (s * L / 2)
    linarith
  rw [hhalf]
  field_simp
  ring

/-- **Duality statement.**  Writing `A(s) = sinh(sL/2)/s` for the screw amplitude at spectral
variable `s`, the symmetric tent transform is `4·A(s)²`.  The prime-side tent and the zero-side
squared amplitude are therefore the same object in conjugate variables, and the square on the zero
side is the transform image of the tent being a self-convolution. -/
theorem tent_transform_eq_four_mul_amplitude_sq {s : ℝ} (hs : s ≠ 0) (L : ℝ) :
    2 * (∫ v in (0 : ℝ)..L, (L - v) * Real.cosh (s * v))
      = 4 * (Real.sinh (s * L / 2) / s) ^ (2 : ℕ) :=
  integral_tent_symmetric hs L

end RHTower
