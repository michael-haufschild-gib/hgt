import GaloisForLFunctions.RHTower.CCMUnitRieszWaveletFrontier

/-!
# The unit-Riesz Markov–virial factorization and the Landau connector

Five exact mechanisms of the card are formalized.

*The wavelet kernel.*  `K_T(u) = w(T−u) − u d(T−u)` is exactly the derivative of `Φ_T(u) = u w(T−u)`
— equation `(9)`.

*The convolution split.*  Hence the coefficient splits as `(h ⋆ w)(T) − ((t h) ⋆ d)(T)`, the first
step of `(11)`.

*The polar part of the virial.*  `∫_0^t e^{-u}du − t e^{-t} = 1 − (1+t)e^{-t}` exactly, which is the
explicit boundary correction in `(13)`.

*The Landau nonnegativity shift.*  `I(T) ≥ −C e^{cT}` is exactly nonnegativity of
`b(T) = I(T) + C e^{cT}` — equations `(18)`, `(20)`.

*The exponent bookkeeping.*  For `0 < ε < δ + 1/2` the shift exponent `c = −1/2 + ε` is strictly
below `δ`, which is what puts the added pole strictly left of the interval `[δ, 0]` — equations
`(19)`, `(21)`.

The Laplace transforms `(14)`–`(16)`, the residue computation `(17)`, the convolution associativity
`w = 1 ⋆ d`, and Landau's first-singularity theorem are cited parents (the transform side is
already carried by `CCMUnitRieszMarkovTransform`).
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The wavelet kernel -/

/-- **Equation (9).**  The moving wavelet kernel is the derivative of `Φ_T(u) = u w(T−u)`. -/
theorem hasDerivAt_movingWavelet {w dw : ℝ → ℝ} {T u : ℝ}
    (hw : HasDerivAt w (dw (T - u)) (T - u)) :
    HasDerivAt (fun s : ℝ => s * w (T - s)) (w (T - u) - u * dw (T - u)) u := by
  have hinner : HasDerivAt (fun s : ℝ => T - s) (-1) u := by
    simpa using (hasDerivAt_const u T).fun_sub (hasDerivAt_id u)
  have hcomp : HasDerivAt (fun s : ℝ => w (T - s)) (dw (T - u) * (-1)) u :=
    hw.comp u hinner
  have hid : HasDerivAt (fun s : ℝ => s) 1 u := hasDerivAt_id u
  have hprod := hid.fun_mul hcomp
  refine hprod.congr_deriv ?_
  ring

/-! ## The convolution split -/

/-- **Equation (11), first step.**  The wavelet coefficient splits into the two causal
convolutions. -/
theorem wavelet_coefficient_split {h w dw K : ℝ → ℝ} {T : ℝ}
    (hK : ∀ u, K u = w (T - u) - u * dw (T - u))
    (hint1 : IntervalIntegrable (fun u => h u * w (T - u)) volume 0 T)
    (hint2 : IntervalIntegrable (fun u => (u * h u) * dw (T - u)) volume 0 T) :
    (∫ u in (0 : ℝ)..T, h u * K u)
      = (∫ u in (0 : ℝ)..T, h u * w (T - u))
        - ∫ u in (0 : ℝ)..T, (u * h u) * dw (T - u) := by
  rw [← intervalIntegral.integral_sub hint1 hint2]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [hK u]
  ring

/-! ## The polar part of the virial -/

/-- The exact exponential window integral. -/
theorem integral_exp_neg_window {t : ℝ} :
    (∫ u in (0 : ℝ)..t, Real.exp (-u)) = 1 - Real.exp (-t) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => -Real.exp (-s)) (Real.exp (-u)) u := by
    intro u _
    have hneg : HasDerivAt (fun s : ℝ => -s) (-1) u := by
      simpa using (hasDerivAt_id u).fun_neg
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-u)) u := by
      simpa using hneg.exp
    have hres := hexp.fun_neg
    refine hres.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun u : ℝ => Real.exp (-u)) (Set.uIcc 0 t) := by fun_prop
  have hval : -Real.exp (-t) - -Real.exp (-0) = 1 - Real.exp (-t) := by
    rw [neg_zero, Real.exp_zero]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable, hval]

/-- **Equation (13), polar part.**  The causal virial of the exponential is the explicit boundary
correction. -/
theorem virial_exp_part {t : ℝ} :
    (∫ u in (0 : ℝ)..t, Real.exp (-u)) - t * Real.exp (-t)
      = 1 - (1 + t) * Real.exp (-t) := by
  rw [integral_exp_neg_window]
  ring

/-! ## The Landau nonnegativity shift -/

/-- **Equations (18), (20).**  The one-sided coefficient bound is exactly nonnegativity of the
shifted function. -/
theorem landau_shift_nonneg_iff {I C c T : ℝ} :
    -(C * Real.exp (c * T)) ≤ I ↔ 0 ≤ I + C * Real.exp (c * T) := by
  constructor <;> intro h <;> linarith

/-- **Equations (19), (21).**  With `0 < ε < δ + 1/2` the shift exponent is strictly below the pole
abscissa, so the added pole lies strictly left of the interval `[δ, 0]`. -/
theorem landau_exponent_lt {delta eps : ℝ} (hlt : eps < delta + 1 / 2) :
    -1 / 2 + eps < delta := by linarith

/-- **Equation (21), bracketing.**  A pole abscissa above `δ` and a convergence abscissa at most
`0` bracket the Landau contradiction interval. -/
theorem landau_bracket {delta sigma : ℝ} (h1 : delta ≤ sigma) (h2 : sigma ≤ 0) :
    delta ≤ 0 := le_trans h1 h2

end GaloisForLFunctions.RHTower

end
