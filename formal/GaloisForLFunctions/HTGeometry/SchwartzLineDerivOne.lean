import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The unit line derivative on the real line is the ordinary derivative

Mathlib's Fourier identities for Schwartz maps are stated with the line-derivative operator
`∂_{m}` in a direction `m` of the ambient space.  On the real line the only direction needed is
`m = 1`, where the operator collapses to the ordinary derivative: `∂_{1} f = f'` pointwise,
definitionally, because `∂_{m} f = evalCLM m (fderivCLM f)` evaluates the Fréchet derivative at
`m` and `fderiv ℝ f x 1 = deriv f x`.

Recording this collapse turns the vector-shaped Fourier lemmas

```text
𝓕 (∂_{m} f) = (2πI) • smulLeftCLM (inner ℝ · m) (𝓕 f)
∂_{m} (𝓕 f) = 𝓕 (-(2πI) • smulLeftCLM (inner ℝ · m) f)
```

into the scalar statements `𝓕(f')(ξ) = 2πiξ·𝓕f(ξ)` and `(𝓕f)' = −2πi·𝓕(x f)`, which are the two
inputs to the Hermite Fourier eigenrelation.
-/

open SchwartzMap LineDeriv
open scoped Real FourierTransform LineDeriv

namespace GaloisForLFunctions

/-- **On the real line the unit line derivative is the ordinary derivative.**  This is the
bridge from mathlib's direction-indexed Fourier identities to their scalar form. -/
theorem schwartz_lineDerivOp_one_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (LineDeriv.lineDerivOp (1 : ℝ) f : 𝓢(ℝ, ℂ)) x = deriv (f : ℝ → ℂ) x :=
  fderiv_apply_one_eq_deriv

/-- The same statement as an equality of functions. -/
theorem schwartz_lineDerivOp_one (f : 𝓢(ℝ, ℂ)) :
    ((LineDeriv.lineDerivOp (1 : ℝ) f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = deriv (f : ℝ → ℂ) :=
  funext (schwartz_lineDerivOp_one_apply f)

/-- The inner product against the unit direction on `ℝ` is the identity, so the multiplier in
mathlib's Fourier identities is plain multiplication by `x`. -/
theorem inner_one_eq_self (x : ℝ) : inner ℝ x (1 : ℝ) = x := by
  simp

end GaloisForLFunctions
