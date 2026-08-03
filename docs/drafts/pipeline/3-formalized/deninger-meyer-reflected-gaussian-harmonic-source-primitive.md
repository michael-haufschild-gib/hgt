# Reflected-Gaussian harmonic-source Green primitive

- **ID:** `deninger-meyer-reflected-gaussian-harmonic-source-primitive`
- **Stage:** 3-formalized
- **Type:** SOURCE CONSTRUCTION / ORIENTED NONLOCAL LANDING
- **Status:** `[LOCAL-RESEARCH] [PAPER PROVED] [LEAN FORMALIZED]`
- **Parents:**
  `deninger-meyer-reflected-gaussian-completed-source-green.md`,
  `deninger-meyer-reflected-gaussian-prime-gamma-cauchy-landing.md`
- **Publication context:**
  `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`
- **Lean module:**
  `../../../../formal/GaloisForLFunctions/RHTower/DeningerMeyerReflectedGaussianHarmonicSourcePrimitive.lean`

## Goal

Replace the merely coefficientwise description of the completed Green primitive by a concrete
Deninger source operator, then apply that operator before integration to the explicit two-sided
prime--Gamma Cauchy boundary.  This closes the oriented source-object arrow without assuming RH or
choosing coefficients after divisor restriction.

## Theorem

For every multiplicity copy `q` of an actual Xi zero `rho_q`,

```text
epsilon(q) = sign(Im rho_q).
```

Indeed `Re lambda_q = Im rho_q`, and `Im rho_q != 0` unconditionally, so the fallback branch in
the lexicographic functional-equation orientation is never attained.  Let

```text
W = i sign(D)
```

be the Deninger leafwise harmonic Hodge multiplier on the completed source carrier.  Then

```text
W^2 = -1,
e_ref = i W h_ref.
```

If `B_tau(x)` is the already constructed two-sided absolute-Euler prime--Gamma Cauchy boundary,
define the oriented source before integration by

```text
B_tau^or(x) = i W B_tau(x).
```

It is Bochner integrable and satisfies the exact source landing

```text
integral_R B_tau^or(x) dx = e_ref.
```

Thus the unique completed Green primitive is a literal oriented nonlocal prime--Gamma source
integral, not a post-divisor interpolation.

## Formal theorem

`DeningerMeyerReflectedGaussianHarmonicSourcePrimitive.lean` proves:

- `deningerArithmeticFEOrientation_eq_deningerFreqSign`;
- `deningerXiHarmonicHodge_eq_deningerHodgeW`;
- `deningerXiHarmonicHodge_sq`;
- `reflectedGaussianHorizonCompletedGreenPrimitive_eq_harmonicHodge`;
- `integrable_reflectedGaussianPrimeGammaOrientedCauchyBoundary`;
- `integral_reflectedGaussianPrimeGammaOrientedCauchyBoundary_eq_greenPrimitive`.

All proofs are unconditional.

## Scientific consequence

Route L now has the concrete oriented source object requested by the strict frontier:

```text
two-sided prime--Gamma boundary
  -> physical Deninger harmonic Hodge orientation before integration
  -> exact completed Green primitive.
```

Remaining problem is no longer construction, completion, divisor landing, or orientation.  It is
the arithmetic compatibility theorem comparing this explicit oriented boundary source with the
closed adaptive Mobius--theta prime-normal resolved sector while intertwining codiagonal
augmentation.

## Anti-theatre audit

- `W = i sign(D)` and Cauchy's formula were already known in corpus and are not claimed as new.
- New content is their exact unconditional identification with the unique all-divisor completed
  Green primitive, including an oriented source integrand defined before divisor reduction.
- No RH premise, zero-location choice, divisor-indexed damping, pulled-back norm, or abstract
  existential comparison is introduced.
- This removes one real ambiguity from Eq. (7.17): source Green orientation is now fixed by the
  actual harmonic frequency and can no longer be supplied by an arbitrary cross-geometry map.

## Log

- 2026-08-03 — paper proof and unconditional Lean formalization completed.
