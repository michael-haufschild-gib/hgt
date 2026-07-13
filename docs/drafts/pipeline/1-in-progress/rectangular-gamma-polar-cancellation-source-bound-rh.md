# Rectangular Gamma--polar cancellation and bounded source law

- **ID:** `rectangular-gamma-polar-cancellation-source-bound-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / THEOREM TARGET (Lean) / RH VALUE RELATION
- **Scientific status:** `[CONJECTURE] [CLASSICAL INGREDIENTS] [NOT AN RH PROOF]`
- **Statement:** For every fixed positive rectangular width, the normalized archimedean bottom
  value minus the elementary polar square is uniformly bounded over all separated apertures.
  Consequently RH is equivalent to boundedness, and hence to all-epsilon one-sided subpower
  lower control, of the corresponding finite prime--polar source values.

## Goal

Turn the now-formal sharp rectangular Guinand--Weil identity into a direct RH-to-source estimate
without differentiating a merely nonnegative Weil value.  The target is source-pure: it relates
the full Xi Weil value, the explicit Gamma correction, the elementary polar square, and the finite
von-Mangoldt autocorrelation already present in Lean.

## Candidate exact identity

For `A_(L,a)(t)` equal to `rectangularTwoEdgeAutocorrelation L a t`, the Gauss digamma integral and
the existing sharp Fourier inversion should give

```text
normalizedBottomArch(L,a) - 2 polarFeature(L,a)^2
 = 2 integral_0^infinity
     [exp(-2t) A_(L,a)(0) - exp(-t/2) A_(L,a)(t)]
       /(1-exp(-2t)) dt
   - (gamma + log pi) A_(L,a)(0).                           (1)
```

For `a >= L >= 0`, the four-tent law reduces on `t >= 0` to two fixed self-overlap tents and one
moving cross tent.  Here `A_(L,a)(0)=2L`, while the moving tent is bounded by `min(L,t)`.  The
right side of `(1)` is therefore bounded by a constant depending only on `L`, uniformly in `a`.

Combining `(1)` with

```text
Weil(L,a) = -2 primeAutocorrelation(L,a) + normalizedBottomArch(L,a)
source(L,a) = -2 primeAutocorrelation(L,a) + 2 polarFeature(L,a)^2
```

gives

```text
source(L,a) = Weil(L,a) - boundedGammaPolarCorrection(L,a). (2)
```

Under RH the existing reciprocal-square estimate bounds `Weil(L,a)` uniformly in `a`; hence the
source is uniformly bounded.  Conversely, the existing rectangular source/Weil lower-tail
criterion returns RH.

## Relation to the sharp dyadic window

A positive finite-width increment law is also available: increasing `(L,x)` to `(L+h,x+h)` adds
at least `h` times every von-Mangoldt atom already in the closed multiplicative shell.  This gives
a value-only majorant for the sharp dyadic window.  A first-order secant alone has the familiar
`h sqrt(n) + 1/h` loss, so the all-epsilon sharp error still requires either a genuinely local
Gamma/Weil slope estimate or the classical RH Chebyshev bound
`psi(x)-x = O(sqrt(x) log(x)^2)`.

## Gates

- [x] 0 -> 1 in-progress: exact candidate identity, existing Fourier inversion, and fixed-width
  domination identified
- [ ] 1 -> 2 fully-proven: justify Gauss/Fubini identity `(1)` and the uniform tent bound on paper
- [ ] 2 -> 3 formalized: axiom-clean Lean theorem for `(1)`, uniform correction bound, and RH
  source equivalence
- [ ] sharp-window completion: formal RH Chebyshev error or an equally strong local value relation
- [ ] RH

## Literature boundary

Gauss's integral representation of the digamma function is classical (DLMF 5.9.12).  The RH
estimate `|psi(x)-x| <= sqrt(x) log(x)^2/(8 pi)` for sufficiently large `x` is Schoenfeld's
explicit form of the von Koch consequence.  Novelty, if any, can attach only to the exact
rectangular value relation `(1)`--`(2)`, not to either classical input.

## Log

- 2026-07-13 — created after the full rectangular Guinand--Weil contour identity was formalized;
  stage-2 corpus and literature audit replaced the unstable derivative target by the exact
  Gamma--polar cancellation value.
