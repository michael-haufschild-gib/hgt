# Nondegenerate Möbius matching preserves differential complexity

- **ID:** `mobius-observation-differential-complexity-invariance`
- **Stage:** 3-formalized
- **Type:** THEOREM / DIFFERENTIAL ALGEBRA / RESPONSE MATCHING
- **Status:** `[PROVEN]` unconditional Lean source check passes
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/MobiusObservationHypertranscendence.lean`

## Statement

Let \(E/F\) be a differential-field extension of characteristic zero and

\[
  M(x)=\frac{a x+b}{c x+d},\qquad a,b,c,d\in F,\qquad ad-bc\ne0.
\]

Then

\[
  M(x)\text{ is DA over }F
  \quad\Longleftrightarrow\quad
  x\text{ is DA over }F,
\]

and equivalently

\[
  M(x)\text{ is HT over }F
  \quad\Longleftrightarrow\quad
  x\text{ is HT over }F.
\]

The totalized division convention of a field does not create a loophole. If \(x\) is HT, then
\(cx+d\ne0\), and the inverse denominator \(-cM(x)+a\) is also nonzero. Consequently

\[
  x=\frac{dM(x)-b}{-cM(x)+a}
\]

holds exactly, and the existing fractional-linear recovery theorem transfers HT to the
observation.

## Why it matters physically

Near-horizon Green functions are commonly connected to exterior detectors by

\[
  G_{\rm full}
    =\frac{b_+ + b_-G_{\rm IR}}{a_+ + a_-G_{\rm IR}}.
\]

Whenever the four matching coefficients belong to the declared differential base and the
connection matrix is nondegenerate, exterior matching cannot erase or manufacture the DA/HT phase
of \(G_{\rm IR}\). Taking \(F=\mathbb C(z)\) permits arbitrary rational frequency-dependent
matching, not only constant matching.

This is a conditional no-cancellation theorem, not a declaration that unknown analytic matching
coefficients are rational or DA. A physical application must classify those coefficients or
extract the universal IR scaling response independently.

## Lean declarations

- `mobiusObservable`
- `mobiusObservable_inverse_denominator_ne_zero`
- `mobiusObservable_recover_of_hypertranscendental`
- `hypertranscendentalOver_mobiusObservable`
- `differentialAlgebraicOver_mobiusObservable_iff`
- `hypertranscendentalOver_mobiusObservable_iff`

## Verification

- [x] corpus research run before adding reusable theorem
- [x] `lake env lean GaloisForLFunctions/HTGeometry/MobiusObservationHypertranscendence.lean`
- [x] one foreground Lean process
- [x] no numerical computation
- [ ] final module build and axiom audit deferred to end-of-task audit

