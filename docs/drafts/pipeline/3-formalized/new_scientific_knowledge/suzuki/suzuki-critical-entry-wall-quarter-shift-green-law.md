# Suzuki critical entry-wall quarter-shift Green law

- **ID:** `suzuki-critical-entry-wall-quarter-shift-green-law`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-critical-entry-wall-quarter-shift-green-law-formalized.md`
- **Type:** SOURCE IDENTIFICATION / CAUSAL GREEN LAW / UNIQUE CALIBRATION
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `suzuki-causal-entry-third-jet-boundary-law.md`,
  `suzuki-critical-aperture-quarter-shift-current.md`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki, arXiv:2206.03682v4, Theorem 1.1; M. Suzuki,
  arXiv:2606.09096v1, equations (2.2), (2.9)--(2.11), Sections 6 and 8.2--8.3

## Frontier attacked

The current open core `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED` needs the actual near-prime
entry channel coupled to the critical Gamma/aperture current.  Previous corpus results left one
specific identification open:

```text
third-jet endpoint reporter  <->  quarter-shift valuation current.               (1)
```

The phase and normalization in `(1)` are not choices.  They are forced by the fact that a delay
`ell=log n` enters an aperture at `a=ell/2`.

## Theorem A: full causal entry Green equation `[PAPER-PROVED]`

Let `F_near(ell,z)` and `F_far(ell,z)` be the denominator-matched delayed-hinge channels from the
parent entry theorem and put

```text
G(ell,z)=F_near(ell,z)-F_far(ell,z).                    (2)
```

For `ell<2a`, let `H(ell,z)` be the high Fourier window, `W(z)` the whole window, and
`tau(ell)=v(a-ell)`.  The already derived second and third delay jets give

```text
G''  =z^2 exp(i z ell)(H-W),
G''' =i z^3 exp(i z ell)(H-W)+z^2 exp(i a z)tau.        (3)
```

Therefore

```text
(d/dell-i z) G''(ell,z)=z^2 exp(i a z)tau(ell).         (4)
```

At entry wall `ell=2a`, `G=G'=G''=0`.  Thus `(4)` is not merely a wall asymptotic: it is the exact
third-order causal Green equation reconstructing the complete near/far difference from endpoint
trace.  Equivalently, with entry depth `s=2a-ell` and `u(s)=v(-a+s)`,

```text
G(2a-s,z)
 =exp(i a z) integral_0^s
    [exp(-i z(s-r))-1+i z(s-r)] u(r) dr.               (5)
```

Indeed the bracket has zero value and slope at zero, and its Laplace transfer is

```text
-z^2/[q^2(q+i z)].                                     (6)
```

Applying `d_s^2(d_s+i z)` proves `(4)` and the three zero initial conditions prove uniqueness.
No estimate or positivity statement occurs.

## Theorem B: wall phase equals critical Gamma phase `[PAPER-PROVED]`

For prime `p`, depth `e`, and `n=p^(e+1)`, define its entry wall

```text
a_(p,e)=log(n)/2.                                       (7)
```

The causal reporter phase at this wall is exactly

```text
exp(i t a_(p,e))=exp(i t log(n)/2),                     (8)
```

which is the conjugated critical Gamma-height phase in the quarter-shift atom.  Moreover

```text
a_(p,e+1)-a_(p,e)=log(p)/2,                             (9)
```

so one valuation step contributes exactly the half-log phase
`exp(i t log(p)/2)` already present in the critical depth ratio.  This explains the quarter shift
as entry-wall geometry rather than an auxiliary convergence trick.

## Theorem C: exact critical entry forcing `[PAPER-PROVED]`

Write the source-defined real endpoint amplitude

```text
A_e(h,b;p)
 =sqrt[log(p)/n * exp(log(n)/2)]
    * I_cubic(h,b;p,e),                                 (10)
```

where `I_cubic` is the corpus's cubically normalized true-aperture innovation.  The critical
quarter-shift atom is exactly

```text
T_e(h,b,t;p)=A_e(h,b;p) exp(i t a_(p,e)).               (11)
```

Substituting endpoint trace `tau=A_e` into the causal Green equation gives the exact forcing law

```text
Delta_3(p,e;t)
 :=F_near'''(2a_(p,e)-,t)-F_far'''(2a_(p,e)+,t)
 =t^2 T_e(h,b,t;p).                                    (12)
```

Consequently the existing quarter-shift recursion becomes a recursion of actual entry-wall
third-jet forcings:

```text
Delta_3(p,e+1;t)=rho(h,b,t;p) Delta_3(p,e;t),           (13)

sum_(e>=0) Delta_3(p,e;t)
 =t^2 T_0(h,b,t;p)/(1-rho(h,b,t;p)).                   (14)
```

Thus the complete depth resolvent is precisely a causal sum of calibrated prime-power entry
forces.  Equation `(14)` closes the phase/type identification in `(1)`; no fitted phase or
leakage coefficient remains.

## Theorem D: calibration is unique off the center `[PAPER-PROVED]`

Fix `t!=0`.  The coefficient `t^2 exp(i t a_(p,e))` never vanishes.  Hence any endpoint trace
`tau` satisfying

```text
t^2 exp(i t a_(p,e)) tau=t^2 T_e(h,b,t;p)              (15)
```

must equal `A_e(h,b;p)`.  At one nonzero spectral point, the quarter-shift current therefore
determines the only endpoint trace capable of producing it.  The actual Suzuki restricted-Weil
resolvent either realizes `(10)` (possibly after the already fixed affine normalization), or the
proposed Ward producer is falsified.

## Scientific consequence and corrected frontier

The former instruction “identify the third-jet trace with the quarter-shift current and then
triple-integrate” is now split into a proved and an open part:

- **proved:** exact Green equation `(4)`, phase equality `(8)`, source amplitude `(10)`, forcing
  identity `(12)`, depth completion `(14)`, and uniqueness `(15)`;
- **open:** prove that Suzuki's concrete deficiency endpoint trace has calibrated expansion
  `(10)`, or prove that its residual contribution to the fixed-width rectangular Ward form is
  uniformly lower semibounded after affine sewing and the continuous Gamma/polar channel.

This leaves `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED` as actual RH frontier, but removes the
previous phase and triple-integration ambiguity.  A mismatch with `(10)` is now a sharp
source-level falsifier, not an unspecified correction term.

## Hostile audit

1. `a_(p,e)` is wall aperture, while `b` in `I_cubic(h,b)` is observer aperture.  They must not be
   conflated.  Fixed `b` is what preserves geometric depth recursion; `(11)` is a weighted
   superposition of reporters located at different entry walls.
2. The factor `t^2` is mandatory: it comes from canonical screw denominator cancellation.
3. Conjugation is mandatory: it changes Gamma phase from `exp(-it log(n)/2)` to the positive wall
   phase in `(8)`.
4. At `t=0`, `(12)` vanishes and cannot identify endpoint trace; uniqueness correctly requires
   one nonzero spectral point.
5. Summability is first in valuation depth.  No standalone critical Gamma Hilbert vector and no
   atomwise positive prime Gram is asserted.
6. Equations `(4)--(14)` use no Xi zero, RH premise, numerical evidence, or asymptotic estimate.

## Novelty audit

Internal search found the third wall jet and quarter-shift resolvent separately, but no causal
Green equation `(4)`, entry-wall phase calibration `(8)`, or identification `(12)--(14)`.
Suzuki's papers provide the delayed prime steps, restricted finite-aperture operator, and
deficiency framework, but do not state this entry-wall/critical-current transference.  Classical
inputs are Leibniz differentiation and a geometric series.  Candidate novelty is their exact
source-specific synthesis; external priority remains unverified.

## Formalization gates

- [x] paper derivation and sign audit
- [x] exact all-depth Green equation
- [x] wall/Gamma phase and amplitude calibration
- [x] unique endpoint trace classification
- [x] Lean formalization of differential transport, wall calibration, forcing recursion, and
  uniqueness:
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalEntryWallQuarterShiftGreenLaw.lean`
- [x] explicit integral Green representation `(5)` in Lean:
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiEntryWallGreenRepresentation.lean`
- [ ] actual restricted-Weil endpoint realization or bounded residual
- [ ] rectangular Ward-defect lower bound and RH

## Lean status of the integral representation

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiEntryWallGreenRepresentation.lean` formalizes `(5)`
unconditionally; axiom audits report only `[propext, Classical.choice, Quot.sound]`.

- `entryGreenKernel z x = exp (-I z x) - 1 + I z x` is the bracket of `(5)`, and
  `entryGreenIntegral z u s = ∫_0^s entryGreenKernel z (s - r) * u r` is the causal convolution.
  The constant wall phase `exp (i a z)` of `(5)` is the calibration already formalized in the
  parent module, so it is carried outside the convolution.
- `entryGreenIntegral_eq` : **the kernel separates.**  Because
  `exp (-I z (s - r)) = exp (-I z s) * exp (I z r)` and the remaining part of the bracket is
  affine in `s - r`, the convolution equals an explicit combination of three primitives of the
  trace, `entryTraceExpMoment`, `entryTracePrimitive` and `entryTraceMoment`, with no `s` left
  inside any integrand.  Every delay jet is then ordinary calculus; no differentiation under an
  integral sign and no Fubini on a triangle is needed anywhere in the proof.
- `hasDerivAt_entryGreenIntegral`, `hasDerivAt_entryGreenJet1`, `hasDerivAt_entryGreenJet2` :
  the three delay jets, with the endpoint terms cancelling exactly as the bracket's double
  vanishing predicts -- `entryGreenJet2` carries no `u` term at all.
- `entryGreen_causal_equation` : `(d/ds + I z) Φ'' = -z ^ 2 * u`, which is `(4)` in entry depth.
  It is a pure ring identity once the jets are computed; the `I ^ 2 = -1` input enters one step
  earlier, in the second jet.
- `entryGreenIntegral_zero`, `entryGreenJet1_zero`, `entryGreenJet2_zero` : the three vanishing
  wall conditions `G = G' = G'' = 0`.
- `entryGreenIntegral_unique` : **uniqueness.**  Any third-order causal solution with those three
  vanishing wall conditions equals the convolution.  The proof integrates the homogeneous
  equation by the integrating factor `exp (I z s)`, so no ODE existence theory is invoked.

Every `[PAPER-PROVED]` statement of this card is now in Lean.  The two remaining gates are the
open RH frontier recorded above, not theorems proved here.

## Subsequent source correction

Later hostile source audit proves `A_e(h,b;p)` contains independently chosen observer aperture
`b`, whereas Suzuki deficiency endpoint is fixed by restricted-Weil resolvent and wall aperture.
Therefore `A_e` is observed amplitude, not literal deficiency endpoint.  Survivor formalized in
`suzuki-critical-wall-field-square-root-weld.md`: bare Gamma amplitude before innovation is correct
endpoint candidate, and its complex bilinear square already equals universal far-hinge numerator.
