# Theta cusp fixed-action C5 exact first-atom tail

- **ID:** TC-C5-EFATOM
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Corpus source:** `ThetaCuspSingleAtomReflectedRiccatiContraction`,
  `ThetaCuspAtomLikelihoodCrossDomination`, `ThetaCuspLikelihoodGapCumulantRiccati`,
  `ThetaCuspReflectedLikelihoodInterferenceFactorization`, and
  `ThetaCuspFixedActionC5HyperbolicGaussianTailCore`
- **Statement:** On `0 < t <= u`, the exact reflected first theta atom has strictly positive
  direct-C5 fixed-action compensation under centre-scale flow.

## Goal

Let

```
A(u) = pi*exp(2u),
z(t) = cosh(2t)-1,
lambda(A) = 3A/(A-3/2)^2,
r(A,z) = 1-lambda(A)z,
q(u,t) = 2A(u)z(t)-log(r(A(u),z(t))).
```

Using the literal displacement jets `a=q_t`, `b=q_tt`, `c=q_ttt` and centre jets
`s=q_u`, `m=q_tu`, `n=q_ttu`, prove for `0<t<=u`

```
H = a*(t*m) - (a+t*b)*s,
P = a*(t*m+t^2*n) - (a+3*t*b+t^2*c)*s,
v = t*a,
0 < 5P-(14+10v+8v/(exp(q)-1))*H.
```

All hypotheses are the physical same-half-line chamber. No sampled value or computed
certificate may enter paper or Lean proof.

## Gates

- [x] 0 → 1 in-progress: corpus-derived, source-pure, exact chamber, RH passport
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: unconditional Lean theorem, direct Lean, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem, proof, certificate, Door-2 audit

## Corpus basis and attack

Corpus proves `A>3`, `r>1/2`, positivity of the first three displacement jets, and the exact
factorization of completed theta action into this first-atom action plus likelihood interference.
The newly formalized Gaussian theorem proves the same compensated inequality after deleting
`-log r`.

Differentiate the rational correction exactly under the scale derivation `delta=2A*d/dA`. If
`d=delta(lambda)`, then

```
s = 4Az + d*z/r,
m = (4A+d/r^2) z_t,
n = 4*(2*lambda*d*z*(z+2)/r^3 + (4A+d/r^2)*(z+1)).
```

Here `d<0`; the task is therefore a genuine compensated sign problem, not monotone addition of
a positive action. Clear only positive factors (`r>1/2`, `exp(q)-1>0`) and seek an exact
decomposition into the proved Gaussian hyperbolic certificate plus correction terms controlled
by the same-half-line identity used in the half-factor theorem.

## RH passport

exact first-atom compensation
→ likelihood-interference perturbation bound from the corpus-exact additive action factorization
→ literal theta far-tail compensation
→ local-bivariate and compact-middle assembly
→ global direct-J orientation
→ fixed-action modular-seam comparison
→ reflection-odd rank-four/Ptolemy packet wall
→ cofinal no-escape
→ CLG/TTF or Weil polarization nonnegativity
→ `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
`riemannHypothesis_iff_xiWeilPolarization_nonneg`
→ RH.

## Open core

Prove or refute the displayed exact compensated inequality. If it fails, extract the sharp
same-half-line tail chamber, factor boundary, or replacement invariant before retiring the
route; the Gaussian theorem remains mandatory positive salvage.

## Log

- 2026-08-29 — conjecture originated from exact corpus action/factor/jet theorems and the proved
  Gaussian compensation core; explicit RH passport recorded before proof work.
