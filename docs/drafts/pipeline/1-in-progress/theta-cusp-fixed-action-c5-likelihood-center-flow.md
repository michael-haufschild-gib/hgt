# Theta cusp fixed-action C5 likelihood centre flow

- **ID:** TC-C5-LIKE-CENTER
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Corpus source:** `thetaCuspFullSource_reflected_action_eq_singleAtom_add_interference`,
  `thetaCuspReflectedLikelihoodInterferenceAction_eq_cumulantAction`,
  `thetaCuspLikelihoodSourceLogPartitionJetTwo_pos`,
  `thetaCuspLikelihoodSourceLogPartitionJetThree_neg`, and
  `strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetThree`
- **Statement:** The three centre-flow jets contributed by the literal higher-atom likelihood
  action are strictly positive throughout the open same-half-line chamber.

## Goal

Let `F` be the corpus's source-coordinate logarithmic likelihood partition and define

```
S(u,t) = 2F'(u)-F'(u+t)-F'(u-t),
M(u,t) = F''(u-t)-F''(u+t),
N(u,t) = -F'''(u+t)-F'''(u-t).
```

Prove unconditionally that `0<t<=u` implies `0<S(u,t)`, `0<M(u,t)`, and `0<N(u,t)`.
Then identify these as the centre derivative of likelihood action, centre derivative of its first
displacement jet, and centre derivative of its second displacement jet.

## Corpus-derived attack

Corpus proves `F''>0`, `F'''<0`, and that `F'''` differentiates to a positive fourth source jet.
Thus `F''` is strictly decreasing, giving `M>0`, while endpoint negativity gives `N>0`.
Moreover `F'` is strictly concave because its derivative `F''` is strictly decreasing; strict
midpoint concavity at the pair `u-t,u+t` gives `S>0`.

## RH passport

likelihood centre-flow signs and exact atom+likelihood centre-jet decomposition
→ likelihood-interference perturbation bound for exact first-atom C5 compensation
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

These signs are necessary structure, not by themselves a claim that nonlinear C5 compensation is
monotone under likelihood addition.

## Gates

- [x] 0 → 1 in-progress: corpus-derived, source-pure, exact chamber, RH passport
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: direct Lean, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone theorem, proof, certificate, Door-2 audit

## Log

- 2026-08-29 — conjecture originated only after corpus search isolated missing centre likelihood
  channels between exact additive action and fixed-action C5 compensation.
