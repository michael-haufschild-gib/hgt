# Theta C5 likelihood mixed-jet trapezoid

Status: `[FORMALIZED]` `[NOVELTY UNVERIFIED]`

## Exact claim

For every same-half-line packet `0<t≤u`, the first mixed-centre likelihood jet is bounded by
displacement times the second mixed-centre likelihood jet:

```text
c5LikelihoodScaleMixedJetOne(u,t)
  ≤ t * c5LikelihoodScaleMixedJetTwo(u,t).
```

## Dependency-closed proof

Let `F` be the higher-atom likelihood log partition and put `k(x)=-F'''(x)`. The corpus proves
`F'''''(x)<0` for `x≥0`; hence `k''(x)=-F'''''(x)>0`, so `k` is convex on the nonnegative source
half-line. The fundamental theorem gives

```text
F''(u-t)-F''(u+t) = integral_[u-t,u+t] k(x) dx.
```

Because `0<t≤u`, this interval is nonnegative. The upper Hermite--Hadamard inequality for convex
`k` gives

```text
integral k ≤ (2t)/2 * (k(u-t)+k(u+t))
           = t * (-F'''(u-t)-F'''(u+t)).
```

The two sides are exactly the named first and second mixed-centre likelihood jets.

## Interpretation

This is the missing upper coupling excluded by the coarse cone audit. Near the seam it forces the
adverse mixed-centre channel to vanish at the same displacement scale as its favorable third-jet
partner. Together with the independently proved exponential lower coupling, it sandwiches the
ratio between a source-gap floor and a third-jet trapezoid ceiling. It does not yet prove the C5
`1/5` tangent reserve; the remaining task is an atom-coefficient domination using this coupled
three-jet cone.

## Audit

- `[CORPUS]` Fifth likelihood source jet is strictly negative; required derivative identities and
  upper Hermite--Hadamard inequality are formal.
- No computation enters proof.
- Lean module:
  `GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodMixedTrapezoid`.
- Direct Lean and exact target build passed; axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
