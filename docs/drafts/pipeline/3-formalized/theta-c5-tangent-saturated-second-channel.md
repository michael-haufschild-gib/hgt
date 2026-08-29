# Theta C5 tangent: saturated second channel is adverse

Status: `[FORMALIZED]` `[NOVELTY UNVERIFIED]`

## Exact claim

For `0 < t ≤ u` and first-atom reflection scale `A(u) ≥ 6`, put

```text
q = first-atom reflected action,
v = t * first-atom reflected first jet,
a = first-atom reflected first jet,
s = first-atom centre-scale action jet,
W = 14 + 10v + 8v/(exp(q)-1).
```

The coefficient carried by the likelihood-cone direction

```text
db = -y,  dm = y,  da = ds = dc = dn = dq = 0
```

in the first variation of the direct-C5 compensation margin is

```text
t * (a * (5-W) - s * (W-15)),
```

and it is strictly negative.

## Dependency-closed proof

The exact first-atom action satisfies `q>0`. Its displacement velocity is strictly
superquadratic: `2q<v`. Therefore the already-proved Bose barrier gives

```text
30 + 12q < W,
```

so in particular `W>30`, `5-W<0`, and `W-15>0`.

The reflected first jet `a` is strictly positive on `0<t≤u`. For the centre-scale jet, write

```text
s = z * (4A + d/r),
z = cosh(2t)-1.
```

Here `z>0`, and the exact physical tail theorem gives `4A+d/r>0` whenever `A≥6`; hence `s>0`.
Thus both terms

```text
a * (5-W),     -s * (W-15)
```

are strictly negative. Their sum is negative, and multiplication by `t>0` preserves strict
negativity.

## Interpretation

This is positive structural salvage from the failed sign-cone proof. The second displacement loss
and first mixed-centre gain do not cancel benignly when the formal bound `dm≤-db` saturates; their
exact C5 coefficient has the wrong sign everywhere in the physical first-atom tail. Any proof of the
`1/5` tangent reserve must therefore use a quantitative non-saturation law and/or retain the joint
third-displacement/second-centre channel. Separate jet signs and the existing pairwise cone cannot
close the tangent theorem.

## Audit

- `[CORPUS]` Superquadratic atom velocity, Bose barrier, first-jet positivity, and scale-action
  slope positivity are already formal in the fixed-action C5 and reflected Riccati modules.
- Standard convexity, log-sum-exp, exponential-family, and monotone-likelihood-ratio theory does not
  determine this source-specific C5 coefficient; no external priority claim is made.
- Lean module:
  `GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5TangentSaturatedSecondChannel`.
- Direct Lean and exact target build passed; axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
