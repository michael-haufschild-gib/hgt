# Hypertranscendental finite-divisor surgery and the quantized Ward index

- **Stage:** 1-in-progress
- **Type:** universal theorem / scoped no-go / finite-rank zero-exclusion boundary
- **Target:** `formal/GaloisForLFunctions/RHTower/HypertranscendentalQuartetWardIndex.lean`

## Object

For `0 < a < 1/2`, `b > 0`, let

```text
Q_{a,b}(s)
 = (((s-1/2)-a)^2+b^2)(((s-1/2)+a)^2+b^2),
Xi_{a,b}(s) = Q_{a,b}(s) Xi(s).
```

The corresponding Euler-edge infinitesimal Ward density is

```text
D_{a,b}(t)
 = 2 Re[2/(1/2+it+a+ib) + 2/(1/2+it+a-ib)].
```

## Selected theorem

The family `Xi_{a,b}` is entire, functional-equation symmetric, Schwarz symmetric,
hypertranscendental, and nonvanishing on the open real critical segment, but it has the prescribed
off-critical quartet `1/2 ± a ± ib`.  Its Ward density is nonnegative and

```text
∫ D_{a,b}(t) dt = 8π,
```

independently of `a,b`.  Meanwhile the exact logarithmic source changes by the nonzero rational
gauge charge `Q'_{a,b}/Q_{a,b}`; at `s=0` that charge never vanishes in the stated parameter range.

The same quartet is realizable by a nonnegative generalized von Mangoldt correction with exact
reflection antisymmetry; its completed carrier is polynomially gauged Xi and its pole order rises
from one to three.  Thus hypertranscendence, entire functional-equation/Schwarz symmetry,
real-axis positivity, and linear Euler positivity do not exclude a single off-critical quartet.
The simple-pole normalization or equivalently exact arithmetic source marking is indispensable.

## Intended finite-packet extension

For any finite family of such quartets, multiply the gauges and add the source/Ward densities.
Hypertranscendence and both symmetries survive, prescribed zeros are inserted, and

```text
Ward mass = 8π · (# quartets with multiplicity)
          = 4π · (pole-order excess).
```

This gives a finite-rank zero-exclusion theorem: inside this positive self-dual rational
deformation class, preserving the simple pole forces the packet to be empty.

## Hostile gates

- [ ] Direct Lean proof, exact file.
- [ ] Axiom audit.
- [ ] Current primary-source novelty audit.
- [ ] Rule out “obvious polynomial multiplication” objection by making the positive Euler source,
      exact source charge, and `8π` index conservation integral to the theorem.
- [ ] General-journal antagonist review.

