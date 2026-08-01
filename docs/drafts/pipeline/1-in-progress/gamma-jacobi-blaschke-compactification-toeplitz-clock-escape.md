# Gamma--Jacobi Blaschke compactification of Toeplitz clock escape

- **ID:** `gamma-jacobi-blaschke-compactification-toeplitz-clock-escape`
- **Stage:** 1 — paper proof and direct Lean proof complete; audit pending
- **Parents:** `SR-41`, `SR-47`, `von-mangoldt-toeplitz-countertrace-analytic-radius-capacity-escape`
- **Type:** source-specific singular-reader compactification / positive no-go survivor
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [ADVANCE]`
  `[EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **RH used:** no
- **Computation used:** no

## Prior obstruction used, not rediscovered

Existing paper theorem for canonical von Mangoldt Toeplitz counterreader says: at prime-edge
aperture `M=p-1`, any analytic continuation of its coefficient symbol beyond reciprocal maximal
clock must vanish at

```text
zeta_p=1/log(p+1).                                      (1)
```

Nodes `zeta_p` accumulate at germ origin. Therefore one nonzero analytic cofinal symbol cannot
carry all zeros; analytic radius collapses or Hardy capacity diverges. That obstruction is parent
input and is not claimed again here.

## Exact Gamma boundary compactification

Apply reciprocal-log Gamma--Jacobi coordinate

```text
kappa(z)=tanh(z^(-1))^2.
```

At exact source clocks `(1)`,

```text
r_p=kappa(zeta_p)=tanh(log(p+1))^2.                     (2)
```

Lean proves every `r_p` is strictly between zero and one and prime marking is retained:

```text
r_p=r_q iff p=q.                                        (3)
```

Thus interior accumulation at `z=0` becomes boundary accumulation at `r=1`, exactly where a
nontrivial Hardy inner factor may carry infinitely many zeros.

## Exact Blaschke budget

Hyperbolic identity gives

```text
1-r_p
 =4(p+1)^2/((p+1)^2+1)^2
 <=4/p^2.                                               (4)
```

No prime number theorem is required. Comparison with ordinary square summability proves

```text
sum_p (1-r_p)<infinity.                                 (5)
```

So `(r_p)` is a Blaschke-admissible zero sequence. Lean also proves

```text
product_p r_p exists and is nonzero.                    (6)
```

Equation `(6)` is value at Hardy origin of normalized prime Blaschke packet; it certifies packet
does not collapse identically. Classical Blaschke theorem then supplies nonzero bounded inner
function with zero set `(r_p)`.

## Why this changes source frontier

Toeplitz analytic-radius no-go left only “singular boundary capacity” and explicitly asked whether
it is odd Gamma--Jacobi residual. `SR-47` identified first residual coordinate with connection
defect. Equations `(2)`--`(6)` now show same Gamma projective coordinate compactifies *entire exact
counterreader zero packet* into admissible Hardy boundary divisor.

This is not generic discovery of Blaschke condition. New source composition is:

```text
von Mangoldt maximal transport clock
 -> reciprocal counterreader zero at 1/log(p+1)
 -> reciprocal-log Gamma--Jacobi projective node
 -> summable boundary divisor with nonzero inner packet.
```

It gives canonical candidate carrier for singular cyclic reader rather than another abstract
matrix completion.

## Remaining falsifier

Still unproved:

1. after conjugating finite counterreader symbols by `z=1/artanh(sqrt r)`, their normalized inner
   factors converge to prime Blaschke packet;
2. outer factor equals rank-one `SR-47` tail/connection transgression rather than arbitrary
   analytic gauge;
3. resulting singular reader implements completed Euler multiplication on infinite-index Krein
   current;
4. reader produces fibre orientation/RH.

Failure of item 1 or 2 must classify exact missing outer factor. Success gives source-fixed
completed reader candidate.

## Collision and literature boundary

Corpus search found no use of `tanh(log(p+1))^2` to compactify reciprocal Toeplitz clock zeros.
Generic Blaschke condition and Meixner--Pollaczek/Xi expansions are known. Targeted primary-source
search found Inoue's and Romik's Meixner--Pollaczek expansions of completed L-functions/Xi and
standard Blaschke-sequence literature, but no von Mangoldt counterreader/Gamma compactification.
External priority remains unverified.

## Lean

Module:

```text
formal/GaloisForLFunctions/RHTower/GammaJacobiToeplitzClockBlaschkeCompactification.lean
```

Capstones:

- `gammaJacobiRightEndpointDiskNode_eq_reciprocalClockPushforward`;
- `gammaJacobiRightEndpointDiskNode_eq_iff`;
- `summable_one_sub_gammaJacobiRightEndpointDiskNode`;
- `multipliable_gammaJacobiRightEndpointDiskNode`;
- `tprod_gammaJacobiRightEndpointDiskNode_ne_zero`.

Direct command passed:

```text
lake env lean GaloisForLFunctions/RHTower/GammaJacobiToeplitzClockBlaschkeCompactification.lean
```

## Gates

- [x] whole-corpus collision audit
- [x] generic Blaschke/Meixner--Pollaczek layer classified known
- [x] source paper proof `(2)`--`(6)`
- [x] direct unconditional Lean proof
- [ ] umbrella wiring
- [ ] axiom audit
- [ ] forbidden-declaration lint
- [ ] final narrow build
- [ ] external expert novelty audit
- [ ] inner/outer convergence of conjugated counterreader
- [ ] completed Euler reader / fibre orientation / RH
