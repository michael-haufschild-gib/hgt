# Von Mangoldt--Gamma all-depth oriented anomaly

- **ID:** `von-mangoldt-gamma-all-depth-oriented-anomaly`
- **Stage:** 3-formalized
- **Type:** `[SOURCE-SPECIFIC POSITIVITY]`, `[PRIME--ARCHIMEDEAN JOIN]`, `[BRIDGE]`
- **Scientific status:** `[PROVED LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaOrientedAnomaly.lean`.
- **Parents:**
  `../../2-fully-proven/not_new_scientific_knowledge/10-euler-gamma-completion/von-mangoldt-gamma-clock-descent-anomaly.md`;
  `../../1-in-progress/prime-gamma-reflection-decimation-defect-resolvent-rh.md`.
- **Statement:** Every positive resolved von Mangoldt atom has a strict common alternating
  orientation in every output coordinate of the finite Gamma-clock descent anomaly at every
  positive depth.

## Exact source theorem

For a positive exponential source atom of weight `q`, rate `lambda`, base point `x`, and positive
Gamma depth `N`, the zeroth anomaly coordinate is

```text
alpha_N(q,lambda,x)
 =q exp(-x lambda)
   (sum_(j<N) (-lambda)^j/j! - exp(-lambda)).           (1)
```

Taylor's theorem with Lagrange remainder gives the strict orientation

```text
(-1)^(N+1) alpha_N(q,lambda,x)>0.                       (2)
```

This is proved as an equality and sign theorem for the actual
`finiteExponentialGammaAnomaly`, not for an independently defined positive proxy.

More generally, for `0<=i<N`, Lean proves the exact residual-depth factorization

```text
(alpha_N(q,lambda,x))_i
 =(-lambda)^i alpha_(N-i)(q,lambda,x)_0,                 (2a)

(-1)^(N+1)(alpha_N(q,lambda,x))_i
 =q exp(-x lambda) lambda^i R_(N-i)(lambda)>0.          (2b)
```

The derivative parity and omitted-tail parity therefore cancel to one sign depending only on
depth `N`, not on the jet coordinate.

For the resolved Euler source,

```text
q_n=Lambda(n)/n,     lambda_n=log n.                    (3)
```

Thus every `n>1` with `Lambda(n)>0` lies in exactly the same strict depth-`N` cone.  The theorem is
finite, unconditional, and prior to analytic continuation.  It uses neither Xi values nor its
divisor, real-rootedness, a target moment measure, or an RH-equivalent positivity hypothesis.

## What this changes

The corpus already had the adjacent-depth Bianchi current and the positive depth-one Cauchy Gram.
The new theorem supplies the missing all-depth orientation of the actual prime--Gamma comparison
anomaly.  It rules out the possibility that higher Gamma jets introduce arbitrary sign changes.

It does not yet close RH.  The remaining mathematical bridge is a reduced Gauss--Ward boundary
identity: after the causal/polar subtraction at the Euler unit boundary, the positive finite
anomaly response must be shown to equal the inverse-tilted completed prime--Gamma germ, or its
finite Hankel jets.  Assuming that equality from reconstruction or source-effectivity would be
circular.

## Lean certificate

The wired module proves:

- `expNegTruncPoly_sub_exp_oriented_pos`;
- `finiteExponentialGammaAnomaly_singleton_zero_apply`;
- `finiteExponentialGammaAnomaly_singleton_apply_eq_zeroAtom`;
- `finiteExponentialGammaAnomaly_singleton_oriented_re_eq`;
- `finiteExponentialGammaAnomaly_singleton_oriented_re_pos`;
- `finiteExponentialGammaAnomaly_singleton_zero_oriented_re_pos`;
- `finiteVonMangoldtWeight_eq_ofReal`;
- `finiteVonMangoldtGammaAtom_oriented_re_pos`;
- `finiteVonMangoldtGammaAtom_zero_oriented_re_pos`.

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.  Its direct check and exact
targeted build pass.  The displayed declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Proof chain

```text
resolved von Mangoldt positivity + exact Gamma Taylor remainder
  -> all-depth common anomaly orientation
  -> [OPEN] positive reduced Gauss--Ward source Gram
  -> [OPEN] inverse-tilted completed moment-jet comparison
  -> complete prime--Gamma Hankel cone
  -> RH.                                                  (4)
```

## Gates

- [x] identify the scalar anomaly with the omitted Taylor tail
- [x] prove strict alternating orientation at every positive depth
- [x] prove the residual-depth factorization and common sign for every jet coordinate
- [x] specialize to actual resolved von Mangoldt mass and logarithmic frequency
- [x] wire, target-build, and audit axioms
- [ ] extend the source response from scalar atoms to the reduced finite Gauss--Ward packet
- [ ] prove the Euler-boundary causal/polar cancellation
- [ ] compare the reduced packet with inverse-tilted completed prime--Gamma moment jets
- [ ] RH
