# Hedenmalm theta anomaly: Burnol covariant aggregation no-go

- **Label:** `P-G122`
- **Route:** P
- **Parents:** `P-G118`, `P-G121`; prior walls `P-G58` and `BurnolAllPrimeCompletionWall`
- **Status:** no-go theorem and anomaly survivor proved in Lean

## Corpus gate

Naive all-prime positive completion is already closed: the inverse-completed Cartier row has a
sharp `ell^2` wall, and off-center nonlinear information has a nonsummable reciprocal-prime lower
bound.  Repeating either divergence theorem would add no knowledge.

## Conjecture tested

P-G121 gives `J_i(z)=-z E_i(z)` for every valid factorization frame.  Test whether aggregation or
scalar renormalization can create new curvature.  For every finite family with arbitrary complex
weights,

```text
J_S(z)=sum_i w_i J_i(z) = -z sum_i w_i E_i(z) = -z E_S(z).
```

If a scalar counterterm `C` is subtracted from mass while covariance is retained, its numerator
counterterm should be uniquely forced to `zC`:

```text
J_S + K = -z(E_S-C)  iff  K=zC.
```

Therefore every nondegenerate covariance-preserving finite renormalization should still normalize
to exactly `z`, independent of family, weights, and counterterm.

## Scientific decision gate

- **Success:** close the complete finite linear/covariant-renormalization class.  Positive
  aggregation cannot manufacture an RH-selecting law; any successful completion must carry a
  source-derived noncovariant orientation anomaly or channelwise boundary condition.
- **Failure:** isolate cross-factorization curvature and test it as a new signed producer.
- Formal target must prove aggregate identity, counterterm uniqueness, normalized reconstruction,
  and independence between arbitrary finite presentations.

## Verification log

- 2026-08-13 — Card opened only after checking the existing all-prime completion and information
  divergence walls; theorem is deliberately orthogonal to those summability results.
- 2026-08-13 — Direct `lake env lean` passed for
  `HedenmalmThetaAnomalyBurnolCovariantAggregationNoGo.lean`.
- 2026-08-13 — Exact module build passed: `[12942/12942]`.
- 2026-08-13 — `#print axioms` on aggregate, rigidity, anomaly quotient, normalized connection,
  and presentation-independence capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-13 — Full `GaloisForLFunctions.RHTower` umbrella build passed: `[19802/19802]`.

## Result and positive survivor

Conjecture is true.  Arbitrary complex finite weights—not only positive weights—preserve

```text
J_S(z) = -z E_S(z).
```

Mass subtraction `E_S-C` preserves this line exactly iff numerator counterterm is `zC`; Lean proves
uniqueness.  For arbitrary `K`, define anomaly `A=K-zC`.  Exact adjusted connection is

```text
z - A/(E_S-C).
```

Thus family size, signed weights, repeated-frame multiplicity encoded in weights, and covariant
scalar renormalization are all presentation artifacts.  Strongest positive survivor is a sharp
classification: every possible new selector in this class is precisely a noncovariant anomaly.
Route P must derive that anomaly from completed source orientation or impose channelwise boundary
flatness before Hermitian aggregation; it cannot emerge from aggregation itself.
