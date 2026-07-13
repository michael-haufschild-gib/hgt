# Shape-blind cycle deletion forces the geometric/Ewens class

- **ID:** `prime-cycle-deletion-geometric-coherence`
- **Stage:** 3-formalized
- **Type:** `THEOREM (Lean) / [NO-GO] [POSITIVE MAXIMAL CLASS] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeCycleDeletionCoherence.lean`
- **Consumer:** `../../1-in-progress/prime-power-ewens-cycle-index-young-rh.md`

## Theorem

Let `r_k` be the relative weight for inserting a distinguished label into a cycle of length `k`.
For a positive cycle shape with parts `lambda`, define

```text
S_r(lambda)=sum_(k in lambda) k r_k.
```

Lean proves

```text
S_r(lambda) depends only on the total size |lambda|
  <-> r_k=r_1 for every k>=1.
```

The forward proof compares the one-part shape `[k]` with the all-singleton shape `[1^k]`; the
reverse proof sums the constant ratio against the total size.

If nonzero multiplicative cycle weights satisfy `r_k=w_(k+1)/w_k`, Lean then proves

```text
w_k=w_1 (w_2/w_1)^(k-1),       k>=1.
```

## Positive meaning

This is not only a no-go for arbitrary scalar prime-power cycle weights.  It classifies the entire
surviving uncolored projective family: up to the rankwise geometric normalization, it is the
Ewens class.  A nongeometric completed source must retain an additional latent prime or
archimedean color through deletion; scalar cycle shape is provably too small a state space.

## Formal declarations

- `cycleDeletionShapeScore`;
- `CycleDeletionShapeBlind`;
- `cycleDeletionShapeBlind_iff_constant_ratio`;
- `cycleWeight_eq_geometric_of_constant_ratio`;
- `cycleWeight_eq_geometric_of_shapeBlind`.

The exact module build is green.  Axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] deletion lift score defined
- [x] shape blindness classified exactly
- [x] geometric weight consequence formalized
- [x] no-go converted into the maximal coherent positive class
- [x] accepted-axiom audit
