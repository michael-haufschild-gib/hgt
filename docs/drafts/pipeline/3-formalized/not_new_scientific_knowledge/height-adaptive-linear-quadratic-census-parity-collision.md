# Height-adaptive linear--quadratic census/parity collision

- **ID:** `height-adaptive-linear-quadratic-census-parity-collision`
- **Stage:** 3-formalized
- **Type:** `[LARGE OUTLANDISH DETOUR] [PROVED BRIDGE] [NOT AN RH PROOF]`
- **Scientific status:** not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHeightAdaptiveLinearQuadraticCensusCollision.lean`
- **Inputs:** `quadratic-reflection-anomaly-rh.md`, `marked-support-quadratic-diagonalization.md`,
  `multiplicity-parity-ladder-route.md`, `height-adaptive-finite-rh-ladder.md`

## Claim

For right-half Xi multiplicities `m_z>0` in a bounded box, put

```text
M(T)=sum_z m_z,   Q(T)=sum_z m_z^2,
E(T)=Q(T)-M(T)=sum_z m_z(m_z-1).
```

Choose one dyadic modulus above the square of the unconditional Xi zero-count envelope.  If
`Q(T)=M(T)` in that finite ring, then the modulus divides `E(T)`, while

```text
0 <= E(T) <= Q(T) <= M(T)^2 < 2^k.
```

Thus `E(T)=0` and every enclosed zero is simple.  An independently sourced `RHLadder 1` makes every
right-half multiplicity even.  No positive multiplicity is both one and even, so integer-height
exhaustion proves RH.

## Positive weakening

The quadratic reflection-anomaly route tries to annihilate the full quadratic circle charge.  This
chain asks only that the marked quadratic boundary census equal the linear SEM contour census in
one finite ring per height.  It may admit arbitrary simple off-line zeros.  Conversely, the first
ladder rung may admit arbitrary even-multiplicity off-line zeros.  Their collision is what proves
RH.

Lean proves the decomposition and bounds as `boxSquareOrderSum_eq_order_add_excess` and
`boxSquareOrderSum_le_sq_boxOrderSum`, the exact simplicity criterion as
`boxSquareOrderSum_eq_boxOrderSum_iff_all_simple`, and the RH capstone as
`riemannHypothesis_of_rhLadder_one_of_xiNatHeightAdaptiveLinearQuadraticCensus`.

## No-go and open cores

At modulus two, `m^2=m` is automatic, so a fixed parity comparison is blind.  The modulus must grow
above the squared source-independent envelope.  Constructing `Q` after reading Xi multiplicities is
also circular: it must come from the integral completed-flux incidence square and the marked
component complex before divisor extraction.

- `[OPEN CORE A]` Construct the source linear--quadratic finite-ring comparison on every integer
  window.
- `[OPEN CORE B]` Supply `RHLadder 1` independently, not as a consequence of the same census.

## Gates

- [x] finite quadratic diagonalization
- [x] height-adapted simplicity theorem
- [x] simplicity/parity RH collision
- [ ] source linear--quadratic comparison
- [ ] independent first ladder rung
- [ ] RH
