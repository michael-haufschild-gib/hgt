# Burnol graph-action filtration

- **ID:** ULF-BGAF-001
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) · dynamic source bridge
- **Source:** `ULF-BGCA-001` · `RoutePPrimitiveBurnolApertureDampingSemigroup` ·
  `RoutePPrimitiveBurnolMatrixCompleteColligation`
- **Statement:** Forward Burnol aperture damping contracts the full prime-mixed graph cap through a
  canonical monotone determinant-line action filtration of total mass `<1`.

## Provenance

- `[CORPUS]` `routePBurnolForwardDampingShift_add` is the forward semigroup law.
- `[CORPUS]` `routePBurnolApertureEnergy_forwardDampingShift_le` is its `L2` contraction law.
- `[CORPUS]` `routePBurnolForwardDampingShift_primitiveFeature` diagonalizes every literal
  prime/depth column at its complex prime-log frequency.
- `[CORPUS]` `routePPrimitiveBurnolWindowGramMatrix_eq_sum_channelGrams` and
  `routePPrimitiveBurnolApertureTransportedGram_loewnerLE_source` retain every finite cross-prime
  matrix coefficient and express the Loewner loss as two positive defect Grams.
- `[PROVED HERE]` The nonlinear determinant-line action remains monotone, tends to zero, and
  defines an exact additive filtration whose total action is the graph-cap area `<1`.

## 1. Abstract theorem

Let `H_+`, `H_-` be complex Hilbert spaces, let `A:H_+ -> H_-` be Hilbert--Schmidt, and let
`(S_c)_(c>=0)` be a contraction semigroup on `H_-`.  Put

```text
A_c = S_c A,
K_c = A_c* A_c,
E(c) = Tr(K_c(I+K_c)^(-1)).                           (BGAF.1)
```

Assume `||A_c||_HS -> 0` as `c -> infinity`.

**Theorem BGAF-A.** For `0<=c<=d`:

```text
0 <= K_d <= K_c,
0 <= E(d) <= E(c),
E(c) -> 0.                                             (BGAF.2)
```

The interval action

```text
Action(c,d) = E(c)-E(d)                               (BGAF.3)
```

is nonnegative and exactly additive:

```text
Action(c,e)=Action(c,d)+Action(d,e),  c<=d<=e.         (BGAF.4)
```

Its total mass is

```text
Action(0,infinity)=E(0)
  = Area_det(z -> graph(zA))
  <= ||A||_HS^2.                                      (BGAF.5)
```

**Proof.** Write `h=d-c`.  The semigroup law gives `A_d=S_h A_c`.  Since `S_h` is a
contraction,

```text
K_c-K_d=A_c*(I-S_h* S_h)A_c >= 0.                    (BGAF.6)
```

For positive operators, `f(t)=t/(1+t)=1-(1+t)^(-1)` is operator monotone.  Indeed, inversion
reverses the Loewner order, so `K_d<=K_c` implies

```text
(I+K_c)^(-1) <= (I+K_d)^(-1),
f(K_d) <= f(K_c).
```

Both terms are positive trace class because `0<=f(K_c)<=K_c`.  Taking traces proves monotonicity
of `E`.  Also

```text
0 <= E(c) <= Tr K_c = ||A_c||_HS^2 -> 0.
```

Equations `(BGAF.3)`--`(BGAF.4)` are algebraic telescoping, and the limit gives `(BGAF.5)` using
`ULF-BGCA-001`.  QED.

The same proof gives the exact nonlinear finite-interval identity

```text
f(K_c)-f(K_d)
  = (I+K_d)^(-1)(K_c-K_d)(I+K_c)^(-1),               (BGAF.7)
```

where the right side is read as a resolvent identity; its trace is nonnegative by the already
proved Loewner order.  This records how positive quadratic Gram loss is converted into the
nonlinear graph action without discarding the full operator.

## 2. Arithmetic specialization

Take

```text
A = A_base = routePPrimitiveBurnolBaseSynthesis,
S_c = routePBurnolForwardDampingShift(c),
A_c = S_c A_base.
```

The semigroup and contraction hypotheses are corpus theorems.  The pointwise forward shift extends
uniquely from the continuous finite-energy core to a
contraction on the half-line `L2` space: the corpus energy inequality gives boundedness and the
core is dense.  Its almost-everywhere semigroup law extends by continuity.  Each zero-clock
prime/depth column is an eigenvector:

```text
S_c f_pe = exp(-c log(n_pe)) f_pe.                    (BGAF.8)
```

Therefore

```text
||A_c||_HS^2
  = sum_pe routePPrimitiveBaseCauchyCubicWeight(pe)
      * exp(-2c log(n_pe))
  -> 0,                                               (BGAF.9)
```

by dominated convergence, because every `n_pe>=2` and the undamped weights are summable.  BGAF-A
applies and gives

```text
0 <= E_base(d) <= E_base(c) <= E_base(0) < 1,
Action_base(0,infinity)=E_base(0)<1.                  (BGAF.10)
```

This filtration is prime-mixed at operator level.  For every finite packet the exact corpus
colligation says

```text
K_c-K_d
  = Gram(boundary defect) + Gram(tail-cocycle defect), (BGAF.11)
```

including all off-diagonal prime/depth/clock pairings.  Diagonalization of individual columns is
not a direct-sum decomposition of the Gram.

## 3. Interpretation

The source cap is not a static scalar budget.  Burnol time contracts it to the vacuum through a
one-sided path whose determinant-line action can only decrease.  Backward time is singular in the
corpus, so this path has a genuine arrow and a sharp formation wall.

This supplies the source half of a filtered Floer/Maslov mechanism:

```text
Burnol forward time        = monotone action filtration,
determinant-line curvature = bulk action density,
cubic projection trace     = candidate Maslov/Schubert boundary charge.
```

No Floer complex is asserted here.  `ULF-TSBC-001` must construct a theta completion
correspondence that respects this filtration.  If it does, an index-one completion event needs one
action unit but the entire source trajectory carries less than one.

## 4. Limits and falsifier

BGAF-A proves only source monotonicity.  It does not show that theta completion is symplectic,
pseudoholomorphic, or filtration-nonincreasing.  A map sending the source path to a target path
while injecting extra action would make the theorem irrelevant.

The next bridge must therefore be stronger than equality of endpoints:

```text
Action_target(completion event)
  <= Action_base(source interval).                    (BGAF.12)
```

at matrix-complete cyclic degree three.  If no coefficient-native theta correspondence satisfies
`(BGAF.12)`, the filtered mechanism fails while BGAF-A remains a source theorem.

## 5. Audit status

- Paper dependencies: closed.
- Lean status: intentionally pending; current task phase forbids Lean work.
- RH status: no claim.
- New narrowing: completion transport must be a monotone filtered correspondence, not an
  arbitrary stable sewing.

## Log

- 2026-09-03 — `[PROVED HERE]` monotone graph action, exact additive filtration, and Burnol
  specialization.
