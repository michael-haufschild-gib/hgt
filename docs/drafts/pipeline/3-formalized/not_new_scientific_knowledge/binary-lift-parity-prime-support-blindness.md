# Binary graph lifts are blind to the full prime-support boundary germ

- **ID:** `binary-lift-parity-prime-support-blindness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NO-GO] [POSITIVE SUCCESSOR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeSupportLiftParityNoGo.lean`
- **Consumer:** `../../1-in-progress/prime-source-ramanujan-lift-ihara-limit-rh.md`

## Theorem

A binary `2`-lift signing sees an edge word only through the parity of every edge multiplicity.
For two labels, compare the multiplicity packets

```text
m=(1,0),        m'=(1,2).
```

For every binary signing `sigma` with `sigma_i^2=1`,

```text
prod_i sigma_i^(m_i)=prod_i sigma_i^(m'_i).
```

Nevertheless `m` has distinct-support cardinality one and `m'` has distinct-support cardinality
two.  The prime-support boundary jets separate them exactly:

```text
J_0(1)=1,  J_0(2)=0,
J_1(1)=0,  J_1(2)=-2.
```

Thus no family of ordinary binary signing characters can carry the full support-cardinality germ
formalized in `PrimeSupportBoundaryJets.lean`.

## Positive successor

The graph route is not killed.  The correct finite carrier must retain edge labels before parity
specialization.  Viable replacements are:

1. a multivariate edge-Ihara zeta whose monomials retain complete edge multiplicities;
2. a squarefree support marking applied before specializing the edge variables to lift phases; or
3. higher cyclic lifts together with a full character packet and a marked derivative that recovers
   distinct support.

Only after the marked support germ has been extracted may one specialize to a unitary lift
character and apply a Ramanujan/interlacing theorem.

## Formal certificate

The module proves:

- `binaryLiftCharacter_support_blind`;
- `singletonLiftMultiplicity_supportCard`;
- `doubledSecondLiftMultiplicity_supportCard`;
- `binaryLiftCharacter_blind_but_boundaryJets_separate`.

The exact module builds.  The result is elementary parity algebra and boundary-jet evaluation, so
it is classified as a formal route boundary rather than new science.

## Gates

- [x] parity-blind pair constructed
- [x] signing-character equality proved for every binary signing
- [x] support-cardinality separation proved
- [x] boundary-jet separation proved
- [x] positive multivariate/marked successor stated
- [x] exact Lean build

