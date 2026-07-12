# Finite full-rank evaluation packet

- **ID:** `finite-full-rank-evaluation-packet`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [BRIDGE]`
- **Lane:** coefficient-uniform relation detection; finite evaluation geometry
- **Statement:** Every finite linearly independent family of complex-valued functions admits a
  square finite evaluation packet with invertible evaluation matrix, so one packet excludes all
  nonzero coefficient vectors simultaneously.

## The theorem

Let `f_0,...,f_(n-1):X→C` be linearly independent over `C`.  Then the evaluation vectors

```text
ev_x=(f_0(x),...,f_(n-1)(x)) in C^n
```

span `C^n`.  Consequently there are points `x_0,...,x_(n-1)` for which

```text
A_(a,i)=f_i(x_a)
```

is invertible.  Equivalently,

```text
forall c in C^n,
  [forall a, sum_i c_i f_i(x_a)=0] implies c=0.              (1)
```

The proof of spanning is coefficient-uniform.  A linear functional annihilating every evaluation
vector gives a finite coefficient vector whose linear combination of the functions vanishes on
all of `X`; independence forces that functional to be zero.  Finite-dimensional basis extraction
then selects exactly `n` evaluation vectors, and row independence makes their matrix a unit.

## Positive law

> **Finite coefficient-uniform detectability.** Finite functional independence is always witnessed
> by one finite square packet, and that packet detects every coefficient vector at once.

This is the correct finite geometry for differential algebra over `C(z)`.  A Baire construction
cannot enumerate the uncountably many complex coefficient vectors.  It must instead enumerate only
the countably many finite monomial patterns, jet orders, and coefficient-degree bounds, assigning
one full-rank evaluation condition to each pattern.

For the prime-log HT route, this law is now instantiated with the expanded functions

```text
(z,x) |-> z^d M_beta(x)
```

for distinct differential monomials `M_beta`.  `ExpandedMonomialEvaluation` chooses the evaluation
points in a noncolliding upper-half-plane translated-node configuration;
`CoefficientUniformJetEscape` transports full rank through simultaneous Cauchy-jet control; and
`BoundedGaugeContinuity` plus `BoundedGaugeGenericity` prove that the resulting actual-derivative
rank-defect locus is closed and nowhere dense in the complete bounded-gauge space.

## Lean certificate

`GaloisForLFunctions.HTGeometry.FiniteEvaluationPacket` proves:

- `span_evaluationVectors_eq_top`;
- `exists_fullRank_evaluation_packet`;
- `coefficients_eq_zero_of_fullRank_evaluation_packet`.

The module builds unconditionally.  All three theorems have only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `admit`, project axiom, opaque
postulate, or unsafe declaration.

## Classification

This is classical finite-dimensional linear algebra and therefore a bridge, not new scientific
knowledge.  Its role is structural: it identifies and formalizes the coefficient-uniform geometry
that the candidate-new facet-sewn HT realization requires.

## Gates

- [x] 0 → 1: coefficient-uniform finite detector isolated
- [x] 1 → 2: complete unconditional paper proof
- [x] 2 → 3: spanning, square packet extraction, and all-coefficient detection formalized
- [ ] 3 → 4: no standalone publication planned; classified as a bridge
