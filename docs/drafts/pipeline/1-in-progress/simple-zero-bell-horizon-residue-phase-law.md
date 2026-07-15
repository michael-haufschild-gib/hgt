# The simple-zero Bell horizon and the residue-rank phase law

- **ID:** `simple-zero-bell-horizon-residue-phase-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / NOVELTY AUDIT IN PROGRESS
- **Scientific status:** `[LEAN-PROVEN: UNIVERSAL AND RECIPROCAL-GAMMA ANALYTIC CLASSIFICATION] [NOVELTY UNVERIFIED]`
- **Methods:** symbolic proof and Lean verification only; no numerical computation
- **Statement:** For a logarithmic derivative with a free simple-zero boundary, the differential polynomials having at most simple poles are exactly the affine span of the complete Bell covariant jets.

## Goal

Let `G` be holomorphic with a simple zero and put `g=G'/G`.  The complete Bell covariant jets

```text
Z_k = B_k(g,g',...,g^(k-1)) = G^(k)/G,       k >= 1,
```

all have at most a simple pole.  The target classification is the converse: subject to an exact
algebraic-freeness condition on the nonconstant zero jets of `G`, a constant-coefficient
differential polynomial in `g` has at most a simple pole at the whole boundary tower if and only if
it belongs to

```text
C + span_C {Z_1,Z_2,...}.
```

The theorem is a static boundary constraint, not a flow.  It is intended to distinguish a
constant-residue logarithmic phase from the factorial residue-scale phase of Gamma.

The universal theorem and the reciprocal-Gamma analytic realization now have unconditional Lean
proofs.  No paper claim may be promoted until the parent-theory and significance gates are also
cleared.

## Candidate theorem

Fix a finite jet height `N`.  In covariant variables `Z_1,...,Z_N`, the principal simple-zero pole
profile is

```text
Z_1 |-> T,
Z_k |-> T R_k       (2 <= k <= N),
```

where `R_2,...,R_N` are independent zero-boundary jets.  For every nonzero polynomial `Q`, the
profile has exact `T`-degree

```text
deg_T Q(T,T R_2,...,T R_N) = totalDegree(Q).                 (1)
```

The nontrivial point is that specializing the residue of `Z_1` to `1` remains injective on each
homogeneous sector: the missing exponent is recovered from the known total degree.  Equation `(1)`
would give the complete covariant-horizon classification

```text
deg_T profile(Q) <= 1  iff  totalDegree(Q) <= 1.              (2)
```

The triangular complete-Bell transformation

```text
(g,g',...,g^(N-1)) <-> (Z_1,...,Z_N)                         (3)
```

must then be proved to be a polynomial automorphism, not merely injective on the coordinate ring.
Pulling `(2)` back through `(3)` gives the claimed nonlinear raw-jet horizon.

## Physical and geometric interpretation

`g` behaves as a one-dimensional logarithmic connection and `G` as its section.  The Bell change
of variables is a gauge change from raw connection jets to covariant section jets.  Pole order is a
boundary-energy filtration.  The simple-zero boundary permits vacuum plus one covariant insertion,
even though it permits nonlinear combinations in raw connection coordinates such as `g'+g^2`.

This is mathematical terminology only.  No quantum dynamics, spacetime model, black-hole entropy,
or empirical physical identification is asserted.

## Counterattacks and anti-theatre gate

1. The isolated Riccati cancellation `g'+g^2=G''/G` is classical and is not new knowledge.
2. Bell's identity `B_k(g,...)=G^(k)/G` is classical and is not new knowledge.
3. A finite triangular coordinate change plus degree filtration may be routine commutative algebra.
   Novelty, if any, must lie in the complete filtered classification for natural
   hypertranscendental carriers and in a nontrivial residue-phase invariant, not in its vocabulary.
4. Multiple zeros change the residue of `g` and may collapse or enlarge the boundary algebra.
   The theorem must state multiplicity assumptions exactly.
5. Algebraic relations among the zero jets can cancel the top pole trace.  Bulk
   hypertranscendence alone does not imply boundary freeness.
6. Differential-rational expressions lie outside the polynomial horizon and supply immediate
   counterexamples if the algebra is stated too broadly.

## Natural examples under attack

- `G=1/Gamma`, so `g=-digamma`.  Reciprocal Gamma is entire with simple zeros on the nonpositive
  integers.  After factorial normalization, its actual zero-boundary derivative ratios are
  algebraically independent in the eventual branch-germ ring.  The analytic tower theorem is now
  proved without assumptions: every nonzero covariant polynomial realizes pole order equal to
  minus its total degree on branches arbitrarily far out, and the raw at-most-simple horizon is
  exactly the complete-Bell image of the affine covariant sector.
- Solutions of linear differential equations provide Bell coordinates but are normally
  differential-algebraic, hence are control examples rather than hypertranscendental examples.
- Completed `L`-functions would make the same coordinate system at simple zeros, but zero
  simplicity and boundary freeness are not unconditional and therefore cannot be used as theorem
  hypotheses in a claimed RH application.

## RH impact audit

No direct RH consequence is presently claimed.  If the completed zeta function had a simple and
free zero boundary, the theorem would classify polynomial logarithmic-derivative surgeries that
preserve the simple-pole horizon.  Neither premise is known unconditionally, so this is only a
diagnostic of what an RH source would need, not an RH result.

## Lean completion target

The required unconditional formal chain is:

1. exact homogeneous dehomogenization injectivity after setting one residue coordinate to `1`;
2. exact equality between profile degree and multivariate total degree for every nonzero finite
   polynomial;
3. the degree-one covariant-horizon iff classification;
4. a polynomial inverse, hence automorphism, for the finite complete-Bell substitution;
5. the pulled-back raw-jet classification;
6. for every natural example claimed, the complete analytic pole-profile and boundary-freeness
   bridge in Lean.

Items 1--6 are complete for reciprocal Gamma.  The relevant modules are:

- `SimpleZeroBellHorizon.lean`: exact degree law, homogeneous chart faithfulness, and polynomial
  Bell automorphism;
- `GammaSimpleZeroBellHorizon.lean`: actual reciprocal-Gamma derivative-ratio identification and
  algebraic independence;
- `GammaSimpleZeroBellHorizonAnalytic.lean`: normalized leading limits, exact meromorphic orders,
  cofinal detection, and complete covariant/raw tower classifications.

The two capstones are
`gammaSimpleZeroCovariantTowerAtMostSimple_iff` and
`gammaSimpleZeroRawTowerAtMostSimple_iff_exists_bellAffine`.  Their axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`.  The formal lint gate passes.

## Gates

- [x] 0 -> 1 in-progress: well-posed finite theorem, attack idea, counterexamples identified
- [x] exact algebraic classification survives proof and countermodel search
- [x] Bell substitution proved polynomially invertible in Lean
- [x] reciprocal-Gamma example proved end to end in Lean
- [ ] at least one further natural hypertranscendental phase is proved, not merely postulated
- [ ] primary parent-theory and priority audit completed
- [ ] residue-rank invariant shown to classify more than renamed coordinate changes
- [x] RH nonconsequence re-audited after the reciprocal-Gamma theorem
- [ ] dual novelty-significance gate cleared
- [ ] Fields-Medal gate cleared

## Current scientific boundary

The reciprocal-Gamma theorem is formal mathematical content, but the Fields-Medal gate is not
cleared.  Bell identities, simple-pole order filtrations, projective dehomogenization, and
triangular polynomial changes are individually classical.  The exact all-orders tower
classification and its cofinal Gamma realization still require a primary-source priority audit and
a comparison with the strongest local differential-polynomial/value-distribution results.  A
second natural hypertranscendental residue phase is also required before proposing a general phase
theory rather than a single-source theorem.
