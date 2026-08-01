# Hedenmalm source Hilbert-Gram closed-graph no-go

- **ID:** `hedenmalm-source-hilbert-gram-closed-graph-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE-C1 OPERATOR-CLOSURE NO-GO
- **Scientific status:** `[PROVED] [FORMALIZED] [SOURCE-SPECIFIC COROLLARY]`
- **Direct parent:** H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*,
  arXiv:2606.17494 (2026)

## Closed question

Can Hedenmalm's missing positive form be obtained as the Gram pullback of a nonzero Hilbert-space
map on the full theta Schwartz source core, with either the exact source line as kernel or a
closable graph in ordinary `L²(R)`?

## Setup

Let

```text
S = Schwartz(R,C),
i:S -> L²(R),
k = normalized completed theta source,       Fourier(k)=Xi,
J:S -> H,
```

where `H` is a complex Hilbert space and `J` is complex-linear.  Let `Q` be a jointly
Schwartz-continuous sesquilinear form satisfying

```text
Q(u,v)=<Jv,Ju>_H,                              (1)
Q(Du,v)=Q(u,Dv),                               (2)
Jk=0,                                          (3)
J!=0.                                          (4)
```

The order in `(1)` matches the convention that `Q` is linear in its first argument.  Let `T` be
any partially defined linear operator from `L²(R)` to `H` whose domain contains `i(S)` and which
realizes `J` there:

```text
T(iu)=Ju  for every u in S.                    (5)
```

No boundedness, closedness, density assertion beyond `(5)`, spectral enumeration, RH, or
simplicity is assumed.

## Theorem

Under `(1)`--`(4)`:

1. `Q` is nonnegative and Hermitian;
2. the algebraic left radical of `Q` is exactly `ker J`;
3. `ker J` cannot equal the one-dimensional source line `Ck`;
4. every partial operator `T` satisfying `(5)` is nonclosable;
5. the unique positive temperate spectral measure representing `Q` is a nonzero atomic measure
   supported on the real Xi divisor, while the ordinary-`L²` image of `ker J` is dense, proper,
   and nonclosed.

Consequently no nonzero positive pair-symmetric Hilbert Gram realization on the full theta
Schwartz core is both source-faithful modulo `Ck` and compatible with a closed or closable
ordinary-`L²` graph.

## Proof

### 1. Positivity and exact Gram radical

Equation `(1)` gives

```text
Q(u,u)=||Ju||²,
```

so `Q` is nonnegative and therefore Hermitian.  If `Ju=0`, then `(1)` gives `Q(u,v)=0` for every
`v`, hence `u` belongs to the left radical.  Conversely, if `u` is in the left radical, taking
`v=u` gives `||Ju||²=0`, so `Ju=0`.  Thus

```text
leftRadical(Q)=ker J.                           (6)
```

Since `J!=0`, some diagonal value `Q(u,u)` is nonzero.

### 2. Theta nullity propagates to a dense radical

Equation `(3)` and `(1)` make `k` a left-radical vector.  Momentum symmetry `(2)` exponentiates
to simultaneous real-translation invariance.  Therefore every real translate of `k` lies in the
left radical.  Since `Fourier(k)=Xi` and the real zero set of the nonzero entire function `Xi` has
Lebesgue measure zero, the real-translation orbit of `k` is cyclic in ordinary `L²(R)`.  Hence

```text
closure(i(ker J))=L²(R).                        (7)
```

Nonzeroness of `Q` makes `i(ker J)` proper: otherwise injectivity of the Schwartz-to-`L²` map and
`(6)` would force every value of `Q` to vanish.  Thus `i(ker J)` is dense, proper, and nonclosed.

The image `i(Ck)` is one-dimensional and closed.  Equations `(6)`--`(7)` therefore rule out

```text
ker J=Ck.                                       (8)
```

This proves the source-faithful Hilbert-Gram obstruction without a divisor or RH assumption.

### 3. Singular sequence

Choose `u` with `Q(u,u)!=0`.  Cyclicity of the radical orbit produces a sequence `z_n` in `S`
such that

```text
i(z_n) -> 0 in L²,
Q(z_m-z_n,z_m-z_n)=0 for all m,n,
Q(z_n,z_n)=Q(u,u) for all n.                    (9)
```

By `(1)`, the middle identity says

```text
||Jz_m-Jz_n||²=0,
```

so `Jz_n=y` is constant.  The last identity in `(9)` gives `||y||²=Q(u,u)!=0`, hence `y!=0`.

### 4. Closed-graph contradiction

By `(5)`, every pair `(i(z_n),y)` belongs to the graph of `T`.  Equation `(9)` gives

```text
(i(z_n),y) -> (0,y).
```

Thus `(0,y)` belongs to the closure of the graph.  If `T` were closable, this closure would be the
graph of a single-valued partial linear operator.  A linear graph has only `(0,0)` over its zero
input, so it would force `y=0`, contradicting the preceding paragraph.  Therefore `T` is not
closable.

### 5. Positive survivor

The positive Bochner--Schwartz representation of `Q`, `(2)`, and `(3)` give a unique positive
temperate measure `mu` with

```text
Q(u,v)=integral hat(u)(t) conjugate(hat(v)(t)) dmu(t),
integral |Xi(t)|² dmu(t)=0.
```

Positivity forces `supp(mu)` into the real Xi zero set; discreteness makes `mu` atomic.  Since
`Q` is nonzero, `mu` is nonzero.  This is the complete surviving source-core class.  It is
necessarily singular and nonclosable, and its Fourier samples annihilate every off-real-zero
Hedenmalm eigenprofile.  Conservativity on the full eigenfamily remains exactly the
RH-and-simplicity-bearing condition.

## Route-C1 subroute consequence

The advertised full-source construction is exhausted in its natural distributional category:

```text
continuous positive pair-symmetric source form
  -> unique real-divisor atomic rigging
  -> dense proper ordinary-L² radical
  -> no faithful Ck quotient
  -> no closable Hilbert Gram graph.
```

A form restricted to Hedenmalm's finite zero-eigenfunction span is not covered, exactly as in the
parent paper.  Such a target-domain form must first prove source-defined domain selection and
conservativity.  Existing divided-source and Xi-Weil closure theorems show that this surviving
faithfulness/orientation assertion is equivalent to RH (and, at second divided level, simplicity),
not a low-cost regularity lemma.  It nevertheless remains an unproved source-construction problem.
Because no other frontier route owns the exact singular boundary-null construction, it is retained
as Route C1's open survivor in
`../../1-in-progress/burnol-hedenmalm-boundary-null-graph-completion-rh.md`.

The exact formalized survivor inside the classified full-source category is the singular
real-divisor Fourier rigging together with its dense nonclosed radical law.  It remains useful as a
classification theorem and as a falsifier for future Hilbert--Pólya proposals, but it does not
prove RH.  At route level, its topology boundary exposes the still-open source-defined singular
Burnol--Hedenmalm completion.

## Hostile audit

1. **No RH smuggling.**  Every statement above is unconditional.  No zero is assumed real or
   simple.
2. **No target-fed construction.**  The no-go starts with a full Schwartz-source Gram map and
   derives divisor support; it does not choose weights after listing zeros.
3. **No continuity overclaim.**  Only `Q` is Schwartz-continuous.  `J` may be discontinuous in
   both Schwartz and ordinary-`L²` topologies.  The theorem proves that any ordinary-`L²` partial
   graph realizing it is nonclosable.
4. **No finite-span overclaim.**  Hedenmalm's `H_finite` escape is stated explicitly and is not
   ruled out.  Its source-defined singular completion is retained as Route C1's open core.
5. **No generic-functional-analysis novelty claim.**  The graph fact is standard.  New content is
   its exact coupling to theta cyclicity, scalar theta nullity, and the Hedenmalm pair.
6. **No repackaging credit.**  The real-divisor measure classification and dense-radical law are
   prior project theorems.  Scientific increment here is the arbitrary-Hilbert-target
   closed-graph consequence and exact Route-C1 boundary.

## Primary-literature audit

Hedenmalm's v1 preprint of 16 June 2026 defines the candidate form only on the finite span of zero
eigenfunctions and asks for a Hilbert form making `(L D,L)` self-adjoint.  It proves that a
positive-definite realization would exclude nonreal zeros, but it does not construct a form,
extend it to a Schwartz source core, classify its measure, or study ordinary-`L²` closability.
Targeted arXiv searches through 1 August 2026 found no follow-up proving the source-core Gram or
closed-graph statements above.  Priority remains provisional because the parent preprint is new.

Primary source:

- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*,
  [arXiv:2606.17494](https://arxiv.org/abs/2606.17494), especially Theorem 3.3.3,
  Definition 4.2.1, Theorem 4.2.2, and Corollary 4.2.3.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/HedenmalmSourceHilbertGramClosedGraphNoGo.lean` proves:

1. `LinearPMap.IsClosable.eq_zero_of_tendsto_graph`;
2. `hilbertGram_leftRadical_eq_ker`;
3. `hilbertGram_kernel_ne_thetaSourceLine`;
4. `hilbertGram_l2PartialOperator_not_closable`;
5. `hilbertGram_nonzero_thetaNull_temperedDenseRadicalLaw`.

Every theorem is unconditional. The leaf is imported by the `RHTower` umbrella. Per-file Lean,
the `/tmp` axiom-audit file, and the single targeted leaf build pass. The repository-wide formal
lint recognizes this leaf as reachable and reports no forbidden declaration in it, but exits on
unrelated concurrently added umbrella-unreachable modules (`BVCoPoisson*`,
`DeningerHermitianCriticalMeasure`, `MobiusExponentialGibbsBoundary`,
`XiCTaylorAnisotropicGaugeCharge`, and `JetPolyCoeffDatum`). No full or umbrella build was run.
Every headline `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] paper proof dependency-closed
- [x] full-source and finite-target categories separated
- [x] exact positive survivor retained
- [x] primary-source audit through 1 August 2026
- [x] generic partial-operator closure infrastructure in Lean
- [x] source-specific Hilbert-Gram no-go in Lean
- [x] axiom, lint, and targeted leaf-build audit
