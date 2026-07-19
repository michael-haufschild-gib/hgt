# Xi transverse valuation--Szegő true-aperture metric

- **ID:** `xi-transverse-valuation-szego-true-aperture-metric`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / positive completion of the raw valuation-layer collapse
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW STRUCTURAL KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `xi-transverse-aperture-projective-tangent-ultrametric`;
  all-valuation transverse rank; finite prime-source Hilbert metric; disk Schur geometry
- **Lean target:** `RHTower/XiTransverseValuationSzegoMetric.lean`

## Headline theorem

Fix a prime `p`, put `L=log p`, and attach to each positive integral aperture `a` the disk node

```text
q_a=exp(-aL)=p^(-a),        0<q_a<1.                    (1)
```

After removing the common prime-logarithm clock, the actual transverse Xi coefficient on
valuation layer `e` is

```text
F_e(a)=1-q_a^(e+1).                                      (2)
```

The raw layers satisfy `F_e(a)->1`; this is the valuation version of the already proved
projective collapse.  Their successive differences instead give the exact geometric feature

```text
D_0(a)=F_0(a)=1-q_a,
D_e(a)=F_e(a)-F_(e-1)(a)=(1-q_a)q_a^e,   e>=1.         (3)
```

Consequently the completed valuation-difference Gram is

```text
K_p(a,b)
 =sum_(e>=0)D_e(a)D_e(b)
 =(1-q_a)(1-q_b)/(1-q_a q_b).                           (4)
```

This is a diagonally weighted Szegő kernel.  Its diagonal is

```text
K_p(a,a)=(1-q_a)/(1+q_a)>0.                             (5)
```

After unit normalization, the aperture feature is literally the normalized Hardy coherent
state

```text
vhat_a(e)=sqrt(1-q_a^2) q_a^e,                          (6)
```

and its squared Hilbert separation is exactly the real disk pseudohyperbolic metric:

```text
1-|<vhat_a,vhat_b>|^2
 =((q_a-q_b)/(1-q_a q_b))^2.                            (7)
```

Thus distinct positive apertures have strictly positive completed separation at one fixed prime.

## Finite rank theorem

For any injective packet `a_0,...,a_(N-1)`, the first `N` valuation differences at the same fixed
prime form the square observation matrix

```text
M_(e,j)=(1-q_(a_j))q_(a_j)^e,       0<=e,j<N.           (8)
```

It factors as

```text
M=V(q_(a_0),...,q_(a_(N-1)))^T diag(1-q_(a_j)).         (9)
```

The nodes are distinct and lie in `(0,1)`, while every diagonal factor is nonzero.  Hence

```text
det M !=0                                                   (10)
```

and the finite Gram `M^*M` is positive definite.  This is stronger than the previous existential
finite-prime Gram theorem in one precise direction: no moving prime packet is required.  One fixed
prime, with valuation depth equal to aperture packet size, separates every finite aperture packet.

## Relation to the Brownian--Laplace factorization

The earlier Brownian theorem gives

```text
B_e(a)=integral_0^a exp(-(e+1)Lt)dt
      =(1-q_a^(e+1))/((e+1)L).                          (11)
```

Therefore `(2)` is the clock-rescaled Brownian sample

```text
F_e(a)=(e+1)L B_e(a),                                   (12)
```

and `(3)` says that the discrete valuation derivative of those clock-rescaled samples is the
Hardy coherent state.  The source geometry has two exact, compatible presentations:

```text
continuous aperture direction  -> Brownian interval kernel min(a,b),
discrete valuation derivative  -> Szegő kernel K_p(a,b). (13)
```

This resolves an ambiguity in the previous completion architecture.  The Laplace sampling arrow
does not need to be inverted to manufacture a Hilbert metric.  The actual valuation filtration
contains its own canonical Hardy completion after taking the source-forced successive difference.

## RH impact: the open theorem becomes a Pick domination

The target Xi object is an anti-causal Hardy leakage channel, and its boundary relative trace has
the same aperture variable.  Equations `(4)`--`(7)` show that the completed source aperture is
already a Hardy reproducing-kernel geometry.  A source-to-Xi contraction should therefore be
formulated as a Pick-kernel comparison, not as an abstract completion statement.

The exact next theorem to seek is a source-defined, prime--Gamma compatible map `T` such that the
aperture coherent states are transported to the finite Xi boundary-strip vectors and

```text
K_source(a_i,a_j)-K_Xi,T(a_i,a_j) >= 0                  (14)
```

as a matrix for every finite aperture packet.  Equivalently, after the correct four-unit
normalization, `T` must be a Schur-class contraction.  A cofinal graph-core limit of `(14)` would
give

```text
Delta_Xi(u)<=4(1-exp(-u))+o(u),   u->0+,                (15)
```

and hence RH by the established boundary relative-trace theorem.

This is a genuine narrowing: finite rank, aperture separation, and a canonical source Hardy
metric are no longer open.  The remaining issue is the sign/contractivity of one explicit
prime--Gamma-to-Xi Pick kernel, together with compatibility across primes and the archimedean
channel.

## No-go closure and scope

The raw layer family `F_e(a)` converges to the constant ray and is not itself the correct completed
metric.  The strongest positive survivor is its valuation derivative `(3)`, which is nondegenerate
and has the closed form `(4)`.

This theorem does **not** prove `(14)`, the four-unit estimate, or RH.  It also does not claim that
the classical Szegő kernel or pseudohyperbolic metric is new.  The candidate-new content is their
exact source-forced occurrence as the completed successive-valuation metric of the actual
transverse Xi arithmetic source, simultaneously with the Brownian aperture factorization and the
all-valuation differential-rank barrier.  No matching statement was found in the live corpus;
external novelty remains unaudited.

## Lean status

`XiTransverseValuationSzegoMetric.lean` is intended to formalize:

1. the disk node and its equality with the actual prime shift factor;
2. the normalized prime-power defect formula `(2)`;
3. the actual successive-layer identity `(3)`;
4. the weighted Vandermonde factorization and positive-definite finite Gram;
5. the completed metric sum `(4)` and diagonal law `(5)`; and
6. the pseudohyperbolic defect identity `(7)` and strict separation.

Direct Lean check and the narrow object build pass.  The principal theorems use only the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or proof placeholder
is present.

## Gates

- [x] 0 -> 1: raw valuation collapse and its nonzero successive difference identified
- [x] 1 -> 2: exact arithmetic, finite-rank, infinite-Gram, and normalized-distance proofs closed
- [x] 2 -> 3: direct Lean check, narrow object build, and standard axiom audit
- [ ] 3 -> 4: external novelty audit and source-to-Xi Pick domination

## Log

- 2026-07-19 — extracted the valuation derivative from the raw projective-collapse no-go and
  identified its exact weighted Szegő Gram and pseudohyperbolic normalized separation.  This turns
  the unspecified source-to-Hardy completion into a concrete prime--Gamma Pick-kernel domination
  problem.
