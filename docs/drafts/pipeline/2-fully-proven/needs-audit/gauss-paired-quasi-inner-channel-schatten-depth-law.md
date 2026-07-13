# Gauss-paired quasi-inner channels have cofinally growing Schatten depth

- **ID:** `gauss-paired-quasi-inner-channel-schatten-depth-law`
- **Stage:** 2-fully-proven / parent residue audit open
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED FROM A NEEDS-AUDIT PARENT] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent results:** Connes--Consani's Gauss factorization and quasi-inner theorem,
  `gauss-component-quasi-inner-residue-hierarchy.md`, the singular autonomous Kolchin-frequency
  law, and `nonautonomous-kolchin-frequency-budget-law.md`
- **Statement:** The canonical Connes--Consani realization of `m` finite places resolves the fixed
  archimedean ratio into `m` prime-paired quasi-inner channels. The direct-sum channel defect has
  exact critical weak-Schatten exponent `2m` and a nonzero arithmetic Dixmier residue. Hence every
  cofinal finite-place construction must grow both its arithmetic channel count and its
  regularization depth, or provide a source-defined covariance/smoothing which cancels the critical
  channel defects.

## Gauss-paired channels

Let

```text
F={p_0,...,p_(m-1)}                                             (1)
```

be a set of `m>=1` distinct rational primes. Connes--Consani define archimedean Gauss components

```text
rho_infinity^(m,k),  0<=k<m,                                   (2)
```

with

```text
product_(k=0)^(m-1) rho_infinity^(m,k)=rho_infinity.            (3)
```

For any bijection between the indices and the primes, put

```text
u_(F,k)=rho_infinity^(m,k) rho_(p_k).                           (4)
```

Every `u_(F,k)` is quasi-inner on the critical Hardy half-plane, and

```text
product_(k=0)^(m-1)u_(F,k)
 =rho_infinity product_(p in F)rho_p.                           (5)
```

Thus the finite-place product is channel-resolved before compression. The archimedean completion
has not acquired new total Gamma degree; its one ratio has been factorized into `m` operator
channels and paired with the `m` arithmetic places.

Let `P` be the Hardy projection and define the channel Hankel defects

```text
H_(F,k)=(1-P)M_(u_(F,k))P.                                     (6)
```

## Exact critical residue of each channel

`gauss-component-quasi-inner-residue-hierarchy.md` proves, pending independent audit, that

```text
|H_(F,k)|^(2m) in L^(1,infinity)                               (7)
```

is measurable and

```text
Tr_omega(|H_(F,k)|^(2m))
 =R_m(p_k)
 =2(p_k-1)^(2m)(p_k^m-1)^2
    /(p_k^(2m)m^2 log p_k)>0.                                  (8)
```

In particular, `H_(F,k)` belongs to weak `S_(2m)` but not to the ordinary Schatten class
`S_(2m)`: if its `2m`-th power were trace class, every Dixmier trace in `(8)` would vanish.

## Direct-sum depth theorem

Put

```text
H_F^channel=directSum_(k=0)^(m-1) H_(F,k).                     (9)
```

Functional calculus of finite orthogonal sums gives

```text
|H_F^channel|^(2m)
 =directSum_(k=0)^(m-1)|H_(F,k)|^(2m).                         (10)
```

The Dixmier trace is additive on positive finite direct sums. Hence `(8)`--`(10)` give

```text
Tr_omega(|H_F^channel|^(2m))
 =sum_(p in F)R_m(p)>0.                                       (11)
```

Consequently

```text
H_F^channel in S_(2m,infinity) \ S_(2m).                       (12)
```

Weak-Schatten inclusion gives `H_F^channel in S_q` for every `q>2m`. Conversely, if `q<=2m` and
`H_F^channel` belonged to `S_q`, then it would belong to `S_(2m)`, contradicting `(12)`. Therefore

```text
inf{q>0:H_F^channel in S_q}=2m,                               (13)
```

with the endpoint attained only in the weak ideal.

## Cofinal regularization law

For the prime cutoff

```text
F_N={p:p<=N},
m_N=pi(N),                                                    (14)
```

the canonical channel carrier has critical exponent

```text
2m_N=2pi(N).                                                   (15)
```

Thus no fixed Schatten class `S_q` contains the channel-resolved defects for all `N`. A standard
regularized Fredholm determinant `det_r(1+H_(F_N)^channel)` requires an integer

```text
r>2pi(N),                                                     (16)
```

so its regularization genus must grow cofinally. This conclusion concerns the unsmoothed
quasi-inner channel defect. Test-function or resolvent smoothing may lower the ideal order, but
that smoothing is then a load-bearing part of the source construction and must be compatible with
the aperture limit.

The full product defect

```text
(1-P)M_(rho_infinity product_(p in F)rho_p)P                    (17)
```

can contain cancellations between the channels in `(9)`. Such cancellation does not refute the
law: it is precisely an operator-valued prime--prime covariance. A successful construction using
`(17)` must prove that this covariance is source-defined, retains the prime incidence, and is
compatible with its determinant or relative trace. Forgetting the channel decomposition before
proving those facts loses the arithmetic carrier.

## Exact coefficient--state allocation of the arithmetic module

At cutoff `N`, the construction in `(4)` uses exactly `pi(N)` labeled local channels. Suppose a
jointly Bohr-almost-periodic realization moves some or all of these rates into nonautonomous
coefficients `a`. Put

```text
V_N=span_Q{log p:p<=N},
D_a=Gamma(a),
A_N=V_N/(V_N intersection D_a).                              (18)
```

The coefficient--state frequency conservation law gives the exact split

```text
pi(N)=dim_Q(V_N intersection D_a)+dim_Q A_N,                  (19)
```

and, for a nondegenerate fixed-coefficient singular ADE fiber with relative Kolchin capacity
`kappa_rel`,

```text
dim_Q A_N<=rank_Q dual(K)<=2kappa_rel.                        (20)
```

If the relative scalar equation has differential order `n_N` and polynomial degree `d_N`, the
uniform characteristic-set bound in `bounded-syntax-singular-ade-prime-capacity-law.md` gives

```text
pi(N)
 <=dim_Q(V_N intersection D_a)+2B(n_N,d_N).                   (20a)
```

Thus a cofinal realization continuously pays for new primes through one of four principal
currencies: growing differential order, growing algebraic degree, growing coefficient-side
frequency, or a state carrier outside bounded finite Kolchin capacity. Growing state arity and a
genuinely global/noncompact constraint are instances of the last currency rather than free
exceptions to the ledger.

Thus every prime direction is paid exactly once: either its character is already carried by the
coefficient hull, or its class survives in the relative solution-state kernel. Nonautonomy can
move arithmetic between the two layers but cannot erase it.

For an autonomous realization `D_a=0`, so `(20)` recovers

```text
kappa(P_N)>=ceil(pi(N)/2).                                    (21)
```

The same cofinal resource therefore has three compatible operator/differential coordinates:

```text
Gauss-paired operator realization:
  channel count pi(N) and critical depth 2pi(N);

nonautonomous realization:
  coefficient rank dim_Q(V_N intersection D_a)
  plus relative state rank at least dim_Q A_N;

autonomous singular realization:
  Kolchin jet capacity at least ceil(pi(N)/2).                 (22)
```

Neither quasi-inner compactness, singularity, nor nonautonomous coefficients supply a
bounded-complexity escape. The last option is a valid carrier only when its coefficient hull
visibly contains the arithmetic characters it claims to absorb.

## Positive Connes carrier law

Every viable cofinal Connes construction using the finite local-ratio system must carry one of the
following equivalent resources explicitly:

1. the growing Gauss-paired channel system `(9)` together with determinant order exceeding
   `2pi(N)`;
2. test-function or relative-resolvent smoothing strong enough to put the complete channel system
   in one fixed determinant ideal, with a proof uniform in `N`;
3. a multiplicative covariance cancellation in the full product defect `(17)`, together with a
   source-defined trace anomaly recording the discarded channel information;
4. a non-Schatten determinant-line, derived-limit, or global constraint which is defined before the
   regularized all-place ratio collapses to the identity.

In alternatives 2--4, the coefficient--state allocation `(19)`--`(20)` remains compulsory. Any
prime character removed from the explicit Gauss channel list must reappear in the coefficient hull
or in the relative operator-state kernel. A covariance or smoothing theorem is therefore
arithmetic only if it preserves this quotient incidence, not merely the resulting scalar trace.

The archimedean Gamma factor supplies the compensating factorization `(3)`. The prime set supplies
the cofinal channel count. The missing RH theorem is a positivity and index-transport theorem on
one of the four carriers above.

## Attack and exact scope

- `[SEARCH]` Gauss factorization, quasi-innerness of every paired factor, and the upper
  infinitesimal order are in Connes--Consani.
- `[PROVED FROM THE PARENT RESIDUE]` The direct-sum endpoint is exact, non-trace-class, and has the
  residue `(11)`.
- `[PROVED]` No fixed Schatten class or fixed regularized-determinant order contains the cofinal
  channel-resolved system.
- `[PROVED FROM THE NONAUTONOMOUS BUDGET LAW]` The coefficient and relative-state layers obey the
  exact prime-module allocation `(19)`--`(20)` under its joint almost-periodicity and nondegenerate
  fixed-fiber hypotheses.
- `[PROVED FROM THE BOUNDED-SYNTAX LAW]` Under the additional scalar order/degree hypotheses, the
  four-currency budget is the explicit inequality `(20a)`.
- `[NOT PROVED]` The full product defect has not been shown to have exact exponent `2m`; channel
  cancellations may improve it.
- `[NOT PROVED]` The theorem does not construct the required covariance, smoothing, determinant
  line, or Weil-positive form.
- `[NOT PROVED]` It does not prove RH.

## Scientific classification

The direct-sum argument and Schatten inclusions are standard. The substantive endpoint constants
come entirely from the needs-audit Gauss-component residue theorem. This card is a route bridge and
inherits that theorem's independent-audit requirement; it is not promoted as new scientific
knowledge.

## Lean decision

The Lean tree does not contain Hardy quasi-inner multipliers, weak Schatten ideals, Dixmier traces,
or regularized Fredholm determinants. An abstract finite-direct-sum wrapper would not certify the
analytic endpoint `(8)`. No Lean file is added for the operator-analytic core.

The one framework-level step here, the coefficient--state allocation `(19)`--`(20)`
(`dim A_N ≤ 2 kappa_rel`, linear form `dim V ≤ dim (V/(V ⊓ D)) + dim D`), is formalized abstractly
and axiom-clean by the shared lemma `HTGeometry.finrank_le_arithmeticComplement_add` in
`formal/GaloisForLFunctions/ArithmeticComplementRank.lean`.  The endpoint residue `(8)` and the
weak-Schatten depth `(12)`--`(13)` remain blocked on the absent Dixmier-trace / weak-Schatten
substrate and on the needs-audit parent residue theorem.

## Gates

- [x] Gauss-paired channel system identified
- [x] exact channel residues inherited
- [x] direct-sum critical exponent proved
- [x] cofinal determinant-depth floor proved
- [x] exact coefficient--state frequency budget and singular Kolchin-capacity comparison attached
- [ ] independent audit of the Gauss-component residue theorem
- [ ] construct a uniform smoothing or covariance cancellation
- [ ] prove semilocal trace-remainder positivity
- [ ] transport the resulting index to the true restricted-Weil operator
- [ ] prove RH
