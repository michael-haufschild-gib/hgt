# Arithmetic Schur renormalization: Gamma elimination is prime-power translation

- **ID:** `arithmetic-schur-renormalization-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM / RH-ROUTE ENDPOINT
- **Scientific status:** `[THEOREMS A--D PAPER-PROVED] [LEAN CORE FORMALIZED]`
  `[MANUSCRIPT DRAFTED] [SOURCE-PURE] [NOVELTY AUDIT OPEN] [NOT RH]`
- **Parents:** `../2-fully-proven/needs-audit/xi-transverse-gamma-valuation-schur-translation.md`;
  `../3-formalized/needs-audit/xi-mobius-schur-valuation-marking.md`;
  `../3-formalized/not_new_scientific_knowledge/prime-laplace-source-generated-transport-coercivity.md`
- **Lean target:** `formal/GaloisForLFunctions/RHTower/ArithmeticSchurRenormalizationLaw.lean`
- **Manuscript:** `docs/drafts/manuscripts/arithmetic-schur-renormalization/main.tex`

## Headline

The archimedean Gamma channel is not a scalar correction to independent prime modes. After the
source-forced rational gauge, eliminating it by Schur complement removes exactly one prime-power
valuation coordinate. Repeating the operation gives an exact arithmetic Schur algorithm:

```text
Gamma Schur elimination = translation by one valuation depth.                 (ASR)
```

The algorithm is conservative only on the complete valuation tower. Every finite-depth closure
leaves a strictly positive residual, while the cofinal residual is zero. Thus the same theorem
simultaneously explains why fixed Gamma capacity fails after scalarization and why coherent
prime--Gamma covariance succeeds before scalarization.

## Universal theorem A: cofinal Schur exhaustion

Let `X` be a set, let `q:X -> (0,1)`, and let `a:X -> (0,infinity)`. Put

```text
h_n(x)=a(x) q(x)^n,
K(x,y)=a(x)a(y)/(1-q(x)q(y)),
K_N(x,y)=(q(x)q(y))^N K(x,y).                             (1)
```

Then for every natural number `N`,

```text
K(x,y)=sum_(0<=n<N) h_n(x)h_n(y)+K_N(x,y),               (2)
K_N(x,y)-h_N(x)h_N(y)=K_(N+1)(x,y).                      (3)
```

For every finite packet `(x_i)` and coefficients `(c_i)`, both terms on the right of `(2)` are
positive semidefinite quadratic forms. Moreover:

1. `K_N(x,x)>0` for every finite `N` and every `x`; no finite Schur chain exhausts the kernel.
2. `K_N(x,y)->0` pointwise as `N->infinity`.
3. On every finite packet, convergence is in every matrix norm.
4. Hence the infinite feature map `x |-> (h_n(x))_(n>=0)` is an exact conservative realization of
   `K`, while every finite prefix is a strict compression.

### Proof

Equation `(3)` is the fixed-point identity

```text
a(x)a(y)/(1-qr)-a(x)a(y)=(qr)a(x)a(y)/(1-qr),            (4)
```

multiplied by `(qr)^N`, where `qr=q(x)q(y)`. Summing `(3)` for `n=0,...,N-1`
telescopes to `(2)`. Positivity follows because the prefix is a sum of rank-one squares and

```text
K_N(x,y)=<q(x)^N h(x),q(y)^N h(y)>_ell2.
```

Strict finite nonattainment follows from `a(x)>0` and `0<q(x)<1`. Pointwise convergence follows
from `(q(x)q(y))^N->0`; finite-packet matrix-norm convergence follows because all norms on a
finite-dimensional matrix space are equivalent. `QED`

This theorem is elementary in abstract coordinates. Scientific content begins with the arithmetic
identification below; no novelty is claimed for geometric-series or Kolmogorov-decomposition
algebra alone.

## Universal theorem B: rigidity and minimality

Suppose a positive kernel `L` and a nonzero coordinate `h_0` obey

```text
L(x,y)-h_0(x)h_0(y)=q(x)q(y)L(x,y),                       (5)
```

with `0<q<1`. Then `(5)` uniquely forces

```text
L(x,y)=h_0(x)h_0(y)/(1-q(x)q(y)).                         (6)
```

If `q(x_1),...,q(x_m)` are distinct and `h_0(x_j)!=0`, the first `m` translated coordinates have
weighted Vandermonde matrix

```text
V_(n,j)=h_0(x_j)q(x_j)^n,       0<=n<m,                  (7)
```

and nonzero determinant. Consequently the realization is minimal on every finite marked packet.
Any two minimal Hilbert realizations satisfying `(5)` are related by the unique unitary carrying
each translated source coordinate to its counterpart.

The last statement is the usual uniqueness of minimal Kolmogorov decompositions, but `(5)` fixes
the entire feature tower from one boundary coordinate. This is the universal rigidity behind the
arithmetic specialization.

## Theorem C: arithmetic specialization

For a rational prime `p`, set

```text
q_p=p^(-1),
H_n(p)=sqrt(q_p)(1-q_p)q_p^n,
K_Gamma(p,r)=sum_(n>=0)H_n(p)H_n(r).                     (8)
```

Let `u_p` be the normalized covariance of the actual Gamma cyclic measure with its centered second
spectral moment, and put

```text
R_p=(1+q_p^2)^2/(1+q_p)^2.                               (9)
```

The formal corpus proves the exact source identity

```text
R_p u_p=-(3sqrt(2)/4)H_0(p),
(3sqrt(2)/4)^2=9/8.                                     (10)
```

Therefore Schur elimination of the Gamma conductor of capacity `9/8` is exactly

```text
K_Gamma(p,r)-(R_pu_p)(R_ru_r)/(9/8)
  =K_Gamma(p,r)-H_0(p)H_0(r)
  =q_pq_r K_Gamma(p,r).                                 (11)
```

Theorem A upgrades `(11)` from a one-step coincidence to a complete renormalization law:

```text
K_Gamma(p,r)
 =sum_(0<=n<N)H_n(p)H_n(r)+(p r)^(-N)K_Gamma(p,r),      (12)
```

with strict positive residual at every finite `N` and zero residual only cofinally. For every
injective `m`-prime packet, the first `m` valuation coordinates retain every prime label by `(7)`.

Thus the archimedean boundary, prime-power depth, coherent covariance, and cofinal limit are one
minimal conservative system. None can be deleted without changing its Schur residual.

## Theorem D: critical Fisher whitening is intrinsically unitary

The genuine local Mobius--Bernoulli Schur factor selects the damped coordinates

```text
Delta B_p(n)=d_p H_n(p),
d_p=sqrt(q_p)/(1+q_p),
d_p^2=q_p/(1+q_p)^2.                                    (13)
```

Their all-prime diagonal mass is summable. The inverse Fisher whitening `d_p^(-1)` grows at least
like `sqrt(p)` and is unbounded on ambient prime `ell2`; the corpus correctly excludes
coefficientwise inverse transport there.

The intrinsic source Hilbert spaces behave differently. Their kernels satisfy the exact
congruence

```text
K_M(p,r)=d_p d_r K_Gamma(p,r).                            (14)
```

Let `C_00(P)` be finite prime packets. Equip it first with the semidefinite Mobius form `K_M` and
second with the Gamma form `K_Gamma`. The diagonal map

```text
(Wc)_p=d_p c_p                                             (15)
```

obeys

```text
||c||_(K_M)^2=||Wc||_(K_Gamma)^2.                         (16)
```

Because every `d_p>0`, `W` is an algebraic bijection of finite packets. Equation `(16)` maps the
two nullspaces onto one another, descends to an isometry of the quotient pre-Hilbert spaces, and
extends uniquely to a unitary between their Hilbert completions. Moreover

```text
Delta B_p(n+1)=q_p Delta B_p(n),                          (17)
```

so this unitary intertwines the complete valuation shift.

This proves the boundary-completed inverse-transport theorem at the source level: Fisher
whitening is unbounded only after forgetting the arithmetic Gram metric. In the intrinsic RKHS it
is exactly unitary, exhaustion-independent, and compatible with every finite Schur section in
`(12)`. No bounded operator on ambient prime `ell2` is asserted or needed.

The argument is universal: every strictly positive diagonal congruence `K_1(x,y)=d(x)d(y)K_0(x,y)`
induces this canonical unitary between intrinsic kernel completions. The candidate-new content is
that the genuine Mobius/Fisher damping and actual corrected Gamma covariance satisfy precisely
this law while sharing the valuation Schur dynamics.

## RH route opened by the law

The target-side corpus identifies a canonical Xi boundary leakage family. Its negative index is
the off-critical zero count, and the four-unit boundary trace bound implies RH. The source side now
has a unique minimal lossless Schur system. The remaining conjecture has one exact form:

```text
[OPEN: ARITHMETIC-SCHUR-TO-XI]
There is a source-defined morphism from the boundary-completed arithmetic Schur system
to the Xi boundary leakage system which intertwines valuation translation and is nonexpansive.
                                                                            (18)
```

If `(18)` holds, its finite Gram inequalities pass through `(12)`, the cofinal residual vanishes,
and the target leakage has at most the source four-unit boundary energy. Existing target theorem
then gives

```text
arithmetic Schur morphism
 -> Xi boundary relative-trace density <=4
 -> no negative Xi leakage index
 -> RH.                                                                  (15)
```

Unlike a bare passivity or Weil-positivity premise, `(14)` specifies source space, boundary
channel, translation action, finite sections, cofinal topology, and exact normalization before
the Xi target is evaluated.

## Why this route is still open

Corpus no-gos eliminate:

- ordinary all-place local-ratio limits: completed symbol collapses to `1`;
- independent prime modes against one scalar Gamma coordinate: Schur cost diverges harmonically;
- bounded scalarization of higher subset/Fock covariance: readout norm diverges;
- every fixed finite cancellation depth: critical inverse transport remains expansive;
- recovery of the Gamma frame by channelwise Fisher whitening: inverse is unbounded;
- finite rank or unmarked cofinal graph closure: valuation Vandermonde marking is required.

None invalidates a closed, boundary-completed, coherent Schur morphism. Equations `(11)`--`(13)`
are its positive source data.

## Literature boundary

Targeted arXiv searches on 2026-07-22 found:

- classical Schur algorithms, Szego kernels, minimal isometric colligations, and factorization of
  Schur functions;
- operator-theoretic and semilocal programs for zeta;
- Connes--Consani--Moscovici's Gamma cyclic measure and prolate/Sonin construction;
- Connes--Consani's finite Gauss-paired quasi-inner local factors.

No checked source states the conjunction `(10)`--`(12)`: actual Gamma covariance, the rational
prime gauge, exact valuation-depth Schur translation, strict finite nonattainment, cofinal
exhaustion, and Mobius/Fisher source marking. Absence of a search hit is not a priority verdict.
Specialist audit remains mandatory. The abstract Schur and minimality components are classical;
candidate novelty is the arithmetic identification and boundary-completed inverse-transport
architecture.

Primary comparison points:

- Connes--Consani, *Quasi-inner functions and local factors*, arXiv:2008.10974.
- Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423.
- Classical Schur/Szego realization and minimal Kolmogorov-decomposition theory.

## Falsifiers

1. A checked source already contains arithmetic identity `(10)` and its cofinal interpretation.
2. The transported Gamma coordinate at depth `n` is not the Schur defect of depth-`n` residual.
3. Finite residual can vanish for a nonempty prime packet.
4. Minimality fails for distinct reciprocal-prime nodes.
5. Boundary-completed inverse transport depends on prime exhaustion or counterterm choice.
6. Any proposed source-to-Xi morphism uses Xi zeros, assumes target positivity, or discards the
   unbounded whitening graph.
7. Target morphism fails on one finite mixed-prime Pick matrix.

## Gates

- [x] prior one-step Gamma/valuation identity and source marking verified in Lean corpus
- [x] scalar, finite-depth, ordinary-limit, and bounded-whitening no-gos audited
- [x] preliminary exact-phrase arXiv search found no matching arithmetic theorem
- [x] universal cofinal exhaustion paper proof
- [x] universal rigidity/minimality paper proof with all degenerate cases
- [x] intrinsic Fisher-whitening unitary and shift intertwining paper proof
- [x] Lean formalization of cofinal exhaustion, strict nonattainment, fixed-point rigidity,
      minimality, arithmetic specialization, Fisher congruence, and shift intertwining
- [x] wire module into `GaloisForLFunctions.RHTower`
- [ ] standalone paper and independent novelty audit
- [ ] construct and prove nonexpansive source-to-Xi morphism `(14)`
- [ ] RH
