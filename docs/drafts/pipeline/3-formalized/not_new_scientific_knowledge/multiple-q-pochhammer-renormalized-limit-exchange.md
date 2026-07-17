# Multiple q-Pochhammer completion has a critical polylogarithmic limit-exchange defect

- **ID:** `multiple-q-pochhammer-renormalized-limit-exchange`
- **Stage:** 3-formalized
- **Type:** LEAN THEOREM / PROGRAMME-4 LIMIT-EXCHANGE THEOREM / MULTIPLE-GAMMA SOURCE BENCHMARK
- **Source:** `docs/reports/rh-status-1707.md`, programme 4;
  `../3-formalized/not_new_scientific_knowledge/elliptic-gamma-source-face-fracture.md`;
  `../3-formalized/not_new_scientific_knowledge/multiple-gamma-holomorphic-period-incidence-exclusion.md`
- **Scientific status:** `[LEAN-FORMALIZED] [PAPER-PROVED] [REDISCOVERED]`
  `[PARENT-THEORY BRIDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/MultipleQPochhammerLimitExchange.lean`

## Exact theorem

For `N>=1`, `r>=0`, define the finite `(r+1)`-direction q-Pochhammer product

```text
P_(N,r)(x,q)
  = product_(0<=j_0,...,j_r<N) (1-x q^(j_0+...+j_r)).       (1)
```

Give its formal logarithm the minimal pole-order normalization

```text
A_(N,r)(x,q)=(1-q)^(r+1) log P_(N,r)(x,q).                 (2)
```

For every `m>=1`, its `x^m` coefficient is

```text
c_(N,r,m)(q)
  =-[ (1-q)^(r+1) / m ]
     (sum_(j=0)^(N-1) q^(mj))^(r+1).                       (3)
```

Then the following coefficientwise iterated limits exist:

```text
lim_(N->infinity) lim_(q->1-) c_(N,r,m)(q) = 0,             (4)

lim_(q->1-) lim_(N->infinity) c_(N,r,m)(q)
  = -1/m^(r+2).                                             (5)
```

Equivalently, the completed-first comparison defect is

```text
Delta_r(x)=-sum_(m>=1) x^m/m^(r+2)=-Li_(r+2)(x),            (6)
```

whereas finite boundary specialization first gives zero after the same normalization.

The exponent `r+1` in `(2)` is intrinsic: it is the exact pole order already visible in the
linear coefficient

```text
[x] log P_(infinity,r)(x,q)=-(1-q)^(-(r+1)).                (7)
```

Thus smaller powers do not regularize the completed boundary, the critical power gives the
nonzero polylogarithmic defect, and larger powers kill it.

## Why this is programme 4 rather than notation

The two operations are defined on the actual finite multiple-q-Pochhammer source:

```text
completion: N -> infinity,
boundary refinement: q -> 1,
renormalization: multiply by the source-forced pole order (1-q)^(r+1).
```

Both composites in `(4)`--`(5)` exist coefficientwise and disagree. This is stronger than the raw
unscaled observation, where both routes diverge and no comparison class is defined.

The theorem is not the conjectural `BCDef_F` of the DA/meromorphic physical-character card. It is
an honest limit-exchange defect in a different, explicitly defined multiple-Gamma source model.
Any later universal calculus must recover `(6)` without identifying it with the unrelated
nonclosed-range or Calkin defects.

## Proof

Formal expansion of `log(1-y)` gives `(3)` because the sum over the `(r+1)`-dimensional box
factorizes:

```text
sum_(j_0,...,j_r<N) q^(m(j_0+...+j_r))
  =(sum_(j<N) q^(mj))^(r+1).                                (8)
```

For fixed `N`, the geometric sum tends to `N` as `q->1`, while `(1-q)^(r+1)->0`, proving `(4)`.
For fixed `0<q<1`, the sum tends to `(1-q^m)^(-1)`, so the completed coefficient is

```text
c_(infinity,r,m)(q)
  =-1/m ((1-q)/(1-q^m))^(r+1).                              (9)
```

The factorization

```text
1-q^m=(1-q)(1+q+...+q^(m-1))                               (10)
```

shows that `(9)` tends to `-1/(m*m^(r+1))`, proving `(5)`--`(6)`.

Lean proves the diagonal-nome coefficient theorem unconditionally for every `r` and every `m>0`:

```text
finite boundary first:       c_(N,r,m)(q) -> 0 as q->1;
completion at fixed q:       c_(N,r,m)(q) -> c_(infinity,r,m)(q) as N->infinity;
completed boundary first:    c_(infinity,r,m)(q) -> -1/m^(r+2) as q->1;
nontriviality:                -1/m^(r+2) != 0.
```

The rectangular multi-nome form follows by the same factorization one coordinate at a time. `QED`

## Hostile review boundary

- The critical scaling must be part of the comparison functor. Introducing it only after seeing
  divergence would be post-hoc regularization theatre. Equation `(7)` is the source-internal
  reason it is forced.
- The coefficientwise formal logarithm is the exact initial theorem. Analytic uniform convergence
  in `x` is a strengthening, not silently assumed.
- The result does not make different period-coordinate limits noncommutative; the finite box is
  symmetric. The noncommutation is specifically completion versus singular boundary refinement.
- Generalized q-polylogarithm limits and multiple elliptic Gamma integral/product formulae are
  parent mathematics. Novelty, if any, could only lie in a later cross-benchmark theorem.
- The result belongs to the raw generalized q-Pochhammer counterterm layer. Ueno--Nishizawa prove
  that the canonically normalized Vigneras multiple q-Gamma function converges to the classical
  multiple Gamma uniformly on compacta away from poles. Thus its native classical-limit defect is
  zero: the nonzero class here is the counterterm/cocycle discarded by normalization.

## Primary parents

- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, `https://arxiv.org/abs/math/0306164`.
- P. L. L. Morain, *Geometric families of multiple elliptic Gamma functions and arithmetic
  applications, I*, `https://arxiv.org/abs/2510.16515`.
- K. Ueno and M. Nishizawa, *The multiple gamma functions and the multiple q-gamma functions*,
  PRIMS 33 (1997), `https://ems.press/content/serial-article-files/40666`.
- R. Mortini, R. Rupp, A. Sasane, *On the Krull Intersection Theorem in Function Algebras*,
  `https://arxiv.org/abs/1605.08204` (adjacent flat-intersection parent, not this theorem).

## Surviving open core

1. Prove the full simultaneous boundary-layer law indexed by the scales
   `(1-q_i)N_i -> rho_i in [0,infinity]`.
2. Identify the paired q-Pochhammer counterterm with the exact Narukawa--Morain Bernoulli
   modularity cocycle on a fixed branch chamber.
3. Formalize the critical exponent trichotomy without importing a full polylogarithm API.
4. Compare the resulting nonzero coefficient sequence with the Gamma factorial-wall benchmark and
   prove exactly what transfers.

## Gates

- [x] exact source product and two operations defined
- [x] both iterated composites made meaningful by a source-forced scaling
- [x] dependency-closed paper proof
- [x] hostile proof review
- [x] external rediscovery verdict
- [x] unconditional Lean coefficient theorem
- [x] touched-file Lean check passed
- [ ] exact comparison with Gamma factorial wall
