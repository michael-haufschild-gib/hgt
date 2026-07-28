# Von Mangoldt Toeplitz countertrace analytic-radius/capacity escape

- **ID:** `von-mangoldt-toeplitz-countertrace-analytic-radius-capacity-escape`
- **Stage:** 1 — in progress
- **Type:** SOURCE-SPECIFIC ANALYTIC ESCAPE LAW / POSITIVE SINGULAR-BOUNDARY SURVIVOR
- **Scientific status:** `[PAPER PROOF] [INDEPENDENT AUDIT PENDING] [NOVELTY PROVISIONAL]`
- **Parent:** `von-mangoldt-weighted-density-boundary-anomaly`
- **Source ledger:** `SR-41`
- **RH used:** no
- **Computation used:** no
- **Lean:** forbidden until independent paper and novelty audits pass

## Frontier changed

The parent constructs, for every finite von Mangoldt successor aperture `M`, the unique normalized
Toeplitz counterweight

```text
d_(M,0)=1,  d_(M,1),d_(M,2),...
```

whose finite sections absorb every positive jet-opening flux. It also proves coefficientwise
convergence as `M -> infinity`. What remains open is whether these regular finite readers compactify
to an analytic symbol on one fixed neighbourhood of the origin, which could then serve as a
regular source-algebra reader.

This card proves that they cannot. Put

```text
C_M(z)=1+2 sum_(r>=1) d_(M,r) z^r.                       (1)
```

At every aperture whose last von Mangoldt edge is nonzero, analyticity of `C_M` beyond the
reciprocal maximal clock forces an exact zero there. In particular, for every prime `p`,

```text
C_(p-1)(1/log(p+1))=0                                   (2)
```

whenever the radius of `(1)` exceeds `1/log(p+1)`. Consequently, on every fixed disk, either the
analytic radii fail cofinally or the Hardy boundary norms grow at least linearly in `log p`.
There is no locally bounded analytic-symbol compactification.

This is the first theorem in the `SR-41` reader attack that converts the abstract prime-clock
order-escape phenomenon into a quantitative singularity law for the literal source-defined
Toeplitz counterreader.

It does **not** identify the singular boundary current with the odd Gamma--Jacobi residual, realize
completed Euler multiplication, establish reflection positivity, locate a Xi zero, or prove RH.

## Universal endpoint theorem

Let

```text
0 < x_0 < ... < x_K,
a_0,...,a_K in C,          a_K != 0,
m(q)=sum_(j=0)^K a_j x_j^(q-2),              q>=2.      (3)
```

Let `c_0=1` and suppose that

```text
sum_(r=0)^N c_r m(2N-r+2)=0                  for N>=1.  (4)
```

Write

```text
C(z)=sum_(r>=0)c_r z^r,
C_N(z)=sum_(r=0)^N c_r z^r.                              (5)
```

### Theorem A: maximal-clock zero

If the radius of convergence of `C` is strictly larger than `1/x_K`, then

```text
C(1/x_K)=0.                                             (6)
```

### Proof

Substitute `(3)` into `(4)` and interchange the two finite sums:

```text
0=sum_(j=0)^K a_j x_j^(2N) C_N(1/x_j).                  (7)
```

Choose a real number `t` with

```text
1/x_K < t < radius(C).
```

Then

```text
A_t=sum_(r>=0)|c_r|t^r < infinity.                       (8)
```

For `j<K`,

```text
|C_N(1/x_j)|
 <= A_t max(1,(t x_j)^(-N)).                            (9)
```

After division of `(7)` by `x_K^(2N)`, the `j`th lower-clock term is bounded by a fixed scalar
times one of

```text
(x_j/x_K)^(2N),
(x_j/(t x_K^2))^N.                                     (10)
```

Both tend to zero. The first base is below one because `x_j<x_K`. For the second,

```text
x_j/(t x_K^2) < 1/(t x_K) < 1.                          (11)
```

The maximal-clock term tends to

```text
a_K C(1/x_K)
```

because `1/x_K` lies strictly inside the convergence disk. Taking the limit in `(7)` gives
`a_K C(1/x_K)=0`; `a_K != 0` proves `(6)`.

No positivity of the lower masses is used. They may have arbitrary signs or vanish.

### Theorem A2: every sufficiently high active clock is a zero

Under the same hypotheses, fix `j` with `a_j != 0`. If

```text
radius(C) > x_K/x_j^2,                                  (6a)
```

then

```text
C(1/x_j)=0.                                             (6b)
```

### Proof

Descend on the active indices. The maximal active index is Theorem A. Suppose `(6b)` is known for
every active `ell>j`. Choose

```text
x_K/x_j^2 < t < radius(C).
```

For `ell<j`, the estimate `(9)` after division by `x_j^(2N)` again tends to zero. For `ell>j`,
the already-proved zero gives

```text
C_N(1/x_ell)
 =-sum_(r>N)c_r x_ell^(-r).
```

Absolute convergence at `t` bounds the corresponding term, after division by `x_j^(2N)`, by a
fixed scalar times

```text
(x_ell/(t x_j^2))^N
 <=(x_K/(t x_j^2))^N -> 0.                             (6c)
```

The sole surviving term is `a_j C(1/x_j)`, which must vanish. This proves `(6b)`.

Thus analytic radius does not force only one endpoint zero. It forces every nonzero transport
clock above the explicit threshold

```text
x_j > sqrt(x_K/radius(C)).                              (6d)
```

## Quantitative boundary-capacity theorem

For `0<a<R`, let

```text
B_(a,R)(z)=R(z-a)/(R^2-a z).                            (12)
```

It is holomorphic on a neighbourhood of the closed disk `|z|<=R`, has its only disk zero at `a`,
satisfies

```text
|B_(a,R)(R exp(i theta))|=1,
|B_(a,R)(0)|=a/R.                                       (13)
```

Normalize the Hardy boundary norm by

```text
||F||_(H2(R))^2
 =(1/(2 pi)) integral_0^(2 pi)|F(R exp(i theta))|^2 dtheta.  (14)
```

### Theorem B: one inward zero forces Hardy capacity

If `F` is holomorphic on a neighbourhood of `|z|<=R`, `F(0)=1`, and `F(a)=0`, then

```text
||F||_(H2(R)) >= R/a.                                  (15)
```

### Proof

The quotient

```text
G=F/B_(a,R)
```

has a removable singularity at `a` and is holomorphic on the disk. Equation `(13)` gives equal
Hardy boundary norms for `F` and `G`, while

```text
|G(0)|=R/a.
```

The mean-value inequality for `G` yields

```text
R/a=|G(0)| <= ||G||_(H2(R))=||F||_(H2(R)).
```

This proves `(15)`.

The same argument gives

```text
sup_(|z|=R)|F(z)| >= R/a.                              (16)
```

### Theorem B2: a clock packet forces multiplicative Hardy capacity

If `F(0)=1` and `F` has distinct nonzero zeros `a_1,...,a_L` in `|z|<R`, then

```text
||F||_(H2(R)) >= product_(ell=1)^L R/|a_ell|.           (16a)
```

Indeed divide by the product of the disk Blaschke factors `B_(a_ell,R)`. Boundary norm is
unchanged, while the quotient's value at zero has modulus equal to the right side of `(16a)`.
The mean-value inequality finishes the proof. Multiplicities can be retained by repeating the
corresponding factor.

## Von Mangoldt specialization

For aperture `M`, the corpus proves the exact atomic representation

```text
finiteVonMangoldtSuccessorRelativeMoment M q
 =sum_(j=0)^M A_(M,j) X_(M,j)^(q-2),                   (17)

X_(M,j)=log(j+2).
```

The mass `A_(M,j)` is the consolidated incoming-minus-outgoing endpoint conductance, including
the order-two logarithmic factor. The counterweight opening law is exactly

```text
m_M(2N+2)+2 sum_(r=1)^N d_(M,r)m_M(2N-r+2)=0.          (18)
```

Thus `(18)` is `(4)` with

```text
c_(M,0)=1,
c_(M,r)=2d_(M,r),  r>=1.                               (19)
```

Take a prime `p` and set `M=p-1`. The finite source edges are

```text
2 -> 3, ..., p -> p+1.
```

The maximal node is

```text
X_(p-1,p-1)=log(p+1),                                  (20)
```

and its unpaired incoming mass is

```text
A_(p-1,p-1)
 =finiteVonMangoldtRealWeight(p) log(p+1)^2 > 0.        (21)
```

Theorem A therefore proves `(2)`.

### Theorem C: analytic-radius/Hardy-capacity dichotomy

Fix `R>0`. For every sufficiently large prime `p`, exactly the following implication holds:

```text
radius(C_(p-1)) > R
  ->
||C_(p-1)||_(H2(R)) >= R log(p+1).                     (22)
```

Indeed `1/log(p+1)<R`; Theorem A supplies the zero `(2)`, and Theorem B with
`a=1/log(p+1)` proves `(22)`.

Consequently:

1. no prime-aperture tail has both one common positive analytic radius and uniformly bounded
   Hardy boundary norm;
2. no prime-aperture tail is locally bounded in the compact-open topology near `0`;
3. any analytic-symbol realization of the canonical counterreader has boundary energy at least
   `R^2 log(p+1)^2` on the radius-`R` circle;
4. a cofinal source completion must carry either collapsing analytic radius or an unbounded
   boundary-capacity coordinate.

The coefficientwise convergence already proved in the parent cannot be upgraded to compact-open
analytic convergence on any neighbourhood of zero.

### Theorem D: active-clock packet capacity

Let `S>R>0`, and suppose `radius(C_M)>S`. Put

```text
J_(M;S,R)
 ={j:
     A_(M,j) != 0,
     X_(M,j) > sqrt(X_(M,M)/S),
     X_(M,j) > 1/R}.                                    (22a)
```

Theorem A2 forces one distinct zero `1/X_(M,j)` for every `j` in this set. Theorem B2 therefore
gives the exact finite-packet lower bound

```text
||C_M||_(H2(R))
 >= product_(j in J_(M;S,R)) R X_(M,j).                 (22b)
```

This is stronger than fixed-capacity divergence. The capacity cost is multiplicative in every
active transport clock that lies above the radius threshold. In the von Mangoldt source, active
clocks include the endpoint pairs generated by prime and prime-power conductances; the corpus's
`p=3 mod 4` transport-mass theorem supplies an unconditional infinite family of strictly negative
active clocks. Any quantitative prime distribution input upgrades `(22b)` to a corresponding
many-clock growth law, but no such estimate is needed for the exact finite theorem.

## Hypertranscendental interpretation

The prime-clock inverse-limit theorem says that stagewise differential algebraicity can disappear
at the exact source limit only through escape from every bounded annihilator-order sector. The
present theorem realizes the same escape inside the actual Suzuki reader:

```text
finite source clock
  -> normalized Toeplitz opening annihilator
  -> reciprocal active-clock zero packet
  -> zeros migrate to the germ basepoint
  -> analytic radius collapses or Hardy capacity diverges
     multiplicatively in the surviving clock packet.             (23)
```

Thus the infinite Euler operation is not represented by a hidden regular analytic germ. Its
source-defined reader necessarily develops a singular boundary coordinate. This sharpens the
generic prime-clock order-escape law: in the moment/reader realization, escaping algebraic clock
complexity has a forced analytic signature and a quantitative Hilbert-capacity cost.

This is useful to the RH route only if the forced capacity can be identified with the already
constructed odd Gamma--Jacobi residual and then shown to feed the completed Euler trace and
critical reflection orientation. Without that identification, `(23)` is a source constraint, not
a zero-location theorem.

## Anti-theatre and collision audit

### Corpus

Search covered:

- `formal/`;
- `docs/drafts/pipeline/3-formalized`;
- `docs/drafts/pipeline/2-fully-proven`;
- `docs/drafts/pipeline/5-failed`;
- source and terminal Suzuki ledgers;
- prime-clock inverse-limit and publication papers.

Corpus already contains:

- universal clock-order escape;
- compact-open Kolchin blindness under rational off-critical quartet surgery, including conserved
  Ward charge escaping every bounded height window;
- the exact finite atomic endpoint representation;
- unique Toeplitz counterweights and coefficientwise aperture convergence;
- fixed-capacity Ward--Schur divergence;
- reflection-even Gamma-capacity no-go;
- ordinary marginal and finite cyclic-reader no-gos.

The compact-open blindness theorem is an essential hostile predecessor: unmarked HT fields and
all local jets can converge while an off-critical divisor charge escapes in height. The present
law does not overcome that no-go. It instead proves that the actual source-marked counterreader
cannot compactify locally and identifies its forced reciprocal-clock zero packet.

No existing card or theorem states the maximal-clock zero `(6)`, the active-clock packet theorem
`(6a)`--`(6d)`, the prime-aperture zeros `(2)`, or the multiplicative Hardy-capacity floor `(22b)`.

The result is not advertised as discovery of endpoint dominance, Blaschke factorization, Hardy
evaluation, or normal-family theory. Claimed novelty is restricted to their exact composition
with the source-defined von Mangoldt Toeplitz countertrace and its reciprocal prime-clock zeros.

### Literature

Targeted arXiv searches found:

- Berg--Szwarc, *Inverse of Infinite Hankel Moment Matrices*, on entire reproducing-kernel
  coefficient matrices and absolutely convergent inverses;
- Basor--Ehrhardt, *Determinant computations for some classes of Toeplitz--Hankel matrices*, on
  finite-section determinant asymptotics;
- general symmetric Toeplitz/Hankel structure and classical moment-problem literature.

No located source contains recurrence `(18)`, endpoint zero `(2)`, or capacity dichotomy `(22)`.
This is an absence-of-hit result, not a priority certificate.

## Hostile falsifiers

The card is retired if any of the following occurs.

1. The parent opening law does not reindex to `(18)`.
2. The atomic representation carries exponent `q` rather than `q-2`, invalidating `(7)`.
3. Aperture `M=p-1` does not have nonzero maximal mass `(21)`.
4. Bound `(9)` is insufficient to kill lower clocks after division by `x_K^(2N)`.
5. The analytic symbol need not be the power series of the unique source counterweights.
6. Corpus already proves the same source-specific maximal-clock zero or analytic-capacity floor.
7. External literature contains an equivalent von Mangoldt successor-countertrace theorem.
8. The theorem does not narrow `SR-41` beyond the already failed fixed-capacity class.

Falsifiers 1--5 are rejected by the paper proof above and exact corpus definitions. Falsifiers
6--8 require independent audit before promotion.

## Exact next question toward RH

The theorem forces the missing reader to have a growing singular boundary capacity. The next
source theorem must determine whether its normalized boundary mode is the coherent odd
Gamma--Jacobi residual already constructed in `SR-37`--`SR-38`.

A useful connector must prove, before reading Xi zeros or a target sign, an identity of the form

```text
renormalizedBoundary(C_M)
  -> oddGammaJacobiResidual

and

completedEulerTrace
 = ToeplitzCountertrace + GammaJacobiBoundaryTrace.      (24)
```

Only after `(24)` is source-proved can the resulting completed reader be tested for the
reflection-positive/Loewner inequality whose violation at a hypothetical off-critical Xi zero
produces the existing double-pole contradiction.

## Formalization plan after audit

1. Formalize generic finite-atomic endpoint-zero theorem for a convergent coefficient series.
2. Prove maximal von Mangoldt transport mass formula at prime-edge apertures.
3. Reindex existing counterweight cancellation to convolution form `(18)`.
4. Specialize endpoint zero `(2)`.
5. Formalize disk Blaschke/mean-square capacity inequality or, if mathlib support is insufficient,
   first formalize the weaker sup-norm bound and retain the `H2` theorem on paper.
6. Prove the fixed-radius dichotomy `(22)`.
7. Run exact-file `lake env lean` checks; use `lake build <module>` only in final audit.

No Lean work begins until independent mathematical significance and novelty audits pass.
