# Suzuki zero modes require a corona/regular two-scale boundary law

- **ID:** `suzuki-corona-regular-two-scale-boundary-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + CONJECTURE
- **Scientific status:** `[PAPER-PROVED MODEL THEOREM] [FALSIFIED PRIOR INTERFACE]`
  `[SOURCE-SPECIFIC CONJECTURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 2--5 and 8
- **Boundary sources:** V. Hernandez-Santamaria, L. F. Lopez Rios, and A. Saldana,
  *Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the
  logarithmic Laplacian*, arXiv:2401.18033v2; H. Chen and T. Weth,
  *The Dirichlet Problem for the Logarithmic Laplacian*, arXiv:1710.03416v6
- **Statement:** The principal logarithmic Dirichlet equation has an exact half-log corona plus
  power-scale regular decomposition.  All inverse-log traces can vanish on a nonzero regular
  solution, and even on an intermediate-scale non-`H1` solution.  Therefore log-grade separation
  cannot detect the whole square-Evans packet.  The RH route must prove a source-specific
  no-intermediate-scale theorem and then close corona and raw Evans branches separately.

## Goal and corrected RH frontier

The completion-safe target remains

```text
ker A_a={0} for every a>0,
```

equivalently `det N_(a,0)!=0` for every aperture.  Existing boundary work proposed that all
endpoint/seam inverse-log coefficients jointly separate the finite characteristic packet.  The
model theorem and counterexamples below show that this is false as a whole-packet principle.
Inverse-log traces see the completion corona.  They do not see the ordinary power-scale branch
which lies in `H1_0`, and without an additional source theorem they also do not see intermediate
flat non-`H1` scales.

The corrected proof architecture is

```text
square-Evans zero mode v
  -> nonzero corona trace/state       -> prime--Gamma corona no-return,
  -> zero corona trace/state, v in H1 -> u=Dv in raw ker G_a -> raw Evans injectivity.
```

The new common gate is not another estimate.  It is a boundary **scale-gap theorem** excluding
every mode strictly between the inverse-log corona expansion and the physical `H1` branch.

## 1. Exact principal two-channel theorem

For a locally integrable `F:[0,infinity)->C`, define the leading Volterra operator

```text
(P F)(L)=2L F(L)-integral_0^L F(t)dt.                    (1)
```

Let `F` be `C1` for large `L`, put `Phi=P F`, and set

```text
H(L)=sqrt(L)F(L),
u(r)=F(log(1/r)).                                        (2)
```

Assume

```text
integral_L0^infinity |Phi'(t)|/sqrt(t) dt < infinity.    (3)
```

`[PROVED HERE]` Then the canonical trace

```text
beta=lim_(L->infinity) sqrt(L)F(L)                       (4)
```

exists and the following identity is exact:

```text
F(L)=beta/sqrt(L)
     -1/(2sqrt(L)) integral_L^infinity Phi'(t)/sqrt(t)dt. (5)
```

If, for some `sigma>1/2` and real `m`,

```text
|Phi'(L)| <= C exp(-sigma L)(1+L)^m                     (6)
```

for large `L`, then precisely one of the following occurs:

```text
beta != 0:
  F(L)=beta L^(-1/2)+O(exp(-sigma L)L^(m-1)),
  u notin H1 near r=0;

beta = 0:
  F(L),F'(L)=O(exp(-sigma L)L^(m-1)),
  u in H1 near r=0.                                     (7)
```

### Proof

Differentiating `(1)` gives

```text
Phi'(L)=F(L)+2L F'(L)=2sqrt(L)H'(L).                    (8)
```

Hypothesis `(3)` makes `H'` integrable, so `H` has a finite limit `beta`.  Integrating `(8)`
backwards from infinity and dividing by `sqrt(L)` gives `(5)`.  Under `(6)`, the elementary tail
bound

```text
integral_L^infinity exp(-sigma t)t^(m-1/2)dt
 =O(exp(-sigma L)L^(m-1/2))                             (9)
```

gives the first estimate in `(7)`.  Equation `(8)` also yields

```text
F'(L)=Phi'(L)/(2L)-F(L)/(2L).                           (10)
```

If `beta=0`, `(9)`--`(10)` give the stated bound for `F'`.  Since

```text
u'(r)=-F'(L)/r,
```

its squared integral is bounded by a constant times

```text
integral^infinity exp(-(2sigma-1)L)L^(2m-2)dL,
```

which is finite because `sigma>1/2`.  If `beta!=0`, `(5)` and `(10)` instead give

```text
u'(r)=beta/(2r L^(3/2))+lower order.
```

Its squared integral contains `integral^infinity exp(L)L^(-3)dL`, which diverges.  This proves
the dichotomy. `QED`

The theorem is exact at the critical threshold: for `sigma=1/2`, logarithmic powers decide `H1`
membership.  The source-faithful regular branch is expected to have integer power scale
`sigma>=1`, safely beyond this threshold.

## 2. Exact falsification of whole-packet log-grade separation

Take

```text
F_reg(L)=exp(-L)-2exp(-2L).                              (11)
```

Then

```text
integral_0^infinity F_reg=0,
(P F_reg)(L)=(2L+1)exp(-L)-(4L+1)exp(-2L).              (12)
```

Thus `F_reg` and its forcing are nonzero but flat at every inverse-log order:

```text
L^N F_reg(L) -> 0 for every N.
```

In the physical coordinate, however,

```text
u_reg(r)=r-2r^2 in H1.                                  (13)
```

Therefore no hierarchy made only of inverse-log endpoint coefficients can separate the whole
Dirichlet solution space, even when the forcing is an exponential polynomial of exactly the type
produced by finite characteristic data.

There is a more hostile obstruction.  Choose a smooth `F_flat` which equals

```text
exp(-sqrt(L))                                            (14)
```

for large `L`, and alter it on a bounded `L`-interval so that its total integral is zero.  Beyond
that interval,

```text
(P F_flat)(L)
 =[2L+2sqrt(L)+2]exp(-sqrt(L)).                          (15)
```

Both sides are flat at every inverse-log order, yet

```text
u_flat(r)=exp(-sqrt(log(1/r))) notin H1.                 (16)
```

Indeed its squared derivative integral has tail comparable to

```text
integral^infinity L^(-1) exp(L-2sqrt(L))dL=infinity.     (17)
```

This kills the implication

```text
all inverse-log coefficients vanish -> regular branch
```

for generic logarithmic equations.  Finite-dimensional compression does not repair it: a finite
detector exists only after joint separation has been proved, and `(11)`--`(17)` show that joint
separation is itself the missing source theorem.

## 3. Strongest positive survivor: two-scale rather than one-scale closure

The counterexamples do not kill the Suzuki route.  They identify its correct representation.
The half-log hierarchy is a coordinate system on the **corona quotient**, not on the whole packet.
The regular power channel must be passed to the already constructed raw screw Evans map.

For a zero mode `v in ker A_a`, define the endpoint traces when they exist by

```text
beta_+(v)=lim_(r->0) sqrt(log(1/r))v(a-r),
beta_-(v)=lim_(r->0) sqrt(log(1/r))v(-a+r).              (18)
```

Suzuki proves `B_a=D^*G_aD` on `H1_0(-a,a)` and `B_a subset A_a`.  Hence the regular connector is
unconditional once `v in H1_0` is known:

```text
v in ker A_a intersect H1_0
  iff Dv in ker(G_a:L2_0->L2_0).                        (19)
```

For the forward direction, `A_av=B_av=D^*G_aDv=0`, so `G_aDv` is constant; `G_a` lands in the
zero-mean space, hence that constant is zero.  The reverse direction follows directly from
`B_a=D^*G_aD` and `B_a subset A_a`.

Thus a trace-zero regularity theorem would identify the trace-zero square-Evans kernel with the
raw finite Evans kernel already present in the corpus.  It would not prove raw injectivity, but it
would prevent the same zero mode from evading both detectors.

## 4. Flat-tail exclusion for boundedly coupled Volterra systems

The intermediate counterexample `(14)` is forced; it does not solve a homogeneous zero-mode
system.  After every regular power term is removed, the exact zero equation should be homogeneous
at any intermediate scale.  The following theorem shows why finite prime coupling cannot support
such a scale.

Let `X` be a Banach space, let `F:[L_0,infinity)->X` be continuous and Bochner integrable, and put

```text
f(L)=||F(L)||,
g(L)=integral_L^infinity f(t)dt.                         (18a)
```

Assume `L f(L)->0` and

```text
2L F(L)-integral_L0^L F(t)dt+T(L)F(L)+E(L)=0,           (18b)
sup_L ||T(L)|| <= C,                                    (18c)
||E(L)|| <= 1/2 [L f(L)+g(L)]                           (18d)
```

for all sufficiently large `L`.

`[PROVED HERE: FLAT-TAIL EXCLUSION]` If

```text
g(L)=o(L^(-3/2)),                                       (18e)
```

then `F=0` almost everywhere on a terminal half-line.  In particular, no nonzero solution of
`(18b)` can have a superpolynomially flat `L1` tail.

### Proof

Let `I=integral_L0^infinity F`.  Since `g(L)->0`, `F(L)->0`, `L F(L)->0`, and `(18d)` gives
`E(L)->0`, passage to the limit in `(18b)` yields `I=0`.  Therefore

```text
2L F(L)+integral_L^infinity F(t)dt+T(L)F(L)+E(L)=0.     (18f)
```

Taking norms and using `(18c)`--`(18d)` gives

```text
(3L/2-C)f(L) <= 3g(L)/2.                                (18g)
```

For `L>=2C`, this implies `f(L)<=3g(L)/(2L)`.  The tail `g` is absolutely continuous and
`g'=-f` almost everywhere, hence

```text
g'(L)>=-3g(L)/(2L),
d/dL [L^(3/2)g(L)] >= 0.                                (18h)
```

If `g` were nonzero at some sufficiently large `L_1`, `(18h)` would give

```text
g(L)>=g(L_1)(L_1/L)^(3/2),
```

contradicting `(18e)`.  Thus `g(L_1)=0`, and consequently `F=0` almost everywhere for
`L>=L_1`. `QED`

The constant `3/2` is inessential.  Any error `o(Lf+g)` gives a polynomial lower bound and rules
out a superpolynomial tail.

This theorem matches the exact Suzuki structure.  The visible translation alphabet is finite at
fixed aperture, so its adjacency operator is bounded on a uniform seam carrier by

```text
2 sum_(n<=exp(2a)) Lambda(n)/sqrt(n) < infinity.         (18i)
```

The exact Volterra remainder also has the favorable local form

```text
R F(L)=integral_0^infinity
 [2F(L)-F(L+s)-F(L-s)]/(exp(s)-1)ds
 + exponentially small tail,                            (18j)
```

where the symmetric display applies away from the lower cutoff.  Taylor's formula gives

```text
||R F(L)||
 <= C sup_(L/2<=t<=3L/2)||F''(t)||+O(exp(-L/2))          (18k)
```

for bounded `C2` tails; differentiating gives the analogous `F'''` bound.  Thus every controlled
intermediate conormal scale such as `exp(-L^theta)`, `0<theta<1`, makes `R F=o(LF)`.  The
polar--Gamma smooth block is bounded, and finite prime propagation is exactly the bounded `T` in
`(18b)`.

The carrier itself is no longer mysterious.  The weighted valuation Wiener algebra
`ell^1(Z^(P_a))`, developed in
`suzuki-two-root-valuation-wiener-lift.md`, gives an absolutely convergent Neumann inverse for
`kappa L` plus Suzuki's bounded finite-prime Laurent polynomial.  It controls every oriented seam
grade at once and proves first-arrival noncancellation.  Remaining source work is sharper: realize
the exact exterior two-root Hardy amplitudes on Suzuki's completed form domain and prove that a
trace-zero pair satisfies `(18d)` after regular power jets are removed.  Once that is done,
`(18a)`--`(18h)` eliminate the entire intermediate transseries sector; no enumeration of possible
flat scales is needed.

### Bounded homogeneous coupling is now completely classified

`suzuki-bounded-seam-half-log-rigidity.md` proves a stronger vector-valued theorem for the
homogeneous pointwise part. If

```text
(2L I+T(L))F(L)=integral_(L_0)^L F(t)dt,
sup_L ||T(L)||<infinity,
```

on any Banach seam carrier, then either `F` vanishes on a terminal half-line or

```text
sqrt(L)F(L) -> beta != 0.
```

No positivity, self-adjointness, commutativity, or finite-dimensional hypothesis is needed.
Consequently finite prime adjacency and bounded polar--Gamma multiplication cannot create an
inverse-log-flat non-`H1` homogeneous cycle. The only surviving scale-gap mechanism is the
genuinely nonlocal logarithmic remainder `(18j)`. The precise next theorem is therefore not a
generic tail estimate: lift `(18j)` to the completed seam carrier and prove that it is an
integrable perturbation after half-log conjugation.

## 5. `SUZUKI-NO-INTERMEDIATE-BOUNDARY-SCALE`

`[CONJECTURE; RH-BEARING ANALYTIC GATE]` For the exact restricted Weil operator and every
`v in ker A_a`:

1. the endpoint traces `(18)` exist;
2. nonzero traces generate the already identified valuation-graded prime seams;
3. if `beta_+(v)=beta_-(v)=0`, then no inverse-log-flat non-`H1` homogeneous seam cycle exists and
   `v in H1_0(-a,a)`;
4. after subtracting every nonzero corona term, the remainder has physical power scale
   `O(r^sigma log(1/r)^m)` with some `sigma>1/2` at every endpoint and oriented seam.

The conjecture is source-specific.  It must use the exact polar--Gamma remainder and the finite
von-Mangoldt translation alphabet.  Generic logarithmic ellipticity cannot prove it because of
`(14)`--`(17)`.

If this conjecture holds, the zero kernel has the exact alternative

```text
ker A_a \ {0}
 = {nonzero corona state}
   disjoint-union
   {H1_0 zero mode whose derivative lies in raw ker G_a}. (20)
```

RH then reduces to two honest and nonredundant source theorems:

```text
CORONA: exact prime--Gamma transport has no nonzero two-ended corona state;
REGULAR: the raw Evans Gram M_a^*M_a is positive definite for every aperture. (21)
```

Neither condition may be replaced by the other.

## 6. Literature correction and novelty boundary

Chen--Weth proved `O(log^(-tau))` boundary decay for every `tau<1/2`.  The 2024 theorem of
Hernandez-Santamaria--Lopez Rios--Saldana subsequently proved the optimal upper rate
`O(log^(-1/2))` and a Hopf lower bound of the same order for nontrivial nonnegative
supersolutions with an interior sphere condition.  Their torsion solution has two-sided
`log^(-1/2)` bounds.

These results validate the critical scale but do not provide: a signed boundary trace limit, a
polyhomogeneous expansion, trace-zero `H1` regularity, exclusion of `(14)`-type intermediate
scales for the Suzuki perturbation, or the raw/corona kernel decomposition `(20)`.  Those are the
live new claims.

## No-go closure

- **Exact killing mechanism:** `(11)`--`(13)` give a nonzero exponential-polynomial particular
  solution invisible to all inverse-log grades; `(14)`--`(17)` give an inverse-log-flat non-`H1`
  solution.  Therefore whole-packet log-quasianalytic separation is false without a source scale
  gap.
- **Strongest positive survivor:** exact Volterra representation `(5)`, sharp `H1` dichotomy
  `(7)`, bounded-coupling flat-tail exclusion `(18a)`--`(18h)`, and regular/raw connector `(19)`
  force the two-channel architecture `(20)`--`(21)`.
- **New insight:** inverse-log flux detects only the corona quotient.  RH proof must exclude an
  intermediate transseries sector and then combine corona no-return with raw Evans positivity.
- **Status:** model theorem paper-proved; external novelty audit found optimal boundary bounds but
  no trace-zero/source-scale-gap theorem; full Suzuki scale gap remains open.  Formal tree lacks
  logarithmic boundary calculus, so an abstract Lean wrapper would not certify this theorem.

## Gates

- [x] corpus raw/completed mismatch retained
- [x] current optimal logarithmic-Laplacian boundary theorem audited
- [x] exact principal trace representation proved
- [x] exponential-forcing corona/`H1` dichotomy proved
- [x] regular power channel shown invisible to every inverse-log grade
- [x] intermediate inverse-log-flat non-`H1` channel constructed
- [x] whole-packet log-grade separation falsified
- [x] boundedly coupled homogeneous flat tails excluded by a Volterra tail theorem
- [x] bounded pointwise seam systems classified by a nonzero half-log trace alternative
- [x] full scale-gap reduced to a uniform exact-remainder/seam-carrier bound
- [x] strongest two-channel survivor extracted
- [ ] prove endpoint trace existence for exact Suzuki zero modes
- [ ] exclude inverse-log-flat non-`H1` homogeneous seam cycles
- [ ] prove trace-zero `H1_0` lift
- [ ] identify trace-zero square-Evans kernel with raw Evans kernel
- [ ] prove corona no-return
- [ ] prove raw Evans Gram positivity for every aperture
- [ ] `det N_(a,0)!=0` for every aperture
- [ ] RH

## Log

- 2026-07-22 -- Created after source/literature audit falsified whole-packet inverse-log
  separation and replaced it with exact corona/regular two-scale closure.
