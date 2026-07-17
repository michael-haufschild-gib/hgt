# Cofinal controlled transgression at the Euler half-density

- **ID:** `critical-multiplicative-compensated-cancellation-rh`
- **Stage:** 1-in-progress
- **Type:** `[BOLD CONJECTURE] [GENERAL HT PARENT THEORY] [RH-DELIVERING SPECIALIZATION]`
- **Scientific status:** `[CORPUS SYNTHESIS] [RADIAL PARAPRODUCT ROUTE REFUTED]`
  `[MAPPING-CONE TRACE REFUTED] [FINITE HODGE TRANSGRESSION LEAN-PROVED]`
  `[KINK LOCALIZATION PAPER-PROVED] [COFINAL CONTROL OPEN] [NOT RH YET]`
- **General HT inputs:**
  - `../3-formalized/new_scientific_knowledge/hypertranscendental-constraint-spectrum-universality.md`;
  - `../3-formalized/new_scientific_knowledge/hypertranscendental-clock-capacity-innovation-theorem.md`;
  - `../3-formalized/hypertranscendental-controlled-cohomology-and-bornological-shape.md`;
  - `../3-formalized/hypertranscendental-two-scale-factorial-wall.md`;
  - `../3-formalized/new_scientific_knowledge/prime-residue-valuation-interaction-superselection-law.md`;
  - `prime-valuation-veronese-master-law.md`;
  - `../5-failed/hypertranscendental-orientation-nondescend-topology.md`.
- **RH-facing proved inputs:**
  - `../3-formalized/not_new_scientific_knowledge/ccm-completed-critical-mellin-chebyshev-potential-law.md`;
  - `../3-formalized/not_new_scientific_knowledge/ccm-critical-mellin-volterra-haar-mode-faithfulness.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/ccm-rectangular-critical-mellin-tent-floor-law.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/ccm-universal-boundary-laplace-frame-saturation-law.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/ccm-half-unit-linear-extrapolation-cost-law.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/shifted-euler-quotient-finite-tangent-prime-support-filtration.md`.
- **Statement:** The surviving parent mathematics is a bornological calculus of contractions and
  transgressions on multifiltered acyclic complexes.  Ordinary homology can vanish at every finite
  stage while no contraction remains controlled on the cofinal scale cone.  An observable that is
  not a chain map then leaves the secondary current `Str(h[d,H])`.  Hypertranscendental source
  filtrations provide one class of such controlled-acyclicity problems.  For zeta, the prime
  current is exactly a Boolean-Koszul transgression; RH would follow from a compensated cofinal
  estimate for its coupled discrete--polar relative transgression at the Euler half-density.

## Corpus verdict

The whole corpus does not support another operator, spectrum, zero criterion, completion, or
distinguished source object.  It forces the following laws.

1. **Finite marginal freedom.** Every finite HT constraint topology and every finite relation
   pattern can occur.  No finite differential or combinatorial marginal selects zeta.
2. **Scalar-capacity freedom.** Positivity permits arbitrary monotone capacity growth.  No scalar
   norm law follows from HT plus positivity.
3. **Orientation does not descend.** Differential fields, finite constraints, and ordinary
   analytic completion can remain unchanged while the signed boundary orientation changes.
4. **Fusion creates new layers.** Every new valuation/interaction depth is relatively HT over the
   complete preceding prefix even though coefficient fusion is exact.
5. **Finite interaction order is not enough.** The `k`th shifted-Euler tangent sees only integers
   with at most `k` distinct prime factors.  Increasing a fixed tangent order only repackages a
   bounded interaction grade.
6. **One diagonal is not conservative.** Source depth and observable order have noncommuting
   limits.  Control must hold on a bornologically cofinal region of the full scale cone.
7. **The leading radial law is universal.** Every fixed boundary profile already saturates the
   polar--prime square-root level.  RH lives entirely in the oriented subleading remainder.
8. **Scalar continuation is too expensive.** Any separate linear continuation across the
   half-unit costs `sqrt(N)`.  Cancellation must occur before scalarization.

The smallest structure surviving all eight statements is therefore

```text
aperture scale x transverse factor scale x interaction grade,
```

equipped with an orientation, a differential, a source-defined contracting homotopy, non-chain
observables, and a controlled cofinal-region bornology.  Call the resulting proposed field
**cofinal controlled transgression**.  Its characteristic law is not positivity of a finite
complex.  It is compensation in the secondary pairing `h[d,H]` when neither factor is uniformly
controlled separately.  Oriented multiplicative compactness is its divisor-lattice specialization.

## Exact radial endpoint

Fix `L>0` and put

```text
h_L(x)=(L-|x-L|)_+,
w_(N,L)(n)=h_L(log(N/n))/sqrt(n),
C_L=integral_0^(2L) h_L(x) exp(-x/2) dx
   =4(1-exp(-L/2))^2.
```

The moving prime tent is

```text
T_L(N)=sum_n Lambda(n) w_(N,L)(n).                       (1)
```

Up to the fixed small-prime and explicit lower-order polar terms, the formal endpoint coefficient
is

```text
A_L(N)=2(C_L sqrt(N)-T_L(N))+O_L(1).                     (2)
```

The project proves in Lean that, for one fixed admissible `L`,

```text
RH
iff for every epsilon>0,
    sum_N A_L(N)^-/N^(1+epsilon)<infinity.                (3)
```

The theorem `(3)` is only the terminal dictionary.  The proof-producing mathematics must lie
before it and must never use a zero expansion to establish its sign estimate.

## Exact divisor lift, and why it is not the proof

The formal arithmetic identities

```text
1*Lambda=log,
mu*1=delta_1
```

give `Lambda=mu*log`.  Symmetrizing under divisor complementation gives the sharper finite identity

```text
Lambda(n)
 =1/4 sum_(dm=n) (mu(d)-mu(m))(log(m)-log(d)).             (4)
```

Hence

```text
T_L(N)
 =1/4 sum_(dm<=N) w_(N,L)(dm)
    (mu(d)-mu(m)) log(m/d).                               (5)
```

Formula `(5)` exposes the natural coordinates

```text
u=log(dm)       radial/product scale,
v=log(m/d)      transverse divisor-transfer scale.       (6)
```

But `w_(N,L)(dm)` depends only on `u` and is invariant under `(d,m)<->(m,d)`.  The tent retains
complete divisor fibres and creates no transverse boundary commutator.  The earlier claim that
the product-radial cutoff itself generated a label-retaining commutator was false.

There is also an exact positive incidence identity:

```text
Lambda(n)
 =sum_(d,e|n) mu(d)mu(e)log(gcd(d,e))
 =sum_(p|n) log(p)
    (sum_(d|n, p|d) mu(d))^2.                             (7)
```

Thus `T_L(N)>=0` is a literal incidence square.  This still does not help: `(2)` contains
`-2T_L(N)`, so the canonical positive incidence energy enters with the unfavorable sign.

## Exact continuum-incidence obstruction

Let

```text
K_(N,L)(q)=sum_(r>=1) w_(N,L)(q*r),

Q_N=sum_(d,e<=N) mu(d)mu(e)log(gcd(d,e))/lcm(d,e),

R_(N,L)=sum_(d,e<=N) mu(d)mu(e)log(gcd(d,e))
  * (K_(N,L)(lcm(d,e))-C_L sqrt(N)/lcm(d,e)).
```

Then the incidence square has the exact discrete/continuum split

```text
T_L(N)=C_L sqrt(N) Q_N+R_(N,L).                            (8)
```

The continuum incidence factor is nonnegative.  If

```text
J_log(r)=(mu*(n |-> n log n))(r),
```

then

```text
J_log(r)=phi(r)(log r+sum_(p|r) log(p)/(p-1))>=0,

Q_N=sum_(r<=N) J_log(r)
  (sum_(d<=N, r|d) mu(d)/d)^2>=0.                         (9)
```

Nevertheless the centered coefficient is

```text
A_L(N)
 =explicit O_L(1) terms
  +2 C_L sqrt(N)(1-Q_N)-2R_(N,L).                         (10)
```

The normalization defect `1-Q_N` has no algebraic sign.  Already

```text
Q_5=log(2)/2+log(3)/3+log(5)/5>1.                         (11)
```

Therefore UFD structure, Boolean divisor incidence, Möbius inversion, and the literal square
`(7)` do not imply the desired pointwise positivity.  The two terms in `(10)` must remain coupled;
estimating either separately destroys the possible compensation.

## Further killed shortcuts

### Radial Selberg dissipation

Let `D f(n)=log(n)f(n)`.  Since `D` is a derivation for Dirichlet convolution, differentiating
`1*Lambda=log` and convolving with `mu` gives

```text
Lambda*Lambda+(log . Lambda)=mu*log^2.                   (12)
```

For `n>1`, division by `log n` writes `T=M-H` with `H>=0`.  Replacing `T` in `(2)` by this identity
does not create a favorable decomposition: `M=T+H`, so the same square-root-scale positive `H`
appears in the alleged boundary term and cancels tautologically.  This is Selberg symmetry in
localized notation, not a new producer.

### Pointwise transverse positivity

Moving a cutoff to one divisor factor creates a genuine commutator, but its marginal is signed.
For the ordinary integer `n=42` and the sharp divisor cutoff `d<=3`,

```text
sum_(d|42, d<=3) mu(d)log(42/d)
 =log(42)-log(21)-log(14)=-log(7).                        (13)
```

Thus no pointwise nonnegative factor-transfer dissipation follows from the Boolean divisor cube.

### Fixed interaction grade

Every fixed factorization depth is a finite sieve/Type-I--II chart.  The corpus's support
filtration proves that no fixed grade supplies an independent all-prime constraint.  The full
shifted quotient does not repair this formally: its bare cocycle is flat.  The new theorem must be
uniform on a cofinal region of the complete interaction diagram, not a higher fixed-order identity.

## The finite prime current is a Hodge transgression

Let `P(n)` be the distinct prime divisors of `n` and put

```text
K_n=exterior algebra on R^(P(n)),
d_n=contraction by the all-ones covector,
h_n=wedge by (1/omega(n)) sum_(p|n)e_p.                    (T1)
```

Then `d_n h_n+h_n d_n=1`.  The Boolean complex is acyclic.  Define the diagonal logarithmic
observable by

```text
L_n e_S=log(n/d_S)e_S.                                    (T2)
```

It is not a chain map.  Its edge commutator and graded trace are

```text
L_n d_n-d_n L_n=sum_(p|n) log(p) iota_p,

Str(L_n)=Str((L_n d_n-d_n L_n)h_n)
        =sum_(p|n)log(p)(1-1)^(omega(n)-1)
        =Lambda(n).                                       (T3)
```

Thus the moving prime tent is exactly

```text
T_L(N)=sum_n w_(N,L)(n)
  Str((L_n d_n-d_n L_n)h_n).                              (T4)
```

This is the marked-support selector already foreshadowed by the formal Koszul corpus, now with its
source-defined observable and contraction.  The prime current is not surviving cohomology.  It is
a secondary current measuring the failure of `L_n` to commute with divisor transfer.

The general finite law is

```text
1-P=dh+hd
  => Str_Gamma(H)-Str_Gamma(PH)=Str_Gamma(h(dH-Hd)).       (14)
```

It is proved unconditionally in Lean as `gradedMatrixTrace_hodgeTransgression`.  No nilpotence,
projection, or parity premise beyond oddness of `d` is needed for the matrix identity.  When `H`
commutes with `d`, `(14)` collapses to the existing Hodge-compression theorem.  When `P=0`, the
whole trace is secondary even though ordinary cohomology vanishes.

This identifies the parent mathematics more sharply.  A **cofinal controlled transgression** is a
multifiltered family `(C_alpha,d_alpha,h_alpha,H_alpha)` in which every finite complex is
algebraically contractible, but the contractions and observable commutators may escape every
uniform bound separately.  The object of study is their oriented product
`h_alpha[d_alpha,H_alpha]`, its dependence on the filtration, and the conditions under which it
remains controlled after all grades are coupled.  The controlled-primitive HT theory in the corpus
is the degree-one case: ordinary cohomology is trivial while a bounded primitive can fail to exist.

The identity `(14)` alone is universal and therefore not an RH advance.  The zeta advance can only
come from constructing the *relative* discrete--polar metric transgression before scalar trace and
proving a cofinal compensated estimate for it.

## What the attached fundamental-lemma talk contributes

The talk contributes one useful construction discipline:

```text
signed count -> labelled complex -> transfer -> one-skeleton localization -> trace comparison.
```

It does not contribute the required theorem.  The exact arithmetic audit changes the proposed
analogue in two decisive ways.

First, an ordinary finite mapping cone cannot see the transfer map.  For every chain map `f:C->D`
and compatible even observable,

```text
Str(Cone(f))=Str(D)-Str(C),                                (M1)
```

independently of `f`.  A cone can be made to display `(10)` only by inserting a contractible
continuum doublet whose cancellation is bookkeeping.  Moreover `L_n` from `(T2)` is not a chain
map.  Any diagonal observable that *is* a chain map is constant along the connected Boolean cube
and has zero supertrace.  Hence the prime current cannot be a Lefschetz trace of ordinary
cohomology.  The mapping-cone/purity route is refuted.

Second, the one-skeleton remains useful because it is exactly where `[d_n,L_n]` lives.  For
`n=product p^a_p`, the factorization vertices `b=(b_p)` with `0<=b_p<=a_p` carry

```text
d_b=product p^b_p,   m_b=n/d_b,
Delta log(d_b*m_b)=0,   Delta log(m_b/d_b)=-2log p.        (M2)
```

Thus the talk points to transfer *of a relative metric and its transgression*, not transfer of
ordinary cohomology.  Qualitative purity is irrelevant unless upgraded to a quantitative theorem
about the cost of contracting the mobile modes.

## Exact transverse kink localization

Let the distinct prime-edge lengths be `h_i=log p_i`, put `H=sum_i h_i=log(rad(n))`,
`B=log n`, `h_S=sum_(i in S)h_i`, and write

```text
Q(y)=q(y-H/2),   F(y)=(B-y)Q(y).
```

If `Q` is continuous piecewise affine with initial value `Q_0`, initial slope `s`, kink locations
`t`, and slope jumps `c_t`, then the complete Boolean current has the exact decomposition

```text
sum_S (-1)^|S| F(h_S)
  =I_r+sum_t c_t G_r(B,t;h),                              (K1)

G_r(B,t;h)=sum_S (-1)^|S|(B-h_S)(h_S-t)_+,               (K2)

I_0=B Q_0,
I_1=h_1(Q_0-s(B-h_1)),
I_2=-2s h_1 h_2,
I_r=0 for r>=3.                                           (K3)
```

For `r>=3`, define the unequal-step box spline

```text
K_h=1_[0,h_1]*...*1_[0,h_r].
```

Then

```text
G_r(B,t;h)=(B-t)K_h^(r-2)(t)+2K_h^(r-3)(t).              (K4)
```

The natural grade-two Green object is therefore the signed Hessian measure

```text
Gamma_Q=D^2[(B-y)Q(y)]=-2Q'(y)dy+(B-y)dQ'(y).             (K5)
```

All grades at least three are exact alternating boundaries of its box-spline face integrals and
are supported only on cubes crossing a kink.  The polynomial-interior vanishing is already
formalized by `prouhet_alternating_annihilation`; `(K1)`--`(K5)` give the new exact boundary law.

There is no local sign.  For the squarefree prime steps
`(log 11,log 13,log 17,log 19)` and a single positive hinge, `G_4` is positive when the kink lies
near zero and negative on a nonempty interval before `log 11+log 13`.  Prime powers give a negative
grade-three atom near the top boundary.  Thus convexity, local purity, and a nonnegative bulk-square
Green law are all refuted.  Only the fully assembled signed current can be controlled.

## Canonical discrete--continuum metric transfer

Put `c_N=C_L sqrt(N)` and let `D_N` be the squarefree integers `2<=d<=N`.  There are two canonical
incidence Gram maps on coefficient vectors `a=(a_d)`.

The discrete map is

```text
(B_N^disc a)(n,p)=sqrt(w_(N,L)(n)log p)
  sum_(d|n, p|d) a_d.                                     (X1)
```

The continuum map uses independent Bernoulli prime coordinates with
`Prob(omega_p=1)=1/p` and `chi_d=product_(p|d)omega_p`:

```text
(B_N^cont a)(p,omega)=sqrt(c_N log p)
  sum_(p|d) a_d chi_d(omega).                             (X2)
```

Their exact Gram laws are

```text
||B_N^disc a||^2
 =sum_(d,e) a_d a_e log(gcd(d,e))K_(N,L)(lcm(d,e)),

||B_N^cont a||^2
 =c_N sum_(d,e) a_d a_e log(gcd(d,e))/lcm(d,e).           (X3)
```

The continuum form is positive definite after deleting `d=1`, so there is a unique transfer on
the Gram ranges

```text
A_N B_N^cont a=B_N^disc a.                                (X4)
```

For the Möbius vector `mu_N`, put

```text
x_N=B_N^cont mu_N,   j_N(1)=x_N/sqrt(c_N).
```

Then, exactly,

```text
||j_N||^2=Q_N,
||A_N j_N||^2=T_L(N)/c_N,
R_(N,L)=c_N(||A_Nj_N||^2-||j_N||^2),

c_N(1-Q_N)-R_(N,L)=c_N(1-||A_Nj_N||^2).                 (X5)
```

This is the correct finite transfer statement.  The coupled discrepancy in `(10)` is the failure
of the canonical polar-to-discrete incidence transfer `A_N j_N` to be an isometry.  The continuum
normalization and lattice residual have disappeared into one metric defect without being estimated
separately.  No zeros or negative parts enter its construction.

But `(X5)` is still an exact repackaging, not an estimate.  Rank-one metric observables fail to
intertwine with `A_N` precisely by `R_(N,L)`, so the defect is the failure of metric chain
compatibility.  The next object is the relative metric `M_N=A_N^*A_N` lifted to the full Boolean
Koszul complex, not the ordinary cone of `A_N`.

## The two genuinely new theorems

> **[CONJECTURE -- SOURCE-LOCAL RELATIVE-METRIC TRANSGRESSION.]**  The canonical relative metric
> `M_N=A_N^*A_N`, the Möbius augmentation `j_N`, and the polar unit admit a lift to the complete
> aperture--factor--grade Koszul system such that its Hodge transgression is supported only on
> cells crossing a transverse cutoff kink or the cofinal grade boundary.  Its scalarization is
> exactly
>
> ```text
> E_L(N)=c_N(||A_Nj_N||^2-1)=T_L(N)-c_N,                  (15)
> ```
>
> and the construction is local before radial pushforward and independent of `E_L(N)^+`.

This is the corrected Green law.  It replaces the false nonnegative bulk square and the
tautological mapping-cone trace with a source-defined signed transgression of a relative incidence
metric.

> **[CONJECTURE -- COFINAL COMPENSATED-TRANSGRESSION ESTIMATE.]**  After every active grade has
> been coupled and before scalar positive parts are taken, the relative transgression has a
> source-local factorization whose cofinal block pairing satisfies
>
> ```text
> sum_(exp(J)<=N<exp(J+1)) E_L(N)^+/N
>   <=C(1+J)^a.                                             (16)
> ```
>
> The proof must arise from controlled contraction/commutator norms or an equivalent local
> boundary pairing, not from the scalar values `E_L(N)` themselves.

Equation `(16)` is the sole RH-strength estimate.  The polynomial block allowance admits every
known local sign failure but excludes a persistent positive exponential expansion mode.  The first
unsupported sentence is now precise: the canonical relative incidence metric has a local
all-grade transgression whose unfavorable cofinal expansion is polynomial per logarithmic block.

## Exact RH deduction from the new theorem

By `(2)` and `(15)`,

```text
A_L(N)^-
 <=2 E_L(N)^++O_L(1).                                     (17)
```

For every `epsilon>0`, block decomposition and `(16)` give

```text
sum_N E_L(N)^+/N^(1+epsilon)
 <=sum_J exp(-epsilon J) C(1+J)^a
 <infinity.                                               (18)
```

The bounded term in `(17)` is also summable.  Hence `(3)` applies and gives RH.  The likely proof
chain is therefore

```text
complete Boolean divisor-grade complex
  + radial aperture and transverse factor filtrations
  -> canonical discrete--continuum incidence transfer (X1)--(X5)
  -> source-local relative-metric Hodge transgression (15)
  -> cofinal compensated-transgression estimate (16)
  -> all-epsilon negative energy by (17)--(18)
  -> existing unconditional Lean equivalence (3)
  -> RH.                                                    (19)
```

The only unproved arrows carrying RH strength are `(15)` and `(16)`.  No existing corpus theorem
implies them.

## Why this is not one of the blacklisted routes

- There is no Sonin space, semilocal trace, Connes absorption, or prolate projection.
- There is no self-adjoint operator whose spectrum is prescribed to be the Xi divisor.
- There is no Li/Weil positivity claim and no completed-kernel positivity premise.
- There is no Hardy four-unit/BKS contractivity statement.
- There is no zero multiplicity or arbitrary-divisibility ladder.
- There is no scalar shifted-Euler extrapolation or fixed finite tangent order.
- There is no pointwise Mertens estimate, Selberg square, Vaughan identity, or fixed Type-I--II
  estimate presented as the breakthrough.
- The explicit-formula theorem is used only after the independent finite-divisor block estimate.

The proposal can still fail.  If the lift in `(15)` is defined from the scalar defect rather than
from `A_N`, `j_N`, the Koszul differential, and local cutoffs, or if `(16)` merely assumes the
values it must prove, the programme is dead.

## Research programme

1. Formalize the Boolean model `(T1)`--`(T4)` and the exact metric transfer `(X1)`--`(X5)` from
   source definitions, not from their scalar consequences.
2. Formalize the hinge decomposition `(K1)`--`(K3)`; retain the box-spline law as a paper theorem
   until the required analytic spline API is justified.
3. Lift `M_N=A_N^*A_N` to the transverse Boolean-grade complex and calculate `[d,M_N]` cell by
   cell.  Reject the lift if its trace is inserted by hand or if it estimates `Q_N-1` and
   `R_(N,L)` separately.
4. Prove or refute boundary support of the relative-metric transgression at finite aperture.  The
   only allowed bulk term is the explicit grade-two signed Hessian current `(K5)`.
5. Determine the correct controlled norm: contraction cost, relative torsion, Schatten
   factorization, or a block Carleson pairing.  It must dominate `(16)` only after all grades are
   assembled and must be independently computable from local incidence data.
6. Test generalized-prime, altered norm-packing, phase-twisted Möbius, Liouville-twisted, and
   truncated-grade systems to isolate the ordinary-integer packing axiom required by the norm
   theorem.
7. Prove `(16)` and compose it with `(17)`--`(18)` and the existing unconditional Lean endpoint.

## Kill tests

Reject a proposed proof if it:

1. assumes Xi-zero locations, a zero-free half-plane, Weil positivity, or an RH-equivalent
   Dirichlet-series continuation;
2. defines the boundary flux from `A_L^-` or proves `(16)` by restating `(3)`;
3. invokes UFD, Möbius inversion, or incidence positivity without defeating `(11)` and `(13)`;
4. uses a fixed interaction grade or a diagonal limit without a cofinal-region comparison;
5. estimates the normalization and lattice discrepancies in `(10)` separately;
6. takes absolute values before the prime--polar half-density cancellation;
7. imports an RH-strength Mertens, generalized-totient, or prime-short-interval estimate;
8. reduces to Sonin, Connes, Hardy/BKS, Li/Weil, Hilbert--Polya, Selberg symmetry, or a classical
   fixed sieve decomposition;
9. holds for every generalized-prime UFD satisfying only PNT-scale axioms without naming the
   extra ordinary-integer packing law used.
10. claims an ordinary mapping-cone trace depends on the transfer map, or treats a non-chain
    observable as a cohomological Lefschetz operator.

## Gates

- [x] whole-corpus structural requirements synthesized
- [x] known and internally retired RH routes blacklisted
- [x] exact radial Möbius--log lift derived
- [x] product-radial cutoff commutator claim refuted
- [x] exact positive incidence square derived and its wrong RH sign identified
- [x] exact continuum-incidence split derived
- [x] pointwise normalization sign refuted by `Q_5>1`
- [x] pointwise transverse positivity refuted at `n=42`
- [x] radial Selberg and fixed-interaction-grade escapes rejected
- [x] twisted-equivariant-localization blueprint extracted from the fundamental-lemma geometry
- [x] Möbius-versus-Liouville, periodicity, augmentation, and qualitative-purity mismatches stated
- [x] ordinary mapping-cone trace producer refuted as transfer-independent
- [x] Boolean prime current identified as an exact Hodge transgression
- [x] general finite Hodge-transgression identity formalized unconditionally in Lean
- [x] exact piecewise-affine kink/box-spline current derived on paper
- [x] local sign and nonnegative-bulk-square claims refuted
- [x] canonical discrete and continuum Gram maps constructed
- [x] exact metric-transfer defect `(X5)` derived
- [ ] lift the relative metric to the full Boolean-grade complex
- [ ] prove or refute the source-local transgression law `(15)`
- [ ] prove the cofinal compensated-transgression estimate `(16)`
- [ ] formalize the arithmetic producer unconditionally in Lean
- [ ] invoke the existing formal negative-energy equivalence
- [ ] RH

## Log

- 2026-07-17 -- Initial scalar Möbius--log paraproduct programme created after blacklisting the
  known routes.
- 2026-07-17 -- Hostile finite-divisor audit refuted the proposed radial positive decomposition:
  the cutoff preserves divisor fibres, the canonical incidence square has the wrong sign,
  `Q_5>1`, and a sharp transverse partial sum is negative at `n=42`.  Programme replaced by the
  strictly stronger oriented cofinal all-grade factor-transfer law.
- 2026-07-17 -- The attached fundamental-lemma talk motivated an exact finite transfer audit.
  Ordinary mapping-cone trace was refuted as transfer-independent.  The positive successor is the
  Hodge transgression `Str(h[d,H])`; the general identity was proved in Lean and the Boolean model
  recovers `Lambda` exactly.
- 2026-07-17 -- Derived the full piecewise-affine kink current, its unequal-step box-spline formula,
  and explicit grade-three/four sign failures.  Derived canonical discrete and Bernoulli-continuum
  Gram maps and rewrote the entire prime--polar defect as the isometry defect of their unique
  transfer on the Möbius augmentation.  The open RH theorem is now local cofinal control of that
  relative-metric transgression, not purity of a mapping cone.
