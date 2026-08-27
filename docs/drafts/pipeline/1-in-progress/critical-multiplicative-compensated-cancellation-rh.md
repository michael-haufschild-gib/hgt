# Cofinal controlled transgression at the Euler half-density

- **ID:** `critical-multiplicative-compensated-cancellation-rh`
- **Stage:** 1-in-progress
- **Type:** `[BOLD CONJECTURE] [GENERAL HT PARENT THEORY] [RH-DELIVERING SPECIALIZATION]`
- **Scientific status:** `[CORPUS SYNTHESIS] [RADIAL PARAPRODUCT ROUTE REFUTED]`
  `[MAPPING-CONE TRACE REFUTED] [FINITE HODGE TRANSGRESSION LEAN-PROVED]`
  `[KINK LOCALIZATION PAPER-PROVED] [ONE-BODY METRIC LIFT REFUTED]`
  `[DOUBLED COVARIANT LIFT PAPER-PROVED] [RAW NORM ROUTES REFUTED]`
  `[POSITIVE CLARK PRODUCER REFUTED] [SIGNED SOURCE DIFFERENTIAL OPEN]`
  `[FINITE DOOB SEWING PAPER-PROVED] [DOOB/WALSH COFINAL COMPLETIONS REFUTED]`
  `[MULTISCALE BUCHSTAB PROVIDER REFUTED] [TYPE-II APERTURE PROVIDER REFUTED]`
  `[HARMONIC-FLOOR STOKES REDISCOVERED] [NULL GAUGE PAPER-PROVED]`
  `[RANK-ONE FATHER EXTENSIONS REFUTED] [MOVING-FRONT SCALAR DIAGNOSTIC COARSER THAN LCM CORE]`
  `[CLASSICAL ENDPOINT DISPERSION REFUTED] [SQUARE-CARRIER PROVIDER REFUTED]`
  `[POSITIVE RATIO AVERAGING RH-EQUIVALENT]`
  `[INTEGRATED CAUSAL--LCM SPLICE PAPER-PROVED] [FULL COAREA DEFECT PAIRING OPEN]`
  `[WEIGHTED COAREA FIBRE PAPER-PROVED] [WEIGHTED TRACE PROVIDER REFUTED]`
  `[BERNOULLI DENSITY VACUUM REFUTED AS JOINING]`
  `[ROOT-FOURIER BRIDGE PAPER-PROVED] [CLASSICAL ROOT LARGE SIEVE REFUTED]`
  `[STOPPED ANOVA COMPENSATOR REFUTED]`
  `[MODERN MULTIPLICATIVE-CORRELATION SAVINGS INSUFFICIENT]`
  `[SPECTRAL/KLOOSTERMAN DISPERSION PROVIDER REFUTED]`
  `[FCRJ RH-EQUIVALENT CHECKPOINT OPEN] [SIGNED INTERVAL-LOCAL CAUSAL TRACE OPEN] [NOT RH YET]`
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
  - `../3-formalized/not_new_scientific_knowledge/ccm/ccm-half-unit-linear-extrapolation-cost-law.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/shifted-euler-quotient-finite-tangent-prime-support-filtration.md`.
- **Statement:** The surviving parent mathematics is oriented additive--multiplicative cofinal
  transgression: nested additive sampling apertures carry multiplicative acyclic Boolean complexes,
  and the complete real horizontal orientation must be reduced before any norm is taken.  An
  observable that is not a chain map leaves the secondary current `Str(h[d,H])`.  For zeta, both
  the von Mangoldt current and the complete prime--polar defect are exact finite Hodge
  transgressions on a doubled divisor complex.  The sole RH-bearing step is a source-space
  Carleson theorem coupling those transgressions across apertures through coherent ordinary-integer
  floor packing.  Hypertranscendental controlled-primitive failures are one general class of the
  same cofinal phenomenon.

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
observables, an additive-aperture transport, and a controlled cofinal-region bornology.  Call the
resulting proposed field **oriented additive--multiplicative cofinal transgression**.  Its
characteristic law is not positivity of a finite complex or smallness of an ordinary operator
ideal.  It is horizontal compensation in the secondary pairing `h[d,H]`, followed by a
cross-aperture Carleson law on the reduced oriented section.  The ordinary divisor-lattice
specialization is selected by coherent principal-ideal floor packing.

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

Str(L_n)=Str(h_n(d_nL_n-L_nd_n))
        =Str((L_n d_n-d_n L_n)h_n)
        =1/omega(n) sum_(p|n)log(p)(1-1)^(omega(n)-1)
        =Lambda(n).                                       (T3)
```

The raw `1/omega(n)` is essential and disappears only after the singleton selector has forced
`omega(n)=1`.  The second equality uses odd graded cyclicity of `h_n`; both this rotation and its
right-oriented acyclic Hodge specialization are now proved unconditionally in Lean.

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

This identifies the parent mathematics more sharply.  An **oriented additive--multiplicative
cofinal transgression system** is a nested family `(C_alpha,d_alpha,h_alpha,H_alpha)` in which
every finite multiplicative fibre is algebraically contractible, but the contractions and
observable commutators may escape every uniform bound separately.  A horizontal orientation is
reduced before norming, and a second additive-aperture transport compares the resulting sections.
The object of study is the source-space Carleson behavior of `h_alpha[d_alpha,H_alpha]`, not its
raw Schatten size.  The controlled-primitive HT theory in the corpus is the degree-one shadow:
ordinary cohomology is trivial while a bounded oriented primitive can fail to exist.

The identity `(14)` alone is universal and therefore not an RH advance.  The finite doubled
prime--polar transgression is constructed below.  The zeta advance can only come from a
non-spectral source-space factorization and a cross-aperture Carleson theorem after complete real
Möbius orientation.

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

But `(X5)` is still an exact repackaging, not an estimate.  The attempted local lift of the
one-body metric `M_N=A_N^*A_N` is now refuted.  In canonical whitened incidence coordinates,

```text
Mbar_N=(1/c_N)J^(-1/2)Z^(-1)D G_disc D Z^(-T)J^(-1/2),
J=mu*(n |-> n log n),                                     (X6)
```

and, for `r=pR`,

```text
(Mbar_N)_(pR,p)
 =p log(p)/(c_N sqrt(J(pR)J(p)))
   sum_(t|R)mu(R/t)kappa_N(pt),
kappa_N(q)=q K_(N,L)(q).                                  (X7)
```

These are all multiplicative finite-difference grades.  The `p <-> pq` entry is already nonzero
for the exact family `L=log 2`, `N=4p`.  Hence the actual one-body metric mixes Boolean parity and
is nonlocal through `Z^(-1)`.  It cannot be the claimed even kink-supported observable.

## The exact doubled covariant lift `[PROVED ON PAPER]`

Let `P_N` be the primes at most `N` and take the doubled complex with basis pairs
`(S,T) subset P_N x P_N` and grading `(-1)^(|S|+|T|)`.  Put

```text
dhat_N=sum_a iota_a,
hhat_N=1/(2|P_N|)sum_a wedge_a,
dhat_N hhat_N+hhat_N dhat_N=1.                            (D1)
```

For `p|n`, let

```text
Z_(n,p)(S,T)=1_(S,T subset P(n))1_(p in S intersect T),  (D2)
```

viewed as a diagonal projector, and let `Pi_00` be the doubled empty-face projector.  Define

```text
Hhat_(N,L)
 =sum_(n<=N)w_(N,L)(n)sum_(p|n)log(p)Z_(n,p)
  -c_N Pi_00.                                             (D3)
```

Then

```text
Str_Gamma(Z_(n,p))=1_(omega(n)=1),

E_L(N)=T_L(N)-c_N
 =Str_Gamma(Hhat_(N,L))
 =Str_Gamma(hhat_N(dhat_NHhat_(N,L)-Hhat_(N,L)dhat_N)).   (D4)
```

This is noncircular and face-defined: it uses only divisor faces, marked prime incidence, aperture
weights, and the explicit polar unit.  It is not local in the full active-prime complex.  Extending
a local face projector by identity preserves locality but kills its global supertrace; freezing the
complement in its vacuum restores visibility but creates an edge in every absent-prime direction.
For a face with `r` primes those boundary blocks have singular values `sqrt(2)` and
`sqrt(2(|P_N|-r))`, each with multiplicity `4^(r-1)`.  The observable also contains an unavoidable
marked-prime bulk current and polar-vacuum edges.  The former kink-only support claim is false.

On the distinguished state the continuum transfer reduces exactly to the marked-support selector,

```text
(A_Nj_N)(1)(n,p)
 =-c_N^(-1/2)sqrt(w_(N,L)(n)log p)1_(omega(n)=1),         (D5)
```

so `(D4)` closes finite covariant-lift existence but supplies no estimate.  The local alternative
`H_n=L_n-P_empty` gives `Str(H_n)=Lambda(n)-1` and misses `E_L(N)` only by the BV quadrature
`O_L(N^(-1/2))`.  Thus one may have genuine locality or one exact global trace; the doubled model
shows the cofinal boundary cost of demanding both.

## The sole genuinely new RH-strength theorem

Ordinary contraction, torsion, Schatten, or full-Gram trace norms are now excluded.  On an
`r`-cube one can have `[H,d]h=dh`, a rank `2^(r-1)` projection with zero graded supertrace.  Phase
twists `z_p=-1`, every fixed-grade truncation, and PNT-scale generalized-prime burst systems all
violate a polynomial logarithmic-block bound while retaining the corresponding finite incidence
identities.

Inside the doubled model the polar obstruction is even sharper: the incidence operator begins in
degree two, while `-c_N Pi_00` leaves a degree-one transgression singular value exactly `c_N`.
Every ordinary Schatten norm therefore costs `sqrt(N)` at each aperture before arithmetic and
polar currents can meet.

The surviving target is an **oriented horizontal cofinal sewing and Carleson theorem**.  It needs a
second cutoff-dependent differential connecting local cubes by actual multiplication transitions
`n <-> nq` and coupling the polar current to arithmetic before norming.

The coefficients of that connection are explicit.  Put

```text
q_R=product_(p in R)p,
W_N(R)=sum_(q_R|n)w_(N,L)(n),
ell(I)=sum_(p in I)log p.
```

The doubled incidence diagonal is

```text
F_N(S,T)=ell(S intersect T)W_N(S union T).                (C0)
```

Its two edge differences are `log(q)W_N(R)` and
`ell(I)(W_N(R)-W_N(R\{q}))`.  A successful aperture connection must be built from these coherent
ordinary multiple counts.

Let `Z_N` be a genuine source space of horizontal sections with real prime-edge orientation

```text
x(dp)=-x(d),                                               (C1)
```

containing the Möbius--polar section `xi_N`.  Construct a degree-changing sewing operator `B_N`
and aperture differential `delta_N` such that

```text
J_N^loc=[delta_N,B_N]_s+R_N,                              (C1a)
```

with zero-supertrace bulk and a block-controlled residual, or equivalently construct from paired
sewn cells—not from a spectral positive part—maps `Gamma_(N,+/-)` satisfying for every `x in Z_N`

```text
tau_N(x,x)=||Gamma_(N,+)x||^2-||Gamma_(N,-)x||^2,
c_N tau_N(xi_N,xi_N)=E_L(N).                              (C2)
```

For coherent block sections `Z_J` and restrictions `rho_N`, define

```text
C_(J,+)x
 =(sqrt(c_N/N)Gamma_(N,+)rho_Nx)_(exp(J)<=N<exp(J+1)).   (C3)
```

The exact open theorem is

```text
||C_(J,+)||^2 <= C_L(1+J)^a.                              (C4)
```

It must hold on a source class larger than the evaluated defect line, with a norm fixed before
`E_L`, with a cutoff-dependent noncompact carrier, and with the distinguished section uniformly
bounded.  A fixed-`N` difference of squares is insufficient; the sewing `(C1a)` is what permits the
polar and arithmetic degrees to meet.  Then

```text
sum_(exp(J)<=N<exp(J+1))E_L(N)^+/N
 <=C_L(1+J)^a||xi||_(Z_J)^2.                             (C5)
```

The ordinary source axiom visible to this construction is coherent principal-ideal floor packing,

```text
#{b: |ab|<=x}=floor(x/|a|).                               (C6)
```

It identifies the normed free monoid with the ordinary positive integers and excludes the
generalized-prime burst countermodel.  It does not imply `(C4)`.  The new mathematics still missing
is the real-oriented all-grade cross-aperture correlation theorem for the coherent floor
remainders in `(C6)`.

## Exact RH deduction from the new theorem

By `(2)` and `(D4)`,

```text
A_L(N)^-
 <=2 E_L(N)^++O_L(1).                                     (17)
```

For every `epsilon>0`, block decomposition and `(C5)` give

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
  -> polar-augmented doubled covariant complex (D1)--(D4)
  -> coherent additive-aperture horizontal source module (C1)--(C3)
  -> cellular signed factorization (C2)
  -> oriented cofinal Carleson theorem (C4)
  -> positive block estimate (C5)
  -> all-epsilon negative energy by (17)--(18)
  -> existing unconditional Lean equivalence (3)
  -> RH.                                                    (19)
```

The doubled finite lift `(D4)` is proved on paper and is not RH strength.  The only unproved arrows
carrying RH strength are the non-spectral cellular source-space factorization `(C2)` and the
cross-aperture operator estimate `(C4)`.  No existing corpus theorem implies them.

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

The proposal can still fail.  If `Z_J` is only the evaluated defect line, if `Gamma_+` is the
spectral positive part of the already assembled scalar form, or if `(C4)` merely assumes the
values it must prove, the programme is dead.

## Research programme

1. Finish the arithmetic specialization of the Boolean model `(T1)`--`(T4)` and formalize the
   doubled face-selector identity `(D2)`--`(D4)` from source definitions.
2. Formalize the hinge decomposition `(K1)`--`(K3)`; retain the box-spline law as a paper theorem
   until the required analytic spline API is justified.
3. Treat `(X6)`--`(X7)` as the exact one-body falsifier; do not retry an even local `M_N` lift.
4. Define the horizontal source module `Z_N` from real Möbius edge orientation and the polar
   augmentation before choosing any positive factor.
5. Derive a cellwise signed factorization `(C2)` on that full source module.  It must retain the
   marked-prime bulk and outer divisor-face boundaries.
6. Construct coherent block spaces `Z_J` using the principal-ideal floor-packing maps `(C6)` and
   prove their distinguished sections are uniformly bounded.
7. Prove or refute the Carleson operator law `(C4)`.  The raw Schatten, full-Gram trace, phase-blind,
   fixed-grade, generalized-prime, and fixed-compact interpretations are already refuted.
8. Compose `(C5)` with `(17)`--`(18)` and the existing unconditional Lean endpoint.

## Kill tests

Reject a proposed proof if it:

1. assumes Xi-zero locations, a zero-free half-plane, Weil positivity, or an RH-equivalent
   Dirichlet-series continuation;
2. defines the boundary flux from `A_L^-` or proves `(C4)` by restating `(3)`;
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
11. takes a finite Schatten norm on the raw Boolean complex or a trace norm of the full Gram
    defect; the exponential-rank and `sqrt(N)log N` compressions refute both.
12. is invariant under primewise phases of the Möbius section or closes at a fixed grade.

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
- [x] local even one-body relative-metric lift refuted by `(X6)`--`(X7)`
- [x] exact doubled covariant source-local transgression `(D4)` proved on paper
- [x] full-complex Schatten, full-Gram trace, phase-blind, fixed-grade, and PNT-scale
  generalized-prime norm routes refuted
- [x] coherent principal-ideal floor packing isolated as the ordinary-integer selector
- [ ] formalize the doubled arithmetic face-selector producer unconditionally in Lean
- [ ] construct a non-spectral cellular signed factorization `(C2)` on a genuine source module
- [ ] prove the oriented horizontal cofinal Carleson estimate `(C4)`
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
- 2026-07-17 -- Refuted that last one-body step: the whitened relative metric contains every
  multiplicative finite-difference grade and already mixes `p` with `pq`.  Replaced it by the exact
  doubled covariant observable `(D3)`, whose finite Hodge transgression is exactly `T_L-c_N`.
- 2026-07-17 -- Hostile norm audit proved exponential Boolean Schatten inflation, a
  `sqrt(N)log N` full-Gram compression, phase/Liouville and fixed-grade violations, and a PNT-scale
  generalized-prime burst countermodel.  The sole surviving target is the oriented horizontal
  source-space Carleson law `(C4)`, using coherent ordinary floor packing across apertures.

## 2026-07-18 hostile audit: flat scalar horizontality collapses to the Möbius line

### Exact rigidity theorem `[PAPER-PROVED] [BRIDGE]`

Let

```text
V_N={d<=N : d is squarefree}
```

including `1`, and join `d` to `dp` whenever `p` is prime, `p` does not divide `d`, and
`dp<=N`.  Let `A` be a real vector space.  For the central-sign connection define

```text
Hor_N(A)={x:V_N->A : x(dp)=-x(d) on every prime edge}.     (C1-no-go)
```

Evaluation at the unit vertex is a linear isomorphism

```text
Hor_N(A) ~= A,

x(d)=mu(d)x(1).                                            (C1-rigidity)
```

Indeed, if `d=p_1...p_r`, every partial product lies below `d<=N`.  Repeated use of the edge
law gives

```text
x(d)=(-1)^r x(1)=mu(d)x(1).
```

Conversely that formula satisfies every edge law.  Thus for `A=R` the anchored horizontal
section space is exactly the one-dimensional Möbius line.

Omitting the unit at each finite cutoff does not create a coherent escape.  In the cofinal
squarefree graph any two primes `p,q` are joined by `p--pq--q`, so they have the same value; every
squarefree product is then fixed by one prime value.  Hence a restriction-compatible scalar
cofinal family is again one line.  The extra components visible at a small cutoff are disappearing
aperture-boundary components, not persistent source degrees.

The same conclusion holds for a fixed vector-valued fibre: central transport `-Id_A` gives one
copy of `A`, not independent arithmetic cell data.  More generally a flat invertible connection on
a connected graph has its horizontal sections determined by one fibre value, subject only to
holonomy invariance.  This is the standard signed-graph switching/flat-local-system mechanism and
is already reflected internally by
`formal/GaloisForLFunctions/HTGeometry/CoherenceFlatness.lean`.  The scalar all-negative case is
the bipartite balance law of Harary,
<https://doi.org/10.1307/mmj/1028989917>.

### Blunt verdict on `(C1)`

`[FALSIFIED AS A SCALAR SOURCE MODULE]`.  If `(C1)` is the definition of `Z_N`, then `Z_N` is the
Möbius line and a fixed-`N` factorization `(C2)` only factors the already evaluated scalar defect.
That violates the card's own requirement that the source class be larger than the defect line.

A vector-valued reading is not false, but it is presently under-typed: the fibre, its norm, its
aperture restriction maps, and the source-local action producing `tau_N` have not been defined.
Taking a large fibre can make `Hor_N(A)` large, but all of that structure then comes from the
unspecified fibre rather than from prime-edge horizontality.  Choosing the fibre or its norm from
the terminal form would merely hide the spectral positive-part construction inside `A`.

This kills the displayed carrier, not the finite transgression `(D4)` and not every possible
cofinal-sewing route.

### Relentless interrogation: stronger representation forced by the failure

The killing mechanism is flatness: treating orientation as an equation on every source vector
turns the prime graph into transport and removes the transverse degrees that `(C2)` needs.
Orientation must instead be an operator on a larger module.

For a fixed source fibre `A`, the minimal non-collapsed replacement begins with all zero-cochains

```text
X_N(A)={x:V_N->A},
(nabla_N x)(d,p)=x(dp)+x(d).                               (C1')
```

Then

```text
ker(nabla_N)=mu tensor A,                                  (C1'')
```

so the Möbius orientation is retained as the flat line while arbitrary source cochains remain
available.  A valid prime--polar carrier must augment `X_N(A)` by a source-defined polar/boundary
channel.  It cannot factor only through `nabla_N`, because `nabla_N(mu)=0`; the nonzero
prime--polar defect must be produced by an inhomogeneous curvature or relative boundary term fixed
before `E_L(N)` is evaluated.

`[CONJECTURE — COVARIANT COCHAIN SEWING]` Replace horizontal scalar sections by an augmented
cochain module on which the explicit face differences in `(C0)` and the exact floor remainders in
`(C6)` define a non-flat aperture connection.  Construct `delta_N`, `B_N`, and the polar boundary
map from those source coefficients so that `(C1a)` and `(C2)` hold on the full augmented module,
with a norm fixed independently of `tau_N`, `Gamma_(N,+/-)`, and `E_L(N)`.  Only after that
factorization exists may its positive part be tested against `(C4)`.

This replacement survives the scalar-line obstruction because the carrier is the full cochain
module and the orientation is its covariant derivative, not its membership condition.  It has not
passed Gate 2 as an exact theorem: the augmented polar edges, their coefficients, and the local
formula for `B_N` are still missing.

`[OPEN CORE]` Give those three objects explicitly and prove a source-local factorization on a
class containing non-flat atomic and coexact sections.  The next decisive test is whether the
Möbius--polar section has a uniformly controlled norm without inserting the assembled defect or a
spectral positive part.

### External parent-theory boundary

Hardy spaces of Dirichlet series provide large Bohr-lift carriers and abstract Carleson criteria,
but they do not supply this sewing.  Hedenmalm--Lindqvist--Seip identify the square-summable
Dirichlet space with an infinite-polytorus Hardy space
(<https://doi.org/10.1215/S0012-7094-97-08601-4>), and Brevig--Perfekt--Seip characterize bounded
Volterra operators there by a product Carleson measure
(<https://arxiv.org/abs/1602.04729>).  These norms are prime-phase invariant and do not by
themselves control the distinguished boundary character `p |-> -1`; the critical Möbius
half-density is also a borderline, not an ordinary global `H^2`, vector.

The Nyman--Beurling--Báez-Duarte theory already combines ordinary floor packing, integer dilations,
and Möbius cancellation, but its useful scalar closure is equivalent to RH
(<https://arxiv.org/abs/math/0202141>).  Importing that closure as `(C4)` would be circular.  Even
generic Carleson theory is not enough: product Carleson embedding requires genuinely open-set
rather than rectangular tests, and dimension-free operator-valued Carleson embedding fails in
general.  Therefore any surviving `(C4)` must exploit the explicit arithmetic sewing, not the word
"Carleson" alone.

### Gate correction

- [x] prove scalar and fixed-fibre central-sign horizontal rigidity
- [x] refute `(C1)` as a genuine scalar source module
- [x] isolate the vector-valued escape as an unspecified-fibre, not a prime-graph, mechanism
- [x] identify full cochains plus a non-flat polar boundary as the minimal representation change
- [ ] define the augmented polar edges and their floor-remainder coefficients
- [ ] construct the source-local `B_N`, `delta_N`, and `(C2)` on non-flat sections
- [ ] only then formulate the exact operator-valued/product Carleson measure behind `(C4)`

## 2026-07-18 refinement: exact cutoff classification and canonical cosheaf audit

### Every scalar cutoff mode is either the Möbius mode or a transient boundary singleton

The preceding rigidity statement has the following exact finite-aperture form.  For any induced
subgraph `G` of the squarefree divisibility graph and any real vector space `A`, multiplication by
the Möbius sign gives

```text
Hor(G;A) ~= A^(pi_0(G)),

x |-> (d |-> mu(d)x(d)).                                  (C1-class)
```

Indeed the transformed function is constant on edges, hence on components, and every
componentwise constant function transforms back to a horizontal section.

For the card's original vertex set

```text
D_N={d : 2<=d<=N, d squarefree},   N>=4,
```

there is one core component and precisely one isolated component for every prime in `(N/2,N]`.
Every composite vertex descends to a prime; every odd prime `p<=N/2` is connected to `2` by
`p--2p--2`.  Therefore

```text
dim Hor(D_N;R)=1+pi(N)-pi(N/2).                            (C1-cutoff)
```

Those additional dimensions are not persistent arithmetic grades.  In `D_(2N)`, every prime
`p<=N` is in the core, so the image of restriction

```text
Hor(D_(2N);A) -> Hor(D_N;A)
```

is exactly the single diagonal copy `mu tensor A`.  Consequently

```text
inverse_limit_N Hor(D_N;A) ~= A,   x_N(d)=mu(d)a.          (C1-limit)
```

This closes the finite-cutoff loophole without an asymptotic or a computation.

### Canonical principal-ideal projection cosheaf `[PAPER-PROVED] [BRIDGE]`

There is a canonical non-flat replacement, but it exposes rather than solves the missing RH
mechanism.  Let

```text
nu_N(n)=w_(N,L)(n)/c_N,
H_N=L^2({1,...,N},nu_N),
(P_(N,d)f)(n)=1_(d|n)f(n).
```

The `P_(N,d)` are commuting orthogonal projections and

```text
P_(N,d)P_(N,e)=P_(N,lcm(d,e)).                            (PC1)
```

For a prime face `S`, take the stalk `P_(N,q_S)H_N` and the genuine noninvertible restriction
`P_(N,q_(S union {p}))`.  Pointing at the empty face gives an exact classification of twisted
compatible sections:

```text
H_N ~= Sec_-(P_N),
f |-> x_S=(-1)^|S| P_(N,q_S)f.                            (PC2)
```

Thus the section space is source-defined and genuinely larger than the Möbius line; its freedom
comes from ordinary principal ideals, not from an unspecified auxiliary fibre.

Define the marked-cell map by

```text
(M_N f)_p=sqrt(log p) sum_(S containing p) x_S.
```

Pointwise inclusion--exclusion gives the exact selector

```text
(M_N f)_p(n)
 =-sqrt(log p) 1_(rad(n)=p)f(n),

||M_N 1||^2=T_L(N)/c_N.                                  (PC3)
```

After adjoining the explicit polar line, put

```text
Z_N=H_N direct_sum R,   xi_N=(1,1),
Gamma_(N,+)(f,a)=M_N f,
Gamma_(N,-)(f,a)=a.
```

Then for every source vector, without using the value or sign of `E_L(N)`,

```text
tau_N((f,a),(f,a))=||Gamma_(N,+)(f,a)||^2-||Gamma_(N,-)(f,a)||^2,
c_N tau_N(xi_N,xi_N)=T_L(N)-c_N=E_L(N).                  (PC4)
```

So literal non-spectral, source-cellular `(C2)` is already closed.  It is the raw factorization,
not the compensated sewing needed by `(C4)`.

### Why `(C0)` and `(C6)` do not create the missing compensation

On the free face module the canonical discrete map

```text
Phi_N^disc(e_S)_p
 =1_(p in S)sqrt(log p) P_(N,q_S)1
```

has Gram kernel exactly

```text
<Phi_N^disc e_S,Phi_N^disc e_T>
 =ell(S intersect T)W_N(S union T)=F_N(S,T).              (PC5)
```

The Bernoulli-continuum map has kernel

```text
c_N ell(S intersect T)/q_(S union T).
```

Their source-defined relative boundary form therefore has kernel

```text
ell(S intersect T)
  (W_N(S union T)-c_N/q_(S union T)).                     (PC6)
```

On the Möbius face vector it evaluates to `R_(N,L)`.  But adding the continuum-normalization
piece and the polar line makes the continuum terms cancel identically:

```text
(||Phi_disc a||^2-||Phi_cont a||^2)
  +||Phi_cont a||^2-c_N|a_empty|^2
 =||Phi_disc a||^2-c_N|a_empty|^2.                       (PC7)
```

Hence `(C0)` plus principal-ideal floor packing provides two positive Gram systems, their relative
difference, and an orthogonal polar rank-one term.  It provides no off-diagonal
arithmetic--polar morphism.  Full cochains and `nabla_N` do not add one, because
`nabla_N xi_N=0`.

The raw factorization also fails the block theorem on its distinguished section.  The fixed-`L`
weighted prime number theorem gives `T_L(N)~c_N`; consequently its positive block output obeys

```text
sum_(exp(J)<=N<exp(J+1))
  (c_N/N)||Gamma_(N,+)xi_N||^2
 =sum_(exp(J)<=N<exp(J+1)) T_L(N)/N
 asymp exp(J/2),                                          (PC8)
```

not a polynomial in `J`.  Meanwhile the normalized principal-ideal norm of `1` is uniformly
bounded.  Thus no choice of this raw positive coordinate can satisfy `(C4)` while retaining the
card's uniformly bounded distinguished section.

### Corrected exact open core

`[FALSIFIED]` `(C1)` as a scalar carrier.  `[PAPER-PROVED BUT INSUFFICIENT]` literal raw `(C2)` on
the principal-ideal projection cosheaf.  `[OPEN CORE]` construct, from source data independent of
`E_L`, its sign, and every spectral positive part, an off-diagonal polar--arithmetic sewing map
whose relative output meets before the positive/negative norm split.  Prove its exact identity on
the full cosheaf and only then ask for the polynomial cross-aperture bound `(C4)`.

Choosing that cross map from the evaluated Möbius vector, rescaling it by the desired defect, or
putting its positive output into the source norm is circular.  No such cross map is determined by
`(C0)`, `(C6)`, flat orientation, or the existing finite Hodge transgression.

### Revised gates

- [x] classify every finite scalar cutoff mode and its cofinal inverse limit
- [x] construct the canonical noninvertible principal-ideal section space
- [x] prove the literal source-cellular raw factorization `(PC4)`
- [x] prove that its continuum relative term telescopes back to raw incidence
- [x] refute raw `(PC4)` against the cross-aperture block bound
- [ ] construct a source-natural off-diagonal polar--arithmetic sewing map
- [ ] prove a compensated cellular difference-of-squares identity after that sewing
- [ ] prove the resulting cross-aperture Carleson estimate

## 2026-07-18 exact floor-remainder factorization and its block no-go

### Euler--sawtooth boundary identity `[PAPER-PROVED] [BRIDGE]`

Extend the tent weight to the positive reals by

```text
w_N(t)=t^(-1/2)h_L(log(N/t)).
```

It is absolutely continuous, supported on `[N exp(-2L),N]`, vanishes at both endpoints, and

```text
integral_0^infinity w_N(t)dt=c_N.
```

Stieltjes and ordinary integration by parts give, for every integer `q>=1`,

```text
W_N(q)=-integral_0^infinity floor(t/q)w_N'(t)dt,

c_N/q=-integral_0^infinity (t/q)w_N'(t)dt.
```

Therefore the coefficient demanded after `(C0)` is exactly

```text
W_N(q)-c_N/q
 =integral_0^infinity frac(t/q)w_N'(t)dt.                (SF1)
```

There is no endpoint term.  This supplies the explicit floor-remainder coefficient that the
previous conjectural gate left undefined.

### Canonical non-spectral cellular factorization `[PAPER-PROVED] [BRIDGE]`

For a prime face `S`, define at each `t>0` the discrete and continuum marked-cell maps

```text
D_t(e_S)(p,n)
 =sqrt(log p)1_(p in S)1_(q_S|n)1_(n<=t),

C_t(e_S)(p,omega)
 =sqrt(t log p)1_(p in S)chi_S(omega),
```

where the Bernoulli prime coordinates satisfy `Prob(omega_p=1)=1/p`.  Their Gram kernels are

```text
<D_t e_S,D_t e_T>
 =ell(S intersect T)floor(t/q_(S union T)),

<C_t e_S,C_t e_T>
 =ell(S intersect T)t/q_(S union T).                     (SF2)
```

Write `w_N'=u_N-v_N` with `u_N=(w_N')_+` and `v_N=(w_N')_-`.  The direct-integral maps

```text
Gamma_(N,+)^rel a
 =(sqrt(u_N(t))C_t a, sqrt(v_N(t))D_t a)_t,

Gamma_(N,-)^rel a
 =(sqrt(u_N(t))D_t a, sqrt(v_N(t))C_t a)_t               (SF3)
```

then satisfy on the entire free face module

```text
||Gamma_(N,+)^rel a||^2-||Gamma_(N,-)^rel a||^2
 =sum_(S,T)a_S a_T ell(S intersect T)
    (W_N(S union T)-c_N/q_(S union T)).                  (SF4)
```

Thus the relative discrete--continuum Gram defect does have an exact cellwise
difference-of-squares factorization fixed solely by the source tent and ordinary floor packing.
No spectral positive part is used.

### The factorization fails both the polar and block gates

Let

```text
b_L(x)=h_L'(x)+(1/2)h_L(x),
A_(L,+)=integral_0^(2L) exp(-x/2)(-b_L(x))_+ dx.
```

The falling side of the tent gives `A_(L,+)>0`, and direct substitution gives

```text
integral_0^infinity t u_N(t)dt=A_(L,+)sqrt(N).           (SF5)
```

For every fixed prime `p`, the continuum coordinate in `(SF3)` therefore forces

```text
||Gamma_(N,+)^rel e_{ {p} }||^2
 >=A_(L,+)sqrt(N)log(p)/p.                              (SF6)
```

After the `c_N^(-1)` normalization required by `(C2)`, this remains bounded below by a positive
constant depending only on `L,p`.  Stacking the coherent face `e_{ {p} }` with the weights in
`(C3)` gives

```text
||C_(J,+)e_{ {p} }||^2
 >=const_(L,p) sum_(exp(J)<=N<exp(J+1))N^(-1/2)
 asymp const_(L,p)exp(J/2).                              (SF7)
```

This is exponential rather than polynomial in `J`.  The failure is independent of the prime
number theorem and occurs on a single persistent prime face.

There is also an exact polar obstruction:

```text
C_t e_empty=D_t e_empty=0.                               (SF8)
```

The relative kernel has zero empty-face row and column.  Appending `-c_N|a_empty|^2` can only add
an orthogonal negative line; it cannot create an arithmetic--polar cross term.  Hence `(SF4)` is
the strongest factorization canonically selected by the sawtooth coefficients, and it still
cannot be the compensated `(C2)` required before `(C4)`.

## 2026-07-18 diagonal exhaustion and the minimal off-diagonal enlargement

### Principal-ideal projections contain exactly the diagonal, no hidden sewing

On unweighted `l2({1,...,N})`, let `P_d e_m=1_(d|m)e_m`, `v_d=P_d 1`, and
`Z_N(d,m)=1_(d|m)`.  Then

```text
K_N(d,e)=<v_d,v_e>=floor(N/lcm(d,e)),
K_N=Z_N Z_N^T,
det(K_N)=1.                                              (DA1)
```

The last equality holds because `Z_N` is triangular with unit diagonal.  Möbius inversion gives
every coordinate projection:

```text
E_n=sum_(k<=N/n)mu(k)P_(nk).                             (DA2)
```

Thus the principal-ideal projections span the full maximal diagonal algebra.  They cannot produce
an off-diagonal polar--arithmetic morphism.

Equation `(DA2)` does give another honest source-incidence difference of squares,

```text
|x_n|^2
 =sum_(mu(k)=+1)||P_(nk)x||^2
  -sum_(mu(k)=-1)||P_(nk)x||^2.                         (DA3)
```

But its two canonical synthesis maps have squared norm `2^(R(N/n)-1)`, where
`R(X)=max_(r<=X)omega(r)`.  Primorials give

```text
2^R(X)=exp((log(2)+o(1))log(X)/log(log(X))),             (DA4)
```

which dominates every fixed power of `log X`.  Atomizing the diagonal by its natural Möbius
resolution therefore reproduces the all-grade norm explosion.

There is a useful but insufficient positive theorem.  For `u_(N,d)=N^(-1/2)v_d`, a weighted Schur
test gives

```text
||Gram(u_(N,d))||=||K_N/N|| <=2 zeta(3/2).               (DA5)
```

So ordinary floor packing has a dimension-free single-aperture Bessel bound.  Across apertures,
however,

```text
<u_(N,d),u_(M,e)>
 =floor(min(N,M)/lcm(d,e))/sqrt(NM),                    (DA6)
```

and a fixed ideal `d` remains coherently correlated throughout a logarithmic block.  Its stacked
mass is again `asymp_d exp(J/2)`.  The missing theorem is therefore not a better fixed-`N` frame
bound; it must differentiate or remove the persistent radial ideal channel.

The incidence-algebra parent of `(DA1)`--`(DA3)` is Rota
(<https://doi.org/10.1007/BF00531932>).  GCD-matrix Carleson--Hunt estimates such as
Aistleitner--Berkes--Seip (<https://doi.org/10.4171/JEMS/537>) concern a different maximal-partial-
sum problem and do not imply the cofinal aperture estimate here.

### Multiplication shifts are necessary, but an unrestricted shift algebra is theatre

On `l2(N)` the source-natural off-diagonal operators are

```text
U_q e_n=e_(qn),
U_q^*U_q=1,
U_qU_q^*=P_q,
U_q P_d U_q^*=P_(qd),
[log(n),U_q]=log(q)U_q.                                  (DA7)
```

Their finite compressions have

```text
(U_q^(N))^*U_q^(N)=projection onto {1,...,floor(N/q)},   (DA8)
```

so the additive cutoff defect and the floor law meet in one exact object.  These are the standard
Nica/right-LCM covariance relations; see Nica
(<https://jot.theta.ro/jot/archive/1992-027-001/1992-027-001-002.pdf>) and Laca--Raeburn
(<https://arxiv.org/abs/0907.3760>).  Those universal operator-algebra theorems supply no
quantitative polar sewing or cross-aperture bound.

Moreover, `(DA2)` supplies `E_1`, and

```text
U_m E_1 U_n^*=E_(m,n).                                   (DA9)
```

Thus unrestricted principal projections plus multiplication shifts generate every matrix unit.
Allowing an arbitrary element of this algebra as `B_N` would merely permit any desired finite
factorization to be encoded after the fact.

The internal corpus already records both infinite-limit versions of this danger:

- `5-failed/prime-coshift-koszul-derived-limit-conjecture.md` proves that an unspecified derived
  limit of prime-shift Koszul fibres supplies no canonical completion defect;
- `5-failed/prime-coshift-additive-trace-coercivity-conjecture.md` proves that the natural scalar
  Abel/heat boundary trace is not closable in the all-prime row graph norm;
- `3-formalized/not_new_scientific_knowledge/additive-heat-diagonal-generates-full-operator-algebra.md`
  proves that adjoining an everywhere-nonzero additive heat aperture to the particle diagonal
  generates all bounded operators.

Therefore the finite shift enlargement survives only under a stricter admissibility gate.  It must
be a specified first-order, vector-valued correspondence built from the compressed prime shifts,
the tent coefficients, marked-face incidence, and the polar empty face.  It may not be an arbitrary
matrix, a scalar trace on the old row graph, or an unnamed derived limit.  Its graph norm must
detect the prime-supported averaging sequence that killed the scalar trace, while keeping the
distinguished section uniformly bounded.

`[EXACT OPEN CORE — SHARPENED]` Define that one constrained correspondence `delta_N` explicitly
and prove both:

```text
source-local transgression(delta_N)=E_L(N)/c_N
```

on a source class containing non-diagonal cochains, and

```text
delta_N kills/differentiates every coherent fixed-ideal channel
```

before positive/negative norm separation.  Only this statement survives `(SF7)`, `(DA4)`, `(DA6)`,
the full-matrix-algebra no-go, and the retired scalar-trace route.  It remains unproved and is the
first RH-strength theorem in this representation.

## 2026-07-18 weighted-shift covariance: exact survivor and exact mismatch

The tent family itself supplies a stronger cross-aperture law than the unweighted relations in
`(DA7)`.  For real aperture `X>0`,

```text
w_(X,L)(qn)=q^(-1/2)w_(X/q,L)(n).                        (WS1)
```

Hence, between the corresponding tent-weighted integer spaces,

```text
U_(q,X)=q^(1/4)V_q : H_(X/q) -> H_X
```

is an isometry onto the principal-ideal range `P_q H_X`.  With

```text
D_X=M_(log n),
A_X=M_(log(X/n)),
```

one has the exact covariances

```text
D_X U_(q,X)-U_(q,X)D_(X/q)=log(q)U_(q,X),
A_X U_(q,X)=U_(q,X)A_(X/q).                              (WS2)
```

Thus the logarithmic observable acquires precisely the prime-edge increment, while the centered
radial clock transports without error.  This is the concrete, non-spectral source representation
that an admissible `delta_N` must refine.

It still does not construct the polar seam.  If

```text
R_p=-sum_(d<=N, p|d)mu(d)P_d,
```

then `R_p` is exactly the projection onto the `p`-power coordinates.  Since

```text
[D,V_p]V_p^*=log(p)P_p,
```

the source trace identity is

```text
T_L(N)
 =sum_p Tr(M_(w_N) R_p [D,V_p]V_p^*).                   (WS3)
```

Equation `(WS3)` recovers the arithmetic term and nothing more.  The continuum mass `c_N` and an
off-diagonal discrete-to-polar correspondence remain absent.

Nor does the most obvious radial commutator repair this.  For `g_X=sqrt(w_(X,L))`,

```text
[M_(g_X),V_q]
 =V_q(q^(-1/4)M_(g_(X/q))-M_(g_X)),                     (WS4)
```

whose square is the all-integer radial edge Dirichlet energy

```text
sum_(qn<=X)|g_X(qn)-g_X(n)|^2.
```

It neither selects prime powers nor contains `c_N`, so it cannot equal `E_L(N)`.

Finally, the retired co-shift audit supplies a mandatory cofinal-norm test.  The prime-supported
averages

```text
x_M=(1/M)sum_(j=1)^M e_(q_j)
```

tend to zero in the natural all-prime row graph norm while their scalar additive boundary stays
`1`.  Any proposed scalar prime-to-polar map on that graph is nonclosable.  A surviving
`delta_N` must therefore use a stronger, independently source-defined vector boundary norm and
must show explicitly why it detects this sequence without inserting the desired block estimate.

`[POSITIVE SURVIVOR]` `(WS1)`--`(WS3)` give the exact cross-aperture multiplication/log carrier.
`[NO-GO]` its natural weight commutator gives only radial Dirichlet energy, and its log commutator
gives only `T_L`.  `[OPEN CORE]` construct the separately source-defined continuum-polar
correspondence that turns this carrier into a compensated vector boundary before norming.

## 2026-07-18 corpus correction: the polar correspondence exists; its cofinal passivity does not

The final sentence of the weighted-shift audit must be read narrowly.  A source-defined
prime--continuum polar correspondence already exists in the live formal corpus.  Put

```text
dR(h)=2cosh(h/2)dh
 -sum_(n>=2)Lambda(n)n^(-1/2)delta_(log n)(h).            (ST1)
```

`CCMPolarPrimeStieltjesAutocorrelation.lean` defines the finite-aperture pairing

```text
B_a(F)=integral_(0,2a] F(h)dR(h)                          (ST2)
```

and proves its exponential-test symbol, constant-test completed error, smooth integration-by-parts
law, and aperture-autocorrelation quadratic form.  In particular, for a zero-extended aperture
vector `v`,

```text
Q_(polar-prime,a)(v,v)=2 Re B_a(C_v),                    (ST3)
```

where `C_v` is its positive-lag autocorrelation.  The module
`CCMRectangularStieltjesAutocorrelation.lean` further proves that the adjacent-block test of this
same carrier is exactly the moving prime tent plus the explicit two-edge polar values.  Thus the
prime and polar channels already meet before scalar evaluation.

The completed-error module identifies the cumulative of `(ST1)` with the fixed causal Volterra
filter of the normalized Chebyshev error.  The exact all-epsilon one-sided estimate for that filter
is already an RH-equivalent formal theorem.  Replacing `(ST1)` by this scalar potential therefore
does not prove the missing estimate.

The canonical Krein/Jordan realization also fails the new block gate.  Writing

```text
dR=sigma_R d|R|
```

gives the source feature used in
`ccm-diagonal-fock-polar-prime-mellin-incidence-law.md`, but on an aperture of size
`X=exp(2a)` its positive continuous mass and negative prime mass are separately of order
`sqrt(X)`.  Normalization leaves a fixed positive channel at every aperture, and stacking it with
`(C3)` again costs `exp(J/2)`.  This is the Stieltjes version of `(SF7)` and `(PC8)`.

That same card gives the exact four-channel colligation

```text
Cauchy = prime - shifted-polar + critical-Mellin-defect
```

and rewrites RH as its cofinal passivity.  The identity is proved; the passivity is RH-equivalent
and open.

`[CORRECTION]` Do not invent another raw discrete-to-polar correspondence: `(ST1)`--`(ST3)` are the
canonical source correspondence and are already formalized.  `[EXACT OPEN CORE]` pull the
weighted multiplication/Boolean transgression into this existing vector Stieltjes carrier and
construct a non-Jordan, source-selected cofinal factorization whose positive channel removes the
fixed continuum and fixed-ideal modes before norming.  Equivalently, prove the existing
four-channel passivity by a new source estimate.  Merely taking Jordan parts, the normalized
Chebyshev scalar, or the spectral positive part is respectively exponentially large,
RH-equivalent, or circular.

## 2026-07-18 bounded-intertwiner and fixed-grade no-go

### Atomic and continuum radial clocks are spectrally disjoint `[PAPER-PROVED] [BRIDGE]`

Let

```text
H_X^disc=L^2(sum_n w_(X,L)(n)delta_n;C^s),
H_X^cont=L^2(w_(X,L)(t)dt;C^r),

A_X^disc=M_(log(X/n)),
A_X^cont=M_(log(X/t)),
```

with finite multiplicities `r,s`.  Every bounded correspondence `J_X:H_X^cont->H_X^disc`
satisfying either

```text
A_X^disc J_X=J_X A_X^cont,                                (BI1)
```

or the shifted log covariance

```text
D_X^disc J_X-J_X D_X^cont=log(q)J_X                       (BI2)
```

is zero.  Indeed the Riesz kernel of the `n`th discrete coordinate must be supported respectively
on the singleton `t=n` or `t=n/q`; both are null for the continuum measure.  The reverse-direction
bounded correspondence is zero for the same reason.

Consequently no bounded finite-multiplicity first-order expression assembled from `(WS2)`,
continuum dilations, clock multipliers, and finite prime-face matrices can have a nonzero
empty-face-to-prime block while retaining exact radial-clock covariance.  The formal Stieltjes
carrier `(ST1)` evades this theorem precisely because it is a distributional form, not a bounded
intertwiner between the two ambient `L^2` spaces.

### One-prime shifts have exact composite contamination

The canonical one-edge vector is

```text
b_p=sqrt(log p)P_p 1.
```

With the normalized tent measure its full prime row obeys

```text
||b||^2
 =c_N^(-1)sum_n w_N(n)log(rad(n)),

||b||^2-T_L(N)/c_N
 =c_N^(-1)sum_(omega(n)>=2)w_N(n)log(rad(n)) >=0.         (BI3)
```

Thus the first-order prime row carries every composite squarefree support, not the von Mangoldt
selector.  Exact prime-power selection requires

```text
R_p=P_p product_(q!=p)(1-P_q)
   =-sum_(d:p|d)mu(d)P_d.                                (BI4)
```

Because the principal projections are linearly independent, `(BI4)` uses every Boolean degree.
No fixed first-order or fixed-grade expression can produce it.  Full Koszul/Hodge cancellation
can and does produce `R_p`, but that is exactly the already-known global output `(PC3)/(WS3)`;
tent commutators and adjoints do not change the support obstruction.

The tempting rank-one map from the normalized continuum polar vector to the already assembled
prime-power vector has norm square `T_L(N)/c_N`.  It violates `(BI1)`--`(BI2)`, acts only on the
evaluated polar line, and is the raw positive channel already refuted by `(PC8)`.  Realizing it by
point evaluation on continuum `L^2` would be unbounded and nonclosable.

### Corpus boundary and corrected representation gate

These conclusions agree with the existing formal/paper no-gos:

- ambient `L^2` has no representative-independent point evaluator;
- order-zero prime-power sampling is maximally blind to the absolutely continuous archimedean
  measure in total variation;
- the natural all-prime row graph does not make the scalar additive boundary closable;
- importing the point-evaluable Weil/de Branges realization is presently RH-conditional.

A surviving non-Jordan factorization must therefore live on a separately source-selected trace,
Sobolev, or RKHS domain where lattice evaluation is bounded and the Stieltjes form is closable.
Choosing an arbitrary stronger norm is not admissible.  The precise new burden is a canonical
stable-synthesis/closed-range theorem for that domain which also detects the prime-average sequence
and removes the fixed-ideal block modes.  This is stronger and more exact than merely asking for a
bounded discrete--continuum map.

`[NO-GO]` bounded clock-covariant first-order sewing and every fixed interaction grade.
`[SURVIVOR]` the already-formalized distributional Stieltjes carrier on an as-yet-unconstructed
source-selected point-evaluable domain.  `[OPEN CORE]` construct that domain and prove its cofinal
stable-synthesis/passivity estimate without using RH or the evaluated defect.

## 2026-07-18 final domain correction: local evaluation exists, cofinal bornology is missing

The last open-core sentence above also needs its precise corpus boundary.  At each fixed aperture,
Suzuki's source form already uses `H_0^1(-a,a)`, and the autocorrelation `C_v` of an aperture vector
is continuous.  Prime-log evaluation in `(ST3)` is therefore well-defined and bounded on the
relevant quadratic autocorrelation class.  The bounded-intertwiner no-go concerns a linear map
between the two ambient atomic/nonatomic `L^2` clock representations; it does not invalidate this
existing distributional/autocorrelation realization.

What is not constructed is a cofinal source bornology across `a -> infinity` on which the
Stieltjes/Gamma boundary relation has a uniform stable-synthesis or passivity estimate.  The proved
`ccm-universal-boundary-laplace-frame-saturation-law.md` makes this sharp: every fixed nonzero
smooth boundary profile gives a translated two-edge family whose positive analysis energy
asymptotically saturates the exact polar--Euler frame level.  Thus leading prime mass, the polar
channel, and finitely many selected profiles have no margin.  The sign lives entirely in the
subleading critical-Mellin/Gamma remainder on an infinite-dimensional profile space.

`[FINAL LIVE OPEN CORE]` Construct the cofinal boundary-profile space and its source-selected norm,
then prove a non-Jordan stable-synthesis/passivity estimate for the existing autocorrelation
Stieltjes carrier, uniformly on that whole profile space.  The norm must keep fixed translated
profiles bounded, detect the prime-average nonclosability sequence, and make the positive block
operator polynomial in the logarithmic aperture.  This one theorem is RH strength.  No audited
corpus or primary source proves it; no new finite-aperture carrier is required.

## 2026-07-18 co-Poisson / affine-residue filter audit

### The two external ingredients are exact bridges, not a passivity theorem

Brownlowe--an Huef--Laca--Raeburn's affine-semigroup boundary quotient gives, for every
`q>=2`, the canonical residue isometries

```text
S_(q,r)e_m=e_(qm+r),       0<=r<q,
S_(q,r)^*S_(q,s)=delta_(r,s)I,
sum_(r=0)^(q-1)S_(q,r)S_(q,r)^*=I.                      (ER1)
```

The corresponding Exel product system composes these bases coherently across multiplicative
scales.  A finite Fourier rotation of the residue index gives the usual Cuntz/QMF low-pass and
zero-sum channels.  This is an exact norm-one arithmetic skeleton
([Brownlowe--an Huef--Laca--Raeburn](https://arxiv.org/abs/1009.3678),
[Bratteli--Jorgensen](https://arxiv.org/abs/funct-an/9612003)).

Burnol's co-Poisson intertwining theorem is also exact.  For a compactly supported multiplicative
filter `g` and a tempered distribution `D`,

```text
Fourier(g*D)=I(g)*Fourier(D),
Mellin(g*D)(s)=Mellin(g)(s) Mellin(D)(s).                (ER2)
```

See [Burnol, Theorem 4.9 and Proposition 4.21](https://doi.org/10.5802/aif.2268).
These results justify testing a compact filter with Mellin zeros at the two polar characters
`+/-1/2`, followed by the affine residue filter bank.  They do not give a Carleson estimate,
a source Stein inequality, or a reconstruction of the moving tent.

The corpus audit is decisive.  Two-boundary annihilation is already present in
`prime-gamma-reflection-decimation-defect-resolvent-rh.md`: it has the cutoff-compatible affine
remainder and the unique order-`k` Hermite boundary filter

```text
B_(k,a)(w,lambda)
 =((w^2-a^2)/(lambda^2-a^2))^k/(w+lambda).              (ER3)
```

Its positive cofinal packets and arbitrary-depth square summability are already formalized.  The
unresolved operation is undoing this boundary divisor while transporting the packet to the
positive-log completed Mellin jets.  That inverse is unbounded.  Thus polar annihilation itself is
`[REDISCOVERED]`, not a new source estimate.

### QMF is an energy-neutral residue refinement `[PAPER-PROVED] [BRIDGE]`

Let `zeta_q=exp(2 pi i/q)` and

```text
H_(q,k)=q^(-1/2)sum_(r=0)^(q-1)zeta_q^(kr)S_(q,r)^*.
```

Unitary Fourier rotation and `(ER1)` give

```text
sum_(k=0)^(q-1)||H_(q,k)x||^2=||x||^2,

sum_(k=1)^(q-1)||H_(q,k)x||^2
 =||x||^2-q^(-1)||sum_r S_(q,r)^*x||^2.                 (ER4)
```

Hence the centered channels only rotate the off-average residue energy.  They cannot decrease the
full positive block without an additional arithmetic identity.

There is a sharp fixed-ideal obstruction.  If `x` lies in the zero-residue range
`Ran(S_(q,0))`, then all its nonzero residue subsequences vanish and `(ER4)` becomes

```text
sum_(k=1)^(q-1)||H_(q,k)x||^2=((q-1)/q)||x||^2.         (ER5)
```

For the normalized tent principal-ideal vector

```text
x_N(n)=sqrt(w_N(n)/c_N) 1_(q|n),
```

fixed-`q` floor packing gives `||x_N||^2=W_N(q)/c_N -> 1/q`.  Therefore the centered output is
bounded below at every large aperture.  With the block weight required in `(C3)`,

```text
sum_(exp(J)<=N<exp(J+1)) c_N/N
  sum_(k=1)^(q-1)||H_(q,k)x_N||^2
  asymp_(L,q) exp(J/2).                                  (ER6)
```

This uses no prime number theorem.  The QMF refinement retains precisely the persistent
principal-ideal mass which the cofinal norm must remove before taking positive parts.

The multiplicative clock gives a second obstruction.  On positive indices,

```text
[D,S_(q,0)]=log(q)S_(q,0),
[D,S_(q,r)]e_m=log((qm+r)/m)e_(qm+r),  r!=0.             (ER7)
```

Only the zero residue has a constant logarithmic increment.  Nonzero residue Fourier channels
replace multiplicative covariance by additive-residue fluctuations.  For a prime `p`,

```text
[D,S_(p,0)]S_(p,0)^*=log(p)P_p,

sum_p log(p)P_p
 =M_(log rad(n))
 =M_Lambda+M_(log rad(n) 1_(omega(n)>=2)).               (ER8)
```

Thus the exact composite contamination `(BI3)` survives.  Iterating the zero residue detects the
valuation `nu_p(n)` but leaves arbitrary coprime cofactors.  Pure prime powers still require

```text
R_p=P_p product_(ell!=p)(I-P_ell),                       (ER9)
```

the existing all-grade selector.  Applying a centered residue channel after inserting `M_Lambda`
merely mixes the already-evaluated prime-power outputs.  It does not construct them.

For BV square-index decimation, `(ER1)` only refines the already-proved off-multiple identity into
its residue summands.  Fourier rotation of those summands supplies neither the missing scale-zero
renormalization nor continuity of the Laurent boundary functionals.

### A polar-annihilating filter cannot by itself reconstruct the moving tent

This obstruction can be stated without operator-algebra language.  On logarithmic coordinates let

```text
(T_g F)(h)=integral g(u)F(h-u)du,
G(z)=integral g(u)exp(-zu)du.
```

If `G(+1/2)=G(-1/2)=0`, then `T_g` kills both polar exponentials.  The adjoint convolution has the
same reflected pair of zeros.  Consequently every compact test in `Ran(T_g^*)` has zero bilateral
Laplace moments at `+/-1/2`.

The translated moving tent `F_(x,L)` is nonnegative, nonzero, and compactly supported.  Hence

```text
integral F_(x,L)(h)exp(-h/2)dh>0,
integral F_(x,L)(h)exp(+h/2)dh>0.                        (ER10)
```

It is not in `Ran(T_g^*)`.  Since

```text
<T_g dR,psi>=<dR,T_g^*psi>,                              (ER11)
```

no source-independent bounded synthesis from the filtered current alone recovers the tent pairing
`<dR,F_(x,L)>`.  One must retain two pointed polar boundary coordinates, use an unbounded
generalized inverse, or prove a new `dR`-specific null relation.  The second option is exactly the
unbounded boundary-divisor reversal already exposed after `(22j1)` in the prime--Gamma card; the
third would itself be a new RH-strength source theorem.

`[NO-GO]` The direct programme "annihilate the polar modes, apply centered Exel/Cuntz channels,
and norm the output" fails both reconstruction `(ER10)` and the block gate `(ER6)`.

### Exact surviving conjunction `[CONJECTURE] [NOVELTY UNVERIFIED]`

The only conjunction not already present in the corpus is a **pointed distributional
Exel--Burnol colligation**.  It would have to retain the two low-pass Gamma/polar boundary jets,
apply residue mixing only inside a source-selected cofinal graph/profile space, preserve the
linear signed prime--polar cross term, and identify its Schur complement with the existing
Stieltjes autocorrelation form before proving a polynomial-in-aperture block estimate.

A pure Cuntz isometry or QMF rotation cannot be this operator because of `(ER6)`--`(ER9)`.  In the
existing Burnol quotient coordinates, the strongest exact target is already the Douglas
factorization

```text
A_+=E_b U_r iota_a,
A_-=E_b U_r^* iota_a,
A_+=A_- C_r,                 ||C_r||<=1,                 (ER12)
```

with `C_r` constructed from the source filters before any zero evaluator is read.  Reflection then
forces flatness and RH.  No audited Exel/co-Poisson theorem constructs `C_r`; asserting `(ER12)` is
the existing RH-strength open core, not evidence for it.

`[RETIRED]` filtered high-pass/QMF as a standalone producer.
`[SURVIVOR]` pointed distributional boundary colligation as one concrete possible provider for the
already-named cofinal Stieltjes passivity theorem.
`[FINAL OPEN CORE UNCHANGED]` construct the cofinal source bornology and prove its non-Jordan
stable-synthesis/passivity estimate.  The Exel basis is admissible bookkeeping only if a new
source identity removes `(ER6)` before norming and retains the two boundary ports needed by
`(ER10)`.

## 2026-07-18 Selberg half-density audit: causal positivity is not boundary passivity

This expands the short rejection at `(12)` into the exact current-level obstruction.  It does not
reopen that retired route.

Let `X` denote multiplication by the positive logarithmic coordinate and set

```text
P=sum_(n>=2) Lambda(n)n^(-1/2)delta_(log n),
eta=sum_(n>=2) lambda_2(n)n^(-1/2)delta_(log n),
lambda_2=Lambda log+Lambda*Lambda=mu*log^2.
```

The derivation identity for Dirichlet convolution gives

```text
X P+P*P=eta,                 eta>=0.                     (ER13)
```

This is the measure form of Selberg's symmetry identity.  Its Laplace transform, initially in the
absolute-convergence half-plane, is

```text
P_hat(z)=-zeta'/zeta(z+1/2),
eta_hat(z)=P_hat(z)^2-P_hat'(z)=zeta''/zeta(z+1/2).      (ER14)
```

See [Selberg, formulas (2.8)--(2.10)](https://www.math.lsu.edu/~mahlburg/teaching/handouts/2014-7230/Selberg-ElemPNT1949.pdf).
The higher Diamond--Steinig currents replace the two summands by positive logarithm-weighted
versions of the same causal convolution
([Diamond--Steinig, Sections 3.1--3.2](https://eudml.org/doc/142054)).
They do not change the geometry below.

For the already-formalized completed polar current, put

```text
Q=2cosh(h/2)dh,             R=Q-P=dR.
```

Substitution into `(ER13)` acts before Jordan decomposition and is exact:

```text
eta=XQ+Q*Q-XR-2Q*R+R*R.                                  (ER15)
```

For the dominant polar half `A=e^(h/2)1_(h>=0)dh`, one has `A*A=XA`.  With
`R_+=A-P`, `(ER15)` has the sharper factorized form

```text
2XA-eta=XR_+ +(A+P)*R_+.                                 (ER16)
```

Thus Selberg symmetry is an exact Riccati/source transduction of the same error current.  Solving
it for the required cofinal estimates recovers the original logarithmic derivative; it supplies
no independent contractive estimate.

### Decisive orientation obstruction `[PAPER-PROVED] [NO-GO]`

The positivity in `(ER13)` is coefficient positivity on product indices:

```text
log(a)+log(b)=log(ab),       Fourier(P*P)=P_hat^2.         (ER17)
```

Boundary passivity needs the reflected Hermitian convolution

```text
P^vee*P
 =sum_(m,n) Lambda(m)Lambda(n)/sqrt(mn)
    delta_(log m-log n),       Fourier(P^vee*P)=|P_hat|^2. (ER18)
```

The distinction is visible on a single finite aperture.  Choose a real smooth bump `phi` of
sufficiently small support, normalize `||phi||_2=1`, and let

```text
v=phi-tau_(log 4)phi,
C_v(t)=integral v(u+t)v(u)du.
```

The support can be chosen so that among the positive atoms `log n` of `eta`, only `log 4` meets the
nonzero negative-lag packet of `C_v`.  Then

```text
C_v(log 4)=-1,
<eta,C_v>=-lambda_2(4)/2<0,
lambda_2(4)=3(log 2)^2.                                  (ER19)
```

The factor `1/2` is the half-density weight `4^(-1/2)`.  Pairing the even extension can add the
reflected negative contribution; the sign does not change.  Hence a positive Selberg measure is not positive
on the aperture-autocorrelation cone.  Positive smooth reweighting and the Diamond--Steinig
hierarchy retain the same counterexample whenever the `log 4` coefficient survives.

Equivalently, a causal tent `h_L=q_L*q_L` gives the literal nonnegative factor-pair square

```text
<eta,h_L(x-.)>
 =<XP,h_L(x-.)>+((P*q_L)*(P*q_L))(x),

<XP,h_L(x-.)><=<eta,h_L(x-.)>.                           (ER20)
```

But the subtracted term is a complementary-scale Hankel/reflection pairing, not a same-aperture
norm square.  In Fourier variables it is `P_hat^2`, not `|P_hat|^2`.  Written with the reflection
`J_x f(u)=f(x-u)`, it is a difference of the squared norms of the `+1` and `-1` reflection
components.  Taking its absolute value or dropping one component is precisely the destructive
Jordan step.

The localized notation from `(2)` makes the scale failure equally explicit:

```text
T_L=M_L-H_L,               H_L>=0,
M_L=T_L+H_L.                                             (ER21)
```

Unconditionally, the existing source asymptotics give `H_L` and `T_L` at the same leading
square-root scale `c_N`, hence `M_L` at twice that scale.  Dropping `H_L` leaves a block contribution
of order

```text
sum_(exp(J)<=N<exp(J+1)) c_N/N asymp_L exp(J/2),          (ER22)
```

rather than a polynomial in `J`.  Keeping `M_L-H_L` is just the original compensated quantity.
Selberg's classical `O(x)` remainder likewise remains at full half-density polar scale after a
fixed logarithmic localization; it is not an RH-strength square-root cancellation estimate.

### Corpus discrimination and survivor

A completely monotone Laplace weight does turn `eta` into a positive right-half-plane Hankel
kernel.  For example,

```text
K_2(x,y)=sum_(n>=2) lambda_2(n)n^(-1-x-y)
```

is a Gram of the features
`sqrt(lambda_2(n)/n)n^(-x)`.  That is a product-index/diagonal-Fock norm.  The corpus already has
the stronger prime and polar Laplace Grams in
`ccm-diagonal-fock-polar-prime-mellin-incidence-law.md`; their signed incidence channel is exactly
the unproved one.  The actual difference-lag quadratic is already formalized in
`CCMPolarPrimeStieltjesAutocorrelation.lean`.

`[RETIRED]` Selberg, higher `mu*log^k` currents, or their positive mixtures as standalone
pre-Jordan producers.  Their positivity is causal/product-index positivity, not Hilbert boundary
positivity.

`[SURVIVOR]` `(ER15)`--`(ER16)` are exact diagnostic Riccati identities.  Any useful reflected
completion must introduce `P^vee*P`, hence the prime-ratio covariance already isolated in
`absolute-euler-paired-gauss-resolvent-autocorrelation-law.md`.  It also restores the large fixed
diagonal channel.  Therefore the reflected completion is not a new theorem target.

`[FINAL OPEN CORE UNCHANGED]` construct the source-selected cofinal boundary-profile bornology and
prove its non-Jordan stable-synthesis/passivity estimate for the existing difference-lag Stieltjes
carrier.  The causal Selberg current neither proves nor weakens that RH-strength statement.

## 2026-07-18 Hardy--Bohr/Helson audit: the two lifts and the missing pointed port

### An exact finite-aperture half-Sobolev frame `[PAPER-PROVED] [BRIDGE]`

There is a more precise positive result than generic Hardy-space language suggests.  Olsen studies

```text
H_w={sum_n a_n n^(-s):sum_n |a_n|^2/w_n<infinity}.
```

If `sum_(n<=x)w_n~C x(log x)^(-alpha)`, his Theorem 4 and Lemmas 3--4 identify the
two-sided Fourier sampling measure on every finite interval.  Take
`w_n=Lambda(n)^2`.  The unconditional PNT consequence

```text
sum_(n<=x)Lambda(n)^2~x log x
```

has `alpha=-1`, so for every bounded interval `I` there are `0<A_I<=B_I<infinity`
such that

```text
A_I ||f||_(W_0^(1/2)(I))^2
 <=sum_(n>=2) Lambda(n)^2/n
      (|fhat(log n)|^2+|fhat(-log n)|^2)
 <=B_I ||f||_(W_0^(1/2)(I))^2.                           (HB1)
```

See [Olsen, Theorem 4 and Section 7](https://arxiv.org/abs/1011.3370) and the
[JFA version](https://doi.org/10.1016/j.jfa.2011.07.007).  Thus the source amplitude

```text
a_n=Lambda(n)/sqrt(n)                                    (HB2)
```

has a canonical local `W_0^(1/2)` analysis/synthesis theory.  This is a genuine finite-aperture
host and should be retained.

The constants are not uniform under interval exhaustion.  If `I_L` has length comparable to `L`,
`phi` is a fixed compactly supported smooth function, and

```text
f_L(t)=exp(i t log 2) phi(t/L),
```

then the `log 2` atom in `(HB1)` gives

```text
|fhat_L(log 2)|^2 asymp L^2,
||f_L||_(W^(1/2))^2 asymp L,
B_(I_L)>=c_phi L.                                        (HB3)
```

This linear loss alone is not a fatal objection: the desired gate permits a polynomial in
logarithmic aperture.  The decisive issue is instead that `(HB1)` is the square of the source
amplitude, not a factorization of the linear Stieltjes current.

### The two Bohr lifts are inequivalent `[PAPER-PROVED] [NO-GO]`

Put

```text
q_n=Lambda(n)/sqrt(n),       U_t e_n=n^(-it)e_n.
```

There are two canonical finite-cutoff vectors:

```text
a_X=(q_n 1_(n<=X))_n,
b_X=(sqrt(q_n) 1_(n<=X))_n.                               (HB4)
```

The linear-amplitude lift has the attractive polynomial norm

```text
||a_X||_2^2=sum_(n<=X)Lambda(n)^2/n
             ~(1/2)(log X)^2.                            (HB5)
```

But its norm square and orbit square produce the reflected quadratic current

```text
|sum_(n<=X)q_n n^(-it)|^2
 =sum_(m,n<=X)q_m q_n exp(-it log(m/n)),                  (HB6)
```

namely `P_X^vee*P_X`.  It has replaced the linear prime measure by a prime-ratio
two-particle source.

The square-root/GNS lift represents the required linear current exactly:

```text
<U_t b_X,b_X>
 =sum_(n<=X)Lambda(n)n^(-1/2-it).                         (HB7)
```

Its zero-lag mass is unavoidably

```text
||b_X||_2^2=sum_(n<=X)Lambda(n)/sqrt(n)~2sqrt(X).          (HB8)
```

This is the polar scale, not a polynomial in `log X`.  More generally, every Hilbert
factorization `x_n conj(y_n)=q_n` obeys

```text
sum_(n<=X)q_n<=||x||_2||y||_2,
max(||x||_2^2,||y||_2^2)>=sum_(n<=X)q_n~2sqrt(X).         (HB9)
```

Thus changing the split between the two ports cannot remove the raw scale.

For the actual tent aperture, take

```text
b_N(n)=sqrt(Lambda(n)w_(N,L)(n)/c_N).
```

Then `||b_N||^2=T_L(N)/c_N->1`.  The vector is normalized at each aperture, but the
cofinal direct-sum weight in `(C3)` gives

```text
sum_(exp(J)<=N<exp(J+1))
  c_N/N ||b_N||^2 asymp_L exp(J/2).                       (HB10)
```

For an arbitrary two-port factorization of the same positive coefficients, `(HB9)` gives the same
lower bound for the sum of the two port energies.  Hence the prime and polar modes must be
identified or quotiented before either port is declared positive.  An ordinary Bohr GNS
construction cannot do that.

The apparent polynomial escape `(HB5)` can recover the linear current only as an off-diagonal
coefficient

```text
sum_(n<=X)q_n n^(-it)=<U_t a_X,u_X>,
u_X(n)=1_(Lambda(n)>0).                                   (HB11)
```

The pointed vector `u_X` has squared norm asymptotic to the number of prime powers below `X` and
has no global `ell^2` limit.  This is exactly the missing unit-to-source row, not a bounded
replacement for it.

### The half-shift obstruction in ordinary Dirichlet--Hardy space

For

```text
F_X(s)=sum_(n<=X)Lambda(n)n^(-s),
```

the standard `H^2` boundary lies at `Re(s)=1/2`, but

```text
||F_X||_(H^2)^2=sum_(n<=X)Lambda(n)^2~X log X.             (HB12)
```

Moving the half-density into the coefficients gives

```text
G_X(s)=sum_(n<=X)Lambda(n)n^(-1/2)n^(-s),
||G_X||_(H^2)^2~(1/2)(log X)^2,                           (HB13)
```

but the desired arithmetic value is now `G_X(it)` on `Re(s)=0`.  The
Hedenmalm--Lindqvist--Seip correspondence gives point evaluation only inside the square-summable
polydisk and local restriction on the shifted line, not on this distinguished boundary orbit
([Hedenmalm--Lindqvist--Seip](https://doi.org/10.1215/S0012-7094-97-08601-4)).

The failure is already visible on these source polynomials.  If
`|t|<=1/(3 log X)`, then all phases have real part at least `cos(1/3)`, so PNT and partial
summation give

```text
|G_X(it)|>=c sqrt(X),

integral_(-1/(3log X))^(1/(3log X)) |G_X(it)|^2 dt
  >=c' X/log X.                                          (HB14)
```

Dividing by `(HB13)` gives at least `c''X/(log X)^3`.  Therefore no cutoff-uniform boundary
restriction at `Re(s)=0` can be extracted from the polynomial coefficient norm.  The full-torus
`H^2` class also has no canonical restriction to the Haar-null arithmetic orbit; this is the
already-formalized ambient point-evaluation obstruction in a multiplicative guise.

### Volterra and Helson do not restore the pointed row

The canonical Hardy--Dirichlet primitive of the prime current is

```text
g_*(s)=log zeta(s+1/2)
 =sum_(n>=2) Lambda(n)/(sqrt(n)log n)n^(-s),
-g_*'(s)=sum_(n>=2)Lambda(n)/sqrt(n)n^(-s).               (HB15)
```

Brevig--Perfekt--Seip prove that boundedness of the associated Volterra operator forces its symbol
into every finite Hardy class, in particular `H^2`
([primary paper](https://arxiv.org/abs/1602.04729)).  But the prime coefficients in `(HB15)` give

```text
||g_*||_(H^2)^2>=sum_p 1/p=infinity.                      (HB16)
```

So the canonical Volterra/Carleson sewing fails before RH enters.

Likewise, the full Helson matrix `M(alpha)_(m,n)=alpha(mn)` with either
`alpha(n)=Lambda(n)/sqrt(n)` or the primitive coefficients from `(HB15)` is unbounded: its
`n=1` column is not in `ell^2`.  Compressing to `m,n>=2` removes precisely that pointed
unit-to-source row.  For the derivative coefficients, the compression is only the direct sum over
primes of rank-one blocks

```text
M_p(j,k)=log(p)p^(-(j+k)/2),        j,k>=1,
||M_p||=log(p)/(p-1),
sup_p ||M_p||=log 2.                                      (HB17)
```

It is bounded because the source row has been deleted.  The general positive Helson/Carleson
theory therefore controls product-index Hankel forms, not the missing prime--polar seam; see
[Perfekt--Pushnitski](https://arxiv.org/abs/1611.03772).  The bounded multiplicative Hilbert
matrix has the same constant-free restriction and an extra `1/log n` damping
([Brevig--Perfekt--Seip--Siskakis--Vukotic](https://arxiv.org/abs/1411.7294)).

### Fixed-resolution Hilbert profiles are excluded

There is also a direct corollary of the corpus's prime-sampling microlocalization law.  If an RKHS
on the logarithmic line has a continuous translation-invariant kernel

```text
K(x,y)=k(x-y),       k(0)>0,
```

then its normalized kernel coherence is bounded below on one fixed radius `|x-y|<=r`.  A Bessel
bound for the critical evaluations would imply

```text
sum_(|log p-x|<=r)(log p)^2/p<=C.
```

The left side is `2xr+o(1)` and diverges.  Hence no fixed-resolution translation-invariant Hilbert
profile space can isolate the prime channel.  Adaptive quartic/rapid Fock spaces can shrink their
coherence radius like `1/x` and make prime sampling bounded or compact, as the corpus proves, but
they still provide no polar cross port and no signed passivity.

### Concrete survivor `[CONJECTURE] [NOVELTY UNVERIFIED]`

The Olsen frame identifies a sharper possible provider for the existing open core: a **pointed
half-Sobolev relative sampling colligation**.  On each finite profile interval it must retain the
map

```text
S_I f=(Lambda(n)/sqrt(n) fhat(+/-log n))_n                (HB18)
```

together with the non-`ell^2` unit port `u=(1)` and the continuous
`2cosh(h/2)dh` polar port.  It must then impose a source-defined null relation identifying the
common unit/polar asymptotic before taking a norm.  Its Schur complement must be the already
formalized difference-lag Stieltjes pairing, and its cofinal restriction maps must satisfy `(C4)`.

Olsen supplies the local `S_I` frame.  Brownlowe/Exel supplies coherent arithmetic refinements.
Burnol supplies distributional multiplicative filtering.  None supplies the pointed null relation,
its cross-aperture closed range, or its passivity.  Declaring the unit port zero reproduces the
constant-free Helson compression and loses the source; retaining it in an ordinary Hilbert norm
reproduces `(HB8)`--`(HB10)`.

`[RETIRED]` ordinary Hardy--Bohr, Volterra, positive Helson, and separate Fock sampling as
standalone providers.

`[SURVIVOR]` the local `W_0^(1/2)` frame `(HB1)` and the pointed relative-colligation problem
`(HB18)`.

`[FINAL OPEN CORE SHARPENED]` construct the pointed polar/unit null relation before completion,
prove the resulting relative half-Sobolev synthesis has closed range cofinally, and prove its
source-resolved positive block grows only polynomially.  This is a concrete model of, not a
replacement for, the existing non-Jordan Stieltjes passivity theorem.

## 2026-07-18 Fourier-duality correction and monotone polar--prime transport audit

### Olsen's theorem is not a frame on the Stieltjes autocorrelation cone

The interpretation of `(HB1)` as a host for `(ST3)` is false.  Olsen's Lemmas 3--4 and Theorem 4
apply to

```text
f in W_0^(1/2)(I)
```

with `f` itself supported in the bounded vertical interval `I`, and sample `fhat(+/-log n)`.
To obtain the repository samples `C_v(log n)` one would have to put

```text
f=|vhat|^2,       fhat=C_v                                  (QT0)
```

up to the Fourier convention.  Although `C_v` is compactly supported when `v` is aperture
supported, `|vhat|^2` is generally not.  It is therefore outside Olsen's theorem.

This is a genuine obstruction, not only a missing density argument.

1. If a nonzero `v` is supported in an interval of width less than `log 2`, then
   `C_v(+/-log n)=0` for every prime power `n>=2`.  Hence no lower prime-sampling bound holds on the
   unrestricted autocorrelation cone.
2. Let `h_0=log 2` and take two normalized smooth packets of width `epsilon` separated by `h_0`.
   Their autocorrelation has a value bounded away from zero at `h_0`, while

   ```text
   integral_R (1+h^2)^(1/2)|C_v(h)|^2 dh=O(epsilon).        (QT0a)
   ```

   Thus the corresponding global `H^(1/2)` upper sampling bound also fails.
3. On Olsen's actual time-limited spaces, the upper frame constant grows at least linearly under
   interval exhaustion, as in `(HB3)`, while compact Fourier gaps between `0` and `log 2` force the
   optimal lower constant to tend to zero.  Olsen--Saksman prove a stronger degeneration for the
   standard Dirichlet--Hardy weights.

The coefficient mismatch remains as well: Olsen controls the quadratic measure
`sum Lambda(n)^2/n delta_(log n)`, whereas `(ST3)` is linear in
`sum Lambda(n)/sqrt(n) C_v(log n)`.  Passing between the two geometries requires an unbounded
diagonal.

`[CORRECTION]` Retain `(HB1)` only as a boundary-side Fourier sampling theorem on its stated
compact-support class.  `[RETIRED]` `(HB18)` as a provider for the Stieltjes aperture and the claim
that Olsen supplies its local source frame.

Primary sources:

- J. F. Olsen, [*Local properties of Hilbert spaces of Dirichlet
  series*](https://arxiv.org/abs/1011.3370), Lemmas 3--4 and Theorem 4.
- J. F. Olsen and E. Saksman,
  [*On the boundary behaviour of the Hardy spaces of Dirichlet
  series*](https://arxiv.org/abs/0907.2708), Lemma 9.
- J. Ortega-Cerdà and K. Seip,
  [*Fourier frames*](https://arxiv.org/abs/math/0005092), for the fixed-exponential-type
  sampling-measure boundary.

### Exact monotone sewing of the full polar and prime measures `[PAPER-PROVED] [BRIDGE]`

The failed Olsen lane does expose a different exact construction.  On the positive lag ray put

```text
q_n=Lambda(n)/sqrt(n),
P=sum_(n>=2)q_n delta_(log n),
Q=2cosh(h/2)dh,
G(h)=Q((0,h])=4sinh(h/2),
M(h)=P((0,h]),
R(h)=G(h)-M(h).                                           (QT1)
```

Enumerate the prime powers as `n_1<n_2<...`, set

```text
m_j=sum_(i<=j)q_(n_i),
beta_j=G^(-1)(m_j)=2 asinh(m_j/4),
I_j=(beta_(j-1),beta_j],
T(h)=log(n_j) for h in I_j.                              (QT2)
```

Then

```text
Q(I_j)=q_(n_j),          T_#Q=P.                          (QT3)
```

Consequently every compactly supported `C^1`, or BV, profile satisfies

```text
integral F d(Q-P)
 =integral (F(h)-F(T(h)))dQ(h)
 =sum_j integral_(I_j)(F(h)-F(log n_j))dQ(h)
 =-integral_0^infinity R(h)dF(h).                         (QT4)
```

The last equality is exactly the already-formalized Stieltjes integration-by-parts carrier in
monotone-transport coordinates.  The construction uses no zero data and no sign choice.

There is a compatible finite graph.  For the first `K` cells,

```text
J_K:L^2(P_K)->L^2(Q|_(0,beta_K]),
J_K a=a o T                                                (QT5)
```

is an isometry and sends the constant on the atomic side to the constant on the polar side.  Its
graph is closed and the graphs are nested with `K`.  This does **not** solve the pointed unit
problem:

- the squared norm of that constant is `m_K->infinity`;
- in ordinary `ell^2` coordinates it is `(sqrt(q_(n_j)))`, the raw GNS vector of
  `(HB7)`--`(HB10)`, not the unweighted row `u=(1)` of `(HB11)`;
- the graph is neutral, but not radical, for the Krein form
  `||g||_(L^2(Q))^2-||a||_(L^2(P))^2`, so that form does not descend through the ordinary graph
  quotient;
- the auxiliary seminorm `||F-F o T||_(L^2(Q))` kills constants, but the anti-diagonal unit trace
  remains nonclosable cofinally.

Thus `(QT5)` is a legitimate locally finite correspondence, not the required global pointed
Hilbert reduction.

### Same-aperture closure forces the completed error back in

At a physical aperture `H` the two restrictions do not have equal mass:

```text
Q((0,H])-P((0,H])=R(H).                                  (QT6)
```

Hence no coupling has exactly those two marginals unless `R(H)=0`.  The canonical boundary closure
is

```text
Qtilde_H=Q|_(0,H]+(-R(H))_+ delta_H,
Ptilde_H=P|_(0,H]+( R(H))_+ delta_H.                      (QT7)
```

They have equal mass and

```text
Q|_(0,H]-P|_(0,H]=(Qtilde_H-Ptilde_H)+R(H)delta_H.         (QT8)
```

The endpoint atom is invisible to the Stieltjes aperture because its autocorrelation test has
`F(H)=0`.  The constant unit test sees `R(H)` exactly.  Endpoint vanishing therefore hides the
pointed defect from that one test; it does not make the defect null.

Let `pi_H` be the monotone coupling of `Qtilde_H` and `Ptilde_H`.  The one-dimensional transport
formula gives

```text
W(H):=integral |x-y| dpi_H(x,y)
     =integral_0^H |R(s)|ds.                              (QT9)
```

This yields the sharpest positive salvage.  On the path space of triples `(x,y,s)` define

```text
d(x,y;s)=sgn(x-y) 1_(min(x,y),max(x,y)](s),
g_F(x,y;s)=1_(min(x,y),max(x,y)](s) F'(s).                (QT10)
```

Fubini and monotonicity give

```text
||d||^2=W(H),
||g_F||^2=integral_0^H |R(s)||F'(s)|^2 ds,
<d,g_F>=integral F d(Q-P)       when F(H)=0.              (QT11)
```

For a pointed scalar `t`,

```text
Gamma_+/- (t,F)=(t d +/- g_F)/sqrt(2)                     (QT12)
```

is therefore an exact, non-Jordan, linear difference-of-squares factorization:

```text
||Gamma_+(t,F)||^2-||Gamma_-(t,F)||^2
 =2 Re(conj(t) integral F d(Q-P)).                        (QT13)
```

It applies directly to compact Lipschitz tents and, in weak-derivative form, to the rectangular
Stieltjes blocks.  It is defined on a source class larger than the evaluated defect line and does
not choose the positive part of the final scalar.

### The transport norm is exactly the RH theorem, not its proof

The positive vector in `(QT10)` already contains the assembled cumulative defect:

```text
||d||^2=integral_0^H|R(s)|ds.                             (QT14)
```

In particular the unit-only source `(t,0)` forces both ports in `(QT12)` to pay
`|t|^2W(H)/2`.  This violates the anti-circularity requirement at `(C2)`: the polar and prime
measures have been paired before norming, but their cumulative discrepancy has then been
Jordanized by absolute value.

The calibration is exact.  RH and the classical von Koch bound give

```text
R(H)=O((1+H)^3),          W(H)=O((1+H)^4).                (QT15)
```

Conversely, any polynomial bound on `W` makes
`integral_0^infinity exp(-epsilon h)|R(h)|dh` finite for every `epsilon>0`.  The already-proved
Laplace identity for `R` then continues holomorphically through every `Re z>0`.  Its
`zeta'/zeta(z+1/2)` term excludes every zeta zero with real part greater than `1/2`; functional
equation symmetry gives RH.  Hence

```text
W(H) has polynomial growth   iff   RH.                    (QT16)
```

The global cost is necessarily infinite.  Even under RH the critical-line poles appear on the
boundary of its Laplace transform, so no finite global `W_1` completion exists.

After the natural `c_N` normalization, the unit-channel block scale is

```text
sum_(exp(J)<=N<exp(J+1)) W(log N)/N
 asymp integral_J^(J+1)W(h)dh.                            (QT17)
```

Thus polynomial `(C4)` control of this transport factorization is literally `(QT16)`.

`[PAPER-PROVED] [BRIDGE]` The monotone map, its locally finite graph, and the path-space
difference-of-squares are exact.

`[REDISCOVERED]` One-dimensional monotone rearrangement and the cumulative-distribution
`W_1` formula; `(QT4)` is the existing critical-Mellin Stieltjes law in that language.

`[FALSIFIED]` Quantile transport as the missing pointed-null or cofinal passivity theorem.  It
either retains the divergent GNS unit, hides `R(H)` at an endpoint zero, or pays the RH-equivalent
absolute cost `(QT14)`.

`[OPEN CORE]` Construct a source-local signed sewing whose positive block does not expose
`|R|`, `E_L^+`, or a spectral positive part before cross-aperture cancellation.  It must retain
the true pointed unit row, reproduce the existing Stieltjes form on compact profiles, and prove
the polynomial block bound from an arithmetic identity stricter than monotone mass matching.

## 2026-07-18 polar-straightened Clark audit: exact phase sewing, cofinal source still missing

### The prime current is an unconditional Clark fibre `[PAPER-PROVED] [BRIDGE]`

It is useful first to restore the symmetric lag line.  Put

```text
P^sym=sum_(n>=2)q_n(delta_(log n)+delta_(-log n)),
Q^sym=2cosh(h/2)dh,                 q_n=Lambda(n)/sqrt(n),
G(h)=4sinh(h/2).                                         (CL1)
```

Then `G` is odd, `G_#Q^sym=dy`, and

```text
sigma_0:=G_#P^sym
 =sum_(n>=2)q_n(delta_(y_n)+delta_(-y_n)),
y_n=2(sqrt(n)-1/sqrt(n)).                               (CL2)
```

For even profiles this is exactly twice the positive-lag carrier, so no arithmetic content has
been changed.  Moreover `y_n^2>=n` for `n>=2`, whence

```text
integral (1+y^2)^(-1)dsigma_0(y)
 <=2sum_(n>=2)Lambda(n)n^(-3/2)<infinity.                (CL3)
```

Thus `sigma_0` is singular and Poisson-finite.  The half-plane Herglotz--Clark theorem therefore
produces a meromorphic inner function `theta` for which `sigma_0` is the `alpha=1` Clark measure.
Choose no Clark mass at infinity and use the symmetry to fix the remaining real Herglotz constant:

```text
m(z)=(1/pi)integral[(t-z)^(-1)-t/(1+t^2)]dsigma_0(t),
m(-z)=-m(z),                 theta=(m-i)/(m+i).          (CL4)
```

This odd normalization is important: the fixed Clark measure alone leaves an additive real
constant in `m`, and the derivative norms below change under that gauge.

Write `theta(x)=exp(i phi(x))` with increasing phase.  The remaining Clark fibres are

```text
sigma_beta
 =sum_(phi(x)=beta mod 2pi) 2pi/phi'(x) delta_x,
sigma_0({+/-y_n})=q_n,
phi'(+/-y_n)=2pi/q_n.                                  (CL5)
```

Aleksandrov disintegration gives, weakly on compact tests,

```text
(1/(2pi))integral_0^(2pi) sigma_beta dbeta=dy.           (CL6)
```

The external ingredients here are parent theory, not RH input: Poltoratski's half-plane Clark
description and atom formula
(<https://arxiv.org/abs/1706.08002>, Section 2.2), and the Clark disintegration/unitary theorems
of Aleksandrov--Doubtsov
(<https://arxiv.org/abs/1904.04308>, Theorems 3.3 and 5.1).  Equation `(CL3)` is the only
admissibility check needed for the prime measure.

### A fixed Clark fibre has the wrong analytic and pointed ports

The common model space `K_theta` does give a neutral analytic graph: after the standard Clark
normalization, the ordinary boundary embedding into `L^2(dy)` and the `beta=0` Clark unitary into
`L^2(sigma_0)` have equal norms on `K_theta`.  This does not identify the Stieltjes multiplier
algebra.  A nonzero compactly supported boundary multiplier cannot preserve `K_theta`; otherwise a
nonzero Hardy boundary function would vanish off a compact set, contrary to boundary uniqueness.
The compact moving tents therefore leave the neutral analytic graph.

The cyclic-vector normalization also damps precisely the unit that must be retained.  Under the
Cayley transform the finite cyclic vector is, up to a constant,

```text
k_i(y)=(y+i)^(-1),
<M_F k_i,k_i> proportional to integral F(y)/(1+y^2) dsigma_0(y).  (CL7)
```

The raw prime current requires the constant vector

```text
1=(y+i)k_i,                                               (CL8)
```

and multiplication by `y+i` is unbounded.  On the positive aperture `Y_X=G(log X)`, the PNT and
partial summation give

```text
m_X=sigma_0((0,Y_X])=sum_(n<=X)Lambda(n)/sqrt(n)
   =2sqrt(X)+o(sqrt(X))=Y_X+o(Y_X).                      (CL9)
```

Thus every fixed-fibre GNS realization of all compact multipliers has raw unit norm squared at
least `m_X`.  After `c_N=C_L sqrt(N)` normalization, its `(C3)` block again costs

```text
sum_(exp(J)<=N<exp(J+1))m_N/N asymp exp(J/2).             (CL10)
```

The Clark graph is maximal neutral, so its coisotropic quotient is zero; an ordinary graph quotient
retains only the Poisson-damped current `(CL7)`.  This refutes a raw fixed-fibre or cyclic-unit
solution.  It does **not** refute the ensemble phase flow, which uses the fibres before norming.

### Exact phase-circle difference of squares `[PAPER-PROVED] [BRIDGE SURVIVOR]`

For compact Lipschitz `F`, set

```text
S_F(beta)=integral F dsigma_beta
 =2pi sum_j F(x_j(beta))/phi'(x_j(beta)),
x_j(beta)=phi^(-1)(beta+2pi j).                          (CL11)
```

Then `(CL6)` says that the polar part is the fibre mean.  Branch differentiation gives

```text
S_F'(beta)
 =2pi sum_j [(F'phi'-F phi'')/(phi')^3](x_j(beta)).      (CL12)
```

Let `s(beta)=beta-pi` on `(0,2pi)`, periodically extended, and use
`L^2(d beta/(2pi))`.  Periodic integration by parts yields the exact signed identity

```text
D(F):=integral F d(sigma_0-dy)
 =(1/(2pi))integral_0^(2pi)s(beta)S_F'(beta)dbeta.        (CL13)
```

Consequently the linear pointed maps

```text
Gamma_+/-^Clark(t,F)=(t s +/- S_F')/sqrt(2)              (CL14)
```

satisfy

```text
||Gamma_+^Clark(t,F)||^2-||Gamma_-^Clark(t,F)||^2
 =2 Re(conj(t)D(F)),
||s||^2=pi^2/3.                                          (CL15)
```

Unlike monotone transport, `(CL14)` neither takes `|R|` nor chooses the sign of the evaluated
defect.  The pointed feature is fixed on one phase circle.  This is the first audited spectral
construction in this sequence that gives the correct **finite-aperture non-Jordan cross term**
without retaining the raw prime GNS unit in that same formula.

It is not yet `(C4)`.  On the full direct sum of pointed profiles, the unit-only direction
`(t,0)` has fixed positive energy.  Stacking it gives

```text
sum_(exp(J)<=N<exp(J+1))(c_N/N)||s||^2 asymp exp(J/2).    (CL16)
```

Therefore the admissible cofinal source cannot be the free space `C direct_sum Lip_c`.  It must
contain a source-defined relation tying the pointed trace to the phase derivative, so that the
distinguished positive combination `t_N s+S_(F_N)'` cancels before norming, while still containing
more than the evaluated defect line.  Defining that relation from `D(F_N)` would be circular.

### Centered phase cells expose a second-order survivor

Let `Y=phi^(-1)` and

```text
H_F(u)=F(Y(u))Y'(u).
```

Then `S_F(beta)=2pi sum_j H_F(beta+2pi j)`, and `(CL13)` becomes the exact midpoint-quadrature
error

```text
D(F)=sum_j[2pi H_F(2pi j)
                 -integral_(2pi j-pi)^(2pi j+pi)H_F(u)du].  (CL17)
```

On each centered cell put

```text
kappa(r)=-(1/2)(pi-|r|)^2,          -pi<=r<=pi.           (CL18)
```

It has zero value and first derivative at cell boundaries and, distributionally,

```text
kappa''=2pi delta_0-1.
```

Hence, whenever `H_F'` is locally BV and `H_F` is compactly supported,

```text
D(F)=sum_j integral_(cell j) kappa(u-2pi j)dH_F''(u),     (CL19)

H_F''=F''(Y)(Y')^3+3F'(Y)Y'Y''+F(Y)Y'''.                (CL20)
```

Every affine phase-cell mode is killed before different cells are summed.  This is a genuine
sharpening of the first-derivative carrier, not a positivity claim.

The exact moving tents also reveal the limit.  Their corners make `H_F''` a signed measure with
Dirac atoms, not an `L^2` vector.  Total variation Jordanizes the source; analytic model-space
norms exclude every nonzero compact profile; and a direct sum of cellwise `H^(-1)` spaces pays one
fixed representer per crossed cell.  None supplies the coherent Hilbert factorization required by
`(C2)`--`(C4)`.

### Hostile verdict and the sharper conjecture

Several tests prevent the Clark vocabulary from becoming theorem theatre.

1. The half-line Clark measure has a free Herglotz constant.  Changing it fixes `sigma_0` and the
   node derivatives in `(CL5)` but changes `phi''`, `S_F'`, and every curvature norm.  The symmetric
   odd choice `(CL4)` fixes the gauge; it proves no estimate.
2. Cauchy--Schwarz in `(CL13)` gives
   `||S_F'||>=sqrt(3)|D(F)|/pi`.  For cutoff-unit approximants, `D(F)` is the cumulative completed
   error.  The phase curvature has encoded that error rather than bounded it.
3. Uniform control on the full Lipschitz ball recovers the Kantorovich norm
   `integral_0^H|R(h)|dh`, whose polynomial growth is RH-equivalent by `(QT16)`.  The target domain
   must therefore be the actual autocorrelation/source cone with coherent restrictions, not all
   Lipschitz tests.
4. The Clark construction works for every singular Poisson-finite atomic measure.  It cannot by
   itself distinguish ordinary primes from generalized-prime burst countermodels; the missing
   estimate must visibly use `(C6)` or an equivalent ordinary-integer sewing law.

`[FALSIFIED]` A fixed Clark fibre, its bounded cyclic vector, the free pointed direct sum, an
`L^2` Peano-curvature factor, or Clark theory alone as the cofinal passivity proof.

`[PAPER-PROVED POSITIVE SALVAGE]` The odd Clark family gives the exact signed phase factorization
`(CL11)`--`(CL15)`, and centered cells give the affine-annihilating distributional Peano law
`(CL17)`--`(CL20)`.

`[CONJECTURE] [NOVELTY UNVERIFIED]` **Odd-Clark folded-derivative sewing theorem.**  For the exact
moving-tent profiles supplied by the formal Stieltjes carrier, construct coherent source spaces
`X_J` and restrictions `(t,F)->(t_N,F_N)` such that:

- the source norm is fixed from the Boolean/principal-ideal packing and the odd Clark phase, before
  `D(F)`, `R`, or any spectral positive part is evaluated;
- `X_J` contains the exact tent transforms, their distributional corner curvatures, and a class
  strictly larger than the distinguished line, but excludes the free unit-only direction
  responsible for `(CL16)` by a source-defined closed relation;
- the distinguished sections are uniformly bounded; and
- the genuinely positive folded channel obeys

```text
sum_(exp(J)<=N<exp(J+1))(c_N/N)
  ||t_N s+S_(F_N)'||_(L^2(T))^2
 <=C_L(1+J)^a||(t,F)||_(X_J)^2.                          (CL21)
```

The opposite folded channel then supplies `(CL15)`, and `(CL21)` would be an admissible concrete
provider for `(C4)`.  The theorem is presently open and carries RH strength.  Its exact mathematical
core is a non-direct-sum Sobolev/RKHS bornology modulo phase-cell affine modes, with coherence
coming from ordinary floor packing rather than from the globally assembled completed error.

## 2026-07-18 Clark closure audit: Fourier classification, inverse jets, and source-linearity no-go

### The whole Clark circle diagonalizes exactly `[PAPER-PROVED] [BRIDGE]`

Let `Y=phi^(-1)` and `H_F(u)=F(Y(u))Y'(u)` as above.  If

```text
a_k(F)=(1/(2pi))integral_0^(2pi)S_F(beta)exp(-ik beta)dbeta,
```

then coarea gives the exact formula

```text
a_k(F)=integral_R F(y)exp(-ik phi(y))dy
      =integral_R F(y)conj(theta(y))^k dy.                (CF1)
```

Thus

```text
D(F)=S_F(0)-a_0(F)=sum_(k!=0)a_k(F).                     (CF2)
```

For arbitrary compact tests the last sum is safely interpreted by Abel convergence.  For the exact
piecewise-linear moving tents, `H_F'` is piecewise BV, so `a_k(F)=O(k^(-2))` and `(CF2)` converges
ordinarily.  Oddness of `theta` and reality/evenness of the symmetric Stieltjes profile give
`a_(-k)=a_k in R`.

There is a complete diagonal Sobolev family.  For any `1/2<s<3/2`, put

```text
u_s(k)=|k|^(-s),             A_s(F)(k)=|k|^s a_k(F),
Gamma_+/-^(s)(t,F)=(t u_s +/- A_s(F))/sqrt(2).            (CF3)
```

Then

```text
||Gamma_+^(s)||^2-||Gamma_-^(s)||^2=2 Re(conj(t)D(F)),
||u_s||^2=2 zeta(2s).                                      (CF4)
```

At `s=1`, multiplication by the diagonal phase `i sgn(k)` identifies `(CF3)` unitarily with the
sawtooth factorization `(CL14)`.  Every diagonal Hilbert factorization of point-minus-mean has this
same trace threshold: the evaluation row is in `H^(-s)(T)` exactly for `s>1/2`.  Changing `s` or
rescaling the two mode vectors only moves cost reciprocally between the pointed row and the profile
row.  Since `||u_s||>0`, the free unit direction still gives `(CL16)`.

The analytic powers of the inner function do not improve this.  If `f,g in K_theta` and
`F=f conj(g)`, then

```text
a_k(F)=<f,theta^k g>=0,             k>=1.                (CF5)
```

The uniformly controlled model-space class is therefore a null class for the defect.  After the
Cayley transform, Bessel control of the powers `theta^k` applies to
`G(y)=pi(1+y^2)F(y)` and yields a right-hand side containing
`integral(1+y^2)|F(y)|^2dy`.  On `y asymp sqrt(N)` this restores the raw aperture factor.  The
Fourier formula is a sharper coordinate description of `(CL21)`, not another source of passivity.

### Global folded `H^(-1)` is valid, but isometric to the same carrier

The preceding rejection of a **direct sum** of cellwise `H^(-1)` spaces must not be overread.
Folding all cells before norming is exact.  Define on the phase circle

```text
P_F(r)=sum_j H_F(r+2pi j),
T_F=P_F''=sum_j H_F''(r+2pi j).                          (CF6)
```

The distribution `T_F` has total mass zero.  Its mean-zero primitive is `P_F'`, and, since
`S_F=2pi P_F`,

```text
||T_F||_(dot H^(-1)(T))
 =||P_F'||_2
 =(1/(2pi))||S_F'||_2.                                  (CF7)
```

In particular the folded corner Dirac masses of an exact tent are legitimate `dot H^(-1)` vectors;
no total variation is required.  With the periodic Peano kernel `(CL18)`,

```text
D(F)=<kappa,T_F>=<s,S_F'>_(L^2(T)).                      (CF8)
```

This is genuinely non-Jordan because every phase cell is summed before the square.  It is also
exactly `(CL14)` under the derivative isometry `(CF7)`.  The global fold repairs the regularity of
the Peano picture, but supplies no smaller norm and no new estimate.  A corner-only formula is not
enough either: the nonlinear polar and inverse-phase Jacobians in `(CL20)` contribute an essential
absolutely continuous curvature term.

The longitudinal/transverse decomposition is now explicit.  Put

```text
a=||s||^2=pi^2/3,
b_F=S_F'=(D(F)/a)s+b_F^perp.                             (CF9)
```

Then

```text
||t s+b_F||^2
 =a|t+D(F)/a|^2+||b_F^perp||^2.                         (CF10)
```

The unique scalar choice minimizing the positive port is `t=-D(F)/a`; it is forbidden because it
defines the source trace from the evaluated prime--polar defect.  It also leaves the transverse
energy untouched.  No scalar relation alone can be the missing sewing.

### The profile fold is not a linear factorization of the aperture quadratic form

For a physical aperture vector, `F=C_v` is already quadratic in `v`.  Hence

```text
v -> C_v -> T_(C_v) -> S_(C_v)'
```

is quadratic, not a linear Hilbert feature.  It becomes linear only after passing to a new profile
or correlation-tensor source spanned by cross-correlations `C_(v,w)`.  The slice `t=1` is affine,
not a source subspace.

Nor can the pointed trace be recovered from the folded seminorm on the full linearized correlation
source.  Choose a smooth compact phase function `H` whose `2pi`-periodization is identically one,
and set

```text
F(y)=H(phi(y))phi'(y).                                   (CF11)
```

It may be chosen real and even with `F(0)>0`.  Then `H_F=H`, so

```text
T_F=0,            S_F'=0,            D(F)=0,             (CF12)
```

while the origin trace is nonzero.  The Dixmier--Malliavin factorization theorem puts every real
even `C_c^infinity(R)` function in the finite linear span of compact cross-correlations, and
polarization puts it in the span of compact autocorrelations.  Therefore

```text
ker(T on the linearized autocorrelation source)
  is not contained in ker(F |-> F(0)).                   (CF13)
```

This is a structural, not numerical, obstruction.  The tempting rectangular trace graph
`2L t=F(0)` excludes the literal pair `(t,0)`, since the two-edge autocorrelation has `F(0)=2L`.
But `(CF11)` gives `T_F=0` with `t!=0`; its positive Clark port is the fixed sawtooth row and its
block still grows as `exp(J/2)`.  A valid source subspace must satisfy a stronger arithmetic kernel
condition than the ordinary origin trace.  The parent factorization used here is J. Dixmier and
P. Malliavin, *Factorisations de fonctions et de vecteurs indefiniment differentiables*,
Bull. Sci. Math. 102 (1978), 307--330.

Differentiating Clark branches before autocorrelation does not restore linearity at the required
regularity.  If `U_h` is physical translation and

```text
A_beta=sum_j [2pi/phi'(y_j(beta))] U_(G^(-1)(y_j(beta))),
```

then `S_(C_v)(beta)=<A_beta v,v>`.  For `v in H^1`, differentiation gives a source-defined sum of
a phase-curvature term and a translation-generator term.  Branchwise polarization is possible,
but its positive energy pays the absolute phase curvature and `||v'||^2`.  The exact rectangular
indicators have endpoint-Dirac derivatives and lie outside `H^1`, indeed outside endpoint
`H^(1/2)`.  The branch factorization is therefore nonclosable on the source that produces the exact
tents.  Differentiability appears only after the quadratic autocorrelation smoothing.

### Exact Euler resolvent of the odd prime phase `[PAPER-PROVED] [BRIDGE]`

The odd Herglotz function itself has an exact arithmetic normal form.  Pairing the positive and
negative atoms cancels the Herglotz subtraction:

```text
m(z)=(2z/pi)sum_(n>=2) q_n/(y_n^2-z^2),
q_n=Lambda(n)/sqrt(n).                                  (CE1)
```

Define the ordinary-integer resolvent

```text
A(w)=sum_(n>=2)Lambda(n)sqrt(n)[(n-w)^(-1)-n^(-1)],
J(w)=2(sqrt(w)-1/sqrt(w)).                              (CE2)
```

It converges locally uniformly off the prime powers and satisfies

```text
m(J(w))=[A(w)-A(w^(-1))]/[pi(sqrt(w)+w^(-1/2))].        (CE3)
```

For `|w|<2`, with `L(s)=-zeta'(s)/zeta(s)`, one has the absolutely convergent expansion

```text
A(w)=sum_(k>=1)w^k L(k+1/2).                            (CE4)
```

Equivalently, on the maximal central Taylor disk `|z|<sqrt(2)`,

```text
m(z)=(z/(2pi))sum_(k>=0)
  U_k(1+z^2/8)L(k+3/2),                                 (CE5)
```

where `U_k` is the second-kind Chebyshev polynomial.  Every zeta logarithmic derivative in `(CE4)`
and `(CE5)` lies in the absolutely convergent half-plane; no continuation or zero information has
entered.  The radius stops exactly at the first Clark atom `y_2=sqrt(2)`.  This is an Euler-safe
central bridge, not a way to estimate high phase cells.

Möbius floor packing is equally exact:

```text
A(w)=sum_(d,k>=1)mu(d)log(k)sqrt(dk)
  [(dk-w)^(-1)-(dk)^(-1)],                              (CE6)

psi(X)=sum_(d<=X)mu(d)log(floor(X/d)!),                  (CE7)

sum_(n<=X)Lambda(n)/sqrt(n)
 =psi(X)/sqrt(X)+(1/2)integral_1^X psi(t)t^(-3/2)dt.     (CE8)
```

This uses the desired ordinary product fibres, but their signs are indispensable.  Jordanizing
the divisor channels before summing `dk=n` costs at least

```text
sum_(dk<=X)|mu(d)|log(k)/sqrt(dk)
 >=sum_(X/2<=k<=X)log(k)/sqrt(k)
 >>sqrt(X)log(X).                                        (CE9)
```

Thus `(C6)` enters the prime Clark function exactly, while any separate positive completion of its
Möbius channels is worse than the already-refuted raw half-density port.

### Inverse-phase node jets are small; whole cells are the real obstruction

At a prime-power node `N`, abbreviate `q=q_N`, `y=y_N`, and write

```text
m(y+t)=-a/t+b_N^Cl+d_N^Cl t+O(t^2),       a=q/pi.        (CE10)
```

The regular coefficients have absolutely convergent source formulas

```text
b_N^Cl=(1/pi)[-q/(2y)
  +2y sum_(n!=N)q_n/(y_n^2-y^2)],                       (CE11)

d_N^Cl=(1/pi)[q/(4y^2)
  +2sum_(n!=N)q_n(y_n^2+y^2)/(y_n^2-y^2)^2]>0,          (CE12)

y_n^2-y_N^2=4(n-N)(1-1/(nN)).                           (CE13)
```

If `Y=phi^(-1)` and `u_N=phi(y_N)`, series inversion gives

```text
Y'(u_N)=a/2,
Y''(u_N)=-a b_N^Cl/2,
Y'''(u_N)=a[1+3(b_N^Cl)^2-3a d_N^Cl]/4.                 (CE14)
```

Splitting the sums in `(CE11)`--`(CE12)` into
`n<N/2`, `N/2<=n<=2N`, and `n>2N`, and using only `Lambda(n)<=log n`, proves

```text
|b_N^Cl| <<(1+log N)^2,
0<d_N^Cl <<sqrt(N)(1+log N),                            (CE15)

|Y''(u_N)| <<q_N(1+log N)^2,
|Y'''(u_N)|<<q_N(1+log N)^4.                            (CE16)
```

The inverse phase is therefore locally flat at every arithmetic node on the correct half-density
scale.  This is a nontrivial positive salvage for the Peano formulation.

It does not control a cell.  If `N_j<N_(j+1)` are consecutive prime powers, then

```text
integral_(u_j)^(u_j+2pi)Y'(u)du
 =y_(N_(j+1))-y_(N_j)
 asymp (N_(j+1)-N_j)/sqrt(N_j)                          (CE17)
```

for comparable endpoints.  Established unconditional prime-gap bounds still allow an exponential
power in the logarithmic aperture, whereas RH gives a polylogarithmic width from the classical
von Koch--Schoenfeld error term.  Node jets cannot replace a signed whole-cell theorem.  The
relevant primary benchmarks are Baker--Harman--Pintz, *The difference between consecutive primes,
II*, Proc. LMS 83 (2001), and Schoenfeld's RH-conditional explicit `psi` bounds, Math. Comp. 30
(1976).

### Revised exact open core

The Clark programme now has a precise closed boundary.

`[PAPER-PROVED] [BRIDGE]` The Fourier law `(CF1)`--`(CF4)`, global folded `dot H^(-1)` law
`(CF6)`--`(CF8)`, Euler resolvent `(CE1)`--`(CE8)`, and inverse-node estimates
`(CE10)`--`(CE16)`.

`[FALSIFIED]` Changing diagonal Sobolev weights, analytic inner powers, a direct-sum or globally
folded Sobolev norm by itself, an origin-trace graph on the full autocorrelation span, branch
differentiation on rectangular vectors, or positive Möbius channels.

`[OPEN CORE]` Construct from the signed ordinary product fibres a coherent arithmetic subspace
`X_J` of the lifted correlation source such that

```text
ker(T|_(X_J)) subset ker(ell_src),                       (CE18)
```

and the angle/closed-range estimate encoded by `(CF10)` is polynomial after the `(C3)` block
weight.  Equivalently, in Fourier coordinates, for one fixed `1/2<s<3/2`, prove

```text
sum_(N asymp exp(J))(c_N/N)sum_(k!=0)
 abs(t_N * abs(k)^(-s)+abs(k)^s * a_k(F_N))^2
 <=C_L(1+J)^A||x||_(X_J)^2.                             (CE19)
```

The subspace and its norm must be defined before `D(F_N)` is evaluated, must contain more than the
distinguished line, and must preserve Möbius cancellation through `dk=n`.  Equations `(CE18)` and
`(CE19)`, not another Clark identity, are the exact remaining RH-strength statement.

## 2026-07-18 Clark source-closure audit: whole cells, range geometry, and signed tails

### Exact whole-cell Hermite classification `[PAPER-PROVED] [BRIDGE]`

The inverse-node jets `(CE14)` do not yet identify what is lost between two Clark nodes.  There is
an exact classification of that loss.  Put `ell=2pi`, enumerate the real Clark nodes so that

```text
u_j=ell*j,             Y(u_j)=y_j,             Y'(u_j)=q_j/ell,
```

and choose a primitive `A'=F`.  On the `j`th phase cell define

```text
f_j(t)=A(Y(u_j+t)),                         0<=t<=ell,
a_j=q_j F(y_j)/ell,
I_j=integral_(y_j)^(y_(j+1))F(y)dy,
g_j(F)=I_j-[q_jF(y_j)+q_(j+1)F(y_(j+1))]/2.             (CH1)
```

The cubic Hermite interpolant gives the identity

```text
f_j'(t)=a_j+(a_(j+1)-a_j)t/ell
  +(6g_j(F)/ell^3)t(ell-t)+R_j(t),                       (CH2)

R_j(0)=R_j(ell)=0,                  integral_0^ell R_j=0.
```

The three derivative summands are orthogonal.  Therefore, first for the smooth class and then in
the corresponding weak form,

```text
integral_0^ell |f_j''(t)|^2dt
 ={|q_(j+1)F(y_(j+1))-q_jF(y_j)|^2+12|g_j(F)|^2}/ell^3
  +integral_0^ell|R_j'(t)|^2dt.                         (CH3)
```

Thus every **cellwise positive** second-order completion pays `|g_j|^2` before different cells
can cancel.  This is not a technical defect of a particular interpolant: `(CH3)` is an orthogonal
identity.

The cell defect has a useful endpoint form.  If

```text
Delta_j=y_(j+1)-y_j,
eta_j=Delta_j-(q_j+q_(j+1))/2,
```

then, distributionally for `F'` of bounded variation,

```text
g_j(F)
 =eta_j[F(y_j)+F(y_(j+1))]/2
  -(q_(j+1)-q_j)[F(y_(j+1))-F(y_j)]/4
  -(1/2)integral_(y_j)^(y_(j+1))
      (y-y_j)(y_(j+1)-y)dF'(y).                         (CH4)
```

In particular

```text
g_j(1)=eta_j,
sum_(j=a)^(b-1)eta_j
 =y_b-y_a-[q_a/2+sum_(a<j<b)q_j+q_b/2].                 (CH5)
```

Even the constant-test cell coefficient is the trapezoid-centered critical Chebyshev error, not a
new positive local quantity.

Folding before norming preserves the signs but returns exactly `(CF9)`.  Indeed

```text
sum_j g_j(F)=-D(F),
S_F'(beta)=(D(F)/a)s(beta)+ell sum_j R_j'(beta),
a=ell^2/12=pi^2/3,                                      (CH6)

<s,sum_j R_j'>=0,
||S_F'||^2=|D(F)|^2/a+ell^2||sum_jR_j'||^2.              (CH7)
```

For the positive-lag moving tent

```text
F_(N,L)(y)=h_L(log N-G^(-1)(y)),
P_L(N)=integral F_(N,L)(y)dy
      =C_L sqrt(N)+C_L^vee/sqrt(N),
C_L^vee=exp(L)C_L=4(exp(L/2)-1)^2,                       (CH8)
```

so

```text
sum_jg_(j,N)=P_L(N)-T_L(N)
 =c_N(1-Q_N)-R_(N,L)+C_L^vee/sqrt(N).                   (CH9)
```

By `(SF1)`, the middle term in `(CH9)` is exactly the signed sum of the ordinary fractional-part
remainders with coefficients
`mu(d)mu(e)log(gcd(d,e))`; no absolute value has entered.  Equivalently it is the adjacent-block
transform of the exact floor formula

```text
psi(X)=sum_(d<=X)mu(d)log(floor(X/d)!).                  (CH10)
```

The Hermite coefficient therefore reproduces the already-open coupled Möbius floor remainder.
Before folding, positivity squares the individual `g_j`; after folding, `(CH7)` pays the assembled
`|D(F)|^2/a`.  Node jets control the endpoints `a_j`, not the transverse residual `R_j`.  Ordinary
floor packing describes the `beta=0` nodes, but not the interior rank-one perturbation roots

```text
m(x_j(beta))=-cot(beta/2),                  0<beta<2pi.  (CH11)
```

Current prime-gap input is also far too weak for a local repair: Baker--Harman--Pintz gives, after
the `y=G(log N)` straightening, only a cell-width bound of order `N^0.025`, still exponential in
`J=log N`.  A whole-cell estimate would have to correlate the equal-`beta` roots across cells and
apertures while retaining the signs in `(CH9)`.

### The block port splits into two independent operator estimates `[PAPER-PROVED] [BRIDGE]`

The kernel condition `(CE18)` is only algebraic.  Its quantitative content can be separated
exactly.  On one logarithmic block put `w_N=c_N/N` and define

```text
mathcalT_J x=(sqrt(w_N) T_Nx)_N,
mathcalA_J x=(sqrt(w_N) ell_Nx)_N,
S(t_N)=(t_N s)_N,              S^*S=aI,
Q=I-SS^*/a.                                                   (CA1)
```

Here `T_N` is the folded derivative/curvature feature and `ell_N` is the independently defined
pointed source trace.  The unnormalized positive port

```text
mathcalB_J=mathcalT_J+S mathcalA_J
```

satisfies the exact Loewner identity

```text
mathcalB_J^*mathcalB_J
 =mathcalT_J^*Q mathcalT_J
  +a(mathcalA_J+a^(-1)S^*mathcalT_J)^*
     (mathcalA_J+a^(-1)S^*mathcalT_J).                  (CA2)
```

Consequently a Clark realization of `(C4)` is precisely the conjunction of

```text
||Q mathcalT_J||^2 <<(1+J)^A,                            (CA3)
||mathcalA_J+a^(-1)S^*mathcalT_J||^2 <<(1+J)^A.          (CA4)
```

Equation `(CA3)` is the transverse folded-curvature estimate.  Equation `(CA4)` is the
longitudinal source-trace/Stokes estimate.  A scalar trace graph can alter only `(CA4)`.

For a bounded Hilbert-space fold `T`, the distinction is sharp:

```text
ker T subset ker ell
  iff the trace representer lies in closure(range(T^*)),

|ell(x)|<=C||Tx||
  iff the trace representer lies in range(T^*).          (CA5)
```

The second condition is the stable factorization `ell=T^*g`; it is strictly stronger unless the
relevant range is closed.  This is the rank-one case of R. G. Douglas,
[*On majorization, factorization, and range inclusion of operators on Hilbert
space*](https://www.ams.org/journals/proc/1966-017-02/S0002-9939-1966-0203464-1/),
Proc. AMS 17 (1966), 413--415.  Thus `(CE18)` must be upgraded from kernel inclusion to actual
adjoint-range membership with polynomial factor norm.

Among all scalar graphs, the unique pointwise and Loewner minimizer is

```text
ell_opt(F)=-a^(-1)<s,T(F)>=-D(F)/a.                      (CA6)
```

It is forbidden because it reads the evaluated defect.  Even it leaves `(CA3)` unchanged.  A
quotient by `ker T` is no repair: `T` descends, but the pointed trace does not, since `(CF11)` gives
`ell(ker T)=C`.  Choosing a splitting can manufacture any trace functional on `range(T)` and in
particular can manufacture `(CA6)`; the quotient canonically remembers none.

Reciprocal rescaling also only trades costs.  If

```text
P_r(t,F)=r t s+r^(-1)b_F,
b_F=(D(F)/a)s+b_F^perp,
```

then

```text
||P_r(t,F)||^2
 =a|r t+r^(-1)D(F)/a|^2+r^(-2)||b_F^perp||^2
 =a r^2|t|^2+r^(-2)||b_F||^2+2Re(conj(t)D(F)).           (CA7)
```

Suppressing the unit row blows every pure-curvature row.  In a source whose effective curvature
range has dimension greater than the scalar trace range, such a transverse direction necessarily
remains.  If the effective range is one-dimensional, the construction has collapsed
observationally to the forbidden evaluated-defect line.  Choosing `r` from `D(F)` or `||b_F||` on
the distinguished vector is line-tailoring, not a source theorem.

### The signed Clark primitive has an exact raw-tail/mean-zero dichotomy

There is nevertheless one exact way in which the Möbius product fibres enter the whole Clark
circle before a norm is chosen.  For the Fourier coefficients `(CF1)`, define the principal-value
sequence

```text
b_r(F)=PV integral_R F(y)(m(y)-i)conj(theta(y))^rdy.     (CM1)
```

The Cayley identity alone gives

```text
b_r(F)-b_(r+1)(F)=-2i a_r(F).                            (CM2)
```

For the exact tents `a_r=O((1+|r|)^(-2))`.  With the principal-value normalization in `(CM1)`,

```text
b_r=-2i sum_(k>=r)a_k,
lim_(r->+infinity)b_r=0,
lim_(r->-infinity)b_r=-2i S_F(0).                       (CM3)
```

Thus `b` is not in ordinary `ell^2(Z)` whenever the prime Clark trace is nonzero.  Retaining its
one-sided constant tail retains the raw prime port.

Subtracting that tail gives

```text
c_r=b_r+2i S_F(0)1_(r<=0),
c_0-c_1=2iD(F).                                         (CM4)
```

The renormalized sequence is in `ell^2` for the exact tents.  More precisely, if

```text
C_F(beta)=sum_r c_r exp(ir beta),
```

then

```text
C_F(beta)=2i[S_F(0)-S_F(beta)]/[1-exp(-i beta)],         (CM5)

sum_r|c_r|^2
 =4integral_0^(2pi)
   |S_F(beta)-S_F(0)|^2/|1-exp(-i beta)|^2
   d beta/(2pi).                                        (CM6)
```

This is an exact anchored half-Sobolev divided-difference norm: a pure mode of frequency `k` has
squared cost `4|k|`.  It is a genuine endpoint improvement over the translation-invariant
diagonal family `(CF3)`.  It is not a pointed solution.  Its kernel is exactly the class for which
`S_F` is constant, including `(CF11)`; the tail subtraction has forgotten the raw trace needed to
define the source point.  Keeping the tail restores that trace and destroys the unweighted Hilbert
completion.

Substituting the signed ordinary-product resolution of `Lambda` into `(CE1)` gives the explicit
product-fibre form

```text
b_r(F)=-i a_r(F)
 +(2/pi)sum_(d,k>=1)mu(d)log(k)/sqrt(dk)
   PV integral_R
    [y F(y)conj(theta(y))^r]/[y_(dk)^2-y^2]dy.           (CM7)
```

For compact tests the tail of the double sum is absolutely convergent; only the finitely many
in-support poles require principal values.  Equation `(CM7)` retains the Möbius signs through the
resolvent correlation.  But the phase `theta` is already the scalar phase of the collapsed positive
prime measure, and `(CM3)` shows exactly where its product signs terminate: either in the raw Clark
trace or in the mean-zero quotient `(CM5)`.

### Positive operator-valued Clark lifting cannot preserve the missing cancellation

The preceding dichotomy is forced by positivity, not by choosing scalar Clark theory.  Suppose a
positive operator-valued Herglotz measure retains each product label `(d,k)` as a separate atom and
uses a two-port compression whose off-diagonal coefficient is

```text
r_(d,k)=mu(d)log(k)/sqrt(dk).
```

Positivity of each compressed atom `W_(d,k)` implies

```text
trace(W_(d,k))>=2|r_(d,k)|.                              (CP1)
```

Therefore positivity **before** `dk=n` pays

```text
sum_(dk<=X)|mu(d)|log(k)/sqrt(dk)
 >>sqrt(X)log X,                                         (CP2)
```

already from the `d=1`, `X/2<=k<=X` slice.  If the product labels are first collapsed at the same
scalar node, the positive aggregate atom `W_n` has off-diagonal
`q_n=Lambda(n)/sqrt(n)`, and hence

```text
trace(W_n)>=2q_n,
sum_(n<=X)trace(W_n)>>sqrt(X).                           (CP3)
```

This is exactly the raw scalar Clark/GNS mass.  Hence a positive operator-valued lift has only two
possibilities: Jordanize the Möbius fibres before product collapse and pay `(CP2)`, or collapse
them first and return to `(CP3)`.  An indefinite homological cancellation can evade `(CP1)`, but
then it is not a Herglotz/Clark positive measure until after the missing signed source differential
has already done the work.

### Hostile verdict and final surviving theorem

`[PAPER-PROVED] [BRIDGE]` The Hermite identities `(CH1)`--`(CH10)`, block decomposition
`(CA1)`--`(CA7)`, and signed Clark primitive `(CM1)`--`(CM7)` sharpen the carrier without using
zero data or numerical evidence.

`[FALSIFIED]` Cellwise positive Hermite energy, node-jet control of whole cells, algebraic kernel
inclusion by itself, a quotient or complement of the phase-partition kernel, reciprocal scalar
rescaling, a scalar trace graph on a genuinely multidimensional curvature range, and a positive
operator-valued Möbius--Clark lift.

`[RETIRED AS A PRODUCER]` Clark/Herglotz positivity.  The Clark fold remains an exact coordinate
and diagnostic after signed arithmetic sewing; it does not create that sewing.

`[OPEN CORE]` Define, before evaluating `D`, a coherent signed product-fibre differential and
source trace

```text
d_J:E_J->X_J,                    eta_J:E_J->ell^2(block),
```

with uniformly bounded distinguished sections and effective curvature quotient of dimension
greater than one, and prove the two separate estimates

```text
||Q mathcalT_J d_J||^2 <<(1+J)^A,                       (CO1)
||eta_J+a^(-1)S^*mathcalT_Jd_J||^2 <<(1+J)^A.           (CO2)
```

The first is a signed equal-phase cross-cell/cross-aperture correlation theorem.  The second is a
product-fibre Stokes law tying the pointed polar trace to that curvature.  Together they are
equivalent to the admissible Clark provider for `(C4)`; separately neither implies RH.  This
nonpositive source differential, not another phase identity or positive completion, is the exact
remaining construction.

## 2026-07-18 divided-difference and arithmetic-martingale closure

### The renormalized Clark primitive is a rank-one divided difference `[PAPER-PROVED] [BRIDGE]`

The norm `(CM6)` has an exact operator-theoretic classification.  Put `z=exp(i beta)`, let
`U=M_z` on `L2(T)`, let `V=1` on `C`, and let `J lambda=lambda 1`.  For

```text
D_1S(z)=[S(z)-S(1)]/(z-1),
X_S lambda=lambda D_1S,
```

equation `(CM5)` becomes

```text
C_F(z)=-2iz D_1S_F(z),
sum_r|c_r(F)|^2=4||D_1S_F||_2^2=4||X_(S_F)||_(S_2)^2.   (CD1)
```

The column `X_S` solves the rank-one Sylvester equation

```text
U X_S-X_S V=S(U)J-JS(V).                                (CD2)
```

For `S(z)=sum_k a_kz^k`, its two boundary tails are explicit:

```text
D_1S(z)
 =sum_(r>=0)(sum_(k>=r+1)a_k)z^r
  -sum_(r>=1)(sum_(k>=r)a_(-k))z^(-r),                  (CD3)

||D_1S||_2^2
 =sum_(m,n>=1)min(m,n)
   [a_m conj(a_n)+a_(-m)conj(a_(-n))].                  (CD4)
```

Thus the signed Clark primitive is precisely a one-column double-operator-integral/divided-
difference object.  It is not a standard Hankel Schatten norm: the cumulative-tail vector is a
boundary vector outside `ell2`, and a finite cutoff pays its length.  Known divided-difference
estimates would assume a stronger Besov/operator-Lipschitz or two-weight Clark estimate; they do
not prove `(CO1)`.  Restoring the raw Clark term repairs the constant kernel only by restoring the
non-`ell2` trace.  This operator language therefore classifies `(CM4)`--`(CM6)` but supplies no new
source estimate.

### The likelihood-ratio Doob differential is an exact finite signed producer

There is a canonical nonpositive arithmetic differential before Clark positivity.  Let

```text
P_N={p_1<...<p_m: p_j<=N},                 Omega_N={0,1}^(P_N),
Z_N=W_N(1)=sum_nw_N(n),                    c_N=C_Lsqrt(N).
```

Push the probability `w_N(n)/Z_N` forward by
`n |-> (1_(p|n))_(p in P_N)` and call the resulting law `mu_N`.  Let

```text
nu_N=product_(p in P_N) Bernoulli(1/p),
L_N=dmu_N/dnu_N,
F_j=sigma(omega_(p_1),...,omega_(p_j)),
D_j=E_nu[L_N|F_j]-E_nu[L_N|F_(j-1)],
(G_Nf)_j=E_nu[f|F_j]-E_nu[f|F_(j-1)].                  (MD1)
```

Every atom of `nu_N` is positive, so all terms are finite and source-defined.  Orthogonal
martingale differences give the exact integration-by-parts law

```text
G_N^*(D_j)_j=L_N-1,
<D,G_Nf>=E_(mu_N)f-E_(nu_N)f,
||G_Nf||^2=Var_(nu_N)(f).                               (MD2)
```

The edge current retains inclusion--exclusion signs before any square.  For a prefix atom
`A subset {p_i:i<j}`, write `q_A=product_(p in A)p` and

```text
v_(j-1)(A)=q_A^(-1) product_(r<p_j,r notin A)(1-1/r),

M_(j-1)(A)=Z_N^(-1)
 sum_(T subset {r<p_j:r notin A})(-1)^|T| W_N(q_(A union T)),

M_j^+(A)=Z_N^(-1)
 sum_T(-1)^|T| W_N(p_jq_(A union T)),

J_(N,j)(A)=M_j^+(A)-p_j^(-1)M_(j-1)(A).                (MD3)
```

On that prefix atom, with `theta_j=1/p_j`,

```text
D_j(omega)
 =[J_(N,j)(A)/(v_(j-1)(A)theta_j(1-theta_j))]
   (omega_(p_j)-theta_j),

||D_j||_2^2
 =sum_A |J_(N,j)(A)|^2/[v_(j-1)(A)theta_j(1-theta_j)]. (MD4)
```

For the sharp uniform aperture, `(MD3)` contains the literal signed residue

```text
p floor(X/(pq))-floor(X/q)=-(floor(X/q) mod p).         (MD5)
```

For the moving tent the continuum character cancels and `(SF1)` gives

```text
J_(N,j)(A)=Z_N^(-1) integral_0^infinity
 sum_T(-1)^|T|
  [{t/(p_jq_(A union T))}-p_j^(-1){t/q_(A union T)}]
 w_N'(t)dt.                                             (MD6)
```

This is the exact weighted Möbius/floor current sought after `(C6)`.

To see its polar seam, let `D_N` be the squarefree `d<=N`, put
`chi_d(omega)=product_(p|d)omega_p`, and for a coefficient matrix `x=(x_(d,e))` define

```text
F_x(omega)=sum_(d,e in D_N)x_(d,e)log(gcd(d,e))
             chi_(lcm(d,e))(omega).                     (MD7)
```

For `x_(d,e)=conj(a_d)a_e` this is a marked-incidence square.  Its two exact expectations are

```text
E_nu F_x
 =sum_(d,e)x_(d,e)log(gcd(d,e))/lcm(d,e),

E_mu F_x
 =Z_N^(-1)sum_(d,e)x_(d,e)log(gcd(d,e))
   W_N(lcm(d,e)).                                       (MD8)
```

At the Möbius matrix `x^mu_(d,e)=mu(d)mu(e)`, the second line is `T_L(N)/Z_N`.  On

```text
K_N=C direct_sum (direct_sum_j H_j),
s_N=(1,D),
mathcalT_N(alpha,x)=(E_nu F_x-alpha,G_NF_x),
```

one therefore has the source-defined Stokes identity

```text
<s_N,mathcalT_N(alpha,x)>=E_mu F_x-alpha.                (MD9)
```

No value or sign of `E_L(N)` occurs in the definition.  In particular

```text
Gamma_(N,+/-)(t,alpha,x)
 =(1/2)sqrt(Z_N/c_N)[t s_N +/- mathcalT_N(alpha,x)]
```

satisfies

```text
||Gamma_(N,+)||^2-||Gamma_(N,-)||^2
 =(Z_N/c_N)Re(conj(t)[E_mu F_x-alpha]).                 (MD10)
```

Taking `t=1`, `alpha=c_N/Z_N`, and `x=x^mu` gives exactly

```text
c_N(||Gamma_(N,+)||^2-||Gamma_(N,-)||^2)=T_L(N)-c_N.   (MD11)
```

This is a genuine finite-level off-diagonal signed producer on a source larger than the defect
line.  It is the exact weighted specialization of standard likelihood-ratio/Doob and Kubilius
geometry, not new science.  It also does not yet give a cofinal norm for which the Möbius matrix is
a uniformly bounded distinguished section.

### The full Doob positive completion fails transversely on one fixed prime

Fix a prime `q`.  Put `x^(q)_(q,q)=1/log(q)` and all its other entries zero, so that
`F_(x^(q))=chi_q`.  With `alpha=1/q`,

```text
mathcalT_N(1/q,x^(q))=(0,G_Nchi_q),
||G_Nchi_q||^2=q^(-1)(1-q^(-1)).                        (MD12)
```

Also `(SF1)` at `q=1` gives

```text
Z_N=c_N+O_L(N^(-1/2)).                                  (MD13)
```

Consequently even the `t=0` positive output obeys

```text
sum_(exp(J)<=N<exp(J+1))(c_N/N)
 ||Gamma_(N,+)(0,1/q,x^(q))||^2
 asymp_(L,q) exp(J/2).                                  (MD14)
```

The longitudinal projection cannot hide this.  With

```text
a_N=||s_N||^2=1+chi^2(mu_N||nu_N),
Q_N^Doob=I-(s_N tensor s_N)/a_N,
Delta_N(q)=W_N(q)/Z_N-1/q=O_(L,q)(N^(-1)),
```

one has exactly

```text
||Q_N^Doob mathcalT_N(1/q,x^(q))||^2
 =q^(-1)(1-q^(-1))-|Delta_N(q)|^2/a_N.                 (MD15)
```

Thus the transverse channel remains bounded below.  On the distinguished source, the unique
longitudinal minimizer is

```text
t_opt=-E_L(N)/(Z_Na_N),                                 (MD16)
```

which again reads the evaluated completed error.  The Doob differential closes the finite signed
Stokes identity, but its natural positive completion proves neither `(CO1)` nor `(CO2)`.

### Centered multiplicative jets shrink, but their von Mangoldt dual does not

The same differential has a flat Koszul form.  For a finite prime set `P`, define

```text
(T_pf)(q)=f(pq),                  D_p=T_p-p^(-1)I,
D_B=product_(p in B)D_p.
```

The `D_p` commute, their oriented cubical Koszul differential squares to zero, and multiplication
by `q_(A union B)` gauges it to the ordinary cubical differential.  Hence the finite complex has

```text
H^0=C(q_A |-> q_A^(-1)),             H^k=0 for k>0.     (KW1)
```

It is a flat, contractible local system rather than a new curvature class.  Its exact floor jet is

```text
D_p floor(t/q)=-{floor(t/q)/p},

D_B floor(t/q)
 =sum_(n<=t)product_(p in B)(1_(p|n)-1/p).              (KW2)
```

Writing `TV(w_N)=V_L/sqrt(N)`, the normalized centered moments

```text
delta_B(N)=D_BW_N(1)/c_N
```

satisfy, for every nonempty `B` and `p_0 in B`,

```text
|delta_B(N)|
 <=[V_L/(C_LN)] product_(p in B minus {p_0})(1+1/p).   (KW3)
```

The decay in `(KW3)` has an exact cross-aperture explanation.  Put

```text
z_L(X)=W_X(1)/c_X,                    (R_pz)(X)=z(X/p).
```

The weight covariance `(WS1)` gives

```text
W_N(q)/c_N=q^(-1)z_L(N/q),                            (KW3a)

delta_B(N)=q_B^(-1)product_(p in B)(R_p-I)z_L(N).      (KW3b)
```

Thus every centered multiplicative jet is already a horizontal aperture coboundary of the scalar
lattice-normalization error `z_L-1=O_L(N^(-1))`.  Its smallness is real but elementary.  The
arithmetic difficulty is entirely in applying the simultaneous marked-singleton trace to this
weak current.

The weak signed-current norm genuinely shrinks:

```text
||delta(N)||_w^2
 =sum_(empty!=B subset P_N)q_B^(-1)|delta_B(N)|^2
 <<_L log(N)/N^2,                                       (KW4)

sum_(N asymp exp(J))(c_N/N)||delta(N)||_w^2
 <<_L J exp(-3J/2).                                     (KW5)
```

The missing Stokes trace lies in the dual geometry.  With `r_p=1/p`, `s_p=1-r_p`,
`Q_0=product_p s_p`, and

```text
phi_B(omega)=product_(p in B)(omega_p-r_p),

F_Lambda(omega)=sum_p log(p)omega_p
                  product_(r!=p)(1-omega_r),
```

the exact Walsh expansion `F_Lambda=sum_B tau_Bphi_B` has

```text
tau_B=Q_0(-1)^|B|[product_(p in B)s_p]^(-1)
 [sum_p log(p)/(p-1)-sum_(p in B)p log(p)/(p-1)],       (KW6)

tau_(P_N)=(-1)^(|P_N|+1)log(q_(P_N)).                   (KW7)
```

The top coefficient shows that the canonical full-cube extension is enormous in the dual norm
`sum_Bq_B|tau_B|^2`.  This is not an artifact of impossible Boolean patterns.  For an arbitrary
extension `G=sum_Bgamma_Bphi_B`, set

```text
L_pG=G({p})-G(empty),                    K_P=product_(q in P)(1+q^(-3)).
```

The Gram matrix of the `L_p` in the weak dual geometry is

```text
G_(p,p)=K_P [p^(-1)/(1+p^(-3))],
G_(p,r)=K_P [p^(-2)r^(-2)/((1+p^(-3))(1+r^(-3)))]      (KW8)
```

for `p!=r`.  Sherman--Morrison gives, for constraints `L_pG=y_p` on `I subset P`,

```text
min ||gamma||_(w,*)^2
 =K_P^(-1)[
   sum_(p in I)p(1+p^(-3))^2|y_p|^2
   -|sum_(p in I)y_pp^(-1)(1+p^(-3))|^2/
      (1+sum_(p in I)p^(-3))].                         (KW9)
```

It follows uniformly that

```text
min ||gamma||_(w,*)^2 >=c sum_(p in I)p|y_p|^2.        (KW10)
```

Take `I` to be the primes in any fixed compact subinterval of the tent support.  Any
source-local observable agreeing with `Lambda` on genuine integer patterns has, after an
irrelevant constant/polar adjustment, `y_p=log p` there.  The prime number theorem and partial
summation then give

```text
||gamma||_(w,*)^2 >>_L N^2log N.                        (KW11)
```

Therefore normalizing the distinguished source consumes the full `N sqrt(log N)` dual cost and
erases the `N^(-1)` gain in `(KW4)`.  The result persists under arbitrary changes off the
arithmetic patterns.

Strengthening to the Bernoulli/chi-square norm repairs trace continuity but restores positive
aperture mass.  If `rho_N=dmu_N/dnu_N`, the empty Bernoulli pattern has mass

```text
Q_0=product_(p<=N)(1-1/p) asymp 1/log N,
```

whereas it is absent from the moving tent for large `N`.  Hence

```text
||rho_N-1||_(L2(nu_N))^2>=Q_0,

sum_(N asymp exp(J))(c_N/N)||rho_N-1||_2^2
 >>_L exp(J/2)/J.                                      (KW12)
```

The weak completion makes curvature small but the von Mangoldt trace discontinuous at exactly
the compensating scale; the strong completion controls the trace but restores exponential block
mass.  No fibrewise diagonal Koszul/Fock completion meets both gates.

### The independent-prime literature does not supply the missing cofinal estimate

The limitation is visible in the strongest relevant primary results.

- Tenenbaum's exact Kubilius total-variation theorem has a positive limit for a fixed
  `u=log(x)/log(y)`; decay requires `u->infinity`.  Polynomial decay is available for a
  polylogarithmic prime cutoff, not for `y=x^beta` or the full cofinal prime window
  ([Theorem 1](https://tenenb.perso.math.cnrs.fr/PPP/EK.pdf)).
- Chen--Jaramillo--Yang require
  `rho_N=log(N)/log|Gamma_N| -> infinity`; their exponential total-variation bound therefore
  covers `|Gamma_N|=N^o(1)` and excludes all primes up to `N`
  ([Theorem 1.5](https://alea.impa.br/articles/v20/20-27.pdf)).
- Arratia's optimal full-prime multiplicity coupling has insertion/deletion distance tending to
  `2`, not to zero ([Theorem 3](https://arxiv.org/abs/1305.0941)).  For the indicator projection,
  the independent Bernoulli radical has the same scale-invariant Dickman limit, while every
  actual integer `n<=N` has `rad(n)<=N`.  Hence the full indicator total-variation distance has
  the unconditional lower limit

```text
liminf TV >=Prob(T>1)=1-exp(-gamma)>0.                  (KW13)
```

  This follows from the Arratia--Barbour--Tavare scale-invariant limit
  ([primary paper](https://www.columbia.edu/cu/simontavare/STpapers-pdf/ABT97.pdf)).

These are static probability bounds for bounded observables, not cross-aperture Hilbert-operator
estimates.  They become relevant only after a new source-defined compression theorem has removed
the high-prime tail.

### Hostile verdict and sharpened survivor

`[PAPER-PROVED] [REDISCOVERED BRIDGE]` The likelihood-ratio martingale gives the first explicit
finite signed arithmetic--polar sewing in this route.  The centered dilation/Koszul jet kills the
flat `1/q` character and has the genuinely shrinking estimate `(KW4)`--`(KW5)`.

`[FALSIFIED]` The full Doob positive port, its longitudinal projection, a weak diagonal Walsh/Fock
completion, a strong Bernoulli/chi-square completion, and modification of the observable only on
impossible Boolean patterns.

`[LITERATURE NO-GO]` Existing Kubilius, Stein, Feller, scale-invariant, and independent-prime
couplings do not cover the cofinal all-prime weighted operator norm.  Their sparse-prime estimates
may be used only after an independent tail theorem.

`[OPEN CORE]` Construct a signed **non-diagonal-in-aperture** Stokes operator which turns the
persistent marked-singleton/fixed-ideal trace into a bounded horizontal aperture coboundary before
any positive norm is formed, while retaining the shrinking current `(KW4)`.  It must reconstruct the marked
von Mangoldt trace on a uniformly bounded source without imposing the simultaneous per-aperture
singleton interpolation cost `(KW11)`, and it must prove the already-separated estimates
`(CO1)`--`(CO2)`.  Any direct sum of independent finite-aperture Doob/Koszul/Fock norms is now
ruled out.

## 2026-07-18 Buchstab scale filtration and the balanced Type-II obstruction

### The centered Buchstab differential is exact `[PAPER-PROVED] [BRIDGE]`

Put

```text
a_N(n)=w_(N,L)(n)log(n),
S_N(z)=sum_(P^-(n)>=z)a_N(n),              P^-(1)=infinity.
```

Assigning each `y`-rough but non-`z`-rough integer to its unique smallest prime gives

```text
S_N(y)-S_N(z)
 =sum_(y<=p<z) B_(N,p),

B_(N,p)=sum_(P^-(m)>=p)a_N(pm).                          (BU1)
```

Let `V(z)=product_(p<z)(1-1/p)`.  At a prime jump,

```text
S_N(p^+)/V(p^+)-S_N(p)/V(p)
 =[S_N(p)/p-B_(N,p)]/V(p^+).                            (BU2)
```

Consequently

```text
S_N(z)/V(z)-S_N(y)/V(y)
 =sum_(y<=p<z)[S_N(p)/p-B_(N,p)]/V(p^+).                (BU3)
```

Equation `(BU3)` is the canonical centered Bernoulli/Buchstab source differential.  It annihilates
the independent `1/p` branch, retains the signed floor discrepancy, and makes every fixed-prime
increment `O_(L,p)(N^(-1/2)log N)`.

It is invariant under every multiscale schedule.  If

```text
z_0<z_1<...<z_r=sqrt(N),
```

then

```text
S_N(z_0)-S_N(sqrt(N))
 =sum_i sum_(z_i<=p<z_(i+1))B_(N,p).                    (BU4)
```

Changing `u_i=log(N)/log(z_i)` only regroups the same unique-smallest-prime branches.

For large `N`, the tent support lies above `sqrt(N)`, and hence

```text
S_N(sqrt(N))=sum_p w_(N,L)(p)log(p),
T_L(N)-S_N(sqrt(N))=O_L(1).                             (BU5)
```

The second line follows because the square contribution is bounded by
`sum_(p<=x)log(p)/p=log(x)+O(1)` on a fixed-ratio interval, while powers of exponent at least three
are smaller.  Thus the terminal Buchstab trace really is the von Mangoldt singleton port up to a
bounded prime-power edge.

### A balanced semiprime chamber survives every regrouping

Choose a closed inner interval `[alpha_LN,beta_LN]` on which the tent profile is bounded below and
put

```text
mathcalB_N=sum a_N(pq),
```

where the sum is over primes satisfying

```text
N^(1/3)<=p<=N^(2/5),              alpha_LN<=pq<=beta_LN.
```

Here `p` is the unique smallest-prime branch label.  The prime number theorem uniformly on the
fixed-ratio `q` intervals and Mertens' prime-reciprocal law give

```text
#{(p,q)} asymp_L N/log N,
a_N(pq) asymp_L log(N)/sqrt(N),
mathcalB_N asymp_L sqrt(N).                             (BU6)
```

This positive mass is unchanged by `(BU4)`.  Any completion which makes the branch labels
positive before their signed collapse therefore has normalized energy bounded below, and

```text
sum_(exp(J)<=N<exp(J+1))(c_N/N)[mathcalB_N/c_N]
 asymp_L exp(J/2).                                      (BU7)
```

Collapsing the labels first returns `(BU5)` and hence the original prime trace.

### The fundamental lemma cannot reach the cofinal scale

For the weighted divisibility sums

```text
A_(N,d)=sum_(d|n)a_N(n)=X_N/d+r_(N,d),
```

bounded-variation quadrature gives

```text
X_N asymp_L sqrt(N)log N,
r_(N,d)=O_L(log(N)/sqrt(N)).                            (BU8)
```

A Rosser fundamental-lemma truncation at level `D` therefore pays

```text
sum_(d<D)|r_(N,d)| <<_L D log(N)/sqrt(N).               (BU9)
```

An absolute polylogarithmic budget forces `D<=sqrt(N)polylog(N)`.  If `z=N^alpha`, its sieve
parameter satisfies

```text
s=log(D)/log(z)<=1/(2alpha)+o(1),                       (BU10)
```

so the fundamental-lemma relative error remains at a fixed nonzero scale while
`X_NV(z) asymp_alpha sqrt(N)`.  Taking `z=N^o(1)` makes the small-prime error shrink but leaves the
balanced chamber `(BU6)` untouched.

This is the classical parity boundary in an exact aperture form.  Friedlander--Iwaniec exhibit a
Selberg sequence with excellent ordinary sieve remainders but no prime values, showing that a
Möbius-sensitive bilinear axiom is additionally necessary
([*Asymptotic sieve for primes*](https://arxiv.org/abs/math/9811186)).  Ford--Maynard prove that a
substantial Type-II range is necessary for any nontrivial prime lower bound; their optimal sieve
uses Type-I and Type-II information together rather than obtaining it from an iterated Buchstab
schedule
([*On the theory of prime-producing sieves*](https://arxiv.org/abs/2407.14368)).

### Hostile verdict

`[PAPER-PROVED] [BRIDGE]` Equations `(BU1)`--`(BU5)` give an exact centered Buchstab differential
and reconstruct the singleton trace.

`[FALSIFIED]` A varying Buchstab threshold, an iterated fundamental-lemma approximation, or a
positive completion of the least-prime branches.  The first two only regroup or approximate the
same branches; the third pays `(BU7)` on a balanced semiprime chamber.

`[POSITIVE SALVAGE]` Buchstab theory locates the first unavoidable bilinear chamber.  It does not
estimate its Möbius-oriented cross-aperture current.

`[OPEN CORE]` Prove an independently sourced, nonpositive **Type-II aperture Stokes law** on the
balanced product region `p asymp N^theta`, `q asymp N^(1-theta)` for a fixed interior range such as
`1/3<=theta<=2/5`.  It must turn the persistent singleton trace into a horizontal aperture
coboundary before branchwise positivity and meet `(CO1)`--`(CO2)`.  This is a more concrete name
for the remaining signed product-fibre theorem; ordinary Buchstab or fundamental-lemma input does
not imply it.

## 2026-07-18 harmonic-floor aperture mapping cone, null gauge, and moving front

### The all-face Euler--Koszul Stokes law is exact `[PAPER-PROVED] [REDISCOVERED BRIDGE]`

Normalize the tent by

```text
kappa_L(X)=h_L(log X)/(C_L sqrt(X)),
z_L(X)=W_X(1)/c_X=sum_(m>=1)m^(-1)kappa_L(X/m),
(R_df)(X)=f(X/d).
```

The multiplicative aperture covariance is

```text
W_N(d)/c_N=d^(-1)(R_dz_L)(N).                            (AB1)
```

On functions of the aperture define the Euler--Koszul operator

```text
K_s=product_p(1-p^(-s)R_p)
   =sum_d mu(d)d^(-s)R_d.
```

Every evaluation on `z_L` is finite.  Differentiating the finite evaluation at `s=1` gives

```text
K'_1=-sum_d mu(d)log(d)d^(-1)R_d
    =sum_p log(p)p^(-1)R_p product_(q!=p)(1-q^(-1)R_q),

(K'_1z_L)(N)
 =sum_n Lambda(n)n^(-1)kappa_L(N/n)
 =T_L(N)/c_N.                                           (AB2)
```

Thus the all-face differential already retains the von Mangoldt singleton trace across apertures;
it does not interpolate that trace separately at every cutoff.  The formal infinite relation
`K_s1=1/zeta(s)` would have right derivative `1` at `s=1`, but its finite-aperture boundary is

```text
T_L(N)/c_N-1
 =-sum_(d<=N)mu(d)log(d)d^(-1)(z_L(N/d)-1)
  +[-sum_(d<=N)mu(d)log(d)d^(-1)-1].                    (AB3)
```

The bracket is not a reduced horizontal coboundary.  Replacing it by the formal infinite Euler
product would insert the missing boundary value rather than prove it.

The exact harmonic-floor mapping cone makes the obstruction canonical.  In `ell2(d>=1)` put

```text
u_d=mu(d)/d,                 a_d=-mu(d)log(d)/d,
H_N(d)=Harmonic(floor(N/d)),
v_n(d)=Harmonic(floor(n/d))-Harmonic(floor((n-1)/d))
      =(d/n)1_(d|n).
```

The live formal corpus proves

```text
<u,H_N>=1,
<a,v_n>=Lambda(n)/n.                                    (AB4)
```

These are respectively `harmonicFloorMoebiusSum_eq_one`, `harmonicFloor_succ_sub`, and
`harmonicFloorMoebiusLog_succ_sub_eq_vonMangoldt` in
`formal/GaloisForLFunctions/RHTower/Mollifier.lean`.  With

```text
V_N=sum_n kappa_L(N/n)v_n,
```

one obtains, without a limit,

```text
V_N(d)=z_L(N/d),
<a,V_N>=T_L(N)/c_N,
<u,V_N>=kappa_L(N)=0                 (N>exp(2L)).         (AB5)
```

Let `M_log` denote multiplication by `log d`; then `a=-M_log u`.  Equations `(AB4)`--`(AB5)`
therefore give the exact signed mapping-cone defect

```text
1-T_L(N)/c_N
 =<u,H_N+M_log V_N>
 =<u,H_N+(M_log-log N)V_N>.                             (AB6)
```

The second equality is the source-defined polar centering; it uses only `<u,V_N>=0`, not the value
or sign of the completed error.

### The constant tail has a null gauge; the moving front does not

The centered vector in `(AB6)` has coordinate

```text
G_N(d)=Harmonic(floor x)-log(x)z_L(x),       x=N/d.
```

Since `z_L(x)=1+O_L(x^(-1))` and
`Harmonic(floor x)=log x+gamma+O(x^(-1))`, write

```text
G(x)=gamma+r_L(x),
|r_L(x)|<<_L(1+log x)/x.                                 (AB7)
```

Then `(AB6)` is exactly

```text
1-T_L(N)/c_N
 =gamma M_1(N)+sum_(d<=N)mu(d)d^(-1)r_L(N/d),
M_1(N)=sum_(d<=N)mu(d)/d.                                (AB8)
```

The displayed Mertens term is a valid decomposition, but it is not gauge-invariant.  Möbius
inversion and `(AB5)` also give

```text
sum_(d<=N)mu(d)d^(-1)z_L(N/d)=kappa_L(N)=0
                                                    (N>exp(2L)). (AB8a)
```

Consequently one may subtract the source-null vector `gamma V_N` in `(AB6)` and obtain the
strictly stronger representative

```text
1-T_L(N)/c_N=sum_(d<=N)mu(d)d^(-1)q_L(N/d),
q_L(x)=Harmonic(floor x)-(log x+gamma)z_L(x),
|q_L(x)|<<_L(1+log x)/x.                                (AB8b)
```

This correction is essential: `gamma M_1(N)` is not by itself a canonical obstruction on the
distinguished Möbius line.  The null gauge moves its constant tail into the transition region where
`z_L` turns on.

For a fixed prime let

```text
(mathcalH_pf)(x)=sum_(k>=1)f(p^kx).
```

On the decay class containing `r_L` and `q_L`, the series converges and telescopes to

```text
(R_p-I)mathcalH_pf=f,
mathcalH_p(R_p-I)f=f.                                   (AB9)
```

Thus every fixed-prime reduced horizontal aperture difference is contractible on the decaying
lattice current.  The apparent constant cohomology class in `(AB8)` can be gauged away on the
distinguished line by `(AB8a)`.  What the homotopy does not contract uniformly is the moving finite
divisor front `d asymp N`: there `x=N/d` remains in a fixed compact interval and `q_L(x)` is of fixed
size.  Moreover, subtracting `gamma V_N` is null only under the distinguished Möbius functional;
on the larger source module required by `(C4)` it creates the rank-one row `<source,V_N>`.  Declaring
that row null would again define the source quotient from the distinguished section.

The norm trade localizes the same front.  For
`Q_N(d)=q_L(N/d)`, the source vectors `u` and `a` have uniformly bounded unweighted norm, while

```text
||Q_N||_2^2 asymp_L N.                                  (AB10)
```

Indeed `Q_N(d)` stays bounded away from zero on a positive proportion of `d` near `N`, despite its
decay for `d=o(N)`.  In the reciprocal norm `sum_d|x_d|^2/d`, its norm square is `asymp_L 1`, while
the dual norm squares of `u` and `a` grow respectively like `log N` and `(log N)^3`.  Even this
improved null-gauge rebalance pays

```text
sum_(N asymp exp(J))(c_N/N)||Q_N||_(1/d)^2
 asymp_L exp(J/2).                                      (AB11)
```

Fixed-prime and balanced-face tests show both sides of the classification:

```text
(R_p-I)z_L(N)=O_L(p/N),
p^(-1)(R_p-I)z_L(p)=-p^(-1)+O_L(p^(-2)),
(R_p-I)(R_q-I)z_L(pq)->-1                 (p,q->infinity). (AB12)
```

The reduced complex genuinely kills persistent fixed-prime modes.  The moving singleton front and
balanced Type-II face remain boundary atoms and cancel only in the signed all-face sum.  Norming
the faces separately pays `(BU7)`; collapsing them first gives `(AB2)`.  The null gauge `(AB8b)`
shows that the remaining scalar difficulty is a high-divisor moving-front convolution, not a bare
constant `M_1` term.

### Exact half-density localization to the moving Möbius front

The null-gauged scalar has a canonical half-density form.  For `0<t<=1` define, without reusing the
tent kernel `kappa_L`,

```text
vartheta_L(t)=t^(-1)q_L(t^(-1)).
```

Equation `(AB8b)` becomes

```text
mathcalM_L(N):=sqrt(N)(1-f_L(N))
 =N^(-1/2)sum_(d<=N)mu(d)vartheta_L(d/N),
vartheta_L(t)=O_L(1+|log t|).                            (MF1)
```

Since `E_L(N)=c_N(f_L(N)-1)`, this fixes every sign and normalization:

```text
E_L(N)^+=C_L mathcalM_L(N)^-,
sum_(N asymp X)E_L(N)^+/N
 =C_Lsum_(N asymp X)mathcalM_L(N)^-/N.                  (MF2)
```

Thus the invariant scalar father is a one-sided logarithmic mean of a normalized, smoothly
weighted moving-front Möbius sum.

There is also an exact renewal classification.  On functions extended by zero to `x<1`, put

```text
(mathsfA f)(x)=sum_(d<=x)mu(d)d^(-1)f(x/d),
(mathsfB f)(x)=sum_(m<=x)m^(-1)f(x/m).
```

Finite regrouping and `sum_(d|n)mu(d)=1_(n=1)` give

```text
mathsfA mathsfB=mathsfB mathsfA=I.                       (MF3)
```

If `Delta_L=mathsfAq_L`, then for every real `x>=1`, including the small-aperture correction,

```text
Delta_L(x)=1-(log x+gamma)kappa_L(x)-f_L(x),
mathsfB Delta_L=q_L,
Delta_L(x)=q_L(x)-sum_(2<=m<=x)m^(-1)Delta_L(x/m).       (MF4)
```

For `x>exp(2L)`, `Delta_L(x)=1-f_L(x)`.  The recurrence is not a contraction:
`sum_(2<=m<=x)1/m` grows, and separating its two signs only couples the two unknown Jordan parts.
Iteration recreates Möbius inversion.

The decay in `(AB8b)` nevertheless removes the low-divisor bulk deterministically.  For
`1<=Y<=N` define

```text
F_(L,Y)(N)=sum_(N/Y<d<=N)mu(d)d^(-1)q_L(N/d).
```

Then

```text
|Delta_L(N)-F_(L,Y)(N)|<<_L log(eY)/Y.                  (MF5)
```

Indeed each omitted term is at most
`C_L log(eN/d)/N`, and summing over `d<=N/Y` gives `(MF5)`.  With `Y=sqrt(N)`, put

```text
F_L^front(N)=sum_(sqrt(N)<d<=N)mu(d)d^(-1)q_L(N/d).
```

The Lipschitz property of the negative part yields the block identity up to a harmless error:

```text
|sum_(X<=N<exp(1)X)E_L(N)^+/N
 -C_Lsum_(X<=N<exp(1)X)F_L^front(N)^-/sqrt(N)|
 <<_L log X.                                             (MF6)
```

Thus `d<=sqrt(N)` is rigorously below the `(C5)` budget.  The unresolved front is exactly
`sqrt(N)<d<=N`; partitioning it by `k=floor(N/d)` produces the coherent moving intervals

```text
N/(k+1)<d<=N/k,                    1<=k<sqrt(N).          (MF7)
```

This is more precise than the phrase `d asymp N`: a fixed-ratio strip is insufficient, while the
whole front remains shorter than the original all-divisor carrier.

The scalar estimate

```text
sum_(X<=N<exp(1)X)F_L^front(N)^-/sqrt(N)
 <<_L(1+log X)^A                                        (MF8)
```

is equivalent to `(C5)` up to `(MF6)`, hence is itself RH strength.  It is an exact diagnostic for
a source theorem, not an independently available scalar lemma.

Its Mellin transform makes the strength test explicit.  If

```text
K_L(s)=(1-exp(-L(s+1/2)))^2/[C_L(s+1/2)^2],
```

then in the initial half-plane, followed only afterwards by meromorphic continuation,

```text
widehat(Delta_L)(s)
 =1/s+K_L'(s)+[zeta'(s+1)/zeta(s+1)-gamma]K_L(s).        (MF9)
```

The tent multiplier has nonremovable zeros only on `Re(s)=-1/2`; it cannot censor an off-critical
zeta zero, and its lattice of critical-line zeros cannot censor all zeta zeros.  Thus eventual-sign
or better-than-half-density scalar shortcuts fail standard Mellin/Landau hostile tests.  The
allowable half-density polylogarithmic scale is exactly the open RH-strength boundary.

Primary arithmetic-renewal results do not cross it.  Balazard and Daval give exact Möbius
transforms and PNT/logarithmic-scale inequalities
([Balazard](https://arxiv.org/abs/1209.3577),
[Daval](https://arxiv.org/abs/2006.01295)); the Erdos--Ingham arithmetic Tauberian theorem requires
slow decrease or monotonicity and supplies no critical rate
([paper](https://www.renyi.hu/~p_erdos/1964-05.pdf)).  Ng's weak-Mertens distribution theory is
conditional on RH plus an additional negative-moment hypothesis
([paper](https://arxiv.org/abs/math/0310381)), while Matomaki--Radziwill's almost-all short-interval
cancellation does not control every coherent exceptional front
([paper](https://annals.math.princeton.edu/2016/183-3/p06)).

### Classical Type-II mean squares require exactly the missing power

This failure is not repaired by Vaughan or Heath--Brown decomposition.  For finite balanced
coefficients define

```text
mathcalB_(a,b)(u)
 =sum_(m,n)a_mb_n(mn)^(-1/2)h_L(u-log(mn)),
A(s)=sum_ma_mm^(-s),        B(s)=sum_nb_nn^(-s).
```

Plancherel gives the exact product Gram

```text
widehat(mathcalB)(t)
 =widehat(h_L)(t)A(1/2+it)B(1/2+it),
widehat(h_L)(t)=((1-exp(-iLt))/(it))^2.                  (TI1)
```

After the `c_N` normalization the Mellin multiplier is

```text
widehat(kappa_L)(t)
 =(1-exp(-L(1/2+it)))^2/[C_L(1/2+it)^2],
widehat(kappa_L)(0)=1.                                  (TI2)
```

A fixed log aperture therefore supplies only a frequency window `|t|=O_L(1)`.  Products near `X`
have log spacing `asymp X^(-1)`, so Montgomery--Vaughan dephasing needs length `gtrsim X`; equal
products never dephase.  An adjacent aperture difference gains `N^(-1)` but its cofinal right
inverse loses `N`; after `(AB8b)` the same loss sits at the moving front rather than an invariant
constant tail.

Writing `E_L(N)=T_L(N)-c_N` and `f_L(N)=T_L(N)/c_N`, the conventional two-sided estimate sufficient
for `(C5)` would be

```text
sum_(N asymp X)|E_L(N)|^2/N <<_L (log X)^A,              (TI3)
```

equivalently

```text
integral_J^(J+1)|f_L(exp u)-1|^2du
 <<_L X^(-1)(log X)^A.                                  (TI4)
```

This demands normalized RMS `X^(-1/2)`.  Stieltjes integration by parts, with
`R(x)=psi(x)-x`, gives

```text
E_L(x)=x^(-1/2)integral_0^(2L)R(x exp(-v))exp(v/2)
                   [h_L'(v)+(1/2)h_L(v)]dv.             (TI5)
```

The fixed-window Mellin coefficient of a zero `rho` is

```text
H_L(rho-1/2)=((1-exp(-L(rho-1/2)))/(rho-1/2))^2,
```

which is nonzero off the critical line.  Hence `(TI3)` excludes every off-line zero, while RH gives
`E_L(x)<<_L log^2x` and implies `(TI3)`.  The two-sided estimate is therefore an RH-equivalent
replacement, analytically stronger than the required one-sided positive-`L1` law `(C5)`.

The primary literature reaches exactly the expected boundary.  Saffari--Vaughan prove
unconditionally, using zero-density exponent `C`,

```text
J_psi(X,H)<<H^2X exp[-c(log X/loglog X)^(1/3)]
```

only for `H>=X^(1-2/C+epsilon)`; Huxley's `C=12/5` gives `H>=X^(1/6+epsilon)`
([paper](https://aif.centre-mersenne.org/item/10.5802/aif.649.pdf)).  For `H asymp X` this misses
the square-root variance needed in `(TI3)` by `X^(1-o(1))`.  Their RH estimate
`J_psi(X,H)<<XH log^2(2X/H)` has exactly the required power.  Heath--Brown's generalized Vaughan
identity supplies an exact decomposition, not this aperture cancellation
([paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D6C21FF61C1489E5856AA5ED276CB0A9/S0008414X00033307a.pdf/prime-numbers-in-short-intervals-and-a-generalized-vaughan-identity.pdf)).
The large sieve and Barban--Davenport--Halberstam average characters or residue classes, not the
principal translated endpoint, and leave the father channel untouched.

There is a genuine transverse survivor.  Lipschitz continuity of `kappa_L` and Chebyshev's bound
give

```text
|f_L(N+1)-f_L(N)|<<_L N^(-1),
sum_(N asymp X)(c_N/N)|f_L(N+1)-f_L(N)|^2<<_L X^(-3/2). (SV1)
```

But the sharp discrete Poincare inequality costs `X^2`; it controls only mean-zero/Haar curvature
and leaves the block father `bar(f)_(L,X)-1` unchanged.

### Generic Hardy/Calderon and finite-gauge completions fail hostile tests

The loss cannot be repaired by reorganizing the adjacent differences into a wavelet tower.  Put

```text
g_N=f_L(N)-1,                 w_N=c_N/N,
W_X=sum_(N asymp X)w_N asymp_L sqrt(X),
m_X=W_X^(-1)sum_(N asymp X)w_Ng_N.
```

The elementary one-sided father/detail inequality is

```text
sum w_Ng_N^+
 <=W_Xm_X^+ +(1/2)W_X^(1/2)
        [sum w_N|g_N-m_X|^2]^(1/2).                     (HW1)
```

Weighted path Poincare and `(SV1)` give only

```text
sum w_N|g_N-m_X|^2
 <<X^2sum w_N|g_(N+1)-g_N|^2
 <<_L X^(1/2).                                          (HW2)
```

Both losses are sharp at the level of a generic aperture theorem.  A positive constant has zero
details and target `asymp sqrt(X)`.  A centered ramp with step `X^(-1)` has zero father and adjacent
energy `asymp X^(-3/2)`, yet its positive weighted mass is again `asymp sqrt(X)`.  A full wavelet
tower only redistributes these coarse modes.  This is consistent with inhomogeneous Calderon theory,
where the low-frequency projection is independent data rather than a consequence of the
cancellation pieces
([He--Liu--Yang--Yuan](https://arxiv.org/abs/1803.09924),
[Goldberg](https://doi.org/10.1215/S0012-7094-79-04603-9)).

The source-null gauge itself has a useful exhaustion and a matching limit.  For compactly supported
`phi`, define

```text
z_phi(x)=sum_(m>=1)m^(-1)phi(x/m).
```

Then the same finite Möbius regrouping gives

```text
mathsfA z_phi=phi.                                       (HW3)
```

Consequently `q_L-z_phi` is cofinally null on the distinguished section.  Suitable `phi` can
remove any prescribed finite collection of Mellin moments.  But for every remaining nonzero gauge
`q^circ`, put

```text
widehat(q^circ)(tau)=integral_1^infinity
                     q^circ(x)x^(-1-itau)dx.
```

On any phase-stable source completion, the uniformly square-summable coherent section
`a_d=d^(-1+itau)` satisfies

```text
sum_(d<=N)a_dq^circ(N/d)
 =N^(itau)[widehat(q^circ)(tau)+o(1)].                   (HW4)
```

Finite moment cancellation leaves some fixed frequency with nonzero multiplier, whose real part
has fixed positive amplitude on infinitely many logarithmic blocks and costs `asymp sqrt(X)`.
Eliminating a whole frequency interval forces `q^circ=0` by Mellin uniqueness; `(HW3)` then requires

```text
phi=mathsfAq_L=Delta_L,
```

which constructs the gauge from the evaluated completed defect.  This refutes generic
phase-stable Hardy completions.  It does **not** refute a genuinely arithmetic source space which
excludes the phase sections by exact real Möbius/Type-II orientation; that exclusion and its stable
norm would themselves be part of the missing theorem.

### Honest rank-one boundary extensions retain the same mass `[PAPER-PROVED NO-GO]`

Compact gauges in `(HW3)` are genuinely null on more than one line.  If `b` is any fixed finitely
supported Dirichlet-convolution coefficient, then pairing `z_phi` with `b*u` gives `(b*phi)(N)`,
which vanishes cofinally.  The boundary value must nevertheless be retained on the full source
mapping cone.

For an unweighted finite aperture put

```text
Q_N(d)=q_L(N/d),
b_(phi,N)=((q_L(N/d)-z_phi(N/d))_(d<=N),
           (phi(N/d))_(d<=N)),

mathscrD_(phi,N)=[0              b_(phi,N)^*;
                  b_(phi,N)     0].                     (BE1)
```

This is a source-defined self-adjoint, non-Jordan boundary extension.  Its only nonzero eigenvalues
are `+-||b_(phi,N)||`, and

```text
||b_(phi,N)||^2
 =sum_(d<=N)|q_L(N/d)-z_phi(N/d)|^2
  +sum_(d<=N)|phi(N/d)|^2.                              (BE2)
```

The obstruction can be minimized exactly.  Under

```text
(Uf)(y)=exp(-y/2)f(exp y),
```

the harmonic lift `phi -> z_phi` has Fourier multiplier `zeta(3/2+it)`.  Therefore, for every
honest fixed boundary weight `lambda>0`,

```text
integral_1^infinity[|q_L-z_phi|^2+lambda|phi|^2]dx/x^2
 =integral_R[|qhat_L-zeta(3/2+it)phihat|^2
             +lambda|phihat|^2]dt.                      (BE3)
```

The unique geometric minimizer and its residual are

```text
phihat_geom
 =conj(zeta(3/2+it))qhat_L/(|zeta(3/2+it)|^2+lambda),

min=integral_R lambda|qhat_L|^2/
                    (|zeta(3/2+it)|^2+lambda) dt>0.      (BE4)
```

The minimum is strict because `q_L(1)=1`.  Riemann-sum scaling then gives, uniformly over every
profile and every such honest port,

```text
inf_phi||b_(phi,N)||^2 asymp_L N,
sum_(N asymp X)(c_N/N)inf_phi||b_(phi,N)||^2
 asymp_L X^(3/2).                                       (BE5)
```

The favorable reciprocal divisor norm reduces the fibre cost to order `1`, but its block cost is
still `asymp_L sqrt(X)`.  Cayley or dissipative realization preserves this controllability singular
value.

If the boundary weight is set to zero, the only zero-bulk choice is

```text
phi=mathsfAq_L=Delta_L,
phi(N)=1-T_L(N)/c_N=-E_L(N)/c_N.                         (BE6)
```

The perfect gauge has merely transferred the evaluated target into its boundary port.  Likewise,
for a local positive graph `||t b_(phi,N)+y_N||^2`, the unique minimizing scalar is

```text
t_opt=-<b_(phi,N),y_N>/||b_(phi,N)||^2,                 (BE7)
```

whose numerator on the distinguished Stokes state is `-E_L(N)/c_N`.  A block-shared minimizer
reads the corresponding weighted block defect.  These are forbidden line-tailored choices.

A cross-aperture compression which merges the scalar coordinates before positivity controls at
most

```text
[sum_(N asymp X)E_L(N)/N]^+,
```

which does not dominate `sum E_L(N)^+/N`; retaining the coordinates restores `(BE5)`.  Thus every
honestly normed rank-one self-adjoint, Cayley, or dissipative father extension is refuted.  The
survivor must be higher-rank, arithmetic, and signed across the moving intervals `(MF7)` before any
positive port is formed.

### Hostile verdict and corrected open core

`[PAPER-PROVED] [REDISCOVERED BRIDGE]` The Euler--Koszul derivative `(AB2)`, harmonic-floor mapping
cone `(AB4)`--`(AB6)`, and reduced contracting homotopy `(AB9)` are exact.  The first three
arithmetic identities are already Lean-proved in `Mollifier.lean`.

`[PAPER-PROVED CORRECTION]` The `gamma M_1` split `(AB8)` is not invariant.  The source-null identity
`(AB8a)` produces the decaying representative `(AB8b)`.  It removes the constant tail on the
distinguished line but not the moving-front row on a genuine source module.

`[FALSIFIED]` Positive Type-II branch completion, raw or reciprocal harmonic-floor completion,
a reduced-difference completion whose homotopy is required to be cofinally bounded, and a
conventional two-sided Type-II/Selberg mean square.  They respectively pay `(BU7)`,
`(AB10)`--`(AB11)`, lose the moving-front power, or assume the RH-equivalent estimate `(TI3)`.
Generic Hardy/wavelet completion and every finite-moment null gauge additionally fail
`(HW1)`--`(HW4)`.  Every honestly weighted rank-one self-adjoint, Cayley, or dissipative boundary
extension pays `(BE5)`; its zero-cost limit is the evaluated-defect gauge `(BE6)`.

`[POSITIVE SALVAGE]` The reduced aperture current is contractible, the scalar trace has the decaying
kernel `(AB8b)`, its transverse adjacent-cutoff energy satisfies `(SV1)`, and `(MF5)`--`(MF7)`
discard the entire low-divisor half at only logarithmic block cost.  The obstruction is not an
unspecified Type-II identity or an unavoidable `gamma M_1` summand: it is the one-sided cofinal
moving-front/source-extension estimate `(MF8)`.

`[SUPERSEDED PROVISIONAL OPEN CORE]` Construct a source-defined, genuinely **one-sided
father--curvature coupling** which
uses the shrinking transverse current `(SV1)` but controls

```text
sum_(N asymp exp(J)) E_L(N)^+/N
```

polynomially before positive norm separation.  Its source and norm must be fixed independently of
`E_L`, its sign, zero data, and the evaluated Mertens sum.  It must extend the null gauge `(AB8b)`
beyond the distinguished line, control the full moving `sqrt(N)<d<=N` front without norming its
interval atoms, and
must not replace the target by `(TI3)` or a square-root two-sided estimate for `M_1`.  This was the
provisional source-space formulation before the support-canonical corpus correction below.

Its provisional theorem form asked, for `X=exp(J)`, for `Z_J`, coherent restrictions `rho_N`, a
uniformly bounded Möbius section `xi_J`, and source-defined non-spectral maps satisfying

```text
tau_(N,F)(z,z)=||Gamma_(N,+)rho_Nz||^2-||Gamma_(N,-)rho_Nz||^2,
tau_(N,F)(xi_J,xi_J)=-F_L^front(N),

sum_(X<=N<exp(1)X)(c_N/N)||Gamma_(N,+)rho_Nz||^2
 <=C_L(1+J)^A||z||_(Z_J)^2.                             (MF10)
```

The maps must be built from the signed moving-interval/floor incidence before evaluation.  The
scalar Jordan decomposition of `F_L^front`, the naive front-row norm, and `(BE6)` are excluded.

## 2026-07-18 corpus correction: the scalar moving front is coarser than the canonical lcm core

`[CORPUS CORRECTION] [MF10 RETIRED AS THE FRONTIER] [EXACT LCM/COAREA CORE OPEN]`

The conclusion immediately above was too coarse.  The identities `(MF1)`--`(MF9)` and the
low-divisor truncation remain valid, but the assertion that `(MF10)` is the exact remaining content
does not survive the live corpus.  The canonical report `docs/reports/rh-proof-shape-1707.md`
already retains the two endpoint cells, active divisor support, and Boolean grades far enough to
give a strictly smaller noncircular core.  In contrast, an abstract source space `Z_J` and maps
`Gamma_(N,+-)` constrained only by their value on `xi_J` can be reverse-engineered from
`F_L^front`; excluding that circularity requires the support-canonical endpoint structure below.

For the fixed-ratio endpoint covariance, write `n=m+h`, let `I_h` be the actual overlap interval,
let `W_h` be its clipped weight, and group divisor pairs by `l=lcm(d,e)`.  The exact active-support
collapse is

```text
sum_(d|Q_z,d|m; e|Q_z,e|m+h; lcm(d,e)=l) mu(d)mu(e)
 =mu(l) 1_(l|m(m+h)).                                  (LC1)
```

For squarefree `l`, the active roots are

```text
R_(l,h)={r mod l:l|r(r+h)},
nu_h(l)=#R_(l,h)=2^omega(l/(l,h)).                     (LC2)
```

The bounded-variation progression estimate in `(35m51)`--`(35m52)` of the canonical report removes
every centered lcm mode `l<=D` at cost `O(log(M)^3/M)` when `D=z asymp sqrt(M)`.  Consequently the
ordinary-prime covariance has the exact reduction

```text
C_M
 =c_M^2 A^3 a_D/12
  +sum_h sum_(m in I_h) W_h(m)
     sum_(l|Q_z,l>D,l|m(m+h)) mu(l)
  +O_(A,rho)(log(M)^3/M),

a_D=sum_(l|Q_z,l<=D) mu(l)/l product_(p|l)(2-1/p).     (LC3)
```

Thus the unresolved cancellation is not merely a high-divisor scalar front.  It is the signed
joining of the explicit low-lcm density with the **active** high-lcm tail.  The middle range
`D<l<=H_h`, where each residue class still has complete periods, and the incomplete range
`l>H_h` are both essential.  A shell localized only at `p asymp sqrt(M)` misses the former and the
unbalanced higher-grade crossings.

The matching preterminal coordinate is the signed divisor coarea.  With

```text
lambda_(S,v)(n)=-sum_(d|n,d|Q_S) mu(d) 1_(0<=v<log d),
Xco+_S(u,v,t)=1_(v>=0) P_0
  sum_(exp(u-t)<n<=exp(u+c-t)) lambda_(S,v)(n)/n,
H_S^0(u,t)=P_0 sum_(exp(u-t)<m<=exp(u+c-t)) a_S(m)/m,
```

prime adjunction has the causal inhomogeneous law

```text
Xco+_(S union {p})(u,v,t)
 =Xco+_S(u,v,t)-p^(-1)Xco+_S(u-log p,v-log p,t)
  +p^(-1)1_(0<=v<log p) H_S^0(u-log p,t).              (LC4)
```

The last term is a canonical harmonic boundary injection fixed before evaluation.  Its integral
recovers the physical von Mangoldt current only at the full terminal divisor set, whereas `(LC3)`
is expressed at the square-root sieve set.  The high-lcm tail is the same coarea current before
integration:

```text
btail_(S,V)(R)=sum_(l|Q_S,l|R,log l>V) mu(l)
             =-lambda_(S,V)(R),                        (LC5)
```

and its prime-adjunction threshold packet is exactly `(35m64)`--`(35m65)` of the canonical report.
Taking an absolute value, positive part, or raw square before the Boolean grades join is forbidden:
the exact zero tangent can have exponentially large separated square mass, as `(35m66)` shows.

`[CORRECTED OPEN CORE]` Derive an exact **future-dressed endpoint pairing**, fixed independently of
the terminal covariance, between the full causal endpoint in `(LC4)` and the square-root-sieve
high-lcm reduction `(LC3)`--`(LC5)`.  It must retain the future Boolean dressing of `(35m59)`, the
complete-period middle `D<l<=H_h`, the incomplete boundary `l>H_h`, and the staircase endpoint
cells.  Then prove a signed interval-local coarea/trace estimate for those paired defects.  A
lower-cone energy, a raw positive square function, a residual defined from `C_M`, or maps chosen to
realize `F_L^front` do not meet the statement.

The first quantitative checkpoint is still the fixed-ratio block-current estimate `(35m20)`, which
is paper-level equivalent to RH.  The exact harmonic rational-grid frame `(35o)`--`(35q)` passes a
generic floor test, while the phase source `(35r)` refutes every coefficient-universal version.
Therefore the missing estimate, if true, must use the exact real all-grade Möbius orientation.
Only after the endpoint pairing and signed trace are proved would it be honest to package their
consequence as a source Carleson theorem of the form suggested by `(MF10)`.

## 2026-07-18 scalar-front dispersion, scale-halving, and square-carrier audit

`[PAPER-PROVED NO-GO] [CLASSICAL LARGE SIEVE/BDH REFUTED AS PROVIDERS]`
`[SCALE-HALVING IS AN ALMOST IDENTITY] [SQUARE CARRIER LEAVES LIOUVILLE FRONT]`

This audit concerns only the coarser scalar front.  It does not supersede `(LC1)`--`(LC5)`.  Put

```text
B_X={N:X<=N<exp(1)X},
F_L^front(N)=sum_(sqrt(N)<d<=N) mu(d)q_L(N/d)/d,
S_X=sum_(N in B_X) (F_L^front(N))^-/sqrt(N).
```

Coordinatewise duality gives the exact one-sided normalization

```text
S_X=sup_(0<=epsilon_N<=1)
 -sum_d mu(d)/d
   sum_(N in B_X, d<=N<d^2) epsilon_N q_L(N/d)/sqrt(N). (FD1)
```

Writing `N=kd+r`, `0<=r<d`, permits an exact discrete Fourier expansion in `r mod d`, but
`epsilon_N` remains arbitrary endpoint data rather than a residue-class average.  On `d asymp D`,
the fixed frequencies `1/d` are spaced by `asymp D^(-2)`.  The classical large sieve therefore
gives, for `b_N=epsilon_N/sqrt(N)`,

```text
sum_(d asymp D) |sum_(N in B_X)b_N exp(2 pi i N/d)|^2
 <<(X+D^2)sum_N|b_N|^2,

classical port cost asymp sqrt(X/D+D).                 (FD2)
```

If `N/d asymp K`, then `D asymp X/K` and
`q_L(N/d)<<_L(1+log K)/K`, so the resulting cell bound is

```text
sqrt(X)(1+log K)/K^(3/2),       1<=K<=sqrt(X).          (FD3)
```

The cofinal cell `K=O(1)`, `d asymp X`, costs `sqrt(X)`, not a logarithmic power.  The zero Fourier
mode is the unremoved father channel; centering it leaves a fixed nonzero mode with the same
`D^2` spacing wall.  Removing that term specifically for the Möbius coefficients would itself be
the missing arithmetic theorem.  This is the exact classical large-sieve mechanism of
[Montgomery--Vaughan](https://doi.org/10.1112/S0025579300004708), not a defect of a chosen
inequality.  Linnik dispersion obtains power savings only after genuine congruence and character
separation, often with a Kloosterman input; the endpoint selector in `(FD1)` provides neither
([Pascadi](https://doi.org/10.1112/S0010437X2500747X)).  BDH averages progression discrepancies
over both moduli and residue classes; treating the moving endpoint in `(FD1)` as that average is a
category error ([Hooley](https://doi.org/10.1515/crll.1975.274-275.206)).

The raw power count makes the loss independent of Fourier language.  If

```text
G_X(d,e)=sum_(N in B_X, max(d,e)<=N<min(d^2,e^2))
             q_L(N/d)q_L(N/e),
```

then

```text
sum_(N in B_X)|F_L^front(N)|^2
 =sum_(d,e)mu(d)mu(e)G_X(d,e)/(de).                    (FD4)
```

The signed diagonal is `asymp_L 1`, while the termwise absolute off-diagonal is `asymp_L X`.
Equivalently,

```text
sum_(N in B_X) 1/sqrt(N)
 sum_(sqrt(N)<d<=N) |mu(d)q_L(N/d)|/d
 asymp_L sqrt(X).                                      (FD5)
```

The two-port absolute statement uses only squarefree density and `q_L(1)=1`; a prescribed
Möbius-sign port uses PNT.  Cauchy before sign collapse replaces the one-sided target by
`sum_N|F_L^front(N)|^2<<poly(log X)`, which is the RH-equivalent two-sided estimate `(TI3)`.

The tempting scale-halving hyperbola transfer is exact but is not a contraction.  Since
`q_L=mathsfB Delta_L`, finite regrouping gives

```text
F_L^front(N)
 =sum_(sqrt(N)<n<=N) c_N(n)Delta_L(N/n)/n,
c_N(n)=sum_(d|n,d>sqrt(N))mu(d)
      =-sum_(d|n,d<=sqrt(N))mu(d).                     (SH1)
```

Every displayed input aperture is below `sqrt(N)`.  Nevertheless splitting the original Möbius
inverse at `sqrt(N)` gives the stronger classification

```text
F_L^front(N)=Delta_L(N)-R_L(N),
R_L(N)=sum_(d<=sqrt(N))mu(d)q_L(N/d)/d,
|R_L(N)|<<_L log(N)/sqrt(N).                           (SH2)
```

Thus the scale-halving formula reconstructs the current value with coefficient `1+o(1)`.  Taking
positive norms after `(SH1)` costs at least a square-root diagonal; correlating the lower-scale
inputs strongly enough to remove it is just the original renewal problem.

Finally, the existing square carrier does not create a new safe source.  With
`lambda(n)=(-1)^Omega(n)`, Dirichlet convolution gives exactly

```text
mu=(sqrtPart mu)*lambda,
mu(d)=sum_(a^2 b=d)mu(a)lambda(b),

F_L^front(N)
 =sum_a mu(a)/a^2
   sum_(sqrt(N)/a^2<b<=N/a^2) lambda(b)q_L(N/(a^2b))/b. (SQ1)
```

The `a` carrier is absolutely summable, but its unit fibre `a=1` is the complete Liouville front,
whose Dirichlet series is `zeta(2s)/zeta(s)` and therefore retains the zeta denominator.  Before
signed `a`-collapse its absolute block mass is again `asymp_L sqrt(X)`; after collapse `(SQ1)`
returns the original Möbius front.  Cauchy across `a` cannot help because the `a=1` diagonal
remains.  The safe square factor and mean-value faces already occur in
`SquarefreeMoebiusNormalization.lean`, `MFreeLadder.lean`, and
`MobiusSquarefreeReciprocalTransfer.lean`; they do not control this Liouville quotient.

`[FALSIFIED METHODS]` Classical endpoint DFT plus large sieve/BDH, conventional quadratic
Type-II dispersion, positive scale-halving polarization, and square-carrier separation before
sign collapse.  All lose `sqrt(X)` or assume `(TI3)`.

`[POSITIVE SALVAGE]` The exact endpoint dual `(FD1)`, almost-identity `(SH1)`--`(SH2)`, and square
factorization `(SQ1)` precisely locate why these methods fail.  They also confirm that the scalar
front has already forgotten the support roots, future Boolean dressing, complete-period middle,
incomplete boundary, and causal injection retained by `(LC1)`--`(LC5)`.  The canonical signed
lcm/coarea trace problem remains untouched.

## 2026-07-18 square-root causal--lcm splice and its unintegrated remainder

`[PAPER-PROVED BRIDGE] [INTEGRATED ENDPOINT PAIRING CLOSED]`
`[DIVISOR-RESOLVED CAUSAL DEFECT JOINING OPEN] [NOT AN ESTIMATE]`

The square-root sieve supplies a canonical algebraic splice between the causal boundary source and
the support-lcm reduction.  It closes the **integrated** endpoint wiring requested after `(LC5)`,
but not the signed interval-local estimate and not yet the full unintegrated coarea pairing.

Let

```text
A_(M,K)={n in N:M exp(-A)<n<=K},
z=sqrt(K),       M exp(-A)>z,
S_0={p:p<=z},    F={p:z<p<=K}.
```

For a prime set `S`, retain `a_S(n)=product_(q in S)(1-1_(q|n))`.  The coefficient-level causal
boundary source in `(LC4)` is

```text
j_(p,S)(n,v)=1_(p|n)a_S(n)1_(0<=v<log p).              (SP1)
```

Order the primes of `F`, let `S_(j-1)` contain `S_0` and the preceding ones, and future-dress each
`j_(p_j,S_(j-1))` by the remaining homogeneous transports from `(LC4)`.  If `(SP1)` is nonzero on
`A_(M,K)`, write `n=p_j r`.  When `r>1`, a prime divisor of `r` is below `z` and already kills
`a_S(n)`; when `r=1`, `n=p_j`.  Two factors above `z` cannot occur because their product exceeds
`K`.  Later transports do not alter the surviving singleton.  Hence the dressed injection sum is
exactly

```text
J_v(n)=sum_j T_(>j)j_(p_j,S_(j-1))(n,v)
      =1_(n is prime)1_(0<=v<log n),

J(n)=integral_0^infinity J_v(n)dv
    =log(n)1_(n is prime)
    =log(n)a_(S_0)(n),              n in A_(M,K).       (SP2)
```

This source is fixed by the aperture and prime filtration before the endpoint covariance is
evaluated.  If `P_K` contains every prime through `K`, the full causal endpoint has the exact
coefficientwise decomposition

```text
lambda+_(P_K,v)(n)=J_v(n)+Rpp_v(n)+C_v(n),

Rpp_v(n)=1_(n=p^k,k>=2)1_(0<=v<log p),
C_v(n)=1_(omega(n)>=2)lambda+_(P_K,v)(n),

integral C_v(n)dv=0,
Lambda(n)=J(n)+integral Rpp_v(n)dv.                    (SP3)
```

Thus the integrated remainder is exactly the already-harmless proper-prime-power row.  The field
`C_v` must nevertheless not be discarded before integration: for a composite with at least two
distinct prime factors it is generally nonzero, and `(35m66)` shows that its raw square can be
exponentially larger than its zero integral.

The canonical way to retain this field is to delay the log-threshold pushforward.  On the Boolean
lcm semilattice define

```text
Omega_(S,n)=sum_(d|n,d|Q_S)mu(d)e_d,
e_d star e_e=e_(lcm(d,e)).                             (SP4)
```

The local factor `e_1-e_p` is idempotent for `star`, so bilinearity gives the exact identity

```text
Omega_(S,m) star Omega_(S,n)=Omega_(S,mn).             (SP5)
```

Let `epsilon(e_d)=1`, `ell(e_d)=log d`, and
`theta_V(e_d)=1_(log d>V)`.  Then

```text
epsilon(Omega_(S,n))=a_S(n),
-ell(Omega_(S,n))=Lambda_S(n),
theta_V(Omega_(S,n))=btail_(S,V)(n)=-lambda_(S,V)(n). (SP6)
```

Equation `(SP5)` is the divisor-resolved form of `(LC1)` and retains every zero-integral composite
packet in `(SP3)`.  In particular

```text
J(m)J(n)/(log(m)log(n))
 =epsilon(Omega_(S_0,m) star Omega_(S_0,n)).            (SP7)
```

Here the quotient is the prime indicator; the existing weight `W_h` already contains the external
`log(m)log(n)/(mn)` labels and the exact clipped endpoint kernel.  Multiplying the normalized
identity `(SP7)` by that weight, summing over `n=m+h`, and writing

```text
beta_M(e_l)=B_l
 =sum_h sum_(m in I_h,l|m(m+h))W_h(m),
v_z=sum_(l|Q_z)mu(l)e_l,
```

gives, without a terminally defined residual,

```text
C_M=beta_M(v_z),

C_M=c_M^2 A^3 a_D/12+R_(M,D)+beta_M(Q_D v_z),
|R_(M,D)|<<_(A,rho)log(M)^3/M,        D asymp sqrt(M). (SP8)
```

The final term is the exact high-lcm tail.  For ordered small primes, `(35m59)` gives

```text
beta_M(Q_Dv_z)
 =-sum_j beta_M(
    product_(k>j)(I-Lscr_(p_k))
    Q_D Lscr_(p_j)P_Dv_(j-1)).                         (SP9)
```

Thus `(SP2)`--`(SP9)` give a genuine target-independent pairing between the integrated causal
boundary injection and the support-canonical high-lcm reduction.  The exact weight `beta_M`
retains the complete-period middle, incomplete boundary, and clipped endpoint cells; `(SP9)`
retains every future small-prime Boolean grade.

`[LIMIT OF THE BRIDGE]` The scalar injection `J` in `(SP2)` has already integrated away `C_v`.
Although `(SP4)`--`(SP6)` retain the divisor-resolved composite profiles algebraically, no
coercive signed pairing has been proved which joins their causal future transport to the crossing
packets in `(SP9)` at an interval-local trace.  Declaring `C_v=0`, norming it separately, or using
only `(SP8)` returns respectively a false deletion, the explosion `(35m66)`, or the
RH-equivalent endpoint covariance.

The precise grade-wise mismatch can be exposed without defining a covariance residual.  Every
active `m` has a unique factorization

```text
m=p r,
p=1 if m is z-smooth, otherwise p>z is its unique large prime factor,
r is z-smooth.
```

For squarefree `d|r`, put

```text
K_v(d,1)=-1_(0<=v<log d),
K_v(d,p)=1_(0<=v<log(pd))-1_(0<=v<log d),     p>z.     (SP10)
```

Direct expansion of the full divisor set gives

```text
lambda+_(P_K,v)(m)=sum_(d|r,d|Q_z)mu(d)K_v(d,p).       (SP11)
```

The `d=1` term for `p>z` is exactly the future prime injection; `d>1` are its transported
composite packets.  Moreover

```text
integral K_v(d,p)dv=log p,       p>z,
integral K_v(d,1)dv=-log d.                            (SP12)
```

The lcm reduction instead assigns the external endpoint label `log m` to **every** small-divisor
grade.  Define

```text
S_v(m;d)=1_(0<=v<log m),
G_v(m;d)=S_v(m;d)-K_v(d,p).                            (SP13)
```

Then, before integration,

```text
a_(S_0)(m)1_(0<=v<log m)
 =lambda+_(P_K,v)(m)+sum_(d|r)mu(d)G_v(m;d).           (SP14)
```

For two endpoints the exact colored identity is

```text
S_v(m;d)S_w(n;e)
 =K_v(d,p)K_w(e,q)+K_v(d,p)G_w(n;e)
  +G_v(m;d)K_w(e,q)+G_v(m;d)G_w(n;e).                 (SP15)
```

After multiplying by `mu(d)mu(e)`, the projection `lcm(d,e)>D` and the future product in `(SP9)`
retain all four ports and every endpoint cell.  To interface with the existing `W_h`, which already
contains `log(m)log(n)`, divide the `m`-profiles in `(SP15)` by `log m` and the `n`-profiles by
`log n`; their integrals then recover the prime indicators without double-counting the labels.

`[EXACT BUT INSUFFICIENT]` Equations `(SP10)`--`(SP15)` are a pre-integration change of profile,
not a quantitative theorem.  The `G` row is defined by comparison with the already selected
endpoint profile and is gradewise nonunique under source-null modifications.  More decisively,
applying `Q_D` to `(SP15)` pairs only the raw high-lcm term in `(SP8)`.  It supplies no causal mate
for the deterministic low-density contribution

```text
c_M^2 A^3 a_D/12,                                     (SP16)
```

which is exactly what must cancel that high tail.  Adding `(SP16)` by hand and calling the sum a
defect merely restates `(SP8)`.

`[CORRECTED OPEN CORE]` Derive, from the causal prime-adjunction law itself, a normalized
divisor-resolved defect whose **same identity** produces both the density term `(SP16)` and the
four future-dressed high-tail ports `(SP15)`, including the complete-period middle, incomplete
boundary, and endpoint cells.  Only then prove its signed interval-local trace estimate before any
positive/absolute operation.  The integrated splice and the grade-wise mismatch are now explicit;
the density--tail causal joining and its quantitative trace remain the RH-bearing steps.

## 2026-07-18 exponentially weighted coarea fibre and trace no-go

`[PAPER-PROVED POSITIVE FIBRE THEOREM] [INTERVAL-LOCAL TRACE REFUTED]`
`[ANCHORED COAREA FATHER GAUGES TO SCALAR TRANSFER]`

The raw unweighted square in `(35m66)` is not the only available coarea geometry.  For a full prime
set and `n>1`, put `R=rad(n)` and write

```text
lambda_n(v)=lambda+_(P_n,v)(n)
 =sum_(d|R,d<=exp(v))mu(d),            v>=0.           (WE1)
```

For `Re(s)>0`, finite integration gives the exact Laplace transform

```text
integral_0^infinity exp(-s v)lambda_n(v)dv
 =s^(-1)product_(p|n)(1-p^(-s)).                       (WE2)
```

Consequently Plancherel gives, for `sigma>0`,

```text
E_sigma(n)=integral_0^infinity exp(-sigma v)|lambda_n(v)|^2dv

 =1/(2 pi) integral_R
   |product_(p|n)(1-p^(-sigma/2-it))|^2/
   ((sigma/2)^2+t^2) dt

 =sigma^(-1)sum_(d,e|R)mu(d)mu(e)max(d,e)^(-sigma).    (WE3)
```

At the critical reciprocal-square weight this yields the unconditional ordinary-integer bound

```text
E_2(n)
 <=(1/2)product_(p|n)(1+1/p)^2
 <=(1/2)(R/phi(R))^2
 <<(loglog(3n))^2.                                     (WE4)
```

Thus exponential coarea weighting genuinely suppresses the Boolean grade explosion for ordinary
integers.  It is not universal over generalized primes.  If `r` distinct atoms all have the same
norm `P`, then on `j log(P)<=v<(j+1)log(P)` one has

```text
lambda(v)=(-1)^j binomial(r-1,j),

E_2
 =(1-P^(-2))/2 sum_(j=0)^(r-1)binomial(r-1,j)^2P^(-2j)
 >=(1-P^(-2))/(2r)(1+P^(-1))^(2r-2).                  (WE5)
```

Repeated-norm bursts remain exponential, so `(WE4)` uses the ordinary-prime norm distribution and
is a real arithmetic fibre theorem rather than a phase-blind coarea principle.

The endpoint trace nevertheless fails at exactly the required power.  A prime or prime-power
profile is `1_(0<=v<log p)`: its `E_2` norm stays between fixed constants while its integral is
`log p`.  More decisively, for primes `p<q` with fixed ratio and `p,q asymp M`, put

```text
F_(p,q)(v)=[lambda_p(v)-lambda_q(v)]/p
          =-1_(log p<=v<log q)/p.
```

Then

```text
||F_(p,q)||_(L2(exp(-2v)dv))^2
 =(p^(-2)-q^(-2))/(2p^2) asymp M^(-4),

|integral F_(p,q)(v)dv|^2
 =|log(q/p)|^2/p^2 asymp M^(-2).                       (WE6)
```

Any uniform interval-local trace from this weighted fibre therefore needs operator norm
`asymp M`, or `M^2` in squared form, rather than a logarithmic power.  The general Cauchy estimate
on `v<=log M` has the same sharp loss.  Centered aperture differences create precisely the profile
in `(WE6)`, so the obstruction is not removed by `P_0`.

Equivalently, the endpoint is the singular boundary evaluation

```text
Lambda(n)=lim_(s->0) s^(-1)product_(p|n)(1-p^(-s)),    (WE6a)
```

whereas `(WE4)` controls the same finite Euler product only on `Re(s)=1`.  The two-prime witness
`(WE6)` proves that coefficient-universal continuation from that line to `(WE6a)` costs the full
aperture.  Any surviving trace must therefore use the exact joined arithmetic source.

There is a canonical father gauge, but it only moves the source.  Let

```text
B(u,v)=1_(0<=v<u),
(R_pF)(u,v)=F(u-log p,v-log p).
```

The identity

```text
B(u,v)-B(u-log p,v-log p)=1_(0<=v<log p)               (WE7)
```

and `(LC4)` imply, with

```text
Y_S=Xco+_S+B H_S^0,

Y_(S union {p})=Y_S-p^(-1)R_pY_S.                     (WE8)
```

At the full active prime set `H_S^0=0`, so `Y_terminal=Xco+_terminal`; at the empty set the whole
causal injection is the initial father `B H_empty^0`.  Thus anchoring diagonalizes the coarea
forcing into the same commuting scalar transfers as `(35m43)`--`(35m45)`.  Terminal polarization
remembers only the complete lcm packet and still requires the low-lcm correction and future
dressing in `(35m58)`--`(35m59)`.

The diagonal-invariant weight `exp(2(v-u))` also fails.  In `du dv` it makes `R_p` unitary, but the
physical counting measure is `exp(u)du`; there `||R_p||=sqrt(p)`, so `p^(-1)R_p` again has size
`p^(-1/2)`, exactly the wall `(35m47)`--`(35m48)`.  At the essential crossing
`v=log D asymp u/2`, its weight is `asymp M^(-1)`: a unit crossing has norm `M^(-1/2)` but order-one
trace, losing `sqrt(M)`.  The weight controls only a top strip `v=u+O(1)` and suppresses the
complete-period middle that `(LC3)` requires.  For `r` equal-log generalized atoms the top-weight
energy equals `(WE5)` by the symmetry `j <-> r-1-j`, so the exponential hostile test also remains.

`[POSITIVE SALVAGE]` Equations `(WE2)`--`(WE4)` provide a canonical polylogarithmic norm for each
ordinary divisor-coarea fibre and may be useful after a signed joining is already known.

`[FALSIFIED METHODS]` Deriving the endpoint from that norm by Cauchy/trace, anchored father
subtraction, or the diagonal-invariant top weight.  They lose respectively `M`, move the causal
source to the empty boundary, or recreate the square-root transfer wall.  None supplies the
density--tail joining or its interval-local trace.

## 2026-07-18 stopped Bernoulli density vacuum and inactive-channel no-go

`[PAPER-PROVED NO-GO] [CONTINUUM VACUUM IS EULER COMPLETION OR DIRECT SPLICE]`
`[PHYSICAL SUPPORT DOES NOT RESTORE MULTIPLICATIVITY]`

The density coefficient in `(SP16)` has a unique natural continuum interpretation.  On the
Boolean lcm module let

```text
v_z=product_(p<=z)(I-Lscr_p)e_1=sum_(l|Q_z)mu(l)e_l,
P_D e_l=1_(l<=D)e_l,       Q_D=I-P_D.
```

Two independent endpoint residue colors force

```text
rho(p)=Prob(p|mn)=2/p-1/p^2,
omega(e_l)=rho(l)=product_(p|l)rho(p).                 (DV1)
```

Thus, with `V_z=product_(p<=z)(1-1/p)`,

```text
omega(P_Dv_z)=a_D,
omega(v_z)=product_(p<=z)(1-rho(p))=V_z^2.            (DV2)
```

The local colored identity is `-1/p-1/p+1/p^2=-rho(p)`, so this state is not chosen to fit the
terminal covariance.  Let `beta_M(e_l)=B_l` be the exact active functional and
`T_M=c_M^2 A^3/12`.  The only stopped low-vacuum/high-active splice is

```text
Phi_D=T_M omega P_D+beta_M Q_D,
Phi_D(v_z)=T_M a_D+beta_M(Q_Dv_z).                    (DV3)
```

Up to the already-proved low progression and `h`-quadrature error, `(DV3)` is exactly `(SP8)`, not
a new pairing.  If

```text
F_j=product_(k>j)(I-Lscr_(p_k))
      Q_D Lscr_(p_j)P_Dv_(j-1),
```

then `(SP9)` gives the alternative exact rewrite

```text
T_M a_D+beta_M(Q_Dv_z)
 =T_M V_z^2-sum_j (beta_M-T_M omega)(F_j).            (DV4)
```

Equation `(DV4)` is the unique total vacuum correction to the future-dressed crossings.  It has no
canonical allocation among the four `K/G` ports in `(SP15)`; only their joined total is invariant.

The fixed-gap form exposes the failure.  Put

```text
J_h=integral_R W_h(x)dx,
beta_h(e_l)=sum_(m in I_h,l|m(m+h))W_h(m),
omega_h(e_l)=nu_h(l)/l,
delta_h=beta_h-J_h omega_h.
```

Then `omega_h(v_z)=S_z(h)` and

```text
J_h omega_h(P_Dv_z)+beta_h(Q_Dv_z)
 =J_h S_z(h)-sum_j delta_h(F_j).                      (DV5)
```

This is precisely the Euler-completed singular-series split `(35m34)`--`(35m39)`.  For an inactive
channel, and in particular `l>K^2`, `beta_h(e_l)=0` while `omega_h(e_l)>0`; extending the vacuum
through `Q_D` therefore manufactures the virtual mass `-J_h omega_h(e_l)`.  Refusing that extension
returns the direct projection splice `(DV3)`.

Stopping at the physical interval length `H_h=#I_h` creates no third option.  When `H_h>=D`,

```text
J_h omega_h(P_Dv_z)+beta_h(Q_Dv_z)
 =J_h omega_h(P_(H_h)v_z)+beta_h(Q_(H_h)v_z)
  +delta_h((P_(H_h)-P_D)v_z).                         (DV6)
```

The last term is exactly the complete-period middle `D<l<=H_h`; the `Q_(H_h)` term is the
incomplete boundary with its endpoint cells.  An active-root-truncated vacuum is not
multiplicative or lcm-closed: for example, on `h=2`, `I_h={2,3}`, the channels `2` and `3` are
active while `6` is inactive.  Its prime-adjunction commutator is the empirical endpoint-floor
defect one was trying to estimate.

`[FALSIFIED METHOD]` A homogeneous Bernoulli vacuum as the density--tail causal joining.  Extended
cofinally it is the inactive-channel Euler completion and has the rough terminal mismatch
`(35m55)`; stopped at `D` or `H_h` it merely restates the projection split and relocates the open
middle/boundary terms.  The algebra also passes generalized-prime burst fakes.

`[POSITIVE SALVAGE]` Equations `(DV5)`--`(DV6)` give an exact classification of the missing term:
the future-dressed signed discrepancy `delta_h` across the complete-period middle, physical
incomplete boundary, and endpoint cells.  A source-specific interval-local estimate for that
joined discrepancy remains open.

## 2026-07-18 positive ratio averaging and adaptive-telescoping no-go

`[PAPER-PROVED EQUIVALENCE] [NONNEGATIVE RATIO AVERAGING IS RH-EQUIVALENT]`
`[COMPLETE-COLUMN TILING DOES NOT ESTIMATE THE AVERAGE]`

Ratio averaging does not lower the strength of `(35m20)`.  Fix
`0<c_-<c_+<A`, put

```text
K_-=ceil(exp(c_-)M),       K_+=floor(exp(c_+)M),
omega_K=log((K+1)/K),      W_M=sum_(K_-<=K<=K_+)omega_K,

mathcalA_I(M)=W_M^(-1)sum_(K_-<=K<=K_+)omega_K
                ||q_K-q_M||_2^2.                       (RA1)
```

Here `W_M=c_+-c_-+O(1/M)`.  Suppose, uniformly for all sufficiently large `M`, that

```text
mathcalA_I(M)<<_A log(2M)^b/M.                          (RA2)
```

Positivity selects an integer `M_1` in the ratio interval for which the same bound holds.  Repeat
at `M_1`, obtaining `M_0=M,M_1,M_2,...` with geometric growth bounded above and below by constants
strictly larger than one and

```text
||q_(M_(j+1))-q_(M_j)||_2
 <<_A log(2M_j)^(b/2)/sqrt(M_j).                        (RA3)
```

The unconditional PNT boundary `q_N->0` and geometric summability then give

```text
q_M=sum_(j>=0)(q_(M_j)-q_(M_(j+1))),
||q_M||_2<<_A log(2M)^(b/2)/sqrt(M).                    (RA4)
```

Thus `(RA2)` implies the block profile bound `(35c)` and RH.  Conversely RH gives the pointwise
bound in `(RA4)` with a logarithmic power, uniformly on compact ratio intervals, hence gives
`(RA2)`.  It also recovers `(35m20)` for every prescribed fixed ratio by the triangle inequality.
So a critical positive ratio average merely permits an adaptive geometric chain before returning
the fixed-ratio endpoint; it is paper-level RH-equivalent.

The exact Green form explains why ordinary column tiling does not prove `(RA2)`.  From
`q_K-q_M=sum_(M<=N<K)kappa_N`, one obtains

```text
W_M mathcalA_I(M)
 =sum_(M<=N,N'<K_+) G_I(N,N')<kappa_N,kappa_(N')>,      (RA5)

G_I(N,N')
 =sum_(K_-<=K<=K_+,K>max(N,N'))omega_K
 =[log((K_++1)/max(K_-,N+1,N'+1))]_+.                  (RA6)
```

The diagonal is admissible by `(35g)`--`(35h)`.  The open part is the signed cross-column Green
correlation.  The zero-mass law `(35m14)` uses a complete column with constant weight, whereas
`G_I` depends on `max(N,N')` and the endpoint interval cuts partial columns.  Double summation by
parts therefore recreates the cumulative Brownian-bridge kernel `(35m24)`; deleting the cross
terms or applying Cauchy loses the same factor `M` as `(35m29)`.

Positive mixing also preserves the lowest obstructing spatial mode.  On a common unclipped
interior, uniform continuous averaging in `c` gives, with `a=|u-v|`,

```text
bar(K)_I(u,v)
 =((c_+-a)_+^2-(c_--a)_+^2)/(2(c_+-c_-))
  -(c_+^3-c_-^3)/(3A(c_+-c_-)),                        (RA7)

bar(K)_I(u,v)=sum_(k!=0)bar(lambda)_k exp(2 pi i k(u-v)/A),
bar(lambda)_k=(c_+-c_-)^(-1)integral_(c_-)^(c_+)
                   |hat(1_(0,c))(k)|^2 dc>0.           (RA8)
```

In particular `bar(lambda)_1` is bounded below by a positive constant depending only on the ratio
interval.  The Riemann-grid witness in `(35m28)`--`(35m29)` still gives operator norm `>>M`.
Arbitrary positive ratio weights only replace `(RA8)` by another positive average of squared
multipliers and cannot cancel this mode.

Via `(35m20e)`, `(RA2)` is exactly a critical bound for a ratio-averaged centered multiplicative
Selberg integral.  Saffari--Vaughan's unconditional estimate

```text
J_psi(X,H)<<H^2X exp[-c(log X/loglog X)^(1/3)]
```

in its zero-density range gives only an `M^(-o(1))` normalized saving when `H asymp X`; `(RA2)`
requires `M^(-1)` up to logarithms.  Their RH estimate has exactly the missing power
([paper](https://aif.centre-mersenne.org/item/10.5802/aif.649.pdf), Lemmas 5--6).  Averaging the
principal translated endpoint does not create the character/modulus separation of BDH.

`[FALSIFIED METHOD]` Nonnegative ratio mixing plus complete-column tiling as a provider for the
endpoint.  Its critical estimate is already RH-equivalent, and its averaged kernel retains the
factor-`M` first-mode obstruction.

`[POSITIVE SALVAGE]` The adaptive-ratio telescoping principle classifies a whole family of exact
equivalent checkpoints: a pointwise-in-`M` critical ratio average on any compact subinterval of
`(1,exp(A))` is equivalent to RH.  Any genuinely new provider must instead join the arithmetic
source before the positive square; the future-dressed signed `delta_h` trace remains the open core.

## 2026-07-18 future-dressed root Fourier audit and the reducible-branch wall

`[EXACT POISSON/CRT BRIDGE] [SUPPORT-DEPENDENT ZERO MODE PAPER-PROVED]`
`[UNIFORM ROOT-SUM CANCELLATION REFUTED] [CLASSICAL LARGE-SIEVE CLOSURE REFUTED]`

The fixed-gap defect has an exact Fourier resolution.  Write

```text
e(x)=exp(2 pi i x),
hat(W)_h(xi)=integral_R W_h(x)e(-xi x)dx,

S_(l,h)(k)=sum_(r mod l,l|r(r+h))e(k r/l).
```

Poisson summation on each residue progression gives, with no remainder,

```text
delta_h(e_l)=l^(-1)sum_(k!=0)hat(W)_h(k/l)S_(l,h)(k).  (PF1)
```

For squarefree `l`, put `g=(l,h)`, `q=l/g`, and `h_0=h/g`.  The primes in `g` force the root to
zero and the other primes choose one of the two branches.  If `q_p=q/p` and
`bar(q_p)q_p=1 mod p`, CRT gives

```text
S_(l,h)(k)=S_(q,h_0)(k)
 =product_(p|q)[1+e_p(-k h_0 bar(q_p))],               (PF2)

|S_(l,h)(k)|<=2^omega(q)=nu_h(l),
|S_(l,h)(k)|=nu_h(l)                    when q|k,

sum_(k mod q)|S_(l,h)(k)|^2=q 2^omega(q).              (PF3)
```

There is average square-root cancellation in the frequency residue, but no uniform Weil-type
bound.  Averaging the square over the moving gap is also exact:

```text
sum_(h mod l)|S_(l,h)(k)|^2
 =product_(p|l,p does not divide k)(2p-3)
  product_(p|l,p divides k)(4p-3).                     (PF4)
```

The reason is structural, not a weakness of `(PF2)`.  On `(Z/lZ)^2` define

```text
G_l(m,h)=1_(l|m(m+h))-nu_h(l)/l,

mathcalF_l G_l(a,b)
 =sum_(m,h mod l)G_l(m,h)e(-(a m+b h)/l).
```

Changing variables to `n=m+h` and factoring by CRT gives

```text
mathcalF_l G_l(0,b)=0,

mathcalF_l G_l(a,b)
 =product_(p|l)[p 1_(p|b)+p 1_(p|b-a)-1]
                                                   (a!=0 mod l). (PF5)
```

Thus density centering removes the entire `a=0` line, not the two branch ridges `b=0` and `b=a`.
For `(a,l)=1`,

```text
mathcalF_l G_l(a,0)=mathcalF_l G_l(a,a)=phi(l).         (PF6)
```

After multiplication by the external lcm coefficient `mu(l)`, the local symbol is

```text
mu(l)mathcalF_l G_l(a,b)
 =product_(p|l)[1-p 1_(p|b)-p 1_(p|b-a)].              (PF7)
```

In the fully generic sector `p does not divide b(b-a)` for every `p|l`, the Möbius sign disappears
and the normalized Fourier coefficient is `+1/l^2`.  On either global ridge its magnitude is
`phi(l)/l^2`, essentially `1/l`.  Positive separation of the ridge and generic sectors therefore
destroys the cancellation one needs; a source-independent square-root root-sum theorem is false.

There is one narrower harmless term which the finite transform isolates.  Extend `W_h` by zero,
put

```text
mathcalW_l(a,b)=sum_(m,h in Z)W_h(m)e((a m+b h)/l),
Delta_l=sum_h delta_h(e_l).
```

Then normalized finite Fourier inversion gives

```text
Delta_l=l^(-2)sum_(a!=0 mod l,b mod l)
                    mathcalF_l G_l(a,b)mathcalW_l(a,b)+Q_l,

Q_l=sum_h nu_h(l)/l [sum_m W_h(m)-integral_R W_h].     (PF8)
```

Since the bracket is bounded by `Var(W_h)` and
`sum_(l|Q_z)2^omega(l)/l<<log(z)^2`, the complete future packet of `Q_l` is
`O(log(M)^O(1)/M)`.  Hence ordinary lattice-versus-integral quadrature is discharged.  The open
content is the main spectral term, whose two ridges are the one-dimensional endpoint marginals

```text
mathcalW_l(a,0)=sum_m [sum_h W_h(m)]e(a m/l),
mathcalW_l(a,a)=sum_n [sum_m W_(n-m)(m)]e(a n/l).       (PF9)
```

The root transform must also retain the prime order and physical support.  For the future-dressed
first crossing

```text
F_p=product_(q>p)(I-Lscr_q) Q_D Lscr_p P_D v_(<p),
```

expansion of the earlier and future Boolean factors yields exactly

```text
delta_h(F_p)
 =sum_(a|P_<p,D/p<a<=D)mu(a)
   sum_(b|P_>p)mu(b)/(p a b)
     sum_(k!=0)hat(W)_h(k/(p a b))S_(pab,h)(k),         (PF10)

-sum_p delta_h(F_p)
 =sum_(l|Q_z,l>D)mu(l)delta_h(e_l).                    (PF11)
```

Every `l>D` has a unique first crossing.  Formula `(PF10)` is an invertible triangular Duhamel
change of basis, not an estimate.  More sharply, for the physical length `H=H_h`, `(35m59)` gives

```text
delta_h((P_H-P_D)v_z)+beta_h(Q_Hv_z)
 =-sum_p[delta_h(P_HF_p)+beta_h(Q_HF_p)].              (PF12)
```

Each term `l=pab` in `(PF12)` uses two different Fourier laws:

```text
D<l<=H:  delta_h(e_l)=l^(-1)sum_(k!=0)hat(W)_h(k/l)S_(l,h)(k),

l>H:     beta_h(e_l)=l^(-1)sum_(k in Z)hat(W)_h(k/l)S_(l,h)(k). (PF13)
```

This zero-mode switch is forced by active support.  Extending the `k!=0` formula through `l>H`
subtracts `J_h nu_h(l)/l` from inactive channels and recreates the Bernoulli/Euler vacuum rejected
in `(DV5)`--`(DV6)`.  Keeping `k=0` makes an empty channel cancel exactly, but the switch at `H_h`
is endpoint-dependent and not multiplicative.

The quantitative wall is now visible without analogy.  The regularity `(35m51)` implies

```text
|hat(W)_h(xi)|
 <<min(||W_h||_1,Var(W_h)/|xi|,Var(W_h')/|xi|^2).       (PF14)
```

For a complete-period dyadic range `l asymp L<=H_h`, `(PF1)` and the last bound give

```text
|delta_h(e_l)|<<nu_h(l)l Var(W_h'),

sum_h sum_(l asymp L)|delta_h(e_l)|
 <<L^2 log(M)^O(1)/M^2.                                (PF15)
```

This reaches the admissible `log(M)^O(1)/M` scale precisely for `L<=sqrt(M)`, reproducing the
already-proved cutoff `(35m51)`--`(35m52)`.  For `l asymp L`, the branch frequencies `k/l` have
Farey spacing `asymp L^(-2)`, so the optimal classical large-sieve constant on an `M`-long window
is

```text
M+L^2.                                                  (PF16)
```

Above `sqrt(M)` it loses the energy factor `1+L^2/M`, reaching a full factor `M` at `L asymp M`.
For `l>H_h`, there are `asymp l/H_h` modes with `|k|/l<=1/H_h` on which `(PF14)` gives no decay;
together with the zero mode they reconstruct the exact zero-or-one endpoint hits.

This boundary agrees with the primary literature rather than improving it.  The optimal spacing
scale is the Montgomery--Vaughan large sieve
([paper](https://doi.org/10.1112/S0025579300004708)); sparse-moduli variants require distribution
absent from the dense squarefree-smooth packet
([Baier](https://arxiv.org/abs/math/0508417)).  Hooley-type and CRT equidistribution theorems,
including Martin--Sitar's treatment of reducible quadratics
([paper](https://arxiv.org/abs/0903.1834)) and Kowalski--Soundararajan's typical-modulus theorem
([paper](https://arxiv.org/abs/2003.12965)), do not give a uniform two-variable, future-dressed
signed estimate at the `M^(-1)` scale.  Nondegenerate quadratic/cubic root estimates likewise do
not remove the explicit reducible ridges `(PF6)`
([Ngo](https://arxiv.org/abs/2107.13301), [Welsh](https://arxiv.org/abs/1809.05211)).

Two exact sums prove that centering the ridges cannot be the missing repair.  With

```text
P_z(n)=sum_(d|Q_z,d|n)mu(d),
```

the complete Möbius sum of the fixed-gap centered symbol is

```text
sum_(l|Q_z)mu(l)G_l(m,h)
 =P_z(m)P_z(m+h)-S_z(h).                               (PF17)
```

Thus `(PF5)` is literally the spectral rewrite of the Euler-completed singular-series discrepancy
`(35m34)`--`(35m39)` and `(DV5)`, not a smaller source.  In product variables `x=m`, `y=m+h`, a
two-sided ANOVA centering looks stronger.  Put

```text
f_l(x,y)=1_(l|x y),
A_l(x)=l^(-1)sum_(y mod l)f_l(x,y)=gcd(x,l)/l,
c_l=l^(-2)sum_(x,y mod l)f_l(x,y)=b(l)/l,
h_l(x,y)=f_l(x,y)-A_l(x)-A_l(y)+c_l.                   (PF18)
```

It kills both global CRT axes.  But multiplicativity gives exactly

```text
sum_(l|Q_z)mu(l)A_l(x)=V_z P_z(x),
sum_(l|Q_z)mu(l)c_l=V_z^2,

sum_(l|Q_z)mu(l)h_l(x,y)
 =(P_z(x)-V_z)(P_z(y)-V_z).                            (PF19)
```

On the active range `P_z` is the exact Eratosthenes prime detector.  Hence deleting both ridges
manufactures the homogeneous Euler centering whose macroscopic terminal mismatch is `(35m55)`;
the removed one-variable axes are precisely its indispensable inhomogeneous correction.

`[FALSIFIED METHODS]` Uniform local square-root cancellation for `S_(l,h)`, classical or sparse
root large-sieve closure above `sqrt(M)`, and positive separation of the two branch ridges from the
generic CRT sector.  A two-sided ANOVA centering can delete the ridges only by reinserting the two
marginal currents `(PF9)`; `(PF19)` shows exactly that this relocates the rough endpoint rather than
estimating it.

`[POSITIVE SALVAGE]` Equations `(PF8)` discharges the scalar lattice quadrature.  More importantly,
`(PF5)`--`(PF13)` provide a sharp discriminator for the remaining theorem: it must cancel the
`b=0` and `b=a` resonance ridges against the generic and mixed CRT sectors only after future
Boolean dressing, the causal endpoint source, the complete-period middle, and the physical
zero-mode switch have joined.  This is a more explicit Fourier face of the same signed
interval-local causal/coarea core, not a narrower proof or a new RH theorem.

### Named open core: future-dressed causal ridge joining `(FCRJ)`

For later hostile tests, the exact remaining scalar can now be named without an arbitrary
residual.  Let `H_h=#I_h` and retain the canonical first-crossing packets `F_p`.  Define

```text
FCRJ_M
 =sum_h {J_h omega_h(P_(H_h)v_z)
          -sum_p[delta_h(P_(H_h)F_p)+beta_h(Q_(H_h)F_p)]}. (PF20)
```

Equations `(DV6)` and `(PF12)` give identically

```text
FCRJ_M
 =sum_h[J_h omega_h(P_Dv_z)+beta_h(Q_Dv_z)]
 =C_M+O_(A,rho)(log(M)^O(1)/M).                        (PF21)
```

The second equality is the already-proved low-lcm progression and `h`-quadrature reduction
`(35m52)`--`(35m53)`.  Consequently

```text
|FCRJ_M|<<_(A,rho)log(M)^b/M                           (FCRJ)
```

is an exact paper-level RH-equivalent checkpoint, not an input to assume.  A genuine provider for
`(FCRJ)` must be fixed before reading `C_M` and must derive the cancellation in `(PF20)` from the
causal prime filtration itself.  It must fail the log-phase and generalized-prime burst sources,
retain the two CRT ridges and their mixed sectors until signed joining, and respect the `k=0`
switch at every moving `H_h`.

## 2026-07-18 stopped ANOVA compensator and support-commutator no-go

`[PAPER-PROVED NO-GO] [PHYSICAL LCM CUTOFF IS NOT A STOPPING TIME]`
`[PREDICTABLE QUADRATIC VARIATION HAS MACROSCOPIC EULER SCALE]`

The moving physical cutoff cannot be inserted into the prime filtration by optional stopping.  On
the Boolean lcm module put

```text
T_p=I-Lscr_p,                 v_z=product_(p<=z)T_p e_1,
P_H e_l=1_(l<=H)e_l,         Q_H=I-P_H.
```

The range of `P_H` is not an lcm subalgebra.  Its exact commutator with prime adjunction is

```text
C_(p,H):=[P_H,T_p]=Lscr_pP_H-P_HLscr_p,
C_(p,H)e_l=1_(l<=H<p l)e_(p l).                         (ST1)
```

For ordered primes and `v_(<p)=product_(q<p)T_qe_1`, define

```text
F_(p,H)=product_(q>p)T_q C_(p,H)v_(<p).
```

Then telescoping gives exactly

```text
Q_Hv_z=-sum_p F_(p,H),
P_Hv_z=v_z+sum_p F_(p,H).                              (ST2)
```

Thus the boundary commutator forced by a putative stopping theorem is already the future-dressed
first-crossing packet `(35m59)` and `(PF12)`.

The same classification holds for the two CRT ridges.  In product variables use `f_l,A_l,c_l,h_l`
from `(PF18)` and put

```text
mathcalE(e_l)=f_l,
mathcalR(e_l)=A_l(x)+A_l(y)-c_l.
```

The unique field which applies two-sided ANOVA centering for `l<=H` but retains the raw physical
zero mode for `l>H` is

```text
mathcalK_H
 =sum_(l|Q_z)mu(l)[1_(l<=H)h_l+1_(l>H)f_l]
 =mathcalE(v_z)-mathcalR(P_Hv_z)

 =(P_z(x)-V_z)(P_z(y)-V_z)-sum_p mathcalR(F_(p,H)).    (ST3)
```

Waiting until after future dressing therefore changes only the allocation.  The invariant total
is the homogeneous Euler centering `(PF19)` plus the exact first-crossing marginal/endpoint
correction.  Deleting the correction is the rough mismatch `(35m55)`; evaluating it is the open
one-dimensional ridge current `(PF9)`.

There is a universal version of this identity.  For any linear compensator `mathcalR`, any
`D<=H`, and the `D`-first-crossing packets `F_p`,

```text
mathcalR(P_Hv_z)
 -sum_p[(beta_h-mathcalR)(P_HF_p)+beta_h(Q_HF_p)]
 =mathcalR(P_Dv_z)+beta_h(Q_Dv_z).                     (ST4)
```

Taking `mathcalR=J_h omega_h` gives `(DV3)`--`(DV6)` and `(PF20)`--`(PF21)`; taking the ANOVA ridge
functional gives `(ST3)`; choosing an empirical `W_h`-dependent functional reads the endpoint
floor counts.  Future dressing cannot improve the direct low/high splice by choosing a fourth
compensator.

Positive martingale energy also lands at the wrong scale.  Under the complete two-dimensional CRT
product law, let for `p_j`

```text
r_j=1/p_j,       X_j=1_(p_j|x),       Y_j=1_(p_j|y),
eta_j^x=X_j-r_j, eta_j^y=Y_j-r_j,
V=product_j(1-r_j),

c_j^x=V_(>j)P_(j-1)(x),
U_(j-1)^x=V_(>=j)P_(j-1)(x)-V,
```

and similarly in `y`.  The Doob martingale of
`N=(P_z(x)-V)(P_z(y)-V)` has exact difference

```text
dN_j=-U_(j-1)^x c_j^y eta_j^y
      -U_(j-1)^y c_j^x eta_j^x
      +c_j^x c_j^y eta_j^x eta_j^y,                   (ST5)
```

with predictable quadratic variation

```text
d<N>_j
 =r_j(1-r_j)[(U^x c^y)^2+(U^y c^x)^2]
  +r_j^2(1-r_j)^2(c^x c^y)^2,

E<N>_terminal=V^2(1-V)^2.                              (ST6)
```

The first two history terms are the mixed-prime sectors.  Removing them changes `(PF19)`, while
retaining and squaring them gives the macroscopic `V_z^2 asymp1/log(M)^2` Euler scale rather than
`log(M)^O(1)/M`.

Under the fixed-gap CRT law, the prime coordinates

```text
Z_j=1_(p_j does not divide x(x+h)),
s_(j,h)=1-nu_h(p_j)/p_j
```

are independent.  With `S_(>j,h)=product_(k>j)s_(k,h)` and
`R_(j-1)=product_(i<j)Z_i`, the canonical Doob martingale has

```text
dM_j=S_(>j,h)R_(j-1)(Z_j-s_(j,h)),
d<M>_j=S_(>j,h)^2R_(j-1)s_(j,h)(1-s_(j,h)).            (ST7)
```

Its centered terminal is exactly
`P_z(x)P_z(x+h)-S_z(h)`, the Bernoulli completion `(PF17)` with both ridges intact.  On the graph
`y=x+h` there is no independent two-variable ANOVA filtration; conditioning with the empirical
weight `W_h` instead makes the initial mean `beta_h` itself and reads the endpoint.

`[FALSIFIED METHODS]` Optional stopping at `H_h`, stopped two-sided ANOVA, and positive predictable
quadratic variation as providers.  The first is the forced commutator `(ST1)`, the second is
`(ST3)`--`(ST4)`, and the third either gives the rough Euler scale or squares the boundary crossing
before future signs join, which also fails the equal-log burst test `(35m66)` and fixed log phases.

`[POSITIVE SALVAGE]` Equations `(ST1)`--`(ST4)` classify every natural stopped compensator in these
coordinates.  Any surviving prime-filtration theorem must estimate the signed boundary commutator
after future dressing; it cannot invoke optional stopping or a positive quadratic variation to
create the missing `FCRJ` trace.

## 2026-07-18 modern multiplicative-correlation scale audit

`[PRIMARY-LITERATURE NO-GO] [LOGARITHMIC OR QUALITATIVE SAVINGS MISS M^(-1)]`
`[MINOR-ARC SUBPACKET CONTROLLED ONLY AT A WEAK SCALE]`

Modern averaged-correlation results do not reach the normalization of `FCRJ`.  In the physical
notation the joined packet is

```text
mathcalT_M
 =sum_h[J_h omega_h(P_(H_h)v_z)+beta_h(Q_(H_h)v_z)
         +delta_h((P_(H_h)-P_D)v_z)],                  (MC1)
```

equivalently `(PF20)` after future-dressed expansion.  The weight bounds give

```text
||W_h||_infinity<<log(M)^2/M^2,
#{(m,h) in the active support}=O(M^2).                 (MC2)
```

Thus the unstructured full scale is order one, while the endpoint requires

```text
mathcalT_M<<_(A,rho)log(M)^B/M.                        (MC3)
```

There are two incompatible ways to compare `(MC1)` with the literature.  Summing the Boolean
coefficients first gives exactly

```text
beta_h(v_z)=sum_m W_h(m)P_z(m)P_z(m+h),                (MC4)
```

and `P_z` is the ordinary-prime detector on the active range.  This is a `Lambda Lambda`-type
correlation after restoring the logarithmic weights, not a `mu(m)mu(m+h)` correlation: the Möbius
coefficient in `(MC1)` lives on the divisor variable `l`.  Keeping `l` instead exposes every
squarefree `z`-smooth modulus through `K^2`, ordered future dressing, two CRT ridges, and the moving
`H_h` zero-mode switch.  Those are growing-complexity data outside fixed-complexity
Chowla/Elliott, nilsequence, and Gowers-uniformity theorems.

The closest direct prime-correlation input is Matomaki--Radziwill--Tao's averaged-shift theorem.
In the range

```text
X^(8/33+epsilon)<=H<=X^(1-epsilon),
```

it saves every fixed power of `log X` in the averaged `Lambda(n)Lambda(n+h)` error
([paper](https://arxiv.org/abs/1707.01315)).  Even granting the most favorable partial summation
against `W_h` and covering needed gap blocks, this normalizes only to

```text
O_A(log(M)^(-A)).                                      (MC5)
```

For every fixed `A,B`,

```text
log(M)^(-A)/(M^(-1)log(M)^B)=M/log(M)^(A+B)->infinity. (MC6)
```

The availability of every fixed `A` does not permit `A=A(M)`, and macroscopic gaps at the edge of
the fixed-ratio support are not a stronger range of that theorem.

The other primary results stop at the same or a weaker boundary:

- averaged Chowla for Liouville gives a quantitative `o(1)` saving, roughly of
  `loglog(H)/log(H)` type in its natural normalization, not `M^(-1)`
  ([Matomaki--Radziwill--Tao](https://arxiv.org/abs/1503.05121));
- Tao's logarithmically averaged two-point Elliott theorem requires a dilation
  `omega(X)->infinity`, whereas the present aperture ratio is fixed, and in any event yields only
  normalized `o(1)` ([paper](https://arxiv.org/abs/1509.05422));
- fixed-shift generalized logarithmic limits are qualitative and have no uniform critical rate
  ([Tao--Teravainen](https://arxiv.org/abs/1708.02610));
- higher uniformity of bounded multiplicative functions gives averaged `o(1)` Gowers norms
  ([MRTTZ](https://arxiv.org/abs/2007.15644));
- quantitative finite-complexity prime Gowers theory has double-logarithmic rather than
  `M^(-1)` error ([Tao--Teravainen](https://arxiv.org/abs/2107.02158));
- Möbius--nilsequence orthogonality gives arbitrary fixed logarithmic savings only at fixed
  nilsequence complexity, unlike the growing rational denominator and future-prime data here
  ([Green--Tao](https://arxiv.org/abs/0807.1736)).

The sharp short-interval nilsequence decomposition likewise separates the wrong object.
Matomaki--Shao--Tao--Teravainen control `Lambda-Lambda^sharp` against nilsequences with fixed
logarithmic savings for every interval of length `H>=X^(5/8+epsilon)`; the almost-all sequel reaches
`H>=X^(1/3+epsilon)`
([all intervals](https://arxiv.org/abs/2204.03754),
[almost all](https://arxiv.org/abs/2411.05770)).  But `Lambda^sharp` retains the structured
major-arc/singular-series component, exactly where the CRT ridges and causal endpoint source live.
Generalized von Neumann estimation of the residual separately deletes the ridge--generic cross
cancellation required by `(PF5)`--`(PF13)`.

There are two honest positive residues.  First, after collapsing the Boolean filtration, all terms
with at least one `Lambda-Lambda^sharp` factor are controllable at the weak scale
`O_A(log(M)^(-A))`; this is a real minor-arc theorem, but not an admissible endpoint estimate and
not a causal provider.  Second, the crude bound for one fixed gap is `O(log(M)^2/M)`, so any
preassigned set of at most `log(M)^C` gaps is already within the endpoint budget.  The unresolved
packet is necessarily a macroscopic family of gaps, not finitely or polylogarithmically many
exceptional shifts.

`[FALSIFIED METHODS]` Direct Chowla/Elliott substitution, fixed-complexity Gowers transference,
and estimating the structured and uniform prime pieces separately as proofs of `(MC3)`.  They
either act on the wrong Möbius variable, erase future/physical support, or miss a full power of
`M`.

`[POSITIVE SALVAGE]` The minor-arc and polylogarithmic-gap packets above are unconditional, but the
surviving theorem must be an **oriented major-plus-minor correlation law**: it must retain the
structured ridges, generic and mixed sectors, future prime order, complete-period middle,
support-dependent zero mode, and endpoint cells inside one signed estimate.

## 2026-07-18 spectral dispersion and Kloosterman-fraction budget audit

`[PRIMARY-LITERATURE NO-GO] [OPTIMISTIC BETTIN--CHANDEE MODEL MISSES BY M^(15/16)]`
`[WELL-FACTORABLE MODULUS RESULTS DO NOT REACH THE PHYSICAL PACKET]`

The CRT root phase has a genuine Kloosterman-fraction expansion, but current spectral dispersion
does not approach the `FCRJ` scale.  In the coprime case `(h,l)=1`, split the two root branches as

```text
S_(l,h)(k)=sum_(d e=l,(d,e)=1)e_e(-k h bar(d)).         (SD1)
```

On a dyadic factor box `d asymp R`, `e asymp S`, `RS=L`, the most favorable mapping to
Bettin--Chandee's trilinear Kloosterman-fraction theorem is

```text
(M_BC,N_BC,A_BC)=(R,S,M),
alpha_d=mu(d)/d,       beta_e=mu(e)/e,
nu_h=hat(W)_h(k/(d e)).                                (SD2)
```

For `L<=H_h asymp M`, `(PF14)` gives

```text
||nu||_2<<L^2/(k^2 M^(5/2)),
||alpha||_2||beta||_2<<L^(-1/2).                       (SD3)
```

In the best balanced case `R=S=sqrt(L)`, Theorem 1 of Bettin--Chandee
([paper](https://arxiv.org/abs/1502.00769)) yields, after the optimistic identification `(SD2)`,

```text
T_(L,k)<<_epsilon k^(-3/2)M^epsilon
 [M^(-33/20)L^(59/40)+M^(-3/2)L^(23/16)].             (SD4)
```

At the two decisive scales,

```text
L=sqrt(M):  T_(L,k)<<k^(-3/2)M^(-25/32+epsilon),
L=M:        T_(L,k)<<k^(-3/2)M^(-1/16+epsilon).        (SD5)
```

The first is worse than the already-proved bounded-variation `M^(-1)` bound at the square-root
cutoff.  The second misses the endpoint by `M^(15/16)`.  Unbalanced boxes add losses such as
`R^(1/4)` or `R^(1/8)`.  The `k^(-3/2)` sum is harmless only in the complete-period range; for
`l>H_h`, the zero mode and `asymp l/H_h` low aliases in `(PF13)` must remain.  Moreover `(SD2)` has
already discarded first-crossing order and future-support dependence, so `(SD4)` is an optimistic
upper limit, not a hidden application to `FCRJ`.

Kuznetsov and arithmetic-progression technology have a structural mismatch in addition to this
power loss:

- the Deshouillers--Iwaniec spectral large sieve estimates Kloosterman forms after diagonal and
  zero modes are separated; here those modes are the `b=0`, `b=a`, and physical `k=0` pieces which
  must cancel against the generic sector and density source
  ([paper](https://eudml.org/doc/142975));
- Bombieri--Friedlander--Iwaniec reach the well-factorable level `x^(4/7-epsilon)`
  ([Theorem 10](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6385-11511_2006_Article_BF02399204.pdf)),
  Maynard reaches `x^(3/5-epsilon)` for suitably well-factorable weights
  ([paper](https://arxiv.org/abs/2006.07088)), and Pascadi reaches `x^(5/8-o(1))` for
  triply-well-factorable weights ([paper](https://arxiv.org/abs/2505.00653));
- smooth squarefree CRT-compatible modulus families reach `x^(1/2+7/300)` in Polymath
  ([paper](https://arxiv.org/abs/1402.0811)) and `x^(1/2+1/40)` in Stadlmann
  ([paper](https://doi.org/10.1016/j.aim.2025.110190)).

Even granting all theorem hypotheses, these exponents cover at most a strip above `sqrt(M)`, not
the complete `L asymp M` packet and still less the incomplete packet extending through `M^2`.
More decisively, those theorems require fixed or CRT-compatible coprime residue data and
well-factorable modulus weights.  Formula `(PF10)` contains both non-coprime axes, all
`2^omega(l)` branch colorings, moving `h`, the exact coefficient
`mu(l)1_(l|Q_z,l>D)`, future-prime order, endpoint `W_h`, and the `H_h` switch.  This high-tail
weight is not uniformly well-factorable with those clauses retained.  Removing them to fit a
theorem produces the homogeneous Euler completion `(PF19)` and its mismatch `(35m55)`.

`[FALSIFIED METHODS]` Generic Kuznetsov/Deshouillers--Iwaniec closure, trilinear
Kloosterman-fraction closure, and importing modern beyond-square-root distribution exponents as a
proof of `FCRJ`.  They either miss a polynomial power or isolate as main terms the very ridge and
zero-mode packets whose signed joining is the endpoint.

`[POSITIVE SALVAGE]` Equation `(SD4)` is a valid power-saving bridge for a smoothed,
complete-period, coprime, independently factorable off-axis dyadic subpacket.  It cannot be removed
by triangle inequality inside `FCRJ`: doing so leaves the endpoint marginals and physical zero
mode, and their cancellation with that subpacket is RH-bearing.  The next candidate must be a
source-specific causal ridge-joining theorem, not a stronger generic Kloosterman estimate.

## 2026-07-18 causally anchored alias collapse and exact probability contraction

`[NEW FINITE THEOREM FORMALIZED] [NOVELTY UNVERIFIED] [PHYSICAL CUTOFF REMAINS]`
`[LEAN-DISCOVERED HYPOTHESIS REMOVAL] [FCRJ NOT CLOSED]`

The reduced-frequency CRT identity is stronger than the primitive-fraction form suggested by
`(PF10)`.  If `(q,d)=1`, then for arbitrary integers `a,h`,

```text
S_(qd,h)(ad)=nu_h(d)S_(q,h)(a).                        (AC1)
```

No condition `(a,q)=1` is needed.  This matters causally.  In a first-crossing packet, the
first-crossing prime `p` may divide the Fourier frequency.  Fully reducing `k/l` would then move
`p` into the complementary alias modulus and erase the first-crossing color.  Equation `(AC1)`
allows `p` to remain anchored in the active denominator `q` even when `p|a`; only future
coordinates are collapsed.  Lean statement design exposed this strengthening before the analytic
regrouping was fixed.

For a complete complementary squarefree packet `N`, `(AC1)` and multiplicativity give the exact
classical divisor identity

```text
sum_(d|N) mu(qd)/(qd) S_(qd,h)(ad)
 =mu(q)/q S_(q,h)(a)
    product_(p|N)(1-nu_h(p)/p).                        (AC2)
```

The formal theorem also proves a stronger Boolean-coordinate version for arbitrary pairwise
coprime nonzero inactive moduli; neither primality of each coordinate nor a global squarefree
ambient modulus is required.

The local factors admit a complete classification.  For prime `p`,

```text
nu_h(p)=1_(p|h)+2 1_(p does not divide h),              (AC3)

1-nu_h(p)/p = (p-1)/p  if p|h,
                (p-2)/p  otherwise.                    (AC4)
```

Thus exact local annihilation occurs if and only if `p=2` and the gap is odd.  There is no
odd-prime zero.

The stronger positive structure is probabilistic.  For a finite coordinate set `S`, put

```text
theta_n=nu_h(n)/n,

w_(S,h)(T)=product_(n in T)theta_n
            product_(n in S\T)(1-theta_n),   T subset S. (AC5)
```

Root-set inclusion gives `0<=theta_n<=1` on nonzero coordinates, and finite product expansion gives

```text
w_(S,h)(T)>=0,
sum_(T subset S)w_(S,h)(T)=1.                           (AC6)
```

Consequently, for responses in any real normed space,

```text
||sum_(T subset S)w_(S,h)(T)R_T||
 <=sup_(T subset S)||R_T||.                             (AC7)
```

This removes all complete complementary alias multiplicity exactly.  It is also sharp as a
source-independent statement: a constant response attains equality, so the contraction norm is
one.  Any missing factor `M^(-1)` must come from the anchored primitive responses and their signed
source joining, not from the Euler weights alone.

Parity supplies an exact positive cutoff localization.  If `2|N` and `h` is odd, the complete
anchored family `(AC2)` vanishes.  At every physical threshold `H`,

```text
sum_(d|N,qd<=H) mu(qd)/(qd)S_(qd,h)(ad)
 =-sum_(d|N,H<qd) mu(qd)/(qd)S_(qd,h)(ad).              (AC8)
```

Therefore an odd-gap survivor is entirely a support-cutoff boundary term.  For even gaps every
local factor is positive, so there is no analogous annihilation.

`[FALSIFIED METHOD]` Treat the physical divisor truncation as if it retained the complete Euler
survival product.  The conditions `qd<=H_h` and `H_h<qd` cut the Boolean cube; the resulting
incomplete divisor remainder is not a product and can have the full boundary scale.  Likewise,
fully reducing every fraction before regrouping can erase the first-crossing prime.

`[POSITIVE SALVAGE]` Join aliases only after fixing a causal anchor containing the first-crossing
prime.  Complete complementary packets then form the exact contraction `(AC7)`, odd-gap completed
packets localize to the cutoff by `(AC8)`, and every remaining obstruction is a physically
truncated anchored primitive response.  This sits between `(PF11)` and `(PF16)`.  It sharpens the
object to be estimated but does not prove `FCRJ`: the even-gap primitive ridges, moving `H_h`
switch, endpoint cells, and signed `h,p` joining remain.

The finite theory is formalized in
`GaloisForLFunctions/RHTower/ReducedFrequencyMobiusAliasCollapse.lean`, including the divisor and
Boolean alias collapses, prime local classification, exact probability normalization and
contraction, parity annihilation, and physical-cutoff balance.  The owned-module build passes;
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the principal
theorems.

`[NEXT OPEN CORE]` Derive the anchored reindexing of the full first-crossing formula without
forgetting the prime color, then prove a source-specific interval-local bound for its truncated
primitive response.  Abstract contraction cannot provide that bound because `(AC7)` is sharp.

### Maximal anchored normal form and sectorwise future contraction

`[PAPER-PROVED REGROUPING] [LEAN FINITE CORE FORMALIZED] [CAUSAL COLOR RETAINED EXTERNALLY]`

The causal anchor can be made canonical.  Write a colored modulus as `l=c m`, where `c` contains
all protected factors of the fixed first-crossing sector and `m` is a squarefree complement with
`(c,m)=1`.  For every integer frequency `k`, put

```text
d=gcd(m,|k|),   r=m/d,   u=k/d.                        (AC9)
```

Then

```text
m=d r,   k=d u,   (d,r)=1,   (r,|u|)=1,
S_(cm,h)(k)=nu_h(d)S_(cr,h)(u).                        (AC10)
```

This is a unique anchored normal form on the complementary coordinates: every factor of `m`
dividing `k` is extracted, while every factor belonging to `c` stays active.  In general `u` may
share factors with `c`.  Thus `(AC9)` is deliberately not lowest-term reduction of the whole
fraction.  It handles negative and zero frequencies as well.

For a fixed colored sector `c`, a squarefree future packet `N`, and a finitely supported frequency
weight `F`, define

```text
T_(c,N,h)(F)
 =sum_(m|N)mu(m)/(c m)
    sum_(k!=0)F(k/(c m))S_(c m,h)(k).                  (AC11)
```

The bijection `(m,k)<->(r,u,d)` from `(AC9)` and the complete `d`-alias collapse give

```text
T_(c,N,h)(F)
 =sum_(r|N)mu(r)/(c r)V_(N/r)(h)
    sum_(u!=0,(u,r)=1)F(u/(c r))S_(c r,h)(u),          (AC12)

V_R(h)=product_(ell|R)(1-nu_h(ell)/ell).
```

Only coprimality with the future remainder `r` is imposed on `u`; factors of the causal anchor are
never reduced away.  The first-crossing prime must still remain as an outer color: the anchored
denominator `c r` alone does not identify which factor of `c` crossed first.

Set

```text
w_(N,h)(r)=nu_h(r)/r V_(N/r)(h),

B_(c,r,h)(F)=1/(nu_h(c)nu_h(r))
  sum_(u!=0,(u,r)=1)F(u/(c r))S_(c r,h)(u).            (AC13)
```

The probability law `(AC6)` becomes `sum_(r|N)w_(N,h)(r)=1`, so `(AC12)` is the signed convex
identity

```text
T_(c,N,h)(F)
 =nu_h(c)/c sum_(r|N)mu(r)w_(N,h)(r)B_(c,r,h)(F),

|T_(c,N,h)(F)|
 <=nu_h(c)/c sup_(r|N)|B_(c,r,h)(F)|.                  (AC14)
```

The abstract norm is exactly `nu_h(c)/c`; take `B_r=mu(r)`.  Hence complete future dressing is a
sharp contraction onto anchored responses, not an endpoint power saving.

For `(PF10)`, use one sector at a time with the first-crossing prime and the earlier shell retained
in `c`; only the unrestricted future packet is `N`.  This preserves the causal color externally
and collapses every redundant future alias.  It does not commute with `(PF13)`: the physical
condition becomes `c r d<=H_h` and truncates the `d`-sum inside `(AC12)`.  Its exact coefficient is
then

```text
sum_(d|N/r,c r d<=H_h)mu(d)nu_h(d)/d                  (AC15)
```

or its complementary high-tail sum, not `V_(N/r)(h)`.  The zero-mode law changes across the same
boundary.  Thus the new normal form identifies the remaining obstruction exactly as a truncated
future-coordinate boundary on each externally colored anchored response.

The identities `(AC9)`--`(AC10)` and complementary maximality are formalized as
`quadraticCongruenceRootSumTotal_causalGCDReduction` and
`causalGCDReduction_complement_coprime`.  The full finite-support regrouping `(AC12)` is a paper
corollary of those identities and the already-formalized divisor collapse.

Two formal corollaries sharpen this picture.  Every normalized root response lies in the closed
unit disk, and complementary insertion preserves it exactly:

```text
|S_(q,h)(a)|<=nu_h(q),
S_(q d,h)(a d)/nu_h(q d)=S_(q,h)(a)/nu_h(q).           (AC16)
```

Thus `(AC12)` removes literal copies of the same normalized response.  However, in a fixed
first-crossing sector the unrestricted future packet contains only primes greater than `p` and
therefore never contains the parity prime `2`.  The odd-gap annihilation `(AC8)` is a valid global
completion/cutoff theorem but is not a hidden gain inside the sectorwise future contraction.

## 2026-07-18 physical-cutoff Jordan no-go and joined-response correction

`[FALSIFIED REPRESENTATION] [PAPER-PROVED POSITIVE SALVAGE] [FCRJ PIVOT]`
`[LEAN-PROVED FINITE JOINING] [BRIDGE] [NOVELTY UNVERIFIED]`

The separately truncated anchored coefficients from `(AC15)` are not the invariant obstruction in
`(PF20)`.  Fix an anchor `c`, a squarefree complementary packet `N`, a divisor `r|N`, and write

```text
theta_h(n)=nu_h(n)/n,

A^<=(c,r;H)=sum_(d|N/r,c r d<=H)mu(d)theta_h(d),
A^>(c,r;H)=sum_(d|N/r,H<c r d)mu(d)theta_h(d),

lambda^<=_r=theta_h(r)A^<=(c,r;H),
lambda^>_r =theta_h(r)A^>(c,r;H).                      (AC17)
```

The cutoff partitions the complete complementary divisor cube, so coordinatewise

```text
lambda^<=_r+lambda^>_r
 =theta_h(r) product_(ell|N/r)(1-theta_h(ell))
 =w_(N,h)(r).                                          (AC18)
```

The two separately signed measures have the exact conserved masses

```text
sum_(r|N)lambda^<=_r=1_(c<=H),
sum_(r|N)lambda^>_r =1_(H<c),                          (AC19)
```

whereas their joined coefficient is the complete positive probability law

```text
w_(N,h)(r)>=0,
sum_(r|N)w_(N,h)(r)=1.                                 (AC20)
```

Most importantly, the low and high coefficients multiply the **same** causally anchored primitive
response `B_(c,r,h)`.  Therefore for every response packet in a real normed space,

```text
sum_(r|N)lambda^<=_r R_r+sum_(r|N)lambda^>_r R_r
 =sum_(r|N)w_(N,h)(r)R_r,

||sum_(r|N)w_(N,h)(r)R_r||<=sup_(r|N)||R_r||.          (AC21)
```

Thus negative Jordan mass of either cutoff half is decomposition-dependent.  It disappears before
estimation when the forced low/high response pieces are joined.  Treating its total variation as
the final `FCRJ` obstruction is false.

The zero mode enforces the same correction at the physical formula.  Since
`beta_h=delta_h+J_h omega_h`, equations `(PF12)`--`(PF13)` give

```text
delta_h(P_(H_h)F_p)+beta_h(Q_(H_h)F_p)
 =delta_h(F_p)+J_h omega_h(Q_(H_h)F_p).                 (AC22)
```

After the first-crossing telescoping and `D<=H_h`, the `H_h`-dependent pieces recombine exactly:

```text
FCRJ_h=J_h S_z(h)-sum_p delta_h(F_p)
      =J_h omega_h(P_Dv_z)+beta_h(Q_Dv_z).              (AC23)
```

So the physical cutoff is absent from the final nonzero-frequency response.  Its separate signed
Jordan measures are a splice gauge, not a new source estimate.

`[POSITIVE SALVAGE]` The exact low/high-to-probability joining `(AC18)`--`(AC21)` is a reusable
finite theorem: a cutoff may destroy positivity in each half while preserving a positive joined
response operator of sharp norm one.  It is Lean-proved in
`GaloisForLFunctions/RHTower/PhysicalCutoffAliasResponseJoining.lean`, including a symbolic
rank-one sign failure, coordinatewise joining, both mass laws, the arbitrary-module response
identity, and the quadratic root-density norm-one contraction.  This is the correct structural
output of the no-go, independent of `FCRJ`.

The genuine remaining object is the global density-versus-response correlation.  With
`N_p=P_>p`, `c=pa`, and the anchored response from `(AC13)`, `(PF10)` and `(AC12)` give

```text
delta_h(F_p)
 =sum_(a|P_<p,D/p<a<=D) mu(a) nu_h(pa)/(pa)
    sum_(r|N_p)mu(r)w_(N_p,h)(r)B_(pa,r,h).             (AC24)
```

Hence the first honest inequality is

```text
|sum_h [J_h S_z(h)
 -sum_(p<=z)sum_(a|P_<p,D/p<a<=D) mu(a)nu_h(pa)/(pa)
    E_(r~w_(N_p,h))[mu(r)B_(pa,r,h)]]|
 <<_(A,rho) log(M)^b/M.                                (AC25)
```

`[FRONTIER CORRECTION]` The absolute-value notation hides an unconditional half.  The exact
operator join `(HGS29)` in `high-grade-sieve-survivor-one-mode-reduction.md` writes the bracketed
global scalar as

```text
FCRJ_M=D_M-R_M=||P_M||^2-E_M,
E_M=E_prog+E_quad,                                      (AC26)
```

where `P_M` is the ordinary-prime endpoint carrier and `E_M` is already inside the allowed
quadrature budget.  Hence

```text
D_M-R_M+E_M=||P_M||^2>=0,                               (AC27)
```

with equality exactly when `P_M=0`.  Therefore the negative half of `(AC25)` is unconditional;
up to the controlled error, `(AC25)` is equivalent to the single reverse response inequality

```text
R_M>=D_M-O_(A,rho)(log(M)^b/M),                         (AC28)
```

or to the small upper bound on `||P_M||^2`.  This corrects the orientation of the open core but
does not weaken its RH-equivalent strength.  The dependency-closed theorem and novelty verdict
are recorded in
`2-fully-proven/not_new_scientific_knowledge/07-functional-analysis-operator-theory/fcrj-corrected-response-saturation-law.md`.

`[MONGE/TOTAL POSITIVITY RETIRED]` The centered full-cell Brownian kernel is inverse-Monge and has
nonnegative ordered `2x2` minors exactly in the long-aperture chamber `c>=A/2`.  Nevertheless an
exact clipped packet with `M=3,K=4` has opposite signs for its two symmetric endpoint-even
one-prime Boolean curvatures inside that favorable chamber.  Thus variation diminution of the
physical Gram does not orient `(AC28)`.  The sharp phase classification, symbolic physical
counterexample, and positive survivor are recorded in
`5-failed/brownian-monge-total-positivity-fcrj-provider.md`.

No sectorwise absolute estimate is justified.  Without the exact common physical profile `W_h`,
the primitive anchored response coordinates can be phase-aligned independently, so CRT
conjugation and causal-color retention alone cannot improve the sector total-variation norm.  Any
surviving conjecture must use the common source and the global `h,p,a,r` joining in `(AC25)`.

## Conjecture loop 58 — endpoint-charge Wiener law for physical FCRJ carrier

### Conjecture `[FROZEN 2026-08-27]`

For a finite active physical prime packet, let `B` be its distinct endpoint nodes on aperture
circle, let `j(x)` be signed prime-log endpoint jump, and define

```text
U_n = sum_(x in B) j(x) fourier_1(x)^n.                  (AC29)
```

Then

```text
lim_(N->infinity) (1/N) sum_(0<=n<N) |U_n|^2
  = sum_(x in B) |j(x)|^2.                               (AC30)
```

For every positive integer `n`, existing endpoint tomography should identify

```text
U_n = (2 pi i n/A) A_n,                                 (AC31)
```

where `A_n` is exact physical FCRJ character amplitude.  Thus every nonempty active packet with
`0<k-m<A` has strictly positive differentiated-character Cesàro mass.  Its character amplitudes
cannot decay `o(1/n)` in Cesàro mean, and no proof of `(AC28)` may discard a fixed tail as uniformly
rapid.

### Corpus basis and attack order

1. `sum_endpointCircleJump_mul_fourier` is exact identity `(AC31)`.
2. Distinct endpoint nodes have distinct unit modes under `fourier 1`.
3. `tendsto_finiteExponentialPencil_cesaro_norm_sq` supplies finite atomic Wiener identity.
4. Existing physical endpoint noncancellation supplies strict positivity of right side.
5. Hostile audit must separate this ultraviolet law from desired total-energy upper bound: an
   exact `1/n` tail is compatible with finite `L2` energy and does not itself prove `(AC28)`.

Primary audit: Wiener mean-square theorem for atomic measures and `O(1/n)` Fourier decay for
bounded-variation functions are classical.  No audited source states exact physical prime-log
endpoint law `(AC30)--(AC31)` or its FCRJ consequence.  Novelty claim, if proved, is restricted to
this coefficient-faithful source specialization and no-go boundary.

### Proof and verdict `[PAPER-PROVED] [LEAN-PROVED] [NO-GO] [POSITIVE SURVIVOR]`

The conjecture is true.  Fundamental character `fourier_1` is injective on positive-length
aperture circle and has unit norm.  Therefore endpoint moment `(AC29)` is a finite exponential
pencil with distinct unit modes.  Expanding squared modulus and Cesàro averaging kills every
off-diagonal mode ratio and retains exactly diagonal coefficient mass, proving `(AC30)`.

For positive `n`, existing endpoint differentiation identity gives `(AC31)` exactly.  Existing
physical noncancellation produces one nonzero character amplitude for every nonempty active packet
with `0<k-m<A`; because character rate is nonzero, some endpoint jump is nonzero and

```text
sum_(x in B)|j(x)|^2 > 0.                               (AC32)
```

Consequently `U_n` cannot tend to zero.  Equivalently,

```text
(2 pi i n/A) A_n  does not tend to 0,                   (AC33)
```

so physical amplitudes are not uniformly `o(1/n)` along positive integer aperture frequencies.

Lean file:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointWienerCharge.lean`.
It proves exact Cesàro law, differentiated-amplitude identity, strict jump-mass positivity, and both
nondecay theorems.  Module is wired into `RHTower.lean`; direct `lake env lean` checking passed.

Hostile limit: `(AC30)` is ultraviolet lower structure, not desired total-energy upper bound.  A
`1/n` Fourier tail remains square summable, and right side `(AC32)` varies with physical packet.
Thus theorem does not prove `(AC28)` or RH.  It retires uniform rapid-tail truncation and any fixed-
mode argument claiming high characters vanish harmlessly.  Positive survivor is a multiscale
estimate that retains exact endpoint charge while proving total Parseval energy
`O(M^-1 polylog M)` from common prime source.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: finite-atomic Wiener mean-square identity and
`O(1/n)` bounded-variation Fourier bound are classical parent results.  Corpus had endpoint
moment identity and general finite-pencil theorem separately, but not their physical FCRJ
specialization, positive jump-mass limit, or non-`o(1/n)` no-go.  No audited primary source states
this bespoke prime-log endpoint theorem.  Novelty claim is source-specific; parent harmonic
analysis is not claimed new.

Verdict: `[PROVED — EXACT FCRJ ENDPOINT WIENER CHARGE; UNIFORM RAPID FOURIER-TAIL PROVIDERS RETIRED]`.

### Formal audit `[2026-08-27]`

`lake env lean formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointWienerCharge.lean`
and targeted
`lake build GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointWienerCharge` both pass.  Scratch
`#print axioms` audits of the exact Cesàro law and both nondecay capstones report only `propext`,
`Classical.choice`, and `Quot.sound`.  Module is imported by theorem-area umbrella
`GaloisForLFunctions.RHTower`; repository formal lint passes with no active `sorry`, `admit`, new
`axiom`, `opaque`, or `unsafe` declaration.

## Conjecture loop 59 — exact FCRJ ultraviolet tail coefficient

### Failed first conjecture `[REDISCOVERED]`

Abstract implication

```text
(1/N) sum_(n<N) a_n -> L  ==>  N sum_(n>N) a_n/n^2 -> L
```

is classical Abelian partial summation, not new scientific knowledge.  Corpus supplied exact
weighted power-tail asymptotics, so generic statement was retained only as Lean infrastructure.

### Source-specific survivor `[PAPER-PROVED] [LEAN-PROVED] [NO-GO] [POSITIVE SURVIVOR]`

For endpoint moment `U_n` and jump charge `J` from `(AC29)--(AC32)`, exact fixed-packet laws are

```text
lim_(N->infinity) N sum_(n>N) |U_n|^2/n^2 = J,          (AC34)
lim_(N->infinity) N sum_(n>N) |A_n|^2
  = A^2/(4 pi^2) J.                                     (AC35)
```

Paper proof uses normalized cumulative energy `g_n=S_n/n` and exact two-kernel Abel decomposition

```text
sum_(n>=M) a_n/n^2
 = -g_M/M + sum_(j>=M) g_(j+1)/j^2
   + sum_(j>=M) [g_(j+1)j/(j+1)]/j^2.                  (AC36)
```

Both tail weights converge to `J`; corpus weighted inverse-square theorem gives limits `J+J`,
while boundary gives `-J`.  Endpoint differentiation supplies exact factor in `(AC35)`.  Character
Parseval proves required summability unconditionally.

For every nonempty active packet with `0<k-m<A`, `J>0`; therefore scaled raw-character tail cannot
converge to zero.  Fixed-packet energy is exactly order `1/N`, not `o(1/N)`.  This strictly sharpens
loop 58's pointwise nondecay and closes high-frequency decay as a source of extra FCRJ saving.

Lean file:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointUltravioletTail.lean`.
Capstones are
`tendsto_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail`,
`tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail`, and
`not_tendsto_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail_zero`.
Targeted module build, direct Lean check, axiom audit, and formal lint pass.

Hostile limit: theorem is pointwise in fixed physical packet.  It supplies no uniform rate when
prime packet, aperture, and colliding endpoint phases move with arithmetic scale.  Remaining FCRJ
burden is therefore exact two-parameter uniformity through phase-separation/collision data plus
common-source total-energy control; no further fixed-packet Fourier decay estimate can close it.

Verdict: `[PROVED — EXACT POSITIVE FCRJ ONE-OVER-N ULTRAVIOLET LAW; FIXED-PACKET EXTRA-DECAY
PROVIDERS RETIRED]`.

## Conjecture loop 60 — quantitative FCRJ endpoint phase-collision tail rate

### Failed first conjecture `[TOO COARSE]`

Controlling every off-diagonal endpoint pair by one minimum chord separation is valid but charges
all pairs at the worst collision, is awkward for singleton packets, and destroys cluster-local
information needed by moving prime apertures.  It was rejected in favor of coefficient-weighted
ordered-pair denominators.

### Pairwise survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

For distinct unit modes `z_x`, coefficients `j_x`, endpoint moment
`U_n=sum_x j_x z_x^n`, jump charge `J=sum_x|j_x|^2`, and collision budget

```text
C = sum_(x!=y) 2|j_x||j_y|/|1-conj(z_x)z_y|,
```

every `N>=1` satisfies

```text
|N sum_(n>N)|U_n|^2/n^2-J|
  <= J/(N+1)+N C/(N+1)^2.                              (AC37)
```

For the physical FCRJ amplitudes this becomes

```text
|N sum_(n>N)|A_n|^2-A^2 J/(4 pi^2)|
  <= A^2/(4 pi^2) [J/(N+1)+N C/(N+1)^2].              (AC38)
```

The proof is an exact one-step Abel telescope.  For `|w|=1`, `w!=1`, and `M>=1`,

```text
|sum_(n>=M) w^n/n^2| <= 2/(M^2 |1-w|).                 (AC39)
```

Expanding `|U_n|^2` over ordered pairs, `(AC39)` controls every off-diagonal phase; integral-test
bounds put the diagonal scaled tail between `N/(N+1)` and `1`.  This gives `(AC37)` with no hidden
cardinality or minimum-separation loss.  Exact endpoint differentiation gives `(AC38)` termwise.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointPhaseCollisionTailRate.lean`.
It proves `(AC39)`, the generic finite-pencil theorem, the exact physical endpoint budget, and
both physical bounds.  Direct `lake env lean`, targeted module build, axiom audit, umbrella wiring,
and global formal lint pass.  Stage-3 card:
`docs/drafts/pipeline/3-formalized/fcrj-endpoint-phase-collision-tail-rate.md`.

Hostile limit: `C_M=o(N_M)` is now an explicit sufficient moving-packet condition, not a proved
arithmetic fact.  Near-colliding prime-log endpoints can make absolute pairwise cost large even
when signed clusters cancel.  Remaining producer is therefore a source theorem bounding physical
collision budget, or a sharper cluster-renormalized invariant, together with common-source total
energy control.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: Abel estimate `(AC39)` and quantitative
finite-atomic Wiener arguments are classical infrastructure.  Corpus and targeted literature
search found no physical clipped prime-log endpoint formula `(AC37)--(AC38)` or its explicit
moving-packet criterion.  Candidate-new claim is restricted to this coefficient-faithful source
specialization and exact obstruction.

Verdict: `[PROVED — EXPLICIT FCRJ PHASE-COLLISION RATE; MOVING-PACKET CORE REDUCED TO SOURCE
COLLISION GROWTH OR SIGNED CLUSTER CANCELLATION]`.

## Conjecture loop 61 — frequency-resolved FCRJ collision saturation

### Failed predecessor `[SINGULAR FRONTIER INVARIANT]`

Loop 60's inverse-chord cost is correct but diverges when two distinct modes approach within the
frequency resolution `1/N`.  Actual scaled pair tail stays bounded there, so raw collision budget
overprices precisely the clusters relevant to moving packets.

### Saturated survivor `[PAPER-PROVED] [LEAN-PROVED] [SHARP BOUNDARY] [POSITIVE SURVIVOR]`

For loop-60 notation define frequency-resolved budget

```text
R_N = sum_(x!=y) |j_x||j_y|
        min(1, 2N/(|1-conj(z_x)z_y|(N+1)^2)).          (AC40)
```

Then every `N>=1` satisfies

```text
|N sum_(n>N)|U_n|^2/n^2-J| <= J/(N+1)+R_N,            (AC41)
```

and raw physical FCRJ amplitudes obey the same right side multiplied by `A^2/(4 pi^2)`.

Proof takes the minimum of two exact scalar controls:

```text
|sum_(n>N)w^n/n^2|
 <= min(1/N, 2/(|1-w|(N+1)^2)).                       (AC42)
```

First branch is absolute inverse-square mass; second is Abel oscillation `(AC39)`.  Pairwise
finite-pencil expansion and diagonal integral bounds give `(AC41)`.  Thus pairs with
`N|1-w|<<1` cost at most full coefficient mass, while resolved pairs retain inverse-chord decay.
Singleton cost is zero, and no minimum separation appears.

Lean additions in
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointPhaseCollisionTailRate.lean` prove
`(AC42)`, generic resolved budget, physical endpoint specialization, and raw-amplitude theorem.
Direct checking, targeted build, axiom audits, umbrella wiring, and global formal lint pass.
Stage-3 card:
`docs/drafts/pipeline/3-formalized/fcrj-endpoint-resolved-collision-tail-rate.md`.

Hostile limit: absolute resolved pair mass still discards cancellation among three or more signed
near-colliding nodes.  Arithmetic core is now sharper: control weighted unresolved clusters and
resolved inverse-chord pairs, or replace them by a signed cluster multipole invariant.  An
arbitrarily small chord alone is no longer an obstruction.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: both scalar branches of `(AC42)` are
classical.  Corpus and targeted current literature search found no pairwise saturated
inverse-square Wiener law or physical clipped prime-log endpoint version.  Candidate-new content
is exact source specialization, resolution-scale boundary, and revised moving-packet obstruction.

Verdict: `[PROVED — PHASE COLLISIONS SATURATE AT FULL PAIR MASS BELOW 1/N RESOLUTION; REMAINING
FCRJ CORE IS WEIGHTED CLUSTER MASS OR SIGNED MULTIPOLE CANCELLATION]`.

## Conjecture loop 62 — physical primewise dipole multipole bound

### Failed first conjecture `[SOURCE-DISCONNECTED]`

An abstract zero-sum assumption on arbitrary endpoint clusters can improve loop 61, but source
does not canonically supply such a partition. Adding one would hide arithmetic burden inside an
unproved premise. Literal source instead pairs two endpoints produced by each prime.

### Primewise survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

For finite prime aperture `P`, write

```text
W = sum_(p in P) log(p)/p,
D = sum_(p in P) (log(p)/p)|z_end(p)-z_start(p)|,
U_n = sum_x j_x z_x^n.
```

Physical endpoint source satisfies, with no activity or separation premise,

```text
sum_x j_x = 0,                                           (AC43)
|U_n| <= n D,                                            (AC44)
|U_n| <= min(n D, 2W).                                   (AC45)
```

Exact endpoint aggregation writes `U_n` prime by prime as

```text
sum_(p in P) (log(p)/p)(z_end(p)^n-z_start(p)^n).
```

Constant test function proves `(AC43)`. Unit-circle power Lipschitz estimate
`|z^n-w^n|<=n|z-w|` proves `(AC44)`; trivial unit bound gives `|U_n|<=2W`, and taking minimum
yields `(AC45)`. Thus unresolved physical mass is dipolar before any cluster choice: short
endpoint arcs cost weighted chord `D`, not full two-endpoint mass.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointDipoleMultipoleBound.lean`.
Direct `lake env lean`, targeted module build, axiom audit, umbrella wiring, and global formal lint
pass. Stage-3 card:
`docs/drafts/pipeline/3-formalized/fcrj-primewise-dipole-multipole-bound.md`.

Hostile limit: `(AC45)` is pointwise. Its low branch grows like `nD`; summing it through entire
inverse-square tail diverges, while high branch alone recreates a `1/N` mass bound. Next source
problem is exact low/high split converting both branches into a quantitative tail law, followed by
arithmetic control of `D` and `W` across moving apertures.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: zero-mass signed-measure Fourier control by
first transport moment is classical. Corpus and targeted literature search found no exact clipped
prime-log identity `(AC43)--(AC45)` or use of literal primewise dipoles in FCRJ ultraviolet
control. Candidate-new content is restricted to this source specialization and its replacement of
unresolved endpoint mass by weighted chord.

Verdict: `[PROVED — PHYSICAL FCRJ SOURCE IS EXACTLY PRIMEWISE DIPOLAR; UNRESOLVED MOMENTS OBEY
THE CLIPPED MULTIPOLE LAW]`.

## Conjecture loop 63 — primewise dipole inverse-square transport energy

### Failed first conjecture `[HARMONIC DIVERGENCE]`

Pointwise geometric interpolation between `|U_n|<=nD` and `|U_n|<=2W` gives
`|U_n|^2/n^2<=2WD/n`. Its harmonic majorant diverges, so it cannot control complete ultraviolet
energy. A source-scale frequency split is essential.

### Transport-energy survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

With loop-62 total weight `W`, weighted primewise chord `D`, and every `N>=1`,

```text
sum_(n>N) |U_n|^2/n^2 <= 4 W D,                         (AC46)
N sum_(n>N) |U_n|^2/n^2 <= 4 N W D.                     (AC47)
```

More precisely, every natural split length `L` satisfies

```text
sum_(n>N) |U_n|^2/n^2 <= L D^2 + 4W^2/(N+L).            (AC48)
```

Proof uses loop 62 on first `L` frequencies and reciprocal-square telescope on remainder. Source
geometry gives `0<=D<=2W`. If `D=0`, every moment vanishes. Otherwise set
`L=floor(2W/D)`: then `LD<=2W` and, because `N>=1`, `2W<=(N+L)D`. Each term in `(AC48)` is at most
`2WD`, proving `(AC46)--(AC47)`. Exact endpoint differentiation transports `(AC47)` to raw FCRJ
character energy with multiplier `A^2/(4 pi^2)`.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointDipoleInverseSquareEnergy.lean`.
Direct `lake env lean`, targeted module build, axiom audit, and umbrella wiring pass. Global formal
lint is temporarily blocked by unrelated concurrently owned sieve-module reachability, so card
remains Stage 2 until that repository-wide gate clears.

Hostile limit: `(AC46)` eliminates phase separation and arbitrary unresolved-cluster mass from
physical tail control, but moving-packet vanishing still requires arithmetic `N W D -> 0`. This is
strictly more source-local than loop 61: only total prime weight and literal within-prime endpoint
transport remain.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: Fourier/Wasserstein and signed Kantorovich
energy comparisons are established infrastructure. Corpus and targeted current literature search
found no clipped prime-log aperture identity `(AC46)--(AC48)` or raw FCRJ specialization.
Candidate-new claim is restricted to exact physical specialization and route reduction.

Verdict: `[PROVED — COMPLETE PHYSICAL FCRJ INVERSE-SQUARE ENERGY IS CONTROLLED BY PRIMEWISE
TRANSPORT W D; MOVING CORE REDUCED TO N W D]`.

## Conjecture loop 64 — active-aperture width ultraviolet law

### Failed first conjecture `[INACTIVE REVERSAL]`

Bounding endpoint chord by clipped interval length without activity is false: when raw endpoints
reverse, clipped length is zero but literal endpoint nodes need not coincide. This premise cannot be
dropped. Exact endpoint differentiation already requires every selected prime interval to be
active, so source statement is frozen on that natural domain.

### Width survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

Let `L` be weighted clipped-interval length, `D` loop-62 weighted endpoint chord, `W` total prime
weight, `A>0`, and assume every selected interval is active. Then

```text
D <= (2 pi/A) L,                                        (AC49)
L <= (k-m) W,                                           (AC50)
N sum_(n>N)|a_n|^2 <= (2A/pi) N(k-m)W^2.                (AC51)
```

For each prime, activity identifies clipped length with `end-start>0`. Fourier character has
angular speed `2pi/A`, so chord-below-arc proves its contribution to `(AC49)`. Definitions
`start=max(0,m-log p)` and `end=min(A,k-log p)` give
`end-start<=k-m`, proving `(AC50)`. Substitution into `(AC47)` and exact raw-amplitude multiplier
`A^2/(4pi^2)` simplifies to `(AC51)`.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointActiveApertureWidthEnergy.lean`.
Direct checking, targeted build, axiom audit, and umbrella wiring pass. Global lint is temporarily
blocked by unrelated concurrent unwired modules, so card remains Stage 2.

Hostile limit: `(AC51)` removes phase collisions, cluster mass, dipole chord, and weighted clipped
length from final physical ultraviolet bound. It does not make width small. Moving-packet disposal
now has exact sufficient source condition `N(k-m)W^2 -> 0`; whether intended CCM-FU scaling supplies
that condition is next arithmetic audit.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: chord-below-arc and clipping monotonicity are
classical. Corpus and targeted current literature search found no clipped prime-log formula
`(AC49)--(AC51)` or FCRJ ultraviolet application. Candidate-new content is exact physical
specialization and elimination of prior collision variables.

Verdict: `[PROVED — ACTIVE PHYSICAL FCRJ ULTRAVIOLET TAIL HAS EXPLICIT APERTURE-WIDTH BOUND;
MOVING CORE REDUCED TO N(k-m)W^2]`.

## Conjecture loop 65 — activity-localized Mertens ultraviolet law

### Failed first conjecture `[DIVERGENT ALL-PRIME MASS]`

A uniform packet-independent bound on `W=sum log p/p` is false; corpus formally proves physical
endpoint weights are not summable over all primes. Any valid elimination of `W` must retain source
localization supplied by active aperture endpoints.

### Mertens survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

For every nonempty active packet,

```text
W <= k + log 4.                                          (AC52)
```

Indeed activity gives `0<end<=k-log p`, hence `log p<k` and `p<exp k`. Put
`M=floor(exp k)`. Every selected prime lies at most `M`; nonemptiness gives `M>=1`. Embedding packet
into all primes up to `M` and applying corpus elementary Mertens upper law

```text
sum_(p<=M) log p/p <= log M + log 4
```

proves `(AC52)` because `M<=exp k`. Combining with `(AC51)` gives, for `m<=k`, including empty
packet by direct zero collapse,

```text
N sum_(n>N)|a_n|^2
  <= (2A/pi) N(k-m)(k+log 4)^2.                          (AC53)
```

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointActiveMertensUltravioletEnergy.lean`.
Direct checking, targeted build, axiom audit, and umbrella wiring pass. Global lint remains blocked
by unrelated concurrent unwired modules, so card remains Stage 2.

Hostile limit: `(AC53)` removes every packet-dependent finite-set, phase, collision, cluster,
transport, and mass invariant from ultraviolet bound. It still requires source scaling
`N(k-m)(k+log 4)^2 -> 0`. This is now an explicit parameter law rather than arithmetic collision
problem. Compatibility with intended moving CCM-FU aperture schedule is next decisive audit.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: Mertens first upper law is classical and
already formal in corpus. Corpus and targeted current literature search found no active clipped
prime-log support localization combined with it to obtain `(AC52)--(AC53)`. Candidate-new content
is exact physical specialization and route reduction.

Verdict: `[PROVED — ACTIVE FCRJ ULTRAVIOLET TAIL HAS FULLY EXPLICIT MERTENS-WIDTH BOUND;
MOVING CORE REDUCED TO N(k-m)(k+log 4)^2]`.

## Conjecture loop 66 — full carrier Mertens-width law and source-retention wall

### Failed first conjecture `[SOURCE-RETENTION COLLAPSE]`

Loop 65 suggests shrinking `k-m` to suppress ultraviolet energy. Treating this as a harmless
regularization while retaining a uniformly nontrivial normalized FCRJ source is false. The same
width controls complete coherent source energy, so normalized source strength collapses with it.

### Full-energy survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

Let `P_M` be exact coherent physical prime-log carrier, `W` total endpoint weight, `L` weighted
clipped length, and `Disp=||P_M||^2/W^2` for nonempty packets. Weighted Hilbert
Cauchy--Schwarz and exact centered-indicator variance give

```text
||P_M||^2 <= W sum_p (log p/p)||phi_p||^2 <= W L.       (AC54)
```

Indeed `||phi_p||^2=ell_p-ell_p^2/A<=ell_p`. Under activity, loop 64 gives
`L<=(k-m)W`; loop 65 gives `W<=k+log 4`. Therefore

```text
||P_M||^2 <= (k-m)W^2,                                  (AC55)
||P_M||^2 <= (k-m)(k+log 4)^2.                          (AC56)
```

The normalized law is

```text
Disp <= k-m.                                            (AC57)
```

In proper physical chamber `0<k-m<A`, nonempty activity and existing endpoint radical theorem
give exact wall

```text
0 < Disp <= k-m.                                        (AC58)
```

Hence any active schedule with `k_n-m_n -> 0` has `Disp_n -> 0`; no uniform positive normalized
source floor survives. On other hand `(AC56)` is direct full-carrier provider: if actual
coefficient-faithful aperture parameters satisfy

```text
(k_M-m_M)(k_M+log 4)^2 << log(M)^B/M,                   (AC59)
```

then corrected-response carrier `||P_M||^2` is already inside FCRJ error budget.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureSourceRetentionWall.lean`.
Direct check, targeted module build, axiom audit, and umbrella wiring pass. Global lint sees this
module as reachable and clean but remains blocked by unrelated concurrently owned unwired modules;
card remains Stage 2.

Hostile limit: actual physical packet uses width `log(K_M/M)`. If this ratio stays bounded away
from one, `(AC56)` gives no `M^-1` saving. Width cannot be freely changed: doing so changes exact
moving prime window, and `(AC58)` shows normalized source collapses. Thus loop closes shrinking
aperture as source-retaining shortcut while converting full FCRJ burden into explicit schedule
test `(AC59)`. Fixed-ratio regime remains genuine centered moving prime-log discrepancy problem.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: weighted Cauchy--Schwarz, centered-indicator
variance, and squeeze are standard. Prime short-window variance literature does not state exact
clipped prime-log physical-carrier synthesis `(AC54)--(AC59)`. Candidate-new content is restricted
to coefficient-faithful full-energy bound and FCRJ source-retention/provider boundary.

Verdict: `[PROVED — COMPLETE PHYSICAL FCRJ CARRIER ENERGY OBEYS PACKET-FREE MERTENS-WIDTH LAW;
SHRINKING WIDTH CLOSES ENERGY ONLY BY COLLAPSING NORMALIZED SOURCE]`.

## Conjecture loop 67 — adaptive-aperture divisor censorship

### Failed escape `[POINTWISE FAITHFUL, UNIFORMLY CENSORING]`

Loop 66 leaves apparent possibility that shrinking width suppresses full carrier energy while
remaining divisor-faithful because every positive fixed-width multiplier is nonzero. This confuses
pointwise injectivity with uniform observability.

### Exact-jet survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

For exact physical log-window divisor multiplier

```text
M_c(z)=exp(cz)-1,
```

global exponential remainder bound gives

```text
||M_c(z)|| <= |c|||z|| exp(|c|||z||).                   (AC60)
```

Consequently `c_n->0` forces `M_{c_n}(z)->0` for every fixed mode. Along positive widths, complex
differentiability supplies exact first jet

```text
M_c(z)/c -> z,
||M_c(z)||/c -> ||z||.                                 (AC61)
```

For every nonzero `z`, eventually

```text
(||z||/2)c <= ||M_c(z)|| <= 2||z||c.                   (AC62)
```

Existing coefficient-faithfulness theorem says `M_c(z)!=0` whenever `c>0` and `Re z<0`. Therefore
every positive shrinking schedule is noncensoring at each finite stage but converges to complete
attenuation, and no positive uniform response floor exists.

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureAdaptiveDivisorCensorship.lean`.
Direct check, targeted build, capstone axiom audit, and umbrella wiring pass.

Hostile limit: loop 66 energy gain is bought at exact first-order loss of divisor observability.
Renormalizing by `1/c` recovers mode `z` but imposes matching inverse-conditioning cost on every
arithmetic and ultraviolet error. Thus adaptive shrinking is closed as free FCRJ regularization.
Fixed positive ratio remains genuine centered moving prime-log discrepancy core.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: exponential Taylor and derivative laws are
classical. Corpus and targeted current-literature searches found no exact synthesis of physical
FCRJ multiplier noncensorship, adaptive attenuation, first-order jet, and loop 66 full-carrier
source collapse. Candidate-new content is coefficient-faithful provider obstruction only.

Verdict: `[PROVED — SHRINKING PHYSICAL APERTURES CENSOR EVERY FIXED DIVISOR MODE AT EXACT LINEAR
RATE DESPITE NONZERO RESPONSE AT EVERY FINITE POSITIVE WIDTH]`.

## Conjecture loop 68 — exact Mertens-coboundary variance bridge

### Failed first conjecture `[ABSOLUTE PAIR COUNT LOSES CONTINUUM CANCELLATION]`

Bounding positive tent overlaps by multiplicative neighbor counts discards rank-one aperture mean.
At fixed ratio this leaves macroscopic continuum pair mass and cannot reach `M^-1 polylog(M)`.
Physical centering must occur before any absolute estimate.

### Exact burden survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

Define finite-packet cumulative physical mass and Mertens discrepancy

```text
C_P(t)=sum_(p in P,log p<=t) log(p)/p,
D_P(t)=C_P(t)-t.
```

Window flux is exact two-endpoint coboundary

```text
Flux_P(m,k;u)
 =C_P(k-u)-C_P(m-u)
 =(k-m)+D_P(k-u)-D_P(m-u).                             (AC63)
```

If `L_P` is weighted clipped-length mass, coherent physical centering gives

```text
CenteredFlux_P(A,m,k;u)
 =[D_P(k-u)-D_P(m-u)]-[L_P/A-(k-m)].                   (AC64)
```

An almost-everywhere representative theorem identifies this scalar exactly with existing complex
Hilbert carrier. Hence

```text
||P_M||^2
 =integral_0^A
   |D_P(k-u)-D_P(m-u)-[L_P/A-(k-m)]|^2 du.             (AC65)
```

At physical scale `m=log X`, `k=log X+c`, the FCRJ bound `||P_M||^2<=B` is equivalent, with no
constant or one-sided loss, to corresponding centered Mertens-increment variance bound

```text
integral_0^A
 |D_P(log X+c-u)-D_P(log X-u)-[L_P/A-c]|^2 du <= B.    (AC66)
```

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureMertensCoboundary.lean`.
Direct check, targeted build, axiom audit, and umbrella wiring pass.

Hostile limit: standard almost-diagonal/Gallagher bounds on uncentered positive pair mass lose
continuum cancellation and remain macroscopic. Pointwise PNT error also misses target scale. The
remaining provider must prove exact centered mean square `(AC66)`, including `log p/p` partial
summation and prime-power corrections. This is now a classical-looking Selberg-type input with
every FCRJ coefficient frozen.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: cumulative differences and variance are
classical; Selberg-integral literature is adjacent. Corpus and targeted current-literature searches
found no exact clipped physical FCRJ identification `(AC63)--(AC66)`. Candidate-new content is
restricted to coefficient-exact bridge and burden equivalence.

Verdict: `[PROVED — FIXED-RATIO FCRJ CARRIER BOUND IS EXACTLY CENTERED TWO-ENDPOINT MERTENS
DISCREPANCY VARIANCE; ALL CONTINUUM AND HILBERT CONVERSION LOSSES REMOVED]`.

## Conjecture loop 69 — exact theta--Abel rank-one provider

### Failed first estimate `[POINTWISE ENDPOINT BOUND WITHOUT ABEL TRANSPORT]`

Bounding cumulative Mertens discrepancies separately retains an arbitrary packet truncation and
hides the continuum correction. The exact `log p/p` coefficient must be transported before
squaring, and physical clipping mean must be computed rather than bounded.

### Exact provider survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

Let the complete support packet be

```text
P(A,m,k)={p prime : m-A<log p<=k}
```

and put

```text
q(h)=[theta(exp h)-exp h]exp(-h),
R(m,k;u)=q(k-u)-q(m-u)+integral_(m-u)^(k-u)q(h)dh.
```

Exact Abel summation at every `u in [0,A]` gives

```text
sum_(m-u<log p<=k-u) log p/p-(k-m)=R(m,k;u).           (AC67)
```

The weighted clipping correction is not an error term: it is exactly response mean,

```text
L(P,A,m,k)/A-(k-m)=(1/A)integral_0^A R(m,k;u)du.       (AC68)
```

Consequently complete physical fusion energy has lossless rank-one decomposition

```text
||P_M||^2
 =integral_0^A R(m,k;u)^2du
  -(1/A)(integral_0^A R(m,k;u)du)^2                    (AC69)
 <=integral_0^A R(m,k;u)^2du.                          (AC70)
```

In particular, a uniform aperture response bound `|R|<=B` gives exact provider

```text
||P_M||^2<=A B^2.                                      (AC71)
```

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelVariance.lean`.
Direct checking, targeted build, axiom audit, and umbrella wiring pass.

Hostile limit: `(AC69)` removes packet, clipping, Hilbert, and rank-one conversion losses, but does
not estimate theta-error response. At `m=log X`, proving raw response mean square
`O(X^-1 polylog X)` is exactly remaining RH-bearing analytic burden. Pointwise PNT error is too
large; cancellation must occur inside response `L²` mass.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: Abel summation and variance decomposition are
classical. Selberg-integral literature is adjacent. Corpus and targeted primary-literature audit
found no exact clipped physical FCRJ synthesis `(AC67)--(AC71)`. Candidate-new content is restricted
to coefficient-exact source identification and zero-loss provider reduction.

Verdict: `[PROVED — COMPLETE FIXED-RATIO FCRJ ENERGY IS RAW NORMALIZED THETA-ABEL L2 MASS MINUS
ITS EXACT RANK-ONE MEAN; REMAINING BURDEN IS ONE SOURCE-PURE MEAN SQUARE]`.

## Conjecture loop 70 — ordinary-PNT fixed-width extinction boundary

### Failed conjecture `[QUALITATIVE PNT DECAY SUPPLIES FCRJ RATE]`

Ordinary PNT makes normalized theta error tend to zero, but its zero-free-region rate does not
manufacture the required `exp(-m)=X^-1` factor after Abel transport and squaring.

### Qualitative survivor `[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]`

If `c>=0` and `|q(h)|<=B` throughout enlarged band `[m-A,m+c]`, endpoint plus interior Abel terms
give exact uniform estimate

```text
|R(m,m+c;u)|<=(2+c)B,  0<=u<=A.                       (AC72)
```

Combining `(AC71)` and `(AC72)` gives

```text
||P_M||^2<=A((2+c)B)^2.                                (AC73)
```

Corpus power-log PNT proves `q(h)->0`. Every fixed translated band eventually lies beyond same
PNT threshold, hence for every fixed `A>0`, `c>=0`,

```text
Energy(P(A,m,m+c),A,m,m+c)->0 as m->infinity.          (AC74)
```

Formal module:
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeAperturePNTDecay.lean`.
Direct checking, targeted build, axiom audit, and umbrella wiring pass.

No-go closure: ordinary PNT now closes qualitative fixed-width carrier extinction completely.
Its strongest positive survivor is `(AC72)--(AC74)`. Remaining FCRJ theorem is purely quantitative:
upgrade qualitative/zero-free-region decay to `exp(-m)poly(m)` by centered theta-response
mean-square cancellation. Treating pointwise PNT as that upgrade is invalid.

Novelty audit `[TARGETED PRIMARY AUDIT, 2026-08-27]`: PNT and bounded-shift uniformity are
classical. Candidate-new content is exact transport through physical theta--Abel carrier and
qualitative extinction theorem `(AC74)`; no RH claim.

Verdict: `[PROVED — ORDINARY PNT KILLS EVERY FIXED-WIDTH COMPLETE PHYSICAL CARRIER QUALITATIVELY;
THE SOLE SURVIVING GAP IS RH-SCALE L2 RATE]`.
