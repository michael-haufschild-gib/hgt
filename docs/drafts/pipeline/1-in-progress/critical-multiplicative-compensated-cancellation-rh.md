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
  `[HARMONIC-FLOOR STOKES REDISCOVERED] [FATHER-CHANNEL COUPLING OPEN]`
  `[ORIENTED COFINAL CARLESON CONTROL OPEN] [NOT RH YET]`
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
- `2-fully-proven/not_new_scientific_knowledge/additive-heat-diagonal-generates-full-operator-algebra.md`
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

## 2026-07-18 harmonic-floor aperture mapping cone and the father obstruction

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

### The reduced aperture complex contracts, but its constant class does not

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

For a fixed prime let

```text
(mathcalH_pf)(x)=sum_(k>=1)f(p^kx).
```

On the decay class containing `r_L`, the series converges and telescopes to

```text
(R_p-I)mathcalH_pf=f,
mathcalH_p(R_p-I)f=f.                                   (AB9)
```

Thus every reduced horizontal aperture difference is contractible on the decaying lattice current.
It annihilates the constant `gamma`, leaving one-dimensional reduced cohomology.  Pairing that
father class with the distinguished source is precisely `gamma M_1(N)`.  Quotienting it makes the
pointed trace undefined; adjoining it restores the classical Mertens boundary.  A square-root
two-sided estimate for that boundary is RH strength, not an available input.

The norm trade is equally rigid.  In unweighted `ell2(d)`, the source vectors `u` and `a` have
uniformly bounded norm, while

```text
||G_N||_2^2 asymp_L N.                                  (AB10)
```

Indeed `G_N(d)` stays bounded away from zero on a positive proportion of `d` near `N`.  In the
reciprocal norm `sum_d|x_d|^2/d`, its norm square is `asymp_L log N`, while the dual norm squares
of `u` and `a` grow respectively like `log N` and `(log N)^3`.  Even this rebalance pays

```text
sum_(N asymp exp(J))(c_N/N)||G_N||_(1/d)^2
 asymp_L J exp(J/2).                                    (AB11)
```

Fixed-prime and balanced-face tests show both sides of the classification:

```text
(R_p-I)z_L(N)=O_L(p/N),
p^(-1)(R_p-I)z_L(p)=-p^(-1)+O_L(p^(-2)),
(R_p-I)(R_q-I)z_L(pq)->-1                 (p,q->infinity). (AB12)
```

The reduced complex genuinely kills persistent fixed-prime modes.  The moving singleton front and
balanced Type-II face remain boundary atoms and cancel only in the signed all-face sum.  Norming
the faces separately pays `(BU7)`; collapsing them first gives `(AB2)`, whose polar subtraction is
the father problem `(AB8)`.

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
products never dephase.  An adjacent aperture difference gains `N^(-1)` but its right inverse
loses `N`, with the constant father in the kernel.

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

### Hostile verdict and corrected open core

`[PAPER-PROVED] [REDISCOVERED BRIDGE]` The Euler--Koszul derivative `(AB2)`, harmonic-floor mapping
cone `(AB4)`--`(AB6)`, and reduced contracting homotopy `(AB9)` are exact.  The first three
arithmetic identities are already Lean-proved in `Mollifier.lean`.

`[FALSIFIED]` Positive Type-II branch completion, reduced-difference-only completion, raw or
reciprocal harmonic-floor norm, and a conventional two-sided Type-II/Selberg mean square.  They
respectively pay `(BU7)`, forget the father trace, pay `(AB10)`--`(AB11)`, or assume the
RH-equivalent estimate `(TI3)`.

`[POSITIVE SALVAGE]` The reduced aperture current is contractible and its transverse adjacent-cutoff
energy satisfies `(SV1)`.  The obstruction is not an unspecified Type-II identity: it is the unique
constant cohomology class in `(AB8)`.

`[OPEN CORE]` Construct a source-defined, genuinely **one-sided father--curvature coupling** which
uses the shrinking transverse current `(SV1)` but controls

```text
sum_(N asymp exp(J)) E_L(N)^+/N
```

polynomially before positive norm separation.  Its source and norm must be fixed independently of
`E_L`, its sign, zero data, and the evaluated Mertens sum.  It must retain the constant class rather
than quotient it, and it must not replace the target by `(TI3)` or a square-root two-sided estimate
for `M_1`.  This is the exact remaining content of `(CO1)`--`(CO2)`.
