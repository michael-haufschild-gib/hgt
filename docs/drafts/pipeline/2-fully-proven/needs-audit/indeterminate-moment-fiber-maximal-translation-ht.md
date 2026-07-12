# Complete moment fibers: formal collapse and residual translation-HT explosion

- **ID:** `indeterminate-moment-fiber-maximal-translation-ht`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** THEOREM (paper) / MOMENT-FIBER HT RIGIDITY DICHOTOMY
- **Lane:** general hypertranscendence; Hamburger moment geometry; Herglotz carriers
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Statement:** Let `M(s)` be the full weak-topological fiber of positive probability measures
  representing a normalized Hamburger moment sequence. If `s` is determinate, `M(s)` is a point.
  If `s` is indeterminate, `M(s)` is a compact metrizable convex Baire space and contains a dense
  residual set of measures whose full complex translation family of Cauchy transforms is
  differentially algebraically independent over `C(z)`; the maximally free measures may themselves
  be chosen from a dense `G_delta` subset of the extreme boundary, while nonextreme maximally free
  measures are also dense. Moreover, pure point, singular-continuous, and absolutely continuous
  subcharts each carry their own residual maximal-HT phase. Nevertheless every two points of
  `M(s)` have the same complete formal differential-translation asymptotic germ at upper infinity:
  every pairwise difference, after every fixed translation and derivative, is flat to all
  algebraic orders. Thus the formal asymptotic quotient collapses the entire fiber to one point
  while its global differential-translation image has residual maximal rank independently of
  convex extremality and spectral type. In addition, the fiber admits a canonical
  normalization-independent affine retraction onto a Bauer simplex of Nevanlinna-boundary
  probabilities, and every infinite closed face of that simplex retains residual maximal rank.

## Medalist lens

Finite moment constraints are too weak for a serious law: their transversality to Cauchy jets is
finite-dimensional annihilator duality. The nontrivial collision is at the opposite extreme.

Fix **every** Hamburger moment. In the determinate case this fixes the measure. In the indeterminate
case it leaves a compact convex Nevanlinna fiber of positive measures. The theorem below proves
that a dense residual subset of this entire canonical fiber has a continuum-size differentially
free translation family, although the whole fiber is one point to every formal asymptotic order.

The object is fixed by the complete moment constraint, not propagated by a flow. The geometry is
the differential matroid living inside one all-order moment fiber.

## Classical Nevanlinna input `[SEARCH]`

Let `(s_n)` be an indeterminate normalized Hamburger moment sequence. Its `N`-extremal solutions
`mu_tau`, indexed by real `tau` and one point at infinity, have Cauchy transforms

```text
m_tau(z)=integral_R 1/(x-z) d mu_tau(x)
        =(A(z) tau+B(z))/(C(z) tau+D(z)).                    (1)
```

This is the convention in Pruckner--Reiffenstein--Woracek, arXiv `2307.10748`, equation (1.1).
The entries are real entire functions and, in the standard canonical-system normalization,

```text
Delta=A D-B C=1.
```

The determinant identity follows equally from the trace-zero canonical-system equation and the
identity initial condition. Every `mu_tau` has moments `(s_n)`.

On the regular set `C Delta !=0`, put

```text
m_infinity=A/C,
q=-D/C,
a=-1/C^2.                                                    (2)
```

Direct subtraction in (1) gives the exact parameter-Cauchy identity

```text
m_tau(z)=m_infinity(z)+a(z)/(tau-q(z)).                      (3)
```

For `z` in the upper half-plane and real `tau`, the denominator in (1) cannot vanish because
`m_tau` is a Cauchy transform and hence holomorphic there. Thus every regular value `q(z)` is
nonreal. In fact `q` has no pole in the upper half-plane: near a meromorphic pole its image contains
real values, again producing a real `tau` with `C(z)tau+D(z)=0`. Hence `q` is holomorphic there.
Connectedness and continuity now give one constant nonzero sign for `Im q`. Consequently the
parameter poles `q(z)` of upper-half-plane nodes and their reflected conjugates lie in disjoint
half-planes.

The function `q` is nonconstant. If it were a nonreal constant, the reality of `C,D` on the real
axis would fail; if it were real, the denominator of (1) would vanish for that real parameter.
Its period group

```text
P_q={h in C:q(z+h)=q(z) as meromorphic functions}            (4)
```

is therefore discrete: periods accumulating at zero would force `q'=0`.

## Nevanlinna translation-aperiodicity `[PROVED HERE]`

```text
P_q={0}.                                                     (4a)
```

The `N`-extremal measure `mu_infinity` is supported on the real zeros of `C`; equivalently, these
are the poles of `q=-D/C`. Its support is infinite, since a finite-support Hamburger measure has a
finite-rank moment matrix and is determinate. Hence `q` has a real pole.

Every pole of the meromorphic Herglotz function `q` is real. If `h in P_q`, translation by `h`
preserves the pole set. Applying it to one real pole shows that `h` is real. If `h!=0`, the complete
arithmetic progression `lambda+Z h` consists of poles, so the zero-counting function of `C` obeys

```text
n_C(r) >= 2r/|h|+O(1).                                     (4b)
```

But every entry of the Nevanlinna matrix is entire of minimal exponential type. Thus
`log M_C(r)=o(r)`. Jensen's formula, applied between radii `r` and `2r` after removing a possible
finite zero at the origin, gives

```text
n_C(r) log 2 <= log M_C(2r)+O(log r)=o(r).                  (4c)
```

This contradicts (4b). Therefore no nonzero period exists. `QED`

## Barycentric all-moment fiber `[PROVED]`

Choose distinct real parameters `(tau_n)` and positive weights `eta_n` with `sum_n eta_n=1` and
infinite support. Put

```text
E_eta={v in ell-infinity(R):sum_n eta_n v_n=0}.              (5)
```

For `0<delta<1`, let

```text
X_delta={rho=1+v:v in E_eta, ||v||_infinity<delta}.          (6)
```

For `rho in X_delta`, define the positive probability measure and its Cauchy transform by

```text
mu_rho=sum_n eta_n rho_n mu_(tau_n),
m_rho(z)=sum_n eta_n rho_n m_(tau_n)(z).                     (7)
```

Every `mu_rho` has the complete moment sequence `(s_k)`. Indeed, positivity permits Tonelli for
even powers. For odd powers, `|x|^(2j+1)<=1+|x|^(2j+2)`, uniformly bounding the absolute moment by
`1+s_(2j+2)`; Fubini then applies. Therefore

```text
integral x^k d mu_rho(x)=sum_n eta_n rho_n s_k=s_k.          (8)
```

On compact upper-half-plane sets, the Möbius family in (1) and every fixed number of its
`z`-derivatives are uniformly bounded for real `tau`: formula (3) has parameter poles a positive
distance from the real axis there. Hence (7) and its derivatives converge normally. Using (3) and
the mean-one condition gives

```text
m_rho(z)=m_infinity(z)+a(z) sum_n eta_n rho_n/(tau_n-q(z)).  (9)
```

Thus one exact all-moment fiber contains a second positive Cauchy-transform problem in the
Nevanlinna parameter.

## All-order flatness of the full moment fiber `[PROVED HERE]`

For any `mu,nu in M(s)`, every fixed `h in C`, every derivative order `r`, and every
`L>=0`,

```text
d_z^r[m_mu-m_nu](i y+h)=O_(mu,nu,h,r,L)(y^(-L))
as y -> infinity.                                           (9a)
```

Thus the complete family of formal asymptotic expansions of all translated derivatives is the same
at every point of the full representing-measure fiber.

### Proof

Let `omega=mu-nu`. Equality of the represented moments gives

```text
integral x^k d omega(x)=0                                   (9b)
```

for every `k>=0`. For any `N`, polynomial division of the Cauchy kernel and cancellation of these
moments give

```text
integral 1/(x-z) d omega(x)
 =z^(-(N+1)) integral x^(N+1)/(x-z) d omega(x)              (9c)
```

up to the harmless sign determined by the chosen expansion convention. On `z=i y+h` with `y`
larger than `2|Im h|`, one has `|x-z|>=y/2` for real `x`. Therefore

```text
|m_mu(z)-m_nu(z)|
 <=2^(N+2) y^(-(N+2)) integral |x|^(N+1) d|omega|(x).       (9d)
```

The absolute moment is finite because `|omega|<=mu+nu` and every representing measure has
all Hamburger moments. Since `N` is arbitrary, the difference is flat to all algebraic orders.

For derivatives, differentiate the exact finite kernel expansion, or apply the same division to
`r!/(x-z)^(r+1)`; the remainder has an additional fixed denominator power and is bounded by a
higher finite absolute moment. A fixed translation changes only the lower bound on `y`. This proves
(9a). `QED`

Let `Flat_infinity` denote the translation- and differentiation-stable space of upper-end
holomorphic germs flat to every algebraic order on vertical rays; it is an ideal in the algebra of
polynomial-growth upper-end germs. Equation (9a) says that every `m_mu`, `mu in M(s)`, has the same
complete differential-translation image modulo `Flat_infinity`, while the canonical full-fiber
theorem below says that a residual lift of that one formal image has maximal translation
differential rank.

## Translation palettes and separated evaluation packets `[PROVED]`

Fix any countable set `H subset C`. Given distinct
`h_1,...,h_m in H`, one can choose arbitrarily many base points `z_b`, high enough that every
`z_b+h_i` lies in the upper half-plane, with all of the following properties:

1. `a`, `q`, and the Nevanlinna matrix are regular at every `z_b+h_i`;
2. `a(z_b+h_i) q'(z_b+h_i)!=0`;
3. all values `q(z_b+h_i)` are pairwise distinct.

For a fixed pair `i!=j`, the meromorphic function
`q(z+h_i)-q(z+h_j)` is not identically zero by (4a). Its collision set is
discrete. The critical, zero, and polar sets are also discrete. Choose the base points
sequentially, additionally avoiding the discrete preimages of the finitely many previously used
`q`-values. This proves the claim. The reflected parameter poles are automatically disjoint because
all `q(z_b+h_i)` lie in one open half-plane.

## Mean-zero parameter-jet controllability `[PROVED HERE]`

Let `zeta_1,...,zeta_M` be a separated upper-half-plane node packet as above, with jet depths
`r_1,...,r_M`. Define

```text
T:E_eta -> product_j C^(r_j+1),
T(v)_(j,r)=sum_n eta_n v_n d_z^r m_(tau_n)(zeta_j).          (10)
```

Then `T` is surjective as a real-linear map.

### Proof

Suppose a real functional annihilates `range T`. Every real functional on the complex jet target
has the form

```text
x |-> Re sum_(j,r) alpha_(j,r) x_(j,r).                     (11)
```

The annihilator of the weighted mean-zero hyperplane `E_eta` in the represented `ell-one(eta)`
functionals is the real span of the constant sequence. Hence, for some real `c`,

```text
Re sum_(j,r) alpha_(j,r) d_z^r m_tau(zeta_j)=c              (12)
```

at every parameter `tau=tau_n`.

For `g_tau(z)=a(z)/(tau-q(z))`, induction on `r` gives

```text
d_z^r g_tau(z)
 =a(z) r! q'(z)^r/(tau-q(z))^(r+1)
  + terms whose pole at q(z) has order at most r.            (13)
```

Indeed, differentiating the leading denominator raises its order and multiplies its coefficient by
`(r+1)q'`; all coefficient derivatives retain lower order.

Subtract the constant in (12) and add the reflected conjugate. Formula (3) makes the result a
rational function `Q(tau)` vanishing at every `tau_n`. The parameter support is infinite, so
`Q` is identically zero. At `q(zeta_j)`, only the unreflected rational function contributes. Its
unique highest principal part has coefficient

```text
alpha_(j,r_j) a(zeta_j) r_j! q'(zeta_j)^r_j.                (14)
```

It is nonzero unless `alpha_(j,r_j)=0`. Descending in the jet order at each separated pole kills
every `alpha_(j,r)`. The remaining constant identity gives `c=0`. Thus the range has zero real
annihilator. Its target is finite-dimensional, so the range is the whole target. `QED`

## Residual maximal-translation theorem `[PROVED HERE]`

For every `0<delta<1`, there is a dense residual set `G_(H,delta) subset X_delta` such that, for
every `rho in G_(H,delta)`, the family

```text
(m_rho(z+h))_(h in H)                                      (15)
```

is differentially algebraically independent over `C(z)`.

### Proof

Fix a finite relation pattern: finitely many shifts from `H`, finite jet depths, distinct
differential monomials, and a polynomial coefficient-degree bound. Choose sufficiently many
evaluation bases `z_b` so the complete translated packet is separated as above. The polynomials
`z^d M_beta(X)` are linearly independent, so the finite evaluation lemma makes their square
evaluation determinant a nonzero polynomial in the target jet packets.

The controllability theorem is surjective on this full packet. A surjective linear map between
finite-dimensional real spaces is open, so every sufficiently small ball in `E_eta` moves the
actual packet through a real neighbourhood while remaining inside `X_delta`. A nonzero complex
polynomial cannot vanish on a real-open set. Hence the densities escaping the pattern are dense.
Normal convergence makes the determinant continuous, so the escape set is open.

There are countably many patterns because `H` is countable. The open subset `X_delta` of the Banach
space `E_eta` is Baire. Intersecting the open dense escape sets gives `G_(H,delta)`. A differential
relation over `C(z)` clears denominators to one enumerated pattern. If the relation is initially
stated only as an upper-end germ, every term is meromorphic on the common connected component above
the finitely many shifted real lines; the meromorphic identity theorem propagates it to all chosen
high evaluation points. It then contradicts the invertible evaluation matrix. `QED`

## Full configuration theorem `[PROVED HERE]`

There is a dense residual subset `G_delta^full subset X_delta` such that, for every
`rho in G_delta^full`, every `m>=1`, and every tuple

```text
(h_1,...,h_m) in Conf_m^q(C)
  :={h in C^m:h_i!=h_j for i!=j},                            (16)
```

the functions `m_rho(z+h_1),...,m_rho(z+h_m)` are differentially algebraically independent over
`C(z)`.

### Proof

Fix `m`, a differential-monomial support of size `R`, a jet depth, and a polynomial
coefficient-degree bound `d`. Put `K=R(d+1)`. By (4a), `Conf_m^q(C)` is the ordinary configuration
space of distinct complex shifts, an open, second-countable, sigma-compact real manifold of
dimension `2m`.

Fix one configuration `h^0`. Choose `N` separated evaluation bases for its full translated node
packet, with

```text
N>m+d+K-1.                                                   (17)
```

All separation, regularity, and noncriticality conditions persist on a relatively compact
neighbourhood `U` of `h^0`.

Let `Y` be the complex row-jet space and let `B subset Y^N` be the locus where the `N by K`
evaluation matrix of the functions `z^e M_beta` has rank below `K`. For a fixed projective
coefficient vector, at most `d` evaluation rows have all coefficient polynomials zero. Every
remaining row imposes one nonzero polynomial equation in its independent jet variables. The
projective incidence variety therefore gives

```text
codim_C B >= N-d-K+1 > m.                                   (18)
```

Choose finitely many directions in `E_eta` whose parameter jets span the full `N`-row packet at
`h^0`; mean-zero controllability supplies them. Their real span `V` is finite-dimensional. For a
fixed base density `rho_0`, define

```text
Psi:V x U -> Y^N,
Psi(v,h)=the row-jet packet of m_(rho_0+v) at z_b+h_i.        (19)
```

The derivative in the `V` direction is onto at `(0,h^0)`. After shrinking `V` and `U`, surjectivity
persists, so `Psi` is a smooth real submersion. Stratify the algebraic set `B` by Whitney strata.
Parametric transversality gives a residual dense set of arbitrarily small `v` for which
`Psi_v:U->Y^N` is transverse to every stratum. Each stratum has real codimension greater than
`2m=dim_R U` by (18), so every transverse preimage is empty. Thus one can escape the fixed relation
pattern simultaneously for all configurations in the patch while staying in any prescribed
positive density neighbourhood.

Compactly exhaust `Conf_m^q(C)` by countably many such patches and intersect over all `m`, jet
depths, monomial supports, and coefficient degrees. Uniform normal convergence on each compact
patch makes every avoidance condition open. Baire's theorem gives `G_delta^full`. Clearing rational
denominators converts any differential relation into one of the excluded patterns. A relation
known first as an upper-end germ extends by the meromorphic identity theorem across its common
connected upper component to the high evaluation rows used on the patch. `QED`

Consequently the entire family `(m_rho(z+h))_(h in C)` is differentially algebraically independent:
every finite subfamily is covered by the theorem.

## Mutually singular extremal simplex `[PROVED HERE]`

The auxiliary barycentric family is not a parametrization artifact. Distinct `N`-extremal measures
are mutually singular. Indeed, for finite `tau`, the support of `mu_tau` is the real zero set of

```text
C(x) tau+D(x),                                               (20)
```

and the support of `mu_infinity` is the real zero set of `C`. If a point belonged to the supports
for two distinct finite parameters, subtraction would give `C(x)=0`, and then (20) would give
`D(x)=0`, contradicting `A D-B C=1`. The same determinant identity separates every finite support
from the support at infinity.

Consequently, for every countable set of distinct parameters `(tau_n)`, the affine map

```text
(w_n) |-> sum_n w_n mu_(tau_n),
sum_n w_n=1,  w_n>=0,                                       (21)
```

is injective. More precisely, for every absolutely summable real sequence `(c_n)`,

```text
||sum_n c_n mu_(tau_n)||_TV=sum_n |c_n|.                    (22)
```

Thus every indeterminate moment fiber contains an isometric infinite probability simplex in total
variation geometry. The parameter-pole theorem says that the tangent hyperplane of this simplex is
simultaneously onto every finite packet of complex Cauchy jets.

## Canonical full-fiber residual theorem `[PROVED HERE]`

Let `M(s)` be the set of all positive probability measures on `R` with moments `(s_n)`, equipped
with the weak topology. If `s` is indeterminate, there is a dense residual subset
`G_s subset M(s)` such that, for every `mu in G_s`, every `m>=1`, and every tuple of distinct
complex shifts `(h_1,...,h_m)`,

```text
m_mu(z+h_1),...,m_mu(z+h_m)                                 (23)
```

is differentially algebraically independent over `C(z)`.

### Compact Baire geometry of the fiber

The fiber `M(s)` is convex. It is tight because every member has the same second moment:

```text
mu(|x|>R)<=s_2/R^2.                                         (24)
```

It is also weakly closed. Suppose `mu_j` converges weakly to `mu`. For each `k>=1`, the common
moment `s_(2k)` gives the uniform-integrability estimate

```text
integral_(|x|>R) |x|^k d mu_j
  <=R^(-k) integral |x|^(2k) d mu_j
  =R^(-k) s_(2k).                                           (25)
```

Weak convergence passes every bounded truncation of `x^k`; (25), followed by `R -> infinity`,
therefore gives `integral x^k d mu=s_k`. Prokhorov compactness now shows that `M(s)` is weakly
compact. Since `R` is Polish, the weak topology on probability measures is metrizable. Hence
`M(s)` is a compact metrizable Baire space.

### Uniform weak continuity of translated jets

Let `K` be a compact set of translation configurations contained in a local patch on which all
chosen evaluation nodes stay a fixed positive distance above the real axis. Every translated jet
is the integral of a kernel

```text
r!/(x-z_b-h)^(r+1).                                        (26)
```

As `(b,h,r)` ranges over the finite evaluation packet and `h` ranges over `K`, these kernels form a
compact subset of `C_0(R)` in the uniform norm: their dependence on `h` is uniform-norm continuous,
their denominators are uniformly separated from zero, and they vanish uniformly at real infinity.
A finite uniform net therefore upgrades ordinary weak convergence to uniform convergence of every
jet packet on `K`.

For a fixed differential-relation pattern, let `B` be its closed finite-dimensional rank-defect
variety from the full-configuration proof. The condition that the jet-packet map avoids `B` for
every `h in K` is open in `M(s)`: its compact image has positive distance from the closed set `B`,
and that distance persists under the uniform weak continuity just proved.

### Density by infinitesimal simplex insertion

Fix `mu_0 in M(s)`, a weak neighbourhood `W` of `mu_0`, one compact local configuration patch, and
one relation pattern. Choose the barycentric simplex (21) and a base density `rho_0 in X_delta`.
For sufficiently small `epsilon>0`,

```text
mu_(epsilon,v)
  =(1-epsilon) mu_0+epsilon mu_(rho_0+v)                    (27)
```

belongs to `W` for every sufficiently small `v in E_eta`; this follows directly from a finite
bounded-continuous-test-function description of `W`. Every measure in (27) remains in `M(s)`.

The derivative of its finite jet-packet map in the `v` direction is `epsilon` times the surjective
map (10). It is therefore still onto. The same finite-dimensional submersion and rank-defect
codimension argument used in (17)--(19) supplies arbitrarily small `v` for which the complete patch
avoids the fixed relation pattern. Thus every one of the open pattern-avoidance sets is dense in
the full fiber `M(s)`.

There are countably many monomial supports, jet depths, coefficient-degree bounds, numbers of
shifts, and relatively compact local patches in a countable cover of each configuration space.
Baire intersection gives `G_s`. Clearing denominators turns every relation over `C(z)` into one of
the excluded patterns. This proves (23). `QED`

## Extreme-point maximal-HT theorem `[PROVED HERE + SEARCH]`

Let `Ext M(s)` be the extreme boundary of the compact convex moment fiber. If `s` is
indeterminate, then

```text
Ext M(s) intersect G_s                                     (28)
```

is a dense `G_delta` subset of `M(s)`. Thus a generic point of the entire moment fiber can be
chosen simultaneously extreme and maximally differentially independent under every finite
configuration of complex translations.

### Classical extreme-boundary density

The needed density input is classical moment theory, not a project claim. Naimark's criterion says
that `mu in M(s)` is extreme exactly when the polynomials are dense in `L^1(mu)`. More concretely,
the canonical solutions of every sufficiently large finite order are dense in `M(s)`, and every
finite-order canonical solution is extreme. This is recorded in Christiansen's survey *The Moment
Problem* and in Schmuedgen, *The Moment Problem*, Chapter 7 (finite-order solutions are extreme).
Consequently `Ext M(s)` is dense.

For completeness, its `G_delta` property needs no moment theory. In any compact metrizable convex
set `K`, let

```text
F_n={x in K:x=(y+z)/2 for some y,z in K with d(y,z)>=1/n}.  (29)
```

The defining subset of `K^3` is compact, so its projection `F_n` is compact. Every nonextreme point
belongs to some `F_n`, and every point in some `F_n` is nonextreme. Hence

```text
Ext K=K minus union_(n>=1) F_n                              (30)
```

is `G_delta`. Apply this to `K=M(s)`. The canonical full-fiber theorem makes `G_s` dense
`G_delta`; Baire's theorem makes (28) dense `G_delta`. `QED`

The opposite convex stratum also contains maximal-HT points densely. Given `mu_0` and a weak
neighbourhood, repeat the infinitesimal-simplex insertion (27) with `0<epsilon<1`. Every resulting
point whose inserted endpoint differs from `mu_0` lies in the open segment joining two distinct
members of `M(s)` and is therefore nonextreme. The barycentric chart is injective, so at most one
parameter value can make the endpoint equal `mu_0`; the dense transversality escape set contains
another value. Hence

```text
G_s intersect (M(s) minus Ext M(s))                         (31)
```

is dense as well.

This removes a previously listed escape hatch. **Extremality by itself does not reduce the generic
translation-HT phase.** A rigid moment carrier must select a specified extreme point by additional
nonflat source data--for example a Friedrichs/Krein boundary condition, an Euler--Gamma pointing,
or an orientation law--rather than merely prove that its representative is extreme.

The complete convex-geometric conclusion is an orthogonality law: with the full moment sequence and
formal asymptotic shadow fixed, maximal translation HT occurs densely on both the extreme and the
nonextreme strata. Convex extremality and global differential rank are independent carrier
coordinates.

## Spectral-type refinement `[PROVED IN COMPANION CARD]`

The companion theorem
`spectral-type-stratified-moment-fiber-maximal-ht.md` strengthens the same law in a
direction not supplied by whole-fiber residuality. Barycenter the `N`-extremal measures against an
arbitrary infinite-support probability `eta` on the real Nevanlinna parameter line, then vary `eta`
by bounded positive mean-one densities. The parameter measure's pure spectral type is transported
into `M(s)`, while the rational parameter-pole proof makes every finite Cauchy-jet packet
controllable.

Choosing `eta` respectively infinite atomic, atomless singular, and absolutely continuous gives
three infinite-dimensional positive charts inside the same `M(s)`. Each chart retains its pure
spectral type and contains a residual maximal full-complex-translation HT phase. Thus pure point,
singular-continuous, and absolutely continuous spectrum are all orthogonal to maximal translation
HT even after the complete moment sequence and formal asymptotic germ are fixed. Componentwise mean
constraints further retain any prescribed mass vector in the full spectral-type simplex without
losing jet controllability.

## Canonical Bauer-retract refinement `[PROVED IN COMPANION CARD]`

The companion theorem `nevanlinna-boundary-bauer-retract-maximal-ht.md` identifies the intrinsic
geometry organizing the preceding barycenters. The projective support-label map

```text
pi(x)=[-D(x):C(x)]
```

pushes every representing measure to a probability on the Nevanlinna boundary. Extremal
barycentring `Beta` has `pi_*` as a continuous affine left inverse, so

```text
R_s=Beta compose pi_*
```

is a continuous affine idempotent on the entire moment fiber. Its image is canonically affinely
homeomorphic to the Bauer simplex of all probabilities on `RP^1(R)`. Projective relabelling under a
change of Nevanlinna matrix cancels between `Beta` and `pi_*`, so `R_s` is normalization-independent.

Dually, `R_s` is generated by the intrinsic idempotent weak-Feller kernel
`Q_s(x,dy)=mu_(pi(x))(dy)`. Its stationary laws are exactly the Bauer retract, its ergodic laws are
the `N`-extremals, and it sends every monomial to the prescribed moment constant in one step. The
constraint therefore produces a canonical projector rather than a generative flow.

Every infinite closed boundary subset supplies a closed face of this simplex, and the
parameter-measure controllability theorem makes maximal full-complex translation HT dense residual
on every such face. Thus the spectral-type theorem is one visible stratification of a larger
universal projective probability modulus forced inside every indeterminate complete-moment
constraint.

The further companion `moment-polynomial-blind-resolvent-complete-boundary-splitting.md` identifies
the Hilbert geometry of this modulus. For every stationary boundary mixture, the constraint
projector is conditional expectation onto `pi`; its mean-zero horizontal space is orthogonal to
every polynomial, while the conditional Cauchy resolvents span that horizontal space. Thus
complete moments erase exactly a named boundary coordinate which finite-centre analytic data
recovers completely. The residual HT phase is located in this resolvent-visible,
polynomial-invisible direction.

More sharply, one scalar Cauchy value at a fixed nonreal point selects an `N`-extremal leaf, and
one complete Taylor germ at any regular nonreal point determines an arbitrary boundary probability
law. This finite-centre determinacy is opposite to the all-order upper-infinity germ, which remains
constant on the entire Bauer simplex.

The threshold companion `finite-jet-aperture-complete-germ-closure-law.md` proves the missing
intermediate classification. After any finite packet of finite-centre Cauchy jets is fixed exactly,
the positive boundary chart remains infinite-dimensional and maximal full-translation HT remains
residual at fixed spectral type. The intersection of all jet levels at one regular point is a
singleton. Thus the carrier passes from maximal aperture to rigidity precisely at coherent germ
completion, not at any finite derivative order.

## Constraint-fiber phase law `[PROVED HERE]`

Write `Pi_infinity(mu)` for the complete formal asymptotic data of all fixed translates and
derivatives of `m_mu` at upper infinity. For every normalized Hamburger moment sequence:

1. `M(s)` is a singleton exactly in the determinate phase.
2. In the indeterminate phase, `Pi_infinity` is constant on the entire compact convex fiber.
3. In that same phase, a dense residual set of lifts of this one formal point has maximal
   differential rank under every finite configuration of complex translations.
4. Equivalently, no nonzero finite-shift differential polynomial over `C(z)` vanishes on every
   Cauchy transform in an indeterminate complete-moment fiber.

The last statement is intrinsic: the common differential-translation ideal of the fiber is zero.
The geometric law is therefore a collapse/explosion pair:

```text
complete moment fiber --formal asymptotic quotient--> one point,
complete moment fiber --global differential translation--> residual maximal rank.  (32)
```

This removes every choice of extremal parameters and barycentric weights from the conclusion. The
simplex is only the local control chart used to prove a canonical theorem about all of `M(s)`.

## Selector aperture law `[PROVED HERE]`

The proof isolates the exact positive constraint required of any marked carrier. Let
`S subset M(s)` be a Baire subspace. For a finite translated evaluation packet `J`, call a map

```text
theta:V -> S,  theta(0)=mu,                                  (33)
```

a **full local `J`-aperture** if `V` is finite-dimensional, `theta` is smooth after applying the
jet-evaluation map, and

```text
D_0(E_J o theta):V -> Jet(J)                                (34)
```

is onto. Say that `S` is densely aperture-complete if every nonempty relatively open subset of
`S`, every relation pattern, and every local compact translation patch contains the centre of such
an aperture, with surjectivity persisting over that patch.

Then a dense residual subset of `S` has maximal differential rank under all finite configurations
of complex translations. Indeed, (34) makes the packet map a submersion. The rank-defect variety
has codimension larger than the configuration patch after enough evaluation rows are chosen, so
parametric transversality makes its avoidance dense; compact-patch continuity makes avoidance open;
and the countable pattern intersection is residual.

The contrapositive is the carrier constraint:

> **If every point of a marked subfiber `S` satisfies one fixed nonzero finite-shift differential
> law, then `S` is locally jet-deficient for that law's rank pattern everywhere. In particular, a
> successful selector must destroy at least one finite Cauchy-jet aperture; merely choosing a
> topologically large, convexly stable, or infinitesimally extremal-mixing-stable subfiber cannot
> create differential rigidity.**

For `S=M(s)`, the maps (27) supply the required apertures in every weak neighbourhood. The new
geometric datum demanded from an RH carrier is therefore not just “a canonical choice,” but a
**jet-deficient source marking** whose defect can be exhibited at a finite translated packet.

## Concrete Xi carrier gate check `[FORMALIZED INPUT]`

The current Xi/Hedenmalm carrier does not remain in the unpointed Hamburger-fiber regime. Its
“moments” are the Taylor coefficients of the analytic germ

```text
G(z)=normalizedPrimeArchMomentGerm(z),                       (35)
```

and the source supplies the nonflat pointing

```text
continuedPrimeArchSourceRelativeTrace(z)=-z G(z).            (36)
```

The unconditional Lean module `RHTower/XiHedenmalmMomentDeterminacy.lean` verifies the exact chain:

1. `normalizedPrimeArchMomentGerm_allOrder_determinate`: the complete Taylor jet of `G` determines
   `G` locally inside the analytic-germ category;
2. `normalizedPrimeArchMomentGerm_allOrder_determines_sourceTrace`: that jet recovers the
   distinguished Euler--Gamma trace through (36);
3. `XiC_unique_entire_solution_of_pointedMomentConstraint`: together with `XiC(0)`, the local
   constraint `XiC'=-z G XiC` determines `XiC` globally among entire solutions;
4. `xiHedenmalmBezoutian_eventuallyEq_pointedMomentBezoutian_offDiagonal`: the same pointed germ
   reconstructs the central off-diagonal Hedenmalm--de Branges Bezoutian.

Thus this concrete route crosses the present selector law by changing category: it uses a pointed
finite-centre analytic jet, where quasianalytic uniqueness holds, rather than an unpointed
asymptotic moment germ at infinity, where `Flat_infinity` is nonzero. The moment-fiber theorem does
not rule the route out.

It also isolates the remaining RH-bearing obligation more sharply. Source selection is already
rigid; what is not proved is the **global orientation** of the reconstructed kernel--a positive,
source-derived Gram factorization or equivalent de Branges/Weil sign law. Maximal HT, moment
determinacy, and analytic continuation do not supply that orientation.

## RH-facing consequence

Moment, Hankel, Markov, de Branges, or spectral routes can use an all-order moment sequence as an RH
carrier only after proving that the relevant moment problem is determinate or after selecting a
proper marked subfiber from Euler/Gamma/source data. An unpointed indeterminate moment sequence,
even the complete one, has zero common differential-translation ideal and leaves residual maximal
HT freedom across the entire complex translation plane.

Positively stated, a successful moment carrier must contain **selection data transverse to the
formal moment shadow**. Determinacy is one such selector. A canonical Nevanlinna parameter,
specified Friedrichs/Krein-type extremal boundary condition, Stokes-scale marking, or Euler-source
boundary condition could be another. Bare extremality is insufficient by (28). The marking must
cut the compact fiber in a way not visible to any algebraic-order moment asymptotic.

This does not assert that the Xi reciprocal-moment problem is indeterminate. It identifies the
general HT law that such a route must cross.

## Parent-theory and novelty attack

1. `[SEARCH]` Nevanlinna parametrization and the Möbius identity are classical.
2. `[SEARCH]` Convex mixtures of representing measures preserve all moments.
3. `[BRIDGE]` The coefficient-uniform Baire detector is existing HT infrastructure.
4. `[BRIDGE]` Flat HT invisibility and faithful analytic translation state behind a zero formal
   asymptotic shadow already occur in `asymptotic-flat-ht-invisibility.md` and
   `ray-complete-flat-translation-faithfulness.md`. Flatness alone is not new.
5. `[SEARCH]` The full solution set is classically parametrized by arbitrary Pick functions, and
   its convexity is standard. The 1995 Berg survey records the Nevanlinna matrix and minimal
   exponential type; Pruckner--Reiffenstein--Woracek (2026) gives the current primary formula and
   growth theorem. Valent (2005) emphasizes the determinate/indeterminate asymptotic divide.
6. `[SEARCH 2026-07-12]` Exact searches combining indeterminate moment fibers, Baire category,
   Cauchy transforms, hypertranscendence, and differential-algebraic independence found no theorem
   asserting generic translation independence on the representing-measure fiber. This is evidence,
   not a priority proof.
7. `[CANDIDATE RESIDUE]` The mean-zero parameter-pole controllability theorem, the upgrade from one
   auxiliary simplex to a dense residual theorem on the entire compact moment fiber, and the
   intrinsic formal-collapse/global-rank-explosion law were not found in the searched literature.
8. `[SEARCH + COROLLARY]` Density of finite-order canonical extreme solutions is classical. Its
   intersection with the full-fiber HT phase proves the new route-level conclusion that extreme
   maximal-HT solutions are dense `G_delta`; the classical density theorem itself is not claimed.
9. The result remains `[NOVELTY UNVERIFIED]`. It must be downgraded if specialist review finds the
   full-fiber theorem to be an existing generic transversality result for moment solutions.

No numerical experiment or RH assumption enters the proof.

## Preliminary significance score

After the full-fiber, extreme-boundary, spectral-type-simplex, canonical Bauer-retract,
polynomial-blind/resolvent-complete splitting, and finite-jet / complete-germ threshold upgrades,
the route is an internal **90/100 candidate**, with a deliberately wide **72--94** range pending
specialist proof and priority review. The earlier escalating self-scores were withdrawn: theorem
count is not evidence of field-level significance.

- **Why materially above the retired 27-point paper:** this is not a Cartesian coexistence package.
  The Nevanlinna parametrization intrinsically turns one exact all-moment constraint fiber into the
  Cauchy control variable that produces HT freedom. The conclusion is now choice-free: it concerns
  a dense residual subset of the whole compact representing-measure fiber, fixes every moment,
  every formal translated derivative asymptotic, and positivity, then proves full complex
  translation rank. The zero-common-ideal statement is a canonical invariant of the constraint
  fiber rather than a feature of a chosen coordinate chart. The dense extreme-point strengthening
  additionally rules out bare extremality as a selector, while the companion disintegration
  theorem rules out pure spectral type as a selector. The Bauer-retract theorem then replaces the
  auxiliary parameter chart by a canonical normalization-free affine idempotent on the whole
  carrier and locates the residual HT phase on every infinite closed face of its universal
  projective probability simplex. The Hilbert splitting then proves that all centered polynomials
  lie vertically while conditional resolvents linearly recover the entire horizontal boundary
  space. The threshold theorem then proves residual maximal HT in every exact finite-jet level and
  uniqueness at the complete-germ limit.
- **Why it now has a plausible 90 case:** the new residue is a canonical geometric
  invariant and a testable source-selection obstruction, not merely coexistence or a genericity
  statement in chosen coordinates. It specifies exactly which universal modulus a rigid carrier
  marking must cross.
- **Why 90 is not yet verified and 100 is remote:** Nevanlinna parametrization, moment-preserving convexity, Choquet
  probability simplices, flatness, and parametric transversality are established parents.
  Specialist priority review is incomplete; genericity is residual rather than an explicit
  source-canonical point; the Xi orientation sign remains open; and the exact theorem is not
  unconditionally formalized in Lean.

## Lean status

The tree already formalizes real Cauchy-jet controllability and coefficient-uniform polynomial
escape for unconstrained discrete mass gauges. It does not formalize indeterminate Hamburger moment
problems, Nevanlinna matrices, extremal representing measures, barycentric measure mixtures, or the
mean-zero parameter-pole theorem. No Stage 3 claim is made.

## Gates

- [x] project prior-research collision search
- [x] preliminary exact literature search
- [x] primary Nevanlinna formula and convention fixed
- [x] Nevanlinna parameter proved translation-aperiodic
- [x] barycentric same-all-moment theorem proved
- [x] all translated derivative differences proved flat to every algebraic order
- [x] mean-zero parameter-jet controllability proved
- [x] countable residual maximal translation HT proved
- [x] all-complex-configuration strengthening
- [x] weak compactness and metrizability of the entire representing-measure fiber
- [x] uniform weak continuity on compact translation patches
- [x] dense residual maximal translation HT on the canonical full fiber
- [x] zero common finite-shift differential ideal
- [x] dense `G_delta` extreme-point maximal-HT strengthening
- [x] pure-point / singular-continuous / absolutely-continuous HT stratification companion theorem
- [x] canonical normalization-independent Bauer-retract and closed-face HT companion theorem
- [x] constraint Markov projector and stationary/ergodic law companion theorem
- [x] polynomial-blind / resolvent-complete boundary Hilbert splitting companion theorem
- [x] finite-jet aperture / complete-germ closure threshold companion theorem
- [x] jet-deficient selector necessity law
- [x] concrete pointed Xi analytic-germ carrier classified on the rigid-selection side
- [ ] specialist moment-problem and differential-algebra literature gates
- [ ] unconditional Lean formalization of the exact theorem

## Log

- 2026-07-12 -- Opened after finite constraint incidence reduced to standard annihilator and
  Schubert geometry. The surviving non-finite constraint is the entire moment fiber of an
  indeterminate Hamburger problem.
- 2026-07-12 -- Fixed the primary convention `m_tau=(A tau+B)/(C tau+D)` from arXiv `2307.10748`,
  used the canonical-system determinant identity `AD-BC=1`, and derived the parameter-Cauchy
  identity.
- 2026-07-12 -- Proved the mean-zero jet theorem by triangular parameter-pole elimination and
  completed the coefficient-uniform Baire proof for every countable palette transverse to the
  period subgroup of `q=-D/C`.
- 2026-07-12 -- Promoted the theorem to every finite configuration transverse to the period group
  by a rank-defect codimension estimate and real parametric transversality. A continuum-size
  translation transversal is therefore differentially free for residual densities in one exact
  all-moment fiber.
- 2026-07-12 -- Proved that every pair of fiber transforms has identical formal asymptotic
  expansions after every fixed translation and derivative. The residual maximal HT theorem now
  lives inside one flat differential-translation coset, isolating the genuinely nonperturbative
  carrier law.
- 2026-07-12 -- Proved the period group is trivial: nonreal periods violate real-pole confinement,
  while real periods force linear pole density, impossible for the minimal-exponential-type
  Nevanlinna denominator. The residual theorem now covers the full complex translation family.
- 2026-07-12 -- Upgraded the auxiliary-simplex result to the entire representing-measure fiber.
  Proved weak compactness and metrizability from moment tightness and uniform integrability, uniform
  weak continuity of translated Cauchy jets on compact configuration patches, and density by
  infinitesimal insertion of the jet-ample extremal simplex. The canonical conclusion is a
  formal-collapse/global-rank-explosion phase law: the full fiber has one asymptotic shadow and a
  dense residual set of maximally translation-HT lifts.
- 2026-07-12 -- Extracted the selector aperture law. Any Baire marked subfiber that remains densely
  locally onto finite translated Cauchy-jet packets inherits residual maximal translation HT.
  Therefore a carrier enforcing a universal differential law must be locally jet-deficient for a
  finite rank pattern; source marking must destroy an aperture, not merely choose a large subfiber.
- 2026-07-12 -- Combined the canonical residual theorem with the classical density of finite-order
  canonical extreme solutions. Since the extreme boundary is dense `G_delta`, extreme measures
  with maximal full-complex translation HT form a dense `G_delta` of the entire fiber. Bare
  extremality is therefore not a rigidity selector. Checked the current Lean Xi carrier against
  the law: its pointed finite-centre analytic germ uniquely reconstructs the Euler--Gamma trace,
  `XiC`, and the local Bezoutian, so it crosses selection; global kernel orientation remains open.
- 2026-07-12 -- Stratified the maximal-HT phase by spectral type in a companion theorem. Arbitrary
  infinite-support measures on the Nevanlinna parameter line transport pure point,
  singular-continuous, or absolutely continuous type into the same complete moment fiber, while
  bounded mean-one parameter reweightings retain full Cauchy-jet controllability. Each type now has
  its own residual maximal full-translation HT chart.
- 2026-07-12 -- Identified the normalization-independent boundary-Bauer retract: the projective
  support-label pushforward is a continuous affine left inverse to extremal barycentring. The
  resulting idempotent is canonical on the full moment fiber, contains the full closed-face lattice
  of the Nevanlinna boundary, and carries residual maximal translation HT on every infinite face.
- 2026-07-12 -- Proved the Hilbert boundary splitting companion. On every stationary boundary
  mixture the constraint projector is conditional expectation onto the support label; all centered
  polynomials are vertical, while conditional Cauchy resolvents span the entire horizontal space.
  This locates the residual HT phase in a polynomial-invisible, resolvent-complete coordinate.
- 2026-07-12 -- Proved the finite-jet aperture / complete-germ closure companion. Every exact finite
  Cauchy-jet level retains infinite positive aperture, fixed spectral type, and residual maximal
  translation HT; the complete Taylor germ at one regular point determines the boundary law.
