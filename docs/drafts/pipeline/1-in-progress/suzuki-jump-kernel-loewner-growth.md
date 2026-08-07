# Suzuki prime--Gamma jump-kernel Loewner growth

- **ID:** `suzuki-jump-kernel-loewner-growth`
- **Stage:** 1-in-progress
- **Type:** RH-SUFFICIENT SOURCE CONJECTURE
- **Status:** `[OPEN CORE] [SOURCE-PURE] [NO RH PREMISE]`
- **Proved reduction:**
  `../2-fully-proven/new_scientific_knowledge/suzuki-jump-kernel-loewner-growth-gap.md`

## Goal

Use one large aperture and finite dyadic pair selected unconditionally by
`suzuki-screw-cesaro-curvature-recurrence.md`.  For reflection-odd normalized source Pick kernels
`H_lambda` and zero-shift Xi-multiplier kernel `K_0`, prove on every finite upper-half-plane node
set

```text
2(H_(-L)-H_(-2L)) >=_Loewner K_0-H_(-2L).             (1)
```

Exact formal connector proves `(1)` is equivalent to positivity of actual normalized sewn jump
Pick kernel.  Existing pole tomography then proves RH.

## Corrected producer `[CONJECTURE]`

The former prime--Gamma-only square is false: direct Neumann comparison cancels only from the
central residue.  At full frequency it leaves the exact projective holonomy

```text
N_L(z)
 =L sin(az)/z
   [W_(-2L)'(0)/W_(-2L)(z)-W_(-L)'(0)/W_(-L)(z)].      (2)
```

See the paper-proved positive survivor
`../2-fully-proven/new_scientific_knowledge/suzuki-full-frequency-neumann-holonomy-survivor.md`
and failed-route ledger `../5-failed/suzuki-prime-gamma-only-jump-square.md`.

Write `m_EG,L` for the affine-sewn quotient with the explicit Neumann triangle removed but the
global Xi multiplier retained.  Correct source-before-divisor conjecture is

```text
K_(m_EG,L)+K_(N_L)=B_L^*B_L.                           (3)
```

Start from exact resolvent identity

```text
R_(-L)-R_(-2L)=L R_(-L)R_(-2L),                       (4)
```

polarize actual reflected Euler--Gamma triangle maps, and couple their endpoint terms to the
centered projective characteristic tangent in `(2)`.  The latter has exact finite-update form

```text
N_L(z)=2L^2 sin(az)/(2z)
 [d J(z)-J'(0)W_(-2L)(z)]/[W_(-2L)(z)W_(-L)(z)],       (5)
```

in the characteristic gauge `W_(-L)=W_(-2L)+LJ`, `d=W_(-2L)'(0)`.

## Decisive tests

- Prove full finite-node quadratic form, not diagonal/central shadow.
- One negative two-node determinant falsifies `(3)`.
- Common characteristic gauge must be fixed before subtraction.
- Finite Donoghue kernel is inadmissible: wrong divisor.
- Functional-equation--Schwarz orbit insertion must fail `(1)` visibly in source term.
- Any derivation dropping `N_L` is already falsified even if its central residue calculation is
  correct.
- If compensated square fails, retain exact Loewner equivalence and seek signed/Krein
  factorization of the coupled Euler--Gamma/holonomy kernel.

## Completion chain

```text
(3) -> (1) -> full jump Pick positivity -> no nonreal Xi pole -> RH.
```

## Log

- 2026-07-22 — Created after central selector was closed by screw-Cesaro recurrence.  Actual sewn
  quotient and Pick kernel were decomposed exactly; full RH burden reduced to `(1)`.
- 2026-07-22 — hostile test killed prime--Gamma-only producer: Neumann comparison has an exact
  noncentral projective-holonomy survivor.  Replaced it by compensated square `(3)`.
- 2026-07-22 — second hostile test killed bare `RESOLVENT-BIANCHI-SQUARE`.  For
  `R_lambda(t)=1/(t-lambda)`, exact affine defect is
  `alpha beta/[t(t-alpha)(t-beta)]`, hence has sign `t` under source-relevant negative shifts.
  Anti-resolvent sewing is a Krein square: positive on positive restricted-Weil coordinates and
  negative on negative coordinates.  Actual open core is now the sharper
  `SUZUKI-GLOBAL-LOCAL-KREIN-WELD`: prove explicit coupled Euler--Gamma/Neumann completion pays
  exactly the negative spectral debt while retaining Xi divisor.  See
  `../2-fully-proven/new_scientific_knowledge/suzuki-affine-resolvent-krein-defect.md`.

## 2026-07-22 frontier correction

Equation `(4)` alone cannot prove `(3)`.  Its exact scalar output is a signed factorization.  In
anti-resolvent orientation, local diagonal weight is

```text
D_(alpha,beta)(t)
=alpha beta/[t(t-alpha)(t-beta)]
=sgn(t) omega_(alpha,beta)(t),   omega>0.               (6)
```

For arbitrary global target `g`, exact target gap is

```text
G_g(t)=D_(alpha,beta)(t)+C_g(t),
C_g(t)=-R_0(t)-g(t),
G_g(t)>=0 iff C_g(t)>=-D_(alpha,beta)(t).               (7)
```

Every negative node therefore creates exact positive completion debt `omega(t)`.  Conjecture `(3)`
must be proved by source identity showing coupled Euler--Gamma exterior and Neumann projective
holonomy cancel this negative part.  Identifying global `K_0` with local zero-shift resolvent would
erase `(7)` and assume missing RH-bearing weld.

## 2026-07-22 bipolarization sharpening

The local completion in `SUZUKI-GLOBAL-LOCAL-KREIN-WELD` is no longer arbitrary.  Let `J` be the
independently fixed Xi-real quarter-turn, `R` the FE coefficient reflection, and `Omega_theta` the
weld area.  Paper theorem
`../2-fully-proven/new_scientific_knowledge/suzuki-xireal-fe-bipolarization-completion.md` proves

```text
Q+_theta=[Omega_theta(.,J.)+Omega_theta(.,R.)]/2,
Q-_theta=[Omega_theta(.,J.)-Omega_theta(.,R.)]/2,
K_theta=Q+_theta-Q-_theta,
K_theta+Q-_theta=Q+_theta>=0.                          (8)
```

Completion in negative-light direction at coefficient `kappa` is nonnegative on every vector iff
`theta>=0` and `kappa>=theta`.  For each negative spectral coordinate, unique minimal rate is exact
debt `theta=-D_(alpha,beta)(t)`.  Operators `(J+R)/2` and `(J-R)/2` are square-zero rank-one
triangle directions.

Sharpened source conjecture `SUZUKI-XIREAL-FE-BIPOLARIZATION-WELD` is:

> common-gauge Euler--Gamma exterior plus Neumann projective holonomy realizes negative square-zero
> triangle `(J-R)/2` with coefficient at least `-D(t)` on every negative block, coherently across
> every finite node set, with no Xi-divisor data.

This exact source identification, not local completion algebra, is current frontier.

## 2026-07-22 finite negative-block Schur target

Paying diagonal debt in `(7)` is not enough when full-frequency Neumann holonomy couples positive
and negative spectral channels.  Exact two-channel form

```text
Q(x,y)=a x^2+2bxy+(c-n)y^2,   a>0, n>0
```

satisfies

```text
Q>=0  iff  c>=n+b^2/a.                                  (9)
```

Term `b^2/a` is strict Schur holonomy tax.  At fixed aperture restricted-Weil negative subspace is
finite-dimensional.  In block form current source conjecture is therefore exact finite condition

```text
C_---N-C_-+(P+C_++)^(-1)C_+- >=0.                      (10)
```

This is `SUZUKI-FINITE-NEGATIVE-BLOCK-WELD`.  It is stronger and sharper than saying completion
“cancels negative modes.”  One negative finite Evans determinant refutes it; proving it gives full
jump positivity and RH.  See
`../2-fully-proven/new_scientific_knowledge/suzuki-krein-schur-holonomy-tax.md`.

## 2026-07-22 coherent completion target

Spectral calculus removes remaining ambiguity in negative-block completion.  With restricted-Weil
operator `A` and `R_lambda=(A-lambda I)^(-1)`, affine defect operator is

```text
D=sgn(A) W,
W=alpha beta |A|^(-1)(A-alpha I)^(-1)(A-beta I)^(-1)>=0. (11)
```

Unique minimal commuting positive correction is

```text
D_-=1_(-infinity,0)(A)W.                               (12)
```

For source vectors `Gamma(z)`, its coherent all-node kernel is fixed:

```text
K_-(z,w)=<W^(1/2)P_-Gamma(w),W^(1/2)P_-Gamma(z)>.       (13)
```

At fixed aperture this is finite rank.  Revised analytic conjecture
`SUZUKI-NEGATIVE-PROJECTOR-TRIANGLE-IDENTITY` asks actual common-gauge reflected Euler--Gamma plus
Neumann completion to equal `(13)` plus positive kernel in fixed Xi-real/FE negative-light
channel.  If source holonomy is not spectrally aligned, taxed Schur condition `(10)` replaces exact
identity.  See
`../2-fully-proven/new_scientific_knowledge/suzuki-negative-projector-coherent-completion.md`.

## 2026-07-22 finite-Morse resolvent-jet replacement

Weighted projector `(13)` is canonical but discontinuous in `A` and not directly generated by
finite shift calculus.  Fixed aperture has only finitely many distinct negative eigenvalues
`lambda_j`.  For one auxiliary shift `rho<inf spec(A)`, put

```text
r_j=1/(lambda_j-rho),
w_j=-D_(alpha,beta)(lambda_j)>0.
```

There is a unique degree-at-most-`k` positive-branch polynomial with

```text
p(0)=0,       p(r_j)=sqrt(w_j).
```

Consequently `p((A-rho I)^(-1))^2` equals weighted negative projector on every negative
eigenspace and only adds positive weight on positive spectrum.  It is a finite source shift jet:

```text
p(R_rho)=sum_(n=1)^k c_n R_rho^n
        =sum_(n=1)^k c_n/(n-1)! partial_rho^(n-1)R_rho. (14)
```

Exact equality with minimal projector is impossible for nonzero finite polynomial: positive
resolvent spectrum is infinite and accumulates at zero, so vanishing there forces polynomial to
be zero.  Positive-tail overpayment is therefore necessary.

Current sharper conjecture is `SUZUKI-FINITE-MORSE-RESOLVENT-JET-DOMINATION`:

```text
K_completion^src(z,w)
-<p(R_rho)Gamma(w),p(R_rho)Gamma(z)> >= 0              (15)
```

on every finite upper-half-plane node set in common gauge.  This single Loewner inequality absorbs
both negative debt and any Schur holonomy tax.  One negative mixed-node determinant falsifies it.
Proving `(15)` gives full jump positivity and RH; matching negative diagonal alone does not.

Paper and Lean theorem:

- `../2-fully-proven/new_scientific_knowledge/suzuki-finite-morse-resolvent-jet-completion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseResolventJetCompletion.lean`.

## 2026-07-22 projective correction and complete jet tomography

Finite-Morse completion `(14)--(15)` is valid for linear affine resolvent defect but is not
canonical for actual Suzuki quotient.  Actual response is projective:

```text
q_lambda=N(u_lambda)/D(u_lambda),
u_lambda=(A-lambda)^(-1)e.
```

On one invariant spectral line common resolvent factor cancels, so Euler--Gamma quotient is
shift-flat even at negative eigenvalue.  This kills linear negative-projector completion as source
producer.  Exact replacement, with affine Neumann channel homogenized, is

```text
U_beta wedge U_alpha
=(beta-alpha)(v,0) wedge (Av,1),
v=(A-alpha)^(-1)(A-beta)^(-1)e.                        (16)
```

See `../2-fully-proven/new_scientific_knowledge/suzuki-homogeneous-projective-resolvent-plucker-lift.md`.

Finite resolvent jets have a stronger positive salvage in representation `(16)`.  On finite
simple cyclic spectral block, zero-constant Lagrange filters in one resolvent isolate every
spectral basis vector.  If `H(v)=(v,0) wedge (Av,1)`, then

```text
H(e_i)=e_i wedge infinity,
H(e_i+e_j)-H(e_i)-H(e_j)=(t_j-t_i)e_i wedge e_j.       (17)
```

Thus source jets generate a basis of entire `wedge^2(V direct_sum R)`: no Neumann homogeneous
coordinate or Euler--Gamma spectral pair can hide from polarized test matrix.

Actual open conjecture is now `SUZUKI-PLUCKER-CD-MATRIX-GRAM`: derive prime--Gamma
Christoffel--Darboux/Green identity factoring full polarized boundary matrix on basis `(17)` as a
positive Gram kernel.  One negative principal minor falsifies it.  Proving it on actual selected
source yields jump Pick positivity and RH.

Paper and Lean:

- `../2-fully-proven/new_scientific_knowledge/suzuki-resolvent-jet-homogeneous-plucker-tomography.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiResolventJetHomogeneousPluckerTomography.lean`.

## 2026-07-22 affine-secant correction: Plücker chord is not full sewn source

Equation `(16)` exactly controls projective difference `q_beta-q_alpha`.  Jump kernel uses weighted
affine intercept

```text
I_(alpha,beta)q=[beta q_alpha-alpha q_beta]/(beta-alpha),
```

which is not determined by Plücker chord.  Under `B -> B+delta D`, every exterior minor is fixed
but `I_(alpha,beta)q` increases by `delta`.

With `x=Bv`, `X=BAv`, `y=Dv`, `Y=DAv`, and homogeneous Neumann coordinate `c`, exact carrier is

```text
I_(alpha,beta)q
=[(X+c)Y-(alpha+beta)xY+alpha beta xy]
 /[(Y-beta y)(Y-alpha y)].                             (18)
```

Spectral expansion of numerator contains diagonal, symmetric-pair, alternating-pair, and
homogeneous Neumann terms.  For opposite shifts, alternating Plücker term vanishes identically
while symmetric term survives.  Thus positive-Grassmannian identity alone cannot prove actual
sewn jump.

Current source conjecture is `SUZUKI-MARKED-SECANT-CD-WELD`: specialize `(18)` to Volterra phase
data

```text
B_z=(1/2)D_z(H_g-H_(r0)A),
c_z=(1/2)D_z(H_(r0)e),
```

and derive prime--Gamma Christoffel--Darboux/Green identity factoring Pick polarization of marked
tensor plus Xi deficit as positive Gram.  This exact identity proves Loewner gap and RH.

Paper, failed route, and Lean:

- `../2-fully-proven/new_scientific_knowledge/suzuki-projective-affine-secant-tensor-lift.md`;
- `../5-failed/suzuki-plucker-only-affine-sewing-producer.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiProjectiveAffineSecantTensor.lean`.

## 2026-07-22 physical Volterra phase target

Complete jet tomography spans homogeneous blade but does not identify actual source functional on
it.  Physical triangle does.  With causal half `V_k`, symmetric coordinate `C_k=V_k+V_k^*`, and
self-adjoint phase `H_k=-i(V_k-V_k^*)`, exact Xi-real triangle split is

```text
-iT_(k,R)=1/2 Fourier[H_k nu]-i/2 Fourier[C_k nu].     (18)
```

Odd phase-one source makes first term even and second odd.  Admissible positivity controls only
`C_lambda`, hence known sine clock.  RH-bearing carrier is `H_lambda`.

Neumann phase `H_r0` is rank-one moment-to-constant map and reproduces exact full-frequency
holonomy.  On resolvent orbit, remaining operator is

```text
Omega=H_g-H_r0*A,                                      (19)
```

plus homogeneous moment coordinate.  Inserting `(19)` into preceding affine-secant theorem gives
complete marked tensor with diagonal, symmetric-pair, alternating-pair, and homogeneous sectors.
Therefore live conjecture remains `SUZUKI-MARKED-SECANT-CD-WELD`: factor Pick polarization of that
marked tensor as positive prime--Gamma Gram, with global Xi multiplier and exact rank-one Neumann
term retained.  One negative principal minor falsifies it.

See
`../2-fully-proven/new_scientific_knowledge/suzuki-volterra-cartesian-phase-defect.md` and
`formal/GaloisForLFunctions/RHTower/SuzukiVolterraCartesianPhaseDefect.lean`.

## 2026-07-22 global-local compound Bezoutian correction

The phrase "marked tensor plus Xi deficit" still left two ambiguities: how local affine chart is
matched to global Xi chart, and how to state kernel across denominator zeros.  Both are removed by
forming one compound projective pair before division.  Write local marked pair `(Q,P)` from
`(18)` and global centered pair

```text
S=XiC',             T=z^2 XiC,
N=Q*T-S*P,          D=P*T.                            (20)
```

Off explicit divisors, `N/D=Q/P-S/T` is exactly full jump response.  More importantly, `(20)` is
division-free and obeys

```text
(Q,S) -> (Q+delta P,S+delta T)  ==>  N unchanged,     (21)
```

for arbitrary pointwise `delta`.  Among every bilinear weld
`aQS+bQT+cPS+dPT`, common-gauge invariance plus vanishing for coincident projective pairs forces
a scalar multiple of `QT-SP`.  Thus compound determinant is canonical, not a chart choice.

For Hermitian cross-Bezoutian `[F,G]=F(z)conj(G(w))-G(z)conj(F(w))`, exact product law is

```text
[N,D]=T(z)conj(T(w))[Q,P]-P(z)conj(P(w))[S,T].        (22)
```

Independent gauges leave relative term

```text
[N+rD,D]=[N,D]+D(z)conj(D(w))(r(z)-conj(r(w))).       (23)
```

Hence earlier affine obstruction needs sharp correction: common pointwise gauge cancels, and real
constant relative gauge is Pick-invisible.  Only relative nonconstant/non-real curvature matters.
Opposite-shift symmetric sectors remain because `(22)` retains `Q`; rank one does not collapse
because determinant is between local and global pairs; fake functional-equation data changes the
global pair and therefore the compound determinant except for genuine projective degeneracy.

The exact source frontier is now `SUZUKI-COMPOUND-BEZOUTIAN-GRAM`: with `Q` built from
`Omega=H_g-H_r0*A` and rank-one holonomy, derive directly from prime--Gamma screw source a positive
Green/Gram factorization of signed kernel `(22)` on one nontrivial aperture.  This is not avoided
because its positivity is RH-bearing; it is attacked after removing representation ambiguity.
One negative principal minor falsifies proposed factorization.  Positive source factorization
gives full jump Pick positivity and RH.

Paper and Lean:

- `../3-formalized/new_scientific_knowledge/suzuki/suzuki-global-local-compound-bezoutian-weld.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiGlobalLocalCompoundBezoutianWeld.lean`.

## 2026-07-22 rooted midpoint Lorentz sharpening

Compound target `(22)` still did not expose local inertia or amount of source completion.  Write

```text
alpha=m-d, beta=m+d, B0=X+c,
U=B0-mx, V=Y-my, F=B0*y-x*Y.
```

Exact marked pair and compound numerator are

```text
Q=U*V-d^2*x*y+m*F,
P=V^2-d^2*y^2,
N=V*(U*T-S*V)+d^2*y*(S*y-x*T)+m*F*T.                (24)
```

Symmetric coefficient diagonal is

```text
(r-m*s)^2-d^2*s^2.                                   (25)
```

Adding rooted diagonal rate `kappa` makes `(25)` nonnegative for all coordinates iff
`kappa>=d^2`; at equality it is one square.  Thus exact missing source mass is halfgap squared,
not unspecified projector.  For dyadic `alpha=-2L,beta=-L`, rate is `L^2/4`.

This debt is physical.  Product resolvent at midpoint obeys

```text
e=(A-m)^2 v-d^2 v,
```

and relative Volterra phase satisfies

```text
Omega(u_mid)+H_r0(e)
=H_g(u_mid)-m H_r0(u_mid)-d^2 H_r0(v).                (26)
```

So rooted channel is literal Neumann phase of midpoint product-resolvent state.  Existing
two-boundary balanced von-Mangoldt--Gamma Grams vanish identically on canonical packet; they
cannot pay `(26)` while marked rank-one intercept survives.  Raw rooted Gamma--Bianchi coordinate
must be retained before boundary compression.

Live open core is now `SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM`: prove signed global Xi term in `(22)`
supplies exact `d^2` rooted Bianchi Gram plus positive archimedean remainder, with common-prime
Julia--Bianchi cross block already forced by corpus.  Then local rooted coefficient
`alpha*beta=m^2-d^2` completes to `m^2`, giving perfect joint square and RH.  One atom coefficient
mismatch or negative finite principal minor falsifies conjecture.

Paper and Lean:

- `../2-fully-proven/new_scientific_knowledge/suzuki-marked-secant-midpoint-lorentz-completion.md`;
- `formal/GaloisForLFunctions/RHTower/SuzukiMarkedSecantMidpointLorentzCompletion.lean`.
