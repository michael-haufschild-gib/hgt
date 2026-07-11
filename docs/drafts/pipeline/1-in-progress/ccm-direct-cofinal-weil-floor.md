# CCM direct cofinal Weil-floor theorem

- **ID:** `ccm-direct-cofinal-weil-floor`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE, `[OPEN RH CORE]`
- **Scientific status:** `[CONJECTURE] [RH-SUFFICIENT]`
- **Parent results:** `ccm-cofinal-weil-spectral-floor-criterion.md`,
  `ccm-rayleigh-transfer-collapses-to-spectral-floor.md`, Suzuki's restricted Weil operator, and
  the CCM radial-prolate incidence laws
- **Statement:** On one cofinal aperture sequence, the lowest eigenvalue of the true even
  restricted Weil operator tends to zero.

## Exact target

Let `A_lambda` be the true compact-resolvent restricted Weil operator in the even sector and put

```text
epsilon_0(lambda)
 =inf{QW(f,f): f in D_lambda, ||f||_2=1}.                        (1)
```

The live CCM theorem is

```text
there exists lambda_j->infinity such that
epsilon_0(lambda_j)->0.                                         (2)
```

By `ccm-cofinal-weil-spectral-floor-criterion.md`, `(2)` implies the full Weil criterion and RH.
It is not a preliminary estimate.

## Quantized form of the target

`ccm-aperture-morse-index-conservation-law.md` replaces the vanishing-error language by the exact
integer carrier

```text
kappa(lambda)=Tr 1_(-infinity,0)(A_lambda).                 (2a)
```

This finite number is nondecreasing with aperture, starts at zero, and satisfies

```text
RH
 <-> kappa(lambda)=0 for every lambda
 <-> ker(G_lambda)=0 for every lambda,                     (2b)
```

where `G_lambda` is Suzuki's compact continuous-kernel screw operator. Thus the positive theorem is
conservation of a quantized aperture charge. A negative eigenvalue cannot be made harmless by
shrinking its magnitude through the logarithmic boundary layer.

## Positive no-negative-birth formulation

Let

```text
N_lambda=(-A_lambda)_+                                          (3)
```

be the negative spectral part. Since `A_lambda` has compact resolvent,

```text
||N_lambda||=max(0,-epsilon_0(lambda)).                          (4)
```

The formal norm statement would be

```text
the negative Weil spectral mass evacuates in operator norm:
||N_(lambda_j)||->0.                                            (5)
```

But `ccm-negative-spectrum-no-evacuation-law.md` proves that the restricted floors are
nonincreasing. Hence `||N_lambda||` is nondecreasing: `(5)` can hold only when

```text
N_lambda=0 for every lambda.                                    (5a)
```

The positive CCM statement is absence of negative spectral birth at every aperture, followed by
approach to the radical from above. It is stronger and more precise than saying that finite
determinants have real zeros or that a specified prolate source has small Rayleigh value.

## Exact Paley--Wiener Toeplitz formulation

Suzuki's Fourier formula for the restricted Weil form is

```text
QW_a(v,v)=1/(2*pi) integral_R w_a(t)|hat(v)(t)|^2dt,             (6)

w_a(t)=log|t|-log(2*pi)
 -2 sum_(n<=exp(2a))Lambda(n)/sqrt(n)*cos(t*log n)
 +hat(r_a'')(t).                                                (7)
```

Here `v` is supported in `[-a,a]`; hence `hat(v)` belongs to the Paley--Wiener space `PW_a`.
Let `P_(PW_a)` denote its orthogonal projection. The bounded-below restricted Weil operator is the
Toeplitz compression

```text
T_a=P_(PW_a) M_(w_a) P_(PW_a).                                  (8)
```

Consequently the exact live theorem is the uncertainty lower bound

```text
integral_R w_a(t)|F(t)|^2dt
 >=-eta_a integral_R |F(t)|^2dt
for every F in PW_a,
eta_a->0.                                                       (9)
```

This is `(5)` in native coordinates. The prime cutoff `n<=exp(2a)` and the exponential type `a`
must grow together; separating either one produces only a finite approximation.

## What the completed radial analysis supplies

The constrained prolate work now proves:

1. exact cofinal radial prime response, including the infinite radial multiplier;
2. exact scalar leading archimedean law
   `A(R_lambda)=log(c)||R_lambda||^2+O(d_1)`;
3. two or more fixed-depth orthogonal trial vectors with Rayleigh values tending to zero;
4. finite-Gamma completion supplies one archimedean valuation direction while the prime incidence
   remains an infinite divisibility carrier.

These results prove upper bounds on the first fixed spectral levels. They do not prove `(5)`,
because a negative vector may lie outside every fixed prolate trial subspace.

## Three competing positive mechanisms

### A. Paley--Wiener Toeplitz contraction

`[CONJECTURE]` Split the exact symbol `(7)` as

```text
w_a=d_a-k_a,                                                    (10)
```

where `d_a` is a positive reference symbol after the exact constant/radical mode has been removed
and `k_a` is the complete prime-incidence part. Prove on `PW_a`

```text
||D_a^(-1/2)K_a D_a^(-1/2)||<=1+eta_a,
eta_a*||D_a||->0,                                               (11)
```

where `D_a=P_(PW_a)M_(d_a)P_(PW_a)` and similarly for `K_a`. Then `(11)` gives `(9)`.
The load-bearing point is that `K_a` must retain the truncated-divisor weighted infinite
radial carrier; a finite-prime or finite-rank contraction is insufficient.

### B. No-negative-birth theorem

`[CONJECTURE]` Let `P_lambda^-` be the negative spectral projection. Prove

```text
P_lambda^-=0 for every lambda.                                  (13)
```

Strong convergence or asymptotic smallness is not an alternative: nested-floor monotonicity shows
that any negative vector at one aperture survives as a uniform negative upper bound at every later
aperture.

### C. Trace-ideal negative mass

`[CONJECTURE]` Construct a trace-class negative part and prove

```text
Tr(N_lambda)->0.                                                 (9)
```

Since `||N_lambda||<=Tr(N_lambda)`, `(9)` implies `(5)`. This mechanism is compatible with the
Connes--Sonin trace architecture, but only if the trace sees every omitted radial/divisor channel.

## Attack and selection

- Fixed-dimensional prolate ladders cannot prove `(5)`; they control only trial upper bounds.
- Compact-open germ, finite Gamma rank, or finite determinant data cannot prove `(5)`; the corpus
  relocation and maximal-quotient theorems make them transverse-blind.
- Strong convergence of negative projections cannot prove `(5)` without norm control.
- A finite Schur matrix cannot prove `(5)` without kernel/channel exhaustion.

Mechanism A is the preferred attack because `(7)` is the exact finite-prime symbol and `PW_a` is
the exact aperture constraint, while the radial work supplies the complete arithmetic incidence
weights. The next theorem must be an infinite-carrier compressed-multiplier estimate, not a new
source vector.

## Exact next lemma

There are now two exact, source-compatible versions of the next lemma.

The aperture version is the injectivity law

```text
ker(G_a)=0 for every a>0.                                  (12a)
```

The Euler-resolvent version uses

```text
A_w(alpha)=w/(w^2+alpha^2),
B_w(alpha)=alpha/(w^2+alpha^2),
Re w>1/2.                                                  (12b)
```

`critical-logderivative-two-channel-weil-resolvent-law.md` proves the unconditional identity

```text
(L(w)+conjugate(L(v)))/(w+conjugate(v))
 =q_W(A_w,A_v)+q_W(B_w,B_v),                              (12c)
```

where `L(w)=d/dw log xi(1/2+w)`. It also proves that this two-channel family is complete for RH.
Hence the source-side alternative is to construct a compatible Gram factorization of every finite
matrix in `(12c)` from the absolutely convergent Euler--Gamma formula in `Re w>1/2`.

Equivalently, in the original Paley--Wiener coordinates one may still prove the source-free
Toeplitz inequality

```text
<T_a F,F>
 >=-eta_a||F||_2^2
for every even F in PW_a,
eta_a->0.                                                       (12)
```

Equation `(12)` is exactly `(5)`. But `(12a)` and `(12c)` show the sharper positive architecture:

```text
Euler two-channel Gram positivity
  -> index-preserving transport into the growing screw spaces
  -> no finite-aperture kernel birth
  -> conserved zero Morse charge
  -> RH.                                                     (12d)
```

The transport must be uniform on the entire relevant closure and must use the complete
prime/source incidence, including the high radial divisor tail. Matching finitely many resolvent
entries does not preserve inertia.

The proved neutral signed-Gamma boundary law makes the carrier requirement quantitative. At prime
cutoff `N`, any recurrent DA realization must allocate

```text
pi(N)
 <=delta_beta+2m(n+1)+rank_Q A_N,                          (12e)
```

with `delta_beta in {0,1}` and `A_N` the complementary arithmetic module. Hence the Gram/aperture
transport in `(12d)` must visibly carry `A_N` unless its differential-state complexity grows
cofinally. Gamma logarithmic phases, polynomial jets, and Stokes corrections cannot be counted as
that module.

The stronger orbit-charge dichotomy and
`ccm-compressed-prime-shift-arithmetic-complement-law.md` identify this module exactly. If `D` is
the rational phase space carried by the finite signed-Gamma completion, then

```text
A_N=V_N/(V_N intersection D),
V_N=span_Q{log p:p<=N}.                                  (12f)
```

The compressed weighted shifts `T_(A,log p)` are linearly independent whenever `log N<A`, and
their operator quotient by the image of `V_N intersection D` is canonically isomorphic to `A_N`.
Thus the CCM source already possesses the forced complementary carrier. The remaining theorem is
not to invent arithmetic state: it is to factor the completed form positively while preserving the
inertia of this explicit quotient through the cofinal aperture limit.

The corpus-level factorization of that carrier is now recorded in
`ccm-sonin-three-grade-relative-carrier-law.md`. The canonical source has three inseparable grades:

```text
noncompact principal Calkin shell carrying A_N
  + Hilbert--Schmidt linear cross carrying the unsquared log(p^m) coefficient
  + positive trace-class residual Gram.                  (12g)
```

The first grade is too large for an all-prime compact sum, the third deletes the principal mode and
squares coefficients, and the second has no canonical trace without a genuine relative
functional. Therefore the preferred version of the Gram/aperture transport in `(12d)` is a closed
principal--relative extension carrying all three grades, followed by a cofinal contraction whose
principal symbol is faithful on `A_N` and whose degree-one functional is Connes's semilocal
logarithmic trace.

The degree-one operator is explicit before Sonin compression. By
`critical-euler-position-commutator-carrier-law.md`, logarithmic position `X_A` and the skew Euler
logarithm `Z_A` satisfy

```text
[X_A,Z_A]
 =sum_(n<e^A)Lambda(n)/n
    (T_(A,log n)+T_(A,log n)^*).                         (12h)
```

The coefficient of the `p^k` term in `Z_A` is exactly `1/(k p^k)`, while the commutator produces
the orbital length `log(p^k)`. Hence the next construction is no longer an unspecified relative
functional: it is the closed transport of `(12h)` through the three-grade Sonin carrier and its
coupling to Burnol's Gamma conductor.

Compression no longer introduces an unspecified error term. For any orthogonal constraint `Q`,
the position/Euler commutator obeys

```text
Q[X_A,Z_A]Q
 =[QX_AQ,QZ_AQ]
  +L_(X,A)^*L_(Z,A)+L_(Z,A)^*L_(X,A),                   (12i)
```

with `L_(X,A)=(1-Q)X_AQ` and `L_(Z,A)=(1-Q)Z_AQ`. Under an admissible relative trace the internal
commutator vanishes, so the exact degree-one source is the polarized leakage Gram. The next theorem
is to put these two leakage maps on a common closed graph, identify their relative trace with the
semilocal logarithmic functional, and prove the completed Gamma--prime square/contraction.

### D. Euler-Pick boundary transport

There is a fourth exact interface which bypasses a direct lower bound on `(7)` but does not bypass
the cofinal carrier. Under the CCM simple-even hypothesis, remove the canonical aperture phase and
write

```text
F_(lambda,N)(z)
 =i lambda^(iz)det_reg(D_log^(lambda,N)-z),
G_(lambda,N)(w)=F_(lambda,N)(-iw).                       (12j)
```

Every `F_(lambda,N)` is even with only real zeros. Therefore, with
`L_(lambda,N)=G_(lambda,N)'/G_(lambda,N)`,

```text
K_(lambda,N)(w,v)
 =(L_(lambda,N)(w)+conjugate(L_(lambda,N)(v)))
   /(w+conjugate(v))>=0                                  (12k)
```

on `Re w>0`. By `ccm-euler-pick-logderivative-transfer-boundary-law.md`, the source convergence

```text
L_(lambda_j,N_j)(w)->xi'(1/2+w)/xi(1/2+w)
locally uniformly on Re w>1/2                            (12l)
```

would pass `(12k)` to the complete two-channel Euler kernel and prove RH.

The dephasing is load-bearing. The canonical determinant in the `w` coordinate has logarithmic
derivative `-log(lambda)+L_(lambda,N)`, so its Pick kernel is

```text
K_(lambda,N)(w,v)-2log(lambda)/(w+conjugate(v)).          (12m)
```

Thus self-adjoint finite spectra do not automatically make the normalized source kernel positive.
The existing Mellin convergence lives in `|Re w|<1/2`, whereas `(12l)` lives in `Re w>1/2`.
A successful Pick implementation must construct a positive relative-background renormalization
of `(12m)` or carry the dephased logarithmic derivatives across that exact boundary. This is the
kernel analogue of the divisor-preserving determinant theorem, not a finite-spectrum shortcut.

The phase has an exact two-channel spectral meaning. If `gamma_k(lambda,N)>0` are the positive
zeros of the dephased determinant, then the signed discrepancy

```text
nu_(lambda,N)
 =sum_k delta_(gamma_k(lambda,N))
   -(log(lambda)/pi)d gamma                              (12n)
```

has Gram transform `(12m)`: the subtracted continuum is exactly the Cauchy background
`2log(lambda)/(w+conjugate(v))`. Hence the positive relative-background theorem can be stated
without choosing a phase convention: prove that `(12n)` is nonnegative on the complete
two-channel resolvent-square cone and converges there to the Xi kernel. Reality of the discrete
spectrum alone does not control this signed discrepancy.

The relative logarithmic kernel has an exact finite-stage charge. By
`ccm-relative-logderivative-coordinate-negative-index-law.md`, if

```text
J_(lambda,N)={j:the j-th Fourier coordinate of the ground vector is nonzero},
```

then

```text
ind_- K_(R,lambda,N)=#J_(lambda,N).                       (12o)
```

Moreover every locally uniform divisor-carrying determinant limit has, for some fixed
`delta>0`,

```text
#J_(lambda,N)
 >=2 floor(delta*log(lambda)/pi)+1.                       (12p)
```

Thus the relative negative charge grows at least linearly in logarithmic aperture in every
successful determinant implementation. The periodic background or operator covariance must cancel
that charge index-for-index. Since the background kernel tends to zero on fixed compact subsets of
the Euler half-plane, the realizing negative directions must escape fixed compact strict-margin
node families through growing matrix size, boundary/infinite-node escape, or the near-radical
mechanism. A fixed scalar Herglotz ratio cannot do this; cofinal nonnegative Fourier coordinates are
incompatible with Xi logarithmic-derivative growth.

### E. Mixed source aperture, relative index, and divisor marking

The exact finite-Euler aperture theorem and the relative-coordinate index theorem measure two
different parts of a successful CCM carrier. For a prime cutoff `P`, every first-order-faithful
rational scalar readout `B_P` has differential aperture `pi(P)`. For a CCM relative determinant
with active coordinate set `J_(lambda,N)`,

```text
ind_- K_(R,lambda,N)=#J_(lambda,N).                       (12q)
```

`ccm-euler-observability-relative-index-allocation-law.md` proves the exact bridge. If the scalar
jet sees rank `rho` and a source-defined residue map jointly retains all `pi(P)` Euler directions,
then

```text
pi(P)-rho<=ind_- K_(R,lambda,N).                          (12r)
```

This is an allocation law, not an identification of cutoffs: `P`, `lambda`, and `N` remain
distinct until the construction supplies their incidence map. Directions already visible in the
scalar differential carrier are not counted again in the relative state.

If a source direction enters through a Fourier residue that vanishes at the base point, `(12r)`
must be read stratifiably rather than discarded. The complete residue Jacobian then forces, on an
open dense set of arbitrarily small real source deformations,

```text
ind_- K_R>=pi(P)-rho.                                     (12r1)
```

The missing direction is paid by quantized negative-index birth immediately off the zero-residue
stratum. Hence the cofinal carrier must retain the full residue support stratification, not only
the active-pole index at the zeta point.

At fixed aperture the source-deformed ground-state map is already explicit. Kato response gives

```text
D_h xi_b
 =R_b^perp P_perp v_h xi_b,                              (12t)

D_h F_b=M_lambda(D_h xi_b).                              (12u)
```

The theorem `ccm-generic-ground-separating-incidence-law.md` shows that the compressed prime-shift
space has an open dense set of separating vectors. At a simple ground state in that set, `(12t)`
and `(12u)` are injective in every retained prime direction. Failure is confined to the explicit
Gram-determinant seam

```text
det((<A_i xi_b,A_j xi_b>)_(0<=i,j<=pi(P)))=0.             (12v)
```

The cofinal source-to-spectral theorem is therefore quantitative transversality: prove that the
true von-Mangoldt ground state avoids `(12v)` with a least-Gram-eigenvalue margin strong enough to
survive the reduced resolvent and the growing Mellin evaluation norm.

`ccm-prime-log-crowding-separating-margin-law.md` proves that this margin forces a specific resource.
If `delta_P` is the nearest-neighbour spacing among `{log p:p<=P}` and `D` is the translation
generator, then

```text
sigma_(lambda,P)<=delta_P^2||D xi_lambda||^2/2,           (12v1)
```

up to the fixed factor for symmetric channels, while

```text
delta_P<=log(P/2)/(pi(P)-1)=O((log P)^2/P).               (12v2)
```

Thus every quantitative cofinal incidence must be paid by inverse-spacing oscillation of the true
ground state. The prolate/Sonin carrier is not merely allowed to escape compactness; it is forced
to carry this growing generator energy at whatever rate the determinant-transfer margin demands.
For the genuine degree-one Euler-ray deformation, this applies exactly on the top shell
`e^(A/2)<p<=e^A`, where every ray has only its first shift inside the aperture. The normalized
nearest-neighbour spacing there is `O(A^2e^(-A))`, so a fixed stable margin costs generator norm
at least of order `e^A/A^2`.

One more coordinate is compulsory. The finite divisor--aperture orthogonality law shows that a
symmetric polynomial can insert an arbitrary off-line orbit without changing differential
aperture, HT, FE, Schwarz reality, or order-one growth. Hence even the joint budget `(12r)` is not
an RH selector unless the CCM determinant/kernel incidence is orbit-sensitive. The positive
three-coordinate carrier is

```text
prime-source visibility
  + relative spectral-state capacity
  + a pointed source--divisor marking that changes under every off-line orbit insertion. (12w)
```

The complete Euler Pick kernel already has the required transverse index. The remaining theorem
is to transport that complete inertia, not merely source rank or active-pole count, into the
restricted screw spaces while preserving the cofinal separating margin.

### F. Signed Möbius Schur transfer and the continuation seam

The signed-channel coisometry now has an exact Hardy-space transfer function. With
`sigma=1+2omega`,

```text
tau_omega(z)
 =E_(P_omega)[mu(d)d^(-z)]
 =zeta(2sigma)/(zeta(sigma)zeta(sigma+z))
 =product_p (1-p^(-(sigma+z)))/(1+p^(-sigma)).            (12x)
```

Every local factor has modulus at most one for `Re z>=0`, so

```text
|tau_omega(z)|<=1.                                       (12y)
```

Thus the signed Möbius synthesis is already a source-defined contraction on the Euler side. The
complete coupled floor--tail transform is

```text
L F_omega(z)
 =zeta(1+z)/((1+omega+z)zeta(1+2omega+z))
  -1/((1+omega)z zeta(1+2omega)).                        (12z)
```

This removes “construct an arithmetic contraction” as an open task. The contraction ceases to be
automatic only when the inverse-transform contour is moved to the divisor boundary: the first
term in `(12z)` has possible poles at

```text
z=rho-1-2omega.                                          (12z1)
```

Those crossed poles are exactly the anti-causal zero modes. Therefore the required positive
operator is not bounded functional calculus of `(12x)`. It is an orbit-sensitive meromorphic
continuation graph carrying the residue seam, together with a renormalization satisfying

```text
||ell_E||_2<=||ell_pole||_2=2.                            (12z2)
```

The rational-orbit countermodel shows why the seam is load-bearing: a symmetric polynomial leaves
the Euler-side multiplier `(12x)` unchanged but inserts a nonzero residue vector. Hence any proof
using only the Schur norm, the diagonal squarefree channel law, or a channel-independent bounded
operator is transverse-blind. A viable CCM/Connes construction must preserve the gauge covariance
of the full continued source and transport its faithful residue index into the screw spaces.

The critical Euler-line graph limit is now complete. The centered Schur difference quotient has
the strong Hardy limit

```text
c_omega/z(
  1/zeta(1+2omega+z)-1/zeta(1+2omega)
)
 ->1/(z zeta(1+z)),                                      (12z3)
```

whose inverse Laplace vector is

```text
m_0(t)=sum_(n<=e^t)mu(n)/n in L2(0,infinity).             (12z4)
```

The renormalized floor-remainder component converges strongly to

```text
1/(1+z)-1/(z zeta(1+z)).                                 (12z5)
```

Therefore the complete coupled causal source converges strongly to `e^(-t)`. Failure of causal
convergence and failure of constant-channel graph membership are no longer open explanations.
The RH content is exactly the noncommutation of this strong limit with the meromorphic contour
transfer: crossed poles create the anti-causal residue seam.

### G. The continuation graph must carry inverse-horizontal charge

`orbit-sensitive-continuation-horizontal-charge-norm-law.md` closes the generic bounded-map
version of the continuation problem. A pole at `w=-gamma+i a` has fixed Euler-line norm and
reflected residue energy

```text
||c/(.-w)||_(Im z=Y)^2=pi|c|^2/(Y-a),
||c exp(-a t)exp(i gamma t)||_2^2=|c|^2/(2a).            (12z6)
```

Hence the norm ratio is `(Y-a)/(2*pi*a)` and diverges as the orbit approaches the critical line.
The same divergence survives a full FE--Schwarz rational quartet: its fixed-line source norm is
uniformly bounded for `0<a<=Y/2`, whereas its two right-half residue modes have energy at least
`4m^2/a`.

Consequently there is no universal bounded, or uniformly Lipschitz, gauge-covariant map from the
ordinary Euler-line Hardy norm to the divisor residue space. Any bounded continuation graph `D`
with residue map `J:D->L2` is forced to allocate

```text
||q_(a,gamma)^sym||_D^2>=4m^2/(||J||^2 a).              (12z7)
```

This turns the obstruction into the positive carrier law: the CCM continuation domain must carry
the full Cauchy residue Gram form

```text
R(q)=||Jq||_2^2
 =4 sum_(j,k)m_j m_k/
    (a_j+a_k+i(gamma_j-gamma_k)).                        (12z8)
```

Equivalently it needs explicit residue coordinates, a Pontryagin/Krein realization of those
coordinates, or a genuinely Xi-pointed nonuniform theorem. The first two make continuation an
unbounded closed graph before renormalization. The third must use arithmetic marking that changes
under every symmetric orbit insertion.

Therefore “construct a bounded continuation” is now retired. The remaining RH-bearing statement
is source-specific:

```text
exact Xi source
  -> closed orbit-marked graph carrying R
  -> distinguished pole-to-divisor renormalization
  -> ||ell_E||_2<=2.                                    (12z9)
```

The four-unit theorem shows that `(12z9)` proves RH. It cannot be established uniformly on the
FE--Schwarz gauge family, whose residue charge diverges like `1/a`.

### H. Semilocal Hankel gap-trace slope

The charged graph has a positive trace-class realization. For an anti-causal profile `ell`, define
the shifted Hankel leakage

```text
(H_u f)(x)=integral_0^infinity ell(u+x+y)f(y)dy,
F_ell(u)=Tr(H_u^*H_u).                                   (12z10)
```

The exact Hilbert--Schmidt identity is

```text
F_ell(u)=integral_u^infinity(t-u)|ell(t)|^2dt,
-F_ell'(0+)=||ell||_2^2.                                (12z11)
```

For the incoming Euler pole `ell_pole(t)=2e^(-t/2)`,

```text
F_pole(u)=4e^(-u),       F_pole'(0+)=-4.                (12z12)
```

For the completed off-line divisor profile, the Cauchy threshold gives

```text
RH
 <-> -F_E'(0+)<=4
 <-> F_E'(0+)>=F_pole'(0+).                             (12z13)
```

Thus the source-specific four-unit theorem is equivalently a semilocal trace-slope conservation
law. This avoids unbounded evaluation of the leakage kernel at its boundary corner while retaining
the full inverse-horizontal orbit charge. Its exact source-side candidate is explicit: if the
infinitesimal shifted-Xi leakage `D` can be closed on the meromorphic graph and `V_b` is the
reflected half-line shift, then

```text
D_u=V_(u/2)^* D V_(u/2),       F_E(u)=Tr(D_u^*D_u).     (12z14)
```

On the Euler half-plane, the candidate `D` has the explicit symbol `-2Xi'/Xi`, including the
von-Mangoldt and Gamma terms. The surviving Connes target is to close its meromorphic graph and
control the initial aperture loss. Section K below sharpens this further: full trace class of the
shifted compressions is unnecessary.

Control at one positive aperture is insufficient. The RH datum is the right derivative at the
singular endpoint, so the cofinal transport must be trace differentiable at `u=0` on the
distinguished Xi graph vector.

### I. Canonical closed two-channel source graph

The orbit-sensitive graph itself is now constructed. Let

```text
q_Xi(z)=-2Xi'(1/2-i z)/Xi(1/2-i z),
D_q={f in H2_+:q_Xi f in L2(R)}.                         (12z15)
```

Cartwright bounded-type theory gives

```text
integral_R log(1+|q_Xi(x)|)/(1+x^2)dx<infinity.          (12z16)
```

An outer majorant `a` with `|a|=(1+|q_Xi|)^(-1)` satisfies
`aH2_+ subset D_q`; because `a` is outer, this is a dense core. The paired map

```text
G_Xi f=(P_+(q_Xi f),P_-(q_Xi f))                        (12z17)
```

is closed in the full graph norm. This paired form is essential: closedness belongs to the source
constraint `q_Xi f=g_++g_-`, not to either projected channel in isolation.

The projected anti-causal channel is nevertheless closable. A lower-half-plane outer majorant
`b` with `|b|=(1+|q_Xi|)^(-1)` gives the dense adjoint core

```text
bH2_- subset D((P_-M_(q_Xi))^*).                         (12z17a)
```

Hence

```text
D_Xi=bar(P_-M_(q_Xi)|D_q)                                (12z17b)
```

is a canonical closed unbounded Hankel operator. No trace-class or RH hypothesis is used.

If a rational FE--Schwarz orbit changes the source by `r in L-infinity(R)`, then the graph domain
is unchanged and

```text
(f,g_+,g_-)
 |->(f,g_++P_+(rf),g_-+P_-(rf))                         (12z18)
```

is a bounded invertible graph gauge. For one upper pole `r(z)=c/(z-w)`,

```text
P_-(rf)(x)=c f(w)/(x-w).                                (12z19)
```

Thus each right-half zero is exactly one rank-one evaluation/residue coordinate; a pole of order
`m` gives its finite evaluation jet. This realizes the pointed source--divisor incidence and the
inverse-horizontal charge without assuming RH.

At the operator level, bounded rational gauges satisfy

```text
bar(H_(q_Xi+r))=D_Xi+P_-M_r,
D(bar(H_(q_Xi+r)))=D(D_Xi).                               (12z19a)
```

Thus the full orbit action is an exact finite-rank perturbation law on the closed anti-causal
operator, not merely an isomorphism of paired graphs.

Accordingly, graph construction is no longer open. The entire remaining analytic seam on this
interface is to construct the positive boundary relative trace of the anti-causal channel and prove
its four-unit density bound on the distinguished Xi source.

### J. Quantized index--trace-slope coercivity

The corpus note that divisor winding is the nonperturbative finite-prime charge now couples exactly
to the graph metric. For a finite right-half divisor `D={1/2+a_j+i gamma_j}` with multiplicities
`m_j`, put

```text
kappa(D)=sum_j m_j,
E(D)=-F_D'(0+).                                          (12z20)
```

Here `kappa` is simultaneously denominator-inner degree, shifted-leakage multiplicity, and
prime-zeta monodromy. The Cauchy diagonal and `0<a_j<1/2` give the strict coercivity

```text
E(D)>=2 sum_j m_j^2/a_j
    >4 sum_j m_j
     =4 kappa(D).                                        (12z21)
```

The incoming Euler pole has

```text
kappa_pole=1,       E_pole=4.                            (12z22)
```

Thus the strip boundary is the exact unit-cost threshold: one incoming pole unit has budget four,
while every outgoing transverse divisor unit costs strictly more than four. The positive CCM law
is now a marked resource conservation theorem:

```text
(kappa_pole,E_pole)=(1,4)
  -> exact completed source incidence
  -> (kappa_off,E_off), with E_off>4 kappa_off if kappa_off>0
  + E_off<=E_pole
  -> kappa_off=0
  -> RH.                                                  (12z23)
```

The index prevents divisor charge from dissolving in the cofinal limit; the trace slope supplies
the strict metric cost; the pointed Euler source orients their coupling. This is the same carrier
triple demanded by the finite-prime monodromy, topological boundary-index, and pointed Krein
results in `docs/prompts/notes.md`.

### K. Full trace class is replaced by a boundary relative trace

Let `H_ell` be the Hankel operator with kernel `ell(x+y)`, let `P_a` project onto `[a,infinity)`,
and put `Q_a=I-P_a`. For `u=2a`, define the positive removed-corner trace

```text
Delta_ell(u)
 =||Q_a H_ell Q_a||_(S_2)^2
  +||Q_a H_ell P_a||_(S_2)^2
  +||P_a H_ell Q_a||_(S_2)^2.                           (12z24)
```

Only `ell in L2` is required. Direct first-quadrant geometry gives

```text
Delta_ell(u)
 =integral_0^infinity min(t,u)|ell(t)|^2dt,

lim_(u->0+)Delta_ell(u)/u=||ell||_2^2.                  (12z25)
```

Equivalently,

```text
Delta_ell(2a)
 =||Q_aH_ell Q_a||_(S_2)^2+||[P_a,H_ell]||_(S_2)^2.     (12z25a)
```

This is precisely a local-corner plus cutoff-commutator relative trace.

Thus the residue energy is a boundary relative-trace density even when the full Hankel operator is
not Hilbert--Schmidt. For the incoming pole,

```text
Delta_pole(u)=4(1-e^(-u)).                              (12z26)
```

The exact positive CCM target is therefore

```text
limsup_(u->0+) Delta_Xi(u)/Delta_pole(u)<=1.             (12z27)
```

By `(12z21)`, `(12z27)` forces `kappa_off=0` and RH. This is smaller than a global trace-class
theorem and matches the relative-compression form of the semilocal Connes trace formula. What must
be constructed from the exact source are the three boundary-block traces and their first-order
density, not an absolute trace of the whole continuation operator.

## Gates

- [x] determinant transfer collapsed to the direct floor criterion
- [x] negative-part norm formulation isolated and evacuation excluded
- [x] compact-kernel repair threshold identified
- [x] fixed-source upper bounds separated from global lower bounds
- [x] three possible global mechanisms compared
- [x] exact Paley--Wiener Toeplitz compression identified
- [x] finite-aperture Morse charge isolated and proved monotone
- [x] RH reduced to compact screw injectivity at every aperture
- [x] complete two-channel Euler--Weil resolvent family constructed
- [x] exact arithmetic-complement operator carrier `A_N` constructed
- [x] three-grade principal--relative carrier forced by the formalized Sonin corpus
- [x] exact degree-one Euler position commutator constructed
- [x] exact compressed position/Euler leakage Gram identity constructed
- [x] dephased finite-spectrum Euler-Pick transfer and aperture-phase defect isolated
- [x] relative coordinate negative index and logarithmic cofinal charge floor proved
- [x] exact scalar-observability/relative-index allocation law proved
- [x] dormant residue directions converted into nearby quantized index birth
- [x] fixed-aperture Kato prime-to-characteristic response constructed
- [x] generic separating locus and determinantal incidence seam isolated
- [x] prime-log crowding converted into an exact ground-oscillation requirement
- [x] orbit-sensitive source--divisor marking isolated as a third carrier coordinate
- [x] signed Möbius synthesis identified as an exact Euler-side Schur contraction
- [x] complete coupled causal transfer function and continuation-pole seam identified
- [x] centered weighted-Mertens boundary vector proved to have a strong critical limit
- [x] complete coupled causal source proved to converge strongly at the Euler boundary
- [x] universal bounded gauge-covariant continuation excluded
- [x] inverse-horizontal residue charge forced into every orbit-sensitive graph norm
- [x] residue charge realized as the initial slope of a positive Hankel gap trace
- [x] four-unit bound restated as semilocal trace-slope conservation
- [x] canonical Xi-pointed closed two-channel graph constructed from the exact logarithmic source
- [x] anti-causal logarithmic-source Hankel operator proved closable on a dense adjoint core
- [x] rational orbit gauges realized as bounded graph automorphisms with rank-one residue channels
- [x] rational orbit gauges realized as bounded finite-rank perturbations of the closed operator
- [x] transverse integer index coupled to the trace slope by `E>4*kappa`
- [x] incoming Euler pole identified as the exact saturated unit `(kappa,E)=(1,4)`
- [x] full trace-class demand reduced to a positive three-block boundary relative trace
- [x] exact `min(t,u)` kernel and pole density `4` proved
- [ ] construct a positive reference splitting `(10)`
- [ ] prove the infinite-carrier contraction `(11)`
- [ ] or construct a source-defined Gram factorization of `(12c)` and an index-faithful aperture
      transport
- [ ] or construct a positive relative-background kernel and prove `(12l)`
- [ ] prove a cofinal lower bound for the true ground-state separating margin
- [ ] transport complete orbit-sensitive Euler-Pick inertia into the screw spaces
- [ ] prove its distinguished pole-to-divisor renormalization is nonexpansive in the charged graph
- [ ] construct the three boundary-block traces `(12z24)` directly from the Xi source graph
- [ ] prove the relative-trace density bound `(12z27)`
- [ ] prove absence of negative spectral birth `(5a)`
- [ ] invoke the cofinal floor criterion to prove RH
