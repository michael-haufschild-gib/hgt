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

The corrected finite-aperture Fourier formula for the restricted Weil form is

```text
QW_a(v,v)=1/(2*pi) integral_R w_a(t)|hat(v)(t)|^2dt,             (6)

w_a(t)=Re psi(1/4+i*t/2)-log pi
 -2 sum_(n<=exp(2a))Lambda(n)/sqrt(n)*cos(t*log n)
 +P_a(t),

P_a(t)
 =[2sinh(a)cos(2a*t)+4t*cosh(a)sin(2a*t)]/(t^2+1/4).            (7)
```

Here `P_a` is the Fourier transform of
`2cosh(x/2)1_(-2a,2a)(x)`, the aperture-truncated polar factor. The distributional formulas
contain `-r''`; this corrects the opposite printed sign in Suzuki's equation (2.7). The proof and
the exact critical Mellin defect are in `ccm-polar-prime-critical-mellin-defect-law.md`.

The function `v` is supported in `[-a,a]`; hence `hat(v)` belongs to the Paley--Wiener space `PW_a`.
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

### A. Paley--Wiener lower-frame theorem

`[PROVED BRIDGE]` The exact positive reference splitting is now constructed, with a different
orientation from the earlier tentative `d_a-k_a` decomposition. The digamma increment is a
countable sum of positive resolvent squares, each prime cosine is a positive translation-difference
square minus its scalar mass, and the polar block has one positive even and one negative odd
channel. On the even sector this gives

```text
T_a^+=B_a^*B_a-mu_a I,                                        (10)

mu_a=2sum_(n<=exp(2a))Lambda(n)n^(-1/2)-m(0),                  (10a)
```

where `B_a` jointly carries every Gamma resolvent channel, every visible prime-shift difference,
and the distinguished even polar boundary moment. The exact construction is proved in
`ccm-polar-euler-frame-minus-level-law.md`.

The remaining theorem is the sharp lower-frame bound

```text
||B_a v||^2>=mu_a||v||^2
for every even aperture vector v.                              (11)
```

This is exactly positivity of the true restricted Weil form, hence the RH core; the splitting does
not prove `(11)`. Its gain is structural: no prime direction, Gamma channel, or polar boundary mode
is hidden in an indefinite scalar symbol.

The leading frame gap cannot prove `(11)`. For every fixed nonzero
`f in C_c^infinity(0,L)`, the even two-edge vector

```text
v_a(x)=f(a-|x|)
```

satisfies

```text
||B_a v_a||^2/[mu_a||v_a||^2]->1.                              (11a)
```

The prime number theorem makes the rescaled prime cross-boundary measure converge to
`exp(-r/2)dr`; its leading rank-one form cancels the positive polar moment exactly. This holds on
an infinite-dimensional profile space, not only for a prolate seed. The theorem is proved in
`ccm-universal-boundary-laplace-frame-saturation-law.md`.

Therefore a source-defined left inverse for `B_a` must be asymptotically extremal on the entire
boundary-profile space and control the subleading signed measure `dR`. The existing Möbius Schur
contraction cannot supply that inverse by bounded causal functional calculus: it is unchanged by
symmetric orbit insertion and acquires the missing divisor information only through the
noncommuting meromorphic contour seam. The live positive mechanism is a divisor-sensitive
left-inverse/factorization whose sharp norm is measured after that seam.

The same two-edge family is an effective noncompact detector. For any fixed off-line quartet
`w=delta+iT`, its contribution along a generic fixed profile has leading term

```text
4exp(2a delta) Re(exp(2iaT)A_f(w)^2),                           (11b)
```

while an all-line reference divisor contributes a uniformly bounded amount. A cofinal phase
sequence makes `(11b)` tend to `-infinity`. The result extends to a finite horizontally isolated
rightmost layer and is proved in `two-edge-boundary-quartet-amplification-law.md`.

This does not yet globalize to the zeta divisor. An off-line divisor need not have an attained or
horizontally isolated maximal displacement. The corresponding positive detector theorem is a full
indicator/spectral-synthesis statement: without selecting a rightmost zero, an off-line completed
divisor must force negative liminf on some cofinal two-edge boundary family. Single-zero dominance
cannot be used.

The nonattained-layer problem nevertheless has an exact scalar carrier. For the cumulative defect
`R` in `ccm-polar-prime-critical-mellin-defect-law.md`, put

```text
omega_R=limsup_(h->infinity) log(1+|R(h)|)/h.                   (11c)
```

Its Laplace transform is the rational-plus-Euler logarithmic derivative. Holomorphic continuation
therefore proves

```text
Re rho<=1/2+omega_R for every nontrivial zero rho,
RH iff omega_R=0.                                             (11d)
```

Under RH the classical von Koch error gives the stronger polynomial bound `R(h)=O(h^3)`.
Conversely, any subexponential bound on `R` excludes all transverse poles at once, without a
rightmost-zero hypothesis. The proof is in `ccm-critical-mellin-defect-abscissa-rh-law.md`.

Thus a boundary proof can globalize either by establishing negative liminf of the full two-edge
divisor sum under RH failure, or positively by proving zero exponential type of `R`. The latter is
the sharper source-side target, but it is already an exact RH criterion; prime-number-theorem
control stops at `omega_R<=1/2`.

The causal Möbius coordinate reaches the same boundary and no farther for free. If

```text
m_0(t)=sum_(n<=e^t)mu(n)/n,
```

then the proved strong limit gives only `m_0 in L2`. Moving its Hardy transform from `s=1` toward
the critical line requires

```text
exp(alpha*t)m_0(t) in L2 for every alpha<1/2.                  (11e)
```

One weight `alpha` excludes zeros from `Re s>1-alpha`, and the full half-unit tower `(11e)` is
equivalent to RH. This is proved in `mobius-half-unit-exponential-moment-rh-law.md`. Hence the
unweighted Möbius Schur contraction cannot yield `omega_R=0` by a bounded left translation. The
positive source theorem must construct a cutoff-dependent synthesis on the nested weighted domains
`D_alpha`, retaining the meromorphic residue graph as `alpha` approaches `1/2`.

At positive source shift `omega`, the absolutely convergent Euler formula supplies only the safe
weighted range `alpha<2omega`. Reaching the critical line from `s=1+2omega` requires
`alpha<1/2+2omega`. The missing continuation width is therefore exactly `1/2` at every stage. The
safe range collapses to zero as `omega->0`; it does not approach the required half-unit tower.

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

The causal and Euler-Pick coordinates are now identified exactly, so no unknown comparison map
remains between them. Put

```text
Phi_omega(z)=xi(1+z)/xi(1+2omega+z),

A_omega(z)=pi^(-omega)
 Gamma((1+2omega+z)/2)/Gamma((1+z)/2)
 *(1+2omega+z)(2omega+z)/((1+z)z(1+omega+z)).           (12z5a)
```

Then `(12z)` is precisely

```text
L F_omega(z)+1/((1+omega)z zeta(1+2omega))
 =A_omega(z)Phi_omega(z).                                (12z5b)
```

Under the affine map `j_omega(z)=i(1/2+omega+z)`, one has

```text
Phi_omega(z)=Theta_omega(j_omega(z)),                    (12z5c)

K_omega(z,v)
 =(1-Phi_omega(z)conjugate(Phi_omega(v)))
  /(1+2omega+z+conjugate(v)).                            (12z5d)
```

The negative index of `(12z5d)` is exactly the number of zeros with
`Re rho>1/2+omega`. Thus the signed causal vector already contains the complete shifted-Xi
quotient after an explicit archimedean-polar scalar conjugacy. The missing upgrade is now exact:
scalar Schur contractivity and one-vector Hardy control must become complete positivity of every
finite matrix `(K_omega(z_j,z_k))`, cofinally as `omega` decreases to zero. At `omega=0`,
`Phi_0=1` and `K_0=0`; retaining only the strong endpoint loses the entire transverse filtration.
The proof and scope are recorded in `ccm-causal-pick-affine-conjugacy-law.md`.

This also fixes the role of the two new HT constraint-dimension theorems. For fixed `omega`,
`(12z5b)` is an invertible scalar meromorphic coordinate change, not a proved nonpure
Stanley--Reisner realization. Scalar principalization therefore forbids attributing the missing
incidence to a hidden one-clock nonpure prime matroid. The actual positive carrier is the cofinal
`omega`-filtration, the complete Pick-section family, and its residue-index jumps; a periodic-pencil
interpretation would require an additional proof of an exact relation complex.

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

For a Hankel kernel the same quantity is simply

```text
Delta_ell(u)=||Q_uH_ell||_(S_2)^2,                      (12z24a)
```

because the output strip `0<=x<u` has line-section length `min(t,u)` on `x+y=t`.

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

Moreover the local corner is `o(a)`:

```text
1/(2a)||Q_aH_ell Q_a||_(S_2)^2 ->0,

lim_(a->0+)1/(2a)||[P_a,H_ell]||_(S_2)^2=||ell||_2^2.   (12z25c)
```

Hence all first-order transverse charge is interface flux. The shrinking local Gamma corner does
not contribute to the limiting density.

The construction is now unconditional on the Xi source. For the closed anti-causal operator
`D_Xi`, define

```text
Delta_Xi(u)=||Q_uD_Xi||_(S_2,ext)^2,                    (12z25b)
```

where the value is the norm of its unique Hilbert--Schmidt extension, if one exists, and
`+infinity` otherwise. The dense source domain makes this extended value canonical. Thus no
separate trace-construction theorem remains: proving `(12z27)` simultaneously proves finiteness
and the correct bound.

Thus the residue energy is a boundary relative-trace density even when the full Hankel operator is
not Hilbert--Schmidt. For the incoming pole,

```text
Delta_pole(u)=4(1-e^(-u)).                              (12z26)
```

The exact positive CCM target is therefore

```text
limsup_(u->0+) Delta_Xi(u)/Delta_pole(u)<=1.             (12z27)
```

Equivalently,

```text
limsup_(a->0+)1/(2a)||[P_a,D_Xi]||_(S_2,ext)^2<=4.       (12z28)
```

By `(12z21)`, `(12z27)` forces `kappa_off=0` and RH. This is smaller than a global trace-class
theorem and matches the relative-compression form of the semilocal Connes trace formula. What must
be constructed from the exact source are the three boundary-block traces and their first-order
density, not an absolute trace of the whole continuation operator.

### L. Cofinal weak boundary-strip transfer

The carrier synthesis in `docs/prompts/notes.md` now has an exact operator transfer theorem. Let
`C_Xi` be a graph core of `D_Xi`. It is enough to construct finite-stage completed Euler--Gamma
operators

```text
A_(N,u) in S_2
```

such that, for every `f in C_Xi`,

```text
A_(N,u)f -> Q_uD_Xi f weakly,                           (12z29)
```

and, uniformly in the cofinal limit,

```text
limsup_(N->infinity)||A_(N,u)||_(S_2)^2
 <=4(1-e^(-u))+r(u),       r(u)=o(u).                   (12z30)
```

Indeed, a subsequence attaining the lower Hilbert--Schmidt norm limit has a weak `S_2` limit.
Evaluation on `f` is weakly continuous, so `(12z29)` identifies that limit with `Q_uD_Xi` on the
core. Graph-core approximation extends the identity to `D(D_Xi)`, and weak lower semicontinuity
gives

```text
Delta_Xi(u)
 <=liminf_(N->infinity)||A_(N,u)||_(S_2)^2
 <=4(1-e^(-u))+r(u).                                   (12z31)
```

Thus `(12z27)` and RH follow. Full operator convergence, determinant convergence, and full trace
class are unnecessary on this branch. The finite construction is nevertheless forced to carry
three positive data simultaneously:

```text
cofinal Euler source on the Xi graph core
  + rational-gauge-sensitive source--divisor pointing
  + uniform one-sided boundary-strip budget
  -> four-unit Xi density
  -> RH.                                                (12z32)
```

This is the singular-completion alternative allowed by the divisor-winding law in the notes: the
charge is transported by the source-defined graph limit and its boundary strip, not manufactured
by an unmarked compact limit. The complete bridge proof is in
`ccm-boundary-strip-weak-compactness-transfer-law.md`.

### M. Translation-covariant transfer has insufficient multiplicity capacity

The simplest possible pole-to-divisor contraction is now excluded exactly. If a bounded operator
`T` on `L2(0,infinity)` commutes with every unilateral right shift and

```text
T ell_pole=ell_D,
ell_D(t)=2 sum_j m_j e^(-(a_j+i gamma_j)t),             (12z33)
```

then Laplace--Hardy commutant theory forces the unique multiplier

```text
phi_D(z)=(z+1/2)sum_j m_j/(z+a_j+i gamma_j).            (12z34)
```

Its high-frequency feedthrough is

```text
lim_(x->infinity)phi_D(x)=kappa(D)=sum_jm_j,
```

and therefore

```text
||T||=||phi_D||_infinity>=kappa(D).                     (12z35)
```

Every nonempty conjugation-closed right-half zeta packet has `kappa(D)>=2`, since nontrivial strip
zeros are nonreal and Schwarz conjugation preserves the right half. Hence no scalar norm-one
shift-covariant operator can transport the incoming pole to an off-line FE--Schwarz packet.

This does not close the CCM route. It proves positively that the transverse multiplicity must be
carried by what global scale covariance omits:

```text
cutoff-dependent noncommutation
  + additional channel arity
  + or a singular pointed graph relation.               (12z36)
```

The current construction uses the pointed graph and the aperture projections. Accordingly the
boundary commutator in `(12z28)` is not an optional reformulation: it is the only surviving scalar
place where the missing multiplicity capacity can reside. The bridge proof is in
`ccm-shift-covariant-pole-divisor-capacity-law.md`.

### N. The real-spectrum boundary-strip shortcut collapses to RH

Let `F_(lambda,N)` be a dephased CCM finite spectral factor under the simple-even hypothesis. It is
even, Cartwright, and real-rooted. Its logarithmic derivative is analytic of Smirnov class in the
upper half-plane. Hence, on the maximal Hardy multiplication domain,

```text
P_-M_(-2F'_(lambda,N)/F_(lambda,N))=0.                  (12z37)
```

The Smirnov maximum principle proves `(12z37)`: whenever the product has an `L2` boundary value,
it belongs to `H2_+`, including the domain cancellations at real spectral poles.

For Xi, the corresponding closed anti-causal operator satisfies

```text
D_Xi=0  iff  RH.                                        (12z38)
```

The forward implication follows because every right-half zero supplies a nonzero rank-one upper
pole coordinate; the reverse implication is `(12z37)` applied to the all-real centered divisor.
Therefore any graph-core convergence

```text
0=Q_uD_(lambda_j,N_j) -> Q_uD_Xi                       (12z39)
```

already proves RH. The weak boundary-strip transfer is not an easier last mile for the real finite
CCM determinants. It is useful only for a finite-stage family that carries genuine transverse
charge, in which case its four-unit budget is the horizontal-control theorem.

The finite-prime theta-cusp screen supplies a source-pure, pointed family converging locally
uniformly and zero-preservingly to Xi, but its positive kernels need not have real-zero Fourier
transforms. Applying `(12z30)` to their logarithmic graphs would therefore restate the remaining
zero-fibre control rather than prove it.

The periodic-pencil intrinsic-dimension and scalar-principalization theorems do not alter this
verdict, but together they classify the only two legitimate uses of relation geometry here. Their
lower bound counts analytic variables in an exact nonpure Stanley--Reisner HT realization; the two
Hardy polarizations in `(12z17)` are not such a `C^2` realization. Moreover componentwise channel
multiplicity, constant finite internal monodromy, and every DA-gauge-flat finite cocycle still force
the one-variable structural ideal to be pure and principal. Therefore a periodic-pencil CCM branch
first needs a proved nonpure source--divisor relation complex and its exact annihilator, and then
must positively expose a second analytic variable, a non-DA-flat cocycle, an infinite-dimensional
internal action with new differential transcendence, or a non-additive action. At present that is a
labelled conjectural design, not an input.

Thus the independent boundary-strip shortcut is closed. The live CCM endpoints return to the two
primary cofinal certificates:

```text
true restricted-Weil floor ->0,
or normalized finite-Weil determinants ->Xi divisor-faithfully.          (12z40)
```

### O. Direct screw-kernel null equation

The shortest surviving CCM branch is now the exact aperture charge. If `u in L2_0(-a,a)` is
extended by zero and lies in `ker G_a`, then differentiating the screw convolution twice gives

```text
(K_infinity*u)(x)
 =sum_(2<=n<e^(2a)) Lambda(n)n^(-1/2)
    (u(x-log n)+u(x+log n)),       |x|<a.                (12z41)
```

Here `K_infinity` is the completed pole--Gamma distribution; away from zero its regular kernel is

```text
e^(|t|/2)-e^(-5|t|/2)/(1-e^(-2|t|)).                    (12z42)
```

The cutoff `n<e^(2a)` is forced exactly by support overlap. Equation `(12z41)` is one static
compatibility constraint among the logarithmic archimedean pseudodifferential channel, the finite
faithful prime-shift module, and the hard aperture boundary. It contains no auxiliary determinant
and no chosen finite-prime approximation.

The differentiated equation must retain two anchors, such as

```text
(G_a u)(0)=0,       (G_a u)(a/2)=0.                     (12z41a)
```

Indeed `(12z41)` only says that `G_au` is affine on the aperture; `(12z41a)` kills the two affine
modes and restores exact equivalence with `u in ker G_a`.

Global Fourier division is invalid because `(12z41)` holds only inside the aperture. The live
mechanisms are therefore source-specific unique continuation: logarithmic-elliptic
quasi-analyticity, boundary-shell prime peeling, or a Wiener--Hopf factorization whose partial
indices are fixed by the Euler--Gamma source. The exact conjecture and its kill conditions are in
`ccm-prime-shift-screw-null-unique-continuation.md`.

The two HT constraint-dimension theorems supply a sharp route bifurcation, not an automatic fourth
mechanism. If the boundary-shell relations are first proved to have an exact nonpure
Stanley--Reisner annihilator, then at least two genuine analytic directions are forced; ordinary
Hardy-channel doubling and DA-flat finite internal state cannot supply them. If the construction
stays one-clock, additive, and DA-flat, its exact full-matroid relation geometry is instead forced
into the pure principal stratum. In that branch the missing RH information must be carried by the
pointed source--divisor incidence, the aperture seam, and the two-sided boundary compatibility,
not by nonpure prime combinatorics. Equation `(12z41)` currently supplies one scalar
pseudodifferential compatibility relation, not a proved full Stanley--Reisner matroid, so no
nonpure relation-complex identification is available.

One scalar regularity shortcut is closed. Iterating the order-`log|D|` archimedean ellipticity
reaches only the intersection of logarithmic Sobolev domains, which still contains every compactly
supported smooth function and is not quasi-analytic.

The earlier crossing argument used an incomplete full-line symbol and is retracted. The
untruncated polar kernel `2cosh(t/2)` is not tempered; on the aperture it contributes exactly the
multiplier `P_a` in `(7)`. Thus the correct characteristic symbol is

```text
W_a(xi)=Re psi(1/4+i*xi/2)-log pi
 -2sum_(n<=e^(2a))Lambda(n)n^(-1/2)cos(xi log n)
 +P_a(xi).                                                (12z43)
```

At zero, `P_a(0)=8sinh(a)` cancels the prime-number-theorem main term. Writing
`X=e^(2a)` and `E(X)=sum_(n<=X)Lambda(n)-X` gives the exact residue

```text
W_a(0)=m(0)+2-4/sqrt(X)
 -2E(X)/sqrt(X)-integral_1^X E(t)t^(-3/2)dt.             (12z43a)
```

The sign is therefore a critical Mellin defect, not a consequence of the leading prime mass. The
corrected symbol tends to `+infinity` as `|xi|->infinity`, so its real zero set is finite but may be
empty. The surviving object is either a zero-free finite-interval factorization retaining the
rank-two polar block or a singular factorization retaining every crossing and proving a
nonvanishing boundary Evans relation.

At fixed `a` the possibly empty real crossing set is finite. After factoring its multiplicity polynomial `p_a`
from `(12z43)` by a bounded rational factor, the remaining multiplier `c_a` is real-zero-free and
invertible. Every interior null solution therefore transforms to

```text
v=c_a(D)u,       p_a(D)v=0,                             (12z44)
```

so `v` is a finite exponential polynomial generated exactly by the real characteristic crossings;
in the zero-free branch its interior trace is zero. The inverse multiplier is nonlocal, so the
exterior trace of `v` remains part of the data. The remaining CCM theorem is a two-sided boundary
factorization/Evans relation with no nonzero compatible pair, retaining the rank-two polar block,
any finite packet, exterior trace, support, mean-zero condition, and anchors `(12z41a)`. The reduction is proved in
`ccm-characteristic-crossing-interior-mode-reduction-law.md`.

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
- [x] relative trace reduced to one output-boundary Hilbert--Schmidt norm
- [x] extended relative trace constructed canonically from the closed Xi source operator
- [x] exact `min(t,u)` kernel and pole density `4` proved
- [x] first-order density localized entirely in the cutoff commutator
- [x] weak Hilbert--Schmidt graph-core transfer of every finite-stage four-unit budget proved
- [x] arithmetic source, pointed incidence, and boundary metric assembled into one positive carrier
- [x] scalar shift-covariant pole-to-divisor contractions excluded by exact multiplicity capacity
- [x] cutoff noncommutation or extra channel arity forced as the surviving positive carrier
- [x] real-spectrum finite logarithmic graphs proved transverse-zero
- [x] graph-core convergence from CCM real spectra proved RH-equivalent
- [x] periodic-pencil analytic dimension separated from Hardy polarization count
- [x] one-clock principal branch separated from nonpure curved/infinite-dimensional branch
- [x] finite-stage boundary-strip shortcut retired as an independent CCM completion
- [x] exact finite-aperture prime-shift screw null equation isolated
- [x] affine loss under differentiation repaired by two exact anchors
- [x] logarithmic-elliptic quasi-analytic shortcut excluded
- [x] exact rank-two polar multiplier restored to the finite-aperture symbol
- [x] polar--prime main-term cancellation reduced to the critical Mellin defect
- [x] false coarse crossing argument retracted
- [x] interior null equation reduced to a finite characteristic-mode packet
- [ ] decide the corrected symbol's zero-free versus crossing branch
- [ ] prove or refute source-specific unique continuation for `(12z41)`
- [x] construct the exact positive frame-minus-level splitting `(10)`
- [x] prove universal infinite-dimensional boundary-frame saturation `(11a)`
- [x] prove two-edge amplification of every fixed off-line quartet `(11b)`
- [x] encode all nonattained transverse layers by the defect abscissa `(11c)`
- [x] classify causal Möbius transport as a cofinal half-unit weighted-domain tower `(11e)`
- [x] identify the causal Möbius quotient with the Euler-region shifted-Xi Pick carrier `(12z5)`
- [ ] prove the zero-type recession `omega_R=0`
- [ ] prove the infinite-carrier lower-frame bound `(11)`
- [ ] or construct a source-defined Gram factorization of `(12c)` and an index-faithful aperture
      transport
- [ ] or construct a positive relative-background kernel and prove `(12l)`
- [ ] prove a cofinal lower bound for the true ground-state separating margin
- [ ] transport complete orbit-sensitive Euler-Pick inertia into the screw spaces
- [ ] prove its distinguished pole-to-divisor renormalization is nonexpansive in the charged graph
- [ ] prove the relative-trace density bound `(12z27)`
- [ ] prove absence of negative spectral birth `(5a)`
- [ ] invoke the cofinal floor criterion to prove RH
