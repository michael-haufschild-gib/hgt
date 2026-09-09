# SQB positive occurrence: theta dilation loop

Status: analytical construction and norm comparison in progress. The literal
theta dilation profile and its two correlation transforms are proved in Lean
in `SelbergThetaDilationTransform`. Every actual theta zero mode has a globally
positive real normalization and a canonical differentiable logarithm, proved
in `SelbergThetaSourcePhase`. Its positive variance is proved in
`SelbergThetaSourceVariance`; quantitative energy bounds and a strict
pointwise disk bound are proved in `SelbergThetaSourceEnergy`.
Full modular Gram transport and normalized
full-Xi occurrence remain unproved. Frontier map is read-only; no numerical
computations.

Chain: original theta/Xi source -> native approximate vectors at the
quarter-shifted energy -> actual entire-operator approximate vectors at the
unchanged full Xi target -> real-preimage classification -> critical line -> RH.
The hardest obstacle is the normalized source residual. The current attack
keeps its complete arithmetic Gram form, including cross terms.

The workflow is conjecture -> analytical proof attempt -> retain a successful
construction or pivot immediately. Failed estimates here are not projects to
formalize as new exclusion theorems. The centered exponential-source exclusion
has been deferred under the user's instruction.

## 1. Arithmetic mean from the original theta source

Write Phi = `thetaCuspFullSource`, and X(s) = `xiCent (s-1/2)`.
The inspected corpus proves Phi is smooth, even and strictly positive, with
all derivative exponential envelopes, and

    integral_R Phi(x) exp((s-1/2)x) dx = X(s).

For y>0 define

    h_rho(y) = (y/2) exp((rho-1/2) log(y)/2) Phi(log(y)/2),
    h_rho,a(y) = a^(-1) h_rho(a y),       a>0,
    P_rho,a(z) = sum_[primitive rows modulo sign] h_rho,a(Im(M z)).

**Conjecture:** this is a genuine admitted modular source with mean X(rho),
so its mean vanishes arithmetically at every actual Xi zero.

**Analytical proof:** y=exp(2x), with its full Jacobian, gives for every complex w

    integral_0^infinity h_rho,a(y) y^(w-2) dy
      = a^(-w) X(rho+2w).                                      (1)

Every integral is absolute: the inspected all-rate theta envelopes dominate
both positive and negative x. In particular, the original height profile and
each Euler derivative have arbitrarily high power decay at both ends.

Absolute row convergence follows by bounding the profile by C t^2 and using
the actual positive quadratic row sum. On the native cell at height y>=1/2,
the nonparabolic row heights t are <=1/y and their total squared height is
bounded by the already proved `nonparabolic_quadratic_bound`. For any N,
the bound |h(t)|<=C t^(N+2) makes their total contribution <=CB y^(-N).
The parabolic row has the same arbitrarily high decay. The argument applies
to Euler derivatives as well. Local normal convergence follows from the
same row majorants: on compact subsets each derivative of a transformed
height is bounded by a constant times that height.

Thus P is smooth, modular, and rapidly decaying in the original cusp,
including its scaled derivative fields. It is in native L2. Absolute
unfolding of its norm justifies full modular strip unfolding; (1) at w=0
then gives

    integral_fd P_rho,a = X(rho).                              (2)

This proves the proposed arithmetic mean identity on paper. It supplies
no normalized residual estimate.

Inspected ingredients: `ThetaCuspTiltFluxSourceWeld`,
`ThetaCuspTiltedSchwartz`, `ThetaCuspSchwartz`,
`SelbergResummedSource`, `ThetaCuspHawkingBMCuspNonparabolicHeight`,
`ThetaCuspHawkingBMCuspWindowAbsoluteRegrouping`, and
`HTGeometry.ModularStripUnfolding`.

## 2. A nonzero source without assuming a norm lower bound

Let E_2 be the original completed field `scalar (3/2)`, whose full
horizontal mean is Lambda(4)y^2+Lambda(3)y^(-1).

**Conjecture:** an explicit dyadic combination gives a nonzero source at
every Xi copy, while retaining (2).

**Analytical proof:** absolute unfolding against E_2 is valid because P and
its absolute row majorant decay faster than every power in the cusp.
Using both Weyl terms, (1) gives

    integral_fd P_rho,a E_2
      = a^(-2) Lambda(4) X(rho+4)
        + a Lambda(3) X(rho-2).                              (3)

Define

    S_rho,a = 2 P_rho,a - P_rho,2a,
    A_rho = Lambda(4) X(rho+4).

Then

    integral_fd S_rho,a = X(rho),
    integral_fd S_rho,a E_2 = (7/4) a^(-2) A_rho != 0.       (4)

The second Weyl term cancels exactly. A_rho is nonzero because
Re(rho+4)>4 and the completed function is nonzero in that Euler half-plane;
Lambda(4) is nonzero as well. Thus every S_rho,a is a nonzero native
mean-zero source at an actual Xi zero. No constant projection is inserted.
Equation (4) proves nonvanishing, not a uniform Hilbert norm bound:
E_2 itself is not an L2 test.

The normalization of E_2 was checked against
`ThetaCuspHawkingBMCuspPositiveMean.positiveCuspRows_completed_mean` and
`cuspScalar_unit_interval_mean`. The safe half-plane nonvanishing is
`xiCent_ne_zero_of_half_lt_re`, used in the inspected `XiEulerSafeCauchyLoss`.

## 3. Moving native-domain vectors and their exact boundary error

Put L=log a and Q(L)=exp(L/2) S_rho,exp(L). Define

    kappa = (rho-1/2)/2,
    e = 5/4-kappa^2.

For the actual native energy operator A=1-Delta_H,

    A Q(L) = (5/4) Q(L) - Q''(L).                           (5)

**Analytical proof:** on the seed, D_y=y d/dy and
`partial_L h_rho,exp(L)=(D_y-1)h_rho,exp(L)`.
The native height expression is `1-D_y(D_y-1)`.
Conjugating by exp(L/2) gives (5). Absolute differentiated row convergence
commutes this expression with full periodization. The rapid cusp estimates
above admit the value and Laplacian in native L2. The existing compact
modular cutoffs then converge in the native graph, retaining both product
rule terms, just as in the inspected `SelbergScatteringSourceGraph`.
Uniform bounds on compact L intervals also give strong twice differentiability.

The exponent sigma=1/2+kappa=rho/2+1/4 satisfies
e=1+sigma(1-sigma). The already proved quarter-shift identity gives
F(e-1)=F((rho/2)(1-rho/2)), exactly the full Xi target.

For a smooth window chi with adequate decay, set

    V_chi = integral_R chi(L) exp(kappa L) Q(L) dL.

Two integrations by parts, retaining the whole original Q, give

    (A-e)V_chi
      = -integral_R exp(kappa L)
          (chi''(L)+2 kappa chi'(L)) Q(L) dL.                (6)

Gaussian chi_R(L)=exp(-L^2/(2R^2)), R>0, makes every integral and boundary
limit absolute. Crude row bounds give at most exponential growth in |L|
for Q and its first two native graph derivatives, which Gaussian decay
dominates. These are actual native-domain vectors on paper.
Equation (4) gives the explicit nonzero test pairing

    integral_fd V_chi_R E_2
      = (7/4) A_rho sqrt(2 pi) R
          exp((kappa-3/2)^2 R^2/2) != 0.                   (7)

The complex Gaussian integral follows from the real Gaussian Fourier
transform and its entire Laplace continuation. Absolute Fubini against E_2
uses (3) applied to the absolute seed majorant, so (7) is legitimate even
though E_2 is not in L2.

For the actual entire covariance C and target mu, C V_chi_R is nonzero and
in the actual entire domain. Its unit normalization has residual exactly

    ||V_chi_R-(2+mu) C V_chi_R|| / ||C V_chi_R||.             (8)

**Occurrence conjecture attempted:** the normalized error tends to zero.
The attempted shortcut from `chi_R'=O(1/R)` and `chi_R''=O(1/R^2)` fails:
these uniform unweighted bounds neither control the exponentially weighted
integrals in (6) nor bound the denominator in (8). No vanishing residual
has been proved. Do not formalize this shortcut or repackage it as an input.
Pivot to the exact original-source Gram form below.

## 4. The full arithmetic norm, derived before estimating it

Set f(y)=2h_rho(y)-(1/2)h_rho(2y), and

    g(t)=exp(-t/2) f(exp t).

Then Q(L) is the original periodization of
`y^(1/2) g(log y+L)`. Define

    K(u) = integral_R conj(g(t)) g(t+u) dt,
    J(v) = integral_R conj(g(t)) g(v-t) dt,
    H(v) = sum_(c>=1) phi(c)/c * integral_R
             J(v-2 log c-log(1+x^2)) / sqrt(1+x^2) dx,

where phi(c) is the ordinary Euler totient, with phi(1)=1.

**Analytically derived exact Gram identity:**

    inner(Q(L),Q(M)) = K(M-L) + H(L+M).                     (9)

Proof: unfold one original row sum against the other. Its parabolic row
gives K. In the nonparabolic rows, write the primitive bottom row as
(c,d), c>0, and write d=r+kc over reduced residues r modulo c. The unit
horizontal integral unfolds to phi(c) copies of the real line. Rescale
the horizontal coordinate by the original height y. The transformed
height is `1/(c^2 y (1+x^2))`. Finally put t=log y. The half-density
Jacobians leave exactly `phi(c)/(c sqrt(1+x^2))`; translating t by L
gives the argument L+M of J. Every rearrangement is absolute, as follows
by performing the same unfolding with absolute seeds and the rapid cusp
majorants used above. This retains all primitive rows and all spatial modes.
The inspected `ThetaCuspHawkingBMEisensteinPoincareRamanujanUnfolding`
contains the corresponding reduced-residue unfolding for power seeds;
(9) for this theta source is not yet a Lean theorem.

Consequently the exact squared norm of `integral w(L)Q(L)dL` is

    G(w) = integral_R integral_R conj(w(L)) w(M)
             [K(M-L)+H(L+M)] dL dM.                        (10)

Its squared native residual at e is G(w''-kappa^2 w).
For w=chi exp(kappa L) this is exactly (6), without replacing signed
cross terms by an absolute majorant.

**Positive occurrence target:** seek explicit source-derived windows
w_R for which

    0 < G(w_R),
    G(w_R''-kappa^2 w_R) / G(w_R) -> 0.                    (11)

The paired candidate is a window
`chi_R(L)(exp(kappa L)+eta_R exp(-kappa L))`.
Its exact error is

    chi_R''(exp(kappa L)+eta_R exp(-kappa L))
      +2 kappa chi_R'(exp(kappa L)-eta_R exp(-kappa L)).

Its coefficient must be determined from the actual two-by-two forms in
(10). Its opposite-phase cross terms retain H at the same stage of the
calculation. The leading real-frequency cancellation below does not give
(11); this Gaussian candidate has not supplied occurrence. A source
construction or an unnormalized small error does not discharge the target.

For the paired Gaussian candidate this test has an exact two-by-two form,
with no numerical matrix evaluation. Write a=Re(kappa), b=Im(kappa), and

    K_R(z)=integral exp(-u^2/(4R^2)+zu) K(u) du,
    H_R(z)=integral exp(-v^2/(4R^2)+zv) H(v) dv.

For w_+(L)=chi_R(L)exp(kappa L) and
w_-(L)=chi_R(L)exp(-kappa L), the native Gram matrix M_R is

    M_++ = sqrt(pi) R [exp(a^2 R^2) K_R(ib)
                       +exp(-b^2 R^2) H_R(a)],
    M_-- = sqrt(pi) R [exp(a^2 R^2) K_R(-ib)
                       +exp(-b^2 R^2) H_R(-a)],
    M_+- = sqrt(pi) R [exp(-b^2 R^2) K_R(-a)
                       +exp(a^2 R^2) H_R(-ib)],
    M_-+ = conj(M_+-).                                    (12)

These formulas follow by u=M-L, v=M+L, whose Jacobian is 1/2,
and one elementary Gaussian integral. In particular the reflected
arithmetic term in M_+- carries exp(a^2 R^2), not the exp(-b^2 R^2)
factor appearing in the diagonal entries. Dropping it before choosing
the paired coefficient would change the norm being tested.

For an equally explicit residual matrix, let

    F_R(r,s)=integral integral chi_R(L)chi_R(M)
               exp(rL+sM)[K(M-L)+H(L+M)] dL dM,
    D_r=R^(-4) partial_r^2-R^(-2)-2r R^(-2) partial_r.

Then, for epsilon,delta in {+1,-1},

    (N_R)_(epsilon,delta)
      = (D_r D_s F_R)(epsilon conj(kappa),delta kappa).     (13)

All parameter differentiations are absolute by the Gaussian majorant.
The actual test is
`(1,eta_R)^* N_R (1,eta_R) / ((1,eta_R)^* M_R (1,eta_R))`.
The two matrices are norms of the original vectors and their actual
native residuals. The needed comparison concerns their relative size
for this literal theta/totient source.

## 5. Exact arithmetic factors of both source correlations

Use the angular-frequency convention

    hat f(z) = integral exp(-i z t) f(t) dt.

Writing c=exp(-log(2)/2), the actual profile from (9) is

    g_0(t) = (1/2) Phi(t/2) exp((rho+1/2)t/2),
    g(t) = 2 g_0(t) - c g_0(t+log(2)),
    d(z) = 2 - c exp(i z log(2)).

The all-plane identities are

    hat g(z) = d(z) xiCent(rho+1/2-2iz),
    hat K(z) = conj(hat g(conj z)) hat g(z),
    hat J(z) = conj(hat g(-conj z)) hat g(z).                (14)

**Proved in Lean:** every complex exponential twist of g, K and J is
integrable. Scaling and translating the actual theta integral proves
the first identity; the Bochner convolution theorem proves both product
identities with their integrability obligations discharged.

At every actual Xi copy rho=beta+i gamma, with b=gamma/2,

    hat g(-i/2) = xi(rho) = 0,
    hat K(-i/2) = hat J(-i/2) = 0,
    hat g(b) = d(b) xi(beta+1) != 0,
    Re(hat K(b)) = |hat g(b)|^2 > 0.                        (15)

These statements are also proved in Lean. The dyadic term cannot vanish
on the real line because c<=1<2. The remaining Xi factor is on the
strict Euler side since beta>0. Thus the arithmetic cancellation of the
mean and the positive source ordinate are both exact source facts.

For the full totient term H, absolute unfolding in Re(s)>1/2 gives the
analytical candidate transform

    integral H(v) exp(-s v) dv
      = [Lambda(2s)/Lambda(2s+1)] hat J(-is).                (16)

The factors come from the full totient Dirichlet series and
`integral (1+x^2)^(-s-1/2) dx`. Formula (16), its continuation to the real
Fourier line, and the required contour and norm interchanges are not Lean
theorems here. Equation (15) gives the source cancellation needed at the
mean pole; it does not by itself justify that continuation.

The expected real-line factor, after those steps, is

    m(t)=Lambda(2it)/Lambda(1+2it),
    A_g(t)=hat g(t)+conj(m(t)) hat g(-t).

The paired Gaussian has leading coefficient
`eta*hat g(b)+conj(m(b))*hat g(-b)` at b. Its vanishing selects the exact
coefficient

    eta_0 = -conj(m(b))*hat g(-b)/hat g(b),                  (17)

whose source denominator is nonzero by (15). This removes a leading
amplitude, but does not move the real spectral multiplier selected by
the window: its displacement from `5/4-kappa^2` is `a^2+2iab`, where
`a=Re(kappa)`. No vanishing normalized residual follows from (17).
An exact asymptotic residual limit is not asserted: that would additionally
require the real-line transport and control after amplitude cancellation.
Do not turn this unsuccessful estimate into another exclusion module.

## 6. Source equation tested as a replacement producer

The next analytical test used the literal theta source in a differential
equation, rather than another freely chosen window. Put alpha=rho-1/2 and

    u_alpha(x)=exp(-alpha*x) integral_x^infinity exp(alpha*t) Phi(t) dt,
    q(x)=Phi'(x)/Phi(x),
    v_alpha(x)=exp(alpha*x/2) u_alpha(x)/sqrt(Phi(x)).

At an actual Xi zero, the bilateral source integral vanishes, so both tails
of u use decaying endpoint representations. Differentiation gives

    u' + alpha*u = -Phi,
    [-d^2/dx^2 + q^2/4 - q'/2] v
      = -(alpha^2/4) v -(alpha*q/2) v.                      (18)

This is the exact local equation; the linear term in alpha remains.
The inspected Witten ground-state and reflected Riccati source theorems
do not remove that term. Therefore this test has not produced a
self-adjoint occurrence construction. Weighted domain and endpoint
claims for v, and any integrated coercive estimate for (18), remain to
be proved before it can be used. No receiver with those claims as new
hypotheses has been added.

The unresolved work is still a source-specific comparison controlling
the full complex target: either (11) in the complete arithmetic norm,
or a proved theta identity controlling the retained term in (18) and
then feeding the existing SQB occurrence chain. Finite reflected-matrix
positivity is available in the corpus; the all-source comparison has
not been derived from it.

### Positive phase construction: proved

For an actual Xi multiplicity copy rho=beta+i gamma, put

    z=(rho-1/2)(-i)=gamma+i(1/2-beta),
    u(x)=hedenmalmCausalVolterra(z,x),
    b=Re(z), c=Im(z), Q=Phi'/Phi.

The corpus supplies b!=0, |c|<1 and XiC(z)=0. The original nonvanishing
conjecture is proved in the stronger form

    b Re(u(x)) < 0                 for every real x.         (19)

This is unconditional at every actual divisor copy, without assuming
critical-line placement. Define p(x)=-b u(x). Then Re(p(x))>0 globally.

The analytical mechanism uses strict logarithmic concavity of the literal
complete theta source. For a Schwartz real tail f with f'<0 on (x,infinity),

    b integral_x^infinity f(t) sin(b(t-x)) dt
      = integral_x^infinity [-f'(t)] [1-cos(b(t-x))] dt > 0

for b>0. Both endpoint terms vanish; strict positivity follows near
x+pi/b. Conjugation supplies the signed statement for b<0. For the actual
tilt f(t)=exp(-c t)Phi(t), its logarithmic slope Q(t)-c is strictly decreasing.
At every x either the right tilted tail decreases, or the reflected left
tilted tail decreases. At an actual zero, causal and anti-causal tails agree.
The factors i and exp(c x), with reflection z -> -z, give exactly (19).

The next positive conjecture, a global source logarithmic coordinate, is
also proved. With ell(x)=log(p(x)) using the principal complex logarithm,

    L(x)=u'(x)/u(x)=-iz-i Phi(x)/u(x),
    ell'(x)=L(x),
    L'(x)=(Q(x)-L(x))(L(x)+iz),                              (20)
    b (Im(L(x))+b)=Re(p(x)) Phi(x)/|u(x)|^2 > 0.              (21)

All statements (19)--(21), including differentiability and nonzero
denominators everywhere, are kernel-checked in `SelbergThetaSourcePhase`.
There are 13 public declarations with no additional mathematical hypotheses
or axioms. The [formal phase audit](../3-formalized/sqb-theta-source-phase.md)
contains the dependency-closed proof and verification details.

### Current analytical test of the retained term

The positive density d=Re(p) satisfies, by taking real and imaginary parts
of the actual first-order equation,

    d''-2c d'+(b^2+c^2)d=b^2 Phi,       d>0.                  (22)

This differential identity is established analytically here; it has not
been added as a separate Lean theorem. Gauging D=exp(-c x)d gives the
positive forced oscillator D''+b^2 D=b^2 exp(-c x)Phi. Both source tilt
and transverse parameter remain explicit.

To test the hardest term in (18), use v=exp(iz x/2)u/sqrt(Phi).
This differs from the earlier v by only a nonzero constant. Its local
logarithmic derivative is L+iz/2-Q/2. The exact equation is

    [-d^2/dx^2+Q^2/4-Q'/2]v=(z^2/4-iz Q/2)v.                (23)

If its full weighted domain and endpoint terms are justified, the imaginary
part of the integrated equation would give

    integral Q |v|^2 = c integral |v|^2.

The weighted balance and finite positive gauge mass are now justified
independently by (24) below. Full second-order operator-domain admission
and the native source comparison remain unproved. Equations (22)--(23) are not counted as
native occurrence. No new conditional receiver or exclusion theorem was
introduced. The SQB completion target remains the normalized bound (11).

### Positive variance identity: proved

For every real tilt |a|<1, write f_a=exp(a x)Phi, w_a=exp(a x)|u|^2/Phi,
h_a=z+ia, and V_a=integral f_a |u/Phi+1/h_a|^2. Lean proves

    0 < V_a,
    integral (Q+a) w_a = 2(a+c)V_a,                        (24)
    integral w_a = V_a + (integral f_a)/|h_a|^2.

The actual two-ended mode/source ratio is globally bounded. The theta
Schwartz source therefore supplies absolute integrability of w_a, the
source current and the variance, and vanishing endpoint terms. Integrating
the tilted first-order equation gives integral exp(a x)u=-integral f_a/h_a.
Expanding the squared deviation gives the energy decomposition; integrating
w_a' gives (24). Strict variance follows because a constant mode/source
ratio contradicts the distinct logarithmic slopes at 0 and 1.

At the original weight the full source current is 2cV_0. At the required
gauge a=-c, the previously provisional source balance is now proved with
its integrability and endpoints:

    integral Q w_(-c) = c integral w_(-c),
    0 < integral w_(-c) < infinity.

`SelbergThetaSourceVariance.lean` contains 23 public declarations for these
statements. Its [formal audit](../3-formalized/sqb-theta-source-variance.md)
records the checks. The reflected-product curvature theorem was inspected
for a direct bound; its potential concerns Phi(u+t)Phi(u-t), and was not
substituted for the different forced-mode potential. The variance identity
is the positive replacement. Native Gram transport remains unproved.

### Quantitative positive continuation: gauge energy between one and two source units

The variance calculation exposes the stronger source estimate

    m/b^2 < M < 2m/b^2,                                    (25)
    m=integral exp(-c x)Phi(x),
    M=integral exp(-c x)|u(x)|^2/Phi(x).

This is proved in Lean by the following closed calculation. The lower estimate
is the strict variance formula at a=-c. Write f=exp(-c x)Phi, U=exp(-c x)u,
w=exp(-c x)|u|^2/Phi. The original equation gives U'=-ibU-if, hence

    integral U=-m/b,
    integral x U=-(integral x f)/b+i m/b^2.

The weighted energy derivative is w'=(c-Q)w-2 Im(U). Integrating this
identity and its product with x gives

    integral (Q-c)w=0,
    integral x(Q-c)w=M-2m/b^2.

The moments and endpoint terms used here are justified by the proved
boundedness of u/Phi and the tilted theta Schwartz source. Put
mu=(integral x w)/M. Since w>0 everywhere and Q is strictly decreasing,

    P(x)=-(x-mu)(Q(x)-Q(mu))w(x) >= 0,
    P(mu+1)>0,
    integral P=-integral x(Q-c)w > 0.

The last identity uses integral (x-mu)w=0 and the exact source balance.
Thus M<2m/b^2. This is a uniform
relative bound on the actual source energy, retaining the transverse
parameter c in its weight. Its transport to the complete native Gram norm
is still required before it can contribute an occurrence proof.

### Stronger positive continuation: a strict pointwise disk

The energy argument yields a stronger pointwise statement, also proved
in `SelbergThetaSourceEnergy`:

    |1+b u(x)/Phi(x)| < 1                   for every x.    (26)

Use the same exact gauge U=exp(-c x)u and w=exp(-c x)|u|^2/Phi, and put

    H(x)=w(x)+2 Re(U(x))/b.

The literal first-order equations give H'=(c-Q)w. Both endpoint limits
of H are zero by the bounded source ratio and Schwartz decay. At any
fixed x, if Q(x)>=c then H is strictly decreasing on (-infinity,x];
if Q(x)<=c then H is strictly increasing on [x,infinity). In either case
the appropriate zero endpoint forces H(x)<0. Clearing positive factors
gives b^2|u|^2+2b Phi Re(u)<0, exactly the disk inequality (26).

It follows analytically that |u/Phi|<2/|b|. The phase consequence is
separately formalized, with the exact source-density identity retained:

    b (Im(L(x))+b/2) > 0.                                (27)

Thus the phase current is positive in the half-spectral gauge required
by (23), strengthening the previous full-shift statement (21).
The two-ended source estimate now supplies an explicit pointwise bound;
it does not remove the retained Q forcing or prove automorphic occurrence.
The [energy and disk audit](../3-formalized/sqb-theta-source-energy.md)
records the five public declarations and their verification.

### Native positive-weight transfer: current construction

The current conjecturing loop transfers the actual source disk through the
complete primitive-row periodization. The native Casimir fixes the half-density
profile: with x=log(y)/2 and z=b+ic, define literal seeds

    h_f(y)=sqrt(y)Phi(x),
    h_U(y)=sqrt(y)u(x),
    P_f=periodize(h_f), P_U=periodize(h_U).

The positive theta envelopes make both row sums absolute and both sources
bounded on the native modular cell. The rowwise disk estimate survives
positive summation with strictness retained at the identity row:

    |P_f(z)+b P_U(z)| < P_f(z),       P_f(z)>0.

Put h=z-i and m=2 integral exp(-x)Phi(x). Absolute strip unfolding and
y=exp(2x) give integral P_f=m and integral P_U=-m/h. Weighted
Cauchy--Schwarz, first within each complete row
sum and then on the native cell, gives the positive norm comparison

    m/|h|^2 <= integral_fd |P_U|^2/P_f
             <= 2 integral exp(-x)|u|^2/Phi < 2m/|h|^2.

This comparison includes all cross terms. Its averaging defect is the
integral of the within-orbit weighted variance of u/Phi. The centered
source V=P_U+P_f/h has zero native mean; its weighted norm equals the native
middle quantity minus m/|h|^2. The complete half-density Casimir calculation
retains the required e=5/4+z^2/4 and gives

    (A-e)P_U = (1/4) periodize[sqrt(y)(z Phi+i Phi')],
    (A-e)V = -1/(4(z-i)) periodize[sqrt(y)(D-1)(D-iz)Phi],

where D differentiates the original x coordinate. Strict nonvanishing of
V, full graph admission and a vanishing normalized residual still require
proof. These statements are the
current analytical construction, not yet counted as Lean theorems or
normalized occurrence. Source admission and the norm comparison are being
formalized together so they can be tested against the actual residual.

## Verification boundary

Equations (14) and (15), with the stated exponential integrability, are
kernel-checked in `SelbergThetaDilationTransform.lean`. The source-phase
statements (19)--(21) are also kernel-checked, in
`SelbergThetaSourcePhase.lean`; the exact variance and gauge-balance
statements (24) are kernel-checked in `SelbergThetaSourceVariance.lean`.
Energy bounds (25), the disk (26), and gauge phase current (27) are
kernel-checked in `SelbergThetaSourceEnergy.lean`. The original modular source admission, full
Gram identity, Gaussian matrix comparison and remaining weighted differential
construction retain the analytical status stated above. No numerical
experiment or new no-go module was performed. No normalized occurrence
estimate or RH proof is claimed.

The [formal correlation audit](../3-formalized/sqb-theta-dilation-correlations.md)
records source checking, the leaf build against existing dependency artifacts,
all 36 axiom checks, and the lint state at that audit. The phase audit has
13 successful axiom checks and a later successful repository lint run.

Discovery used broad OR corpus queries for intertwining/transmutation,
source/resonance/synthesis, Mellin/Eisenstein/unfolding, theta kernels,
and Gram/totient/Hankel structure. The Deninger Gelfand source lift was
inspected and still requires the Hilbert realization; it was not used as
an unconditional producer. The co-Poisson Fourier identity was inspected
with its actual admission assumptions; it was not assumed to be a native
modular intertwiner.
