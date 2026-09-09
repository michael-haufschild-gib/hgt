# SQB positive occurrence: theta dilation loop

Status: analytical construction and norm comparison in progress. The literal
theta dilation profile and its two correlation transforms are proved in Lean
in `SelbergThetaDilationTransform`; full modular Gram transport and normalized
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

## Verification boundary

Equations (14) and (15), with the stated exponential integrability, are
kernel-checked in `SelbergThetaDilationTransform.lean`. The original modular
source admission, full Gram identity, Gaussian matrix comparison and
replacement differential construction retain the analytical status stated
above. No numerical experiment or new no-go module was performed. No
normalized occurrence estimate or RH proof is claimed.

The [formal correlation audit](../3-formalized/sqb-theta-dilation-correlations.md)
records source checking, the leaf build against existing dependency artifacts,
all 36 axiom checks, and the unrelated repository lint failures.

Discovery used broad OR corpus queries for intertwining/transmutation,
source/resonance/synthesis, Mellin/Eisenstein/unfolding, theta kernels,
and Gram/totient/Hankel structure. The Deninger Gelfand source lift was
inspected and still requires the Hilbert realization; it was not used as
an unconditional producer. The co-Poisson Fourier identity was inspected
with its actual admission assumptions; it was not assumed to be a native
modular intertwiner.
