# Finite heads inside the actual polar xi carrier

Status: paper-only BRIDGE, not a new scientific result or an audited Lean
theorem. The quantitative conjecture below is OPEN. Universal WP02 is OPEN.
These sources are not compact; they are not admitted to `IsPolarTest a`.

## Exact diagnostic

Use the paper Fourier convention and put

    gamma(t) = archimedeanWeilSymbol(t/(2*pi)),
    A(t) = (t^2+1/4)*XiC(t),
    F_P(t) = A(t)*P(t)                         (P a complex polynomial).

All integrals here are real-line Lebesgue integrals in the paper frequency
variable. For a finite list of polynomials define

    rho(t) = sum_j |F_(P_j)(t)|^2,
    mass(rho) = integral rho,
    E(rho) = integral gamma*rho,
    b_n(rho) = integral cos(t*log n)*rho(t).

Weights are absorbed into the polynomials. The inverse transform of F_P is
`(1/4-D^2) P(iD) Phi`. The actual derivative-transform identities give this
formula: paperFT(D f)(z)=-i*z*paperFT(f)(z). Every such source is smooth with
the corpus's derivative decay, vanishes at both half-poles, and its entire
transform vanishes at every actual zeta-zero evaluation. None of these facts
asserts compact support. The symmetric integer atom is b_n/pi; only its
vanishing is used below.

Let B be the actual `WeilPositivitySummableWeightsObstruction` Fejer source,
let m_B=integral |paperFT B|^2, and set

    c_B = -archEnergy(B)/(2*m_B) > 0.

The sign and m_B>0 follow from the corpus's strict negative energy theorem
and square-density integrability: mass zero would force energy zero. Its
autocorrelation support has radius 17/25<log 2, so every b_n vanishes for
n>=2.

**Paper claim.** For every finite M>=2 there is a finite polynomial list
such that mass(rho)=1, b_n(rho)=0 for 2<=n<=M, and E(rho)<=-c_B. No uniform
degree, coefficient, truncation-aperture, or complete-tail bound is asserted.

## Paper argument, including the energy topology

Put omega=1+|gamma| and H=L2(omega(t)dt). The actual gamma symbol is continuous
and has at most logarithmic growth. The actual Xi restriction is nonzero
almost everywhere and has every exponential decay rate below pi/4.
Polynomial factors and omega therefore leave a positive exponential margin:
for some delta>0, integral omega*|A|^2*exp(2*delta*|t|) is finite. This needs
one positive exponential margin, not all real exponential moments.

The linear span of F_P is dense in H. Indeed, if g in H is orthogonal to
every A(t)t^k, set h(t)=omega(t)*conj(g(t))*A(t). Cauchy--Schwarz gives

    integral |h(t)| exp(delta*|t|)
      <= ||g||_H * (integral omega*|A|^2*exp(2*delta*|t|))^(1/2).

All polynomial moments of h vanish. Its Fourier transform is holomorphic
in the strip of this width; differentiation on a narrower strip is justified
by the remaining exponential margin. All derivatives at zero vanish, so
the identity theorem makes that transform zero throughout the strip.
Fourier injectivity gives h=0 almost everywhere. Since omega>0 and A is
nonzero almost everywhere, g=0. The Hilbert orthogonal-complement criterion
proves the asserted density. This is the weighted version of the mechanism
already formalized in `XiPolynomialDensity`.

For v in H, write b(v) for the vector of b_n(|v|^2), 2<=n<=M. Each component,
mass, and E is continuous on H: use

    || |v|^2-|w|^2 ||_L1(omega dt)
      <= (||v||_H+||w||_H)*||v-w||_H.

Every nonzero real linear combination q(t)=sum_(n=2)^M a_n*cos(t*log n)
takes a negative value. Distinct positive logarithms give mean(q)=0 and
mean(q^2)=sum a_n^2/2>0 by direct integration over [-T,T] and division by
2T. If q were nonnegative, q^2<=||q||_infinity*q would contradict these
limits. A compactly supported nonzero L2 frequency function on an interval
where q<0 has negative q pairing and belongs to H. Density supplies an
F_P with the same strict sign.

For each unit vector a, choose one such F_P. The strict sign persists on an
open neighborhood of a. A finite subcover of the unit sphere gives a fixed
finite list V_1,...,V_s and delta_M>0 such that

    min_l a dot b(V_l) <= -delta_M          for every unit a.

Finite-dimensional separation implies that the convex hull of their b
vectors contains the closed ball of radius delta_M about zero. In particular
every residual vector r has a positive representation in these b vectors
with total coefficient at most ||r||/delta_M (and use all coefficients zero
when r=0).

Choose F_(Q_k) converging in H to paperFT(B)/sqrt(m_B). Its b vectors tend to
zero, its masses to one, and its energies to -2*c_B. Correct -b(F_(Q_k))
using the fixed V_l and nonnegative coefficients with total tending to zero.
The resulting finite positive mixture has b=0 exactly. Its mass still tends
to one, and its energy still tends to -2*c_B, because the correcting list
is fixed and has finite individual mass and energy. For a sufficiently
large k its mass is positive and its energy divided by mass is below -c_B.
Rescale all polynomials by the reciprocal square root of that mass. This
proves the paper claim, with no unproved rate assertion.

## What remains genuinely quantitative

Define d(M) as the least natural d for which the displayed conditions hold
using a finite list of polynomials of degree at most d. The paper claim
makes this finite. Degree refers to P, before the fixed polar factor in A.

**Competing exact conjectures.**

- C-linear: there are C>0 and M0 such that d(M)<=C*M for every M>=M0.
- Its negation: for every C>0 and M0 there is M>=M0 with d(M)>C*M.

Given the audited frontier, the bold question is whether coherent polynomial
cross terms can retain a fixed negative gamma energy while cancelling a
linearly growing complete integer head at only linear derivative degree.
The qualitative convex-cone construction above does not answer it. Counting
matrix variables is not a proof of positive feasibility.

[OPEN CORE] Bound, or obstruct, the degree of the positive polynomial
mixture while simultaneously retaining the exact M-1 cosine equalities,
unit mass, and fixed strict energy margin. No norm equivalence, polynomial
density theorem, diagonal derivative limit, or fixed-order tail estimate
currently read supplies that joint bound.

Verdict: SURVIVES PRELIMINARY ATTACK, but deferred as an auxiliary diagnostic
unless a proved degree bound also controls the full arithmetic tail after
physical truncation. It is not a substitute for the selected vanishing-mass
defect producer. Even C-linear by itself would not contradict WP02: the
uncancelled tail and compactness admission have not been paid.

## Ancestry and utility gate

Corpus parents checked: `XiPolynomialDensity`,
`WeilWorkDeficitRestrictedXiDensity`, the C2f finite-cone paper argument in
WP06 PROOF, actual Fejer negative energy, and the actual polar derivative
transform/zero-evaluation identities. WP06 C10 already asks for a growing
derivative family with a complete weighted tail bound; its content is
different and stronger in the direction needed for its receiver. Do not
relabel it as a discovery of this cycle. WP06 C15 is a diagonal positive
derivative-mixture problem; arbitrary polynomial cross terms are retained
here.

External primary ancestry includes
[de Jeu's extended Carleman theorem](https://arxiv.org/abs/math/0111019)
for polynomial density. Romik's
[orthogonal polynomial expansions for xi](https://www.math.ucdavis.edu/~romik/data/uploads/papers/riemannxi-acta-online-first.pdf)
concerns expansions of xi in classical bases; the weights displayed in its
introduction are gamma weights, not the actual |A|^2 constrained moment
problem above. No quantitative conclusion was transferred between them.

Classification of the paper claim: BRIDGE / classical density and convexity,
not significant new scientific knowledge. No Lean work is authorized by this
note as an automatic next step: first establish utility for the actual
all-sample, compact-polar signed lower bound. No route is declared formally
retired on the strength of this unformalized diagnostic.
