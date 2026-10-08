# One-pole recovery below logarithmic spectral cost

Cycle32. Status: dependency-closed paper proof and complete Lean
formalization in six new leaves, ending in
WeilWorkExposingRayOnePoleFibreDensity.lean. All six final saved-leaf
audits and all33 public theorem axiom audits pass. Verdict BRIDGE;
external scientific novelty unestablished.
This advances a larger exponent range on the one-pole source class. It
neither narrows nor solves the original all-full-source beta<1 conjecture
or the universal WP02 inequality.

## Exact conjecture selected and audited

Let 0<=beta<1 and w(t)=1+log(2+|t|)^beta. Let Kone(v) be the densities
of actual finite nonnegative mixtures of compact complex C2 functions,
each row satisfying AT LEAST ONE of Fhat(i/2)=0 or Fhat(-i/2)=0, whose
raw integer trace is v at EVERY integer n>=2, including the zero tail.
Different rows may choose different poles. Let Kpol(v) require both zeros
on every row, with otherwise exactly the same source and mixture class.
The selected statement is

    closure_L1(w dt) Kone(v) = closure_L1(w dt) Kpol(v)

for every finitely supported real trace v. Equivalently, every such actual
one-pole mixture admits arbitrary weighted recovery by actual two-pole
mixtures with the whole integer trace exact. No common support, profile,
row count, energy, coefficient growth or positivity hypothesis is added.

The stronger full-source statement for1/2<=beta<1 remains OPEN. The literal
Fejer source has neither pole zero, so this theorem does NOT upgrade its
recovery beyond the already proved beta<1/2 range.

The first attempted shortcut was classical conditional positive-definite
distribution theory. The inspected Chung–Kim2005 theorem uses homogeneous
polynomial differential constraints; it is not a ready-made theorem for
the two imaginary evaluations here. Booker/Oliver L-data classification
also cannot be used without its discrete divisor/admissibility conditions.
The proof below instead uses actual resonators and a finite-translation
recurrence, paying its source growth explicitly.

## 1. Set up the actual separating form

Fix any real continuous linear functional ell on L1(w dt), any real
sequence b, and suppose

    A_b(f) <= ell(rho_f)

on every actual two-pole source. Here A_b(f)=sum_(n>=2)b_n atomCoeff(f,n)
and rho_f=|paperFT f|^2. Each individual atom sum is finite.
Set Q(f)=ell(rho_f)-A_b(f). This is a real quadratic form on compact
complex C2 sources, invariant under real translation. For a fixed f put

    k_f(x) = (Q(f+tau_x f)-2Q(f))/2,
    tau_x f(u)=f(u-x).

Thus k_f(0)=Q(f), k_f(-x)=k_f(x), and for real coefficients r_j,

    Q(sum_j r_j tau_(x_j)f) = sum_(j,k)r_j r_k k_f(x_j-x_k).

These follow by expanding both the squared Fourier modulus and the
finite arithmetic correlation pairing. The spectral cross term is ell
applied to rho_f(t)*cos(xt); its absolute value is at most
norm(ell)*integral w*rho_f. It is therefore bounded uniformly in x.
No representing measure or full-positivity extension is assumed.

## 2. Derive the critical exponential kernel growth

The actual polar resonators, their exact raw trace and zero tail, and
`resonator_logWeighted_mass_bound` give the growing Toeplitz bound from
cycle30. Their primitive star vectors imply, for some D>=0,

    sum_(n in S)b_n^2 <= D^2*(1+log N)^(2beta)

for EVERY primitive S contained in[2,N]. This is valid for0<=beta<=1;
no harmonic-envelope assumption is required.

Write B(N)=sum_(2<=n<=N)|b_n| and L(N)=D*(1+log N)^beta. Then

    B(N) <= 4*sqrt(N)*L(N), N>=1.                    (1)

Proof by strong induction on N. N=1 is zero. For N>=2 put M=floor(N/2).
The set (M,N] is primitive: if k>=2 and n>M then kn>=2(M+1)>N.
Its size is at most N. Cauchy–Schwarz and the preceding square bound give
its absolute mass at most sqrt(N)*L(N). The remaining[2,M] mass is at
most4sqrt(M)L(M). Since L is nondecreasing on positive integers and
4sqrt(M)<=3sqrt(N), their sum is at most4sqrt(N)L(N). This proves(1)
without counting the number of dyadic levels.

Choose a>=0 with support(f) contained in[-a,a]. Its correlation is
continuous, bounded by some Mf, and supported in[-2a,2a]. In the
arithmetic cross term at x only n<=exp(|x|+2a) occur. By(1), and the
bounded spectral cross term above, there is a finite Cf>=0 such that

    |k_f(x)| <= Cf*exp(|x|/2)*(1+|x|)^beta.          (2)

Rounding the cutoff down only improves its square root; its logarithm
is at most |x|+2a. The finitely small cutoffs are absorbed into Cf.
All constants depend on f,b,ell,beta; none is assumed uniformly over f.

## 3. The translation recurrence removes one constraint

For every real x, the actual three-translate source

    f_x = f - [tau_x f + tau_(-x)f]/[2*cosh(x/2)]

has BOTH pole zeros. Write c=1/cosh(x/2)>0. Its nonnegative form is

    0 <= (1+c^2/2)k_f(0)-2c*k_f(x)+(c^2/2)k_f(2x).

Consequently, with d(x)=k_f(x)-k_f(0)*cosh(x/2),

    d(2x) >= 4*cosh(x/2)*d(x).                     (3)

For x>0 define G(x)=exp(-x/2)*d(x). Equation(3) becomes

    G(2x) >= 2*(1+exp(-x))*G(x).                  (4)

Equation(2) gives G(x)<=C'_f*(1+x)^beta. If G(x0)>0 for some x0>0,
induction in(4) gives G(2^j*x0)>=2^j*G(x0). Dividing the upper bound
by2^j contradicts beta<1 as j tends to infinity. Thus d(x)<=0 for
x>0, and evenness plus d(0)=0 give

    k_f(x) <= Q(f)*cosh(x/2) for EVERY real x.     (5)

In particular, for either r=exp(x/2) or r=exp(-x/2),

    Q(tau_x f-r*f)
      = (1+r^2)Q(f)-2r*k_f(x) >=0,              (6)

because1+r^2=2r*cosh(x/2). These are actual sources, with respectively
one or the other pole zero. The conclusion holds for ALL f, not only a
fixed-profile family. The estimate(5) does not assert Q(f)>=0.

## 4. Every actual one-pole source is covered

Suppose f is compact C2 and integral exp(-u/2)f(u)du=0, equivalently
paperFT f(i/2)=0 under this corpus's `exp(I*z*u)` convention. Define

    g(u)=exp(u/2)*integral_(-infinity,u) exp(-v/2)f(v)dv.

Then g is compact C3, supported in any interval supporting f:
below that interval the integral is zero, and above it the pole condition
makes the complete integral zero. Differentiation gives g'-g/2=f.
For h tending to0 through positive values,

    [tau_h g-exp(-h/2)g]/h -> -f

in C2 uniformly, with a common compact support for0<h<=1. Every numerator
has nonnegative Q by(6); division by positive h preserves the sign of Q.

Q is continuous for this convergence. For the arithmetic term, one fixed
compact support fixes a finite integer cutoff, and correlations converge
uniformly by elementary integral bounds. For the spectral term,
common-support C2 convergence implies Fourier differences bounded by
C*epsilon/(1+|t|^2), by direct integration and twice integrating by parts.
Their weighted L2 norms tend to zero since
integral w(t)/(1+|t|^2)^2 dt is finite. Cauchy–Schwarz applied to
|rho_u-rho_v|<=|F_u-F_v|*(|F_u|+|F_v|) gives weighted L1 convergence.
Continuity of ell follows. Therefore Q(f)=Q(-f)>=0.

For the other pole, use exp(-u/2) times the primitive of exp(v/2)f(v),
so g'+g/2=f, and the r=exp(h/2) version of(6). All signs and support
conditions are retained. This proves extension of EVERY weighted polar
separator to every one-pole source, with no added research premise.

Lean implementation refinement: common-support C2 convergence can be
replaced by a cheaper direct Fourier argument. The primitive equation gives
Fhat(f)(t)=-(I*t+1/2)Fhat(g)(t). For0<h<=1 the normalized translation
multiplier is bounded by2|t|+1, whose square is at most8(t^2+1/4).
Thus the weighted densities of the difference quotients are dominated by
8w(t)|Fhat(f)(t)|^2, already integrable. Pointwise multiplier convergence
and dominated convergence give weighted L1 convergence. One common compact
support fixes the finite atom cutoff; the Fourier cosine atom identity
then transfers this convergence to every atom in that cutoff. The other
sign uses g'+g/2=f and the same constant bound: for0<h<=1,
|exp(+-h/2)-1|<=h. This proves exactly the same closure passage and
does not impose any additional regularity on f.

## 5. Recover the exact whole fibre

Use the same actual signed coordinate polar resonators and strict Banach
separation as in POLAR-FIBRE-DENSITY-PROOF.md, now with the one-pole source
class in place of all full sources, and ambient space L1(w dt). The polar
fibre remains convex, nonempty for every finite trace, and contained in
the one-pole fibre. If a finite one-pole mixture were outside the closed
polar fibre, separate it by ell and a strict level. Append the artificial
row(-v,-s), use the existing algebraic null-cone duality to obtain b,
and apply section4 to EVERY row of the given mixture. Summing its
nonnegative coefficients contradicts strict separation. Reverse inclusion
of closures follows from inclusion of the source classes.
Metric closure gives finite positive recovery; clearing the nonzero sqrt(n)
factors in logVector gives exact raw atom identities for EVERY n>=2.
This is the same dependency-closed separation proof already verified in
WeilWorkExposingRayFibreDensity and SublogFibreDensity.

## Hostile boundary and remaining main problem

The growth threshold in the ABSTRACT recurrence is sharp. The even kernel
k(x)=x*sinh(x/2), with k(0)=0, satisfies equality in(3), but
k(x)>k(0)*cosh(x/2) for x>0. Its kernel quadratic vanishes when both
exponential moments vanish: expansion of (x-y)sinh((x-y)/2) factors each
summand through one zero moment. Its growth is O(x*exp(x/2)); it can
violate one-pole positivity. This is an abstract repeated-pole example,
NOT a source-realized arithmetic separator and NOT a counterexample at
beta=1 for the actual corpus problem.

The remaining full-source obstruction can contain a pure cosh term,
which is invisible even when just one pole vanishes. Neither(5) nor the
one-pole recovery theorem removes it. Eliminating or identifying that
actual arithmetic contribution remains an OPEN CORE for the original
beta<1 full-source conjecture and the critical gamma-energy problem.
No such open core is inserted into the selected one-pole theorem.

Classical ancestry: positive-definite kernels, finite translation
quadratics, elementary doubling growth and Hahn–Banach separation.
Novelty of this exact arithmetic-source application is unestablished.
The payoff is identifying a surviving simple-pole obstruction after the
repeated-pole growth is excluded; it is not an RH positivity proof.

## Final Lean implementation and audit

- LogLocalMass: actual primitive-square bounds give the square-root local
  coefficient mass bound without an extra logarithm.
- CoshDoubling and LogKernel: abstract sharp recurrence, actual-source
  growth, cosh majorant, and both exponential difference families.
- OnePolePrimitive: actual compact C3 solution of g'-s*g=f, including the
  exact Fourier identity, for either half-pole zero of a compact C2 f.
- OnePoleTransfer: normalized differences converge in weighted L1;
  density is bounded by8 times the original, error by9 times its weighted
  density. A common compact support fixes the entire arithmetic cutoff.
  Each raw atom difference is bounded by weighted L1 error divided by pi.
  Every actual polar separator therefore extends to every one-pole row.
- OnePoleFibreDensity: equality of whole fibre closures and actual finite
  positive recovery with exact raw atoms, including every zero-tail atom.

All filenames have the WeilWorkExposingRay prefix. Every final audit used
`lake --old env lean <leaf>` with its leaf cache output. The combined
imported axiom audit covers all33 public theorems and reports only
propext, Classical.choice and Quot.sound. All35 owned leaves are wired
exactly once. No full or umbrella build, heartbeat override or numerical
experiment was used. Global lint's five remaining reachability errors
belong to unrelated HTGeometry modules.
