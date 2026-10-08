# Cycle27 — polar density inside every exact finite atom fibre

Status: dependency-closed paper argument, fully formalized and leaf/axiom
audited through cycle29. No energy bound follows.
Verdict: BRIDGE. This is an actual recovery statement, not a lower-energy
producer. Scientific novelty beyond the classical parent theories remains
unestablished. Neither E-escape nor E-recovery is settled.

## Exact statement

Use the corpus's paper Fourier transform and literal atomCoeff. Write

    rho_f(t) = |paperFT(f)(t)|^2,
    m(f) = integral |f(u)|^2,
    A(f)_n = atomCoeff(f,n), n >= 2.

Let K(v) be the spectral densities of all finite nonnegative mixtures of
complex compact C2 tests with total atom vector v. Let Kpol(v) be the same
set with both Fourier values at i/2 and -i/2 zero in every row. Apertures,
profiles and row counts are unrestricted. The vector v has finite support;
its coordinates outside that support are still required to vanish exactly.

**Fibre-density theorem:** for every finitely supported real v,

    closure_L1 Kpol(v) = closure_L1 K(v).

Equivalently, every actual finite nonnegative full-test mixture admits,
for every epsilon>0, an actual finite nonnegative polar mixture with the
same coefficients at EVERY integer n>=2 and spectral L1 error <epsilon.
There is no energy, aperture, derivative or row-count estimate.

The null version was suggested by the cycle26 diagnostic. The proof below
forces the stronger all-fibre assertion. It has been returned through the
paper and scope audits rather than silently substituted for E-recovery.

## 1. Exact coordinate reachability

For each n>=2 the corpus twoPointResonator(n,+/-1) is an actual compact
smooth polar test whose only nonzero integer coordinate is

    A(f)_n = +/- 2 resonatorMass(n),   resonatorMass(n)>0.

Consequently every finitely supported v is attained by a finite positive
polar mixture, after scaling the appropriate signed coordinate rows.
The zero vector is attained by the empty mixture. These are exact
identities, including the entire zero tail, not limiting interpolation.

Parents: isPolarTest_twoPointResonator and atomCoeff_twoPointResonator in
WeilPositivityPrimeBlindDuality.lean.

## 2. A bounded spectral separator yields a constant Toeplitz bound

Let ell be any bounded real linear functional on real L1. Suppose some
real coefficient sequence b obeys

    A_b(f) := sum_(n>=2) b_n A(f)_n <= ell(rho_f)

for every compact C2 polar f. Each sum is finite. Put C=2*pi*||ell||.
Plancherel gives ell(rho_f)<=C*m(f).

Apply this to the actual polar multiplicative resonator with arbitrary
finite complex coefficients c_m. The exact mass and atom identities,
after division by the positive profile mass, give

    2 Re sum_(n>=2,m>=1) b_n c_(nm) conjugate(c_m)
      <= C sum_m |c_m|^2.                                      (1)

All sums are finite because c has finite support. No bound or sign of b,
Dirichlet series, RH, or energy inequality has been assumed. In particular
the right side is constant in the largest index; it has no log N term.

Parents: resonator_poles, resonator_log_sample and resonator_mass in
WeilWorkPBAPCriticalResonator.lean. Using raw atomCoeff removes sqrt(n)
from (1); the normalized logVector convention instead absorbs it in b.

## 3. Transfer (1) to every compact source

Fix a complex compact C2 source f, supported in [-a,a]. Set
M=max(2,floor(exp(2a))) and let P be the finite set of primes <=M. For
L>=0 put

    B_L = { product_(p in P) p^e_p : 0<=e_p<=L }.

Unique factorization gives |B_L|=(L+1)^|P|. In (1), at each real x, insert
c_m=f(x-log m) for m in B_L, and zero otherwise; then integrate over x.
All sums remain finite. Translation invariance and the autocorrelation
definition give

    sum_(2<=n<=M) b_n A(f)_n q_L(n) <= C*m(f),                  (2)

where

    q_L(n) = |{m in B_L : nm in B_L}| / |B_L|
           = product_(p in P) max(0,L+1-v_p(n))/(L+1).

Terms n>M vanish because the correlation is supported in [-2a,2a].
Every n<=M factors over P, so q_L(n)->1. Taking the limit of the fixed
finite sum in (2) proves

    A_b(f) <= C*m(f)                                           (3)

for every compact C2 f, without either polar condition. This explicit
finite-box argument proves the required transference; no unproved
continuity between the discrete and ordinary topologies is used.

Its classical parent is positive definiteness of discrete measures:
Lenz--Strungaru, Proposition 2.4,
[Note on the set of Bragg peaks with high intensity](https://arxiv.org/pdf/1412.7377).
The argument here specializes that principle to the literal integer atoms.

For Lean the same argument uses B_L=divisors(D^(L+2)), D=M!, avoiding
new prime-box enumeration. For each n<=M, n divides D, so

    divisors(D^(L+1)) subset {m in B_L : n*m in B_L} subset B_L.

The divisor-count formula gives

    |divisors(D^(L+1))| / |divisors(D^(L+2))|
      = product_(p|D) ((L+1)*v_p(D)+1)/((L+2)*v_p(D)+1) -> 1.

Squeezing gives the same overlap limit. Each prime exponent in this fixed
finite product is positive. No enumeration or numerical computation is
required.

## 4. Remove the polar restriction from the separator inequality

Define Q(f)=C*m(f)-A_b(f). By (3), Q is a nonnegative Hermitian quadratic
form on compact C2 sources. Translation leaves Q invariant: it leaves
both mass and autocorrelation unchanged. Polarization and Cauchy--Schwarz
therefore make sqrt(Q) a translation-invariant seminorm. This does not
assert that Q is bounded in the physical L2 norm.

For X>0 define

    c_X = 1/cosh(X/2),
    S_X f = f - (c_X/2)(f(.-X)+f(.+X)).

The Fourier multiplier is 1-c_X*cos(X*z), so S_X f is compact C2 and
vanishes exactly at z=+/-i/2. As c_X->0, the seminorm triangle inequality
gives

    sqrt(Q(S_X f-f)) <= c_X sqrt(Q(f)),
    ||S_X f-f||_2 <= c_X ||f||_2.

Thus Q(S_X f)->Q(f) and m(S_X f)->m(f), hence
A_b(S_X f)->A_b(f). Plancherel and

    || |F|^2-|G|^2 ||_1 <= ||F-G||_2 (||F||_2+||G||_2)

give rho_(S_X f)->rho_f in L1. Apply the assumed polar inequality to
S_X f and pass to the limit:

    A_b(f) <= ell(rho_f)                                      (4)

for every compact C2 source f. Crucially, arithmetic continuity comes
from the positive form Q, not from an invalid exchange of a growing
atom sum with the L1 limit.

Cycle28 quantitative implementation: define the literal finite-on-compact
functional

    q_b,C(k) = C*k(0) - sum_(n>=2) b_n*(k(log n)+k(-log n)),
    K_f(y) = q_b,C(translate_y(corr_f)).

The full mass bound proves positive definiteness of K_f by expanding the
autocorrelation of an arbitrary finite complex translated packet. Thus
|K_f(y)| <= Q(f). The exact three-source expansion gives

    Q(S_X f)-Q(f)
      = -c_X*(K_f(X)+K_f(-X))
        + c_X^2/4*(2*K_f(0)+K_f(2X)+K_f(-2X)),
    |Q(S_X f)-Q(f)| <= (2*c_X+c_X^2)*Q(f).

The same multiplier gives the pointwise density estimate

    |rho_(S_X f)(tau)-rho_f(tau)|
      <= (2*c_X+c_X^2)*rho_f(tau).

Integrating proves actual L1 convergence. Subtracting the zero-atom mass
form from q_b,C proves convergence of the raw arithmetic pairing. For a
bounded real L1 functional ell, its norm supplies C=2*pi*||ell|| through
Plancherel. This yields an unconditional equivalence between its polar
and full arithmetic lower bounds. It supplies section4, not section5:
S_X f alone does not preserve the exact integer trace.

## 5. Separate a fixed fibre and derive a contradiction

Fix v and rho in K(v). Suppose rho is outside closure_L1 Kpol(v).
This closed convex set is nonempty by section 1. Strict point-versus-set
separation gives a bounded real ell such that

    ell(rho) < inf {ell(eta): eta in Kpol(v)}.                  (5)

Let p(w) be that infimum in the fibre w. It is finite for every w:
coordinate reachability supplies an upper bound. If p(w)=-infinity,
append any fixed polar mixture in fibre v-w; this forces p(v)=-infinity,
contrary to (5). Similarly no negative-cost null mixture exists, since
arbitrary positive multiples could be appended to a fixed mixture in
fibre v. Thus p(0)=0. Mixture addition and nonnegative scaling show that
p is a finite sublinear functional on the real vector space of finitely
supported atom vectors.

The algebraic Hahn--Banach theorem supplies a linear b with b(w)<=p(w)
for every w and b(v)=p(v). To verify its one-dimensional starting step,
for t>=0 use p(tv)=t p(v); for t<0 use -p(v)<=p(-v), which follows from
subadditivity at v+(-v)=0. When v=0 start on the zero subspace.

In particular A_b(f)<=ell(rho_f) for every polar row. Sections 2--4
extend this to every full row. Summing over the actual nonnegative
mixture representing rho yields

    ell(rho) >= b(v)=p(v),

contradicting (5). Hence K(v) lies in closure Kpol(v). The reverse
closure inclusion is immediate from Kpol(v) subset K(v).

Cycle29 implementation of this algebraic step avoids defining the infimum.
Choose s with ell(rho)<s<=ell(eta) for every eta in Kpol(v). Adjoin one
artificial row with trace -v and cost -s to the actual polar rows. Consider
any finite nonnegative null combination of this augmented system, and let
alpha be its artificial-row coefficient. Its remaining actual mixture d
has trace alpha*v. If alpha>0, d/alpha lies in Kpol(v), so its cost is at
least s; hence the augmented total cost is nonnegative. If alpha=0,
suppose d had negative cost. Add t*d to any fixed actual mixture c0 in
Kpol(v), with t=(cost(c0)-s+1)/(-cost(d))>0. Its trace remains v and its
cost is s-1, a contradiction. Thus the augmented null-cone condition
holds in both cases. Signed coordinate resonators provide the two-sided
coordinate reachability required by the corpus's algebraic feasibility
theorem. It supplies b with b(v)>=s and the actual polar-row inequality.
Section4 extends the latter to full rows; summing the given full mixture
contradicts ell(rho)<s<=b(v). This proves the same exact-fibre conclusion,
including v=0 and the empty mixture, without any new feasibility premise.

## Consequences and limits

1. The literal nonpolar fejerTest has zero integer trace. Therefore
   actual exact-null polar recovery families exist in spectral L1.
   E-escape, if true, cannot be vacuous through failure of recovery.
2. Every finite exposing trace has the same L1 fibre closure with and
   without the two rowwise polar zeros. A bounded spectral functional
   cannot distinguish those two closed fibres.
3. No bound on the recovery's signed archimedean energy follows. Its
   multiplier is unbounded; bounded energy itself would still not give
   uniform integrability. Neither the universal lower inequality nor
   the vanishing mass-defect producer is proved here.
4. The earlier MATCHED-SPECTRAL-LIMIT conjecture controls one prescribed
   upper construction with an energy and aperture rate. This theorem
   controls every finite full-test fibre, but supplies none of those
   quantitative rates. It is a different statement.
5. This is not polar-to-full admission for WeilPositive: its gamma term
   gives a log N Toeplitz bound, whereas section 3 needs a constant.

## Hostile and novelty audit

- Exact poles and all infinitely many integer equations are retained.
- Complex profiles, arbitrary finite positive mixtures and v=0 are included.
- Empty mixtures and zero coefficients cause no exceptional case.
- Far polarization alone does not preserve atoms; section 4 uses it only
  inside the dual proof. The final recovery follows from separation.
- No boundedness of A_b on L2 is assumed: only positivity of Q and
  translation invariance are used.
- The finite-box transfer, algebraic Hahn--Banach, seminorm argument and
  strict separation are classical. No novelty is claimed for them.
- The actual all-fibre conclusion was not supplied by the inspected
  corpus hits. Search absence is not a proof of scientific novelty.
- Lean must prove this actual conclusion, not accept transference or
  recovery as an added hypothesis and present a conditional receiver.

## Formalization plan

1. Prove actual constant Toeplitz transfer with finite prime-exponent
   boxes; keep all correlation and finite-sum integral identities exact.
2. Prove the positive-form far-polarization limit and separator extension.
3. Build the actual L1 fibre sets, sublinear cost and separation argument;
   finish the unconditional all-fibre theorem and literal Fejer corollary.
4. Audit every public theorem, wire completed leaves into RHTower, and
   run only their foreground `lake --old env lean` checks plus formal lint.

Formal checkpoint: the installed 393-line `WeilWorkExposingRayFibreTransfer`
leaf verifies the divisor
overlap, finite translated-source averaging, constant Toeplitz transference,
and the unconditional equivalence of `PolarMassBound b C` and
`FullMassBound b C` for every real b,C. Its final foreground leaf audit
exits0 without warnings; both public theorem imported axiom audits exit0
with exactly propext, Classical.choice and Quot.sound.
Section4 is now formalized in the 490-line
`WeilWorkExposingRaySeparatorExtension` leaf. Its capstone
`polarSpectralBound_iff_fullSpectralBound` quantifies over every actual
bounded real linear functional on real L1 and every real arithmetic
coefficient sequence. It proves the polar/full equivalence without
transference, recovery, coefficient-growth or RH premises. The source
Fourier multiplier, both exact polar zeros, positive-kernel bound, and
quantitative arithmetic and spectral L1 limits are included. The saved
leaf's foreground `lake --old env lean` audit exits0 without diagnostics.
All11 public theorem imported axiom audits exit0 with exactly propext,
Classical.choice and Quot.sound. Global formal lint exits1 on8 unrelated
unreachable modules; it reports no WP02 issue.
Section5 and the actual exact-fibre conclusion are formalized in
`WeilWorkExposingRayFibreDensity` (330 lines). Public capstones prove the
closure equality, actual finite positive recovery, literal raw-atom
preservation at every integer, and literal Fejer exact-null recovery.
The saved leaf and all5 imported public theorem axiom audits exit0 without
diagnostics; axiom sets are exactly propext/Classical.choice/Quot.sound.
All23 owned leaves are wired. Cycle29 global lint reports7 unrelated
unreachable modules, no WP02 issue; exact names are in EVIDENCE.md.
No recovery-energy bound is supplied.

## Cycle28 energy diagnostic

The formal separator extension immediately proves on paper a uniform
cutoff obstruction. If g is bounded measurable, g<=gamma everywhere, and
ell_g is its bounded real L1 integration functional, no arithmetic sequence
b satisfies PolarSpectralBound(b,ell_g). Otherwise the formal equivalence
would extend that inequality to the literal Fejer source psi. All integer
atoms of psi vanish, so 0<=ell_g(rho_psi). But positivity of rho_psi and
g<=gamma give ell_g(rho_psi)<=E(psi)<0, a contradiction. This applies to
g=min(gamma,R), since gamma has a constant lower bound.

The scope is all compact sources and all apertures with one fixed cutoff.
It does not exclude cutoffs that depend on aperture or on a chosen family.
It also does not decide whether actual exact-null L1 recovery has bounded
full gamma energy. The implication is paper-derived here; its separate Lean
instantiation has not been performed. The positive survivor is the proved
bounded-separator equivalence and now-proved actual exact-fibre recovery.
