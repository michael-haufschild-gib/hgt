# WP05 result

**Verdict: OPEN.** Assigned canonical-measure settlement problem remains unsolved.

## Centered phase cost added in cycle 58

For original full positivity alone, with actual residue B and centered trace
H(t)=F(t)-B*zeta(1/2+it), Lean proves

    |Q(T)-2*E_centered(T)| <= C*T^(5/6), T>=1.

Here Q is the actual canonical Gaussian phase cost and E_centered is the
positive-height Gaussian integral of |H|^2. A corollary gives arithmetic
rigidity/RH or an eventual lower bound Q(T)>=kappa*T with kappa>0.
No coefficient sign, multiplicativity, source functional equation, atomicity,
or energy-decay premise is added. Neither result eliminates the second branch.

Six leaves provide exact hyperbola cancellation, centered Mellin Gaussian
estimates O_c(T^c) for 1/2<c<1, zero-safe phase algebra, residue-free contour
extraction, the error bound and its dichotomy. Targeted --old build and all six
mandatory direct lake env lean audits passed. All36 public declarations use
only propext, Classical.choice and Quot.sound. Imports wired once each;
source hashes rechecked; index passed. Global lint has seven unrelated
unreachable leaves and no C58 errors. One direct log contains a nonfatal
unnecessarySeqFocus style warning. Receipt: cycle58-verification.json.

Verdict BRIDGE; independent scientific novelty not established. C59 asks for
a source-derived contractive bound on the pole-normalized completed quotient;
its arithmetic comparison remains OPEN CORE. Generic maximum-principle and
low-degree classification receivers do not supply that bound.

## Complex-power energy added in cycle18

For original full positivity, let a_z be the Dirichlet exponential of
z*logZetaCoeff(lam truncated below2). Its branch is fixed on Re(s)>1.
For every complex z with Re(1/z)>1/2 there exists K>=0 such that, for N>=1,

    sum_(1<=n<=N) |a_z(n)|^2/n
      <= K*(1+log N)^(1/(2*Re(1/z)-1)).

No coefficient sign, multiplicativity, atomicity, gap or phase premise is
added. The literal series and exact logarithmic convolution are exported
in PowerCoefficients; PowerLogMoment supplies the exact real-exponent
induction; PowerEnergy combines these with the full-source Toeplitz bound.
All three targeted --old leaf builds and mandatory direct source audits
passed; final source logs are empty. All nine public declarations use only
propext, Classical.choice and Quot.sound. Imports are wired once each and
source hashes revalidated. Lint reports six unrelated unreachable leaves,
no WP05 or forbidden-declaration error. Receipt: cycle18-verification.json.

Verdict BRIDGE, not demonstrated scientific novelty. Imaginary and negative
powers are outside this range. The sharp all-power energy conjecture and
WP05 phase settlement remain unproved. C17's mean-plus-energy saturation
shortcut is false on weaker data, not a counterexample to original full
positivity. C20's prime-restricted O(log log N) energy bound follows by Abel
summation from the primitive-set parent. The unrestricted bound and its
sharper leading-constant question remain under attack; that parent does not
control the whole composite contribution.

## Exact reciprocal remainder order added in cycle 12

`WeilWorkSettledPhaseReciprocalTailOrder.lean` proves, from the original full
positivity alone, that every polynomial-length reciprocal prefix leaves the
full original boundary atom exponent in its remainder. For every fixed real
ordinate a and A>=0, writing s_h=1/2+h+i*a and P_N for the first N reciprocal
Dirichlet terms,

    log(1+|G(s_h)-P_N(s_h)|) / log(1/h) -> boundaryMeasure(hW).real{a}

uniformly over N<=h^(-A) as h->0+. Zero atoms are included. The proof first
establishes uniformly subpower prefix growth using ordinary reciprocal
convergence and finite Abel summation, then transfers the existing atom-order
law through two triangle inequalities. No coefficient, atomicity, meromorphic
extension, or phase-settlement premise is added.

Targeted `--old` leaf build, mandatory direct `lake env lean` source audit,
and axiom audit passed. All three exports use only propext, Classical.choice,
and Quot.sound. The module is wired into the umbrella. Global lint reports
seven unrelated unreachable modules; no owned WP05 failure.

Verdict **BRIDGE**: classical parents, no significant scientific novelty claim.
This is a fixed-ordinate theorem; it does not give moving-height uniformity or
settle the phase-only approximation problem. WP05 remains OPEN. The next
focused arithmetic conjecture is vanishing normalized alternating means of
the original forward coefficients, the first nonprincipal mode of C11.

## Interior phase cancellation added in cycle 10

For the original hW there exists Y0>=4 such that, for every Y>=Y0 and
0<eta<=1, the actual regularized phase satisfies

    |integral_Y^(2Y) p_eta(t) dt| <= 18*Y/(eta^2*log Y).

The height threshold is independent of eta. This proves cancellation at every
fixed interior width, and also wherever eta(Y)^2*log Y tends to infinity.
It uses the full positive Poisson measure, the right-line arithmetic lower
bound, local Caratheodory control, and integration by parts. No atomicity,
coefficient majorant, edge continuity, phase lock, or RH premise was added.
Source: `WeilWorkSettledPhaseInteriorCancellation.lean`, capstone
`exists_integral_regularizedPhase_le`; the derivative and Poisson comparison
bounds are also exported.

Targeted --old leaf build and final standalone lake env lean audit passed.
One umbrella import is wired. All three public declarations passed axiom
inspection with exactly propext, Classical.choice and Quot.sound. Global lint reports
fifteen unrelated unreachable modules and no WP05 error.

Verdict: BRIDGE. Classical analysis now paid for the actual source, not
significant scientific novelty. It rules out transferring a near-unit boundary
mean uniformly across fixed widths. It does not refute or prove the required
near-maximal mean on eta=Y^-8, where this cancellation bound is ineffective.

Cycle11 conjecture C11 asks for square-root cancellation of actual forward
coefficients in nonprincipal rational additive modes, with polynomial modulus
cost. Exact statement, competing failure, and attacks are in PROOF.md.
It remains OPEN CORE; even its proof would leave the moving-line reciprocal
denominator tail unpaid. The existing common-ratio rigidity already excludes
the simplest normalized periodic perturbation as a genuine source.

## Explicit moving-line phase estimate added in cycle 9

For original hW, put W=integral (1+r^2)^(-1) d(boundaryMeasure hW), and

    p_eta(y)=exp(2i Im sourcePrimitive(1/2+eta+iy)).

Lean now proves, for every Y>=1,

    integral_(Y,2Y] |p_(Y^-8)(y)-p(y)| dy <= (68*pi+66)*W/Y,

where p is the full canonical phase below. The public capstone exports a
nonnegative source constant C; its proof uses the displayed constant. It needs
no atomicity, support gap, edge continuity, or extra coefficient condition.
The general two-parameter bound is also exported. Source:
`WeilWorkSettledPhaseRegularization.lean`.

Targeted --old build and required standalone `lake env lean` audit passed;
the latter had empty diagnostics. One umbrella import is wired. All three
public declarations passed axiom inspection with exactly propext,
Classical.choice and Quot.sound. Global lint reports sixteen unrelated
unreachable modules and no WP05 error.

Verdict: BRIDGE. This is a classical Poisson smoothing estimate for the actual
source, not significant scientific novelty or settlement. The phase variance
on this moving line differs from boundary variance by O(1), by an elementary
unit-circle estimate on paper. Its source-derived power saving remains unproved.
The first substantive phase-concentration milestone remains OPEN.

## Full canonical phase obstruction added in cycle 8

Put p(y)=exp(i*pi*boundaryMeasure.real(Ioc(-y,y))). For every original hW
and every real theta, either lambda(n)=vonMangoldt(n) for n>=2 and RH holds,
or there are a,K>0 and arbitrarily large Y with

    a*Y*exp(-K*log(Y)/loglog(Y))
      <= integral_(Y,2Y] |p(y)-exp(2*pi*i*theta)| dy.

This is an unweighted phase bound for the full canonical measure: diffuse,
central and low-ordinate mass are retained. No atomicity, support-gap,
boundary-continuity or phase hypothesis is added. The proof identifies the
cycle-7 remainder a.e. with phase defect times the actual radial quotient,
derives its Littlewood envelope from interior norm monotonicity, then integrates
and pays the exact y=2t rescaling. Source:
`WeilWorkSettledPhaseCanonicalDisorder.lean`.

The targeted --old build and final standalone Lean audit passed without module
diagnostics. The module is wired once into the umbrella. All eight axiom checks
passed with exactly propext, Classical.choice and Quot.sound.
Global lint reports six unrelated unreachable modules and no WP05 error.

Verdict: BRIDGE, not significant scientific novelty or WP05 closure. This removes
atomicity and continuous-edge premises from the earlier quantitative phase
obstruction; it does not produce settlement. The next source conjecture is a
power-saving upper bound for mean-square phase differences within each dyadic
block. Its exact statement, elementary alignment transfer and unproved source
core are recorded in PROOF.md. No assertion of that conjecture was added to Lean.

## Source rigidity-or-disorder alternatives added in cycle 7

For each real theta, write kappa=exp(2*pi*i*theta). Use the actual radial
quotient Phi(t)=quantizationTraceF(2t), its reflected quotient Psi, and

    r(t)=1_{t<0}*(kappa^(-1)*Phi(t)-Psi(t)).

The original hW alone now yields either lambda(n)=vonMangoldt(n) for n>=2 and
RH, or delta*abelMass(r,delta) fails to tend to zero as delta decreases to zero.
The quantitative alternative gives eta>0 and arbitrarily large T with

    eta*T < integral_(T,2T] |r(-t)| dt.

This retains the actual canonical measure, without an atomic representation,
support gap, continuous critical-edge extension, extra coefficient bound or
phase-decay premise. Abel decay is an internal case split, not a source input.
The proof uses the refreshed corpus's actual radial Laplace identities, radial
residue comparison and coefficient uniqueness. Source:
`WeilWorkSettledPhaseAbelRigidity.lean`. Its targeted --old leaf build and final
standalone Lean audit passed, and it is wired once into the umbrella. All five
axiom inspections use exactly propext, Classical.choice and Quot.sound. Global
lint reports nine unrelated unreachable modules,
with no WP05 module named.

Verdict: BRIDGE. This removes source premises from the earlier coefficient
receiver and proves an actual-source weighted obstruction. It does not supply
WP05's unweighted phase upper bound or its exact atomic representation. The
next phase extraction is paper-closed; its Lean proof remains outstanding.

## Actual-source theta identities added in cycle 6

For the actual coefficients a=dirichletExp(lamLog lam), the original hW now
supplies the exact critical-trace inversion

    theta(r)-beta*r^(-1/2)*exp(-pi*r)
      = (1/(4*pi))*integral_R r^(-(1/2+iy)/2)*e(y) dy.

Restoring the polar part gives theta(r)=beta*r^(-1/2)+K_Phi(r). If
s(t)=1/2+2it and

    Phi(t)=b(2t)/(s(t)*(s(t)-1)*Gamma_R(s(t))),
    g(t)=(b(2t)-b(-2t))/(s(t)*(s(t)-1)*Gamma_R(s(t))),

the same source also gives

    theta(r)=r^(-1/2)*theta(1/r)-beta+beta*r^(-1/2)+K_g(r).

Here b retains the full canonical measure, including diffuse, central and low
mass. No atomicity, support gap, boundary continuity, extra coefficient bound,
or phase hypothesis is supplied. Source: `WeilWorkSettledPhaseThetaTrace.lean`.
The targeted leaf build and final standalone Lean audit passed without leaf
diagnostics. The module is wired once into the RHTower umbrella.
Twelve axiom inspections passed with exactly `propext`, `Classical.choice` and
`Quot.sound`. Global lint reports eight unrelated unreachable modules and no
WP05 error; evidence is retained in the cycle-6 audit files.

Verdict: BRIDGE. This supplies the actual-source theta identities required by
the existing coefficient argument. It does not yet compose that argument or
give a phase upper bound. Next use the already available measurable radial
representative and growth estimate, rather than duplicate its regularity proof.

## Actual-source contour shift added in cycle 5

The original full-positive source now supplies uniform quadratic decay for its
pole-subtracted completion E on `1/2<Re(s)<=3/2`, an integrable boundary trace e,
global L1 convergence to e, and for every r>0 the exact identity

    integral_R r^(-(3/2+it)/2) E(3/2+it) dt
      = integral_R r^(-(1/2+it)/2) e(t) dt.

No boundary continuity, atomic representation, support gap or phase-decay
hypothesis is added. Source: `WeilWorkSettledPhaseMellinTrace.lean`. Its targeted
leaf build, final standalone Lean audit and seven axiom inspections passed.
Audited declarations use only `propext`, `Classical.choice` and `Quot.sound`.
Global lint reports six unrelated unreachable modules and no WP05 error.

Verdict: BRIDGE. This removes the continuity premise from the actual source's
weighted contour shift. It does not yet prove coefficient rigidity for this
trace or produce the required phase upper bound. Gamma-weighted decay cannot be
substituted for a bound on the normalized phase defect.

## Canonical boundary trace added in cycle 4

From the original `hW : WeilPositiveFull lam` alone, the normalized completed
producer has an almost-everywhere boundary trace b and satisfies

    integral_R |G(1/2+x+iy)-b(y)| dy -> 0 as x decreases to 0,
    b(y) = exp(i*pi*mu((-y,y])) b(-y),  y>0.

Here mu is the original canonical boundary measure. Diffuse mass, low spectral
mass and the central atom remain present. No atomicity, support gap, boundary
continuity or phase-decay assumption is added. The modulus limit follows from
Herglotz positivity; canonical interval inversion supplies the phase, and the
existing right-edge Gamma decay makes the convergence global in L1.

New source: `WeilWorkSettledPhaseTrace.lean`. The targeted leaf build, final
`lake env lean` source audit and all nine axiom inspections passed. The audited
declarations use only `propext`, `Classical.choice` and `Quot.sound`. Global lint
reports 12 unrelated unreachable modules, with no WP05 error.
Verdict: BRIDGE, using classical boundary inversion. This removes the atomic
representation premise from the trace construction, but the critical-line
coefficient receiver still needs an extension to this measurable trace. Neither
that transfer nor phase settlement has been proved.

## Quantitative phase obstruction added in cycle 3

For an exact positive atomic representation of the original canonical boundary
measure, every fixed candidate phase theta satisfies this dichotomy: either
lambda=Lambda and RH, or there are a,K>0 and arbitrarily large Y such that

    integral_(Y,2Y] |exp(2 pi i S(y))-exp(2 pi i theta)| dy
      >= a Y exp(-K log Y/log log Y).

Here S is the actual strict-cutoff `phaseSum`. No phase-decay hypothesis is
assumed. The new coefficient-free source bound controls the producer's boundary
size; the existing weighted block receiver then gives the obstruction by
contraposition. The logarithmic scale strengthens the obstruction obtained by
contraposing each fixed-power receiver separately.

New module: `WeilWorkSettledPhaseDisorder.lean`. Exact representation, positive
masses, support at least one, local finiteness and weighted summability remain
explicit inputs. They are not produced by the theorem. This is an intermediate
obstruction, not an unconditional solution of the assigned problem, and no broad
scientific novelty is claimed. Verification details are in `EVIDENCE.md`.

## Source estimate added in cycle 2

`WeilWorkSettledPhaseLittlewood.lean` removes the extra coefficient hypothesis
from the corpus's Littlewood bound. For every original full-positive system,

    Re producerLogZeta(hW,sigma,t) <= C log|t| / log log|t|

uniformly for `1/2 < sigma <= 2` and sufficiently large `|t|`. Full positivity
is the only source premise. No atomicity, Euler product, pointwise coefficient
bound, or settled phase is assumed. The proof uses absolute summability at two
and a shorter cutoff in the existing Soundararajan inequality.

The targeted leaf build, final `lake env lean` source audit, and axiom audit passed.
Both new declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
This is a source-growth extension, not a proof of a phase
estimate. Its method is classical; significant scientific novelty is not claimed.
WP05's first phase milestone remains open.

## Audited contribution

Finite positive unit-mass packets have exact phase transport cost. With c=(1+cos q)/2 and atoms at l=1+|a| and r=l+|d|, strict cumulative count S satisfies

    integral_R |exp(2 pi i S(y))-1| dy = |exp(2 pi i c)-1| |d|.

For any finite family, integrated phase defect is at most the sum of these costs; overlapping packets and repeated ordinates are allowed. Half-mass packets attain cost 2|d| while their counting discrepancy from a unit atom at r is at most 1/2 everywhere. Consequently no uniform bound on integrated phase cost follows from that counting discrepancy alone.

New module: `formal/GaloisForLFunctions/RHTower/WeilWorkSettledPhasePackets.lean`. Main statements have no additional mathematical premises: parameters specify explicit spectra, with positivity and support bounds proved internally.

**Novelty assessment: BRIDGE.** This formalizes and sharpens the corpus's existing dipole mechanism; it is not claimed as significant new scientific knowledge, a new infinite spectral class, or a detector for the actual Weil measure. It does not complete WP05's first research milestone. A finite family varying with its width is not a counterexample to asymptotic settlement of one fixed full-positive system.

## Paid and unpaid

- Paid for explicit finite packets: positivity, ordinates at least one, exact strict-cutoff phase identity, finite-family integral bound, sharp single-packet example.
- Unpaid for canonical `boundaryMeasure hW`: atomicity, support restriction, exact atomic representation, source-derived power settlement.
- No theorem supplies existence of a full-positive system, equality with von Mangoldt, or RH.

## Active research conjecture

For the actual full canonical phase p, prove from hW that some epsilon>0 gives

    integral_(Y,2Y]^2 |p(u)-p(v)|^2 du dv = O(Y^(2-epsilon)).

The exact moving-line version uses
`p_eta(y)=exp(2i Im sourcePrimitive(1/2+eta+iy))` with eta=Y^-8.
Cycle 9's verified regularization changes this variance by O(1) on paper.
The arithmetic variance bound itself remains OPEN CORE.
Fixed-line reciprocal mean squares and the algebraic period-defect identity
do not supply it. The earlier arbitrary-o(T) fractional-mass question remains
open; its historical arguments are retained in PROOF.md.

This is the same constant-phase target, not a second AP project. No unproved
variance assertion has been added to Lean. Exact evidence and verification are
recorded in EVIDENCE.md; paper arguments and the remaining gap are in PROOF.md.

## Cycle15: ordinary forward sums

For every original full-positive source hW, set a=sourceCoeff lam and
B=sourceCompletion hW 1. For every epsilon>0 the new theorem proves

    |sum_(n=0..N) a(n) - B*N| <= C_epsilon*(N+1)^(1/2+epsilon).

No coefficient sign, arithmetic projection, spectral atomicity, phase decay
or residue normalization is added. In particular B=1 is not established.
This supplies the previously unverified ordinary principal-mode mean. The
centered coefficients also have ordinarily convergent Dirichlet series on
Re(s)>1/2. A companion theorem constructs the holomorphic pole-subtracted
forward function there and bounds it by every positive power of height on
each closed inner strip up to Re(s)=2.

Modules: `WeilWorkSettledPhaseForwardRegularPart.lean` and
`WeilWorkSettledPhaseForwardSummatory.lean`, imported once in RHTower.
Both targeted --old builds and mandatory direct source audits passed.
All three exports passed the axiom audit with only propext, Classical.choice
and Quot.sound. Detailed commands and source hashes are recorded in
`cycle15-verification.json`. Global lint reports nine unrelated unreachable
modules; no owned WP05 failure was reported.

Verdict: BRIDGE. The proof is a classical Perron argument using checked
source bounds; significant scientific novelty is not claimed. The central
phase estimate, atomic representation and support restriction remain open.
C16 now isolates a prime-deletion logarithmic residue law. Its current
fibre route still requires absolute deviation bounds not supplied by signed
summatory cancellation. No C16 assertion has been introduced as a Lean premise.

## Cycles22--24 research checkpoint

No additional Lean theorem or WP05 closure. C21's full logarithm moment and
C22's complete composite exponential moment remain unproved. The existing
Gamma-odd energy measures discrepancy from a variable Gamma phase; it cannot
be substituted for constant-phase defect. The exact corrected observable and
the remaining amplitude-weight gap are recorded in PROOF.md.

The next source conjecture is a uniformly bounded signed cubic correlation
sum over a,b>=2,ab<=N, with summand
lambda(a)lambda(b)lambda(ab)/(ab log(a)log(b)log(ab)). This retains every
composite term and isolates the first interaction missed by variance. Its
source bound and any implication to phase settlement remain unproved.

## Cycles25--26: direct cubic cost and parity refocus

WP05 remains OPEN; no new Lean theorem this cycle. The direct full-source
Toeplitz test gives the exact paper Schur bound B_N<=K_N*V_N-A_N^2/K_N for
the logarithmically weighted signed cubic. This is a BRIDGE from the parent,
not a demonstrated scientific advance. It gives no opposite sign bound.
The2026 multiplicative-Hilbert bounded-symbol result does not insert the
actual source weights or pay the sharp product cutoff.

C24 remains unproved and has no proved transfer to settlement. Research now
returns to C26, the conductor-two case of C11: square-root-with-epsilon
cancellation for the actual forward coefficients' alternating sums. Unlike
global Haar moment repackaging, this would pay a named arithmetic input:
C13 and the p=2 logarithmic prime-deletion residue law. Its source producer
is OPEN CORE; neither positivity of a filtered source nor an Euler factor
has been assumed. Exact statement and failed transfers are in PROOF.md.

## Cycle27: finite even logarithm and nonzero odd radial pole

For every original full-positive source hW, the actual even logarithm
L_2(sigma)=sum_(even n>=2) lambda(n)/(log(n)*n^sigma) has a finite real
right limit ell_2 and error O(sigma-1). Consequently, with a=sourceCoeff lam,

    L(oddPart a,sigma)/L(a,sigma) = exp(-L_2(sigma))
                              = r + O(sigma-1),  r=exp(-ell_2)>0.

Writing B=sourceCompletion hW 1, one also has B!=0 and the actual radial
expansion L(oddPart a,sigma)=r*B/(sigma-1)+O(1). All statements derive from
original hW; no parity limit, Euler factor, coefficient sign or deleted
continuation is added. The source input is the polynomial Gaussian/Mellin
inequality, applied at both signs to bound the even derivative series.

Six new Deletion* leaves are wired once into RHTower. Targeted --old builds
and all six mandatory lake env lean direct audits passed without owned
leaf warnings. Thirteen exports passed the axiom audit with only propext,
Classical.choice and Quot.sound. Index refreshed. Global lint failed on six
unrelated unreachable modules; no owned deletion leaf failed. Commands,
source hashes and exact diagnostics are in cycle27-verification.json.

Verdict: BRIDGE. This closes a source-existence gap; significant scientific
novelty is not claimed for the transfer. Neither r=1/2 nor ell_2=log2 is
proved. There is no deleted meromorphic continuation or ordinary parity
mean yet. The canonical atomic representation, support restriction and
constant-phase settlement remain OPEN. C28 now targets r=1/2 exactly.

## C30, part 1 — every fixed rational cosine twist is controlled

**FORMALIZED BRIDGE; WP05 OPEN.** Let d=lamC(lam)-Lambda and b=d*1*1.
From the original `WeilPositiveFull lam` alone, for every p>=0 and q>0 there
is C>=0 such that, eventually as sigma tends to 1 from above,

```text
|(sigma-1)^2 Re[Gamma_R(sigma) sum_n b(n) cos(2*pi*n*p/q)/n^sigma]| <= C.
```

The capstone is `exists_abs_sourceCosineSeries_rat_normalized_le` in
`WeilWorkSettledPhaseRationalBound.lean`; its Mellin form is
`exists_abs_sourceNormalizedCosineMellin_rat_le`. The proof uses the actual
finite arithmetic Gaussian quadratic, applies opposite two-label coefficients,
then combines reciprocal frequencies with periodicity and strong induction on
the denominator. Absolute Mellin convergence is proved independently from the
signed small-parameter bound. No filtered-source positivity, coefficient sign,
Euler product of the unknown source, or rational-twist regularity is assumed.

This extends the parity control to every fixed rational frequency. It does not
claim constants uniform in q, a limit of the rational twists, or their analytic
continuation. The finite Fourier/coprime-mask transfer to every finite deletion
endpoint is now proved in C30 part 2 below. Canonical endpoint normalization remains
open. Scientific novelty beyond the literature is not
established; the classification is BRIDGE.

Four targeted modules compile; all four final `lake env lean` audits are clean.
Ten axiom checks use only propext, Classical.choice, Quot.sound. All imports are
wired once; index passed. Repository lint fails on 15 unrelated unreachable
modules and reports no error in these four modules. Exact hashes and receipts:
`cycle30-verification.json`.

Corpus refresh also found an actual logarithmic forward energy/variance limit
with K=|B|^2+V and V>=0. The new source does not prove V=0. This is a stronger
starting point for the variance route, not closure of the settled-phase target.

## C30, part 2 — every finite prime deletion has a positive endpoint ratio

**FORMALIZED BRIDGE; WP05 OPEN.** For every nonzero natural Q and the original
hW alone, the literal excluded logarithm

```text
L_Q(sigma) = sum_(n>=2, not Coprime(n,Q)) lam(n)/(log(n)*n^sigma)
```

has a finite right limit ell_Q and satisfies
`|L_Q(sigma)-ell_Q| <= K_Q*(sigma-1)` on a right neighborhood of one.
`exists_sourceDeletedLogarithm_lipschitz_limit` in `CoprimeLogarithm.lean`
is the exact endpoint theorem; `sourceDeletedLogarithm_eq_tsum` identifies the
literal convergent series. The modulus is arbitrary, not restricted to a prime.

For a(n)=sourceCoeff(lam,n), the actual coprime/full forward ratio is exactly
`exp(-L_Q(sigma))` on sigma>1. It tends to the positive real number
`r_Q=exp(-ell_Q)` with an O_Q(sigma-1) error. Capstones:
`coprime_source_ratio_eq` and `exists_coprime_source_ratio_limit` in
`WeilWorkSettledPhaseCoprimeRatio.lean`.

Proof: exact finite real cosine expansion of the coprime mask; C30 rational
bounds; mask compatibility with convolution; positive principal-character
residue of the canonical constant-sequence factor; subtraction from the full
source deviation; restoration of excluded Mangoldt terms; bounded-derivative
extension and the actual Dirichlet exponential. No additional source premise,
coefficient sign, filtered-source positivity, or unknown-source Euler product.

This does not identify r_Q with the canonical coprime density, provide uniform
constants in Q, establish deleted analytic continuation/ordinary means, or force
zero forward variance. Scientific novelty beyond literature remains unestablished.

All eight part2 modules compile and pass final direct `lake env lean` audits with
empty diagnostics. Fourteen capstone axiom queries use only propext,
Classical.choice, Quot.sound. Imports are wired exactly once; index passes.
Latest repository lint has eight unrelated unreachable-module errors and no C30
error. Receipt: `cycle30-coprime-verification.json`. Together with part1 this seals
12 modules and24 capstone axiom checks. C31 attacks residual variance V=0.


## Cycle 33: exact positive valuation logarithms

**BRIDGE; scientific novelty unestablished; WP05 OPEN.** All eight new modules
compile and pass their final direct source audits. All16 capstone axiom queries
passed with only propext, Classical.choice, and Quot.sound. Every module is wired
once. The verification receipt is `cycle33-verification.json`. Global lint has9
unrelated unreachable-module errors and no C33 error. No full build was run.

For every prime p and every k>=1, original `WeilPositiveFull lam` implies that

L_(p,k)(sigma) = sum_(n>=2, p^k|n, p^(k+1) does not divide n)
                   lam(n)/(log(n)*n^sigma)

has a finite right limit ell_(p,k) at1, with an O_(p,k)(sigma-1) remainder.
The series identity is on sigma>1; convergence of the literal series at1 is
not claimed. Endpoint values and constants are not made uniform in p or k.

The new mechanism is an exact finite local difference. If b=(lamC-Lambda)*1*1,
u=1_(p does not divide n), and delta_p is the Dirichlet point mass, then
(1-delta_p)^2*b=(lamC-Lambda)*u*u. Exact valuation projection commutes with the
coprime factors and shifts by one under delta_p convolution. The previously
proved rational cosine estimates bound each projected b. The coprime square's
positive normalized residue then bounds the projected logarithmic derivative.
Restoring the absolutely summable canonical contribution and integrating gives
the endpoint with linear error. No Euler product, sign, positivity, or analytic
continuation is assumed for the restricted unknown source.

The result distinguishes valuation depths that every coprime deletion combines.
It does not determine their constants or imply zero forward variance. C31 remains
open. C32's polynomial diagnostic is now sealed below and is not represented
as a full-positive source example.

## Cycle 32: coprime endpoints miss local polynomial variance

**REDISCOVERED classical model classification; positive survivor formalized;
WP05 OPEN.** Four modules pass final direct Lean audits, eight axiom queries
use only standard axioms, and every module is wired once. Index passes; lint
reports five unrelated unreachable HTGeometry modules. Hashed receipt:
`cycle32-verification.json`. No full or umbrella build.

For any integer p>1, let P be a real polynomial with P(0)=P(1/p)=1, and set
a(n)=sum_j P.coeff(j)*1_(p^j|n) for positive n. Its actual Dirichlet series is
zeta(s)*sum_j P.coeff(j)*(p^j)^(-s). Every coprime/full ratio tends to phi(Q)/Q.
The period average of |a(n)-1|^2 is nevertheless strictly positive whenever
P is nonconstant. The same coefficient sequence is used in both assertions.
An explicit family exists: P=1+X*(X-C(1/p)). The capstone is
`exists_localModel_coprime_invisible_variance` in
`WeilWorkSettledPhaseLocalPolynomialInvisibility.lean`.

The exact positive classification is also audited: the invisible polynomials
are precisely 1+X*(X-C(1/p))*R; the finite period variance has explicit positive
geometric valuation weights and vanishes exactly for P=1. This establishes why
coprime endpoint normalization alone loses information needed for variance
rigidity. It is not an example satisfying WeilPositiveFull, and no infinite
ordinary/logarithmic variance limit is asserted by this diagnostic.

## Cycle 34: uniform sparse source bound with sharp energy constant

**BRIDGE; scientific novelty unestablished; WP05 OPEN.** Both modules pass
final direct Lean audits, six axiom queries use only standard axioms, and
imports occur once. Index passes; lint has five unrelated HTGeometry errors.
Receipt: `cycle34-verification.json`. All owned scratch files cleaned.

For the actual source a=sourceCoeff(lam), its proved critical log-energy
constant K satisfies: for every e>0, eventually as sigma decreases to1,
SIMULTANEOUSLY for every integer q>=1,

  |(sigma-1)*LSeries(1_(q|n)*a(n),sigma)|^2 <= (K+e)/q.

The neighborhood is independent of q, and no masked radial residue is assumed
to exist. In particular one common C and eta control all q on 1<sigma<1+eta.
Capstones: `exists_forward_uniform_divisibility_energy` and
`exists_forward_divisibility_near_one` in
`WeilWorkSettledPhaseUniformDivisibility.lean`.

The proof retains the exact mask square mass q^(-sigma)*zeta(sigma), including
the zero-index convention, combines weighted Cauchy--Schwarz with the source
Abel majorant, then chooses one neighborhood using the canonical zeta residue.
Prime powers give uniform deep-valuation tail control. This does not supply
canonical local endpoint values, source coefficient signs, finite-divisibility
approximation in square mean, or zero variance.

## Cycle 35: coprime covariance and prime-deletion square summability

**SEALED BRIDGE; scientific novelty unestablished; WP05 OPEN.** All five
new modules pass final direct `lake env lean` audits. All 22 public theorem
axiom queries use only propext, Classical.choice, Quot.sound. Imports occur
exactly once. Receipt: `cycle35-verification.json`. Global lint reports eight
unrelated unreachable modules; no C35 module is named. No umbrella/full build.

For the actual full-positive source a, B=sourceCompletion(1), and its existing
centered logarithmic variance V, one simultaneous family of positive coprime
residues r_Q satisfies the full finite covariance inequality with kernel
phi(QR)/(QR)-phi(Q)/Q*phi(R)/R. At primes this gives

  |B|^2 * sum_p [p^2/(p-1)] * (r_p-(1-1/p))^2 <= V,

where the nonnegative series is proved summable, not merely formally bounded.
The capstone is `exists_forward_prime_deletion_summable` in
`WeilWorkSettledPhasePrimeDeletionSummability.lean`. This is a standard
covariance/Bessel argument applied to the actual source, without extra source
assumptions. It does not force canonical residues, zero variance, or settled
phase. Finite-divisibility square-mean approximation remains an open conjecture.

Cycle 36 corrects two route assessments: finite-prime-support rigidity is
already proved in `WeilFiniteSupportRigidity`; V=0 alone has no audited
receiver proving phase settlement. Neither statement may be silently assumed
when attempting to close WP05. The actual phase/residual-measure producer
remains the main unpaid obligation.

## Cycle 40: every prime-valuation forward ratio has a real endpoint

**SEALED BRIDGE; scientific novelty unestablished; WP05 OPEN.** All five new
modules pass final direct `lake env lean` source audits with empty logs.
All18 public theorem axiom reports contain only propext, Classical.choice and
Quot.sound. Imports occur once; index passes. Global lint reports7 unrelated
unreachable modules, with no C40 finding. Receipt: `cycle40-verification.json`.
Fourteen owned scratch files were cleaned; development diagnostics archived.

For the original full-positive source a=sourceCoeff(lam), each prime p has a
positive coprime ratio endpoint r_p and a real sequence ell with ell_0=0 such
that, simultaneously for every k>=0,

  LSeries(1_(v_p(n)=k)*a(n),sigma)/LSeries(a,sigma)
    -> r_p * [z^k] exp(sum_(j>=1) ell_j*z^j),  as sigma decreases to1.

Here ell_j for j>=1 is the already proved actual valuation-logarithm endpoint,
and coefficient extraction is a finite polynomial. The capstone is
`exists_forward_valuation_endpoints` in
`WeilWorkSettledPhaseValuationEndpoints.lean`. Its only source premise is the
original `WeilPositiveFull lam`; primeness specifies the arithmetic parameter.

The proof splits the source convolution exponential into its coprime part and
the exponential supported on p-multiples. Depth k truncates the latter to powers
0 through k; finite valuation convolution and C33 then supply its endpoint.
C30 supplies the coprime factor. No infinite depth limit exchange, source
multiplicativity, coefficient sign, or new analytic assumption is used.

This produces valuation information missing from coprime deletion alone. It
does not identify canonical endpoint values, prove positivity at positive
depths, remove diffuse/fractional spectral mass, or settle phase. The polynomial
algebra is classical; no independent scientific novelty is claimed.

## Cycle 46: logarithmic regularization of the full source phase

**SEALED BRIDGE; scientific novelty unestablished; WP05 OPEN.** Three final
direct source audits have empty logs. All14 public theorem axiom queries use
only propext, Classical.choice, Quot.sound. Both new modules are wired once;
source hashes match the audited receipt. Index passes. Global lint reports
seven unrelated unreachable modules, no C46 finding. No full/umbrella build.
Receipt: `cycle46-verification.json`; owned scratch cleaned.

For original hW alone, there exists C>=0 such that for every Y>=4 and
0<eta<=1,

  integral_[Y,2Y] |regularizedPhase_eta-canonicalPhase|
    <= C eta Y log(Y+3) log(1+6Y/eta).

Capstone: `exists_integral_regularizedPhase_sub_le_log` in
`WeilWorkSettledPhaseLogRegularization.lean`. The proof retains all atomic and
diffuse mass, integrates an endpoint envelope against the scale-Y Poisson
weight, and invokes the existing source real-axis logarithmic bound.
No new coefficient, representation, regularity, or sign assumption is used.

For every fixed epsilon>0, eta=Y^(-epsilon) gives a relative power saving
(paper consequence; no separate Lean power-width corollary). This improves
boundary approximation, not phase concentration. The existing interior
cancellation estimate remains ineffective in this small-width range.
The Poisson smoothing mechanism is classical.

## Cycle55 — actual local valuation functions are zero-free (8 October2026)

**SEALED SOURCE BRIDGE; WP05 remains OPEN.** For every original
`hW : WeilPositiveFull lam` and every prime p, the actual normalized valuation
endpoints u_k form a real signed series U_p(z)=sum_k u_k z^k. It is holomorphic
and nonzero on |z|<sqrt(p), U_p(0)>0, and U_p(1)=1. The actual ratio series
converge uniformly on every smaller closed disk; the endpoints are absolutely
summable. No source multiplicativity, coefficient positivity, atomicity,
phase settlement, or extra source energy premise is assumed.

Capstone: `RHTower.WeilSingularArithmetic.exists_forward_valuation_zero_free`,
`formal/GaloisForLFunctions/RHTower/WeilWorkSettledPhaseValuationZeroFree.lean`.
The proof combines C34 uniform divisibility control, C40 endpoint production,
exact twisting of the convolution exponential, logarithmic square summability,
absolute regrouping, and local Hurwitz. It does not use entire continuation.

Ten leaf modules built with `lake --old build +<module>:olean`; all ten passed
final `lake env lean <source>` checks with empty logs. All34 public declarations
use only propext/Classical.choice/Quot.sound. Every leaf is wired once; no full
or umbrella build. Index passed. Global lint reports six unrelated unreachable
modules, listed in `cycle55-verification.json`; none is a C55 source.

Scientific verdict remains **BRIDGE**: actual source constraints strengthened,
independent novelty beyond literature unestablished. Signed coefficients may
still be negative. One-prime nonvanishing gives neither independence across
primes nor the required global settled phase. C56 prime endpoint independence
and C57 sharp critical mean square remain open; neither has a paper proof.
