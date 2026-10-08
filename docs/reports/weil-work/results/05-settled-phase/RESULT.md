# WP05 result

**Verdict: OPEN.** Assigned canonical-measure settlement problem remains unsolved.

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
