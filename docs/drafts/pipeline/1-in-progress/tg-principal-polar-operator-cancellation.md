# TG C9.11p — canonical principal prime–polar operator cancellation

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / hard source-construction target
- **Route:** TG, joint prime–Gamma relative admission
- **Predecessor:** ../3-formalized/tg-principal-source-trace-current.md (C9.11n–o)
- **Status:** exact complex-response recovery and native signed-energy operator formalized; cofinal prime–polar tail control unproved

## Hard target

Construct and prove cofinal convergence or meromorphic continuation of the
original signed prime–polar correction response on its actual operator carrier.
Retain both dilation directions and both correction legs. A scalar trace
remainder placed on a chosen probe does not solve this target. After this,
Gamma completion, source-to-Hardy cubic compatibility and the strict sub-unit
law still have to be established before RH follows.

## Corpus-grounded candidate

`CCMPolarPrimeStieltjesAutocorrelation.criticalMellinAtomWeight` is
`Λ(n) n^(-1/2)`. `CCMFirstClockPrimePowerTowerCollapse` proves its exact
prime-power form. Dividing by the nonzero log position gives the original
logarithmic coefficient `1/(k sqrt(p^k))`. The k≥2 response family is already
summable in genuine Schatten-one.

`CCMGuinandWeilLiteralPolarPrimeSource.ccmGuinandWeilPoleSourceFunctional`
has literal density `2 cosh(u/2) du`. Therefore the corresponding logarithmic
polar tail has density `2 cosh(u/2)/u`, away from u=0. This normalization must
be carried through the same physical symmetric dilation observable; no
coefficient may be fitted using a desired trace value.

For a fixed positive aperture a, test the cofinal family

`H_R = Σ_{p≤exp R} p^(-1/2) C_a(D_p+D_(1/p))`

`      − ∫_(log 2)^R (2 cosh(u/2)/u) C_a(D_(exp u)+D_(exp(-u))) du`.

First construct the integral in genuine Schatten-one from the actual
trace-class J and strong dilation continuity. Then derive the signed kernel
and decide whether H_R is Cauchy in trace norm. Restoring proper powers is
already justified. The lower-end Gamma/pole normalization and the complete
meromorphic source transport remain separate required proofs; the displayed
family is only the cofinal polar-tail candidate.

## What the preceding obstruction teaches

The original raw prime response has `p Re Tr S_p → K_a>0`, where
`K_a=2(Phi_a(1)+1)` and Phi is the actual central double Fourier window.
Thus raw trace-norm admission fails. This fixes a necessary scalar
cancellation datum, but does not prove signed operator convergence.

The same exact real-scale trace formula suggests the polar integrand has
leading term `K_a/u`. This is a paper diagnostic for the native density,
not an audited operator cancellation or a substitute for it.

## Current attack and failed estimate

Keep `J=AB(1-AW)+BAW` and both terms in
`C_a(D)=(1-Q)DJ-JDQ0`. Reduce the signed source acting on each actual
Fourier Taylor output `soninCutoffMonomial a n`; then reassemble the genuine
nuclear expansion if a uniform signed tail is proved.

The corpus gives the exact AE cutoff monomial and normalized dilation
formulas. In the contracting direction, multiplying D_p by p^(-1/2)
cancels its square-root normalization. At nonzero x the finite prime head
therefore has the literal form

`x^n Σ_{p≤min(exp R,a/|x|)} p^n`.

Changing variables r=exp u in the proposed polar term gives, on the same
support, the continuum contribution

`x^n ∫_2^min(exp R,a/|x|) (r^n+r^(n-1))/log r dr`,

with the integral interpreted as zero when the support upper bound is below 2.
These pointwise formulas still require AE/Bochner Lean verification, and the
expanding direction plus the full response must be retained. They expose
actual signed arithmetic error rather than an absolute coefficient majorant.

Separate prime and pole estimates fail: both contain the harmonic trace
current. The existing `CCMPrimeGammaQuantileCancellation` theorem gives only
`o(e^a)` relative to physical mass plus higher Gamma energy, not Schatten-one
Cauchy control. No critical-scale error estimate is assumed. The next hard
step is a signed nuclear-tail law from these actual kernels; if it fails,
extract its precise operator obstruction and strongest positive survivor.

## Evidence and process

2026-10-02: relevant searches in `/tmp/tg-c911o-{gamma-source,continuum,polar}-search.json`.
Partial results, background refresh incomplete; source/compiler freshness
reported and candidate/source statements inspected. Read the actual definitions
and the cutoff-monomial dilation proof. No computation, axioms, conditional
admission theorem, or scalar-probe repair introduced.

## C9.11p.1 — exact recovery conjecture before signed completion

Current source searches (`/tmp/tg-c911p-*-search.json`) were partial with
snapshot coverage and incomplete background refresh. Their candidate/source
statements were inspected. The corpus already isolates `C(D)Q=-JDQ` and
proves the active-space conservation law and compactness of J.

New paper conjecture: the complete response admits a bounded real-linear
recovery of DJ for every self-adjoint D. Put F=1-Q. Since QJ=JQ=0,

`C(D)F=(F+J)DJ=(1+J)F DJ`,   `(C(D)Q)*=-QDJ`.

The operator `1+J=Q+A+B` is injective: its quadratic form is the sum of
squared norms of the three orthogonal projections. Its kernel would lie in
A-perp and B-perp, hence in Q, and also in ker Q. Since J is compact,
Fredholm alternative makes `1+J` boundedly invertible. Consequently

`DJ=(1+J)^(-1) C(D) F − (C(D)Q)*`.

The forward reconstruction is also exact: `C(D)=F(DJ)−(DJ)*Q0`.
Both are bounded maps in genuine Schatten-one, so the actual complete
response cannot acquire trace-norm cancellation that is absent from DJ.
This is a source recovery law, not an assumed cofinal convergence or an
optimized norm constant. Formalize it, then use it to attack the signed
prime–polar source on the explicit correction right factors. The compact
inverse and exact recovery are being checked; no Lean claim yet.

The reconstruction forces a stronger paper statement. The already proved
`J²+J=AB+BA` gives `J=(AB+BA)(1+J)^(-1)`. Hence DJ and the literal two-leg
source D(AB+BA) are related by bounded right multiplication in both directions.
Combining this with response recovery proves exact equivalence of trace-norm
summability and cofinal limit admission for C(D), DJ and D(AB+BA), for arbitrary
self-adjoint source families. The inverse and real-linear trace-norm maps are
now in Lean scratch; this directly removes the hidden possibility that response
compression alone could repair a divergent prime–polar time-band source.

### Complex-source strengthening

The self-adjoint recovery and all its trace-norm maps passed scratch Lean.
For the eventual complex contour family, self-adjointness cannot be imposed.
The stronger exact identity is

`DJ=(1+J)^(-1) C(D)F − (C(D*)Q)*`.

Thus the genuine object is the pair `(C(D),C(D*))`, with bounded real-linear
recovery of `(DJ,D*J)` and a bounded forward map in the opposite direction.
The same right inverse identifies this with `(D(AB+BA),D*(AB+BA))`.
Both summability and existence of arbitrary-filter trace-norm limits are
therefore equivalent, without any self-adjointness or convergence premise.
The strengthened pair, rather than only the self-adjoint case, is now being
Lean-audited. This preserves the complex source needed for Hardy contours.

### Verified checkpoint, 2026-10-02

The strengthened result is now fully formalized in
`SoninCorrectionResponseRecovery.lean`: final foreground `lake --old env lean`
audit passes with empty diagnostics; all sixteen public axiom queries use only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella import is wired. Formal
lint reports eleven unrelated unwired leaves, with no finding in this leaf.
The complete paper proof and audit are in P3
`tg-complete-response-source-recovery.md`.

Contribution to the hard problem: response compression cannot create missing
trace-norm cancellation. The precise remaining object is the full signed
time-band pair, with no self-adjointness premise even for complex contours.
This closes source recovery, not prime–polar admission. The next attack is
the native signed dilation kernel and its arithmetic tail; no critical-scale
prime-error bound or cofinal convergence will be assumed.

## C9.11p.2 — full signed dilation energy (paper derivation; energy part formalized below)

Two further deep searches finished: `/tmp/tg-c911p-signed-mellin-search.json`
and `/tmp/tg-c911q-dilation-continuity-search.json`. Both report non-partial
retrieval, snapshot coverage and incomplete background refresh. Candidate
lemmas and source arguments were inspected. The search exposes existing
prime–polar error-flux identities, but no verified tail bound applicable to
this operator. `SoninDilationContinuity` supplies strong continuity on full
SoninL2; there is no need to restrict the polar integral to the even carrier.

The exact overlap in `SoninCutoffMonomialDilation` forces a new signed energy
law. Let `f_n=soninCutoffMonomial a n`, `a>0`, and `lambda=n+1/2`.
On logarithmic scales the existing ordered overlap, conjugate symmetry and
the dilation group law give

`<D_exp(u) f_n,D_exp(v) f_n> = ‖f_n‖² exp(-lambda |u-v|)`.

For `u,v>=0`, the mixed overlap is

`<D_exp(u) f_n,D_exp(-v) f_n> = ‖f_n‖² exp(-lambda(u+v))`.

Take any finite complex measure nu with compact support in the positive
logarithmic ray. Define the two strong integrals

`V_+ = ∫ D_exp(u) f_n dnu(u)`, `V_- = ∫ D_exp(-u) f_n dnu(u)`.

These are paper notation for integration against total variation with its
complex density; actual prime–polar specialization can instead use a finite
atomic sum minus a finite Bochner integral. Strong continuity and compact
support give integrability; the bounded overlap kernel permits Fubini.
The same-direction kernel is unchanged by simultaneous reflection, so
`‖V_-‖²=‖V_+‖²`. The mixed kernel factors exactly, giving

`<V_+,V_-> = ‖f_n‖² |∫ exp(-lambda u) dnu(u)|²`.

Consequently the **complete two-direction energy**, with all cross terms, is

`‖V_++V_-‖² = 2‖V_+‖² + 2‖f_n‖² |∫ exp(-lambda u) dnu(u)|²`.

The mixed term is nonnegative even for complex signed coefficients. Thus
opposite dilation directions cannot cancel an unbounded one-leg energy on
these actual Taylor outputs. This is a full source energy identity, not an
absolute-value majorant or an assumed decorrelation law.

### Literal prime–polar specialization

For `t>=2` and real q, use positive real powers and define

`E_q(t) = Σ_(p<=t) p^q − ∫_2^t (r^q+r^(q-1))/log(r) dr`.

Let `K_R` denote the bounded finite signed dilation source **before** C is
applied, so the response above is `H_R=C(K_R)`, with the same prime
coefficients and native polar density.
For `X=exp R`, `Y=exp S`, `log 2<=S<=R`, its increment on f_n has exact paper
energy

`‖(K_R−K_S)f_n‖² = 4 a^(2n+1) [`

`  ∫_Y^X |E_n(t)−E_n(Y)|² / t^(2n+2) dt`

`  + |E_n(X)−E_n(Y)|² / ((2n+1) X^(2n+1))`

`  + |E_(-n-1)(X)−E_(-n-1)(Y)|² / (2n+1) ]`.

Derivation: the contracting increment is zero for `|x|>a/Y`, and otherwise
equals `x^n (E_n(min(X,a/|x|))−E_n(Y))`, up to null endpoints. Substitute
`t=a/|x|` in its squared L2 norm, retaining the constant tail for `t>=X`.
Its elementary integral contributes the displayed boundary term. The mixed
moment is exactly the difference of E_(-n-1), because multiplying the native
density by exp(-(n+1/2)u) and setting r=exp u gives
`(r^(-n-1)+r^(-n-2))/log r`. Finally
`‖f_n‖²=2a^(2n+1)/(2n+1)` gives the coefficient above.

**Status:** the full signed-energy law and bounded source construction are
now formalized in C9.11q below. The displayed E_q coordinate formula remains
a dependency-closed paper calculation; its AE substitutions and exact
arithmetic integral identity still need Lean verification.
No decay or convergence of E_q is asserted. The next hard proof must control
the displayed positive signed-error integral, boundary term and mixed moment
with enough degree control to reassemble the actual time-band source. Merely
renaming this as a convergence premise would not advance the frontier.

## C9.11q — signed energy implementation and degree transfer

The signed-energy deep search `/tmp/tg-c911q-signed-energy-search.json`
finished non-partial, with snapshot coverage and incomplete background
refresh. Candidate lemmas and source arguments were checked. The existing
ordered monomial overlap supplies the exact covariance kernel; it does not
by itself prove signed-tail control.

The implementation first treats a complex L1 weight against a positive
measure, then represents the literal finite prime–polar source using the
sum of its prime Dirac measures and its continuum interval measure.
The weight is the original inverse square root at each prime atom and the
negative native polar density almost everywhere for the continuum. Finite
prime support has zero Lebesgue measure, so neither contribution is changed.
Strong continuity on full SoninL2 proves all required integrability. A bounded
operator is constructed from the same strong continuum integral; no even-only
restriction or source-convergence premise is used.

Verified checkpoint: `SoninPrimePolarSignedEnergy.lean` passes its final
foreground `lake --old env lean` leaf audit with empty diagnostics. All
thirteen public axiom queries use only `propext`, `Classical.choice`,
`Quot.sound`. The leaf is wired. Formal lint reports twelve unrelated unwired
leaves and no finding in this module. Full proof and audit:
P3 `tg-prime-polar-signed-energy.md`.

This turn closes the original finite operator construction and exact positive
mixed energy, including the literal continuum. It does not close cofinal
admission: the signed arithmetic tail still needs proof. The next attack
retains the E_q formula and the exact degree-transfer law below. The additional
Lp-integral search `/tmp/tg-c911q-lp-integral-search.json` was partial, with
snapshot coverage and incomplete background refresh; candidate/source
arguments were inspected. One alternative to pointwise L2 evaluation is to
factor the verified covariance kernel into its cumulative exponential feature
and apply scalar Fubini, preserving the exact arithmetic error energy.

### New degree-transfer conjecture: exact dissipative resolvent law

The second current search `/tmp/tg-c911q-resolvent-energy-search.json` is
non-partial with snapshot coverage and incomplete background refresh.
Its source arguments include the actual dilation group law and Mellin
unitary intertwining. No returned theorem has yet been verified as providing
the following exact degree transfer.

Put `U_t=D_exp(t)`, `lambda_n=n+1/2`, and construct on full SoninL2

`R_n f = ∫_0^∞ exp(-lambda_n t) U_t f dt`, `T_n=1−n R_n`.

Unitary group covariance and an absolutely convergent double integral give

`R_n+R_n*=2 lambda_n R_n*R_n`,

hence the exact identity

`T_n*T_n + n(n+1) R_n*R_n = 1`.

This is more than a degree-wise estimate: every lost norm has an explicit
positive resolvent energy. For `f_0=1_[-a,a]`, direct integration over
`0<=t<=log(a/|x|)` gives

`T_n f_0(x)=(|x|/a)^n 1_[-a,a](x)`.

Let `S_n` multiply by `sign(x)^n`; it is an L2 isometry and commutes with all
positive dilations. Thus `f_n=a^n S_n T_n f_0`. Every finite or integrable
signed dilation source K commutes with these operators. Therefore the
proposed exact transfer is

`‖K f_n‖² + a^(2n) n(n+1) ‖R_n K f_0‖² = a^(2n) ‖K f_0‖²`.

This includes both dilation directions and complex signed source weights.
If formalized, it would remove the separate uniform-degree obstacle in the
time-band nuclear expansion: all Taylor outputs are controlled by one
actual ground-source vector. It does not bound that ground vector or prove
prime–polar convergence. The latter still requires a proof of decay for its
positive signed arithmetic error energy. Status: paper derivation; operator
construction, double-integral identity, parity transport and Lean audit pending.

## C9.11r — whole-ray resolvent energy attack

The current deep search `/tmp/tg-c911r-unitary-resolvent-search.json` is
non-partial with snapshot coverage and incomplete background refresh.
Candidate/source arguments were inspected. The corpus supplies full Sonin
strong continuity and group covariance, as well as a separate causal Hardy
Laplace construction. The latter does not identify the required full physical
operator, so the literal Sonin integral is being constructed directly.

An exact translated-tail proof avoids imposing a generator-domain premise.
For `g(t)=exp(-lambda t)U_t f`, its tail obeys

`exp(-lambda h) U_h R_lambda f = ∫_h^∞ g(t)dt`

`                              = R_lambda f − ∫_0^h g(t)dt`.

Both tails are integrable for every real h. The fundamental theorem of
calculus differentiates the right side at zero with derivative −f. The
squared norm of the left side is exactly
`exp(-2 lambda h)‖R_lambda f‖²`, by unitarity. Uniqueness of this derivative
then yields `Re<R_lambda f,f>=lambda‖R_lambda f‖²`, hence the proposed
resolvent energy law. This keeps the initial boundary term and uses no
smoothness assumption on f. Construction and tail translation are in scratch
Lean; degree transport and the arithmetic tail remain required afterward.

C9.11r identification mechanism (paper, being formalized): let
`g_n=1_[−a,a]|x|^n`, `N=2a`, `lambda=n+1/2`. Direct cutoff overlap gives

`<U_t f_0,g_m> = (2a^(m+1)/(m+1)) exp(-(m+1/2)t)` for `t>=0`,

hence

`<R_lambda f_0,g_m> = 2a^(m+1)/((m+1)(lambda+m+1/2))`.

The exact resolvent energy gives
`‖R_lambda f_0‖²=4a/((n+1)(2n+1))`. Consequently
`‖T_n f_0‖²=2a/(2n+1)` and
`<T_n f_0,g_n>=2a^(n+1)/(2n+1)`.
Since `‖g_n‖²=2a^(2n+1)/(2n+1)`, expansion of the squared difference
proves `a^n T_n f_0=g_n` for every n, including n=0. Multiplication by
`sign(x)^n` (with any modulus-one choice at zero) is isometric and commutes
with positive dilations, giving the required actual signed monomial.
This avoids unsupported point evaluation of a Bochner integral in L².
The exact energy identity is checked in scratch; the production leaf audit
is running. Absolute-monomial inner products and source transport are still
under construction. No arithmetic decay or RH conclusion has been obtained.

Intended frontier consequence, not yet claimed in Lean: the exact transfer law
for `K=K_R−K_S` should remove degree-uniform Taylor control as an independent
admission hypothesis. The physical time-band Taylor term has output `f_n`;
therefore its nuclear source tail is controlled by the same `K f_0` through
an absolutely summable operator series. For the symmetric physical source,
Fourier conjugation exchanges the two dilation directions, so the Fourier
channel must be transported as well. After the existing response recovery,
this should factor native full-response S1 admission through an actual single
ground-column L2 tail. Establishing that ground arithmetic tail is still the
hard unresolved step; no generic contraction or scalar trace limit settles it.

C9.11s paper proof and corpus audit: the source-direction and genuine nuclear
assembly arguments in `SoninTimeBandTaylorSourceDirection` and
`SoninPrimeSquareTimeBandNuclear`, together with
`summable_succ_mul_norm_fullTimeBandFourierTaylorTerm`, give the correct
completion mechanism. The corpus search `Taylor rank one source Schatten
nuclear convergence weighted sum output monomial` completed non-partially
(snapshot coverage; background refresh incomplete); candidate lemmas and
source arguments were inspected. No abstract trace reporter substitutes for
Schatten-one convergence.

For positive a, exact cutoff mass and C9.11r yield

`a^n‖f_0‖ <= (n+1)‖f_n‖`,

`‖K f_n‖ <= (n+1)‖K f_0‖‖f_n‖/‖f_0‖`.

Each actual Fourier Taylor term A_n has range in span(f_n), hence
`‖K A_n‖ <= (‖K f_0‖/‖f_0‖)(n+1)‖A_n‖`. The latter is summable. Every
K A_n has rank at most one, so its operator norm equals its genuine trace
norm. Sum these terms in the complete Schatten-one Banach space and compare
their continuous operator image with the already known actual Fourier Taylor
sum. Uniqueness identifies the sum as the original K times the time-band
operator. This proves a native nuclear tail estimate with a fixed constant
independent of P,Q,R,S. It does not assume arithmetic Cauchy convergence.
The Fourier-channel transport and complete-response reconstruction must still
be made explicit. C9.11s is drafted in scratch Lean, not yet checked.

C9.11r production status: `SoninDilationResolventEnergy.lean` and
`SoninPrimePolarGroundTransfer.lean` both passed foreground final audits using
`lake --old env lean <leaf> -o <olean>`, with empty diagnostics. Both are wired
into RHTower. The native source's generic full-vector application theorem was
added to `SoninPrimePolarSignedEnergy.lean`; that leaf also passed its final
audit. C9.11r now proves the exact all-degree energy identities for both signed
and symmetric native tail differences. Public axiom audit and generated-index
refresh remain to be completed together with the active C9.11s nuclear leaf.
C9.11s scratch `/tmp/tg-c911r-nuclear.lean` is currently checking; no production
nuclear leaf has yet been created. The live arithmetic search is
`/tmp/tg-c911r-arithmetic-ground-search.json`; inspect results before proposing
the next arithmetic conjecture. The RH goal remains active and unmet.

Arithmetic search checkpoint: `prime counting logarithmic integral error
weighted square integrable critical ground source cancellation` returned
partial results (pending coverage; background refresh incomplete; malformed
local-model filter result and retrieval deadline). Available candidates and
source arguments were inspected. `Sieve.primeCounting_sub_logIntegral_isBigO`
supplies a subexponential PNT error, not the needed critical weighted L² tail.
`CCMPrimeDeficitChronologicalWork` was read: its exact storage balance proves
only a lower bound for signed chronological work. The upper signed-work term
is explicitly retained. Therefore no reversal of storage positivity is
available for ground-tail admission. This is evidence about retrieved
results, not a claim that the corpus contains no stronger arithmetic theorem.

For the actual TG ground source and canonical prime cutoff, the direct
physical formula is
`K^+_[Y,X] f_0(x) = E_0(min(X,a/|x|))−E_0(Y)` on `0<|x|<=a/Y`, zero outside.
Its expected squared norm is
`2a ( ∫_Y^X (E_0(t)−E_0(Y))²/t² dt + (E_0(X)−E_0(Y))²/X )`.
The endpoint term is retained; weighted integral finiteness alone must not
silently erase it. This exact coordinate identification is still paper-only.
Next hard arithmetic target is native signed cancellation in this full
positive energy, rather than an estimate of absolute prime coefficients or
a reversed chronological-work inequality.


C9.11r–s closed, 2026-10-02: all four affected leaves pass final foreground
`lake --old env lean <leaf> -o <olean>` audits with empty diagnostics.
All 32 public declarations were audited in `/tmp/tg-c911r-axioms.lean`;
exit 0, only `propext`, `Classical.choice`, `Quot.sound`.
All three new modules are wired; generated indexes refreshed; all 32 names
are present in LEAN_API. Global lint has twelve unrelated unwired modules,
no finding in these four leaves. P3 `tg-prime-polar-ground-nuclear-transfer`
contains the complete paper proof and certificate. Scratch proof drafts are
removed; audit/search evidence retained. All owned processes terminated.

Current proof route remains TG. This turn resolved exact all-degree native
source transfer and physical time-band nuclear control through one ground
column. It did not solve arithmetic cancellation. Next attack: the actual
native ground-tail positive energy (including its endpoint term), plus the
explicit Fourier/full-response transport needed to use this control in TG.
No RH proof/falsification, Gamma completion, Hardy comparison or strict
sub-unit law is claimed. Goal remains active and unmet.

## C9.11t — faithful native ground probe (active, paper attack)

Previous turn is progress: exact all-degree ground transfer and physical
S1 control are checked and indexed. Actual arithmetic ground cancellation is
still open. This turn revalidated the native energy and nuclear statements
in the current tree and searched the corpus for its arithmetic frontier.

New conjecture from the verified transfer law: for every aperture a>0 there
is a fixed sufficiently narrow input cutoff f_b (0<b<=a) and a bounded
operator V on physical L2 such that, for every original native symmetric
tail K, `V(K H_a f_b)=K f_0`, with H_a the literal square time-band Fourier
operator and f_0 the output ground cutoff at a. Consequently ground L2
admission is equivalent to the actual physical S1 admission already
controlled by C9.11s. This is a faithful source recovery theorem, not an
improvement of numerical constants or an arithmetic-decay assumption.

Paper mechanism: the exact Fourier column H_a f_b is supported on [-a,a]
and has coefficient expansion
`sum_n ((-2pi i)^n/n!) (integral_-b^b y^n dy) f_n`.
Insert the proved `f_n=a^n S_n T_n f_0`. Divide by2b. This yields a bounded
operator series A_(a,b) on full physical L2, with constant term I and
remaining term norms bounded by `(2pi*a*b)^n/n!`. Therefore A_(a,b) tends
in operator norm to I as b→0+, and is invertible at some fixed b<=a.
Each series term commutes with every native K. Hence
`K H_a f_b=2b A_(a,b) Kf_0`; set `V=(2b)^-1 A_(a,b)^-1`.
A weaker norm-only proof can avoid explicit inversion: bound the same
column remainder by `2b(exp(2pi*a*b)-1)||Kf_0||` and absorb it for small b.
The actual Fourier/Taylor column and source commutations must be identified
in Lean; no arbitrary test-vector or inverse premise may replace them.

Why this matters to the hard arithmetic target: C9.11s was only a sufficient
control. C9.11t would prove that the native nuclear operator cannot hide a
bad ground-tail energy. It would identify the exact source admission
obstruction before attempting the signed critical arithmetic work. It does
not itself bound that work, prove RH, or supply Gamma/Hardy/sub-unit closure.

C9.11t scratch theorem proved, 2026-10-02: the full actual-column identity,
series inversion, original-source commutation, bounded ground recovery and
reverse genuine nuclear estimate pass Lean together. The generic series
has coefficients `((n!)^-1*z^n*mu_n) S_n T_n`, where
`mu_n=(1+(-1)^n)/(2(n+1))`. Its identity term and geometric remainder prove
invertibility for sufficiently small `z=-2pi i ab`. No assumed arithmetic
bound, supplied test-vector identity or abstract inverse was used. The two
previously private native commutation lemmas are now public and their leaf
passes its final foreground audit. Production recovery leaf is wired and
under final audit; public axiom checks and index/lint are still pending.

Critical-arithmetic corpus search `/tmp/tg-c911t-critical-energy-search.json`
completed nonpartial, with snapshot coverage and background refresh still
incomplete. Candidate lemmas, source arguments and proposed ingredients were
inspected. The retrieved prime-counting Big-O has the subexponential PNT
error `x exp(-c sqrt(log x))`; this estimate does not itself bound the critical
weighted square integral. The chronological-work balance retains its signed
upper-work obligation. Neither is relabelled as ground cancellation.
A second search targets the exponential covariance's cumulative Volterra
factorization, to attack the exact native arithmetic energy and its endpoint.

C9.11t closed, 2026-10-02: both affected production leaves pass final
foreground audits with empty diagnostics. All fourteen public declarations
pass `#print axioms` with only the three standard foundations. The new leaf
is wired; index refresh and API-name checks pass. P3
`tg-prime-polar-ground-recovery` contains the complete paper proof and audit
paths. This is actual frontier progress: native ground and square time-band
nuclear admission now have fixed bounds in both directions. It proves no
arithmetic decay. Global lint result is recorded below when complete.

## C9.11u — critical signed cumulative energy (formalized finite identity)

Hard conjecture remains unconditional Cauchy decay of the canonical native
ground tails, with original prime coefficients and polar density. C9.11t
means Fourier smoothing cannot weaken this requirement. The next attack
stays on this arithmetic problem; no smaller numerical constant is sought.

The actual covariance already proved in `SoninPrimePolarSignedEnergy` forces
an exact cumulative factorization. For a finite native signed source w dmu
supported in [L,U], put `C(t)=integral_(u<=t) exp(u/2) w(u) dmu(u)`.
The scalar identity

`exp(-|u-v|/2)=integral_(max(u,v))^infty exp((u+v)/2-t) dt`

and signed Fubini predict

`||K_+ f_a||²=2a integral_R exp(-t)|C(t)|² dt`.

Finite support and integrability justify Fubini before passing to any
cofinal limit. For actual primes Y<p<=X and continuum [log Y,log X], the
factor exp(u/2) cancels the prime inverse square root and changes the polar
density to `(exp(u)+1)/u`. Thus C(t) is exactly
`E_0(min(X,exp(t)))−E_0(Y)` above log Y and zero below, where
`E_0(x)=pi(x)−integral_2^x (1+1/v)/log(v) dv`. Splitting the constant tail
above log X and changing variables gives

`||K_+[Y,X] f_a||² = 2a (integral_Y^X (E_0(x)−E_0(Y))²/x² dx`
`                               +(E_0(X)−E_0(Y))²/X)`.

The endpoint term is mandatory. Full symmetric energy additionally retains
the signed decaying moment from C9.11q. The hard step is to prove the
resulting signed critical energy tends to zero, not to assume weighted-L2
admission or discard its endpoint. Planned mathematical attack: obtain the
exact ordered-block cross terms from the same covariance, then seek an
upper bound for their signed chronological work using actual arithmetic
identities. Kernel positivity alone supplies no such upper bound.

The new Volterra corpus search `/tmp/tg-c911t-volterra-search.json` completed
nonpartial with snapshot coverage and incomplete background refresh.
Candidate lemmas, source arguments and ingredient sets were inspected. It
retrieved general Volterra/Cauchy–Schwarz bounds but did not identify an
applicable native signed cumulative-energy theorem. This is not an
exhaustive absence claim. Rephrase against the literal covariance and
prime-deficit modules before implementing the needed exact identity.

C9.11t final housekeeping: global lint exited 1 with eleven unrelated
unwired leaves, no finding in the two affected modules. All fourteen public
names occur in LEAN_API. All owned processes exited. Obsolete C9.11t proof
and API scratch are removed; final audit logs, axiom scratch, research JSON
and pipeline records are retained. Goal remains active and unmet.

C9.11u implementation attack: revalidated the actual recovery theorem and
searched covariance and logarithmic-unitary mechanisms in the current
corpus. Both searches completed nonpartial with snapshot coverage and
incomplete background refresh; candidates, source arguments and ingredients
were inspected. The native covariance is authoritative. The retrieved
coprime balance controls energy PLUS signed cross work, so it is not an
upper bound for energy alone.

A direct physical proof now avoids assuming a cumulative representation.
The corpus's finite-set indicator pairing determines every L2 vector by its
local scalar integrals. Dominated scalar Fubini therefore identifies the
strong polar integral pointwise. On the actual ground vector, the original
polar coefficient becomes `(exp(u)+1)/u`; the prime inverse square root
cancels its dilation normalization exactly. Under `x=a exp(-t)`, physical
cutoff membership becomes `u<=t`. This yields the literal finite-prime
cumulative error. Existing head-chart mass and even-carrier half-line mass
then give its exact critical energy. This is the active Lean proof, not an
admission premise. The hard Cauchy bound is still the target after this
identity, with the terminal square retained.

C9.11u scratch proof completed: actual logarithmic ground representative,
exact weighted cumulative energy, genuine scalar integrability and terminal
square all pass Lean with empty diagnostics. New production leaf
`SoninPrimePolarCumulativeEnergy` is wired and undergoing its final audit.
No uniform arithmetic bound or cofinal convergence has been proved.

## C9.11v — chronological arithmetic work (finite laws formalized)

The covariance of two native source blocks with disjoint ordered logarithmic
supports [b,R] and [R,S] factorizes. With C_1 the earlier block's terminal
counting discrepancy and

`H_2 = sum_(q in P_2) 1/q - integral_R^S (1+exp(-u))/u du`,

the proposed exact identity is

`inner(K_1 f_a,K_2 f_a) = 2a C_1(R) H_2`.

Paper derivation: the verified native covariance is
`2a exp(-|u-v|/2)`. Ordered supports replace |u-v| by v-u. Multiply by both
original source weights. The earlier exponential cancels the prime inverse
square root and yields the counting-polar density (exp(u)+1)/u. The later
exponential yields 1/q and (1+exp(-v))/v. Finite signed Fubini factors the
cross term; neither polar leg is dropped. This identity is not yet Lean.

The hard conjecture is a cutoff-uniform upper bound, with vanishing tail,
for the resulting full signed chronological work. A scalar harmonic bound
alone is insufficient: it multiplies the earlier counting discrepancy.
Existing coprime balance bounds energy PLUS signed work and cannot discharge
this upper bound. The current Möbius square-root split controls only its
short transient; explicit, constant and long signed channels remain.
No arithmetic conjecture is claimed falsified by these insufficient estimates.

The cross-work search completed nonpartial with snapshot coverage and an
incomplete background refresh. Candidate lemmas, source arguments and
proposed ingredient sets were inspected. Its useful hits are the actual
coprime balance, centered Möbius reconstruction and full prime-work identity;
none inspected proves the needed signed-work bound. An ordered-source search
is running before any new Lean code for C9.11v.

C9.11v further paper deduction, from C9.11u's exact energy rather than a
statistical model: put F(t) equal to the cumulative signed source and divide
the ground energy by 2a. At a prime logarithm r=log p, F jumps by one, so
its terminal square changes by

`exp(-r) ((F(r-)+1)^2-F(r-)^2) = (2F(r-)+1)/p`.

Between prime entries, F' = -(exp(t)+1)/t. Differentiating the integral-plus-
terminal expression cancels its two exp(-t)F(t)^2 contributions, leaving

`-2(1+exp(-t)) F(t)/t`.

Thus, for a synchronized block with zero initial cumulative value, the
exact chronological energy predicted by finite jump calculus is

`sum_(p in P) (2F(log p-)+1)/p`
`  - 2 integral_b^R (1+exp(-t)) F(t)/t dt`.

The prime left limits and both endpoint conventions must be handled
explicitly in Lean; the continuum has no atoms. This deduction is complete
on paper under the stated finite synchronization, not yet formalized.
It identifies the precise difficult work: the signed off-diagonal prime
work and polar work must compensate the harmonic diagonal sum 1/p.
Neither absolute values nor generic positive covariance can do this.
No probabilistic independence, sign premise, or arithmetic asymptotic is
introduced. A failed absolute-value estimate is not a falsification of the
arithmetic cancellation conjecture.

The ordered-source search finished nonpartial with snapshot coverage and
incomplete background refresh; all candidate names, source arguments and
ingredient sets were inspected. It did not return an applicable native
ordered inner-product theorem. Existing connected cumulative and Abel
factorizations concern other carriers; they are not substituted for this
source. The source's already-audited logarithmic covariance directly proves
the ordered paper factorization and is the Lean starting point.

C9.11u final closure, 2026-10-02: production leaf passes foreground final
`lake --old env lean` audit with empty diagnostics. All five public axiom
queries pass with only the standard three foundations. Wired, index passed,
all five public names verified in LEAN_API. Global lint exits 1 with thirteen
unrelated unwired leaves; no finding in the new leaf. All owned processes
are terminal; obsolete scratch removed. P3 `tg-prime-polar-cumulative-energy`
contains complete paper proof and audit paths. Actual ground-tail decay is
still open. C9.11v now attacks the signed chronological work; no RH proof
or falsification is claimed and the goal remains active.

C9.11v execution, 2026-10-02: revalidated C9.11u source and final audit.
New work search `/tmp/tg-c911v-work-search.json` returned partial results with
snapshot coverage and incomplete background refresh. All available candidate
names, source arguments and ingredient sets were inspected. Useful hits
`CCMPrimeDeficitChronologicalWork` and `CCMPrimeEntryWorkSampling` were read:
they prove an analogous full Chebyshev storage balance and explicitly only
a LOWER bound on work. Midpoint sampling merely moves the jump budget into
work. It is therefore not an upper-bound argument and is not pursued here.

The native TG ground source has a different concrete weight. Define its
actual entering vector B_a(u)=exp(-u/2) D_exp(u) f_a. Its ordered covariance
is exactly 2a exp(-v) for u<=v. The actual source is
`sum B_a(log p) - integral_b^R ((exp(u)+1)/u) B_a(u) du`.
This yields the ordered block factorization stated above directly on full
SoninL2, not through a substituted scalar model. Lean scratch now proves the
kernel, actual source representation and earlier-source/later-entry pairing;
ordered block, prime-jump and polar-derivative proofs are being checked.

Actual single-prime energy jump (prime not already in P, every earlier
prime <=p, unchanged original continuum through log p):
`Delta ||K f_a||^2 = 2a (2 C_P(log p)+1)/p`.
Actual polar motion with fixed P and R>b, all earlier log primes<=R:
`d/dR ||K(P,b,R) f_a||^2 = -4a (1+exp(-R)) C_P(R)/R`.
The latter follows by Banach-valued FTC before differentiating the actual
Hilbert norm square. Both signs remain signed; no dissipativity or
independence premise is introduced. These identities make the actual
arithmetic compensation target precise but do not prove its upper bound.

C9.11v scratch and first production audit pass. Eight public declarations
are now in `SoninPrimePolarChronologicalWork`, wired into RHTower. The exact
source pairing, ordered native block cross work, actual prime jump, strong
polar derivative and norm-square polar derivative all elaborate. Two
informational ring normalization suggestions are being removed before the
final audit; no proof premise or statement is changed. The L2 real/complex
pairing bridge uses the actual integrable pointwise pairing, since the two
L2 inner-product instances are not definitionally identical.

## C9.11w — actual signed compensation (next hard attack)

For the canonical genuine prime window b<log p<=R, the new jump and polar
laws predict the full finite balance

`||K_[b,R] f_a||²/(2a) = sum_(b<log p<=R) 1/p + 2 W_b(R)`,

`W_b(R) = sum_(b<log p<=R) F_b(log p-)/p`
`         - integral_b^R (1+exp(-t)) F_b(t)/t dt`.

The target is uniform cancellation
`sum 1/p + 2 W_b(R) -> 0` as b->infinity, uniformly in R>=b,
with the actual terminal square retained. A mere renaming of this identity
as an admission hypothesis is not a proof. The next arithmetic mechanism to
attack is expansion of the actual prime-count coefficient through the
corpus's von Mangoldt/Möbius divisor identities, retaining proper prime
powers and the original logarithmic weight. Search
`/tmp/tg-c911w-mobius-work-search.json` is running. Neither absolute-value
bounds, midpoint sampling, nor the signed coprime balance has proved the
needed compensation. The upper-work conjecture remains open, not falsified.

C9.11w search completed nonpartial with snapshot coverage and incomplete
background refresh. Candidate lemmas, source arguments and ingredient sets
were inspected. Revalidated exact toolchain arithmetic identities
`ArithmeticFunction.moebius_mul_log_eq_vonMangoldt` and
`ArithmeticFunction.sum_moebius_mul_log_eq`. For n>1 the latter gives the
literal prime-power counting weight
`Lambda(n)/log(n) = -sum_(d|n) mu(d) log(d)/log(n)`;
at p^k this is 1/k, so proper prime powers must be retained or transferred
through the already-audited proper-mode admission, never silently removed.

The useful new hit `EulerDeletionAveragedDivisorCovariance` was inspected at
its source definition, actual von Mangoldt relation, cumulative covariance
and square bound. Its Graham estimate controls UNSUMMED divisor coefficient
energy. Its actual accumulated energy separately retains every pair through
a maximum-index kernel. This matches the chronological issue exposed here:
applying the coefficient-square bound as if it bounded cumulative ground
energy would drop temporal correlations. No such inference is made. The
hard attack stays on the full signed Möbius covariance and its polar term.

C9.11v final closure, 2026-10-02: final production leaf audit passes
foreground `lake --old env lean` with empty diagnostics. All eight public
axiom queries pass with the three standard foundations only. Wired and
indexed; all eight public API names verified. Global lint exits 1 with eleven
unrelated unwired modules and no finding in the new leaf. All owned processes
exited; superseded proof drafts removed. P3 `tg-prime-polar-chronological-work`
contains the complete paper proof and audit paths. Progress is the actual
source-specific work laws; the required arithmetic upper bound has not been
proved. C9.11w continues the full signed Möbius covariance attack. No route
is retired and no RH proof or falsification is claimed.

C9.11w new conjecture and paper attack: the missing bridge to the corpus's
full discrete maximum-index covariance is the literal continuum, not a
license to replace it by chosen coefficients. For each n>=2 define

`R_n = integral_[log n, log(n+1)] ((exp(u)+1)/u) (B_a(u)-B_a(log n)) du`.

Retain also its exact cell coefficient
`alpha_n = integral_[log n,log(n+1)] (exp(u)+1)/u du`.
The original polar cell equals alpha_n B_a(log n)+R_n. For n<m, every u in
the n-cell satisfies u<=log m<=v in the m-cell. Expanding the audited ordered
B covariance gives EXACTLY zero between the two differences. Strong-integral
pairings therefore predict R_n perpendicular R_m.

Furthermore `||B_a(u)-B_a(log n)||² = 2a(1/n-exp(-u))`, at most
`2a(1/n-1/(n+1))` on the n-cell. The alpha_n are uniformly bounded using
only positivity, exp(u)<=n+1, log n>=log2 and log(1+1/n)<=1/n.
Thus `||R_n||² <= constant_a/(n(n+1))`. Orthogonality should prove unconditional
summability of the ENTIRE original discretization-error vector series, with
vanishing tails. No alpha_n is replaced by an asymptotic coefficient and no
signed arithmetic covariance is discarded. This is not the desired RH
bound: it aims to close the actual continuum-to-discrete source bridge so
that the remaining full signed covariance can be attacked on the corpus's
exact discrete carrier. Search is running before new Lean code.

C9.11w Lean implementation: the normalized entry covariance proves exact
orthogonality of two separated cell differences. It also proves the full
within-cell difference norm square before estimating it. The literal cell
integrand is strongly integrable by continuity on the positive interval.
A coarse uniform density bound and the shrinking logarithmic width give
`||R_n|| <= C_a/(n+2)`. This seeks square summability, not absolute summability.
The Hilbert orthogonal-family theorem then assembles the full error series.
The exact native polar-only operator identity is included, so convergence
is attached to the original source and its exact mass, not an invented
approximating family. The full discrete prime–polar covariance remains open.

Search outcomes: covariance and polar-cell searches completed nonpartial;
counting-energy search was partial. All used snapshot coverage with incomplete
background refresh. Candidate names, source arguments and ingredient sets
were inspected. Relevant statements were checked: the returned prime-count
estimate is the previous subcritical PNT bound; generic Beurling density,
critical-feature energy and theta screening do not assert the required
native counting-error bound. The polar-cell search returned the actual
C9.11u/v ground formulas but no applicable cell-error admission theorem
among inspected hits. This is not an exhaustive absence claim.

C9.11w full scratch audit now exits 0 with empty diagnostics. Exact native
reconstruction, orthogonality, square summability and unconditional vector
assembly all pass. The production leaf `SoninPolarGroundDiscretization`
contains eight public declarations and is wired; final leaf and foundation
audits follow. The existing chronological leaf also exposes and has audited
the actual entry continuity and polar-density identity used here.

C9.11x corpus search `/tmp/tg-c911x-signed-grid-search.json` completed
nonpartial, snapshot coverage, background refresh incomplete. All candidate
statements, source-argument statements and the proposed ingredient set were
inspected. Generic logarithmic-derivative kernels and prime multiplication
identities do not bound the native covariance. The returned divisor coarea
variance and hyperbolic-sector limit concern different signed kernels; no
transfer to the present critical source is asserted. The full signed
maximum-index covariance, with exact polar masses, remains the hard target.

C9.11w final production audit passes with empty diagnostics:
`/tmp/tg-c911w-final.log`. The exact source correction is now a verified
unconditional infinite-family admission theorem. Its P3 card is
`tg-polar-ground-discretization`. It removes the continuum-cell error,
not the remaining signed arithmetic maximum-index covariance.

## C9.11x — full signed integer-grid compensation

Retain exact alpha_n from C9.11w, and put
`c_n = 1_(n prime) - alpha_n` for integers n>=2. The actual finite grid
source is `G_(L,N) = sum_(L<=n<=N) c_n B_a(log n)`.
The audited ordered covariance predicts the exact whole-space identity

`||G_(L,N)||²/(2a) = sum_(n,m in [L,N]) c_n c_m / max(n,m)`.

For `A_k=sum_(L<=n<=k)c_n`, telescoping the reciprocal kernel yields

`sum_(k=L)^N A_k²/(k(k+1)) + A_N²/(N+1)`.

The terminal square is essential. Removing it, taking absolute values of
the c_n, or bounding only the unsummed coefficients changes the hard
problem. C9.11w admits the entire original within-cell correction; it
supplies no bound on this grid energy.

Next conjecture: the full expression tends to zero as L tends to infinity,
uniformly over N>=L. This is an unproved signed arithmetic cancellation
statement. No numerical rate is imposed. The first paper attack will
expand `Lambda(n)/log n = -sum_(d|n) mu(d)log(d)/log n`, retain the proper
prime powers and exact alpha_n, and keep every resulting divisor-pair
kernel. The corpus's full cumulative covariance is the correct finite
carrier; its unsummed Graham estimate is not a bound for that carrier.
A source-specific estimate for the resulting full signed quadratic form
is the required mathematical advance. No claim that this conjecture is
proved or equivalent to RH has been made.

C9.11x focused maximum-kernel search completed nonpartial, snapshot coverage,
background refresh incomplete: `/tmp/tg-c911x-max-kernel-search.json`.
Candidate statements, source arguments and ingredient sets were inspected.
The covariance/period ingredient set is only a proposed transfer, not a
proof: complete-period residue covariance is a different kernel.

A useful additional exact arithmetic representation is now source-checked:
`PrimeCountDamping.jetCoeff n = mu(n)*omega(n)` and
`sum_(d|n) jetCoeff d = -1_(n is a prime power)` for n!=0;
`jet_floor_sum` gives the completed prime-power count exactly. Source:
`EulerDeletionPrimeCountEndpointVariance`, lines 1–220 inspected.
This opens a log-free divisor representation of the discrete prime source,
provided all proper powers and the original polar centering are retained.
The same module proves only a LOWER endpoint-energy variance bound, not
an upper critical bound. `EulerDeletionPrimeCountAmplification`, lines
1–170 inspected, also excludes an indiscriminate damping-energy bound;
it must not be used to control the endpoint derivative. Next mathematical
attack: the full polar-centered signed divisor-jet covariance itself.
No new Lean theorem about that arithmetic covariance has yet been claimed.

C9.11w closure: both affected final leaf audits pass with empty diagnostics.
All eighteen affected public foundation audits use only the standard three
foundations; index exits 0 and every API name is verified. Global lint exits
1 with ten unrelated unwired leaves and no finding in either affected leaf.
P3 `tg-polar-ground-discretization` and the TG frontier record the exact
source-preserving result and its limitations. Owned superseded proof drafts
are cleaned; audit and search evidence remain. All owned processes exited.
RH remains unproved and unfalsified; the goal remains active.

C9.11x centered-jet search completed nonpartial, snapshot coverage with
background refresh incomplete. Candidate/source statements and ingredients
were inspected; the returned phase-rank and generic damping factors do not
control this covariance. Further source audit of
`EulerDeletionPrimeCountEndpointTransfer` verifies that the full endpoint
error estimate still needs a coefficient-prefix envelope. Its exact
prime-power convolution does not bound that envelope. The arithmetic
cancellation conjecture remains open; no presumed derivative bound is used.

## C9.11y — faithful recovery of both original response channels

The following source-specific factorization arose while checking whether
full-response passage could hide the unknown ground covariance. Write
A and B for the actual time/Fourier projections and T=AB+BA. Then

`T (1-A) B = AB - (AB)^2 = AB(1-AB)`.

Therefore, if the actual `1-AB` is invertible,

`AB = T (1-A) B (1-AB)^(-1)`.

Exchange A and B for the other channel. Actual invertibility should follow
without a new premise from the already-proved norm(BAB)<1 and the algebraic
Jacobson identity, using B²=B. This would prove bounded right-factor
recovery of each channel for EVERY complex left source D. It is stronger
than knowing that a sum belongs to the trace ideal, and is the precise
missing piece for testing faithfulness of the complete response.

Conjecture/proof target: original paired response admission is equivalent
to admission of all four actual time-band source blocks DAB, DBA, D*AB,
D*BA. For native symmetric sources, exact Fourier covariance should then
reduce both channels to the already-controlled physical ground column.
This targets the stated full-response gap; it does not claim arithmetic
cancellation or retire its C9.11x conjecture. Corpus search for the exact
factorization and native transport is running before new Lean code.

C9.11y first scratch audit passed with empty diagnostics. The literal
one-minus products are invertible; both exact right recovery factors and
the complete four-channel nuclear summability/limit equivalences elaborate.
The sole initial proof error was associativity in a projector identity;
explicit A(AB)=AB resolves it without changing any statement. Production
leaf `SoninTimeBandChannelRecovery` is written and wired; final audit starts.
Native full-source Fourier, adjoint and reflection identities are drafted
with the strong polar integral retained. No arithmetic limit is assumed.

C9.11y channel leaf final audit exits 0 with empty diagnostics:
`/tmp/tg-c911y-channel-final.log`. Its 13 public declarations retain both
literal channels and both complex source directions in genuine S1.

The native continuation of the paper proof is now explicit. Let F be actual
Fourier transform, U=F^-1, R=physical reflection and H=AFA the physical
square time-band operator. The original identities are BA=UH and AB=RHF.
For the actual symmetric prime–polar tail D, Fourier reverses each dilation
direction inside both the finite prime sum and the original strong polar
integral. Thus DF=FD. Real source weights and unitary dilation adjoints
also give D*=D; physical reflection commutes as well.

Write W for the already-audited correction right factor. Then

`DJ = R (DH) F(1-AW) + U (DH) W`.

This is a fixed bounded linear reconstruction in S1 from DH. The existing
real-linear paired-response map therefore produces the complete response
pair from the physical time-band source, with a fixed norm constant.
In reverse, recover DJ from the response pair, multiply on the right by
`(1+J) R_BA`, and on the left by F. The new channel identity gives DBA;
commutation with F and FBA=H then give DH exactly. Combining the two fixed
bounded maps with the already-proved ground/time-band estimates yields
cutoff-independent two-way control between the actual complete response
and its physical ground column. This closes native Fourier/full-response
transport if Lean accepts the source identities and norm passage. It does
not prove decay of the ground column, Gamma completion, Hardy compatibility
or the strict sub-unit law. The actual signed arithmetic covariance remains
C9.11x's unsolved mathematical target.

C9.11y native first pass found representation issues only: dependent scale
proofs require `simp` when rewriting exp(-t), Fourier strong-integral
transport needs its explicit continuous-linear-map coercion, and the prime
coefficient is a complex inverse so conjugation first passes through inverse.
These are repaired in the full draft. The same draft now contains actual
bounded S1 forward and recovery maps and both cutoff-independent ground /
complete-response inequalities. A single foreground scratch audit is running.

C9.11y complete native scratch audit exits 0 with empty diagnostics.
Both bounded S1 reconstruction maps and both uniform native ground/complete
response inequalities elaborate, together with all five original-source
symmetry identities. Production leaf `SoninPrimePolarFullResponse` is now
written and wired; its final foreground audit starts. The source maps have
no arithmetic decay or new analytic-domain hypothesis. No heartbeat change
was used. The C9.11x arithmetic cancellation target remains open.

C9.11y both final production audits pass with empty diagnostics. P3
`tg-full-response-ground-admission` now contains the full paper proof and
exact Lean coverage. The source-specific two-way norm bounds close native
Fourier/full-response passage. Foundation audit of all 21 public declarations
and index refresh are running. C9.11x arithmetic cancellation, Gamma
completion, Hardy compatibility and the strict sub-unit law remain open.

C9.11y closure: both final production leaf audits pass with empty diagnostics.
All 21 public foundation queries use only propext, Classical.choice and
Quot.sound. Both leaves are wired and indexed; all 21 API names verified.
Global lint exits 1 with eleven unrelated unwired leaves and no finding in
either new leaf. Logs are `/tmp/tg-c911y-channel-final.log`,
`/tmp/tg-c911y-native-final.log`, `/tmp/tg-c911y-axioms.log`,
`/tmp/tg-c911y-index.log`, `/tmp/tg-c911y-lint.log`.

All owned processes have exited, and superseded proof drafts are cleaned.
P3 `tg-full-response-ground-admission` and the TG frontier record the exact
new theorem. This turn solves native Fourier/full-response transport;
it does not solve the C9.11x signed Möbius covariance bound. The next hard
attack returns to that actual polar-centered covariance with the endpoint
square retained. The corpus's exact mu*omega divisor identity is available,
but its endpoint variance lower bound and coefficient-prefix envelope do
not provide the required upper bound. No cancellation hypothesis has been
added. Gamma completion, Hardy compatibility and strict sub-unit control
also remain open. RH remains unproved and unfalsified; goal active.

## C9.11z — cofinal energy attack, with terminal tightness explicit

The C9.11x arithmetic-jet search completed nonpartial (snapshot; background
refresh incomplete). All returned candidate/source statements and ingredient
sets were inspected. Prime-power support of a residue-history martingale is
not the physical reciprocal-maximum covariance. No upper bound transfers
from that ingredient set. The exact jet convolution remains available.

A second attack through Selberg's complete logarithmic renewal was checked
against `SelbergWeightEvaluation` and `PMSelbergSublinearPowerBoundary`.
The former retains the actual von Mangoldt convolution but supplies only a
linear error bound. The latter already constructs comparison sequences with
literal prime weights, sublinear Selberg response and divergent critical
variance. Thus a coercivity argument based only on that response bound is
invalid. This is an existing obstruction, not a new theorem or a reason to
abandon the actual signed covariance.

New conjecture, directly from the audited ground-entry covariance: the
uniform-all-sharp-cutoffs target in C9.11x contains a terminal tightness
requirement beyond what a cofinal TG construction needs. Let
`B_n = soninGroundEntry a (log(n+2))`, `c_n = 1_Prime(n+2)-alpha_(n+2)`,
`A_n = sum_(j<=n)c_j`, and `D_n=B_n-B_(n+1)`. The actual D_n are pairwise
orthogonal, with squared norm `2a/((n+2)(n+3))`. Finite Abel summation gives

`G_N = sum_(n<=N) A_n D_n + A_N B_(N+1)`.

The two terms on the right are orthogonal, so

`||G_N||²/(2a) = sum_(n<=N) A_n²/((n+2)(n+3)) + A_N²/(N+3)`.

Proposed strongest survivor: finite total positive energy is equivalent to
existence of a cofinal Cauchy subsequence of the literal grid sources, and
also to bounded cofinal returns of their norms. This does NOT discard the
terminal square: summability forces arbitrarily late indices at which
`A_N²/(N+3)` tends to zero, since otherwise the energy dominates a divergent
harmonic tail. Along those selected cutoffs the terminal vector vanishes;
the orthogonal series supplies the remaining strong limit. In reverse,
bounded cofinal returns bound every nonnegative energy prefix.

This separates the true cofinal producer from an unnecessary all-cutoff
terminal claim. The arithmetic total-energy bound itself is still unproved.
Search `/tmp/tg-c911x-cofinal-energy-search.json` is running before Lean work.
No claim about Gamma completion, Hardy compatibility, strict sub-unit control
or RH follows yet. Next step: verify whether this exact native cofinal
criterion is already present, then attack the positive total energy using
the complete signed jet representation rather than scalar renewal bounds.

C9.11z full scratch audit passes with empty diagnostics, including the
literal original prime/polar cell assembly. Production leaf
`SoninPrimePolarCofinalGroundEnergy` is written and wired; its final
foreground leaf audit is running. Eleven public declarations cover the
unchanged grid coefficients, cumulative energy, exact norm with endpoint,
bounded cofinal returns, cofinal strong convergence, explicit endpoint
selection, and transport through the original polar cell integrals.

The proof uses exact annular orthogonality and harmonic nonsummability.
It does not use a prime-count estimate. The practical mathematical change
is precise: the cofinal source producer needs finite total arithmetic
energy, not a separate uniform estimate on every sharp-cutoff endpoint.
No failure of all-cutoff convergence for the actual primes is asserted.
The original arithmetic energy remains unbounded by anything proved here.

## C9.12 — full signed divisor-pair energy, after cofinal criterion

The next attack is on the actual total positive energy, not further
abstract admission receivers. Corpus search
`/tmp/tg-c912-signed-hyperbolic-pair-search.json` is running. Source inspection
of `RoutePMobiusHyperbolaCancellation` verifies the exact complete-square
subtraction and unconditional `sum_(de<=M)mu(d)mu(e)=o(M)`. Inspection of
`RoutePHyperbolicPairDeletion` verifies that its stronger weighted result
uses a specific unsigned dilation profile with a uniform quotient power
remainder. Its normalization is M². Neither theorem by itself bounds the
TG reciprocal-maximum covariance, and the mu*omega jet weights are not
plain mu weights. The intended next conjecture must retain the complete
actual kernel and its polar cross terms before any hyperbolic partition;
no transfer across these differences has been asserted.

C9.11z final production leaf audit exits 0 with empty diagnostics:
`/tmp/tg-c911z-final.log`. The complete theorem applies to the unchanged
actual prime coefficients and original polar cell integrals. Foundation
audit of all eleven public declarations is now running. No umbrella build,
heartbeat increase, numerical experiment or new axiom was used.

C9.11z all eleven public foundation queries pass with exactly the standard
three foundations. Index exits 0 and all eleven API names are present.
P3 `tg-cofinal-polar-ground-energy` and the TG frontier contain the proved
criterion. Global lint is running. This closes a precise cofinal-admission
question, not the hard arithmetic energy estimate.

C9.12 first pair search completed partial and mostly returned irrelevant
algebraic division cancellations. Its suggested ingredient set does not
apply. A focused lexical RouteP search recovered the actual hyperbolic
modules already source-checked; it has no coverage/freshness fields, so no
freshness claim is made. The actual weighted RP theorem uses a different
profile and cannot be imported as a TG bound.

C9.12a conjecture/proof attempt on the literal mu*omega jet: perhaps its
complete LCM pair fibre is prime-supported. Expanding the divisor transform
refutes that proposed support. Write j(n)=mu(n)*omega(n). The corpus gives
`sum_(d|n)j(d)=-1_IsPrimePow(n)` for n>0. For

`H(n)=sum_(lcm(d,e)=n)j(d)j(e)`,

complete divisor-pair regrouping gives
`sum_(m|n)H(m)=(sum_(d|n)j(d))²=1_IsPrimePow(n)`.
The latter is also `sum_(d|n)(-j(d))`. Divisor-transform injectivity therefore
predicts the exact nontrivial survivor `H=-j`, not prime support. In particular
at a product of two distinct primes the fibre is -2, not zero. All common
prime factors must be retained. The local bivariate polynomial confirms it:
for r distinct prime factors the full fibre polynomial is `(xy-x-y)^r`;
its mixed derivative at x=y=1 is `r*(-1)^(r-1)`.

This is a source-derived signed pair law, not a critical-energy bound.
Search `/tmp/tg-c912-jet-lcm-search.json` is running to determine current
coverage before any new Lean code. If the exact law is not already present,
the next paper/Lean task is to prove the complete fibre identity and derive
its sharp finite-cutoff remainder, preserving the actual TG kernel rather
than replacing it by a complete-period covariance. The full signed weighted
remainder, including polar cross terms, remains the hard mathematical target.

C9.11z closure: final leaf audit and all eleven public foundation audits
pass. Leaf wired and indexed; every public API name verified. Global lint
exits 1 on twelve unrelated unwired leaves, with no finding in this leaf.
Final evidence: `/tmp/tg-c911z-final.log`, `/tmp/tg-c911z-axioms.log`,
`/tmp/tg-c911z-index.log`, `/tmp/tg-c911z-lint.log`. Superseded owned drafts
and the exploratory API scratch are removed. All owned processes exited.
RH remains unproved and unfalsified; the goal remains active.

C9.12a search completed nonpartial with snapshot coverage and incomplete
background refresh. Candidate/source statements and proposed ingredients
were inspected. Source checks of `EulerDeletionTruncatedDivisorPairCorrelation`
lines 330–379 and 580–607 expose `lcmPairFibre_moebius_inversion` and its
finite-carrier version. Combined with `sum_divisors_jet` and
`jetCoeff_eq_primePower_convolution`, these supply the exact paper proof
of complete jet fibre H=-j. The specialized theorem has not yet been audited
in Lean. Finite TG kernel weights must still be retained; the literal
counting source uses floor columns of j, not bare j vectors. Do not replace
that kernel by lcm-only or complete-period covariance. Next hard activity
is the signed, polar-centered weighted remainder after the exact fibre
identity, not a scalar renewal estimate or a new generic receiver.

C9.12 continuation revalidated the prior production proof, foundation log,
current frontier and the exact source signatures. Prior turn classified as
progress: authoritative cofinal criterion changed, arithmetic energy still
unproved. This turn targets the signed pair law inside the actual kernel.

C9.12b new shifted conjecture from the corpus's exact divisor transform:
let H_j(n;k,m) be the complete lcm=n pair fibre of j(d)j(e) with d|k and e|m.
Möbius inversion gives exactly

`H_j(n;k,m)=sum_(r|n) mu(n/r) *
  1_IsPrimePow(gcd(r,k)) * 1_IsPrimePow(gcd(r,m))`.

No period average is taken. On the diagonal k=m this reduces to
`-j(n)*1_(n|k)`. Before proving an upper bound, this law must be carried
through the original finite counting windows and the full signed polar
centering. A finite counting window automatically keeps all incident d,e
below its cutoff even when their lcm exceeds it; high-lcm fibres must not
be dropped.

A stronger local sign formula is suggested by the exact bivariate source
factor: for squarefree n with every prime dividing k*m, let L count primes
of n dividing k only, R those dividing m only, S those dividing both.
Then H_j should be mu(n)*(L*R-S); if a prime divides neither, the fibre
vanishes. The negative shared-prime term competes with the positive
exclusive-prime product. This formula is paper-derived, not yet Lean-audited.
The available finite-LCM Möbius inversion gives the first displayed theorem
without any local-factor guess. Focused corpus search is running before its
new Lean implementation. None of these identities proves critical energy
finiteness; the actual weighted, polar-centered covariance remains the goal.
