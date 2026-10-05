# BAG physical contraction matching through the joint damping-height limit

- **ID:** BAG-C28.56af, active physical-transfer formalization.
- **Route:** BAG actual rational cubic -> literal physical contraction matching
  and retained finite-height near-resonances -> complete growing moments/self-return.
- **Predecessor:** C28.56ae full Schwartz arithmetic boundary, all four production leaves and
  all 33 public axiom audits passed.

## Current checkpoint

C28.56af.1 is closed in Lean: the actual complete divisor-square Dirichlet
series equals the existing BAG axis continuation, both poles remain explicit,
and uniform damping-squared cancellation holds on actual zero-free disks.
See [audited source theorem](../3-formalized/bag-damped-square-axis-coalescence.md).
Production and all12 public axiom audits passed. The stronger uniform smooth
joint damping-height law now has a [paper proof](../2-fully-proven/bag-uniform-damping-height-square-law.md),
C28.56af.2. Its COMPLETE literal-window uniform law is now formalized in
C28.56af.2b: five new leaves,15 public declarations passed all production
and standard-axiom audits. Every edge, both tails and both coalescing residues
are retained, including e log X->0. See
[full joint-law proof](../3-formalized/bag-uniform-damping-height-square-law.md).
The full signed cubic and RH remain open. Earlier conjecture and process
language below records development and is superseded here.

## Hard problem

Identify the literal arithmetic axes with the physical repeated-prime
contractions, including their all-equal overlap, under a proved JOINT damping
and height limit. The cubic's full signed near-resonant contribution must be
retained. Fixed-test distributional convergence does not give this transfer.

Current calibration conjecture determines the joint quadratic normalization
from the ACTUAL source, rather than assuming fixed-damping Haar means remain
valid at moving height. Let

    D_epsilon(n) = pmPowerDampedDivisorCoeff epsilon n
                 = product_(p|n) (1-p^(-epsilon)),  n>0.

For c>0 fixed, epsilon_N=c/log N, conjecture for the literal physical smooth
window W=bagPhysicalHeightWindow:

    lim_(N->infinity) (log N/N) * sum_n D_(epsilon_N)(n)^2 W(n/N)
      = (c/2)*(1-exp(-2*c))*integral W.

The sum is finite because W has its proved physical support. A stronger
version replaces W by every fixed smooth compact profile on (0,infinity),
then supplies uniform control as c tends to zero with N. The sharp dyadic-band
version must retain endpoint contributions rather than silently smoothing them.
These are CONJECTURES, not audited results or premises to an RH theorem.

## Corpus facts already read

- PMPowerDampedMobiusDivisorHaar: literal divisor sum, finite prime product,
  positivity, and D_epsilon(n)<=1 for epsilon>=0.
- PMPowerDampedMobiusRamanujanExpansion: grouped, absolutely convergent
  Ramanujan expansion for every fixed n and epsilon>0. Individual ungrouped
  residue-frequency summability is not supplied.
- PMPowerDampedMobiusSecondMoment: fixed-epsilon mean of D_epsilon(n)^2 tends
  to pmPowerDampedSecondDensity epsilon.
- PMPowerDampedMobiusSmallDampingVariance: that density divided by epsilon
  tends to 1/2. This is an ITERATED limit, not the conjectured joint limit.
- ChiPrimeGaussianCubicMain: exact full physical cubic main and its two
  repeated-prime contractions minus the all-equal overlap, with complete
  signed off-diagonal retained.
- BagPhysicalWindowGram: actual W is Schwartz; its exact Fourier scaling and
  signed Gram identity are already proved.

Search87795 (deep300) was nonpartial65534/65534 and returned the actual source
and log-convolution laws, not this joint limit. Search89001 was nonpartial
65591/65591 but mostly irrelevant to the mathematical meaning of height;
all candidate/source/idea/ingredient sections were inspected. Compiler metadata
mostly source-only/pending; background refresh incomplete. A more focused
PMPowerDamped/LSeries/second-moment search is in progress at creation.

## New paper mechanism to prove or refute

At a prime put q=p^(-s), t=p^(-epsilon). The source's exact local square
Dirichlet factor is

    (1-2*t*q+t^2*q)/(1-q).

Algebra predicts the COMPLETE factorization

    sum_n D_epsilon(n)^2 / n^s
      = zeta(s)*zeta(s+2*epsilon)/zeta(s+epsilon)^2 * H_epsilon(s),

    H_epsilon(s) = product_p [1-(t*(1-t)*q/(1-t*q))^2].

No omitted prime powers or selected residue modes are allowed. Build the
actual identity and normal convergence from the source if missing. The local
correction tends to one and admits a summable p^-2 majorant near s=1 on the
real right side; the small-damping variance source already exposes its s=1
specialization. This does not yet prove the complex moving-contour bounds.

The two moving numerator poles, at s=1 and s=1-2*epsilon, predict opposite
residues asymptotic to epsilon/2. At epsilon=c/log N the second contributes
the factor -exp(-2*c). Dropping it yields the WRONG proposed joint law.
The denominator's inverse zeta factors must be controlled on the entire
moving contour using the actual zero-free source, not RH.

A precise preliminary consequence to audit is, for every a>0,

    lim_(epsilon->0+) sum_n D_epsilon(n)^2 / n^(1+a*epsilon)
      = (a+1)^2/(a*(a+2)).

Its positive logarithmic-scale measure would have limiting atom1 at zero
and density (1-exp(-2*t))/2 for t>0. Weak convergence on that logarithmic
scale alone does NOT resolve a physical band whose width shrinks on that
scale. The hard target remains the moving-pole LOCAL normalization above,
including uniform small-c control needed for prime extraction.

## Do not overclaim the bridge

Even the proposed quadratic normalization would not prove the complete cubic
near-resonance estimate. The corpus explicitly refutes generic quadratic-to-
cubic promotion for prime packets. Continue with the original signed cubic,
actual V/W weights, every contraction and finite-height near-resonance. Do not
replace prime coefficients by the damping derivative without accounting for
prime powers: the derivative is a von Mangoldt source, not a prime indicator.
Growing moments, moving cofactors, positive common-height self-return and RH
remain open. No route retirement or negative theorem is claimed here.


## Exact source identification and uniform continuation, 2026-10-04

New algebraic observation grounded in axisRegularFactor:

    H_epsilon(s) = axisEulerCorrection (s+epsilon) (-epsilon).

Indeed its local factor has z=p^(-(s+epsilon)), U=p^epsilon, hence
1-z^2*(1-U^(-1))^2/(1-z)^2 is EXACTLY the deficit factor above.
The existing normally convergent axis product already supplies joint complex
analytic control. Do not rebuild a duplicate Euler correction. Prove the
complete actual divisor-square Dirichlet series identity using multiplicativity
and its full prime-power geometric factors. This directly connects the
physical coefficient energy to the arithmetic axis source.

Strengthened hard local target: for fixed C>0 and smooth compact positive-axis W,
with L=log N, uniformly 0<epsilon<=C/L,

    sum_n D_epsilon(n)^2 W(n/N) / (N*epsilon^2*L)
      - ((1-exp(-2*epsilon*L))/(2*epsilon*L))*integral W -> 0.

This includes the coalescing-pole regime epsilon*L->0 needed for prime
extraction. The fixed-c conjecture is only a consequence. A proposed proof
retains epsilon^2 before any contour estimate. Write F(s) for the actual
pole-removed zeta source and

    U(s,epsilon)=F(s)*F(s+2*epsilon)/F(s+epsilon)^2
                  *axisEulerCorrection(s+epsilon,-epsilon).

Then the Dirichlet source equals

    [1+epsilon^2/((s-1)*(s+2*epsilon-1))]*U(s,epsilon),

and U(s,0)=1, its first damping derivative is zero. Holomorphic division
should give U=1+epsilon^2*V locally, with polynomial bounds on actual
zero-free neighborhoods. Therefore (DirichletSource-1)/epsilon^2 has
uniform contour bounds, with both poles retained, even as epsilon->0.

Proposed contour: height T=(log N)^kappa, 0<kappa<1/9, left displacement
delta comparable to T^(-9) from exists_zeta_polynomial_zeroFree_region.
Then delta>>epsilon and delta*log N->infinity. Fixed smooth W has arbitrary
Mellin decay; select its order after the actual polynomial source bound.
On the initial right line, D_epsilon(n)<=epsilon*log n for n>1 supplies
uniform tails after epsilon^2 division. The two residue contributions are
N*epsilon/2 times

    U(1,epsilon)*M_W(1)
      -exp(-2*epsilon*L)*U(1-2*epsilon,epsilon)*M_W(1-2*epsilon).

U-1=O(epsilon^2), M_W(1-2epsilon)-M_W(1)=O(epsilon); after dividing by
N*epsilon^2*L these errors vanish uniformly, including arbitrarily small
positive epsilon. All contour-edge, tail, holomorphic-division and actual
Dirichlet identification obligations remain to be proved and audited.
This paragraph is a proof plan, NOT a completed dependency-closed proof.

Search93135 completed partial65595/65595, malformed local-model JSON in
filter_and_judge; all returned candidate/source/idea/ingredient sections
inspected. Coverage snapshot older generation; compiler mostly source-only
or pending; refresh incomplete. It finds fixed-epsilon moment/divisor laws,
not the joint local theorem. Followup90093 seeks Euler/LSeries machinery;
JSON /tmp/bag-square-dirichlet-axis-search-01a1.json.


Proof refinement: use the centered normalized axis
Q(sigma,alpha)=regularAxisSource(sigma,alpha)/F(sigma)^2.
Q(sigma,0)=1 and its FIRST alpha derivative is zero for every admissible
sigma. Physical U(s,epsilon)=Q(s+epsilon,-epsilon). On the actual
zero-free disks about 1+i*t, F and inverse F have polynomial bounds,
and the existing axis correction has a global tube bound. Cauchy plus
the double zero bounds |Q-1|/|alpha|^2 uniformly by a polynomial in
1+|t|. This direct scalar slice argument can supply the needed contour
estimate without constructing a new joint holomorphic quotient first.
It retains arbitrary moving sigma and arbitrarily small damping.

Search90093 finished nonpartial65596/65596, no errors, older coverage
snapshot, mostly source-only compiler state, refresh incomplete. All
sections inspected. Actual EulerProduct.eulerProduct_hasProd applies;
completely multiplicative variants do not apply to the divisor square.
Search12567 finished nonpartial65596/65596, no errors, refresh incomplete;
all sections inspected. Its proposed homological-complex double-zero
ingredient is irrelevant; no analytic source implication follows. Use
actual axis value/derivative identities and scalar Cauchy estimates.

First new scratch83640 exited1: inferred complex powers of real exponents
from ambiguous casts, and a missing explicit function argument in term_def0.
Those elaboration errors led to a timeout in the dependent Euler proof;
corrected the types instead of raising heartbeats. Combined identity and
coalescing-source scratch77963 is the only live owned Lean build at this
checkpoint. No new production theorem claimed yet.


Latest audited checkpoint: production80197 and axiom26840 exit0, all12 public
names standard axioms only; index41850exit0, all12 indexed; lint38417exit1
exactly40 unrelated unreachable modules, no proof debt or own errors.
The production source is ChiRamanujanDampedSquareAxis.lean, wired once.
All owned Lean/search/index/lint jobs are terminal at this checkpoint.

Next exact work is the actual-window moving rectangle assembly in af.2.
Mathlib mellinInv_mellin_eq has been read; it requires MellinConvergent,
vertical integrability and continuity. The corpus IsTest.eulerDeriv and
mellin_eulerDeriv retain smooth positive-axis compact support, but the current
MellinTestFunctionPerron source only exposes order-two uniform strip decay.
Build the all-order uniform version and instantiate the literal
bagPhysicalHeightWindow (LogPhasePhysicalWindow:121), rather than assuming
an abstract test bound. The local-domain rectangle residue theorem in
RectangleConfluentTwoPoleResidue is applicable after constructing the actual
holomorphic pole-subtracted remainder; the simpler RectangleTwoPoleResidue
requires an ENTIRE remainder and does not apply directly. Keep both original
infinite tails and all four edges. No fixed-line estimate is promoted to a
uniform moving-strip estimate.


## C28.56af.2 active Lean attack, 2026-10-04 continuation01a2

Previous turn was verified progress (af.1 actual-source and uniform double
cancellation). Work now targets the COMPLETE smooth joint damping-height law
in P2, not another fixed-damping receiver. Search14830 is running for the
literal moving-pole contour source. Needed MellinTestFunctionPerron dependency
has no olean although its dependencies are present; checking that leaf alone
in the foreground before using its Euler-derivative identities. Do not modify
other active source files or start full builds.

First owned proof construction: induct the compact test Euler derivative to
arbitrary order on a fixed strip, instantiate the literal physical height
window, establish its Mellin inversion, then construct the actual holomorphic
two-pole-subtracted source and its rectangle identity. These are dependencies
of the hard af.2 local law. Retain uniform epsilon^2 through every estimate.

C28.56af.2 source update (01a2): Mellin dependency leaf passed. Search14830
nonpartial65601/65601 found no complete actual contour. Search20110 lexical
confirmed Euler differentiation. Search27110 nonpartial65603/65603 (refresh
incomplete; semantic coverage unavailable; compiler mostly source-only) found
AnalyticDividedDifference and the local two-pole rectangle machinery; all
candidate/source/idea/ingredient sections inspected. Unrelated two-point
spacing candidates do not supply the required source.

Exact new construction now in scratch: with p=1, q=1-2e,
g(s)=Q(s+e,-e) M(s) X^s, the normalized integrand is
A(s)+g(s)/((s-p)(s-q)), A=(Q-1) M X^s/e^2. Its pole-subtracted remainder is
A(s)+dslope(dslope(g,p),q)(s). The algebraic decomposition is valid globally
off p,q, and analyticity follows locally from the actual regular source.
Choose d=min(c/8,1/128) from actual polynomial zero-free disks. For
0<delta<=d/(1+T)^9, 0<e<delta/4 and 0<b<=delta, the complete rectangle
[1-delta,1+b]+i[-T,T] lies in this actual analytic domain. This removes any
assumed zero-free-region or analytic-remainder premise from the planned
rectangle theorem. Scratch not yet audited; full uniform law still open.

01a2 verified checkpoint: actual-window Mellin scratch and production leaf
both passed. Actual rectangle scratch passed, then the clean production leaf
passed (82488). New leaves are ChiRamanujanDampedSquareMellin and
ChiRamanujanDampedSquareContour, each imported once into RHTower. No umbrella
build. Axiom and lint audits remain pending until the current right-line
construction is finished.

Right-line construction uses the literal finite prime product to prove
D_e(n)<=e log n for every n>1. Squaring yields a complete positive majorant,
independent of the damping after division by e^2. Corpus PSeriesTailAboveCutoff
supplies the whole p-series comparison; exponential Taylor domination supplies
log^2 n <=8/b^2*n^(b/2). Hence the entire original line at Re s=1+b has
|S_e(s)-1|<=24 e^2/b^3, uniformly at every height. Constants are incidental;
the preserved damping factor is the reason this step is necessary. Scratch
currently checking; no result asserted before its audit. Search30084 was
nonpartial65603/65603; all candidate/source/idea/ingredient sections inspected;
its divisor-convolution proposals alone do not give this uniform domination.
Search3757 lexical found the p-series tail source used directly.

Next exact transfer step (01a2, active scratch): summed Mellin inversion for
all actual divisor-square coefficients. Search17813 lexical recovered
SmoothWeightPerron and PerronSummable; their literal windows differ, so the
new proof uses the now-verified actual bagPhysicalHeightWindow transform.
The source coefficient bound gives absolute integral-sum exchange. For each
positive integer n, positive-real complex-power multiplication identifies
n^(-s) X^s=(n/X)^(-s), and actual-window inversion gives that term exactly.
The integral interchange itself proves summability; no assumed interchange
or selected finite subseries is used. Scratch /tmp/bag-square-perron-01a2.lean
is written but not yet checked. Required remaining law: subtract n=1,
connect the infinite line to the rectangle, bound both tails/all other edges,
and combine both coalescing residues uniformly. RH unchanged.

## C28.56af.2a final audit, continuation01a2

Four new leaves,19 public declarations are complete: Mellin6, Contour3,
RightLine5 and Perron5. Perron normalized complete-sum equality and full
absolute integrability passed scratch58812, production49430 and axiom13357.
Earlier three leaf/axiom audits are recorded above. Every public declaration
uses only propext/Classical.choice/Quot.sound. Final index21998 passed; all19
API entries and allfour RHTower imports verified exactly once. The required
checked MellinTestFunctionPerron dependency is imported once into HTGeometry.
No full/umbrella build. Final lint77120 failed on34 unrelated unreachable
modules only; no proof debt and no new-leaf/dependency errors. Global lint
is not claimed clean. All owned build/search/index/lint sessions terminal.

The exact source passage now removes n=1 for X>=1 and identifies the FULL
weighted divisor-square sum/e^2 with the literal absolutely integrable
normalized contour line. This closes summed inversion, not the uniform
joint law. P3 and frontier rowaf.2a now record all19 results.

## Next hard attack: uniform coalescence and integrated contour error

Conjecture C28.56af.2b: source constants eta,C>0 exist such that for ALL
X>1 and 0<e<=eta, the TWO actual rectangle residues, divided by X log X,
differ from Psi(e log X) M(1) by at most C/log X. No lower bound on e log X.
This is a uniform cancellation statement; the constant is incidental.

Corpus evidence: af.1 gives Q(1+e,-e)=1+O(e^2) and Q(1-e,-e)=1+O(e^2).
The new literal M is entire. Search30728 lexical found and source inspection
verified HTGeometry.norm_sub_le_of_hasDerivAt_ball in ComplexBallMeanValue.
A compact derivative bound for M gives |M(1-2e)-M(1)|<=B e. With r=X^(-2e)
in [0,1], the error numerator is exactly

    (Q_plus-1) M(1) - r*((Q_minus-1) M(1-2e)+(M(1-2e)-M(1))).

It is O(e), before division by 2e log X. Prove this ACTUAL source result in
Lean next, then integrate the retained left/horizontal/tail estimates from
P2 and assemble the joint limit. Search evidence saved in
/tmp/bag-square-residue-meanvalue-search-01a2.json. No af.2b Lean scratch yet.
Full signed cubic near-resonances, growing profiles/moments, moving cofactors,
positive common-height self-return and RH remain open. Goal stays active.

## C28.56af.2b active proof, continuation01a3

Previous turn classified PROGRESS: nineteen production/axiom-audited source
and contour declarations changed the frontier. Goal and BAG route unchanged.
Current scratch construction will prove the actual two-residue uniform
coalescence, then address integrated contour errors. The entire actual M
makes dslope(M,1) analytic everywhere (already imported corpus lemma), hence
bounded on a compact ball. The identity (s-1)*dslope(M,1)(s)=M(s)-M(1)
supplies the needed O(e) shift without an assumed derivative bound. Combine
with af.1 actual Q=1+O(e^2) and X^(-2e)<=1 before dividing by e log X.
Search7740 deep is running; no owned Lean build yet. No full law or RH claim.

01a3 continuation update (2026-10-05): residue production20834 passed cleanly.
ChiRamanujanDampedSquareResidues has two definitions and three theorems:
the exact signed packet, its actual-source C/log X error uniformly over the
FIXED interval 0<e<=eta, and TendstoUniformlyOn of that error. This includes
every joint path with e log X tending to zero. Its RHTower import is present;
axiom/index/lint audits remain pending until the edge/tail batch completes.
The proof uses entire dslope(M,1) on a compact ball; no derivative premise.
Two norm-estimate elaboration errors were corrected without changing the
mathematics. Deep residue search7740 was nonpartial65611/65611, errors[],
refresh incomplete; proposed generic Mellin derivatives did not replace
actual Q quadratic cancellation. All candidate/source/idea sections read.

Deep tail search81830 was nonpartial65612/65612, errors[], refresh incomplete.
Its CGL truncation hit led to the existing generic TWO-sided power-tail
theorem in InghamUniformDetectorMellinFullTwoTail. Apply it to the actual
integrable normalized square source: Mellin strip decay and the complete
24/b^3 right-line bound give both discarded tails with no e dependence.
Scratch /tmp/bag-square-tails-01a3.lean is checking in55185 after a syntax
fix. The two-pole left/horizontal geometry is written in
/tmp/bag-square-edges-01a3.lean; first74837 exposed local proof elaboration
issues, now corrected for the next check. No integrated bound is claimed
formalized yet. Lexical edge search recovered the exact actual continuation
remainder. Full square law, full signed cubic and RH remain open.

Next exact transfer identity retains all four errors. With R the full
right-line integral, R_T its truncation, L the left edge, B/U the bottom/top
edges and P the residue sum, the rectangle gives

    R-2*pi*P = (R-R_T)+L+i*(B-U).

After division by 2*pi*X*log X this is the actual weighted energy minus
the normalized two-residue packet. No tail/edge may be silently discarded.
For final limit one may use T=u, X=exp(u^18), b=u^(-18) and
delta=d/(1+u)^9; this covers all sufficiently large heights. Polynomial
tail errors and exp(-delta*log X) times a polynomial must all tend to zero.
Deep joint-limit search95710 is running; no receiver-only limit replaces
the actual source. This is a proof-organization choice, not bound tuning.

01a3 second checkpoint: actual two-tail scratch55185 and production94324
passed cleanly; ChiRamanujanDampedSquareTails is wired once. Actual left and
BOTH horizontal integrated bounds passed scratch57529. Production edge
audit is running. For one source d>0, C>0 and every j an actual A_j>0:

    |left integral| <= C X^(1-delta)(1+T)^55(1+2/delta^2),
    |each horizontal integral| <= A_j X^(1+b)(1+T)^54/(1+T)^j.

The same rectangle geometry is used, with T>=1, e<delta/4, b<=delta and
delta<=d/(1+T)^9. Pole distances are proved from real/imaginary parts;
the source-disk condition and Mellin-strip condition are also derived.
No boundary growth premise was introduced. Generic right-tail decay and
integrability are applied to the actual full source, not a selected series.
Joint-limit deep search95710 completed nonpartial65617/65617, errors[],
refresh incomplete. All candidate/source/idea/ingredient sections inspected;
suggested envelope/AkraBazzi pairing is not applicable. Corpus PolyExpDecayLimit
and the actual mathlib power/exponential limits supply the elementary final
decay step. Scratch /tmp/bag-square-joint-limits-01a3.lean contains the
source-matched left-error limit, not yet checked. Exact transfer scratch
/tmp/bag-square-transfer-01a3.lean also awaits its first check. RH remains open.

01a3 third checkpoint: edge production42770 passed. Transfer production50009
passed with three public declarations: actual normalized energy, exact
four-error identity, and the COMPLETE actual error bound. The latter gives,
for a source d>0 and every integer j>=2, one K_j>0 independent of damping:

    |energy_e(X)-residuePacket_e(X)| <= K_j/(X log X) *
      [X^(1+b)/b^3 * T^(1-j)/(j-1)
       + X^(1-delta)(1+T)^55(1+2/delta^2)
       + X^(1+b)(1+T)^54/(1+T)^j].

Four new leaves now have11 public declarations and all production audits
passed. All are wired once; axiom/index/lint remain pending. Source equality
and four-error assembly needed explicit scalar algebra to avoid rewriting
inside the actual integrals. No analytic assumption was introduced.

The full uniform joint-law scratch now includes: all three normalized error
limits, eventual moving geometry uniform in c in (0,C], residue control,
and conversion from X=exp(T^18) to ALL X via T=(log X)^(1/18). First5177
reached only one ring-recursion failure in scalar normalization; replaced
that expansion with a six-variable scalar identity, no compiler-limit change.
Current scratch check28356 is running. Literal M(1)=integral W remains to be
added before final source-window statement. The complete joint law is NOT
yet claimed audited. Scratch /tmp/bag-square-joint-limits-01a3.lean is active.

## C28.56af.2b final closure, continuation01a3

Full actual-window uniform law passed scratch20250, production72335 and
all15-public-declaration axiom17545. Only standard logical axioms occur.
Earlier four production checks also passed. Index28644 refreshed allfive
leaves; all15 API entries and once-only RHTower imports verified. Lint22251
reports40 unrelated unreachable modules only, no proof debt or own finding.
All jobs terminal; seven completed owned scratch files removed, all logs
and corpus-search JSON retained. No full/umbrella builds or compiler-limit
increases. P3 and frontier C28.56af.2b record the complete literal-window law.

The target succeeded; do not spend another turn reproving or tuning it.
Continue C28.44: the COMPLETE signed physical cubic with its near-resonances.
Fresh exact search and source reads confirm the actual prime-only Vaughan
identity already removes proper powers. It does not control the aggregate
weighted row. Preserve Type-I squarefree masks, the signed Type-II coefficient,
all common q,r moduli, contractions/overlap and incomplete determinant fibres.
The prior signed-medium card documents why scalar unit-phase bounds and
absolute cross-modulus energies do not close that aggregate. The next proof
must overcome that precise signed estimate, not add it as a hypothesis.
Full growing-profile transfer, growing moments, moving cofactors, positive
common-height self-return and RH remain open. Turn classified PROGRESS;
goal remains active, with no external blocker.
