# TG C9.14: Gamma logarithmic-clock endpoint and the actual cutoff domain

- **Stage:** 1-in-progress
- **Route:** TG, lower-end Gamma/pole normalization
- **Status:** C9.14 endpoint obstruction and exact relative ground completion formalized; C9.15 scalar source identification formalized; C9.16 joint distant-clock obstruction formalized; C9.17 full remainder response and reference domain active
- **Original goal:** unconditional RH proof or falsification, not a no-go alone

## Corpus basis and exact question

`CCMPublishedSourceSineCoefficient.ccmPublishedArchimedeanDensity u` is
`gamma(u)=exp(u/2)/(exp(u)-exp(-u))`.
`CCMGuinandWeilArchimedeanOddSource.tendsto_h_mul_ccmPublishedArchimedeanDensity`
proves `u*gamma(u) -> 1/2` at zero from the right. This is a first-order pole.
The existing TG principal logarithmic source divides the nonzero first-clock
position u: prime coefficient becomes `1/(k*sqrt(p^k))` and the polar density
becomes `2*cosh(u/2)/u`. Applying that same operation to the Gamma channel
produces `gamma(u)/u`. This last full-source identification still needs its
own proof; do not silently equate a sine-tested scalar distribution with
a symmetric operator.

Test the explicitly defined, finite-cutoff operator

`K_(eps,b)=integral_(eps)^b gamma(u)/u * (D_(exp u)+D_(exp(-u))-2I) du`

on the literal ground cutoff `f_a=1_[-a,a]`, for a>0, 0<eps<b. No claim
about the original completed Gamma source follows until the source weld is
verified. The operator above is defined and meaningful independently.

## Conjecture C9.14a and proposed paper proof

For some b>0 and every a>0, `||K_(eps,b) f_a|| -> infinity` as eps->0+.
This is a structural domain issue, not optimization of a constant.

The actual dilation convention in the corpus gives
`D_(exp u) f_a=exp(u/2)*1_[-a*exp(-u),a*exp(-u)]` and
`D_(exp(-u)) f_a=exp(-u/2)*1_[-a*exp(u),a*exp(u)]`.
On the annulus `a*exp(-eps)<|x|<a`, every u in [eps,b] therefore leaves the
exact scalar integrand `(exp(-u/2)-2)*gamma(u)/u`. Restricting the Bochner
integral to this annulus gives the exact vector

`[integral_(eps)^b (exp(-u/2)-2)*gamma(u)/u du] * 1_annulus`.

The principal Gamma limit supplies b>0 for which `gamma(u)/u>=1/(4u^2)`
throughout (0,b]. Since exp(-u/2)<=1, the absolute scalar is at least
`(1/4)*(1/eps-1/b)`. The annulus has measure `2a*(1-exp(-eps))`, whose
ratio to eps tends to 2a. Hence the squared norm has a lower bound of
order 1/eps and diverges. This is analytic, with no numerical experiment.

Check both dilation formulas against actual source definitions, verify
Bochner restriction/interchange, and formalize this exact annular identity
and divergence. Do not replace it by a generic singular-kernel example.

## Positive survivor to develop before any retirement

The exact annular response identifies the missing boundary trace and
provides a source-faithful lower-end subtraction diagnostic. A serious
second pass should classify the admitted domain of this Gamma observable
on the actual time-band anticommutator T=AB+BA. Candidate: zero endpoint
traces of Bf in physical coordinates and of Fourier(Af) in Fourier
coordinates remove the cutoff singularities; the full equivalence needs
a dilation-generator/Gamma-symbol domain proof and is not established.

If the source weld instead forces a different regularization or parity,
retain that exact source and revise the conjecture. A failure of the
bounded assembly does not falsify RH and does not retire TG.

## Relation to active arithmetic work

C9.12's exact signed jet covariance is formalized; C9.13 still attacks
`Summable soninPrimePolarGridEnergy`. That arithmetic problem is not
abandoned. C9.14 examines another explicitly required TG gap: lower-end
Gamma completion, before a joint operator or Hardy/sub-unit assertion.

- 2026-10-03 — Corpus Gamma principal coefficient and actual Sonin response
  definitions read. Focused Gamma source search running; endpoint proof
  formulated analytically. No Lean theorem or full-source identification
  claimed yet.

## Second pass: forced principal part and positive relative completion

The endpoint argument suggests a canonical positive survivor, not merely
an exclusion. Split the EXACT density on (0,infinity) as

`gamma(u)/u = 1/(2u^2) + r_gamma(u)`.

The homogeneous term is forced by the audited principal coefficient, not
fitted to an RH or trace target. From the defining exponential expression,
`gamma(u)=1/(2u)+1/4+O(u)` near zero, hence
`r_gamma(u)=1/(4u)+O(1)`. At infinity gamma decays and the remainder has
O(u^-2) tail. These stronger asymptotics still need paper-to-Lean verification.

For the actual symmetric ground difference F_a(u), the exact dilation
covariance predicts `||F_a(u)||=O(sqrt(u))` at zero and a bounded norm
globally. Thus `r_gamma(u)*F_a(u)` should be Bochner integrable on (0,infinity).
The original full source is retained as its forced unbounded homogeneous
Gamma principal operator plus this admitted remainder. No coefficient or
parity is discarded. The known monomial-transfer and Taylor nuclear maps
may then transfer actual ground convergence of the remainder to the full
Sonin response pair; check their precise generic hypotheses before use.

Scalar source weld: the finite symmetric multiplier is
`2*integral_(eps)^b (cos(xi*u)-1)*gamma(u)/u du`; its xi derivative is
`-2*integral_(eps)^b sin(xi*u)*gamma(u)du`, exactly the truncated published
odd Gamma source up to the displayed fixed factor. Full cutoff removal and
meromorphic completion are further obligations. The homogeneous multiplier
is predicted to be `-pi*abs(xi)/2`, not zero. This is a principal/residual
operator construction, not a proof that the original full source is bounded.

Search evidence: `/tmp/tg-c913-gamma-source-search.json` was partial with
snapshot coverage and incomplete refresh. Candidates/source arguments and
proposed ingredients were inspected. They did not supply this endpoint
identity or relative split. A more focused endpoint-integral search is active.

Lean scratch `/tmp/tg-c914-gamma-endpoint.lean` starts with the literal
finite-cutoff vector and exact shell pairing. It is under audit; no result
from that scratch is yet marked formalized.

### Lean progress

The initial `/tmp/tg-c914-gamma-endpoint.lean` audit exits 0: actual symmetric
dilation difference, exact shell norm, full literal Gamma finite-cutoff
Bochner integrability and exact shell pairing are verified. The source uses
the existing normalized physical rayDilate, not a modeled step function.
The full draft now additionally proves Gamma work >= constant/u^2 on (0,1],
uses the actual short interval [eps,2eps], and derives
`a/256 <= eps*||gammaGroundTruncated a eps 1||^2` and norm divergence along
EVERY eps->0+. Those added statements are under audit, not yet verified.
No new production module has been created for C9.14.

Focused endpoint search `/tmp/tg-c914-endpoint-integral-search.json` completed
nonpartial with snapshot coverage, incomplete refresh. It returned the
actual principal-coefficient theorem and sine integrability, but no new
applicable operator endpoint result. Candidate/source statements and proposed
ingredients were inspected.

The extended Lean audit now checks the lower bound and the all-cutoff norm
divergence: its only errors were two algebraic rewrites in the new remainder
proof, subsequently repaired. The new audit adds actual Bochner integrability
of the exact remainder over (0,infinity), using the physical square-root
ground modulus at zero and bounded dilation norms at infinity. These are
integrability certificates, not a numerical optimization program. The
remainder proof and final dependency/foundation audit are still pending.

Mathematical consequence to investigate next: the forced homogeneous term
is an unbounded dilation-generator observable. A source-faithful completion
must retain it as a reference operator with its domain; deleting it cannot
be justified as an arbitrary renormalization. Full Sonin response admission
for the remainder and the exact scalar-source primitive identity are the
next structural obligations. Arithmetic signed energy, Hardy compatibility,
and strict sub-unit control remain open.

### Exact scalar source identification: next conjecture

The corpus search also located `CCMActualHeadGammaAutocorrelationEnergy`.
Its density `ccmGammaTranslationDensity` is the same positive exponential
quotient, and its theorem `integral_ccmGammaTranslationDensity_mul_cosineDefect`
identifies the integral WITHOUT clock division with the Gamma phase-rate
difference. That is not the observable above.

C9.15 conjecture: the full clock-divided scalar multiplier
S(xi)=2 integral_0^infinity (cos(xi*u)-1) gamma(u)/u du equals
2 log(||Gamma(1/4+i*xi/2)||/Gamma(1/4)). The source-based proof attempt is
to use the corpus geometric expansion gamma(u)=sum_n exp(-2(n+1/4)u),
the audited digamma difference series, and differentiation of the integral.
One predicts S'(xi)=-2 integral sin(xi*u)gamma(u)du
=-Im digamma(1/4+i*xi/2). Both expressions vanish at xi=0 after integration.
All interchanges, the imaginary digamma identity, the norm derivative and
normalization must be proved; this is not yet an audited theorem. The
strong operator domain and transport to the actual Hardy carrier remain
separate obligations even if this scalar identity succeeds.

Remainder search `/tmp/tg-c914-remainder-integrable-search.json` is nonpartial
with snapshot coverage and incomplete compiler freshness. Candidates and
source arguments concern other dilation/Laplace objects and supply no
missing Gamma endpoint proof. Lexical Gamma primitive search has no coverage
metadata; its useful hit is the phase-rate Binet identity just distinguished.

### C9.16: distant-clock cancellation test (new conjecture)

Let S_eps=B(0)-B(eps), M_eps=||S_eps||^2, and form the mean-zero
annulus probe Q_eps=S_eps/M_eps-S_(2eps)/M_(2eps). The exact audited
shell pairing predicts <Q_eps,F(u)>=0 for every u>=2eps. It therefore
annihilates every finite prime or continuum ground dilation supported
away from clock zero, independently of its signed coefficients. For
eps<=u<=2eps, its Gamma pairing is exactly
-2a exp(u/2)(exp(-u)-exp(-2eps))/M_(2eps), with one sign.
A structural lower bound on this short-window integral should prove
divergence even after adding arbitrary distant-clock ground terms.
This is a stronger joint-source obstruction conjecture, not yet a
Lean theorem. Its intended positive replacement is the retained
homogeneous reference plus the admitted exact Gamma remainder, not
deletion of Gamma or retirement of route TG.

C9.15 focused search is partial (filter_and_judge unfinished), snapshot
coverage, refresh incomplete because the background indexer runs.
Useful exact corpus ingredients: `digamma_eq_integral_gauss`,
`integrableOn_digammaGaussIntegrand`, and
`hasDerivAt_log_norm_Gamma_vertical`. A scratch proof now extracts the
actual sine source from the imaginary Gauss integrand under u->2u,
including its normalization; no result from that draft is audited yet.

C9.16 paper calculation strengthened: the normalized probe has
||Q_eps||^2=1/M_eps-1/M_(2eps)<=1/(a eps). On [eps,3eps/2],
-<Q_eps,F(u)>=(2a/M_(2eps))*exp(-u/2)*(1-exp(-(2eps-u)))
is bounded below by a fixed positive constant for eps<=1/2. The
Gamma weight is bounded below by a constant/eps^2 on this interval,
and all later clocks vanish against Q_eps. Hence its Gamma pairing
has magnitude >=constant/eps. Cauchy-Schwarz would then force
||K_(eps,R)f_a+W_eps||^2>=constant*a/eps for EVERY W_eps annihilated
by Q_eps and every R>=2eps, with no bound on W_eps. This is a
structural separation from distant clocks, not a claim about RH.
Exact annulus pairings, cutoff integral restriction and the norm
identity still need formalization before this stronger result is claimed.

C9.14 closure: targeted production audit exits 0 with empty diagnostics.
All fifteen public foundation queries exit 0 and use only propext,
Classical.choice and Quot.sound. Umbrella wired. Index exits 0 and all
fifteen declarations are present. Global lint exits 1 on the same twelve
unrelated unreachable leaves recorded in `/tmp/tg-c914-lint.log`; none
belongs to this change. P2 positive proof moved to P3, explicit bounded
Gamma candidate closed in P5 with that survivor. No RH conclusion.

C9.16 search `/tmp/tg-c916-annulus-cancellation-search.json` is nonpartial
with snapshot coverage and incomplete refresh. Useful hits are existing
physical ground covariance/transport statements (and the just-added
C9.14 leaf); no pre-existing mean-zero Gamma annulus theorem was found.
The proposed generic ingredient set was not accepted as a proof.

C9.15 first scratch audit identifies the literal imaginary Gauss kernel
correctly. Two presentation issues in sine integration (imCLM projection
and explicit scaling lambda) were repaired. A subsequent audit accepted
the sine integrability and exact integral normalization; the remaining
log-derivative conversion exposed class-instance conversion goals rather
than a mathematical gap. The next audit uses `convert!` to compare
instances, adds an integrable Gamma envelope, the full cosine-symbol
Bochner integral, local derivative domination, and equality with the
normalized Gamma log modulus via the common derivative and value at zero.
The complete C9.15 draft remains unverified in `/tmp/tg-c915-gamma-symbol.lean`;
no C9.15 production module or theorem is claimed yet.

C9.15 now has a complete paper proof in
`2-fully-proven/tg-gamma-clock-log-modulus-source.md`. The new analytic
step is an integrable positive envelope w(u)=u gamma(u) below 1/2 and
w(u)=gamma(u) above it. It dominates both the cosine primitive and all
frequency derivatives in a fixed frequency neighborhood. This allows
differentiating the full integral, not just a finite-cutoff expression.
The final equality follows from equal derivatives and the normalization
at zero. The current combined scratch audit includes that exact identity.

Next response construction, once this scalar source weld is audited:
the existing monomial-transfer energy argument applies to any bounded
operator commuting with the literal dilation resolvent and parity maps;
the existing nuclear proof uses precisely that property and the actual
Taylor columns. The Gamma finite remainder operators should satisfy
these commutations directly under their strong integrals. C9.14 ground
convergence would then make their actual time-band actions Cauchy in
Schatten one. Fourier reflection exchanges the two dilation directions,
so the symmetric remainder should admit the full response pair. This
is a precise proposed extension of corpus theorems, not an assertion
that source-specific prime-polar theorems already apply to Gamma.

C9.15 combined scratch reached only one remaining unknown identifier in
an absolute-value simplification; the full mathematical argument and all
other declarations elaborated without further errors. The repaired source
is now `formal/GaloisForLFunctions/RHTower/SoninGammaClockSymbol.lean`,
wired into the umbrella and undergoing the required targeted production
audit. Seven public declarations have /tmp foundation queries prepared.
Do not treat this module as finally audited until the process exits 0.

C9.16 can avoid normalization denominators by using
Q=M_(2eps) S_eps-M_eps S_(2eps). Its exact squared norm should be
M_eps M_(2eps)(M_(2eps)-M_eps), and its pairing with F(u), for u>=eps,
should be -2a M_eps exp(u/2)(exp(-u)-exp(-max(u,2eps))). This is
nonpositive and vanishes for u>=2eps. Restricting to [eps,3eps/2]
gives the joint-source escape argument while retaining all arbitrary
distant-clock coefficients. This equivalent scaling is a proof
simplification, not a change of the conjecture or a search for sharper
constants. The C9.16 statement remains unformalized.

C9.15 targeted production audit exits 0. The complete Gamma log-modulus
identity, absolute symbol integrability, full derivative and sine source
normalization are verified, with two nonfatal tactic suggestions and no
errors/warnings. Seven public foundation queries and indexing are running.
C9.16 first exact physical probe draft is `/tmp/tg-c916-gamma-annulus.lean`;
it has not been audited and is not a production module. It starts from
the actual B_a covariance and aims at the full distant-clock no-go with
the exact C9.14 principal/remainder completion as positive survivor.

C9.15 closure: final targeted leaf audit exits 0 (two nonfatal tactic
suggestions, no errors or warnings). All seven foundation queries exit 0
with only propext, Classical.choice and Quot.sound. Umbrella wired; index
exits 0 and all seven declarations are present. P2 moved to P3. Global
lint running. The full scalar Gamma primitive identity is now closed;
its actual Sonin functional calculus, the unbounded reference domain,
the full remainder response and the Hardy gate are not thereby proved.
C9.16 exact probe/distant-clock annihilation/local response/norm draft is
under audit in `/tmp/tg-c916-gamma-annulus.lean`. No C9.16 result claimed.

C9.15 global lint exits 1 on thirteen unrelated unreachable leaves: the
previous twelve plus ThetaTailPositiveBalancePrimitive. No C9.14/C9.15
finding. Exact list in `/tmp/tg-c915-lint.log`; no unrelated leaf changed.

C9.16: the first exact probe audit exits 0, including its full local
symmetric response and exact norm. The native prime-polar extension
then had one remaining definitional goal `0 = 0 u` in the Bochner
integral; it was repaired with reflexivity. The current audit adds the
actual finite Gamma pairing and nonnegative local work, with finite
Bochner integrability proved from the literal density and dilation orbit.
Next: prove work >=a^2/36 on [eps,3eps/2], integrate to a^2 eps/72,
use ||Q||^2<=32a^3 eps^3, and apply Cauchy-Schwarz to Gamma plus the
actual prime-polar source. Full paper proof is now in
`2-fully-proven/tg-gamma-distant-clock-separation.md`. No C9.16 module
is in production; all ongoing code is `/tmp/tg-c916-gamma-annulus.lean`.

C9.16 native prime-polar annihilation and the exact finite Gamma work
pairing now elaborate. The latest analytic audit had only the scalar
normalization a^2*4*9=a^2*36 left after clearing denominators; it was
closed by ring. The combined scratch now additionally derives the
Cauchy-Schwarz inverse-cutoff energy lower bound and norm divergence
for arbitrary prime-cutoff functions, arbitrary two continuum upper
cutoff functions and every Gamma upper cutoff tending to infinity.
This whole combined audit is pending; no joint divergence theorem is
claimed formalized yet.

C9.17 response search `/tmp/tg-c917-gamma-response-search.json` launched
for the exact admitted remainder. Proposed next construction: build its
finite strong-integral operators, prove the literal dilation/parity
commutations, use the exact monomial energy law and actual Fourier
Taylor columns to get Schatten-one Cauchy convergence, and transport
the symmetric limit through the full response pair. Retain the full
unbounded homogeneous reference; do not infer its domain or an RH
sub-unit bound from remainder convergence.

2026-10-04 — C9.16 combined scratch audit exits 0, including joint
energy residue and cofinal norm divergence for arbitrary native prime
and continuum cutoff functions. The production leaf is now
`SoninGammaDistantClockSeparation.lean`, wired and under its final audit.
Eleven public foundation queries are prepared. No RH conclusion; this
forces retention of the homogeneous Gamma reference in this concrete
raw-source assembly.

C9.17 deep search completed nonpartial with snapshot coverage and
incomplete refresh. Its proposed dilation-symmetry ingredient set did
not supply the needed Gamma response producer. Exact corpus proofs in
SoninPrimePolarGroundNuclear and SoninPrimePolarFullResponse were
inspected: their private generic ingredients use monomial dilation
commutation, Fourier/reflection commutation and self-adjointness. The
Gamma finite symmetric remainder should satisfy these, but a direct
application of the current source-specific theorems would be invalid.
A focused lexical ground/nuclear search is checking available generic
statements before implementing the actual missing producer.

2026-10-04 — C9.16 CLOSED. Final leaf exit 0, empty diagnostics; all eleven
foundation queries exit 0 with only standard foundations; index exit 0 and
all eleven public declarations verified. Global lint exit 1: thirteen
unrelated unreachable modules (RoutePBiasedPrimeProjection replaces the
previous ThetaTailPositiveBalancePrimitive finding). P2 moved to P3,
P5 records exact positive local invariant. Obsolete scratch parts removed.
C9.17 now constructs the actual remainder operator and nuclear completion;
no arithmetic summability, reference-domain or Hardy/sub-unit claim is made.
