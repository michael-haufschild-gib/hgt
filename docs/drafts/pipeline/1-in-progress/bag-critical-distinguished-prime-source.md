# BAG actual critical source: distinguished primes

Route: complete signed physical BAG cubic. Continuation01ac.

Hard target remains signed o(N/log(N)^2) cancellation of the full projected
transverse action, not a fixed-scale representation. The corpus's existing
rational dilation and six-zeta identities use local coefficients supported
on valuations >= -1. The actual critical source is differentiated and
square-sieved. Transfer of those identities requires proving its coefficients.

Corpus basis: ChiRamanujanCriticalFiniteAtoms, ChiRamanujanPrimeOnlyAtoms,
ChiRamanujanFiniteRationalAtoms, ChiRamanujanFinsuppTrace. Search
/tmp/bag-critical-local-source-search-01ac.json inspected: partial reranking
deadline, complete65721/65721 source inventory, background refresh incomplete,
compiler mostly source-only/pending. All20 candidates and20 source arguments
plus proposed ingredients inspected; the broad query drifted to unrelated
Galois decomposition. Lexical localDilation query10575 found the exact
definition and complete all-shift sum theorem; both verified in source.
No mathematical absence is inferred from the search.

Conjecture: writing U_d for normalized full d-torsion averaging, the actual
finite critical prime source is exactly

    sum_(p in P prime) log(p)*(U_p-U_(p^2)) * product_(q in P prime, q!=p) (delta-U_q).

Reason to test: U_p*U_(p^2)=U_(p^2), so (delta-U_p)*(delta-U_(p^2))=delta-U_p.
Differentiating the damped factor at zero gives log(p)*U_p, whose square-sieved
version is log(p)*(U_p-U_(p^2)). This is a proposed source identity, not yet a
Lean theorem. Prove exact equality for all integer Fourier coefficients,
then for the actual finite Fourier test/lifted physical action. Do not infer
pointwise atom equality merely from a covered-band multiplier identity.

Next attack after matching: derive the correct signed rational/cone trace
with all distinguished-prime placements, then determine which cancellations
survive the physical profile and both literal contraction projectors.
An uncoupled old six-zeta trace cannot be substituted without this proof.
No local trace, signed saving, or RH result is claimed here.

## Full shifted local trace conjecture

Let c_z(i) be the existing coefficient: 1 for i>=0, -z/(1-z) at -1,
zero below. For ALL integer a,b,c and 0<z<1, conjecture

    sum_(i,j in Z) c_z(i+a)c_z(j+b)c_z(i+j+c) z^(i+j)
      = z^(-c)*c_z(a+b-c)/(1-z)^2.

Paper mechanism: sum j by the corpus's localDilation_hasSum after translation
j->j+b. The row vanishes unless i=b-c. Its sole surviving value gives the
formula. Prove absolute full-pair summability first: bounded third coefficient
times the product of two shifted weighted coefficient sequences, each a
translated geometric sequence plus one atom. This avoids an unjustified
iterated sum. Scratch /tmp/bag-shifted-cubic-01ac.lean is in development.

The normalized local coefficient of U_p-U_(p^2), as predicted by the source
conjecture, is z*c_z(i+1) at z=1/p: z on i>=-1 and -z^2/(1-z) at -2.
The full finite-source match remains to prove. If the trace formula passes,
use all distinguished-prime placements; do not substitute the unshifted
six-zeta trace. No physical cancellation conclusion follows yet.

Core shifted-pair summability and exact HasSum now pass scratch15263. The
proof uses the complete pair sum, not a conditional iterated sum. Extra
support classification, distinguished-slot formulas and unconditional
critical-prime/finite-prime forms are being audited. The first-slot tagged
value predicted by the formula is z/(1-z)^2; the third-slot tagged value is
-z/(1-z)^3. Thus unchanged unshifted orthogonality is the wrong transfer.
These are full shifted valuation traces, not yet physical growing-test bounds.

Actual finite-source scratch6949 reaches the all-integer Fourier identity:
differentiate the product of square-sieved prime factors, whose zero values
are 1-I_(p divides n) and derivatives log(p)*(I_(p divides n)-I_(p^2 divides n)).
Finite atom limits then identify the exact critical source, including zero
and uncovered frequencies. Three definitional-elaboration errors remain in
that scratch; no source-match theorem is claimed as audited yet.

Next checkpoint: source scratch10665 passes with an empty log after those
definitional fixes. ChiRamanujanShiftedCubicTrace production15708 passes with
an empty log, including full summability, exact zero classification, tagged
slot values, unconditional critical primes and every finite prime set.
ChiRamanujanCriticalDistinguishedPrime is in its production audit.
P2:bag-critical-source-shifted-trace records both dependency-closed proofs
and the remaining source-to-rational/profile gaps explicitly.

## Next conjecture: weighted shifts retain a finite diagonal correction

Lexical weightedLocal search inspected all15 hits; six relevant BAG entries
lead to ChiRamanujanWeightedCubicLocal and ChiRamanujanWeightedRationalTrace.
The full local weighted decomposition and HasSum were read. Other hits are
unrelated constitutive-observer declarations. No absence inference.

For complex c_z, set h=z/(1-z). Its exact first difference is conjectured

    c_z(t+1)-c_z(t) = -h*1_(t=-2)+(1+h)*1_(t=-1).

Use 1+h here for the identity at EVERY complex z; replacing it by
(1-z)^(-1) requires z!=1, satisfied by every actual prime reciprocal.

After translating i,j, three distinguished-slot shifts reduce the weighted
trace to c_z(i)c_z(j)c_z(i+j+k)x^i y^j, with k in {-2,-1,0,1}.
The difference formula leaves only FINITELY MANY diagonal pairs, since
i,j>=-1 on the first two coefficient supports. Thus derive the weighted
shifted Euler factors from weightedEuler plus the exact diagonal correction,
retaining complex Mellin weights. For k=1 the proposed correction is

    -h^3/(x*y)-h*(1+h)*(x^(-1)+y^(-1)).

This is not yet a Lean theorem. Prove the coefficient and finite-diagonal
identities, then the full weighted HasSum; do not assert a Mellin/prime-net
interchange. In parallel logical order, still prove the literal rational
node grouping of the all-frequency distinguished source. These are the
next tasks towards the actual growing-profile signed cancellation.

Weighted third-slot conjecture now proved: scratch86201 and production37262
pass; the latter log is empty. ChiRamanujanWeightedThirdShift retains both
complex Mellin weights and has an unconditional theorem for every prime and
all real frequencies. Its complete difference is supported on three pairs.
The three other shift patterns are not automatically covered by that theorem.
The earlier source and all-shift real leaves passed all13 standard-axiom
probes87231 and index63528; lint7342 has35 unrelated unreachable modules.
Weighted four-name axiom88278 and final lint/index audits are pending here.

## Next exact weighted identities (paper derivation; Lean still open)

Let W_k=sum_(i,j) c_z(i)c_z(j)c_z(i+j+k)x^i y^j, h=z/(1-z),
S0=1-h*(y/x+x/y), S1=x+y-h*(y^2/x+x^2/y). The coefficient first
difference predicts

    W_(-1) = W_0-h^2*(x^(-1)+y^(-1))-(1+h)*S0,
    W_(-2) = W_(-1)+h*S0-(1+h)*S1.

Prove each through the finitely supported diagonal difference, then combine
with the proved W_1 correction. For nonzero x,y, translating first two
coordinates of a general shifted trace gives x^(-a)*y^(-b)*W_(c-a-b).
Actual distinguished-prime placements have a,b,c in {0,1}, so these FOUR
k values cover every placement, including coinciding distinguished primes.
Do not drop coincident labels before proving their physical projector match.

Literal rational grouping route: push every actual atom to the finite group
ZMod(rad(P)^2). Candidate local coefficients come from delta-U_p and
U_p-U_(p^2); Chinese remaindering assembles them. Their finite Fourier
coefficients must match the audited all-integer source identity; finite
Fourier injectivity can then give exact grouped rational node weights.
This is a proposed proof mechanism, not an audited match. Also prove each
individual distinguished multiplier on the covered physical band is
log(p)*1_(n=p), so literal contractions correspond to equality of the
distinguished labels before transferring any trace. These next tasks retain
the actual source instead of assuming the rational six-zeta correspondence.

## Final01ac audit checkpoint — C28.56ag.8

All three arithmetic leaves pass production and all17 public declarations
pass standard-axiom audits. Weighted axiom88278 passes; final index48316
verifies all25 declarations across the four01ac leaves and one import each.
Final lint98092 has35 unrelated unreachable modules, no new-leaf/proof-debt
error; global lint is not clean. P2/P3:bag-critical-source-shifted-trace and
frontier C28.56ag.8 are current. All owned processes terminal and completed
scratch sources removed; logs/search JSON retained. The next exact weighted
identities and literal source matching above remain OPEN. No signed saving,
uniform growing-profile estimate or RH producer was proved. Goal ACTIVE.

## continuation01ad — remaining weighted placements and physical labels

Previous turn classified as progress: four audited leaves changed the actual
source and trace frontier, without a cubic saving. Mission remains an
unconditional Lean RH proof/refutation through BAG. Current source and
C28.56ag.8 revalidated. Search86824 is running with ChiRamanujan module filter.

This turn proves the remaining weighted offsets by finite diagonal correction,
then translates all three distinguished slots, including coincident labels.
It also targets the individual distinguished multiplier on the actual covered
band so literal contractions can be moved to prime labels rigorously. Both
steps address the signed source/profile cancellation route; no estimate or
reduced-rational grouping is assumed. Global growing cancellation, moments,
moving cofactors, common-height self-return and RH remain open.

Search86824 finished: partial filter/judge malformed JSON, full65733/65733
inventory, refresh incomplete and compiler mostly source-only/pending.
All20 candidates and20 source arguments plus proposed ingredient set inspected.
It finds the relevant shifted/local/weighted sources; the axis proposal is
not itself the physical projector match. Exact weightedThirdShift lexical
query returned definition and decomposition, both revalidated in current source.
No mathematical absence inferred. Scratch weighted-all-shifts01ad now proves
finite diagonal HasSums and uses the coefficient predecessor identity to
derive W_(-1),W_(-2); first Lean audit92885 is running.

Core scratch81751 passes after fixing explicit zpow-ofNat normalization and
coefficient predecessor cases; no mathematical conjecture failed. Removed
three redundant convert/try-rfl warnings. The scratch now also contains the
translation of arbitrary three-slot shifts, four-offset Euler selector,
and unconditional all-prime/all-finite-prime Mellin-weighted HasSum for all
distinguished placements (Fin2 labels); these additions await their audit.

Second scratch /tmp/bag-distinguished-labels-01ad.lean is in development audit
42215. It defines each distinguished multiplier entry, proves nonnegativity,
uses the actual all-source covered-band identity to kill each composite entry,
and evaluates every prime entry individually. Target unconditional finite-band
subtype theorem and exact equality of the existing physical projector with
distinguished-label exclusion. No production leaf added this continuation yet.

Node-grouping search97782 completed with partial text-retrieval interruption,
full65736 inventory, refresh incomplete and mostly source-only/pending compiler
metadata. All20+20 hits and proposed ingredients inspected. It finds
sum_filter_reducedModulus_eq, an exact residue-to-reduced-denominator bijection,
and literal torsion Fourier sums. These may support the finite critical match.
The positive-damping infinite Ramanujan weight Euler formula was read and
cannot be used at zero damping without a new argument. Mathlib ZMod.dft_dft
and binary ZMod.chineseRemainder source checked for the finite Fourier route.
No absence inference or analytic-limit shortcut is made.

Label production87443 passes with empty log: every individual distinguished
entry equals its own prime logarithm on the covered band, and the EXISTING
two-contraction projector acts exactly by distinguished-label exclusion.
Weighted development17530 had only two function-eta simplification errors in
the zero/one offset cases; corrected explicitly, and the complete new leaf is
in production audit. Source arithmetic and all-placement proofs had no other
diagnostics. P2:bag-weighted-distinguished-cubic records both exact proofs.

For subsequent node grouping, exhaustive source search found actual character
CRT compatibility in HyperKloostermanRootNumber and
ReducedFrequencyMobiusAliasCollapse, beyond the broad search hits. Read those
lemmas before reconstructing CRT character normalization from scratch.

## Next conjecture: exact critical grid mass

Let R=rad(P), Q=R^2, and group EVERY actual critical prime-only atom modulo
one on the grid k/Q, k in ZMod Q. For each retained prime p define

    d_p(k)=1_(p^2 divides k)-p^(-1)*1_(p divides k),
    t_p(k)=p^(-1)*1_(p divides k)-p^(-2).

Conjectured exact grouped mass:

    G_P(k)=sum_(p in P prime) log(p)*t_p(k)*product_(q!=p) d_q(k).

On ZMod(p^2), the complete Fourier multipliers of d_p and t_p should be
1-I_p(n) and I_p(n)-I_(p^2)(n). Finite CRT plus the VERIFIED all-frequency
critical source identity should identify G_P with the literal grouped atoms.
The required arbitrary-finite CRT already exists: ZMod.prodEquivPi and
ZMod.prodEquivPi_apply in Mathlib/Data/ZMod/QuotientRing.lean, source read.
It is a ring equivalence to all prime-square coordinates; no inductive
reconstruction of CRT is necessary. Actual character compatibility is
GaloisForLFunctions.RHTower.HyperKloosterman.stdAddChar_crt in
HyperKloostermanRootNumber (namespace source verified). Check its API in
a scratch probe before use. ZMod.dft is a linear equivalence and dft_dft is
the exact inversion formula. No numerical grid evaluation is proposed.

Predicted classification after proving the mass identity: G_P vanishes if
the reduced denominator has squared factors at TWO distinct retained primes.
For a squarefree reduced denominator d dividing R, write
A_P=product_p(1-1/p), m_P(d)=product_(p divides d)(-1/(p-1)),
L_P=sum_p log(p)/p. The predicted mass is

    A_P*m_P(d)*(L_P-log(d)).

At a unique squared prime, only that distinguished term survives. This is
paper reasoning from the proposed local factors, NOT an audited node theorem.
It would explain both the new valuation -2 stratum and the corrected signed
logarithmic coefficient. Prove the literal grouping first; do not substitute
this formula into the physical Mellin action on conjectural evidence.

## Final01ad checkpoint — C28.56ag.9

Two production leaves pass: ChiRamanujanWeightedDistinguishedCubic77712 and
ChiRamanujanDistinguishedPrimeLabels87443, empty logs. All21 public declarations
pass axiom25745 with standard axioms only. Index30505 passes, all21 API entries
and single imports verified. Lint75464 has33 unrelated unreachable modules,
no new-leaf/proof-debt error; global lint is not clean. P2/P3:
bag-weighted-distinguished-cubic and frontier C28.56ag.9 are current.
All owned processes terminal; completed01ad scratch sources removed, logs
and searches retained. Next active conjecture is the literal grid mass above.
No physical signed saving or RH result is claimed. Goal ACTIVE.

## continuation01ae — exact local product source

Previous weighted-placement/label results move the source-transfer frontier,
but give no signed saving. Current attack remains the critical grid mass.
Search20154 /tmp/bag-critical-grid-search-01ae.json is nonpartial, with all
65744/65744 files inventoried; refresh remains incomplete under the background
indexer and compiler metadata mostly pending/source-only. Torsion Fourier
orthogonality and phase additivity are the useful retrieved ingredients;
no absence inference is made.

Refined paper proof: use local coordinates k_p in Fin(p^2) and the rational
node sum_p k_p/p^2. Its Fourier phase factors without CRT inverse coefficients.
Local weights d_p=delta_0-p^(-1)1_(p divides k_p) and
t_p=p^(-1)1_(p divides k_p)-p^(-2) have precisely the established local
Fourier multipliers. Finite product summation gives the entire candidate
source. Both actual and candidate sources are torsion of order rad(P)^2;
finite Fourier injectivity then identifies their grouped nodes, including
zero and repetitions. Normalized local weights must subsequently match
the already proved shifted valuation coefficients. This is a dependency-
closed paper mechanism, not yet an audited Lean source identity.

Search91212 /tmp/bag-grid-growing-transfer-search-01ae.json is nonpartial,
65751/65751 inventory, refresh incomplete and compiler mostly pending/source-only.
All20 candidates and20 source arguments plus proposed ingredients inspected.
Current WeightedRationalTrace and RationalCubicTrace read: their finite
prime-support cuts restrict BOTH positive and negative valuations to P.
The actual grid plus all integer lifts instead restricts denominators; its
numerators can contain primes outside P. Thus a direct substitution of the
finite lattice trace would drop actual numerator cofactors. No absence is
inferred; this exact domain distinction must be preserved in the next full
profile transfer. The all-positive-rational theorem in the existing corpus
requires sigma>1 and is untagged, so it does not itself close the critical,
distinguished, growing-profile problem.

Next source-derived conjecture, not yet Lean-audited: evaluate the ACTUAL
normalized distinguished-label cone trace at balanced critical Mellin weights.
For a finite prime set S write A=product_p(1-1/p), L=sum_p log(p)/p.
Apply the already audited all-integer shifted local trace to all triples
of distinguished labels, retaining p!=r and q!=r (p=q is allowed).
At the r-prime the local coefficient is c(-1)=-1/(r-1); at p and q
the coefficients are 1. The tagged z factors give the predicted exact sum

    -A * sum_(r in S) log(r)/(r-1) * (L-log(r)/r)^2.

This is strictly negative when S has at least two primes. It is a finite
valuation-lattice identity, not a physical cubic estimate. Prove this exact
signed formula before claiming the label projector kills the balanced cone.

For the actual denominator-restricted rational sum, the omitted numerator
cofactors supply outside-S geometric Euler factors. In the absolute half
planes Re(s),Re(t)>1 their product should be
zeta(s)*zeta(t)*product_(p in S)(1-p^(-s))*(1-p^(-t)).
Thus the predicted balanced double-pole coefficient is A^2 times the
displayed finite trace, not zero. No critical full unordered HasSum is
asserted: its integer-pair subseries already has positive harmonic absolute
mass whenever S is nonempty. A complete proof must retain the actual
physical test and justify its cancellation of, or contribution from, this
pole and the full near-cone region. This calculation changes the next
attack from a blind finite-trace substitution to the exact tagged/cofactor
Mellin source and its physical pole pairing. It does not rule out BAG.

## Final01ae checkpoint — C28.56ag.10

ChiRamanujanCriticalGridSource (489 lines,25 public declarations) passes
production97363 with an empty log. All25 pass axiom73382: standard axioms
only. Index61870 passes; exact API module/name rows and single import checked.
Lint37187 has36 unrelated unreachable modules, no new-leaf/proof-debt error;
global lint is not clean. Actual grouped-node product, full local-coordinate
bijection, direct all-node weight, shifted local normalization and two-square
vanishing are closed. P2/P3:bag-critical-prime-square-grid and frontierag.10
record this closure. No numerical computation, full build or resource hack.

Mathematical conjecture succeeded. Development errors were explicit Lean
coercion/parameter inference and tactic syntax, all resolved; no premise was
added. The predicted negative balanced labeled trace and full numerator-
cofactor Mellin pairing above are NEXT, not audited results. Signed growing
cubic saving, moments, moving cofactors, common-height self-return and RH
remain open. Goal ACTIVE. All owned jobs terminal; completed scratch sources
removed, logs/search JSON retained.

## continuation01af — signed labeled cone and full cofactors

Previous grid-source turn classified PROGRESS: actual grouped masses and
shifted local normalization are now authoritative Lean theorems, without a
signed cubic saving. Current source and both physical label exclusions were
revalidated. This turn attacks the displayed negative balanced trace formula,
then the numerator-cofactor correction needed for the full actual source.
The point is to determine the signed pole that the physical growing test must
handle, not to remove cofactors or assume balanced cancellation. The actual
near-cone/growing-profile bound, moments, moving cofactors, common-height
self-return and RH remain open. Corpus search37838 completed and is being
inspected before new code.

Search37838 (shifted labeled traces) and search95868 (coprime Dirichlet
series) are nonpartial with complete inventories65755 and65757. Background
refresh remains incomplete; compiler metadata is mostly pending/source-only.
All20 candidates,20 source arguments and proposed ingredients in each were
inspected. Current mathlib source supplies the principal-character L-series,
finite Euler factor, continuation and residue; it does not supply the new
tagged physical cancellation. No absence conclusion is used.

The balanced-label conjecture succeeds. ChiRamanujanBalancedLabelTrace has
13 public declarations; production3062 passes with empty log. Its complete
signed finite-prime HasSum is exactly the displayed negative sum of squares,
strictly negative iff two distinct primes are retained. All13 axiom probes
show standard axioms only; the combined probe script had an unrelated
universe-inference error in a new mathlib API probe, now corrected, so its
successful terminal audit remains pending. One umbrella import is wired.

Next proof under development: the actual coprime numerator Dirichlet factor
is the principal L-function at the retained-prime level. Combine its residue
with the explicit weighted distinguished-label Euler polynomial, prove
continuity at (s,t)=(1,1), and obtain the full mixed-source double-pole
coefficient. The finite-prime part must retain its s,t dependence throughout;
simply multiplying a constant balanced trace would not establish this claim.
The rational reindexing and physical pole pairing remain explicit debts.

The cofactor scratch first audits exposed Lean inference/performance issues,
not a mathematical counterexample: subtype-coercion rewrites need explicit
finite-product functions; product-limit targets need prodMk_nhds; broad
unfolding/continuity automation and concrete HasSum multiplication hit the
default heartbeat limit. The proof is now factored into local continuity
steps and an abstract multiplication lemma, with no resource-limit change.

Reindex search5904 finished PARTIAL (source_retrieval interrupted), complete
inventory65761, incomplete background refresh and semantic coverage unmeasured.
All20 candidates and20 source arguments were inspected, plus its proposed
ingredient set. Relevant hits: positiveRationalValuations,
valuationCoefficient_coprime_sub, rationalCubic_eq_valuation and natural
factorization uniqueness. Its Deninger-ray proposed ingredient is unrelated
and rejected. Direct current source supplies rationalOfValuations_natural,
rationalOfValuations_injective, positiveRationalEquiv, Finsupp filtering and
Nat.factorizationEquiv. Partial search is not used as absence evidence.

Next reindex construction: split a prime-valuation vector into retained and
outside-prime filters. In the denominator-supported sector every outside
valuation is nonnegative, so its rational product is an actual positive
integer n. The existing rationalOfValuations_natural plus injectivity recovers
its natural valuations, proving coprimality with the retained-prime level.
Conversely a retained vector plus positive coprime n has exactly those
coordinates. This gives the required bijection without suppressing numerator
primes. Extend it to pairs and the literal grid coefficient before making
any claim about the full physical pole pairing.

## Final01af checkpoint — C28.56ag.11

Both conjectures succeed: exact balanced-label negative square trace, and
its full mixed-source numerator-cofactor joint residue. BalancedLabelTrace
(190 lines,13 public) production3062 and CofactorPole (308 lines,18 public)
production30300 both pass with empty logs. Combined axiom6422 passes all31
with standard axioms only. Index92350 and all31 exact API entries/single
imports verified. Lint73204 has25 unrelated unreachable modules, no new-leaf
or proof-debt finding; global lint not clean. P2/P3
bag-balanced-labeled-cofactor-pole and frontierag.11 are current.

This is progress on the actual source obstruction, not a physical cubic
saving. The next conjecture is the explicit mixed-valuation/coprime-numerator
bijection described above, followed by equality with the complete literal
rational grid source. Only after that transfer can the proved pole be paired
with the actual growing physical profile and entire near-cone remainder.
Growing moments, moving cofactors, common-height self-return and RH remain
open. Goal ACTIVE. All owned jobs terminal; completed scratch sources cleaned,
logs/search JSON retained. No computations, full builds or resource hacks.

## continuation01ag — complete rational/cofactor reindexing

Previous turn classified PROGRESS: the balanced trace and completed mixed
source pole are audited. Their physical transfer is still open. Current
cofactor definitions and source status were revalidated. This turn proves
that every denominator-supported positive rational has exactly one retained
valuation vector and positive coprime numerator cofactor, then transfers the
complete two-coordinate source. Search44715 is running. The intended bridge
retains arbitrary numerator primes; no finite-support substitution is allowed.
Physical pole/near-cone cancellation, growing moments, moving cofactors,
common-height self-return and RH remain open. This is the next necessary
source identification for attacking the full physical signed action.

Search44715 completed nonpartial, complete inventory65764, no errors;
background refresh incomplete, compiler mostly pending/source-only. All20
candidate lemmas,20 source arguments and proposed ingredients inspected.
Useful direct hit: cpow_rationalOfValuations transports BOTH complex powers
without assuming imaginary frequencies. The proposed private prime-product
lemma is already mediated by public rationalOfValuations facts; no attempt
to invoke a private theorem across modules.

The mixed valuation bijection and denominator characterization have passed
all but one elementary cast step in scratch audits. That step is now written
as an explicit congruence instead of rewriting its own exponent. The same
scratch now contains the paired equivalence, both full complex character
identities, a rational source defined from its actual shifted coefficients
(not as a pullback), and its full HasSum over denominator-supported rational
pairs. Development audit is running. Exact identification with the literal
finite grid, and physical growing-profile cancellation, are still debts.

RationalCofactors development10471 and production62049 pass with empty logs;
source is wired once. It proves the complete paired rational HasSum with no
numerator support restriction. The grid follow-up search61153 completed
nonpartial with complete inventory65766, incomplete background refresh and
mostly pending/source-only compiler metadata. All20 candidates,20 arguments
and proposed ingredients inspected. Public BAG prime-valuation inversion and
mathlib factorization suffice; unrelated ClassFieldTheory/float suggestions
are not imported or used.

Grid development28979 passes local valuation/base/tag identities: for EVERY
positive a, v_p(a/R^2)=v_p(a)-2 and the normalized local factors equal the
literal integer divisibility weights. The full grouped-source sum and
vanishing outside the prime-square denominator grid are now in scratch
proofs under audit. Remaining issue in the first global audit was inferred
subtype-coercion rewriting; explicit product/sum functions address it.
No mathematical premise or heartbeat change was introduced.

## Audited01ag checkpoint — C28.56ag.12

Grid production15658 passes with empty log, after development87600. Together
with rational production62049, all40 public declarations pass axiom13267
using only propext, Classical.choice and Quot.sound. Index56173 passes; all40
exact API rows and one import per leaf checked. Lint78719 has24 unrelated
unreachable modules, all inspected; no new-leaf or proof-debt finding.
P2/P3 bag-rational-numerator-cofactors and frontierag.12 record the full proofs.

The rational source now retains every positive coprime numerator, both
complex powers and both literal label exclusions. Its exact grid attachment
includes every positive lift, including zero residue, and proves vanishing
outside the prime-square denominator grid. This is PROGRESS on the source
transfer, not a signed physical saving or RH closure.

Physical-pairing search31155 completes nonpartial65773, no errors; all20
candidates,20 source arguments and ingredients inspected. Suggested
coords_symm/ABHN pole cancellation is unrelated and rejected. Actual
primeGaussianCubicOffDiagonal is COMPLEX: its norm must be small, not merely
its real part. The full transverse Fourier profile retains the r integral,
entire physical-window Mellin line and all integer lifts.

Mellin-pairing search5344 completes nonpartial65775, no errors; all20
candidates,20 source arguments and ingredients inspected. Background refresh
incomplete and compiler source-only/pending, so no absence claim. Current
mathlib mellinInv_mellin_eq supplies one-variable inversion only after
Mellin convergence, vertical integrability and continuity are proved.
Height-profile inversion has a different domain; sesquilinear Fourier
symmetry does not prove physical pole cancellation. Relevant Perron source
arguments justify sum/integral exchange by summable integrals of norms.

Next conjecture: the ACTUAL positive-cone restriction
Phi_N(x,y)=Fourier(bagCubicPhysicalSchwartz)(x,y,-x*y) admits absolutely
integrable two-variable Mellin inversion on positive real lines. On lines
Re(s),Re(t)>1 it may then be paired with the complete rational HasSum to
retain the exact signed Euler/cofactor expression. The full polynomial cone
restriction, its Mellin boundary behavior and every exchange must be proved;
no stationary product approximation, assumed vertical integrability or
zero-residue shortcut. The established negative residue is nonzero.
Near-cone/tail coupling, other frequency sectors, growing moments, moving
cofactors, common-height self-return and RH remain open. Goal ACTIVE.

Search29038 (Schwartz Mellin vertical integrability polynomial composition)
completes nonpartial65775 with no errors; all20 candidates,20 source
arguments and ingredient sets inspected. Its proposed step from integrable
positive-axis Mellin norm to vertical integrability is INSUFFICIENT: these
are different integrals. Sonin/Cap statements also carry extra function-space
premises not established for the actual physical profile. Do not invoke them
as automatic vertical convergence.

Useful current toolchain mechanism: SchwartzMap.compCLM takes temperate
growth of a map e and a polynomial upper bound for the input norm by
1+norm(e). For e(x,y)=(x,y,-x*y), the first two coordinates give the lower
norm control, and all coordinates are polynomial. Thus this should construct
the COMPLETE cone restriction as a Schwartz function, without replacing the
hyperbolic transition by its stationary value. For Mellin inversion on
Re(s)=c>1, Re(t)=d>1, the proposed log profile is
g(u,v)=exp(c*u+d*v)*Phi(exp u,exp v). Its mixed derivatives are finite sums
of exponential weights times polynomially weighted derivatives of Phi.
Schwartz decay controls each positive end, and c,d>0 control each negative
end, including mixed quadrants. Establish this as a two-variable Schwartz
map, then Fourier inversion gives the full Mellin inversion and vertical L1
bound. Use EuclideanSpace R (Fin 2) for Fourier, not the max-norm product
with an invented inner-product instance. No Lean proof of this new step yet.

The next interchange has a precise majorant: on the two vertical lines,
each rational source term has the same norm as at real exponents c,d.
Its sum is finite by criticalRationalCone_hasSum; the vertical Mellin norm
is integrable by the proposed log-profile proof. Their product justifies
the sum/integral exchange. This would give the actual positive-cone pairing,
not the full signed physical estimate; near-cone and other sectors remain.

## continuation01ah — full physical cone Mellin pairing

Previous01ag is PROGRESS: complete rational source/grid transfer is audited.
Current source revalidated the actual Schwartz amplitude and unconditional
cutoff family. This turn attacks the missing analytic pairing, beginning
with the literal polynomial-cone restriction and its logarithmic Mellin
profile. Search11570 is running. No pole cancellation or RH claim follows
from source identification alone; the complex signed physical norm remains
the target. No analytic convergence hypothesis may replace its proof.


Both proposed analytic steps now PASS: PositiveQuadrantLogSchwartz proves
all mixed logarithmic derivative decay, two-variable inversion and vertical
integrability on real parts (2,2). ChiPrimeGaussianCubicConeMellin proves the
full cone restriction Schwartz and its exact rational HasSum/integral pairing
by a summable integrable norm majorant. The unconditional actual cutoff
family preserves original sharp/smooth error and all integer-lift summability.
No tensor product or stationary replacement enters. This is PROGRESS on the
hard physical source transfer, not a cancellation estimate.

Production71522/10862 pass empty; axiom93534 passes all25 with only propext,
Classical.choice and Quot.sound. Index69307 passes, all25 API rows and one
import per leaf verified. Lint59769 has28 unrelated unreachable modules;
all inspected, no new-leaf or proof-debt finding, global lint not clean.
P2/P3 bag-full-physical-cone-mellin-pairing records dependency-closed proofs.
Search11570/90276/31282 completed nonpartial/no errors; all candidates,
arguments, ingredients and generated ideas inspected. Background refresh
incomplete; source/compiler freshness mostly pending/source-only. The
valuation-shift ingredient does not represent additive transverse defect.
No general Mellin line, canonical positive-axis identity, continuation or
contour displacement claimed.

Next conjecture: complete bilinear Fourier correlations of the literal
prime-square base/tag grid retain a nontrivial transverse-defect law. Derive
that law symbolically under BOTH label exclusions before attempting to
couple the proved nonzero negative cone residue to the near-cone contribution.
The finite-grid source and public local Fourier transforms, not an unproved
stationary ansatz, determine the coefficients. Full signed complex norm
saving, growing moments, moving cofactors, common-height self-return and
RH remain open. Goal ACTIVE.


## continuation01ah — exact local transverse survivor

ChiRamanujanTransverseDefectGrid now proves all-test product pushforward
for both base and restricted-tag factors on F_p, and its exact literal
prime-square attachment. The base map exhausts every p-divisible node;
all other base coefficients vanish. The ENTIRE prime-square base/base sum
at physical prime frequency equals -(1-1/p), not zero. Local orthogonality
cannot be used to discard the transverse source. Strong positive survivor:
the negative centered zero atom plus every nonzero defect mass as one exact
operator. All four product-test placements are retained. Full tag support
outside the subgroup is not covered by these restricted-tag identities.

Production86909 passes empty; axiom89006 passes all17 with standard3 only;
index49770/API17/import1 checked. Lint58246 has33 unrelated unreachable
modules, all inspected; no new-leaf/proof-debt finding, not globally clean.
P2/P3 bag-transverse-defect-grid-law and frontier ag.14 current.
Search84667 nonpartial65786 and88818 nonpartial65794/noerrors, search76592
PARTIAL65789 with retrieval interruption/runtime reranking deadline. All
available20+20, ingredient sets and ideas inspected; no absence claim.
Szego residualProfile and Ramare energy decomposition do not solve the
physical defect. Existing KloostermanBilinear norm q is fixed-modulus only.

Assessment: cone Mellin pairing closes a real analytic gap; the new local
law eliminates a false cancellation mechanism and identifies its surviving
signed operator, but yields NO growing signed estimate. Next attack must
retain the actual profile H(a,b) separately in both tangential coordinates.
At nonzero defect delta its exact local source is p^-2 sum_(a!=0)H(a,delta/a);
zero defect retains the two full axes and intersection. Finite Fourier
expansion produces Kloosterman inverse fibres. Prove this complete-profile
law and its lifted R^4/label-excluded source attachment, then the signed
physical estimate; do not substitute a product test or fixed-period average.
Growing moments, moving cofactors, common-height self-return and RH open.
All owned jobs terminal. Completed scratch sources removed; audit logs and
search JSON retained. Goal ACTIVE.
