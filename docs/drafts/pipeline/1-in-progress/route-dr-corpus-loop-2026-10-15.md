# Route DR: corpus-only research loop

Goal: unconditional Lean proof of `RiemannHypothesis`. Status: IN PROGRESS.

User constraints: local Lean corpus only; no external novelty audit, numerical experiments,
added axioms, admitted proofs, conditional RH capstone, full builds, or heartbeat increases.
Existing unrelated worktree changes are preserved.

## Plan

1. Reconstruct DR's actual frontier from indexed declarations and current Lean sources.
2. Formulate and attack an exact arithmetic cancellation conjecture.
3. Finish dependency-closed mathematical proofs before formalizing survivors.
4. Audit new modules with `lake env lean`, targeted dependencies only, and formal lint.
5. Return to the missing cancellation theorem until unconditional RH is proved.

`update_plan` is not exposed in this session; this card is the persistent task ledger.
Serena is configured for Python only and cannot extract Lean symbols; use source reads/patches.

## Current evidence

- `RegularizedLogZetaAbscissa.lean` proves RH iff the literal coefficients
  `(Lambda(n)-1)/log(n)` converge to the right of one half. This is an equivalence,
  not an unconditional convergence theorem.
- `LogZetaDirichletDivergence.lean` proves the unregularized positive log-zeta
  series diverges at every point with real part below one.
- `PaperPrimePowerDefect.lean` identifies the difference from the regularized
  prime-indicator row as `1/k` on each proper prime-power layer. Its partial sums
  have growth exponent at most one half.
- `PaperPrimeRegularizedIdeal.lean` proves the difference has essential norm
  exactly one half. Compact pole subtraction does not make either raw row compact.
- Initial hybrid searches report complete inventory but stale/source-only compiler
  coverage. Search hits require source inspection and direct Lean verification.

## Live questions

Can source arithmetic force signed partial sums of `(Lambda(n)-1)/log(n)` to have
growth exponent one half? `[OPEN CORE]`: no such unconditional producer identified.

User steering: stay on DR's genuinely missing theorem. Do not replace it with
boundary optimization or another equivalence. Prime-square abscissa formalization
was dropped before any Lean edits: it does not solve the source cancellation.

The hard target remains `ConvergesRightOf logZetaRegCoeff (1 / 2)` with no assumed
RH, zero-free half-plane, positivity certificate, or cancellation bound.

Current mechanism under attack: whether finite Dirichlet coefficient square
energy can control the actual untwisted arithmetic partial sums after the pole is
subtracted. Random-character/averaged estimates cannot be silently specialized
to the literal character. Search and attack that specialization explicitly.

External novelty/significance remains unaudited by explicit user instruction.

## Direct audit

`lake --old env lean /tmp/hgt_dr_frontier_audit.lean` exited 0. The audited
equivalence has only `propext`, `Classical.choice`, and `Quot.sound`; its target is
the ordinary `RiemannHypothesis` about zeros of `riemannZeta`, not a surrogate.
The scratch file printed the exact definitions of RH and `ConvergesRightOf`.
The subsequent current-source audit
`lake --old env lean GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean`
also exited 0, with no diagnostics. No project Lean files were edited in this
cycle; no new module or umbrella wiring was needed. RH remains unproved here.

## Source reconstruction and attempted proof mechanisms

Current Lean sources give the following exact arithmetic model. Write

    E(N) = psi(N) - N + 2 gamma,
    F(N) = sum_(m=1)^N log m - sum_(d=1)^N floor(N/d) + 2 gamma N.

Then `F = floorSummatory E`, `|F(N)| <= 24 sqrt N` for positive N, and

    E(N) = sum_(d=1)^N mu(d) F(floor(N/d)).

Evidence: `PsiDefectSqrtBound.lean` and
`CCMFUSuzukiMobiusDivisorAbelProducer.lean`. The latter already proves a
smoothed uniform bound for this exact signed source is equivalent to RH.
Repackaging that bound as an assumption would not advance DR.

Attempt 1: transfer coefficient square energy from a phase average to the
literal Dirichlet polynomial. Verdict: BRIDGE with missing control, not proof.
`DirichletPolynomialSincEnergy.lean` retains an exact signed off-diagonal sinc
term. Discarding it is unjustified; the unsigned envelope loses the cancellation.

Attempt 2: bound every quotient block of the Möbius recovery separately.
For `N < d <= 2N`, `floor(2N/d)=1`, hence that block is exactly

    (2 gamma - 1) * (M(2N) - M(N)).

Here `F(1)=2 gamma-1>0`. A square-root/subpower estimate for that block already
requires dyadic Mertens cancellation. Telescoping dyadic blocks recovers the
full Mertens bound. Verdict: BRIDGE, not a reduction of the hard problem.
This does not disprove the block estimate; it disqualifies treating it as an
elementary consequence of the source envelope. Keep the full coupled sum.

Attempt 3, active: exploit the exact Tatuzawa–Iseki relation before absolute
values:

    E(N) log N + sum_(k<=N) Lambda(k) E(floor(N/k))
      = sum_(n<=N) mu(n) log(N/n) F(floor(N/n)).

The corpus proof of `abs_psiDefect_selberg_core` bounds the right side absolutely
and obtains O(N), insufficient for DR. The current investigation asks whether
the signed convolution has a source-specific energy identity that prevents
growth faster than square root. No nonnegativity of the mixed term is assumed.
An arbitrary causal function has no such cubic-energy sign; the actual
arithmetic relation between E, Lambda, and F must enter any proof.

The follow-up corpus search returned `MobiusRenewalEnergySign.lean`. Its exact
finite-source identity is `renewalPairing = Gamma(r)*shiftedMoment - energy`,
and its pairing is eventually strictly negative for r in an interval above one.
This rules out an unqualified positive-renewal-feedback argument. It is a
different pairing from the Chebyshev/Tatuzawa expression above: no identification
between them has been proved, so it does NOT decide the latter's sign.

Concrete next candidate (not a theorem): retain the actual Chebyshev pairing

    B_sigma(X) = sum_(m<=X) E(m) *
      (sum_(k<=m) Lambda(k) E(floor(m/k))) / m^(1+2 sigma).

Ask whether, for every sigma>1/2, there is a cutoff-independent C_sigma with

    B_sigma(X) >= -C_sigma *
      (1 + sum_(m<=X) E(m)^2 / m^(1+2 sigma)).

This is a source-specific lower-bound conjecture, not asserted positivity.
It could fail through arbitrarily negative normalized mixed energy. Its proof
would still have to be combined with signed control of the right side of the
Tatuzawa identity; the O(N) absolute estimate is explicitly insufficient.
First attack: expand the two sides using the literal relation between Lambda
and the increments of E; test whether the proposed coercivity is circular or
whether the full source supplies a new cancellation identity. Do not assert an
RH implication from this lower bound alone.

Immediate algebraic attack on this candidate: `Lambda(k)=E(k)-E(k-1)+1`
for k>=1 (including k=1, since E(0)=2 gamma). Therefore its inner convolution
is exactly

    F(m) + sum_(k<=m) (E(k)-E(k-1)) E(floor(m/k)).

The first part already has the favorable bound

    |sum_(m<=X) E(m) F(m) / m^(1+2 sigma)|
      <= 24 * (sum_(m<=X) E(m)^2/m^(1+2 sigma))^(1/2)
            * (sum_(m>=1) m^(-2 sigma))^(1/2),

by the source envelope and Cauchy–Schwarz. The unresolved part is the actual
cubic increment term, together with its coupling to the signed Möbius source
on the other side of Tatuzawa. Neither changing the weight nor improving 24
addresses it. This expansion identifies the next exact term to attack without
asserting that a lower bound for B alone would prove RH.

Anti-theatre audit: no new scientific theorem yet, and no unconditional RH proof.
Useful output is a directly verified DR target and elimination of two unsupported
inferences. Do not count the already-known square-root source bound or an RH
equivalence as a new result. Next work stays on the signed global source term.

## Local resonance audit and multiplicative-kernel test

DR remains active. No failure below retires DR or weakens its unconditional
target. External searches and numerical experiments remain excluded by the task.

Write `B(s)=divisorSourceEntire s`, `Z(s)=zeta(s)`, and

    H(s) = B(s)/(s Z(s))
         = (-Z'(s)/Z(s) - Z(s) + 2 gamma)/s.

The second equality holds away from 0, 1, and zeros of Z, using the exact source
identity in `DivisorSourceEntire.lean`. For Re(s)>1, H is the Mellin transform of
the literal step error E. Define the differential transport

    T(H) = -H' - (Z'/Z) H.

The exact conjugation identity is

    T(H) = -(B/s)'/Z,
    T^k(H) = (-1)^k (B/s)^(k)/Z.

These are identities on the zero-free punctured domain, not assertions that
this domain contains the half-plane needed by DR.

At a zero rho != 0,1 of multiplicity m, put u=s-rho and
`Z(s)=c u^m+O(u^(m+1))`, c!=0. Then

    H(s) = -m/(rho u) + O(1),
    T(H)(s) = m(m-1)/(rho u^2) + O(1/u).

Thus the leading double pole cancels at every simple zero, regardless of its
real part. More generally `T^k(H)` has pole order at most m: its numerator is
analytic. For m=1 no repeated transport produces a higher-order pole. For
0<=k<m the leading coefficient is
`(-1)^(k+1) m(m-1)...(m-k)/rho` at order `u^(-k-1)`.
This is a dependency-closed local paper calculation, not a Lean theorem or a
global energy estimate. Verdict: the proposed leading-log coercivity mechanism
is FALSE; the source-specific integrated energy conjecture remains OPEN.
No conclusion about the existence of off-line zeros follows from this audit.

A separate exact kernel test explains why a low-negative-index replacement
cannot be applied indiscriminately to the literal log-regularized coefficients.
For indices i,j=0,...,r-1, take n_i=6^(i+1). Then n_i*n_j has two distinct
prime factors, hence Lambda(n_i*n_j)=0, and

    logZetaRegCoeff(n_i*n_j-1)
      = -1/((i+j+2) log 6).

For a nonzero real vector c, its quadratic form is

    -(1/log 6) integral_0^1 t (sum_i c_i t^i)^2 dt < 0.

The strict inequality follows because a nonzero polynomial is nonzero on some
open subinterval of (0,1). Thus this kernel has negative subspaces of every
finite dimension. Paper proof only; no new project Lean module was added.

Positive survivor: for finite indices n_i>=2, the differentiated kernel obeys

    sum_ij c_i c_j (Lambda(n_i*n_j)-1)
      = sum_p log p (sum_{i: n_i is a positive power of p} c_i)^2
        - (sum_i c_i)^2.

Only primes appearing in the finite index set occur. Unique factorization
proves the identity. The form is nonnegative on `sum_i c_i=0`, and the
composite ray above makes its negative index exactly one when nonempty.
This does not imply convergence of the prime sum: product indices n_i*n_j
with both factors >=2 only expose higher prime powers. Treating that positivity
as control of the missing first-prime contribution would be another unjustified
bridge. Verdict: BRIDGE with an explicit loss of the unresolved component.
No claim of scientific novelty is made for these elementary kernel facts.

Corpus follow-up also found actual source autocorrelation results in
`MobiusDivisorCriticalSourceAutocorrelation.lean` and
`MobiusDivisorCriticalCorrelationTailSign.lean`: the second signed lag moment is
strictly negative, and negative correlations occur beyond every finite cutoff.
These concern `criticalAbelLogProfile`, not the Chebyshev mixed energy B_sigma.
No identification of the two is asserted. Pointwise nonnegative correlation is
therefore not an admissible replacement for a proof about the full signed form.

The remaining simple-zero residue of the transport is concrete. If
`a=Z'(rho)!=0` and `b=Z''(rho)`, then

    Res_rho T(H) = (b/a - 2 gamma - 1/rho)/rho.

This keeps the source's derivative phase, which the cancelled double pole
discarded. Next attack: determine whether actual arithmetic supplies a sign
or global pairing identity for this residual phase. Generic positive Laplace
source arguments are insufficient: `DivisorSourceResponseSign.lean` already
proves negative real logarithmic response cofinally far to the right.

Audit: RH is still unproved; no new scientific theorem has been established.
The current work isolates exact failure mechanisms, but formalizing those
routine identities would not meet the requested mathematical progress gate.
Next cycle must attack the remaining source-specific phase or the full signed
energy, rather than optimize source constants or add another conditional RH
interface. The paper-to-Lean phase is pending a nontrivial proved survivor
that advances this obstacle.

## Active scope correction: Kummer-root topology

The user's latest instruction fixes the hard problem explicitly:
**certify a zero-free half-strip through Kummer-root topology, rather than
direct analytic zero estimates.** This supersedes the proposed next step about
the Chebyshev source energy or residual analytic phase. Earlier abscissa work
does not constitute progress on this topological certification problem.

Current source evidence:

- `XiDyadicDescentLevelUniversalityLaw.lean` identifies each root depth with
  `RHLadder k`, Euler-germ extension, half-band roots, local circle monodromy,
  and actual chart deck triviality. Its sixteen conditions are equivalent
  realizations, not sixteen independent restrictions.
- `FarFieldAnchor.lean` provides unconditional trivial deck charge in Re(s)>1
  and transport along already-certified deformations. It does not construct a
  deformation through the half-strip.
- `QuadrantSeamConservation.lean` disproves the generic terminal dichotomy:
  compact conjugate-pair islands can retain odd local charge, and an even seam
  collision can split into two odd charges. Symmetric aggregate cancellation
  cannot certify the local root needed here.
- `XiDerivativeKummerCollision.lean` gives a finite alternative: a common
  nontrivial root degree for xi and xi' excludes a zero because its two orders
  are consecutive. `XiDerivativeKummerRootRH.lean` proves the converse under
  RH, so assuming that root pair would merely assume an equivalent target.

Active plan:
1. Locate the strongest existing source-specific topological extension theorem
   and identify precisely what remains unconstructed.
2. Conjecture and attack a source-specific construction that trivializes local
   Kummer holonomy without presuming zero-freeness of the swept domain. It must
   distinguish individual islands and handle all finite zero multiplicities.
3. Complete the paper construction before Lean. Do not replace the producer
   by another conditional certificate or a direct analytic zero estimate.

The mathematical goal remains active and unmet. No project Lean changes have
been made during the exploratory audit above.

### Verified Kummer foundation and next construction audit

The scratch audit `lake --old env lean /tmp/hgt_dr_kummer_audit.lean` exited 0.
It checked `exists_farHalf_root`, `rhLadder_iff_germ_extends`, and
`rh_iff_all_farHalf_germs_extend_all_levels`, and printed the exact definitions
of `RHLadder`, `rightHalf`, and `farHalf`. The unconditional germ theorem and
the RH equivalence depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The final direct current-source audit
`lake --old env lean GaloisForLFunctions/RHTower/GermExtension.lean` also exited 0
without diagnostics. This verifies the consumer and Euler anchor, not the
missing extension.

Additional source audit: `ProKummerLinearThresholdSelection.lean` already proves
that finite linear-depth action of the actual local formation charges is
equivalent to RH. `ProKummerHolonomyCapacity.lean` reconstructs the integer charge
from its full root-of-unity tower and gives its exact finite-depth recurrence.
Thus decay of `exp(2 pi i m/d)` toward 1, or compatibility across root degrees,
does not kill m. Every fixed nonzero integer m has those properties. A new
capacity bound or a claim of coherent punctured-domain roots would need a real
producer; neither is a proof by itself.

Concrete construction candidate to investigate: continuation of the actual
Euler-side finite Kummer covers with preservation of their local sheet-return
permutations on each half-strip window. Finite Euler factors are units on the
strict-right region. To use them, one must construct a comparison with the
actual Xi root cover that controls possible new branch cycles during
continuation. Mere equality of the far-field topological class, ordinary
continuation of xi itself, or unit normalization supplies no such comparison.
Verdict at present: BRIDGE, with the source-specific comparison still OPEN.
Do not formalize this open comparison as an assumption and call it progress.

Next substantive task is that comparison or a different explicit construction
of the same Kummer gluing, retaining local charge and every finite multiplicity.
No return to direct zero estimates, Chebyshev energy optimization, generic
symmetry drainage, or another equivalent RH interface is authorized by this
plan. No new scientific theorem has been established in this cycle; the verified
topological foundation and precise failed inferences are preparation for the
still-unsolved construction.

## Kummer source comparison cycle: the dilation correction

Previous goal turn classified as progress: current Lean checks established the
correct Kummer consumer and replaced the misidentified analytic target. This
cycle's corpus search found `EulerTruncationRigidity.lean`, which already proves
the free finite Euler towers and their exact mismatch with additive approximants.
Thus the proposed generic finite-Euler comparison is REDISCOVERED as an open
interface; its missing comparison has not been constructed.

`PairedEtaRootContinuationBoundary.lean` supplies a different actual arithmetic
source: `etaPair = C * zetaPoleUnit`, with an explicitly known auxiliary zero
on Re(s)=1, and the normalized family

    J_h(s) = (exp(h(1-s))-1)/(h(1-s)),
    poleDilationSource h s = J_h(s) * zetaPoleUnit s.

The first formula is used for h>0 and Re(s)<1, where its denominator is nonzero.
At h=log 2, the source is etaPair/log 2. The paper construction below identifies
the actual Kummer covers throughout the open half-strip, including at any
hypothetical zeros of zeta. It does not assume those zeros absent.

For h>0 put z=h(1-s). On Re(s)<1, Re(z)>0 and |exp(-z)|<1, so both z and
1-exp(-z) lie in the principal logarithm's domain. Set

    L_h(s) = z + Log(1-exp(-z)) - Log(z),
    r_(h,k)(s) = exp(L_h(s)/2^k).

All these functions are holomorphic on Re(s)<1, r_(h,k) never vanishes, and

    exp L_h = exp(z)*(1-exp(-z))/z = J_h,
    r_(h,k)^(2^k) = J_h,
    r_(h,k+1)^2 = r_(h,k).

For the actual cyclic covers y^(2^k)=zetaPoleUnit(s) and
y^(2^k)=poleDilationSource(h,s), the maps

    (s,y) -> (s,r_(h,k)(s)*y),
    (s,y) -> (s,y/r_(h,k)(s))

are inverse continuous maps, preserve the base, and commute with every deck
scalar. This is an explicit isomorphism of the branched covers, not just an
equivalence of root-existence assumptions. It also applies at zeros because
the correction root is a unit. The proof is dependency-closed: the exponential
identity, the principal-log domain checks, and the two displayed inverse maps
are all that is needed.

Verdict on dilation as a charge-removal mechanism: FALSE. Every local Kummer
obstruction of the genuine pole unit survives every positive dilation on this
half-strip. Positive survivor: the explicit coherent cover transport above,
which permits using the absolutely convergent paired source without confusing
its auxiliary boundary divisor with the unresolved Xi divisor. Formalize this
exact transport as a checked source construction; do not count it as a new
scientific result or as the missing zero-free certificate. The RH-producing
gluing remains open after it.

### Verified coherent transport; active gluing problem unchanged

The positive survivor is now formalized in
`formal/GaloisForLFunctions/RHTower/PairedEtaKummerCoverTransport.lean` (221 lines)
and imported by `RHTower.lean`. Its actual root surfaces are subspaces of the
open half-strip times C, so the result includes hypothetical branch points.

- `exp_dilationLog` and `dilationRoot_pow` prove the explicit source identity.
- `dilationRoot_succ_sq` proves coherence of the correction roots.
- `pairedEtaCoverHomeomorph` unconditionally identifies the actual pole-unit
  root surface and the normalized paired eta root surface at every dyadic level.
- `pairedEtaCoverHomeomorph_base` fixes the base point.
- `pairedEtaCoverHomeomorph_squareLevel` commutes with the continuous squaring
  transitions.
- `pairedEtaCoverHomeomorph_deckMul` commutes with all deck rotations.

Verification: direct current-source command
`lake --old env lean GaloisForLFunctions/RHTower/PairedEtaKummerCoverTransport.lean`
exited 0 with no diagnostics after the final source edit. A separate `/tmp`
copy of that exact source with six `#print axioms` commands also exited 0;
the source identity, root law, coherence, homeomorphism, squaring compatibility,
and deck compatibility all use only `propext`, `Classical.choice`, `Quot.sound`.
`scripts/formal_tools.py lint` exited 0 (`formal lint passed`; existing large-file
warnings elsewhere). `scripts/formal_tools.py index` exited 0 and refreshed
the documented API/gap/overview outputs. No full or umbrella Lean build ran.

The further deep corpus query `paired eta partial sums root monodromy homotopy`
completed without partial retrieval. It returned finite paired-eta sums,
derivative formulas, additive gap decompositions, and convergence estimates;
no checked producer of trivial sheet return was found among these hits.
Compiler coverage remains mostly pending/stale, so retrieval does not certify
those candidate declarations. No external search or numerical experiment ran.

Verdict: the dilation charge-removal conjecture is FALSE; its positive survivor
has both a complete paper proof and checked Lean proof. The survivor is an
explicit source comparison, not a new scientific result or a zero-free
certificate. In particular, neither having unit correction roots at all levels
nor transporting the actual covers proves the covers have trivial monodromy.

The active hard problem remains: construct the actual Euler-marked Kummer
sections across the half-strip, or force their sheet return to be trivial on
every isolating loop, at all dyadic levels. The new module allows that problem
to be worked on with normalized paired eta without altering its charge. Further
unit normalizations and convergence estimates alone do not discharge it.
Do not mark RH solved or the research goal complete, and do not pivot to the
earlier abscissa/Chebyshev interpretation of DR.

## Actual paired-source root construction: convolution-root attempt

Previous goal turn: PROGRESS. It added and verified the explicit coherent
source-cover transport, but did not create a zero-free certificate. The next
cycle must construct actual source roots, not further correction units.

Candidate mechanism: represent the paired source divided by s as the Laplace
transform of its positive logarithmic interval density. If this source had
positive convolution roots at every dyadic level, their transforms would
produce an actual Kummer tower. This is stronger than an analytic root and
must be attacked before relying on it.

The density is `exp(-sigma*x)` times the indicator of the union of intervals
`[log(2n+1), log(2n+2)]`. Its first interval starts at zero and its first gap
is `(log 2, log 3)`. Exact candidate obstruction: for a fractional root
exponent alpha in (0,1), the Euler-marked inverse Laplace kernel begins as

    (x^(alpha-1) - alpha*(x-log 2)^(alpha-1))/Gamma(alpha)

on `(log 2, log 3)`. The second term has a negative singularity at log 2;
therefore the canonical root cannot be a positive measure. This would expose
the signed local kernel required by actual Kummer gluing, while distinguishing
failure of positive roots from failure of holomorphic roots.

OPEN CORE of this attempt: justify the canonical local convolution-root
formula and its applicability to the actual paired eta source, rather than
postulating a generic inverse transform. Corpus audit in progress. No new
Lean theorem is claimed from this candidate yet.

### Convolution attempt: exact failure and anti-theatre audit

The positive convolution-square candidate is FALSE for every exponential tilt.
Its failure has a complete paper proof on
`docs/drafts/pipeline/5-failed/route-dr-positive-paired-eta-root-producer-2026-10-15.md`.
Exponential moments pass to a probability convolution root. Its transform
would consequently square to the actual paired eta transform on Re(s)>0,
contradicting the simple auxiliary zero at `1+2*pi*i/log 2`. This proof does
not assume anything about genuine off-critical zeta zeros.

The corpus already contains the analytic no-go and the moment-inheritance
lemma. It also contains the universal coherent formal coefficient tower and
the squarefree tower's absolute-convergence wall. All four declarations were
checked in a fresh scratch import and axiom audit; exit 0, only `propext`,
`Classical.choice`, `Quot.sound`. The exact `rightHalf` in the paired-source
analytic no-go is Re(s)>1/2, not Re(s)>0; the constructed probability transform
would be analytic on the larger half-plane and hence would violate it.

The positive survivor is the already verified coherent cover transport and
the existing unique formal arithmetic tower. Their paper and Lean status is
recorded on the failed producer card. No duplicate Lean wrappers were added.
The suggested local signed-kernel formula remains an unformalized exploratory
formula, not a claimed continuation theorem or zero-free certificate.

Anti-theatre: no new scientific theorem in this cycle. The exact candidate
was tested and rejected, and its stronger existing parent results were
identified. Avoid repeating probability roots, merely formal coefficient
roots, generic symmetry propagation, or unit normalization as if any supplied
the missing analytic section. The next construction must address the actual
Euler-marked section's local sheet return, without assuming its triviality or
substituting an absolute-convergence optimization problem. DR and the RH goal
remain active.

Final verification for this cycle: the direct current-source command
`lake --old env lean GaloisForLFunctions/RHTower/PairedEtaRootContinuationBoundary.lean`
exited 0 without diagnostics. No project Lean source was changed this cycle;
there was no full/umbrella build and no reason to rerun the unchanged lint gate.
The three corpus searches completed without partial retrieval, but their
compiler coverage was mostly pending/stale; the explicit Lean audits, not
search ranking, support the theorem claims above.

## Transverse arithmetic deformation of the actual root divisor

Previous turn classification: progress in testing a concrete construction,
without a new scientific theorem. Positive probability roots were rejected;
the genuine Kummer continuation target remains unchanged.

New mechanism under investigation: use the Hurwitz parameter as a transverse
arithmetic deformation, rather than multiply the source by another unit.
Formally, `partial_a zeta(s,a) = -s*zeta(s+1,a)`. At a hypothetical right-strip
zero rho of zeta(s,1), the derivative in a at a=1 is nonzero because
Re(rho+1)>1. Thus the two-variable divisor is smooth in the transverse
parameter even when the s-slice zero has high multiplicity.

The prospective root construction would have to control genuine continuation
in this two-variable source family and its restriction back to a=1. It is not
enough to infer trivial monodromy from transversality: the model `a-s^m`
already has a smooth total divisor and an arbitrary-multiplicity slice. The
Euler anchor is also not automatically uniform in a. Both points will be
audited against actual Hurwitz-source results before any new Lean theorem.

OPEN CORE: construct an arithmetic-compatible transport that rules out a
nontrivial slice Kummer character, rather than assume a joint root or a
divisor-avoiding homotopy. This cycle is investigating the exact source
deformation and its possible obstructions; no zero-free conclusion is claimed.

The actual local zero graph is now formalized, with no root-existence premise:
`XiHurwitzAnchorZeroGraph.exists_analytic_hurwitz_zero_graph` (namespace
`RHTower`) gives A(rho)=1, analyticity, the exact local zero-graph equivalence,
and simple shift zeros along the graph. Its source dependencies are the new
compact normal-convergence bound, local normal-series C1 theorem, joint
Hurwitz regularity, and the actual anchor implicit-function theorem. All five
source modules currently check. Imports were added to their area umbrellas.

The fixed-width root-tube obstruction is written in
`RHTower/HurwitzRootTubePinching.lean` but not yet checked. The exact contact
order identity remains paper-proven and not yet formalized. Neither is being
counted as a completed Lean result. The paper card is
`3-formalized/route-dr-hurwitz-anchor-zero-graph-2026-10-15.md`.

Local corpus searches for normal series, implicit contact order, punctured
power roots, and Hardy zeros were non-partial; compiler coverage was mostly
pending/stale, so all claimed new results rely on direct source checks.
The normal-series argument is a local extension of an existing entire-series
argument, not a new analytic principle. The exact source zero graph is a
verified constraint on DR root gluing, not a zero-free certificate.

### Completed source-deformation cycle

The fixed-width tube obstruction and the full positive survivor now both
check from current Lean source. Exact result:
`RHTower.exists_analytic_hurwitz_zero_graph_with_contact_order` gives the
actual zero graph, transverse shift order one, and
`ord(A-1)=ord(zeta)=ord(Xi)` for every Xi zero, without simplicity.
`RHTower.not_forall_exists_hurwitz_shift_disk_power_root` rules out every
fixed positive shift tube for every root degree greater than one, using
Hardy's existing non-numerical critical-line zero theorem.

The contact proof uses the strict derivative to establish
`zeta(s)/(1-A(s)) -> -rho*zeta(rho+1) != 0`, then removes the quotient's
meromorphic singularity to obtain an analytic unit. This preserves exact
multiplicity rather than merely estimating a neighbourhood radius.

Eight new source modules pass; six final axiom checks report only `propext`,
`Classical.choice`, `Quot.sound`; index exits 0. Repository lint exits 1
solely for three unrelated missing umbrella imports, listed on the formalized
card. Own modules are wired; no unrelated source was changed. Temporary
search/verification files are cleaned up after recording these results.

The no-go card is
`5-failed/route-dr-fixed-width-hurwitz-root-tube-2026-10-15.md`;
the exact survivor is in
`3-formalized/route-dr-hurwitz-anchor-zero-graph-2026-10-15.md`.
DR remains active. This cycle closes a specific false construction and its
positive salvage; it does not close the RH-facing root-section problem.
Next work must produce arithmetic control of the actual slice Kummer
character. Do not replace this with shrinking-tube existence, smoothness of
the total divisor, or another reformulation of root existence.

## Arithmetic distribution versus Kummer descent

Current target remains the actual Euler-marked root section on the right
half-strip. No external searches, numerical experiments, or old research
Markdown were used. The preceding local Hurwitz graph cycle is complete;
this cycle tests an arithmetic mechanism rather than extending that geometry.

Plan: inspect actual distribution and reciprocity source; formulate the
proposed charge-divisibility step; attack it before formalization; preserve
the exact surviving obligation. No new root or zero-free theorem is claimed.

Corpus findings:

- `Hurwitz/PolygammaHurwitzValue.lean`, `hzeta_distribution`, is an additive
  trace identity in Re(s)>1. It is not a multiplicative norm identity.
- `RHTower/XiHurwitzRationalFiberSeam.lean` already identifies normalized
  shifted rational-fibre responses with n^s. Equality of the reflected
  responses on the Xi divisor is explicitly RH-equivalent. It is not an
  available source equality.
- `RHTower/DeningerKummerHasse.lean` separates already-realized local
  currents; it does not realize every sum-zero current or supply a
  comparison to the analytic zeta section.
- `RHTower/XiDyadicDescentLevelUniversalityLaw.lean` already identifies
  each root rung with local divisor divisibility and deck triviality.
  Repackaging one of these as a norm-descent hypothesis would not prove it.
- The deep producer search completed without partial retrieval or errors.
  Its proposed zero-free-strip ingredient set explicitly requires RH.
  This ingredient set is circular for the present task and is rejected.
  Compiler coverage is mostly pending/stale; retrieval is not verification.

Exact candidate tested: binary arithmetic refinement, with its normalized
Euler marking, supplies one additional dyadic root level for the original
anchor rather than merely for the binary norm.

The actual binary identity on the defining half-plane is

    H(s,1/2) = (2^s-1) zeta(s),
    H(s,1/2) H(s,1) = (2^s-1) zeta(s)^2.

It persists wherever these functions are analytically continued. Locally
at any exponent of positive real part away from the pole, 2^s-1 is a
nonvanishing analytic unit: its modulus argument uses |2^s|=2^Re(s)>1.
If the anchor has order m, this norm has order 2m. Its square root therefore
does not provide a square root of the anchor. More generally a d-th local
root of u*f^N, for positive integers d,N and a nonzero analytic germ f,
imposes exactly d | N*ord(f), with u a local analytic unit;
after cancellation this is d/gcd(d,N) | ord(f). Norm degree and root degree
must both be retained. Equal dyadic growth of the two carries no new
divisibility information. This is ordinary local divisor theory, not a new
scientific theorem.

Verdict on the claimed additional level: CIRCULAR. Ordinary norm roots give
no gain; assuming the additional level reinstates the missing anchor-root
condition. This verdict rejects that inference, not DR or the possibility
of a stronger arithmetic theorem using more source structure.

Second pass: the additive trace cannot replace the norm. On a disk about
zero the two analytic units 1 and z-1 have sum z, whose simple zero prevents
even a local square root. This only refutes a general trace-to-root rule;
it is not a counterexample to the complete Hurwitz arithmetic source.
Odd-degree norms avoid losing dyadic charge, but their own roots still need
to be constructed; no such producer has been supplied. The exact positive
survivor is the divisibility cancellation law above, already covered by
local order/root theory. Do not formalize it as purported new RH progress.

OPEN CORE: derive a root level for the original Euler-marked section from
additional arithmetic structure, with a proof of the actual sheet return.
Neither additive distribution, normalized n^s response, norm replication,
global current separation, nor an assumed extra root level supplies this.
The next cycle must test a source-defined operation that changes this
obstruction, before writing more bridge lemmas.

Verification: `lake --old env lean /tmp/hgt_dr_binary_norm_audit.lean`
exited 0. It checked the actual convergent Hurwitz binary norm formula and
the nonvanishing of 2^s-1 for Re(s)>0. Axiom checks for the existing binary
value theorem and exact punctured-root divisibility criterion returned only
`propext`, `Classical.choice`, `Quot.sound`. The meromorphic continuation
discussion above is paper reasoning, not a newly formalized continuation
theorem. No repository Lean source was changed; no full or umbrella build
was run. An initial scratch syntax error was fixed before the successful
audit. No lint or index rerun was warranted for this notes-only cycle.

Anti-theatre / anti-laziness: this cycle produced no new scientific theorem
and no zero-free certificate. Its limited output is rejection of a
circular arithmetic norm-descent step against the actual source. Source
search and existing bridges cannot replace construction. No work was
deferred for difficulty or effort. Keep DR and the RH goal active; do not
spend the next cycle formalizing the elementary divisibility calculation
or expanding the already-complete local graph infrastructure.

## Prime-weight monodromy construction audit

Previous cycle classified as limited progress: the actual binary norm
inference was rejected and the next candidate changed; no RH rung was
proved. Current source checked before relying on the earlier notes.

New card: `route-dr-prime-weight-monodromy-2026-10-15.md` in this directory.
It tests the actual Euler product with coefficients i^Omega(n), after
pole clearing. Its nonintegral character detects any nonzero zeta order
through a nonintegral logarithmic residue. The candidate meromorphic
continuation is RH-equivalent, not supplied by that residue argument.

The finite Z/4 grading has total Euler norm zeta(4s), but each individual
character retains its first prime trace. The four-state determinant only
cancels that trace in the total norm. A regularized individual determinant
recovers the known analytic unit, not the missing continuation. Pole
clearing also changes finite-stage monodromy at 1, which cancels only in
the infinite source; this comparison cannot be silently assumed.

Scratch Lean audit of the exact four-character local polynomial identity
and the meromorphic imaginary-residue obstruction exits 0 with only
standard axioms. No repository Lean source was edited. Full source
continuation remains OPEN CORE. This is a tested BRIDGE, with no new
scientific theorem and no zero-free certificate. Keep DR active and attack
the individual source attachment, not further equivalent criteria.

## Entire pole-counterterm and direct contour audit

Card: `route-dr-entire-pole-counterterm-2026-10-15.md` in this directory.
The source is an explicit entire exponential counterterm times the finite
Euler product, normalized at 2. Every finite source is a unit on Re(s)>0
and has compatible marked dyadic roots. Paper checks give the actual
pole-filled target on Re(s)>1 and at the single point s=1. They do not give
convergence in a neighborhood crossing Re(s)=1.

Current Lean source already contains the Ein--Mertens subtraction and
Mertens product asymptotic. That part is REDISCOVERED. The conjectured
half-plane convergence is BRIDGE, with first-prime continuation still open.
No newly formalized root-convergence or root-gluing theorem was obtained.

Direct contour attack: around a hypothetical isolated zero of order m,
every finite logarithmic derivative has zero period, but the target has
period 2*pi*i*m. Thus the contour-current discrepancy has arclength L1
norm at least 2*pi*m for every cutoff. This conditional statement is
ordinary argument-principle machinery already represented in the corpus,
not a claim that such a zero exists or a proof that the explicit family
fails. It prohibits silently exchanging continuation, the cutoff limit,
and the Kummer return map. Entire pole normalization cannot change this
period. The higher prime-power correction has zero period too.

Anti-theatre / anti-laziness: no new scientific theorem and no certified
half-strip. The normalization repaired a finite-stage mismatch but did not
move the RH frontier. Corpus checking prevented spending Lean work on that
repair as if it solved the target. The actual sheet-return comparison was
attacked directly and remains unproved; difficulty was not used to defer
a known proof step. No numerical computation or external search was used.
No repository Lean file changed, so no lint/index or umbrella build was
run. Searches completed without reported errors; pending/stale compiler
coverage was recorded rather than advertised as formal verification.

Continue DR at the source attachment itself. Any proposed continuation
operation must prove its effect on the integer contour period for the
actual primitive prime source. Neither a new counterterm, a determinant
that removes the first trace, unweighted convergence of high-degree
holonomy, nor an assumed normal family meets this obligation. Keep the RH
goal active; the source conjecture and zero-free half-strip remain open.

## Arithmetic Frobenius root-lift audit

Previous goal turn: limited progress through evidence that changed the
next construction, with no new RH theorem. It tested the explicit entire
pole counterterm and found that contour sheet return retains the original
source attachment problem. This cycle tests an actual cover action instead
of another scalar counterterm.

Card: `route-dr-arithmetic-frobenius-root-lift-2026-10-15.md`.
On the Euler region the marked cube action on w^(2^k)=E is
w |-> w^3/r_(2^k)^2. Continuing it around a zero of order m requires
2^k | 2m. It is automatic at degree 2; at degree 4 its normalizer is the
first missing square root. At higher depth it is equivalent to the preceding
root level, so this does not provide an induction producing new roots.
Verdict on the proposed automatic gain: CIRCULAR. Actual arithmetic global
extension remains BRIDGE, not disproved and not constructed.

Arithmetic p-power action on the cyclotomic stages is present in current
Lean source. That theorem does not identify the action with one on the
actual analytic cover. A continuous complex field/ring endomorphism is
identity or conjugation, so exponent 3 on primitive eighth roots cannot
be obtained that way. Schwarz reflection does exist on real-type sources,
but reverses base-loop orientation while inverting deck labels. Both signs
change, leaving arbitrary multiplicity possible. Do not substitute this
map for the required action over the identity.

Scratch audit exited 0 without warnings: quartic fiber preservation,
involution, normalizer recovery, cubic deck covariance, the exact finite
translation condition, and the continuous coefficient obstruction. Axiom
lists contained only the standard axioms. The broader analytic cover
classification remains paper reasoning; no new formal source extension is
claimed. Initial scratch errors were fixed before the final audit. No
repository Lean edits, full build, umbrella build, lint, or index rerun.
Four corpus searches completed; coverage warnings were retained in the card.

Anti-theatre / anti-laziness: this cycle still produced no new scientific
theorem or half-strip certificate. It rejected a concrete circular
construction, using the actual distinction between arithmetic and analytic
actions. Further classification of the same normalization is not the next
task. DR needs an independently constructed arithmetic operation controlling
the actual monodromy, not a lift defined by a root already assumed to exist.
No work was deferred because it was difficult. Keep the goal active.

## Actual prime-curve vacuum regularity

Previous turn: progress through a checked failure of the Frobenius lift;
the proposed normalization could not create a new root level. Current
cycle tests a smooth finite-energy source at the actual Euler vacuum.

Card: `route-dr-prime-curve-vacuum-regularity-2026-10-15.md`.
For v(sigma)=(p^-sigma)_p in the prime Hilbert space, the paper argument
shows that a C^k germ G matching log zeta(sigma) for all sufficiently large
real sigma must have DG(0)[e_p]=1 for every prime p<=2^k. Therefore no
single C^infinity, hence no holomorphic, Hilbert germ at zero can match
this actual arithmetic curve. This does not assume extension on arbitrary
finite prime packets, and does not exclude singular-vacuum or other
topological source constructions.

The positive survivor is explicit: for each finite k, retain the finite
Euler head p<=2^k and encode the tail in the scalar coordinate x_2 using
p^-sigma=(2^-sigma)^(log(p)/log(2)). The tail begins above power k, giving
a C^k germ with exactly the required real-curve values and vanishing tail
jets through order k. Each fixed finite regularity order is possible;
one smooth vacuum germ is not. Full proof, scope, and derivative control
are in the card. It is paper work, not yet a fully formalized theorem.

Companion draft `route-dr-prime-curve-vacuum-coefficient-work-2026-10-15.lean`
formalizes only the Dirichlet coefficient-separation dependency. The
little-o theorem handles the endpoint n=M. Direct Lean check exits 0;
scratch axiom output contains only standard axioms. No production module
or umbrella changed. Do not call the whole regularity theorem formalized.

Next required work is the actual curve/Taylor coefficient extraction and
the exact finite-C^k positive survivor. The candidate is not retired while
that closure work remains. The paper argument derives from standard
Taylor/Dirichlet/Hilbert machinery; novelty and significance beyond those
parent theories remain unestablished. The requested half-strip is still
uncertified. Keep the full RH-through-DR goal active.

## Exact finite-smoothness survivor verified

Added `RHTower/PrimeCurveFiniteSmoothModels.lean`, namespace
`RHTower.PrimeCurveModel`, and its RHTower umbrella import. Main theorem
`exists_finiteSmoothGerm`: for every natural k, an explicit function on
real ell^2(primes) is C^k on a positive ball about zero and matches
log|zeta(sigma)| on the actual prime curve for every real sigma>1.
The ball radius can be chosen independently of k. The model depends on k.

The tail uses the exact zero extension `(max(t,0))^a`, a=(r+1)log(p)/log(2),
over primes p>2^k. All tail jets through k vanish at zero. Uniform derivative
bounds reduce to summable p^(-2(r+1)) weights; no analytic continuation
or zero estimate enters. The curve itself is in ell^2 for sigma>1/2.
The finite prime head and tail are identified with the full real Euler
logarithm, then with log|zeta| using the actual Mathlib Euler product.

Production direct Lean check exited 0, silent. Three scratch axiom audits
returned only propext, Classical.choice, Quot.sound. Formal lint passed
with repository large-file warnings. No full or umbrella builds. Two new
corpus searches completed partial=false/errors=[]; external searches and
numerical computations were excluded as requested.
Index refresh exited 0. Owned temporary Lean and search files were removed
and absence verified; the earlier active coefficient draft is retained.

Remaining in the active vacuum card: exact derivative functional/norm,
actual-curve Taylor coefficient extraction, and smooth-germ contradiction.
The old coefficient-separation draft remains needed. Do not retire the
candidate or call the full boundary theorem formalized yet. No half-strip
or RH certificate was gained. Standard parent theory explains this positive
construction; scientific novelty remains unestablished. Keep DR active.

## Actual-curve vacuum boundary fully verified

The previous outstanding work is now closed. Added and directly compiled:

- `RHTower/PrimeCurveFiniteSmoothJets.lean`: the explicit finite-C^k
  model has derivative the finite prime reader and norm sqrt(pi(2^k)).
  It also supplies the bounded all-prime reader contradiction and the
  packaged model/identity/derivative/norm existence theorem.
- `RHTower/PrimeCurveTaylorControl.lean`: actual Hilbert prime curve,
  finite truncation, radial Taylor bound, and transfer of actual-curve
  vanishing to a finite Taylor polynomial with the required decay.
- `RHTower/PrimeCurveVacuumRigidity.lean`: finite multilinear expansion,
  prime-frequency isolation, Dirichlet coefficient extraction, the C^1
  endpoint, the sharp norm lower bound, and the full smooth-germ no-go.

Exact final result: a C^k germ on real ell^2(primes), k>=1, matching
log|zeta(sigma)| on the actual vector (p^-sigma) for all sufficiently
large real sigma has derivative value 1 at every e_p with p<=2^k.
Its derivative norm is at least sqrt(pi(2^k)). The explicit finite model
attains that bound. No single C-infinity germ has the matching property.
The proof derives these coefficients from actual-curve agreement; it does
not assume agreement on arbitrary finite prime packets. No continuation
or RH premise enters. The k=1, p=2 endpoint is included.

All new production checks exited 0, silent. Their required object files
were generated for dependency checks. The final scratch axiom audit of
the positive model, Taylor transfer, sharp coefficient theorem, sharp
norm bound, and C-infinity contradiction returned only propext,
Classical.choice, Quot.sound. Formal lint exited 0 with repository
large-file warnings. Index generation exited 0. No full or umbrella build.
The three modules are wired into the RHTower umbrella.

Moved the completed negative candidate and archived coefficient draft to
`5-failed/route-dr-prime-curve-vacuum-regularity-2026-10-15.md` and
`5-failed/route-dr-prime-curve-vacuum-coefficient-work-2026-10-15.lean`.
The positive survivor's construction, derivative, sharp bound, and
attainment are all fully formalized. The original coefficient draft is
superseded by `RHTower.PrimeCurveCoefficient` in the integrated module.

Paper Kummer corollary: a complex-valued smooth source R near zero with
R(0) nonzero and R(v(sigma))^d=zeta(sigma) would yield the forbidden smooth
germ d*log|R|. This corollary has not separately been packaged in Lean.

Anti-theatre: this is a precise exclusion of a proposed source class,
with its sharp positive survivor. It gives no compatible global root
sections or zero-free half-strip. Scientific novelty/significance beyond
standard Taylor, Dirichlet, prime, and Hilbert arguments is unestablished.
Anti-laziness: the actual-curve coefficient link, the sharp endpoint, and
the exact positive classification were completed rather than left as
assumptions. Only this smooth-vacuum producer is retired. DR stays active;
the next unresolved work is arithmetic attachment of Kummer roots with
the singular first trace retained. The RH goal remains active.

Final cached lexical lookup finds `exists_finiteSmoothGerm_with_derivative`,
`truncated_radial_taylor_isLittleO`, and `no_smooth_euler_curve_germ` in
their integrated modules. The lexical output has no partial/coverage
fields; no additional freshness claim is inferred. All 25 owned temporary
source/search/log files were removed by exact path and absence verified.
No owned prime-curve Lean process remains. Persistent state is in the
archived card, live log, production modules, and Serena memory
`route-dr/prime-curve-vacuum-rigidity-sharp-closure-2026-10-15`.

## User correction: work on the actual half-strip obstruction

User explicitly redirected: "certify the half-strip", then "stop this
busywork ... work on the actual hard obstacle to overcome". This controls
the next work. Do not continue auxiliary interpolation formalization,
estimate optimization, generic no-go classifications, or new conditional
RH equivalence modules as a substitute for the arithmetic construction.

The finite vertical-measure candidate remains unfinished in its own card.
Its already checked scratch proof was preserved unchanged as
`route-dr-vertical-convolution-coefficient-work-2026-10-15.lean` next to that
card. Arithmetic gap and finite interpolation are checked; finite-measure
Fourier continuity, genuine Euler-root identification, and escape packaging
are not. The candidate is not retired. No production Lean changes this cycle.

Actual target remains Omega={Re(s)>1/2, Im(s)>0}. Around a hypothetical zero
rho of order m, the degree-d Euler root returns with multiplier
exp(2*pi*i*m/d). Need an arithmetic construction forcing trivial return,
not merely a small multiplier as d grows or a root on the punctured domain.
The singular first prime trace is the unresolved source term; the higher
prime-power terms already extend holomorphically on Omega.

Direct attempted mechanism: simultaneous prime-phase inversion. On Re(s)>1,
the all-prime sign twist has Euler product prod_p(1+p^(-s))^(-1) and equals
zeta(2*s)/zeta(s); the corpus has the exact Liouville Dirichlet identity in
`LiouvilleDirichletSeries.lean`. Since zeta(2*s) has no zero on Omega,
the twist reverses local divisor charge: m becomes -m. An independently
constructed holomorphic realization of this arithmetic twist on Omega
would forbid every positive charge and certify the half-strip. Merely
defining it as the quotient does not do this: the quotient is meromorphic,
and its possible poles are precisely the obstacle.

Paper attack on source-level inversion: write P(s)=sum_p p^(-s) initially
in Re(s)>1. The remaining logarithmic Euler sums H_plus and H_minus,
starting with prime powers k>=2, converge on Re(s)>1/2. The two germs are
exp(P+H_plus) and exp(-P+H_minus), and their product is zeta(2*s).
The regularized Hilbert-Schmidt determinants therefore handle both higher
parts but leave opposite singular first traces. A holomorphic realization
of both first-trace exponentials has NOT been constructed. Assigning it
through a determinant normalization, a line-bundle trivialization, or the
quotient would reinsert the missing no-pole statement. This is an open
construction attempt, not a proved advancement or a newly established
obstruction theorem. Do not spend the next cycle formalizing that identity.

Broad deep corpus search completed partial=false/errors=[]; its semantic
hits were mostly unrelated Euler-characteristic material. Inventory was
complete but many compiler entries were pending/stale; no exhaustive
absence or fresh-compilation claim follows. Targeted current Lean source
confirms the actual prime monodromy residue and the Liouville identity.
No external searches, numerical jobs, or new Lean builds after the scope
correction. RH and the half-strip remain unproved. Keep the goal active.

Anti-theatre: the checked auxiliary draft is not progress on trivializing
actual monodromy. The direct source inversion attempt has an explicit
unresolved holomorphy step and yields no certificate. Anti-laziness: remain
on that arithmetic obstruction (or an actual construction addressing the
same charge), rather than closing incidental formalization tasks.

## User-directed infinite limit on the target half-strip

Latest instruction: "then use an infinite limit that converges only on the
target half-strip and establish that convergence". The finite-factorization
attempt exposed the right domain issue: a finite identity expressing Xi as
products of genuine entire Poisson boundaries propagates globally and
doubles each positive Xi zero order. An infinite locally uniform limit on
Omega need not propagate to the critical-line boundary. Constructing that
limit, with its actual arithmetic attachment, is now the task.

Exact target: construct arithmetic holomorphic Q_N on Omega, without
dividing by Xi or assuming its nonvanishing, such that Xi^2 Q_N tends to Xi
locally uniformly there. Equivalently one can construct compatible actual
Euler Kummer roots there. This target has NOT been proved. Runge division
by Xi, idempotence of the boundary ideal, or normality assumed as a premise
would merely insert the missing result.

Current source checks: DeningerMeyerPoissonMellinFactorization gives the
actual factorization B_f=zeta*M_f and zero annihilation. The exact Xi cap
source and full-jet boundary inclusion already exist. DeningerPreimageContinuous
gives local convergence of the physical Mobius inverse on x>0; it gives no
control at x=0 and hence no Mellin convergence throughout Omega.

Candidate under attack: use finite arithmetic inverse sources with a
cutoff tending to the excluded physical endpoint, and prove local normal
convergence of their scalar Mellin transforms on Omega. Raw Abel-damped
Mobius sums would have the correct reciprocal Euler germ. The unproved
step is removing the endpoint cutoff in the scalar transform. A weighted
Hilbert-space sum can converge for Re(s)>1/2 while evaluation at the
endpoint is unbounded; that convergence must not be presented as the
required scalar limit. No new conditional criterion will be formalized.

Both previously owned searches (sessions 36868 and 91670) are terminal,
exit 0. Their JSON has partial=false and errors=[]; substantial compiler
metadata is pending/stale. The boundary-square search did not yield an
arithmetic factorization producer. The Liouville harmonic search returns
already conditional one-sided criteria; that side direction is not the
current task. No numerical work or external search. No new Lean build or
production edit. The half-strip and RH remain unproved.

### Explicit compensated Kummer limit, still unproved

Use Omega={Re(s)>1/2, Im(s)>0} and s0=2+i. Define the holomorphic
function a on Omega by

    a(s0) = integral_2^infinity x^(-s0)/log(x) dx,
    a'(s) = -2^(1-s)/(s-1).

Omega is convex and excludes 1, so the primitive exists without a zeta
nonvanishing assumption. On Re(s)>1 it equals the convergent integral
integral_2^infinity x^(-s)/log(x) dx. For X>=2 set

    L_X(s) = a(s)
      + sum_{p<=X} sum_{k>=1} p^(-k*s)/k
      - integral_2^X x^(-s)/log(x) dx,
    R_{d,X}(s) = exp(L_X(s)/d),  d>=1.

Every finite-cutoff R_{d,X} is holomorphic and nonzero on Omega. The
root sections are exactly compatible: R_{de,X}^e=R_{d,X}. On Re(s)>1
they converge to the marked Euler root. Thus this candidate does not
replace the arithmetic germ by an unrelated nonzero exponential. The
continuous counterterm removes the pole contribution rather than the
singular first prime trace itself.

The exact unresolved Cauchy assertion is, for every compact K in Omega,

    sup_{s in K} | sum_{X<p<=Y} p^(-s)
                    - integral_X^Y x^(-s)/log(x) dx | -> 0
    as Y>=X->infinity.

The k>=2 part already has a normally summable tail, by comparison with
sum_p p^(-2*min_K Re(s)). It cannot supply the missing first-trace
convergence. A locally uniform limit of L_X would supply all compatible
actual roots and certify Omega. No proof of the displayed Cauchy assertion
has been found. This is an explicit BRIDGE under attack, not a proved
producer or a novelty claim. Do not formalize the implication as progress.

Connection to the requested infinite boundary factorization: write
Xi(s)=C(s)*zeta(s), where the explicit Gamma completion factor C is a
holomorphic unit on Omega. Then Q_X=C^(-1)*exp(-L_X) is already defined
without division by Xi. If the unresolved convergence holds, Xi^2 Q_X
tends locally uniformly to Xi. Each known holomorphic Q_X can itself be
approximated on a compact exhaustion of Omega by polynomials, without any
assumption about Xi zeros. Polynomial multiples of Xi are actual cap
boundaries in the existing corpus. A diagonal approximation would then
give the required infinite sum/product-source factorization. The only
unproved certificate-producing step remains the first-trace limit above.

### Rejected bounded-operator shortcut

For D_n f(x)=f(n*x) on L2((0,infinity),dx), ||D_n||=n^(-1/2).
Consequently both sum_n n^(-s) D_n and sum_n mu(n)n^(-s) D_n converge
absolutely in operator norm for Re(s)>1/2 and are mutually inverse, by
Dirichlet convolution. Applied to exp(-x), this really constructs a
Hilbert-valued inverse source on the desired half-plane. It does NOT
construct the scalar reciprocal zeta or its Kummer roots there.

Reason: the required endpoint trace f->f(0) is unbounded even on the
dilation orbit of exp(-x): exp(-N*x) has L2 norm (2N)^(-1/2) tending to
zero and endpoint value 1. Therefore bounded-operator inversion, its
fractional powers, and Hilbert-space convergence cannot be passed through
that trace. This rejects that proof step, not the infinite-limit task.
The positive operator identity is elementary background, not a new RH
rung; no auxiliary Lean module will be made for it.

Further source audit: PrimeBoundaryPoissonJumpField and
PrimeBoundaryWickExpansion establish actual compensated symmetric
probability limits; those omit the required scalar first trace. The
ThetaRenewalPrimeBoundary header and initial proofs establish an
absolutely summable *paired* source current whose admitted counterterm
still retains the full Xi divisor. None supplies the displayed limit.

The exact compensated-root corpus search finished (session 91501, exit 0).
Its result is partial=true because the local filter/judge returned malformed
JSON, with inventory complete and compiler metadata mostly pending/stale.
Available hits cover finite Euler logarithms, quadratic random Euler
approximations, Euler connections and prime source definitions; they do
not establish the displayed convergence. No exhaustive absence claim.
The earlier local-limit search also finished (58169, exit 0,
partial=false/errors=[]); its Montel and Dirichlet-convergence hits carry
the missing normality/convergence as hypotheses.

Anti-theatre: the finite-stage construction and rejected trace passage do
not certify a single new zero-free point. No novelty or scientific theorem
is claimed. Another conditional Lean bridge would not solve the task.
Anti-laziness: the actual scalar convergence and arithmetic attachment
were attacked; no effort estimate or infrastructure detour was used to
avoid them. The corpus was checked. Remain on the compensated first trace,
with the unbounded endpoint trace excluded as a purported proof method.
No new Lean module, build, axiom audit, lint or umbrella change this cycle.
Full RH objective stays active; no external blocker exists.

## Source differentiation attack on the infinite limit

Revalidation found that the preceding continuous pole compensation repeats
the earlier Ein/pole-filled construction recorded in the route-dr
entire-pole-counterterm memory. It is not a new mechanism. The explicit
finite compatible roots remain valid, but their unresolved normality is
the same first-trace problem. Do not restart that normalization as a new
research cycle. No certificate progress in the preceding turn.

Tested a source-level alternative within DR: make the actual boundary
image stable under differentiation on Omega. This would lower the order
of a hypothetical positive-order zero and contradict preservation of its
full divisor. The candidate arithmetic lift is explicit, rather than
assuming stability of the image.

For a Schwartz cap source f, on x>0 define

    B f(x) = sum_{n>=1} f(n*x),
    V f(x) = sum_{n>=1} Lambda(n)*f(n*x),
    nabla f(x) = log(x)*f(x) - V f(x).

The sums converge absolutely at each fixed positive x, locally uniformly
away from 0. Schwartz decay also permits the double sum below. The exact
divisor identity sum_{d|k} Lambda(d)=log(k) gives

    B(V f)(x) = sum_{k>=1} log(k)*f(k*x),
    B(nabla f)(x) = log(x)*B f(x).

This is an actual physical source identity. It does not say that nabla f
is a Meyer cap or that its Mellin transform is holomorphic on Omega.
On Re(s)>1, absolute Mellin summation gives

    M(nabla f)(s) = (M f)'(s) + (zeta'/zeta)(s)*M f(s).

For the exact Xi cap, M f=C is the explicit nonzero Gamma completion
factor on Omega. Thus the meromorphic continuation of this source
transform is C' + C*zeta'/zeta. At a hypothetical zero rho of order m,
its residue is m*C(rho), which is nonzero. Consequently the proposed
source admission is exactly the unresolved pole-removal issue; it does
not follow from pointwise convergence of the physical dilation sum.

The finite-shift form is equally explicit. For fixed t and x>0,

    h_t(x) = sum_{n>=1} mu(n)*(n*x)^t*B f(n*x)

converges by rapid decay at infinity, and divisor cancellation yields
B h_t=x^t B f. In an absolute-convergence right half-plane its Mellin
transform is Xi(s+t)/zeta(s). A rightward shift large enough to put s+t
in Re>1 makes the numerator nonzero, but no holomorphic Mellin admission
on Omega has been proved. This is the infinitesimal/finite source version
of the existing scalar translation conductor obstruction, not a repair.

Verdict: BRIDGE, with the tempting inference from pointwise source
convergence to holomorphic Mellin admission rejected. No positive
half-strip convergence theorem was obtained. The exact algebraic source
identity is background for the attack, not a claimed new RH rung, and
will not be turned into auxiliary Lean code.

Corpus evidence this cycle: ThetaNaturalScheduleEulerOscillation.lean
1-135 confirms the raw natural Euler schedule's oscillating envelope;
Sieve/VonMangoldtPerron.lean 1-60 verifies the exact Lambda Dirichlet
identity only on Re>1. PrimeRotationXiSourceTransport declarations and
comments confirm the existing meromorphic conductor/zero-pole transport
classification. The first 110 lines of the new WeilPhiDoobDivisorEnergy
file give a divisor-energy coordinate representation, not a source
admission theorem; no claim about its full result is made and no peer
file was changed.

Two owned deep searches finished: prime-tail normality (session 29897)
and logarithmic source derivation (90958), both exit 0, partial=false,
errors=[]. Inventory complete; compiler coverage mostly pending/stale.
Available hits provide Mellin identities and conditional continuation,
not the missing admission. No exhaustive absence claim. No external
research, numerical computation, Lean build, or production edit.

Anti-theatre: no scientific novelty or zero-free certificate this cycle;
the compensation was rediscovered and differentiation re-expresses the
same obstruction. Avoid both as purported solved steps next time.
Anti-laziness: the actual infinite source and its Mellin attachment were
attacked directly; no effort estimate was used to skip work. Next work
must establish actual local convergence/admission, not prove another
equivalent criterion. DR and the full RH goal stay active and unproved.

## Causal-division pullback and the two endpoint tails

Previous turn classified as no progress on the certificate. Current tree
now contains DeningerMeyerCausalDivision.lean (272 lines when read): it
constructs a causal inverse of the target Euler generator at a vanishing
Mellin moment, with all-weight decay and all derivatives retained. Read
the entire source. This is a genuine target-space construction, but the
theorem does not assert membership in the Poisson boundary image. No new
compilation or axiom audit of that peer-owned working file was run here.

Tested whether this new construction provides the missing infinite source
limit. The pullback can be calculated explicitly. Let f be the exact Xi
cap, C=M f, and rho in Omega. On the positive ray put

    u_R(x) = x^(-rho) * integral_x^infinity t^(rho-1)*f(t) dt,
    u_L(x) = -x^(-rho) * integral_0^x t^(rho-1)*f(t) dt.

Both solve (-x*d/dx-rho)u=f, and

    u_R(x)-u_L(x) = C(rho)*x^(-rho).

C(rho) is nonzero on Omega. The right solution decays rapidly at
infinity but contains C(rho)*x^(-rho) at zero. The left solution is
smooth at zero but contains -C(rho)*x^(-rho) at infinity. Neither is a
Schwartz cap. Their Mellin integrals give the same meromorphic expression
C(s)/(s-rho), in their respective strips of convergence; changing causal
orientation moves the nonzero homogeneous term to the other endpoint.

The literal positive dilation sum of u_R does converge for each x>0.
Absolute tail Fubini gives

    B u_R(x) = x^(-rho) * integral_x^infinity t^(rho-1)*B f(t) dt.

At a hypothetical Xi zero rho, the right-hand side is precisely the
all-weight target division supplied by the new source file. Thus the
target division really does have a pointwise Poisson representation, but
its displayed preimage is outside the admissible source class. Its
Mellin pole cancels one order of the Xi zero. This is not an argument for
absence of rho.

The Hilbert resolvent does not repair the issue: for Re(rho)>1/2, u_L is
square integrable (its nonzero power tail is at infinity), whereas u_R
is not square integrable at zero. The L2 branch still has a Mellin pole
at rho, and its ordinary positive dilation series has a non-summable
leading n^(-rho) tail when Re(rho)<1. A regularized Poisson action is not
the cap boundary action used by the divisor-annihilation theorem.

Verdict: using target-space causal division as automatic boundary
division is CIRCULAR. The exact target construction is retained; no
claim that it supplies an arithmetic root or localized boundary-square
factorization. This is an applicability audit, not a new no-go theorem
or a retired DR route. Do not formalize the elementary tail calculation
as a substitute for the requested convergence proof.

Also read the current XiWardCubicParabolicSourceLanding.lean (194 lines)
and HTGeometry/ParabolicCauchyAveraging.lean (145 lines). Their parabolic
average retains the endpoint multiplicity and kills the moving pole.
The Euler-arithmetic equality is stated on the absolute Euler chamber;
the global object uses the continued logarithmic derivative. It detects
the retained charge, not its vanishing. No uniform arithmetic
cutoff/limit interchange on Omega has been supplied by these results.

Searches 19872 (causal-division source) and 93953 (causal pullback) both
finished with exit 0, partial=false, errors=[]. Inventory complete and
compiler metadata mostly pending/stale. Hits include the new causal
decay theorem, existing range classification, and specified closed-range
theorems. None of those statements identifies the divided target as a
Poisson boundary. No exhaustive missing-proof claim is made.

Anti-theatre: no new scientific result, no half-strip certification,
and no Lean proof this cycle. Current source constructions were checked
for the actual missing implication, not treated as a solved producer.
Anti-laziness: the literal pullback and both endpoint choices were worked
out rather than replacing admission by an assumption. No effort-based
deferral, external search, numerical work, peer edit, or auxiliary Lean
module. Actual root/source convergence remains the active hard task.
