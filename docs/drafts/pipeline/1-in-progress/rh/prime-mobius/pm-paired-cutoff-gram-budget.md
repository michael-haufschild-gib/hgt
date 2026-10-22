# PM: signed Gram budget with the natural product cutoff retained

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ACTUAL SMALL-DAMPING PRODUCER
- **Route:** PM; witness half-mass positivity via cofinal small-damping L2 admission.
- **Status:** The actual Gram-budget conjecture remains open; no premise added.
  Exact prime-pair identities and the fixed-channel covariance sign have a
  successful targeted build, final direct-file audit and ten standard-axiom audits.

## Exact conjecture

For every epsilon>0, there exists a finite C_epsilon such that, for every Q,

`pmPowerDampedRamanujanGramQuadratic epsilon Q
 <= C_epsilon * sum_(1<=q<=Q+1) pmPowerDampedRamanujanLogSquareTerm epsilon q`.

This concerns the actual Möbius-aligned coefficients, not arbitrary
coefficient vectors. The corpus proves summability of the logarithmic
square terms. It also proves that a common actual Gram budget implies L2
admission of the literal power-damped Fermi source. Thus this conjecture
would supply the missing producer for every positive damping, rather than
another reformulation alone. No domination proof is currently available.

## Proposed proof mechanism and its unresolved step

The exact prime recursion pairs a_q with
`a_(p*q)=-a_q/(p^(1+epsilon)-1)` when p does not divide q. The primitive
pairing identity to check against the corpus is

`P_(p*q)(N)=p*P_q(floor(N/p))-P_q(N)`.

Work inside the natural denominator cutoff throughout. Separate paired
terms p*q<=Q+1 from every omitted boundary term p*q>Q+1. Preserve the full
quadratic cross terms. The hard mathematical step is a signed estimate
for the aggregate paired interior plus the complete cutoff boundary,
paid by the actual summable logarithmic square mass.

The proven divergence of finite prime-aperture norms for 0<epsilon<1/2
excludes a uniform summable prime-growth bound that first completes all
products. Any successful estimate must use the natural cutoff boundary.
The finite absolute transfer-kernel mass also leaves the input prefix
norms unpaid. Neither result can be substituted for the desired bound.

## Corpus basis

- `PMPowerDampedMobiusRamanujanWeights`: exact Euler weights and prime recursion.
- `PMPowerDampedMobiusRamanujanLogMass`: actual logarithmic square summability.
- `PMPowerDampedMobiusRamanujanQuadratic`: complete Gram identity and admission receiver.
- `PMPowerDampedMobiusRamanujanVariance`: exact energy-centered covariance, with all cross terms.
- `PMPowerDampedMobiusRamanujanTransfer` / `KernelMass`: literal cutoff-dependent transfer and its finite weighted absolute mass.
- `PMPowerDampedMobiusPrimeThreshold`: complete prime-aperture divergence.
- Search61/62 inspected all returned candidate/source statements and proof/ingredient groups;
  partial at reranking / semantic retrieval respectively. Compiler coverage mostly pending/stale.

## Prior attempt closed

`../../../5-failed/pm-scalar-tail-correction.md` records the audited failure of
the last-scale harmonic correction and its positive all-centers Mertens
window floor. That result does not supply this Gram upper estimate.

## Next proof attempt

Verify the paired primitive identity from the exact divisor expansion,
then derive the complete finite-Q quadratic decomposition before making
any inequality. Test proposed signed boundary compensation against the
existing prime-aperture obstruction. Formalize only a dependency-closed
mathematical advance; do not add a conditional receiver for this conjecture.

## Prime pairing: paper derivation in progress

Search63 completed (not partial); candidate/source statements and ingredient
groups inspected. Inventory complete, compiler metadata mostly pending/stale,
semantic coverage not measured. No existing prime-paired primitive or Gram
identity was returned. Exhaustive matching source search found neither.

Write `P_q(N)=pmRamanujanPrimitive q N`, `w_N=1/[N(N+1)]`, and
`G(q,r)=sum_N P_q(N).re*P_r(N).re*w_N`. For a prime p coprime to q,
split divisors of p*q into d and p*d, d|q. Möbius prime multiplication and
integer division give `P_(p*q)(N)=p*P_q(N/p)-P_q(N)` exactly.

The complete block of weights with floor(N/p)=k telescopes to w_k/p for
k>=1. The k=0 block contributes zero because every P_q(0)=0. Thus
`sum_N P_q(N/p).re*P_r(N/p).re*w_N=G(q,r)/p`.
For q,r>1 coprime to p, bounded periodic primitives justify absolute
summation. Expanding the product of the two primitive identities proves

`G(p*q,p*r)+G(p*q,r)+G(q,p*r)=(p-1)*G(q,r)`.

This is an exact signed identity, not an upper budget. The natural-cutoff
decomposition, using denominator cutoff X, is as follows. Let
`b=p^(1+epsilon)-1`, let f contain q>=2, q<=X/p, p not dividing q, and
let g contain q>=2, X/p<q<=X, p not dividing q; both use actual a_q*P_q.
Set `z=a_p*P_p` when p<=X and zero otherwise, `h=g+z`, and
`D_p f(N)=f(N/p)`. Then the entire centered prefix equals
`h+(1+1/b)*f-(p/b)*D_p f`. Its energy is exactly

`||h||^2 + ((1+1/b)^2+p/b^2)*||f||^2
 -2*p*(1+1/b)/b*<f,D_p f>
 +2*(1+1/b)*<h,f>-2*p/b*<h,D_p f>`.

No term can be dropped on sign grounds yet. A universal triangle bound
introduces prime growth of order p^(-1/2-epsilon), which is not the needed
summable increment for small damping. The open step is a signed estimate
of the displayed covariance combination for actual f and h, including z.
The exact primitive, dilation and four-term Gram identities now pass the
targeted build of `PMPairedRamanujanGram.lean`.

### Signed covariance test: fixed composite channel

The next conjecture within this same estimate is the fixed-channel limit

`G(p*q,r) -> phi(r)*Lambda(q)/2-G(q,r)`

as primes p tend to infinity, with fixed q,r>1. The primitive identity
reduces this to a dilation-mixing limit. If f(0)=0 is bounded and g is
periodic with mean m, bounded prefixes of g-m and finite Abel summation on
each interval [p*k,p*(k+1)) give

`p*sum_N f(N/p)*g(N)/[N(N+1)] -> m*sum_k f(k)/[k(k+1)]`.

Each centered block is at most a constant times 1/(p*k)^2 in absolute
value; the k=0 contribution vanishes. Summing against bounded f gives an
error tending to zero. Apply f=P_q.re, g=P_r.re, m=-phi(r)/2 and the
audited reciprocal moment sum P_q.re/[N(N+1)]=-Lambda(q).

Lean strengthened the sign conclusion: G(q,q)>0 for every q>1, using the
nonzero period sum to locate a nonzero primitive value. Consequently
G(p*q,q) is eventually negative whenever q>1 is not a prime power, with
no squarefreeness requirement. When q is also squarefree, its actual
Möbius-aligned weight is nonzero and a_(p*q)=-a_q/b, b>0; the actual
weighted cross term a_q*a_(p*q)*G(p*q,q) is therefore eventually positive.
This disproves the candidate justification that individual prime pairs
always dissipate energy. The precise mixed limit and exact Gram relation
are its positive survivors. It does not settle the signed sum for growing
q,r at the natural cutoff. All ten exported statements passed the targeted
build, final direct-file audit and axiom audit. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The leaf is wired into
`RHTower.lean`. The failed sign conjecture and exact positive survivors
are closed in `../../../5-failed/pm-prime-pair-termwise-dissipation.md`.

Search64 (partial: reranking and semantic variants) found no positivity
theorem for actual centered cumulative sums. Search65 completed and found
Cesaro weighted-average and periodic-prefix infrastructure, but no
floor-dilation covariance limit. Its candidate/source and ingredient
groups were inspected. Source inspection found the finite Abel argument
in EulerDeletionMobiusGlobalLogSaving (private helper), available for an
explicit local proof of the mixing step.

## Next hard step after the sign test

Return to the complete displayed cutoff energy, with h=g+z retained.
The same-channel cross term cannot supply uniform cancellation: it has
the wrong sign for each fixed squarefree composite channel and large
prime partner. The producer must estimate the combined covariance across
different cofactors and the entire natural-cutoff boundary. The new
fixed-channel limit is not uniform in the cofactors and is not an upper
energy budget. Search66 targets the literal finite prime split and its
boundary identities; any subsequent inequality must pay all of these
terms with the actual summable coefficient-square mass. Search66 returned
the cofactor floor identity, prime column recursion and aperture
obstruction; no missing signed upper estimate. It was partial at deadline
and filtering/judging, with coverage pending. All returned candidate/source
statements were inspected; no proof/ingredient groups were returned.

## Complete transfer covariance attack

The previous turn is progress: it proved exact mixed covariance and
falsified the termwise dissipative sign. It did not supply admission.
The next conjecture uses the full kernel, rather than assigning a sign
to individual q,p*q pairs.

The corpus identifies w(m)=|a_epsilon(m)| as a probability mass with
joint squarefree divisibility mass d^(-1-epsilon). Put
`psi_p(m)=1` if p divides m, and `psi_p(m)=-1/(p^(1+epsilon)-1)` otherwise.
The literal transfer is
`T(m,r)=w(m)*r^(-epsilon)*product_(p|r) psi_p(m)`.
The source-grounded conjecture is the exact orthogonality law

`sum_m w(m)*psi_S(m)*psi_U(m)
 = if S=U then product_(p in S) 1/(p^(1+epsilon)-1) else 0`

for finite prime sets S,U. It follows on paper from the joint divisibility
mass: the prime indicators are independent Bernoulli variables with
probabilities p^(-1-epsilon), each psi_p has mean zero, and its second
moment is 1/(p^(1+epsilon)-1). This would identify actual signed transfer
columns by their prime support, with an exact quadratic diagonalization.

The hard producer remains the same: retain the complete source input
`F_(Q/(m*r))(r*t)` inside this averaging, and bound its actual cutoff
quadratic by summable coefficient-square mass. Orthogonality cannot be
applied as if that input were independent of m. The cutoff introduces
mixed differences of prefix functions. Their aggregate physical L2 cost
must be proved; a zero column sum or a finite kernel norm alone is not
enough. Search67/68 inspect existing signed-kernel and prime-independence
infrastructure before any new Lean code for this mechanism.

### Truncated prime balance (paper proof)

Search68 was partial with complete inventory/snapshot coverage; all returned
candidate/source statements and ingredient groups were inspected. It found
finite Bernoulli/Walsh infrastructure but no signed PM cutoff producer.
Search69 was partial with coverage pending and supplied no missing estimate.

Orthogonality alone leaves an unestimated constant component: expanding the
transfer against the Mobius prefix gives, for squarefree d, the coefficient
`mu(d)*product_(p|d)(1-psi_p(m))`. Its full w-average is `mu(d)`.
Thus a Jensen bound on the expanded random source retains the original
hard Mobius energy. This is not a proof that the full signed transfer fails.

The next direct boundary statement uses the actual w and actual cutoff.
Write b=p^(1+epsilon)-1 and
`B_(p,Q)(H)=sum_(Q/p<n<=Q, p does not divide n) w(n)*H(n)`.
For any p-invariant H (H(p*n)=H(n)), splitting multiples of p and using
`w(p*n)=w(n)/b` for p not dividing n gives the exact finite identity

`sum_(n<=Q) w(n)*psi_p(n)*H(n) = -B_(p,Q)(H)/b`.

The squared version is

`sum_(n<=Q) w(n)*psi_p(n)^2*H(n)
 = (sum_(n<=Q) w(n)*H(n))/b - (b-1)*B_(p,Q)(H)/b^2`.

For p-invariant f,g, these imply the full cutoff quadratic identity

`E_Q[(f+psi_p*g)^2]
 = E_Q[f^2]+E_Q[g^2]/b
   -2*B_(p,Q)(f*g)/b -(b-1)*B_(p,Q)(g^2)/b^2`.

In particular the cutoff cross form is negative semidefinite when f=g.
No sign claim is made for general f*g. The actual prefix input is not
p-invariant; its failure of invariance is exactly another cutoff difference.
After auditing this literal boundary balance, retain that difference when
applying it to F_(Q/(m*r)). Do not discard it or substitute auxiliary
orthogonality for the physical L2 bound.

The draft strengthens the finite balance to arbitrary H, with no invariance
premise. Define

`J_(p,Q)(H)=sum_(n<=Q/p,p does not divide n) w(n)*(H(p*n)-H(n))
             -B_(p,Q)(H)`.

Then `E_Q(psi_p*H)=J_(p,Q)(H)/b`, and for arbitrary f,g,

`E_Q[(f+psi_p*g)^2]
 = E_Q[f^2]+E_Q[g^2]/b+2*J_(p,Q)(f*g)/b
   +(b-1)*J_(p,Q)(g^2)/b^2`.

This follows from the pointwise two-value law
`psi_p^2=1/b+(b-1)*psi_p/b` and finite reindexing of multiples of p.
Unlike the earlier invariant statement, it applies literally to the source
prefix depending on m. For H(m)=F_(Q/(m*r))(r*t), H(p*m)-H(m) is an actual
Mobius coefficient band, not zero. Its signed cross-prime physical energy
remains the producer to be estimated.

### Prime-order constraint on a prospective energy induction

Search70 was partial with snapshot coverage. Candidate/source statements were
inspected; it returned the fixed-channel Gram limit and bounded centered
prefixes, not a bound uniform in growing cofactors.

A prospective induction cannot be uniform over arbitrary completed prime
apertures. The following exact paper calculation must be checked against the
corpus and formalized before it is used as a no-go. Let S be finite primes,
M their product, alpha_S=product_(p in S)(1-p^(-1-epsilon)). Restrict the
actual Ramanujan coefficients a(q) to q dividing M. Its cofactor at d|M is

`d*sum_(m|(M/d)) mu(m)*a(d*m)
 = (alpha/alpha_S)*mu(d)*d^(-epsilon)`.

The first equality expansion uses disjoint prime supports; the product over
the complement is product(1+1/b_p). Hence its finite Fermi source is exactly
`(alpha/alpha_S)` times the canonical finite-prime Mobius source. Since
0<alpha_S<=1 and alpha>0, the corpus's canonical-aperture divergence for
0<epsilon<1/2 would force divergence of these completed Ramanujan apertures
as well. Their coefficient-square logarithmic mass is bounded by the already
summable full mass. Thus the proposed natural-cutoff Gram estimate, if true,
must use natural denominator order essentially; an induction valid for all
prime-complete supports would be false. This does not falsify the natural
cutoff candidate. Search71 checks this exact finite-aperture identification.

Search71 was partial with snapshot coverage; all candidate/source statements
and ingredient groups were inspected. It found no completed-Ramanujan-aperture
identification. The actual finite Mobius aperture definition and the canonical
norm-divergence proof were read. A direct way to formalize the new identity
uses `pmRamanujanPrimitive_prime_mul`, which also holds at q=1:

`U_S(N)=sum_(T subset S) a(product T)*P_(product T)(N)` obeys
`U_(S union {p})(N)=(1+1/b_p)*U_S(N)-(p/b_p)*U_S(N/p)`.

The normalized Mobius floor sum obeys the same recursion because
`(1+1/b_p)*p^(-epsilon)=p/b_p`, with initial value alpha*N.
This avoids introducing a new multiplicativity API for Ramanujan sums.
Take its dyadic floor difference to obtain the Fermi-source identity.
For a Gram conclusion, keep the fixed q=1 packet: the centered primitive
omits it, and passing from integer cumulative values to the continuous
fractional-part source adds only the fixed density sawtooth. Both are
bounded packets, not vanishing terms.

## Cutoff-balance audit completed (2026-10-02)

`PMRamanujanCutoffPrimeBalance.lean` closes the arbitrary-input mean and
quadratic identities, the invariant-input boundary identity, and the
nonpositive cutoff cross form for products of other prime factors.
All eleven exports (four definitions, seven theorems) have only standard
Lean axioms. Final targeted build built only the new leaf; final actual-file
`lake env lean` exited zero without diagnostics. Umbrella wiring and
whitespace checks passed. The exact positive result is archived in
`../../../3-formalized/pm-ramanujan-cutoff-prime-balance.md`.

Global lint has fourteen unrelated unwired-leaf errors:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MobiusDivisorCriticalCompensatedCauchy, MobiusDivisorCriticalLogProfilePrimitive,
MobiusDivisorCriticalLogProfileTail, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, RoutePCompensatedMassRiccati,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.

Assessment: the literal signed cutoff decomposition is new and exact;
no upper physical energy budget was proved. The next attack must use
natural denominator order to estimate the combined J terms. First audit
the completed-aperture normalization above, to prevent importing an
impossible all-support induction into this natural-order problem. Its
paper proof is recorded, but its Lean identification and divergence
transfer are still pending; no new no-go is declared closed.

## 2026-10-02 — Completed-support test in progress

Search72 completed (partial=false, snapshot coverage). All candidate/source
statements and the ingredient group were inspected; no aperture normalization
was present. The current draft proves both prime-insertion recursions and is
checking their exact normalization. Define the completed Fermi aperture by
`U_S(floor(1/t))-2*U_S(floor(1/(2*t)))`, retaining the q=1 packet. The intended
formal no-go concerns this literal finite Fermi source: at each 0<epsilon<1/2,
its norms diverge along canonical completed prime supports, although the sum
of the actual q*log(2q)*|a(q)|^2 on those supports is uniformly bounded. This
would exclude an order-independent coefficient-square ceiling; it does not
falsify the natural-denominator cutoff estimate.

The normalization has a stronger positive interpretation: it equals
`sum_(T subset S)|a(product T)|`, the actual probability mass retained by
that completed aperture. Therefore it lies between alpha and 1. This is
seen by evaluating the primitive identity at N=1: P_q(1)=mu(q), the
Mobius floor sum at 1 is 1, and a(q)*mu(q)=|a(q)|. Thus divergence cannot
be attributed to an artificial growing normalization. The exact source
identity, probability-mass classification and divergence/finite-log-mass
separation are all being audited in the same draft.

## Completed-support extension falsified and audited (2026-10-02)

`PMRamanujanCompleteAperture.lean` formalizes the exact primitive and Fermi
normalization by retained actual probability mass, alpha<=kappa(S)<=1.
For every fixed 0<epsilon<1/2, completed prime-support norms tend to infinity,
while their logarithmic coefficient-square mass stays bounded. Every fixed
multiple of that mass is eventually exceeded by squared energy. This closes
the conjecture test against support-independent prime induction, including
its strongest positive survivor; see
`../../../5-failed/pm-ramanujan-completed-support-budget.md`.

All 21 exports passed standard-axiom audits, targeted build and final
actual-file `lake env lean`. Only the new leaf built; umbrella wiring is
complete. Global lint has twelve unrelated unwired leaves:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MobiusDivisorCriticalMovingHeadAsymptotic, MobiusDivisorCriticalPrimeTailError,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.

The natural-cutoff upper estimate is still OPEN. Completed prime supports
cannot replace the natural denominator cutoff in that proof. The next
producer attempt must estimate the combined ordered J terms, not infer a
physical bound from auxiliary orthogonality or a support-independent
coefficient-square estimate. Search73 checks the wider corpus for an actual
unconditional ordered Mobius cumulative-energy producer before choosing the
next conjecture; the existing PM log-saving and fixed-channel limits alone
remain insufficient.

## Ordered-band producer attempt (2026-10-02)

Search74 completed; search75 was partial; searches76 and77 completed.
Candidate/source statements and ingredient groups were inspected. Inventory
coverage was complete for the completed searches, while compiler metadata
was mostly pending/stale. No actual small-damping upper producer was found.

The parity-defect alternative concerns a different square-root Abel source.
Its late-prime head construction preserves parity through one additional
prime step; it does not establish full processing or a PM energy bound.
The support-localization attempt also remains insufficient: literal prefix
differences overlap near zero, so their shrinking supports are not an
orthogonality theorem. Inspection of the completed-aperture divergence proof
shows that it uses Mellin analytic uniqueness, not a quantitative growth
rate. It cannot presently show that omitted-product energy dominates the
natural cutoff, and no such comparison is claimed.

The next direct conjecture is an ordered-band estimate. For j>=0 put

`S_j(N)=sum_(2^j<q<=2^(j+1)) a_epsilon(q)*P_q(N)`.

Conjecture: for each epsilon>0 some finite C_epsilon satisfies

`sum_(N>=1) |S_j(N)|^2/[N(N+1)] <= C_epsilon*2^(-epsilon*j)`.

This is a stronger proposed mechanism for the existing natural-cutoff
budget, not a new theorem. Summable square roots along j would give a
common bound at dyadic denominator endpoints, and pointwise convergence
plus Fatou would supply the literal cumulative-energy budget and admission.
No arbitrary intermediate-cutoff bound is needed for that implication.
The exponent is provisional; any genuinely summable sequence of band
norms would suffice. The research target is cancellation, not optimizing
that exponent.

The corpus cofactor identity fixes the exact source to estimate. For
1<=X<Y, extend b_X(d)=pmPowerDampedRamanujanCofactor(epsilon,X,d)
by its already-zero formula for d>X. Then the band primitive equals

`sum_(d<=Y) (b_Y(d)-b_X(d))*floor(N/d)
 = -sum_(d<=Y) (b_Y(d)-b_X(d))*fract(N/d)`.

There is no density term: both complete cofactors have density alpha.
Moreover mu(d)*(b_Y(d)-b_X(d)).re is the nonnegative exact mass
`d*sum_(X/d<m<=Y/d)|a_epsilon(d*m)|`. This follows by subtracting the
audited cofactor sign identities and splitting the nested finite ranges.
It retains all signs and the complete product band. No bound follows by
discarding these signs; the absolute argument still has the half-damping
barrier. The hard next step is an upper bound for the full signed band
quadratic, including different-d covariance. Do not formalize another
conditional admission receiver in place of proving this bound.

### Complete-period cancellation and the anchored comparison attempt

Search78 completed and79/80 were partial; none supplied the band producer.
Source inspection found an exact common-period centered-residue covariance
in `EulerDeletionMobiusPeriodCovariance` and the signed gcd-square
diagonalization in `Sieve/GcdPowerDiagonalization`. These can be combined
with finite cofactor inversion, without an estimate or a sign premise.

Paper conjecture now proved algebraically: for finite real weights a(q)
supported on 2<=q<=Q, the period-centered primitive combination has exact
complete-period variance

`(1/12)*sum_(2<=q<=Q) gcdPowKernel(2,q)*a(q)^2`.

Indeed its residue coefficient is
`b(d)=d*sum_(m<=Q/d) mu(m)*a(d*m)`. The multiples coordinate
`sum_(d<=Q,e|d)b(d)/d` equals a(e), by finite hyperbola interchange and
`sum_(m|n)mu(m)=1_(n=1)`. The signed gcd-square form therefore collapses
exactly to the displayed diagonal. The subtracted constant kernel vanishes
because a(1)=0. The period mean is retained separately; its value is
`-sum_q a(q)*phi(q)/2`. This is actual denominator orthogonality of the
centered primitives, not a statement about anchored reciprocal energy.

The direct hard comparison to test is whether an actual complete dyadic
band has anchored reciprocal energy bounded by a fixed epsilon-dependent
multiple of its complete-period second moment divided by the band scale.
The exact variance gives the correct diagonal scale for this attempt;
its mean and finite-window boundary must also be retained. Such a comparison
is not known and cannot be invoked as an assumption. Formalizing the exact
finite covariance is the next step in attacking that comparison; no
conditional RH theorem will be added for it.

### Anchored centering after the exact period diagonal (2026-10-02)

The new `PMRamanujanPeriodDiagonal.lean` draft passes Lean and its targeted
old-mode build. Finite multiples inversion, drift-removed residue identity,
period mean, covariance, complete second moment, centered second moment
and the literal natural-band specialization are proved. Final direct-file
and exported-axiom audits passed. No anchored upper bound follows.

Search81 was partial and supplied the existing residue covariance source.
Search82/83 were partial (full inventory; compiler metadata largely
pending/stale). All candidate/source statements and ingredient groups were
inspected. They supplied no missing comparison. In particular the existing
Möbius weighted-period identity retains each progression weight, and its
period-averaging obstruction forbids treating those weights as uniform.

The attempted estimate by the whole period second moment leaves an unpaid
signed totient sum. The better producer conjecture centers in the actual
reciprocal probability measure instead. For the complete actual band
`X<q<=2X`, write `S_X(N)=sum_q a(q)P_q(N)` and
`m_X=-sum_q Re(a(q))*Lambda(q)`. The corpus reciprocal-mean theorem gives
this mean exactly; its coefficient majorant is summable. The new period
identity gives `D_X=(1/12)sum_q gcdPowKernel(2,q)*|a(q)|^2` exactly.

New hard conjecture: for each epsilon>0 there is C_epsilon such that

`sum_(N>=1) |S_X(N)-m_X|^2/[N(N+1)]
 <= C_epsilon*log(2X)*D_X/X`  for all X>=1.

This remains a conjecture, not an added premise or a new Lean receiver.
The actual coefficients and the whole denominator band are essential.
A coefficient-independent version across arbitrary band subsets would
contradict the completed-aperture obstruction. The mean can be controlled
by the existing von-Mangoldt coefficient majorant with part of epsilon
reserved for a tail bound. Together with the actual coefficient decay,
the displayed variance bound would give summable dyadic band norms.

The paper attack via absolute residue weights failed: it loses the factor
of the band scale. Period centering alone also failed: converting it to
anchored centering requires the exact subtraction of the squared difference
of the totient and Mangoldt means. That subtraction must remain inside the
signed quadratic; estimating its terms separately pays the original gap.
No falsification of the actual band conjecture is claimed.

A largest-prime/cofactor attack keeps
`P_(p*m)(N)=p*P_m(N/p)-P_m(N)` and the literal prime interval
`X/m<p<=2X/m`. The audited mixed-covariance proof already has a quantitative
error `2*A*B*zeta(2)/p`, where A bounds the first input and B bounds centered
prefixes of the second. It only becomes useful when that entire cofactor
cost is controlled. The remaining smooth and balanced-factor bands cannot
be dropped. Search84 checks existing uniform cofactor machinery; proving
full signed aggregate cancellation is still the next hard task.

Search84 was partial, with coverage pending (generation1184807); all
returned statements were inspected. No uniform aggregate estimate was
returned. The private quantitative covariance bound above was checked in
its actual proof: it pays both input suprema and the entire centered-prefix
cost, so a fixed-cofactor limit does not bound the moving balanced-factor
region. This is a failed inference, not a failure of the exact prime-pair
identity or a falsification of the centered-band conjecture.

All ten public declarations of the period-diagonal leaf passed `#print
axioms`: only propext, Classical.choice and Quot.sound. The targeted old-mode
build compiled only that leaf (103 seconds); all other entries were replayed.
The final direct-file audit exited 0 without diagnostics. Global lint exits 1 on fourteen
unrelated unwired leaves: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMFiniteEulerDenominator,
CCMRestrictedWeilPolarFreeShift, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SuzukiMatchedEvenSourceBound, ThetaMovingShellFirstOrderPhase,
ThetaTailTwoPointPositivity, ZetaZeroDensityPowerSaving. No error names the
new leaf; its umbrella import is present.

For the next proof attempt, the already-solved scalar estimates should not
be rebuilt: `|a(q)|<=q^(-1-epsilon)` bounds the actual Mangoldt band mean by
`C_epsilon*X^(-epsilon/2)`, reserving half the damping in its summable
majorant. Also `J_2(q)<=q^2` gives the expected diagonal scale directly.
The only unpaid part of the new conjecture is the full signed, reciprocal-
centered off-diagonal covariance. A prime-only subband has coherent early
primitives, so dropping composites discards the very cancellation needed.
The next attack must retain cross terms between prime channels and every
composite factor regime, including growing balanced cofactors. These
observations are proof planning, not new Lean upper estimates.

### Critical-profile subtraction attack (2026-10-02)

Search85 (partial) again supplied no complete moving-cofactor bound. The
actual cofactor formula instead exposes a source-specific asymptotic:
for each fixed N, `X^epsilon*S_X(N)` has a positive divisor-profile limit.
The full dependency-closed paper derivation, its normalization, and the
weaker sufficient moving-remainder target are recorded in
`pm-ramanujan-band-critical-profile.md`.

This is a new producer attempt, not a conclusion from period averaging.
The profile has finite anchored energy on paper. Its squarefree residue
has only prime and prime-square local layers and absolutely summable
reciprocal mass. The main term's normalization is fixed by the exact
identity `density * reciprocal_profile_mean = 1`. The m=1 moving cofactor
still contains the original signed Mobius channel. Its covariance with all
other factors must remain; fixed-index convergence cannot prove the
needed norm bound. The logarithmic normalized comparison is stronger than
necessary, so the working target permits the existing positive-damping
margin instead of pursuing a sharp critical rate.

Search86 was partial;87 complete. All returned statements and ingredient
groups were inspected. Lean formalization starts with the exact positive
profile, its divisor/floor identity and subpower weighted summability;
the actual band-limit weld must also be completed before reporting this
as a formalized asymptotic of the literal source.
