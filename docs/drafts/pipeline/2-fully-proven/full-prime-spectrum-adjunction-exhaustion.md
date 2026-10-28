# Spectral exhaustion by torsion-adjunction energies

- **ID:** full-prime-spectrum-adjunction-exhaustion
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Source:** Ramanujan full-matrix quasimodes; harmonic rough-number tensorization; prime-defect Dirichlet form
- **Statement:** Every bounded energy window of `log(N) I-P_N` converges, with multiplicity, to the simple energies `gamma+log(m)+tameDifferent(m)`.
- **Count:** uncounted; eleven of sixteen scratch modules pass; endpoint checks and final actual-source audits remain

## Goal

The finite-packet quasimode project provides actual nearby eigenvalues for each
fixed conductor. It does not exclude additional bounded-energy branches. The
proposed theorem would identify the entire bounded-energy spectrum and its
eigenvectors, thereby determining every fixed ordered eigenvalue asymptotic.
The optimal pole gap would be a consequence, not a separately counted numerical
improvement. No full Weil positivity or RH implication is asserted.

## Gates

- [x] Corpus novelty and significance audit, with stated primary-literature exclusions.
- [x] Dependency-closed paper proof of compactness, exact spectral counts, and simple eigenlines.
- [ ] Exact Lean realization, direct source checks, transitive axioms, umbrella wiring.

## Existing input inspected

`ThePrimeFormHasASpectralGapBelowItsPole.lean` and its formalized card were read
in full. Its public result gives one uniform positive pole-complement gap.
`TheHarmonicMeasureTensorizesOverPrimes.lean` was read in full, including
the ladder/level identities and prime-peeling proof. Inside that proof the local
`claim` bounds every rough interval, not merely its published Q=0 specialization:

`harmonicVar Q X f <= K*exp(Psi(Q,X))*glauberForm Q X f`.

For X>=2, `Psi(Q,X)=-A*S(Q)/log(X)<=0`, so one constant K bounds all rough
intervals. The small-X cases have zero variance. Exposing and auditing this
stronger interface remains necessary; the local claim is not an available
public Lean declaration. Reuse this argument rather than assume rough-fibre
tensorization. Its proof is baseline, not independently new mathematics.

The targeted interface search confirmed only the Q=0 public theorem. A
scratch draft, `/tmp/TheRoughHarmonicMeasureTensorizesUniformly.lean`, retains
the existing prime-peeling induction and replaces its final specialization
by the bound `exp(Psi(Q,X))<=1`. It has not been checked or installed. The
existing source and olean are preserved. This stronger exported input is
support for exhaustion, not a separate contribution.

The exact valuation moment also has an unverified scratch draft,
`/tmp/PrimeDefectControlsValuationMoments.lean`. It reuses the inspected
prime-supported divisor reindexing and reciprocal Mangoldt mass bound;
its conclusion is `log(p)*sum_n v_p(n)*x(n)^2 <= 2D_N(x) +
2log(p)/(p-1)*sum_n x(n)^2`. It is not installed or counted.

Initial whole-corpus and RAPT-restricted searches returned the existing single
gap, finite-sieve spectrum, finite-class horizon limits, and unrelated Ramanujan
prefix/PM/CCM matrices. The current RAPT README's spectrum/module description
was checked through its new tensorization and gap entries. These first searches
did not exhibit bounded-window exhaustion of the literal prime matrix. This is
only an initial novelty audit, not an assertion of exhaustive novelty.

The initial HTGeometry machinery search returned generic compact-operator
spectral finiteness (`CompactOperatorDiscreteSpectrum`,
`CompactOperatorBoundedBelow`) and spectral approximation/Schur lemmas for
other operators. Their statements were inspected in the search results;
their sources have not yet been audited for use. No ready-made variable-horizon
arithmetic compactness certificate was identified by that search.

## Proposed compactness mechanism

Write `y(n)=sqrt(n)*x(n)` and let D_N be the literal pole-defect Dirichlet form.
The ground-state top-control inequality already used by the spectral-gap proof
gives, for each small eta and all sufficiently large N,

`<x,(log(N)I-P_N)x> >= (gamma-eta)||x||^2+(1-eta)D_N(x)`.

Thus bounded renormalized energy controls D_N. Two separate truncations should
make these bounded-energy vectors uniformly close to a finite Ramanujan span.

1. Fix P>1 and condition harmonic measure on the prime valuations below P.
   Each fibre is `n=d*k`, with fixed small-prime part d and P-rough k<=N/d.
   Uniform rough tensorization, together with the same disjoint ladder-edge
   bound but `log(q)>=log(P)`, should give

   `||x-E_(P,N)x||^2 <= K*D_N(x)/log(P)`.

   Here E is harmonic conditional expectation in pole gauge, transported back
   to ordinary Euclidean coordinates. The exact fibre identity and scaling
   must be proved; they are not assumptions of the target.

2. For each fixed small prime p, the elementary inequality
   `(a-b)^2 >= a^2/2-b^2`, summed over its downward prime-power edges, suggests

   `sum_n v_p(n)*|x(n)|^2 <= 2*D_p(x)/log(p)+2*||x||^2/(p-1)`.

   Every n has v_p(n) downward p-edges. The negative terms reindex as a
   geometric sum bounded by `||x||^2/(p-1)`. This bounds mass outside any fixed
   box of the small-prime valuations by O(1/L), uniformly in N. Conditional
   expectation contracts that same box-complement norm because the box is
   measurable in the conditioning variables.

   Existing exact interfaces were checked in
   `TheDeficitOfThePrimeFormIsADirichletEnergy.lean`: `sum_edges_eq_sum_divisors`
   reindexes all edges by their top; `log_mul_ladderDefect_le` bounds one
   prime's edge defect by D_N. The new quasimode support theorem
   `sum_divisors_primePower_mangoldt` counts the prime-supported divisor atoms,
   while `sum_dvd_vonMangoldt_div_le` bounds the reciprocal bottom-edge mass.
   Thus the moment estimate can reuse exact existing reindexing. A coarser
   bound with D_N in place of each D_p suffices after summing the finitely many
   small primes; no sharp aggregate constant is needed for compactness.
   The full deficit source, including its top-row absorption argument, has
   now been read. No uniform control of the Mertens remainder is being added
   as an assumption.

The two orthogonal errors add: conditional variance plus the discarded
conditional mean. First choose P large, then a valuation cutoff L large.
The remaining space has dimension independent of N. Its vectors are linear
combinations of `1_(small-prime valuations=e)/sqrt(n)` for finitely many e.
Each one-prime shell indicator is an exact finite linear combination of the
ground and valuation steps, by triangular inversion of their displayed values.
Taking products puts this space inside a fixed finite Ramanujan-conductor span.
The required inversion, coordinate projection, and uniform estimates remain
unproved here.

The corpus already supplies the needed finite divisor-to-Ramanujan inversion:
`RHTower.pm_ramanujan_sum_divisors` in
`PMPowerDampedMobiusRamanujanExpansion.lean`, whose statement and proof were
read, gives `sum_(q divides d)c_q(n)=d*1_(d divides n)` for positive d,n.
Taking real parts and the existing coefficient-identification bridge should
express each divisibility indicator in the finite normalized Ramanujan span.
Each exact valuation shell is the difference of two such indicators; products
are indicators at the product modulus because the primes are distinct.
This removes any need for a new abstract triangular-inversion theorem.
The application and its exact finite-span statement remain unformalized.

## Proposed exhaustion step

Use the actual Ramanujan Gram and residual limits from the quasimode project.
For a normalized actual eigenvector at bounded renormalized eigenvalue lambda,
its inner product with a normalized Ramanujan profile of energy E is bounded
by that profile's residual divided by `|lambda-E|`. Uniform approximation by
a fixed finite span then excludes spectral points a fixed distance from every
energy in that span. A subsequence argument must retain the established common
lower bound and properness of E(m)>=gamma+log(m).

To exclude extra multiplicity near one E, a spectral cluster of dimension at
least two contains a unit vector orthogonal to the corresponding Ramanujan
profile. All other profile coordinates are small by energy separation and the
cluster residual bound. The finite-span approximation then contradicts unit
norm. This also suggests convergence of each simple spectral projection to the
normalized Ramanujan line. A complete finite-dimensional argument with explicit
quantifiers is still required; this card is not a paper-proof completion.

A useful finite certificate would avoid constructing an infinite operator first:
for each fixed energy ceiling R, find a finite conductor set S and c>0 such
that every unit vector of energy at most R has
`sum_(m in S)|<v_(m,N),x>|^2>=c` eventually, where
`v_(m,N)=u_(m,N)/sqrt(log(N))`. The proposed approximation estimate and the
finite Gram limit should imply this. For each energy in S, choose disjoint
small windows. If a window held two orthonormal actual eigenvectors, a unit
vector in their span could be chosen orthogonal to its one Ramanujan mode.
The other mode coefficients would be small by the residual identity and the
separated energies, contradicting the certificate. All steps still require
proof. No conditional certificate is to be substituted for its actual arithmetic
construction.

The corpus dimension-count input was found in
`HTGeometry/GreedyCourantFischer.lean`, now read in full. Its complex-Hilbert
lemma constructs a nonzero vector orthogonal to any prescribed finite family
by the kernel of the coordinate map and rank-nullity. The real finite-matrix
variant is ordinary supporting linear algebra; no spectral compactness
assumption is hidden in this step.

The strongest useful exact target is: for every real T outside the arithmetic
energy set, the number of actual renormalized eigenvalues below T, counted with
multiplicity, eventually equals `#{m>=1:E(m)<T}`, and their simple eigenlines
converge to the corresponding Ramanujan lines. Properness follows from
`tameDifferent(m)>=0` and `log(m)->infinity`; the exact count and line convergence
do not follow from the current quasimode theorem alone.

## Sharpened finite-dimensional proof plan

The approximation space can be chosen explicitly. Let Q be the primes below
P and let M be their product with every exponent L. If all small-prime
valuations are below L, each fibre indicator is

`product_(p in Q)(1_(p^e_p divides n)-1_(p^(e_p+1) divides n))`.

Expand this finite product. Each term is a divisibility indicator at a divisor
of M. The inspected divisor-to-Ramanujan identity therefore puts every such
fibre indicator in the span of `c_m`, m dividing M. Thus the finite conductor
set can be exactly `M.divisors`; no limiting inversion is required.

For the valuation moment, apply `a^2/2 <= (a-b)^2+b^2` to each edge
`a=x(n*p^k)`, `b=x(n)/sqrt(p^k)`. Reindexing its first sum by the top vertex
gives `log(p)*sum_n v_p(n)*x(n)^2/2`. The second sum is at most
`log(p)/(p-1)*||x||^2`. This proves the proposed bound once the finite
reindexing and geometric tail are written out exactly.

The two approximation errors are orthogonal: fibrewise residual has weighted
mean zero, and truncating the conditional mean stays fibrewise constant.
Their squared sum is at most `K*D/log(P)` plus the finite-prime valuation
tail. Choosing P, then L, gives distance at most 1/2 to the fixed conductor
span for every unit vector of energy at most T. The finite Gram limit bounds
the synthesis map above and below, yielding the positive coordinate certificate.

For implementation, an inequality avoids even the orthogonality calculation.
Let h be the full conditional mean in physical coordinates, and set z=h on
the valuation box and z=0 outside it. Pointwise,
`|x-z|^2 <= |x-h|^2 + 1_(outside box)*|x|^2`.
Thus the rough-fibre variance bound plus the original vector's valuation tail
already gives the needed approximation. No contraction theorem for the
truncated conditional mean is required.

For the counting argument, fix T outside the energy set and let S_T consist
of all conductors with E(m)<T. If the actual spectral subspace below T had
dimension greater than |S_T|, it would contain a unit vector x orthogonal
to all their Ramanujan profiles. It has energy at most T. For every remaining
conductor m in the compactness certificate, E(m)>T, and spectral expansion
gives

`|<v_(m,N),x>| <= ||(A_N-E(m))v_(m,N)||/(E(m)-T)`.

The finitely many right sides tend to zero, contradicting the certificate.
This proves the upper count without subsequences or a new infinite operator.
The existing finite-packet theorem gives the lower count. Thresholds on
either side of E(m) then isolate exactly one eigenvalue eventually. Its
eigenline converges because every other spectral component of v_(m,N) is
bounded by its residual divided by the fixed separating gap. These are
proof steps to implement, not substitute analytic assumptions.

## Scope

This is stronger than the proposed coherent ground-state completion: it would
also rule out extra bounded-energy branches of the original finite matrices.
It needs no claim that all high-energy eigenvalues or growing conductor packets
are uniformly controlled. The existing one-gap theorem and generic spectral
compactness machinery are excluded from novelty. No new result is counted.

The concurrent `rapt-sharp-gap-of-prime-form-is-two-log-two.md` card was read
in full. Its first-gap target is also excluded from this contribution's novelty;
the target here is exact bounded-window counting with multiplicity and convergence
of every fixed eigenline.
Its parent `rapt-top-spectrum-of-prime-form-is-log-integers.md` was also read
in full. That existing open conjecture has exactly the ordered-energy target
`E(m)=gamma+log(m)+tameDifferent(m)`. The proposed exhaustion theorem would
resolve it and strengthen it to multiplicities and eigenline convergence.
No numerical evidence from that card is used in this argument.

The coordinate certificate has an explicit elementary proof once the arithmetic
approximation is established. Choose `z=sum_m a_m v_m` with `||x-z||<=1/2`.
The finite Gram limit gives `||z||^2>=sum_m a_m^2/2`. Since `||x||=1`,
`||z||<=3/2`, hence `sum_m a_m^2<=9/2`, while `<x,z>>=1/2`.
Cauchy--Schwarz therefore gives `sum_m |<x,v_m>|^2>=1/18`.
This constant is only a positive witness; optimizing it is immaterial.

## Exact fibre interfaces inspected

`RHTower/Sieve/SmoothRough.lean` and `RHTower/SteinhausSmoothRoughSplit.lean`
were read in full. They supply the actual factorization, positivity, divisibility,
prime support, and uniqueness needed for the finite horizon partition. In
particular `sieveSmoothPart_mem_smoothNumbers`, `not_dvd_sieveRoughPart`, and
`smooth_rough_pair_unique` avoid reconstructing unique factorization here.
Use small primes `<P`, so their literal smooth factor is
`Sieve.smoothPart (P-1) n` and the complementary factor lies in
`roughInterval P (N/d)` when `n=d*k<=N`.

The fibre energy can be simpler than an induced graph: restrict only its bottom
vertex to `roughInterval P X`, keeping every admissible upper multiplier.
The existing distinct-prime-power edge injection then gives
`log(P)*glauberForm P X (poleGauge x)<=roughPoleDefect P X x`.
An unverified draft of this exact extension and its variance consequence is
`/tmp/TheRoughPrimeDefectControlsVariance.lean`.
For the fibre at d, use `x_d(k)=sqrt(d)*x(d*k)` and divide its bound by d.
The square-root factors cancel in the defect. Unique smooth/rough factorization
partitions the bottom vertices, and `(N/d)/k=N/(d*k)` preserves each edge cutoff.
The sum of all fibre bounds is therefore paid by the literal full defect.

A generic projection-energy search returned
`HTGeometry.nestedOrthogonalProjection_complement_energy_partition` in
`FiniteClockResolutionVariance.lean`, now read in full. It proves the abstract
orthogonal splitting. The arithmetic conditioning map, its finite partition,
and its valuation truncation still have to be constructed exactly; the generic
identity is established supporting infrastructure.

The next exact partition search found the stronger existing input
`RHTower.sum_Icc_eq_smoothRough_sum` in `SteinhausSmoothRoughSum.lean`.
Its complete source was read. It already reindexes every complex finite sum
by literal smooth and rough factors. Taking real parts, interchanging the
finite sums, and absorbing `d*k<=N` into `k<=N/d` supplies the desired real
fibre formula. This reindexing is baseline and must be reused.
The unverified adapter draft is
`/tmp/TheHorizonSplitsIntoSmoothRoughFibres.lean`; it uses the existing complex
sum theorem and the same arithmetic factors. No additional Lean process was
started while the quasimode package was checking.

An alternative finite-span assembly uses the existing CCM gcd-orbit Möbius
law (`CCMRationalZModUnitInvariantMobius.lean`, reread in full). A truncated
valuation-box function factors through `gcd(n,M)`, with `M=product_(p<P)p^L`.
Ordinary finite Möbius inversion expands any such function in the indicators
`1_(d divides n)`, `d divides M`; divisor--Ramanujan inversion then changes
that basis to conductors dividing M. This avoids expanding every product of
shell indicators. Exact factorization through the gcd and the normalized
Ramanujan coefficient bridge remain to verify.

The coefficient bridge was located and its source read:
`BVI/DilationJumpValuationClock.lean` proves
`ramanujanNaturalCoefficient_re_eq_lagCoefficient` for every pair of natural
indices. Taking real parts of `pm_ramanujan_sum_divisors` therefore gives the
exact real coefficient inversion needed here; the quasimode module already
identifies `normalizedRamanujanMode` with that coefficient divided by
`sqrt(phi(m))` for positive conductors.

For each smooth d define the conditional pole-gauge mean with weights 1/k on
that rough interval. The Euclidean approximation is this mean divided by
sqrt(n) on the fibre. The exact squared error should be
`sum_d harmonicVar P (N/d) (fun k => sqrt(d*k)*x(d*k))/d`.
After uniform tensorization, each prime-ladder base edge in this sum maps to
the unique full edge `d*k -> d*k*q^a`; distinct fibre/prime/ladder labels have
distinct edges, and `log(q)>=log(P)`. This is the finite reindexing still to
formalize for the conditional-variance bound.

The conditional-mean adapter now has an unverified draft,
`/tmp/TheSmoothRoughMeanApproximatesBoundedDefect.lean`. It defines the literal
fibre mean and its physical vector, identifies the squared approximation error
with the weighted rough variances, proves the scaled rough defects sum to
the full defect, and assembles the `C/log(P)` error bound. Its imported new
support drafts and the adapter itself still need sequential Lean checks.

The finite gcd-profile expansion has its own unverified adapter draft,
`/tmp/GcdProfilesHaveFiniteRamanujanExpansions.lean`. It reuses finite Möbius
inversion and the inspected real Ramanujan coefficient bridge, then interchanges
finite divisor sums. The output uses the exact normalized modes of the
quasimode theorem and only conductors dividing M. This algebra is baseline
support; the new theorem still requires constructing the bounded-energy
approximation and proving actual spectral exhaustion.

The finite expansion is also established external baseline: Toth--Haukkanen,
[The discrete Fourier transform of r-even functions](https://arxiv.org/html/1009.5281),
Sections 2.3--4. The gcd-function Ramanujan basis and Möbius description were
checked in the primary text through Proposition 2 and its proof. Neither this
algebra nor its Lean adapter is a separately counted contribution.

The exact box-to-gcd adapter has an unverified draft,
`/tmp/ValuationBoxesAreFiniteRamanujanSpans.lean`. The modulus is constructed
from the existing bundled-prime exponent vector, so its prime valuations are
exactly L below P and zero elsewhere. The inspected `Nat.factorization_gcd`
then truncates each retained valuation by `min(v,L)`. Box membership is
preserved, and inside the box the gcd equals the existing smooth part.
Together with the preceding finite expansion, this gives one fixed conductor
set for every truncated smooth-part profile, independently of N and x.

The unverified valuation-tail adapter is
`/tmp/PrimeValuationBoxesCaptureBoundedDefect.lean`. It sets
`B_P=sum_(p<P)(2/log(p)+2/(p-1))` and derives
`mass_(outside box)<=B_P*(D+mass)/L` from the exact moment inequality.
For `mass<=1`, `D<=K`, and any eta>0, choose P with
`log(P)>2C(K+1)/eta`, then L with `L>2B_P(K+1)/eta`.
The conditional error and discarded tail are each at most eta/2. The gcd-span
identity supplies coefficients in the fixed conductor set dividing the box
modulus. Thus these inputs would prove uniform finite-Ramanujan approximation
at every horizon; their Lean checks and final assembly remain.

The complete approximation assembly has an unverified scratch draft,
`/tmp/BoundedPrimeDefectHasFiniteRamanujanApproximation.lean`. For every
K>=0 and eta>0 it selects a fixed finite positive conductor set S such that
every horizon vector with squared mass at most one and defect at most K has
squared distance at most eta from its Ramanujan pole-profile span. It uses
the pointwise truncation inequality and the explicit prime and valuation
cutoffs above. All nine support drafts still require sequential checks;
none is installed, audited, or counted.

The generic finite Gram estimate has an unverified scratch draft,
`/tmp/FiniteGramApproximationCertificate.lean`. Entrywise proximity to identity
gives a one-half synthesis lower bound. A unit vector within distance one-half
of the span then has squared coordinate mass at least 1/18 by Cauchy--Schwarz.
The inspected `ChronologicalHalfTailGram.lean` already uses this perturbation
mechanism, and `GreedyCourantFischer.lean` supplies the rank-nullity argument.
These are baseline supporting linear algebra, not separate contributions.

The actual-matrix energy adapter has an unverified draft,
`/tmp/TheRenormalizedPrimeEnergyControlsTheDefect.lean`. Extension by zero
identifies the existing atomic form with the literal Euclidean matrix form.
Its sharp counterterm bounds defect by `max(0,2(T-gamma+1))` on every unit
energy sublevel, eventually uniformly in N. This discharges the energy-to-defect
step using an existing unconditional theorem and transfers the finite-span
approximation to actual horizon vectors. Eleven drafts now await checks.

The normalized-coordinate adapter has an unverified draft,
`/tmp/BoundedPrimeEnergyHasFiniteRamanujanCoordinates.lean`. It transfers the
existing Gram and residual limits to `u_m/sqrt(log N)`, obtains an eventual
uniform finite Gram lower bound, and combines the actual energy approximation
with the generic certificate. The endpoint constructs the fixed conductor set
and its positive coordinate lower bound for every unit vector of energy at
most T. Twelve scratch drafts now await sequential verification.

The unverified properness adapter is
`/tmp/TheAdjunctionEnergyHasFiniteSublevels.lean`. Nonnegativity of the tame
correction bounds a strict energy sublevel by `m<exp(T-gamma)`. It defines the
exact finite conductor sublevel and supplies a positive threshold gap for
that finite set. This elementary support does not itself count as a contribution.

The unverified finite spectral-window adapter is
`/tmp/HermitianSpectralWindowBounds.lean`. Parseval identifies the shifted form,
bounds squared overlap with a trial vector above T by its residual squared
divided by the squared energy gap, and proves a multiplicity-sensitive window
count from injectivity of finitely many coordinates. The proof uses the literal
Hermitian eigenbasis and finite-dimensional rank, not an assumed compact limit.
Fourteen scratch drafts now await sequential verification.

The actual spectral-count assembly has an unverified scratch draft,
`/tmp/TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum.lean`. It defines the
renormalized eigenvalues of the literal matrix and proves the proposed exact
strict-sublevel count away from arithmetic thresholds. Finite packets give
the lower count. For the upper count, every low spectral vector orthogonal
to the arithmetic sublevel would have all coordinates in the constructed
certificate bounded by a finite sum of residual squares divided by fixed
positive gaps. That sum tends to zero, contradicting positive coordinate mass.
Fifteen drafts remain unchecked; the multiplicity-one and eigenline conclusion
still needs its exact finite-window deduction.

The unverified eigenline deduction is
`/tmp/TheSimplePrimeEigenlinesConvergeToRamanujanLines.lean`. Properness and
energy injectivity produce an isolating radius; the two threshold counts
differ by one. The existing nearby-eigenvalue theorem then gives convergence
of that unique actual eigenvalue. A newly drafted Parseval projection estimate
in `HermitianSpectralWindowBounds.lean` bounds the complementary squared norm
by the actual residual squared divided by the fixed window gap squared.
Thus the proposed spectral projection captures the normalized Ramanujan vector.
All sixteen drafts still await verification and remain uncounted.

## Dependency-closed paper argument for the drafted endpoints

This argument fixes the exact theorem targeted by the sixteen scratch sources.
It is not a valid completed contribution until those sources pass Lean and all
final audits. Write `P_N` for the literal prime matrix, `A_N=log(N)I-P_N`,
`E(m)=gamma+log(m)+tameDifferent(m)`, and
`v_(m,N)=c_m(n)/sqrt(phi(m)*n*log(N))` for positive conductors and N>=2.
For every T outside `{E(m):m>=1}`, the target is

`#{eigenvalues of A_N below T, with multiplicity} = #{m>=1:E(m)<T}`

for all sufficiently large N. Each E(m) additionally has a fixed isolating
window containing one simple actual eigenvalue eventually. That eigenvalue
tends to E(m), and its spectral projection captures v_(m,N) in squared norm.

### 1. The actual arithmetic compactness estimate

For a real horizon vector x, extend by zero and put

`D_N(x)=sum_(u<=N)sum_(t<=N/u) Lambda(t)*(x(ut)-x(u)/sqrt(t))^2`.

The existing sharp counterterm, with epsilon=1/2, gives eventually and
uniformly in x

`<x,A_N x> >= (gamma-1/2)||x||^2 + D_N(x)/2`.

Consequently unit vectors of energy at most T satisfy
`D_N(x)<=K_T=max(0,2(T-gamma+1))`.
The exact double-sum/Euclidean-form identity is part of the energy adapter.

The inspected prime-peeling proof bounds every rough harmonic variance by
`K exp(Psi(Q,X)) G_(Q,X)`, where Psi<=0 for X>=2; for X<2 the variance
vanishes. Thus one constant C>0 works for every roughness threshold Q and
horizon X. On a Q-rough interval with Q>=2, every prime ladder has weight
log(p)>=log(Q). Bound each ladder variance by its edges from the valuation-zero
base. Distinct pairs (prime, positive exponent) give distinct prime powers,
so these edges inject into the literal defect. Therefore

`Var_(Q,X)(sqrt(k)*z(k)) <= C/log(Q) * D^rough_(Q,X)(z)`.

Here only the bottom vertex is restricted to the rough interval; the edge
multiplier t remains unrestricted. This precise restriction matters in the
following partition.

Write every n uniquely as d*k with d Q-smooth and k Q-rough. On the fibre d,
the quotient horizon is X=N/d. Apply the last inequality to
`z_d(k)=sqrt(d)*x(d*k)`. Its pole gauge is exactly `sqrt(d*k)*x(d*k)`.
The harmonic conditional mean h of this gauge, divided by sqrt(n), satisfies

`||x-h||^2 = sum_d Var_(Q,N/d)(sqrt(d*k)*x(d*k))/d`.

The same rescaling multiplies each edge square by d. Dividing by d and
partitioning bottom vertices by their unique smooth/rough factors therefore
gives exactly `sum_d D^rough_(Q,N/d)(z_d)/d=D_N(x)`. Hence

`||x-h||^2 <= C*D_N(x)/log(Q)`.

Large retained valuations are controlled separately. For any prime p, apply
`a^2 <= 2(a-b)^2+2b^2` on every downward p-power edge. Reindexing by the
upper vertex counts exactly v_p(n) edges at n. The bottom term is bounded
by the geometric series `sum_(j>=1)p^(-j)=1/(p-1)`. This proves

`log(p)*sum_n v_p(n)*x(n)^2 <= 2D_N(x)+2log(p)/(p-1)*||x||^2`.

Let `B_Q=sum_(p<Q)(2/log(p)+2/(p-1))`. Outside the box v_p(n)<L for every
p<Q, at least one retained valuation is at least L. Summing the preceding
moment bounds gives

`mass_outside_box <= B_Q*(D_N(x)+||x||^2)/L`.

Set z=h inside the box and z=0 outside. Pointwise,
`|x-z|^2 <= |x-h|^2+1_outside*|x|^2`; thus no projection contraction
assumption is needed. For ||x||^2<=1 and D_N(x)<=K, first choose Q>=2 with
`log(Q)>2C(K+1)/eta`, then L>0 with `L>2B_Q(K+1)/eta`. The resulting
squared error is at most eta, uniformly in N and x.

This approximation lies in one explicit finite Ramanujan span. Set
`M=product_(p<Q)p^L`. The gcd with M replaces every retained valuation by
min(v_p(n),L). It preserves box membership, and inside the box equals the
full Q-smooth part. Thus the truncated conditional mean is `F(gcd(n,M))/sqrt(n)`
for a real function F depending on N and x. Finite Möbius inversion expands
F(gcd(n,M)) in indicators 1_(d divides n), d dividing M. The already proved
identity `sum_(q divides d)c_q(n)=d*1_(d divides n)` expands these indicators
in the normalized Ramanujan modes with q dividing M. The conductor set
`S=M.divisors` depends only on K and eta, not on N or x.

### 2. A uniform positive coordinate certificate

The quasimode theorem gives `Gram(v_(m,N),v_(l,N))->[m=l]` on each fixed
finite positive conductor set. If its entries differ from identity by at most
`1/(2(|S|+1))`, then for every coefficient vector a,

`||sum_(m in S)a_m v_(m,N)||^2 >= (sum_(m in S)a_m^2)/2`.

Indeed the Gram error is bounded by the entrywise error times
`(sum|a_m|)^2 <= |S| sum a_m^2`.

Use the compactness estimate with eta=1/4 and K=K_T. For each unit vector x
of energy at most T, choose z in that fixed span with ||x-z||<=1/2. Then
||z||<=3/2, so its synthesis coefficients satisfy sum a_m^2<=9/2. Also
`<x,z>=1-<x,x-z>>=1/2`. Cauchy--Schwarz in the finite coefficient space
therefore yields

`sum_(m in S)|<x,v_(m,N)>|^2 >= 1/18`.

The constant is only a positive witness. It is uniform over the entire
bounded-energy unit sublevel and all sufficiently large horizons.

### 3. Exact multiplicity-sensitive spectral count

The tame different is nonnegative, so E(m)>=gamma+log(m). Hence
`S_T={m>=1:E(m)<T}` is finite. The finite-packet theorem and the positive
minimum of T-E(m) on S_T give at least |S_T| actual eigenvalues below T,
counting multiplicity, for all sufficiently large N.

For the upper count, suppose the actual subspace below T had dimension greater
than |S_T|. The linear map recording its coordinates against the profiles with
m in S_T has a nontrivial kernel. Normalize a nonzero kernel vector x. Its
energy is at most T and all its S_T coordinates vanish.

For any m with E(m)>T, expansion in the actual Hermitian eigenbasis and
Cauchy--Schwarz give

`|<x,v_(m,N)>|^2 <= ||(A_N-E(m))v_(m,N)||^2/(E(m)-T)^2`.

This estimate holds for every unit vector supported in the entire low spectral
subspace, not merely for a single eigenvector. One direct proof restricts the
Parseval sum for v to that subspace: every residual weight there is at least
(E(m)-T)^2. The remaining coefficient sum for x is one.

Apply this estimate to the fixed finite detecting set from Section 2. A conductor
in S_T contributes zero; every other detecting conductor has E(m)>T because
T is not an arithmetic energy. Its actual residual tends to zero by the
quasimode theorem. Thus the total detecting coordinate mass is bounded by a
fixed finite sum tending to zero, contradicting 1/18. The actual low dimension
is at most |S_T|. Combined with the lower count, this proves the exact assertion.

### 4. Isolation and convergence of the actual eigenline

Fix m>=1. Properness makes the set E(l)<E(m)+1 finite; energy injectivity
separates its members. Choose delta>0 so that |E(l)-E(m)|<2delta implies l=m.
The thresholds E(m)-delta and E(m)+delta are outside the arithmetic energy set,
and their arithmetic counts differ by exactly one. The proved actual counts
therefore imply that the half-open window [E(m)-delta,E(m)+delta) contains
exactly one spectral index eventually. This includes multiplicity and hence
gives a simple eigenvalue.

For any epsilon>0, the existing conductor-m quasimode puts an actual spectral
point within min(epsilon,delta/2) of E(m). It lies in that window and must be
the unique point there. Thus its energy tends to E(m).

Let Pi_N be the literal orthogonal projection onto that window. Every excluded
actual eigenvalue is at distance at least delta from E(m). Parseval gives

`delta^2*||(I-Pi_N)v_(m,N)||^2 <= ||(A_N-E(m))v_(m,N)||^2 -> 0`.

The normalized profile has squared norm tending to one, so this captures its
nonzero limiting line in the unique actual eigenspace. All projections and
residuals here belong to the actual finite matrix; no abstract limiting
operator or assumed spectral compactness enters the argument.

## Refreshed novelty and scope audit

The final corpus queries for full-matrix bounded spectral exhaustion returned
the present quasimode/packet package and other operators, not the exact count.
The compactness query returned unrelated Ramanujan primitive/residue and
hyperbolic-defect estimates. The current concurrent finite-prime valuation-chain
source was inspected through its stated theorem and box construction: its
sharp Poincare constant and finite-prime boxes are excluded from this count.
The earlier ordered-spectrum backlog already conjectures the same energy list;
resolving that conjecture with actual multiplicities and eigenlines is the new
claim, not proposing the list itself.

Additional primary-literature searches again located the previously audited
Hilberdink singular-value and Hilberdink--Pushnitski LCM results. The former's
[abstract and displayed triangular matrix](https://centaur.reading.ac.uk/66059/1/finitetoeplitz.pdf)
concern singular-value asymptotics of a different operator. No matching exact
Mangoldt-matrix exhaustion result was identified in these searches. This is
a bounded literature audit, not a claim of exhaustive worldwide novelty.
The finite gcd/Ramanujan expansion, generic Gram perturbation, rank-nullity,
and spectral projection estimate are baseline supporting arguments.

The contribution targets the prime matrix's bounded translated spectral edge.
Full Weil positivity still requires its archimedean coupling. Neither RH nor
a zero-density conclusion is inferred from this theorem.

## Formalization checkpoint

The paper argument is closed and is followed directly by sequential Lean
verification. First check: `/tmp/TheRoughHarmonicMeasureTensorizesUniformly.lean`;
log `/tmp/TheRoughHarmonicMeasureTensorizesUniformly-check.log`. No exhaustion
source is installed yet. Passing transitive audits will be recorded in
`logs/full-prime-spectrum-exhaustion-axioms-2026-10-28.log`.

The uniform rough-interval tensorization scratch check passed with no diagnostics
beyond a clean transitive audit: propext, Classical.choice, Quot.sound. The
source is installed in RAPT. Its first olean is built solely because the rough
defect adapter imports it. The other fifteen drafts remain unchecked. Current
command is that first dependency build; its tool handle is authoritative.

Uniform tensorization's first dependency build completed: both artifacts exist,
its log is empty, and no owned compiler remains. Sequential verification now
continues with the valuation-moment adapter. The energy draft's finite-sum
coordinate evaluation uses the actual `PiLp.projₗ` linear projection.

The valuation-moment scratch passed with only propext, Classical.choice,
Quot.sound in its transitive audit. Source installed; first required olean is
building for the box-tail adapter. Two of sixteen scratch modules now pass.

The rough-defect variance adapter passed. Its actual prime-power edge injection
and the `C/log(Q)` variance estimate have a clean transitive audit. Source
installed; first required olean builds for the smooth/rough projection adapter.
Three of sixteen scratch modules pass. Spectral exhaustion remains unverified.

The exact smooth/rough horizon partition passed with a clean transitive audit.
It is installed; its first required olean builds for the conditional-mean
projection adapter. All first four scratch modules pass. Twelve remain
unverified, as do the final actual-source audits and exhaustion endpoints.

The conditional-mean adapter passed with a clean transitive audit. Its scaled
rough defects sum exactly to the full defect, and its physical squared error is
bounded by C/log(Q) times that defect. Source installed; first required olean
builds for the finite Ramanujan approximation module. Five scratch modules pass;
eleven remain unverified. The full exhaustion result is still uncounted.

The gcd/Ramanujan scratch's first check failed only at simplification of
nonzero gcd/modulus conditions in the divisor-set identity. Replaced the step
by explicit forward and reverse membership implications. Retry follows;
failed-check axiom output was not retained as audit evidence. Five modules
remain verified, with all five first required oleans now complete.

The gcd/Ramanujan retry passed with only the three standard logical axioms.
The explicit divisor-membership proof closed the local error. Source installed;
first required olean builds for the valuation-box adapter. Six of sixteen
scratch modules pass. All five preceding first dependency builds are complete.

The valuation-box adapter's first check found one ambiguous name: `min_zero`
collides with `Finset.min_zero`. Qualified the order lemma as `_root_.min_zero`.
The retry follows. Failed-check axiom output is excluded from audit evidence;
the six preceding sources and their first dependency builds remain verified.

The valuation-box retry passed with a clean transitive audit. Source installed;
first required olean builds for the box-tail estimate. Seven of sixteen scratch
modules pass. The explicit gcd modulus and its finite Ramanujan conductor set
are now verified; mass capture and the spectral endpoints remain unverified.

All seven required first oleans passed. The box-tail scratch failed on finite-sum
scope around its additive coefficient and an ambiguous `not_imp`. Parenthesized
the summand and qualified the logical lemma; the retry is running. Failed-check
axiom output is excluded. The later eigenline draft now uses the inspected
`Finset.card_le_one_iff` with implicit indices.

The box-tail scratch now passes without diagnostics beyond the clean transitive
axiom report. Removed an unused simp argument and a tactic after `field_simp`
had already closed its goal. Source installed; its first olean builds solely
for the uniform finite-approximation assembly. Eight of sixteen scratch modules
pass, and the first seven required dependency builds are complete. The endpoint
and final actual-source audits remain; count is unchanged.

The uniform finite-Ramanujan approximation assembly passed on its first check,
with a clean transitive axiom report. One fixed conductor set now approximates
every mass-bounded, defect-bounded vector at every horizon. Source installed;
its first olean builds for the matrix-energy adapter. Nine of sixteen scratch
modules pass. The remaining seven include the actual spectral endpoints; all
final actual-source checks and umbrella wiring remain.

All nine first dependency builds passed. The generic Gram certificate's first
check exposed inner-product orientation, an unavailable square-sum lemma, and
missing finite-set/scalar annotations. The scratch now uses explicit real inner
symmetry, the already available finite Cauchy--Schwarz theorem with a constant
one vector, and explicit annotations. Retry follows; failed-check axiom output
is excluded. Nine scratch modules remain verified.

The generic Gram certificate passed after removing one unnecessary tactic separator. Its clean transitive audit uses only propext, Classical.choice, Quot.sound. Source installed in HTGeometry. Ten of sixteen scratch modules pass; all nine preceding required oleans passed. The first Gram-certificate olean is needed by the bounded-energy coordinate certificate. Final source checks and spectral endpoints remain unverified; count stays 3/250.

The matrix-energy scratch first check failed only at PiLp.projₗ: its dependent-family argument is explicit. Corpus-first API search and the mathlib source confirm the signature. Added the constant real family in the scratch; retry follows. Failed axiom output was excluded. Ten scratch modules remain verified, with ten first required oleans passed.

The matrix-energy adapter retry passed with clean transitive axioms. The constant real family closes the coordinate-projection API issue. Actual source installed; its first required olean supports the bounded-energy coordinate certificate. Eleven scratch modules pass, with the preceding ten dependency builds complete. Five scratches and all final actual-source checks remain.
