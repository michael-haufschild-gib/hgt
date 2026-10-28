# Spectral exhaustion by torsion-adjunction energies

- **ID:** full-prime-spectrum-adjunction-exhaustion
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** Ramanujan full-matrix quasimodes; harmonic rough-number tensorization; prime-defect Dirichlet form
- **Statement:** Every bounded energy window of `log(N) I-P_N` converges, with multiplicity, to the simple energies `gamma+log(m)+tameDifferent(m)`.
- **Count:** uncounted; novelty, full paper proof, and Lean remain

## Goal

The finite-packet quasimode project provides actual nearby eigenvalues for each
fixed conductor. It does not exclude additional bounded-energy branches. The
proposed theorem would identify the entire bounded-energy spectrum and its
eigenvectors, thereby determining every fixed ordered eigenvalue asymptotic.
The optimal pole gap would be a consequence, not a separately counted numerical
improvement. No full Weil positivity or RH implication is asserted.

## Gates

- [ ] Full corpus novelty and significance audit.
- [ ] Dependency-closed paper proof of compactness and spectral exhaustion.
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
