# Coherent completion by the prime ground states

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** finite-prime horizon finite part; proposed valuation/KMS diagonalization
- **Count:** uncounted; separate novelty, paper, and Lean obligations

For a finite prime set Q, let H_Q be ell-two on its supported positive integers
and let A_Q be the actual operator `diag(log n)-P_Q+gamma_Q I`. Its complete
finite-prime diagonalization, original maximal domain, simple spectrum, and
compact shifted inverse are now formalized on the valuation-spectrum card.

For Q contained in R, conjecture compatible embeddings obtained by tensoring
with the normalized geometric ground vector at each new prime. In the unique
factorization n=d*e with d Q-supported and e supported on R minus Q,

`V_(Q,R) f(d*e)=sqrt(delta_(R minus Q))*f(d)/sqrt(e)`.

Finite Euler products should prove isometry and composition. The local ground
equation should prove `A_R V_(Q,R)=V_(Q,R) A_Q`, including domain preservation.
The resulting Hilbert completion would have an excitation basis indexed by all
positive integers, with energies

`gamma+log(n)+tameDifferent(n)=gamma+2log(n)-selfIntersection(n)`.

The actual finite-prime operator and the embedding identities must be proved;
defining an abstract diagonal operator with these eigenvalues does not suffice.
Compact resolvent and spectral simplicity likewise require their own proofs.

This completion changes the embeddings of the finite-prime sequence spaces.
Comparison with the original full Weil-test carrier and uniform passage from
arithmetic horizons remain separate problems. No all-primes Weil sign or RH
claim follows from a formal infinite tensor product.

Inspected leads are recorded on
`docs/drafts/pipeline/3-formalized/local-valuation-haar-diagonalization.md`.
No computations, no Lean proof, and no contribution count for this conjecture.

A further corpus query for an infinite-prime ground-state/tame-different spectrum
found `HTGeometry/PrimeLogKMSRealization.lean`. Its construction through line 150
was inspected: the carrier is a vacuum and one prescribed log-prime level per
prime, with normalized transition intensities. It does not identify the present
number-minus-Weil-kernel operator or its coherent ground-state embeddings.
It is baseline for thermal terminology, not evidence for the present conjecture.

Possible construction route: use the physical product with the normalized new-
prime ground vector, prove its coefficient formula and its action on the existing
finite-prime eigenbasis, then prove domain intertwining from the actual spectral
domains. Only after those identities may the all-integer excitation carrier serve
as a concrete realization of the Hilbert completion. Density and the completion's
universal property remain obligations, as do novelty and all-prime energy audits.

A second construction route may avoid rebuilding a tensor-product carrier.
Use each proved coefficient unitary and extend excitation labels by zero under
`S_Q -> S_R`. This defines an isometry, but is not the desired result by itself.
Prove its physical coefficient formula on every existing product eigenvector:
the unchanged-prime factors agree, and every new-prime ground contributes
`sqrt(1-1/p)*p^(-v_p(n)/2)`. Their product is exactly
`sqrt(delta_(R minus Q))/sqrt(e)`. Equality on the complete eigenbasis then
extends the coefficient identity to every vector, because coordinate evaluation
on each side is continuous. This discharges the physical embedding rather than
assuming it. The proved spectral domains then give actual-domain intertwining.

The candidate completion is ell-two on all positive integer excitation labels,
with each finite-prime coefficient space included by zero extension. Every
finite label set is contained in one finite prime sieve, so the union is dense.
This could also prove uniqueness: compatible isometries into another Hilbert
space give the same orthonormal excitation vectors, and density identifies their
completion. None of these new identities has a Lean proof yet; they remain one
prospective contribution, not separate counts for the embeddings and label operator.

The existing generic `HTGeometry/IncompleteTensorProduct.lean` was read in full.
It already constructs the Hilbert completion of finite-excitation pure tensors
from any unit reference family and proves its product inner kernel. Thus generic
incomplete-tensor existence is baseline. The proposed novelty must remain the
specific arithmetic coefficient formula, actual-domain operator compatibility,
and identification of that physical completion.

An exact arithmetic coefficient identity should connect the finite-sieve basis
to the full-horizon quasimodes. For supported positive m,n the proposed identity is

`Phi_(m,Q)(n)=sqrt(delta_Q)*c_m(n)/sqrt(phi(m)*n)`.

At one prime, the existing Blaschke coefficient at excitation k>=1 is zero
below v=k-1, equals `-1/sqrt(p)` at v=k-1, and equals
`(1-1/p)*p^(-(v-k)/2)` at v>=k. These agree algebraically with the displayed
Ramanujan formula; the k=0 factor is the normalized geometric ground state.
Coprime multiplicativity and the finite product should give the full formula.
This identity would make the physical embedding proof particularly direct.
Its exact square-root/product rewrites, finite-prime support conditions, and
Lean verification remain obligations. It is part of the proposed completion,
not another independently counted contribution.

The coefficient search also surfaced
`RHTower/XiTransverseValuationCanonicalReconstruction.lean`, read in full.
It reconstructs finite Xi-shift aperture coefficients from a prescribed valuation
sampling matrix and compares its Gram phases; it does not identify the literal
number-minus-prime-kernel operator, the Ramanujan eigenbasis coefficients, or
these ground-state embeddings. This is an excluded neighbouring construction.

The full-horizon quasimode project offers another physical comparison to audit.
For a finitely supported excitation vector b, set
`J_N b=(log N)^(-1/2)*sum_m b_m u_(m,N)`.
The proposed Gram and residual limits would imply
`norm(J_N b)->norm(b)` and
`norm((log N I-P_N)J_N b-J_N A b)->0`.
Those finite linear-combination consequences alone are supporting statements,
not a new contribution. Coupled to the actual coherent completion, they could
identify the same arithmetic operator as the asymptotic action on every finite
excitation span of the full horizon matrices. A bounded-time unitary-dynamics
comparison may follow from the residuals by Duhamel's identity. No such limit
has yet been formally proved here, and it would still not establish exhaustion
of the entire finite-matrix spectrum.

Literature baseline: Hilberdink's
[multiplicative-matrix tensor theorem](https://doi.org/10.1016/j.laa.2017.06.037)
already treats infinite prime tensor products. Hilberdink--Pushnitski's
[LCM paper, Section 2](https://arxiv.org/html/2401.06892v1)
gives eigenvalue products indexed by finite prime-exponent patterns for its
different kernel. Thus neither prime factorization of a Hilbert carrier nor
integer indexing of tensor eigenvalues can count as new here.

Another carrier identification to audit is the product of geometric valuation
laws `mu_p(v)=(1-1/p)*p^(-v)`. Removing the finite-prime ground factor should
identify the physical embeddings with adjoining constant functions in new
coordinates. Normalized Ramanujan modes should then form the product excitation
basis in that probability-space completion. The finite local completed row is
a reversible jump generator, since
`mu_p(v)*p^(-a)=mu_p(v+a)` for upward step a and downward rate one.
The positive operator obtained by negating the Markov generator should have the local adjunction energies. Extending this to an actual
closed all-prime form, and identifying any profinite-Haar realization, remains
unproved.

The proposed profinite-Haar carrier must be the radial subspace invariant under
multiplication by profinite units. Valuations forget the unit coordinates, and
Ramanujan sums are constant on those unit orbits. Thus their proposed complete
basis concerns the geometric valuation probability space, equivalently the
radial Haar subspace after that identification is proved. Completeness in all
of profinite L2 is not the intended assertion. An actual unit-orbit/radial
identification and the associated measure pushforward remain proof obligations.
The zero p-adic coordinate has infinite valuation and Haar measure zero;
any map to natural-valued valuation coordinates must handle that null set
explicitly. It cannot be treated as a pointwise bijection on the whole carrier.

The targeted radial search found
`CCM/CCMRationalProfiniteHaarUnitRadialization.lean`, subsequently read in full.
It already proves that averaging actual adelic congruence-class samples over
profinite units gives a unit-invariant function on `ZMod N`. This is a relevant
existing finite radialization mechanism; it does not assert the present L2
completion, Ramanujan basis completeness there, or the adjunction generator.
`HTGeometry/PrimeRadialFusionFieldCorrespondence.lean` was inspected through
its profile/fusion construction. That radial terminology concerns formal
power-series differential fields, a different object; it is not a dependency
for this Hilbert-space project.

`CCM/CCMRationalZModUnitInvariantMobius.lean` was then read in full. It proves
that finite unit orbits are indexed by gcd and that every unit-invariant
additive-valued function has a canonical expansion in divisibility indicators.
This supplies a finite radial spanning mechanism. Passing from those indicators
to normalized Ramanujan modes and proving density in the actual radial L2
space still require their own exact arguments.

The exact divisor-to-Ramanujan inversion was subsequently found and its proof
read: `RHTower.pm_ramanujan_sum_divisors` in
`PMPowerDampedMobiusRamanujanExpansion.lean` states
`sum_(q divides d)c_q(n)=d*1_(d divides n)` for positive d,n. Its real-part
version can supply the finite spanning bridge after the already available
Ramanujan coefficient identification. The L2 density and arithmetic operator
identification remain the substantive new obligations.

This also exposes a distinction requiring proof: the finite-prime geometric
ground masses at a fixed ordinary integer contain `delta_Q`, whose product over
all primes vanishes. The expected completion is therefore not obtained by
retaining point evaluations at ordinary integers in the original counting
carrier. A positive result must identify the actual completion and its form,
rather than merely report this obstruction.

The first profinite/Ramanujan corpus query returned
`CCM/CCMRationalProfiniteIntegerCyclicQuotient.lean`; its opening definitions
and quotient argument were inspected. It already supplies the product-of-p-adics
carrier and finite cyclic quotients. `BVI/ResidueModeCompleteness.lean` was
inspected at its statement and basis construction: it concerns a uniform c0
norm on normalized residue profiles, not this probability Hilbert space.
No global Ramanujan-Haar completeness theorem was found by that initial query;
the broader novelty and dependency audits remain open.

For the finite Ramanujan product, the generic Mathlib
`Nat.multiplicative_factorization` is already used by
`ArithmeticFunction.IsMultiplicative.multiplicative_factorization` in
`NumberTheory/ArithmeticFunction/Defs.lean`; that source was inspected.
It accepts a function with coprime multiplicativity and value one at one,
so a separate arithmetic-function wrapper should be unnecessary. Its exact
declaration and proof in `Data/Nat/Factorization/Induction.lean` were then read;
Lean use still needs a scratch check. The inspected corpus helper
`RHTower.Sieve.prod_eq_of_multiplicative` and the vendored
`ArithmeticFunction.IsMultiplicative.prod_factors_of_mult` only cover squarefree
products; neither is the desired full prime-power coefficient identity.

A refreshed harmonic-completion search surfaced
`RHTower/PaperPrimeRotationCoherentOperator.lean` and
`RHTower/RouteRCompletionQuantumCostSeparation.lean`. The former was read in
full: its coherent operator is a finite bilateral weighted-shift compression,
with a Gram Fredholm determinant limit. The latter was read through its marked
completion profile: it concerns an external tensor of a summable Hadamard
corona class. Neither supplies the physical ground-state embeddings or the
actual maximal-domain adjunction completion required here. Their terminology
and generic constructions remain excluded baselines.

The ground-state search also surfaced
`RHTower/CHMDHarmonicGroundPotentialAndMaximalDomainPrimeShiftForm.lean`.
Its first 200 lines were inspected: it identifies the theta-ground potential
and bounded prime-shift form on the continuous theta mass carrier. It does not
supply the discrete geometric-vacuum embeddings targeted here. A comparison
between these two actual carriers would need a separate proved map; matching
prime-shift terminology does not provide one.

The later counting search surfaced `RHTower/EulerActivationSquarefreeProbability.lean`.
Its probability construction through the infinite-occupancy theorem was read.
It already constructs an infinite prime product and proves almost-sure infinite
occupancy, but its critical local law has occupancy probability 1/(p+1), with
a shifted geometric occupied fibre. The proposed ground-state valuation law
has occupancy probability 1/p. These are different measures; the activation
carrier cannot be substituted without a proved change of measure. The generic
infinite-product and cylinder-independence construction is reusable baseline.

An explicit generator target on the geometric valuation carrier is available
for audit. With r=1/p and v the p-valuation, set
`L_p f(v)=log(p)*(sum_(a>=1)r^a*(f(v)-f(v+a))
 + sum_(a=1..v)(f(v)-f(v-a)))`.
Detailed balance is `mu_p(v)*r^a=mu_p(v+a)`, so its proposed quadratic form is
`log(p)*sum_v mu_p(v)*sum_(a>=1)r^a*(f(v+a)-f(v))^2`.
On finite valuation-cylinder functions the full generator sums only the active
prime coordinates. The intended operator is gamma plus its closure, identified
with the actual finite-prime operators through the ground-state embeddings.
Proving that identity, form closability/domain equality, and completeness of the
finite-excitation basis remains necessary. A corpus search for a Ramanujan/Haar
prime-jump generator returned continuous Weil/Doob forms and divisor-jump
operators; no matching geometric-valuation generator was identified among the
inspected statements. This is a lead, not a completed novelty audit.

A concrete probability-space route can use bounded valuation-cylinder functions
as a dense core. The positive local generator displayed above has finite upward
geometric rate, and its downward rate grows only linearly in v; geometric
valuation moments control both its form and its L2 action on bounded cylinders.
The finite-prime ground transform must still prove exact equality to A_Q-gamma.
Completeness of finite Ramanujan products would then make that core essentially
self-adjoint; the claimed closure cannot be supplied as an assumed interface.

The local energy also suggests a conditional-variance representation. Let E_K
be conditional expectation for the partition v=0,...,K-1 and the tail v>=K;
E_0 is expectation onto constants. The k-th nonconstant radial Haar mode is
fixed by E_K exactly when k<=K. Its energy is
log(p)*(k+1/(p-1)), so the proposed exact form identity is

`<f,L_p f>=log(p)*(p/(p-1)*norm(f-E_0 f)^2
                         +sum_(K>=1)norm(f-E_K f)^2)`.

On finite Haar sums this follows by finite orthogonality; extending by monotone
nonnegative sums would identify the closed form. Each term is a conditional
variance, suggesting a direct Markov-contraction proof and a reversible
all-prime semigroup after the carrier and core identities are proved.
This is an unverified mechanism within the same completion candidate, not a
separate contribution or a generic hierarchical-Laplacian novelty claim.

A later source search found the exact required measure already in the corpus:
`HTGeometry/PrimeValuationSector.lean`, inspected through its cylinder and
zero-point results, defines `primeValuationLaw(p)=geometricMeasure(1-1/p)` and
`primeValuationMeasure=Measure.infinitePi primeValuationLaw` with probability
instances. Its cylinder masses are exactly the sieve density. Reuse this
carrier; construction of the geometric product measure is excluded baseline.
This supersedes the need to adapt the different Euler-activation measure.
The physical finite-prime unitary, complete Ramanujan basis, actual closed
adjunction generator and domain intertwining remain the intended new content.

The same search also surfaced `PoissonEulerSobolevNaturalCone.lean` (local-law
section inspected): its valuation probabilities use p^(-2r) for r>1/2 and
belong to a normalizable counting-space vector. That is a different parameter
regime; the critical product carrier above is the appropriate existing object.
`FieldOnePadicCyclicHaarQuadrature.lean` was inspected through its finite cyclic
quadrature and Fourier definitions. It supplies literal normalized p-adic Haar
and exact finite-level integration, useful for a later proved radial-Haar map;
that map is still absent here.

The exact-measure use search also found `HTGeometry/PrimeValuationInfiniteSupport.lean`
and `PrimeValuationLevelStructure.lean`, both read in full. Almost-sure infinite
prime support, nullity of all ordinary-integer valuation vectors, exact local
tail probability p^(-m), and almost-sure finite repeated-prime support are
already proved. They supersede the earlier merely proposed carrier distinction;
none counts as new here. The remaining sector source supplies measure-preserving
coordinate evaluations and independence. These give concrete measure inputs
for the desired L2 basis and generator without changing probability laws.
