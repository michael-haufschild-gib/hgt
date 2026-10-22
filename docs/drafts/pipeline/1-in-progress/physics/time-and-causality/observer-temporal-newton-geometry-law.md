# Observer-temporal Newton geometry law

- **ID:** `observer-temporal-newton-geometry-law`
- **Stage:** 1-in-progress
- **Type:** MASTER THEOREM CANDIDATE / UNIVERSAL LAW / QUANTUM RECURRENCE
- **Parent:** `observer-time-ensemble-cascade-law`
- **Scientific status:** `[WEIGHTED CORE SCRATCH-VERIFIED]`
  `[FINITE/COUNTABLE WHOLE-LAW SOURCE WRITTEN]`
  `[LOCAL HERMITIAN MASTER SOURCE WRITTEN]`
  `[FINITE CASCADE TERMINATION LEAN-VERIFIED]`
  `[PHASE-SUPPORT IDENTITY SOURCE WRITTEN]`
  `[TERMINAL HAAR / INFINITE CASCADE SOURCE WRITTEN]`
  `[FINAL DEPENDENCY AUDIT PENDING] [PRIORITY AUDIT OPEN]`

## Question

What single mathematical object is casting the already proved shadows called
spectral recurrence, perturbative birth order, observer-time dimension,
connected-cluster locality, replica order and weak-coupling phase-ensemble
wall crossing?

## Jump

The scalar recurrence time is not the primitive object. For an observer
character \(k\) and local coupling vector
\(\mathbf g=(g_e)_{e\in E}\), the primitive object is the analytic spectral
relation germ
\[
  R_k(\mathbf g)=\sum_j k_j E_j(\mathbf g).
\]
Its multivariate Taylor support, together with the observer-visible
character lattice, defines an observer-temporal Newton geometry.

Every scalar switch-on schedule
\[
  g_e(\varepsilon)\sim c_e\varepsilon^{w_e}
\]
is a valuation of this geometry. Its observed birth exponent is the least
weighted Taylor degree surviving in the corresponding initial form. Thus
different experimental ways of turning on the same interactions are
different one-dimensional shadows of one invariant object.

## Candidate universal law

For every finite Hermitian local quantum system with a simple decoupled
product spectrum, every positive integer interaction weighting, every real
switch-on direction and every finite observer:

1. the observer contrast is either the zero analytic germ or its exact birth
   order is no smaller than every weighted connected interaction packet
   spanning that observer;
2. persistent rational spectral-constraint rank plus resolved temporal
   dimension is exactly conserved at every Taylor resolution;
3. at every inverse-power observation horizon, the complete uniformly
   time-sampled phase probability law has one unique weak limit;
4. every character of that limit is in exactly one of three regimes:
   unresolved, universal sinc window, or dephased, according as observation
   order lies below, at, or above its analytic birth valuation.

The same complete phase-law conclusion extends from every finite analytic
real spectrum to every countable analytic real spectrum because every
reporter character has finite support.

## Stronger synthesis: support conservation and finite--infinite fracture

The algebraic filtration and the probability-law wall crossing are not
parallel analogies.  At horizon \(g^{-r}\), the projective characters that
equal one almost surely under the unique limiting phase law are exactly the
relations whose spectral jets vanish through order \(r\).  Consequently
the rational codimension of the limiting law's almost-sure character
constraints equals the resolved temporal dimension:
\[
 \dim_{\rm phase}(\mu_r)
 =
 \dim_{\mathbb Q}\operatorname{range}J_{r+1}.
\]
Thus temporal dimension can be defined from the observed probability law
alone.  Exact conservation becomes
\[
 \dim_{\rm phase}(\mu_r)
 +\operatorname{rank}_{\mathbb Q}
   \{\hbox{almost-sure phase constraints of }\mu_r\}
 = |I|-1.
\]

Finite and infinite spectra then separate sharply.

* For every finite analytic spectrum, the descending constraint filtration
  stabilizes at one finite order.  Beyond that last temporal birth, every
  active projective character has limiting Fourier coefficient zero and
  every exact relation has coefficient one: the terminal projective law is
  Haar on the exact observable phase quotient.
* One explicit countable analytic spectrum,
  \(E_0(g)=0,\ E_{n+1}(g)=g^{n+1}\), has a projective character born at
  every positive order.  It therefore has no terminal temporal layer, while
  its complete countable phase probability law still has a unique weak
  limit at every inverse-power horizon.

This yields the proposed worldview statement:

> finite quantum systems eventually finish revealing their observable
> temporal geometry; infinite quantum systems need not.

`FiniteTemporalCascadeStabilizationLaw.lean` is dependency-closed and
foreground-verified.  `ObserverTemporalPhaseSupportLaw.lean`,
`FiniteTerminalTemporalHaarLaw.lean`,
`InfiniteTemporalCascadeWitness.lean`, and
`LocalObserverTemporalSupportConservationLaw.lean` contain the source-level
closure and await the final dependency build.

This is now represented by production sources
`WeightedInteractionPacketNewtonLaw.lean`,
`WeightedObserverTemporalSteinerLaw.lean`,
`WeightedObserverTemporalBirthLaw.lean`,
`FiniteAnalyticPhaseEnsembleWallCrossingLaw.lean`,
`CountableAnalyticPhaseEnsembleWallCrossingLaw.lean`, and
`LocalWeightedPhaseEnsembleLaw.lean`.  The replica reduction, weighted
cardinality identity, proper-restriction cancellation, lifted analyticity
and arbitrary-direction factorization compile in the isolated foreground
scratch audit.  Production dependency closure awaits the one final module
build.

## Stronger master conjecture

For every finite local analytic spectral family and every finite observer:

1. the multivariate spectral-relation germs define a canonical tropical
   character complex (a valuated matroid only if exchange is proved);
2. its support decomposes exactly into spatially indecomposable interaction
   packets spanning the observer;
3. every positive coupling weight \(w:E\to\mathbb R_{>0}\) induces a scalar
   birth valuation
   \[
     v_w(k)=
     \min_{\alpha\in\operatorname{supp}R_k}
       \sum_e w_e\alpha_e;
   \]
4. the kernel flag of \(v_w\) obeys exact dimension/constraint conservation;
5. observation on \(T=\tau\varepsilon^{-r}\) converges to the unique phase
   probability law whose character transform is \(1\), the initial-form
   window kernel, or \(0\) according as \(v_w(k)>r\), \(=r\), or \(<r\);
6. for every endpoint rectangle, local edge geometry excludes all monomials
   below weighted Steiner cost. For generic unrestricted edge-local
   Hermitian interaction, the weighted-Steiner initial form is nonzero.

Items 1--5 would identify an explicit Newton/tropical object behind the
already sourced complete wall-crossing theorem. Item 6 remains the
non-tautological generic physical sharpness theorem. Neither is required
for the universal lower-and-limit law above, but both would strengthen its
geometric reconstruction content.

## What is already unconditional

The corpus proves the following scalar and Boolean shadows:

- every finite-support character has an exact analytic birth valuation;
- that valuation is non-Archimedean and its relation kernels are saturated;
- lost rational constraint rank equals gained observer-time dimension;
- every active scalar character has exact unresolved/window/dephased wall
  crossing;
- all convergent character transforms determine one unique weak phase law
  on finite and countable product tori;
- local spectral germs decompose exactly into noncancelling connected
  observer-spanning interaction packets;
- an active observer ray is born no earlier than its connected-packet
  Steiner cost;
- two-site rectangle characters form an independent second-replica family
  of exact rank \((|A|-1)(|B|-1)|C|\), giving
  \((q-1)^2q^{n-2}\) delayed constraints in an \(n\)-site \(q\)-level
  product spectrum.

These are necessary projections of the conjectured geometry, not yet a
proof of the multivariate master object.

## What this would mean

Previous work asks for a recurrence time, a Thouless time, a perturbative
order, a graph distance or a detector order separately. The proposed law
says these are coordinate readings of one observer-dependent Newton
geometry:

> quantum time is the valuation geometry of the spectral relations an
> observer can test.

This is not an extra spacetime dimension. It is a complete operational
geometry of which relative phases exist at each observation horizon.

Locality then has a sharper meaning than finite propagation speed. It
restricts which temporal directions can be born at all at a given
interaction cost. A distant pair already carries exponentially many
independent low-replica relations, all excluded from early temporal layers.

## Apex correction: law before rank

Hostile review rejects identifying rational character rank with geometric
support dimension. A one-dimensional irrational phase segment can have no
nonzero rational character fixed almost surely, hence maximal rational
character rank despite topological dimension one.

The master invariant must therefore be the complete scale-indexed phase
probability law, not its relation-rank shadow. Its proposed universal
Fourier law is
\[
 \widehat\mu_{w,r,\tau}(k)=
 \begin{cases}
  1,&v_w(k)>r\ \text{or }k\text{ is exact},\\
  \operatorname{sinc}(\tau c_{k,w}),&v_w(k)=r,\\
  0,&v_w(k)<r,
 \end{cases}
\]
where \(v_w(k)\) is the weighted analytic birth valuation and \(c_{k,w}\)
is its nonzero initial coefficient. Uniqueness of compact-torus Fourier
transforms makes these coefficients one probability law, not a collection
of scalar analogies.

All proposed consequences must now be derived as functionals of this law:

- locked-character rank gives observer phase-relation dimension;
- weighted locality bounds which Fourier modes can leave \(1\);
- critical sinc profiles retain crossover information erased by rank;
- recurrence and return-target geometry are read from the same law;
- finite spectra reach a terminal projective Haar transform after the last
  valuation layer, whereas countable spectra need not have a last layer.

The phrase “support dimension” is forbidden unless an actual geometric or
measure-theoretic support dimension is proved. Use “rational phase-relation
rank” or “observer character dimension”.

## Remaining formal targets

1. Run the dependency-closed build and repair any integration errors in the
   complete Fourier-law, weighted observer, finite/countable ensemble and
   calibrated local-character master sources.
2. Package the full limiting Fourier trichotomy for every character; do not
   reduce it to the unit-character/rank corollary.
3. Define the character initial form and prove tropical evaluation for
   every weight vector away from its finite cancellation fan.
4. Formalize the labelled-cycle witness proving generic exact weighted
   distance birth for every two-site rectangle.
5. Derive the existing recurrence rate--distortion and observer-return laws
   as explicit functionals or terminal consequences of the same probability
   law.
6. Decide whether mixed moments on compact polydisks give a dependency-closed
   whole-law extension for contractive open-system modes; keep only the
   already proved per-mode semigroup wall crossing if this does not close.

## Hard falsifiers

Reject this route if any occurs:

1. analytic packet response is not divisible by the product of the
   interaction coordinates in its packet;
2. two distinct packet sectors can cancel as multivariate germs despite the
   proved Möbius projector orthogonality;
3. weighted scalar birth is not the minimum weight of a surviving Taylor
   monomial;
4. character valuations fail the valuated-matroid exchange law;
5. the labelled-cycle endpoint witness has zero weighted-Steiner initial
   form;
6. primary literature already contains the full chain from local analytic
   spectrum through valuated character geometry to unique phase-law wall
   crossing.
7. the limiting-law unit-character space differs from the stabilized jet
   relation space;
8. a finite analytic spectrum supports infinitely many strict temporal
   dimension jumps.

The initial priority search found Newton polygons applied to exceptional
point eigenvalue splitting and linked-cluster theorems applied to
perturbative support. It found model-specific hydrodynamic, random-matrix
and dissipative spectral-form-factor crossover results. It did not find the
deterministic chain

\[
\text{weighted locality}\to
\text{all spectral-character births}\to
\text{rank conservation}\to
\text{unique whole phase-law wall crossing}.
\]

This remains provisional until citation-by-citation priority review is
complete.

Failure of item 4 would kill the word “matroid”, not the Newton-geometry
law. Failure of item 5 would kill generic graph-distance sharpness and the
headline claim that locality hides activatable clock directions.

## Nature gate

Passing mathematical closure is insufficient. The paper must show that this
geometry changes how researchers understand an existing broad problem:
the weak-coupling emergence of spectral correlations and recurrence
statistics. It must derive at least one experimentally or numerically
testable multi-scale prediction not obtainable from a conventional scalar
Thouless-time fit. Otherwise the result belongs in a specialist
mathematical-physics journal.
