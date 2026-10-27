# Arithmetic Lorentzian geometry: what could produce the missing sign?

This report uses the route ledger, killed-route ledger, route-unification ledger,
`route-obstacles.md`, walls ledger, `fable2.md`, and the requested programme READMEs in their
specified order. Repeated README paths were read once. Mathematical leads were followed through
the corpus search tool into Lean statements. No web sources or numerical experiments were used.
The research log is [astra-arithmetic-lorentzian-2026-10-27.log](../../../logs/astra-arithmetic-lorentzian-2026-10-27.log).

## 1. Assessment

**The best opportunity is to construct a compatible arithmetic sign, rather than another
equivalent formulation of it.** Arithmetic Lorentzian geometry is a useful programme for this
purpose, provided it distinguishes three tasks:

1. Construct forms whose signature follows from elementary operations.
2. Identify those forms with, or prove the required domination of, the actual Weil intersection
   form, including its poles and infinite place.
3. Preserve that comparison on an exhaustive family of signed tests.

The corpus contains substantial solutions to parts of each task. It does not yet contain their
composition into an RH proof. The walls restrict particular mechanisms; they do not establish
that all symmetry, all geometry, or all future realizations are impossible. Nor can a corpus
review establish that mathematics as a whole lacks every suitable tool.

### 1.1 What the programmes collectively establish

The early incidence programmes locate the square-root threshold and the loss of sign in unsigned
estimates. Orientation and criticality translate that loss into an arithmetic energy or defect.
The surface and correspondence programmes identify the missing sign as Hodge index, distinguish
identities from positivity, and provide fake data that satisfy the identities. Gauge and duality
programmes identify what multiplicative information forgets and what successor information
recovers. Polarization and conjugate-diagonal geometry separate the positive form from the
equivariant form. Electrostatics computes their discrepancy through currents, moments and work.
Renormalization determines which signs survive subtraction. Spacing analysis starts paying the
actual interactions jointly. Lorentzian geometry asks whether that payment can become a
construction principle.

This progression is mathematically cumulative. A stronger receiver, a computed defect, or an
exact equivalence remains valuable: it exposes precisely what a new producer must deliver. But
describing an escape state does not exclude it; computing a nonnegative defect does not bound it;
and recognizing an RH-equivalent signature does not construct it.

### 1.2 Changes to the picture in `fable2.md`

Several proposed questions require updating before they become a foundation.

| Proposal or older frontier description | Current mathematical position |
|---|---|
| Stability stops below the atomic spacing. | SSHA proves Markov positivity at `w ≤ c₀ log(1+1/N)`, uniformly in `N`, and full Weil positivity after a rank-one pole correction. |
| Paying that pole correction is always still missing. | The current ACS section theorem retains a weighted reserve and pays both pole moments on independent arithmetic sections at a smaller fixed spacing fraction. It proves the full Weil form dominates their square mass. |
| Zero defect at any fixed spacing fraction would prove RH. | These separated families already have unconditional positive results. Their dimensions grow, but their shrinking supports do not by themselves give an exhaustive test space. |
| Montgomery at `α=1` is equivalent to an `o(log N)` worst-eigenvalue bound. | `fable2.md` labels this an interpretation. An averaged pair statistic and a uniform inequality over signed coefficient vectors have different quantifiers. The identification requires a theorem. |
| Every unbounded overlap schedule is already covered. | The exact inspected SSHA theorem uses one fixed cubic spline and all finite integer-log translates. Its negative index detects all distinct right-half-strip zeros. A general moving-width schedule needs its own transfer proof. |
| Nonnegative coefficients and connected links supply the curve sign. | ALG's golden datum has the Metzler sign, connected support and a positive weight with positive image, yet fails weighted trickle-down. The local signature input still carries substantive information. |
| Dirichlet characters form the periodic part of the full unit prime torus. | Characters at primes dividing the conductor vanish; full-torus characters have unit modulus. Their domains and missing local factors must be specified. Vertical characters also preclude the proposed naive periodicity classification. |
| The scale map already realizes the archimedean factor. | A substitution of variables is defined; equality with the required Γ-term, polar terms and renormalized diagonal is a separate, unproved construction. |

The relevant exact statements are
`markovEnergy_atomicTest_nonneg_spacing` and `re_W_add_sinh_sq_nonneg_spacing` in
[SSHA's stability module](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheStabilityLawAtTheSpacingScale.lean),
`integral_sq_le_weilPair_arithmeticSection` and `arithmeticSections_effectivity` in
[ArithmeticSectionsPayThePole](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticSectionsPayThePole.lean),
and `riemannHypothesis_iff_splineAtomic_negIndex_eq_zero` in
[UnboundedOverlapIsTheRiemannHypothesis](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/UnboundedOverlapIsTheRiemannHypothesis.lean).
These statements concern different families; they must not be substituted for one another.

Two further advances change priorities. The simple-pole completed positive class identifies
`ζ` up to a nonzero real scalar; identity of the source no longer needs to be rediscovered in
that class. And IGP proves a strict gain over the Montgomery–Taylor simple-critical proportion
by retaining Gram slack below the pair-correlation barrier. Thus a threshold of a particular
estimate is not necessarily a threshold of all arguments using the same range. Neither result
supplies all-test Weil positivity. See
[TheSimplePoleClassIsZeta](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/TheSimplePoleClassIsZeta.lean)
and `HD_one_add_pos_le_liminf_xiSimpleCriticalRatio` in
[CriticalLineZeroProportion](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean).

## 2. Question 1: opportunities for a different proof mechanism

### 2.1 Compatible gluing, with an exact cost

The statement “local Hodge inequalities do not add” is too coarse to guide construction. It has
an exact positive successor.

Let `Q_i` be finite symmetric forms and let `e` have positive square for each. Put

\[
a_i=Q_i(e,e)>0,\qquad b_i(x)=Q_i(e,x),\qquad
R_i(x)=\frac{b_i(x)^2}{a_i}-Q_i(x,x).
\]

Each local form is hyperbolic exactly when `R_i ≥ 0`. For `Q=Σ_i Q_i`, `A=Σ_i a_i`, define

\[
V(x)=\sum_i a_i\left(\frac{b_i(x)}{a_i}-\frac{\sum_jb_j(x)}A\right)^2.
\]

The exact law is

\[
\boxed{R_Q(x)=\sum_iR_i(x)-V(x).}
\]

Consequently, the sum is hyperbolic **exactly when its local reserves dominate the dispersion
of its local polar rows**. Common negative hyperplanes are the zero-dispersion case. Local
hyperbolicity alone misses the cost `V`.

The scalar weighted-variance identity already exists as `HTGeometry.schurComplement_sum_eq` in
[QuotientFusionProjectionGenesis](../../../formal/GaloisForLFunctions/HTGeometry/QuotientFusionProjectionGenesis.lean).
The ALG development here uses it to construct the matrix

\[
C_e(Q_i)=\sum_i\frac{(Q_i e)(Q_i e)^T}{a_i}
          -\frac{(Qe)(Qe)^T}{A}.
\]

It is positive semidefinite and annihilates `e`. Subtracting it from `Q` leaves the anchor row
unchanged and adds the local reserves exactly. Thus `Q-C_e(Q_i)` is hyperbolic whenever the local
forms are. This is a precise closure operation, not a claim that the original sum has the same
signature. See [PolarGluingAndDispersion](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/PolarGluingAndDispersion.lean).

**Arithmetic opportunity.** Seek a source-defined decomposition of the *whole* intersection
form, together with an archimedean, successor or overlap energy that pays this dispersion.
The question becomes a comparison of explicit forms. It is no longer “find a common base”
without specifying what compatibility costs. SSHA's joint use of tilted prime rows and the
archimedean cross kernel is evidence that paying two interacting costs together can succeed
where their separate norms fail.

**Boundary.** The prime towers in AIT are not automatically the `Q_i` of such a decomposition.
Their positive local KMS forms and a one-positive-square intersection form are different
objects. Adding a pole to each tower can overcount the same global pole. The anchor, all local
reserves, and the comparison with the actual target must be constructed explicitly. Subtracting
`C_e` merely because it would help changes the problem.

### 2.2 Construct links from arithmetic sections

The most promising higher-degree version of `fable2.md` is a section or incidence construction
whose links inherit a signature theorem for an independently proved reason. The important
analogy with combinatorial Hodge theory is the inductively closed class of objects, not the word
“Lorentzian.” A proposed cubic lift whose links are assumed hyperbolic has moved the question.

ALG already makes this diagnostic exact. For connected Metzler forms in the positive-image
regime, weighted trickle-down is equivalent to hyperbolicity. The golden datum passes the
entrywise sign and connectivity tests but fails the inequality. See
[TheMetzlerDichotomy](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMetzlerDichotomy.lean)
and [TheFrobeniusLadderIsMetzler](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheFrobeniusLadderIsMetzler.lean).

A productive calibration would therefore start with actual finite-field sections or an actual
counting construction, produce the links, and recover their signature without inserting purity
as an input. The corpus already has counting proofs for actual curves; those are a stronger
starting point than abstract nonnegative point counts, which the fake curves share. The
transport problem is then which arithmetic operation over `ℤ` replaces the relevant flatness,
dimension count or product-formula estimate.

### 2.3 Retain structural slack before seeking a stronger analytic range

IGP provides a concrete success of this principle: an equality pattern allowed by a trace
estimate is incompatible with the non-lattice zero set of the actual correlation kernel.
Keeping the resulting slack gives a strict unconditional improvement.

The corresponding opportunity for Weil positivity is to identify incompatible near-equality
patterns for the prime, archimedean and pole estimates. A norm bound optimized independently
for each term may pay for vectors that cannot simultaneously be extremal. The polar-dispersion
law is one algebraic language for such incompatibility; tilted Schur weights are an existing
analytic instance. A useful result must quantify the slack on signed vectors in the required
norm, not merely exhibit different extremizers.

This can circumvent a wall attached to a particular estimate. It does not destroy the general
need for an arithmetic sign or prove RH from a positive-density gain.

## 3. Question 2: three research questions to prioritize

### Priority 1 — What arithmetic construction pays polar incompatibility?

**Precise target.** Construct finite arithmetic forms, their anchor and their link or gluing
maps from the source. Prove their identification with the required intersection form. Then
derive the dispersion payment or weighted trickle-down inequality from an independent
arithmetic operation.

An acceptable finite-field prototype must distinguish actual curves from the golden datum
and complex fake for a named structural reason. A theorem for all abstract curve data with
nonnegative counts cannot do this. For `ℤ`, an acceptable construction must explain where the
successor or the fixed infinite place enters; prime-side diagonal conjugacy otherwise transports
the construction to sign twins.

**First substantive milestone.** An exact decomposition and payment on a larger explicit
family than the already positive spacing-scale sections, with a quantified reserve that remains
available for extension. The new gluing law supplies an invariant to calculate, not its desired
arithmetic bound.

**Why first.** This addresses the producer common to the three unified routes. More receivers
will not substitute for it.

### Priority 2 — Can signed positivity survive overlap on an exhaustive family?

**Precise target.** Extend source-defined positivity from separated sections to overlapping
tests while controlling the actual overlap Gram, prime lag form, archimedean cross form and both
pole moments together. Establish transfer in a topology controlling Weil's form. Growing
dimension alone is insufficient.

The non-ratio terms have the explicit gauge factor

\[
\omega(k)-\omega(m)\omega(n),\qquad
|\log k-\log(n/m)|\lesssim w.
\]

It vanishes on exact ratios. This identifies where prime-side gauge information reappears.
But a coefficient margin does not imply a signed form margin, and the diamagnetic inequality
still makes a modulus-closed Markov lower-bound argument accept dominated twins. The pole and
the chosen signed domain must be accounted for. See
[TheGaugeEntersThroughNonRatioLags](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeEntersThroughNonRatioLags.lean)
and [TheDiamagneticInequality](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDiamagneticInequality.lean).

**First substantive milestone.** A bounded-overlap inequality with an explicit error measured
in the overlap norm, plus a transfer theorem identifying which aperture or orbit it controls.
Next, determine whether its reserve survives iteration. The fixed-spline negative-index theorem
provides a precise exhaustive endpoint; it does not license every unbounded-overlap schedule.

**Why second.** The corpus has now paid the full form on real arithmetic section spaces. The
remaining question is their extension, not another coarse self-energy constant or an assumed
average-to-operator equivalence.

### Priority 3 — What forces the exceptional set to be empty?

**Precise target.** Turn the arithmetic reading of a candidate off-line zero into an upper
bound below one transverse-energy quantum, or prove a propagation law that makes one exception
incompatible with an available global budget.

AES supplies source-work exhaustion, energy quantization and power-sparse alignment sets.
The missing implication is pointwise: an off-line zero must force a sufficiently large signed
prime statistic at its own ordinate, or enough companions to exhaust the budget. The outward
reserve inside the strip cannot simply be continued into `Re s>1`; the archimedean background
and the signs of other zero contributions matter.

**First substantive milestone.** A depth-dependent forcing law at the actual zero ordinates,
with the needed length and conductor stated. Compare its exceptional-set bound with existing
zero-density results. For exclusion, strengthen it to a subquantum bound or a proved
exception-propagation contradiction. A vanishing proportion still permits one zero.

**Why third.** This is an independent route to exclusion. It tests whether the newly computed
positive quantities can constrain the divisor, rather than only describe it. The objects and
thresholds are in [ArithmeticElectrostatics](../../../formal/GaloisForLFunctions/ArithmeticElectrostatics/README.md).

## 4. Question 3: a field capable of supplying these tools

**Arithmetic Lorentzian geometry should be the theory of source-defined signature certificates
and their compatibility under arithmetic operations.** The affine monoid supplies its arithmetic
language; anchored forms, links and finite parts supply its geometric language. The aim is a
Hodge index theorem for the specified arithmetic pairing, with the origin of its sign visible.

### Objects

* Finite spaces of real or complex arithmetic tests and their exact Gram matrices, with the
  pole plane retained. Real hyperbolicity and Hermitian inertia are related but distinct APIs.
* Anchored symmetric forms, their polar rows, Schur reserves and dispersion corrections.
* Source-defined section spaces and incidence complexes with restriction or link operations.
  A positive signature is a theorem about these objects, not a field in their definition.
* Prime ladders, successor maps and logarithmic cells, with their exact affine relations.
* Gauge-twisted kernels together with a fixed archimedean and polar structure. The common
  gauge matters; the spectrum of the prime kernel alone does not select the source.
* Regulated families, counterterms, finite parts and comparison maps. Changing a basis,
  changing a regulator, and changing the quadratic form are different operations.
* Exhaustions and their analytic norms, recording which tests the finite certificates reach.

### Language and principles

Use signature, primitive hyperplane, reserve, dispersion, link, pullback, domination, finite
part and exhaustion. Introduce higher-degree support conditions only with the operations that
need them. Lorentzian log-concavity must not be conflated with real stability or real-rootedness.

1. **Fix the target before constructing its certificate.** An identity or domination theorem
   must connect the constructed object to the full arithmetic form.
2. **Keep the sign local enough to prove and strong enough to transfer.** Connectivity alone
   does not supply local signature. Count or construct the links.
3. **Measure compatibility.** A sum pays polar dispersion; a regulator pays its counterterm;
   an overlap extension pays its cross terms; a localizer pays its conductor.
4. **Separate source selection from sign production.** Successor flatness may identify the
   Euler gauge without proving any Hodge inequality there.
5. **Keep a common budget.** The two global pole moments cannot be spent independently at
   every prime or every link.
6. **Treat the limit as a theorem.** Control signed tests in a form-controlling topology;
   specify what survives and what exhausts the target space.
7. **Scope obstructions.** A failure of scalar counterterms or multiplicative localizers
   constrains that construction class. Extract its exact positive survivor.

### Tools and foundational pillars

The degree-two foundation is already strong: reverse Cauchy–Schwarz, hyperplane criteria,
pullback, domination, CND closure, the scaling-surface bridge and nef shifts. Trickle-down and
the Metzler dichotomy add local-to-global tests and a sharp calibration failure. The development
here adds polar gluing: the reserve identity, the positive correction and the constructed
hyperbolic form. These are tools for producing and comparing certificates; their application
to the full arithmetic target remains a mathematical question.

The next tools should be a source-defined link calculus; multiscale gluing with the actual
cross forms; a quantitative overlap transfer; and a signature argument retaining structural
slack. Higher-degree Lorentzian polynomials belong when a constructed polynomial has an
arithmetic Hessian identity. An Euler product with positive coefficients alone does not supply
that identity or the required signature of its derivatives.

### Position among the programmes

ACS and AOG specify the target and calibrations. AIT supplies local towers and exact transfers.
AET supplies counts and growth laws. BGG and ACG supply gauge selection and charged operations.
APol and CDG supply the distinction between positive and equivariant pairings. AES supplies
quantized defect and work. RBG and RAPT supply the rules of subtraction and survival. SSHA
supplies joint analytic payment. ALG should own the construction and composition of signature
certificates connecting these results. It should import these tools rather than rename them.

### Success criteria

A contribution must prove an unconditional theorem about a constructed object, state its exact
domain, and identify its arithmetic content. Algebraic structural conditions must remain
explicit; no unknown arithmetic estimate may be hidden in an interface. A claimed advance toward
RH must identify which producer or transfer step it improves, and which fake or twin it excludes.

The programme succeeds at its full RH target only when a source-defined construction reaches
the actual Weil form on an exhaustive family and proves the needed signature. The present
foundations, exact gluing laws and local arithmetic positivity do not complete that programme.
The three priority questions above remain open; they are the work required to turn this field
from a useful language into a proof mechanism.
