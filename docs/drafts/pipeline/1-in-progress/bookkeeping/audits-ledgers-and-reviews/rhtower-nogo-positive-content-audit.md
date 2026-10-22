# RHTower no-go positive-content audit

- **ID:** rhtower-nogo-positive-content-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / RESEARCH AUDIT
- **Source:** `formal/GaloisForLFunctions/RHTower/` · generated `formal/LEAN_API.md`
- **Statement:** Every theorem explicitly presented as an RHTower no-go will be tested for a positive image, quotient, classification, sharp boundary, escape object, or activation theorem; only statements surviving proof, significance, parent-theory, literature, and rediscovery gates may be promoted beyond `[NOVELTY UNVERIFIED]`.

## Goal

Determine whether each negative RHTower theorem is merely a dead construction, or instead identifies a positive mathematical object that can support genuinely new scientific knowledge. The audit must not rename negations as positive theorems. It must extract the smallest invariant, quotient, image, extremal boundary, or complementary existence statement actually forced by the proof.

## Gates

- [x] 0 → 1 in-progress: scope, corpus boundary, attack protocol, and initial candidate moves stated
- [ ] 1 → 2 fully-proven: every candidate promoted by the audit has a complete paper proof; every rejected candidate has an explicit reduction or counterattack
- [ ] 2 → 3 formalized: promoted theorem targets have trusted Lean proofs, focused builds, generated indexes, and lint/axiom checks
- [ ] 3 → 4 publication-ready: surviving significant results pass a serious parent-theory and literature audit and are independently checked

## Corpus boundary

The census has three rings.

1. **Filename ring:** every theorem-bearing module under `formal/GaloisForLFunctions/RHTower/` whose filename contains `NoGo`: `EdgeScaleNoGo`, `EndpointNoGo`, `JointReadingNoGo`, `LandauShadowNoGo`, `PinnedAffineWeldBoundaryNoGo`, `PrimeDivisorAtomsNoGo`, `SeamArchimedeanNoGo`, `ShortWindowNoGo`, `ShortWindowNoGoGeneral`, `SpurNoGo`, `WeldGermOrientationNoGo`, and `WindowSymmetryNoGo`.
2. **Declaration ring:** every RHTower declaration whose generated API docstring explicitly calls it a no-go, even when its module name does not. Initial examples include `no_polynomial_surgery_zeta`, `scalarGluingDetector_factors_through_orbitShape`, `degenerate_disc_neg`, `ram_constant_on_orbit`, `xi_antiholo_axis_eq_half`, and `factoredKrein_ne_congr_weldPlaneGram_of_pos`.
3. **Mechanism ring:** capstone theorems in modules explicitly named `Barrier`, `Blindness`, `Refutation`, `Nonselection`, `Exhaustion`, or `Trivialization`. These are included when their theorem excludes a class of detectors or constructions, not merely when the word occurs in narrative prose.

The adjacent root module `OrbitQuotientLiftNoGo` is recorded separately because it is outside the RHTower namespace/directory, although its orbit-lift mechanism may supply a parent comparison.

## Audit protocol

For each no-go family, record:

1. the exact constrained object and forbidden construction;
2. the proof mechanism stripped of project vocabulary;
3. the strongest positive statement already present in Lean;
4. at least three competing positive moves: image/classification, quotient/obstruction class, sharp boundary/extremizer, escape object, or certificate activation;
5. the fake proof of the best move and its first unsupported sentence;
6. smallest, symmetric, degenerate, and boundary attacks performed by reasoning rather than numerical experiment;
7. parent-theory reduction and likely literature class;
8. disposition: `[SEARCH]`, `[BRIDGE]`, `[NOVELTY UNVERIFIED]`, `[CONJECTURE]`, or `[OPEN CORE]`;
9. the exact next definition, theorem, counterexample, or formal strengthening.

## Initial candidate moves

- `[CONJECTURE]` The pinned-affine boundary no-go is the kernel theorem of a universal quotient, and the positive object is the quotient detected by the Fitting boundary class. Existing `PinnedAffineDefectQuotient` and `CutoffCochain` code may already prove most of this; novelty is not assumed.
- `[CONJECTURE]` Endpoint steerability should be promoted from “orientation is blind” to a fiber classification: at fixed deck class, the attainable endpoint-sign image is the full four-element sign square. The open question is whether this survives beyond the anchored two-endpoint model.
- `[CONJECTURE]` The weld natural-reader no-go is the vanishing of degree-one invariants under a shear group. The positive residue may be the first nontrivial invariant degree or a universal coinvariant, not another zero theorem.
- `[CONJECTURE]` The short-window no-go contains a sharp phase boundary separating impossible spread anchors from potentially live concentrated carriers. The positive object is the admissible coefficient cone below that boundary, provided it has a nontrivial intrinsic classification.
- `[CONJECTURE]` Prime-divisor invisibility is positively a localization theorem: finite Euler/archimedean units lie in the kernel of the local divisor map, while additive/seam certificates live in its nonzero image. The open issue is whether the resulting exact sequence is genuinely new or standard divisor theory in project notation.
- `[CONJECTURE]` Equivariant ramification no-go should become an orbit-quotient classification of functorial ramification data. This is probably `[SEARCH]` unless the RHTower charge functor adds a non-parent obstruction.

## Anti-theatre baseline

- The existing `NoGoPositiveFormulations.lean` package is a useful `[FORMALIZATION]`/`[BRIDGE]`, not new scientific knowledge by itself.
- A theorem of the form `¬ P` rewritten as `P → False`, an alias of an existing theorem, or a restatement that an invariant is zero does not count as positive content.
- A universal quotient, exact image, sharp classifier, or complementary existence theorem can count as mathematical progress, but scientific novelty remains unverified until the parent and literature gates are complete.

## Open core

`[OPEN CORE]` Determine which no-go proof leaves a residue not already exhausted by standard invariant theory, divisor theory, orbit theory, or elementary extremal inequalities, and prove that residue as a precise positive theorem.

## Log

- 2026-07-10 — created in `1-in-progress`; prior positive-wrapper work located and explicitly downgraded to infrastructure; three-ring corpus boundary established.

## Audit pass 1 — explicit `NoGo` modules

| Family | Positive residue already proved | Attack / parent reduction | Disposition | Next mathematical move |
|---|---|---|---|---|
| `EdgeScaleNoGo` | The edge engine has exact phase resolution `pi/rho0`; below one half-turn a pure exponential realizes the rate floor with no event. | The witness is the elementary phase path inside one open half-plane. The positive statement is sharp but routine complex analysis. | `[BRIDGE]` | Reuse the sharp scale; do not create a positive alias. |
| `EndpointNoGo` | `incidence_endpoint_sign_steerable` is surjectivity onto all four sign pairs over prime sets beyond every bound; the deck class remains fixed after anchoring. | The no-go itself is a routine collision corollary. The underlying `anchorTilt_pair_reachable_nonneg` is a substantial prime-log finite-subsum reachability theorem and must be audited separately against rearrangement/universality theory. | `[NOVELTY UNVERIFIED]` for the steering engine; `[BRIDGE]` for the no-go conversion | Formulate the cofinal endpoint-fiber saturation theorem only as infrastructure; investigate finite-dimensional prime-tilt cone reachability as the nontrivial strengthening. |
| `JointReadingNoGo` | The pinned FE/Schwarz symmetry acts on the xi divisor and has exponent two. | Two commuting involutions generate an elementary `C2 x C2` action. Exact group/orbit classification is standard and does not supply unbounded weights. | `[SEARCH]` / `[BRIDGE]` | Record orbit-size stratification only if a consumer needs it. |
| `LandauShadowNoGo` | Involution-equivariant parity localizes exactly to the fixed locus; conjugation selects the real axis and FE reflection selects the critical line. | This is finite involution orbit pairing. The generic positive wrapper already exists. | `[SEARCH]` | No new theorem unless a non-mod-two fixed-locus invariant is found. |
| `PinnedAffineWeldBoundaryNoGo` | `PinnedAffineDefectQuotient` is already the universal additive quotient by pinned affine defects; the Fitting boundary descends and detects a nonzero class. | Universal quotient construction is standard, but it is the correct positive object. Raw constant/prime evaluation activates it everywhere, so nonvanishing alone is not an RH selector. | `[BRIDGE]` | Seek a completed arithmetic compatibility law on the quotient, not another quotient-nonzero theorem. |
| `PrimeDivisorAtomsNoGo` | The pinned prime-source interface is completely classified: `SigmaSourceMap A rho` iff every prime component is zero; additive EM atoms and multiplicative finite-factor atoms are disjoint at a strip zero. | Finite Euler and archimedean factors are analytic units, so this reduces to standard local divisor theory. | `[BRIDGE]` | The only live positive object is non-factorwise extension/completion data; do not repackage factorwise zeros. |
| `SeamArchimedeanNoGo` | Every positive weighted gap functional escapes masked sampling outside its gap; the completed-zeta theta specialization survives sampling at every positive integer logarithm on every consecutive logarithmic gap. | `SeamArchimedeanSamplingQuotient` now proves arbitrary-mask/arbitrary-site/arbitrary-gap support separation and recovers prime-power sampling on `(log 2, log 3)` as a compatibility instance.  This remains classical support separation made exact for the RHTower source. | `[PROVED]` / `[BRIDGE]` | Reuse the general defect class; any novelty must come from a further theorem consuming it, not from restating support separation. |
| `ShortWindowNoGo` | Any sharp mean-value pinning certificate has depth at most three. | Harmonic diagonal versus adjacent off-diagonal estimates give the bound. It is a useful exact admissible-depth statement, not new parent mathematics. | `[BRIDGE]` | Use the bound to eliminate the sharp carrier; no alias needed. |
| `ShortWindowNoGoGeneral` | A viable short-window coefficient family must escape the spread cone; equivalently it must possess weighted local concentration. | The contrapositive and a local-dominance index follow by summing adjacent terms, so they are routine. | `[BRIDGE]` | If needed, prove a local-dominant-frequency design lemma as engineering infrastructure. |
| `SpurNoGo` | A concrete hyperbolic two-cluster polynomial is sent by `D^2+1` to a strictly positive quartic with two nonreal conjugate pairs. | This kills the unrestricted one-pair preservation claim. The example alone supplies no new classifier; the exact degenerate discriminant threshold is elementary quadratic algebra. | `[BRIDGE]` | The live question is a sharp geometric hypothesis for one-pair preservation, not a positive restatement of the counterexample. |
| `WeldGermOrientationNoGo` | The weld area form is the surviving invariant; every natural marked vector or linear scalar reader vanishes. | This is the standard absence of invariant vectors/covectors for the two-dimensional symplectic action. Higher invariant tensors are generated by symplectic pairings in the parent theory. | `[SEARCH]` | Any live reader must add at least two marked arithmetic directions or a lattice/filtration; formalize only with a concrete completed source. |
| `WindowSymmetryNoGo` | The height-line stabilizer inside the FE/Schwarz Klein action is exactly `{id, mirror}`. | Finite case split on the four symmetries. | `[SEARCH]` / `[BRIDGE]` | Reuse the exact stabilizer theorem; no further wrapper. |

## Audit pass 1 — declaration and mechanism rings

| Mechanism family | Positive residue | Disposition |
|---|---|---|
| `RHTower.no_polynomial_surgery` | Multiplication by a specified nonconstant polynomial leaves the ordinary Dirichlet-series class. This does not exclude finite divisor changes with an additional nonvanishing factor or imply class-level zero rigidity. | Routine first-coefficient asymptotics; no new mechanism. See the [scope correction](../../dirichlet-polynomial-surgery-scope-audit.md) and the existing prescribed-divisor Helson theorem. |
| `FESchwarzGermGluingTrivialization` | Scalar gluing data are classified up to gauge solely by fixed versus free orbit shape. | `[SEARCH]` / `[BRIDGE]` via rank-one Hilbert 90 and a flat scalar square. |
| `QuadrantRamifiedCover` | Equivariant ramification data descend to the orbit quotient and are constant on each orbit. | `[SEARCH]`; standard orbit descent. |
| `SeamVerticalDecay.xi_antiholo_axis_eq_half` | The critical line is the unique vertical anti-holomorphic symmetry axis of xi. | `[BRIDGE]`; follows from the known axis plus nonperiodicity, so it is not a new mechanism. |
| `WeldPolarizationDirection` | Positive local weld metrics cannot produce the off-line Krein signature by congruence. | `[SEARCH]`; Sylvester inertia/signature invariance. |
| `DeciderBarrier` | Any decider factoring through an invariant is constant on its fibers. | `[SEARCH]`; tautological factorization principle, useful only as audit language. |
| `ConnectedSymmetryBarrier` | Deck charge is constant on preconnected parameter families and therefore factors through connected components of the member-window pair space. | `[BRIDGE]`; standard homotopy/open-closed conservation, but the pair-space formulation is useful. |
| `FittingDeckChargeBarrier` + `IntegralJetCharge` | The coefficient-sensitive charge channel is controlled by the constant-line quotient `R/nR`: it vanishes over divisible `Q` and survives over the integral lattice. | `[BRIDGE]`; standard `Hom(R,Z/n)` factorization through `R/nR`, but a high-value arithmetic design rule. |
| `PinnedAffineConstantSourceBlindness` | Finite constant sources enter the one-slot quotient only through their scalar sum; pointwise prime sources are active everywhere and pointwise-tuned cancellation is vacuous. | `[BRIDGE]`; exact source-label loss, but elementary linear collapse. |
| `FESemilinearShearExhaustion` | FE-compatible upper shears are exactly odd polynomials and every such shear is FE-semilinearly split. | `[BRIDGE]`; explicit elementary gauge classification. |
| `FiniteDivisorPrefixNonselection` | Every finite critical-line divisor prefix has both fixed-orbit and free-orbit FE/Schwarz extensions with the same finite Euler head. | `[BRIDGE]`; multiplication by fresh orbit polynomials is an explicit but routine construction. |
| `TailBlindness` + `CombinedShadowBlindness` | Orbit-quartic multiplication preserves the finite Euler head and logarithmic-derivative tail while planting off-line charge. | `[BRIDGE]`; the positive content is closure of a deliberately soft class, so it identifies missing whole-object data but is not new science. |
| `WeldKreinRateBlindness` | All positive prime-rate blocks are congruent; the entire factorwise divisor-order profile is zero, so only non-factorwise extension data can activate a completed divisor. | `[SEARCH]` for congruence, `[BRIDGE]` for the factorwise/completed separation. |
| `ShearedSeamGaugeTrivialization` | Absolute row gauge splitting and symmetry-relative splitting are distinct; cutoff alignment and fixed parity are extra structure. | `[BRIDGE]`; the later FE-semilinear exhaustion kills the upper-shear extension as a source of new classes. |

## Candidate competition after pass 1

### Candidate A — finite-dimensional prime-tilt cone reachability

`[CONJECTURE]` Let `s_j = sigma + i t_j`, `0 < sigma < 1`, with an explicit nonresonance condition on the ordinates. For every target `T in R_{>=0}^r`, tolerance `epsilon > 0`, and prime cutoff `Q`, there is a finite set of primes `P`, all above `Q`, such that the vector of Euler-anchor tilts at the `s_j` lies within `epsilon` of `T`.

- **Why it is generated by a no-go:** `EndpointNoGo` reveals that the endpoint-sign fiber is saturated because the two-point tilt vector is controllable. The positive object is the reachable cone, not the blindness statement.
- **Small/boundary attacks:** `r=1` is classical scalar subseries reachability; `r=2` is proved under the current narrow-frequency hypotheses; repeated or rationally locked ordinates can collapse the cone and must be excluded; `sigma >= 1` loses divergent prime mass and should fail for large targets.
- **Fake proof:** use Kronecker recurrence to produce arbitrarily late logarithmic prime windows in every sign orthant, the prime number theorem to give each window enough primes, decay `p^{-sigma}` for small steps, and a vector staircase/Steinitz argument to approximate the target.
- `[OPEN CORE]` Prove the directional divergence condition for the *actual nonlinear prime-tilt vectors* uniformly in every supporting direction, with a nonresonance hypothesis that is both necessary and stable under FE reflection.
- **Parent attack:** Pecherskii rearrangement and zeta-universality methods already give broad density theorems for prime-generated vectors. Until exact comparison is complete, this cannot be promoted above `[NOVELTY UNVERIFIED]`.

### Candidate B — coefficient torsion gate

`[PROVED]` in the current special cases and `[CONJECTURE]` in universal form: the additive finite charge carried by the constant Fitting-jet line over a coefficient ring `R` is classified by `R/nR`; rational coefficients erase the channel, integral coefficients retain it.

- **Attack:** this is standard abelian-group algebra after project vocabulary is removed.
- **Disposition:** `[BRIDGE]`, not new scientific knowledge.
- **Use:** it is a precise building block: any seam-to-deck construction must specify a non-`n`-divisible arithmetic lattice before asking for a finite charge.

### Candidate C — archimedean sampling quotient

`[PROVED]` Every positive weighted gap functional escapes arbitrary nonlinear reconstruction from masked samples outside the gap.  The completed-zeta theta density specializes this to every consecutive positive-integer-log gap, so even the strictly finer channel sampling at all positive integer logarithms cannot reconstruct the local theta functional; prime-power sampling on `(log 2, log 3)` is the compatibility instance.

- **Proof:** `SeamArchimedeanSamplingQuotient.lean` defines `maskedSamples`, `gapTent`, and `weightedGapFunctional`.  The capstone `weightedGapFunctional_not_factors_through_maskedSamples` compares the canonical gap tent with zero.  `archimedeanThetaSeamFunctionalOn_not_factors_through_maskedSamples` inserts the actual positive theta density, and `archimedeanThetaSeamFunctionalOn_not_factors_through_positiveIntegerLogSamples` proves the consecutive-logarithm family by excluding an integer strictly between two consecutive integers.
- **Certificate:** `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/archimedean-theta-seam-sampling-quotient.md`.
- **Disposition:** `[BRIDGE]`, not new scientific knowledge.  It is now an exact nonzero sampling-quotient class available as a building block; novelty must come from a further theorem that uses this class beyond classical support separation.

### Candidate D — relative invariant degree of the weld class

`[SEARCH]` The absence of natural vectors/covectors says invariant degree one vanishes; the first nonzero scalar invariants require two marked vectors and are generated by the symplectic pairing.

- **Attack:** this is classical invariant theory of `SL_2`/`Sp_2`.
- **Disposition:** useful design rule, not new scientific knowledge.

## Audit pass 2 — narrative no-gos and positive escape modules

The filename/declaration census was extended to modules whose headers explicitly state a no-go or whose sole role is the positive escape from one.

| Family | Positive statement | Attack and disposition |
|---|---|---|
| `ZeroResonanceIndependence` | For every nonzero scalar `alpha`, the prime-log resonance exponents are `Q`-linearly independent; under Schanuel, the exponent/value family has transcendence degree at least the number of chosen primes. | Scaling preserves linear independence, so the line-blindness is exact but standard. The Schanuel consequence is conditional parent theory. `[SEARCH]` / `[BRIDGE]`; no line detector can be extracted from transcendence type alone. |
| `RelativeTorsor` | Dressing local xi roots by the global finite Euler root leaves the deck class exactly unchanged; the relative torsor is deck-isomorphic to xi's torsor. | Multiplication by a common nonvanishing factor cancels in the transition ratio. `[BRIDGE]`; the positive object is the original torsor, not a new relative class. |
| `WeldTowerFree` | Every finite completed Euler-Gamma factor has a coherent infinite Kummer tower on `Re s > 0`, whereas xi's tower costs the ladder divisibility condition. | Zero-free analytic units on a simply connected domain have roots. `[BRIDGE]`; the useful conclusion is that the obstruction is non-factorwise/emergent. |
| `ApexIndependence` | The named ladder weld class has connecting value `idx` and, for `idx != 0`, lies outside the prime-flux image in real `H^2`. | The file itself correctly notes that this composes banked facts. The separation reduces to independence of `{1} union {log p}`. `[BRIDGE]`; a specific class-level building block, not new scientific knowledge by itself. |
| `ArchimedeanBalancedPerron` scalar no-go | Exact scalar decompletion is unique and cancels rather than transports the Gamma factor; nevertheless the balanced third-order probe extracts each Dirichlet coefficient exactly. | Scalar uniqueness is division by a nonzero factor. The positive coefficient-extraction formula is substantial infrastructure but the no-go conversion adds no new mechanism. `[BRIDGE]`. |
| `WholeLoopClosure` + `ArcWindingDictionary` | The correct replacement for endpoint signs already exists: full boundary-arc argument variation recovers the deck parity/zero count, and the finite Euler anchor contributes no monodromy. | This is the argument principle and logarithm transport. `[BRIDGE]`; it closes the endpoint no-go positively, but the scientific content of the new candidate must come from prime-tilt reachability, not the dictionary. |
| `CutoffCochain` | A nonzero cross-boundary cochain exists outside the pinned commutator/affine family. | This is the correct positive escape object already banked. Its identification with a completed semilocal Sonin action remains separate. `[NOVELTY UNVERIFIED]` only for that future identification, not for the abstract escape. |
| `GoldilocksTrichotomy` | Candidate carrier classes split into soft, Goldilocks, or categorical cells; finite surgery rigidity witnesses one boundary. | The trichotomy is definitional after the predicates are chosen. `[PROJECT ARTIFACT]` / `[BRIDGE]`, not scientific novelty. |
