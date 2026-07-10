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
| `SeamArchimedeanNoGo` | Prime-power logarithms are locally finite; the conditional Hermitian spectral realization implies RH. | The prose no-go is stronger than the formal theorem surface: no Lean theorem yet constructs a test function in a sampling gap and proves finite-prime pairing zero but archimedean pairing nonzero. Distributional support separation is standard, but the exact seam functional is a useful missing bridge. | `[OPEN CORE]` / `[BRIDGE]` | Define the sampling restriction kernel and prove the archimedean functional does not factor through it. |
| `ShortWindowNoGo` | Any sharp mean-value pinning certificate has depth at most three. | Harmonic diagonal versus adjacent off-diagonal estimates give the bound. It is a useful exact admissible-depth statement, not new parent mathematics. | `[BRIDGE]` | Use the bound to eliminate the sharp carrier; no alias needed. |
| `ShortWindowNoGoGeneral` | A viable short-window coefficient family must escape the spread cone; equivalently it must possess weighted local concentration. | The contrapositive and a local-dominance index follow by summing adjacent terms, so they are routine. | `[BRIDGE]` | If needed, prove a local-dominant-frequency design lemma as engineering infrastructure. |
| `SpurNoGo` | A concrete hyperbolic two-cluster polynomial is sent by `D^2+1` to a strictly positive quartic with two nonreal conjugate pairs. | This kills the unrestricted one-pair preservation claim. The example alone supplies no new classifier; the exact degenerate discriminant threshold is elementary quadratic algebra. | `[BRIDGE]` | The live question is a sharp geometric hypothesis for one-pair preservation, not a positive restatement of the counterexample. |
| `WeldGermOrientationNoGo` | The weld area form is the surviving invariant; every natural marked vector or linear scalar reader vanishes. | This is the standard absence of invariant vectors/covectors for the two-dimensional symplectic action. Higher invariant tensors are generated by symplectic pairings in the parent theory. | `[SEARCH]` | Any live reader must add at least two marked arithmetic directions or a lattice/filtration; formalize only with a concrete completed source. |
| `WindowSymmetryNoGo` | The height-line stabilizer inside the FE/Schwarz Klein action is exactly `{id, mirror}`. | Finite case split on the four symmetries. | `[SEARCH]` / `[BRIDGE]` | Reuse the exact stabilizer theorem; no further wrapper. |

## Audit pass 1 — declaration and mechanism rings

| Mechanism family | Positive residue | Disposition |
|---|---|---|
| `DirichletRigidity.no_polynomial_surgery` | Ordinary Dirichlet-series membership is rigid under multiplication by a nonconstant polynomial; finite divisor surgery leaves the class. | `[NOVELTY UNVERIFIED]` as an exact statement, but likely a routine consequence of first-coefficient asymptotics; significance gate currently fails. |
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

`[CONJECTURE]` The finite-prime seam functional factors through restriction to the locally finite prime-power log set, whereas the archimedean seam functional has a nonzero restriction to the kernel of that sampling map. Hence the archimedean functional defines a nonzero class in the quotient of continuous distributions by prime-power-supported distributions.

- **Attack:** abstract support separation is standard distribution theory; novelty could only lie in the exact completed seam identification.
- `[OPEN CORE]` Define the actual test-function space and both functionals in Lean/paper form, construct a gap-supported test function, and prove the archimedean evaluation is nonzero rather than merely assert continuous support.
- **Disposition:** `[BRIDGE]` until the exact seam functional adds non-parent content.

### Candidate D — relative invariant degree of the weld class

`[SEARCH]` The absence of natural vectors/covectors says invariant degree one vanishes; the first nonzero scalar invariants require two marked vectors and are generated by the symplectic pairing.

- **Attack:** this is classical invariant theory of `SL_2`/`Sp_2`.
- **Disposition:** useful design rule, not new scientific knowledge.
