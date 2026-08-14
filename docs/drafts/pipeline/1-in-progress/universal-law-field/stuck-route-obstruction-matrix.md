# Stuck-route obstruction matrix — the field's target list

- **ID:** ULF-MATRIX-1
- **Stage:** 1-in-progress
- **Type:** PROGRAM DRIVER / OBSTRUCTION INVENTORY + FIELD-STATUS AUDIT
- **Source:** user correction 2026-08-09: the field must engage the corpus's stuck RH routes, not
  free-float; assembled from `rh-producer-map-corpus.md` §§14–23, the lane-elimination and
  five-lanes records, and the criterion classification
- **Status:** [DRIVER] [HONEST GAPS MARKED] [FORMER CENTRAL LAW FALSIFIED 2026-08-13]
  [POSITIVE SURVIVOR PROMOTED] [NOT RH]

## 1. The walls, as the corpus has actually proved them

| # | wall | sharpest corpus form | status |
|---|---|---|---|
| W1 | positivity must be created | raw prime-side Grams are cofinally PSD **for free**; the regularization that makes them finite is what kills it | proved in three lanes |
| W2 | multiplicative blindness | any convergent multiplicative regularization sees only leading asymptotics (`tendsto_mul_regularized`); positivity inherited iff the normalizer is a moment sequence (`HankelNormalizationPositivity`) | proved |
| W3 | weld trilemma | finite ⊕ positive ⊕ Hankel impossible for every linear block combination; weld shape not PSD (one quadratic); no-defect escape is Hamburger-circular | proved (§§20–22) |
| W4 | criterion trichotomy | every criterion is strictly-weaker / RH-per-zero / exactly-RH; group 3 is the problem | proved classification |
| W5 | count direction | RH needs an unconditional **upper** bound on a count; every engine bounds below except zero-density, capped at `(2−2σ)(2σ−1)`; escape needs structure outside `min(power, meanValue)` | derived, closed |
| W6 | Perron/Halász caps | coefficient-blind, or uniform distance = prime mass; complementary, both unconditional | proved |
| W7 | MR / short-interval wall | corridor needs κ<1; bilinear correlations are the wall for Route E | mapped, external |
| W8 | UV noncompactness | `archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator`; no trace-class comparison crosses; **the one live object** | proved no-go, model missing |
| W9 | Lee–Yang mass floor | only survivor is the factored form `E·XiC`, and `E` alone pays `log 2/2` | proved |
| W10 | Deninger gauge ceiling | the debt is a gauge invariant; structural producers' premises are `(1−2Reρ)·(positive)` — group 3 | proved |
| W11 | Burnol first wall | Cartier residue cancellation (see the stage-2 Burnol card) | paper-proved layer |

## 2. What the abelian-zeta-gas layer genuinely instantiates (and what it does not)

Honest mapping of ULF-GAS-1/3/4 (after errata) onto §1. **Instantiates ≠ explains**; the gas gives
the same laws on a simpler source, which is evidence for a common mechanism, not leverage on any
wall.

| gas result | wall shape it instantiates |
|---|---|
| probabilistic death at σ=1 + non-unimodular counterterm necessity + exact modulus budget (GAS-3) | W1: continuation across a divergence exits the positive cone; the exit price is exact |
| multiplicative resolution cap (GAS-4 Thm 3.1) | W2/W6: solvable multiplicative certificates are scale-coarse / coefficient-blind |
| genus-one erasure = depth-≥2 unit; separated scaling → arithmetic-free limit | W2: the corpus's Hilbert-matrix limit (`§16`) is the same "positivity kept, arithmetic lost" branch |
| KMS-unique / condensation-wall dichotomy (GAS-1 Cor 4.2) | none directly; a wall-type taxonomy |
| moment horizon `r<σ` (GAS-5 calibration) | W4-adjacent: heavy tails put the source outside moment-determined classes |

Not touched by the gas layer: W3 (weld), W5 (count direction), W7 (MR), W8 (UV), W9, W10, W11.

**Rediscovery log (kept as method discipline):** this session's candidate "regularization license
law" (Hadamard multiplier PSD iff moment sequence) was found already proved in
`rh-producer-map-corpus.md` §15 + `HTGeometry/HankelNormalizationPositivity.lean`, with a sharper
sequel (§17: multiplicative blindness) and a full closure (§§18–22). Verdict REDISCOVERED before
writing; the corpus must be read lane-deep, not memory-deep, before any conjecture.

**One small checked addition (heuristic, not a theorem):** the natural nonlinear escape from §21 —
the Schur complement `A − C B⁻¹ Cᵀ` of the divergent block in the full two-feature Gram — is
finite and PSD by construction (so it evades the linear trilemma), but it degenerates: the mixed
entries `∑ Λ(n)/n·Δ(logⁱn)·logʲn` converge while every direction of `B` diverges, so `B⁻¹→0` and
the complement collapses to the uncancelled successor Gram (`β=0` branch). The nonlinear escape
buys nothing. To be proved cleanly before it is cited as closed.

## 3. Retired central-law candidate: the regularization trilemma

The corpus has proved, lane by lane, instances of one unstated general law. Freeze it as the
field's central conjecture:

> **Regularization trilemma (frozen).** Let a directed positive source have divergent cost along a
> condensation wall (in the PRD sense), with its free positivity carried by cofinal Gram/moment
> structure. Then any observer rendering the source finite satisfies at least one of:
> (a) it factors through leading-order data and is blind to the subleading stratum where the
> divisor lives — the multiplicative/blind branch;
> (b) it exits the positive cone, with exit price bounded below by an exact budget (the divergent
> positive mass it removes) — the subtractive/budget branch;
> (c) it is equivalent to exhibiting the limiting positive measure itself — the circular branch.
>
> Corpus instances: (a) = `tendsto_mul_regularized`, the Hilbert-matrix limit, GAS-4's cap;
> (b) = the weld trilemma §21, GAS-3's modulus budget; (c) = §22's Hamburger circularity, the
> group-3 classification.

`[FALSIFIED 2026-08-13]` The requested fourth branch exists.  For the divergent positive pencil
`G_t=diag(t,1)`, compression to the second coordinate is exactly `1`: finite, positive, and fully
sensitive to the subleading coordinate, with no leading normalization, signed subtraction, or
limiting-measure certificate.  More generally, a fixed Gram compression of
`t B^*B + D^*D` is pointwise bounded exactly when its carrier lies in `ker B`, and then the full
subleading compressed Gram survives unchanged.  See the failed card
`regularization-face-mechanics/regularization-trilemma-falsified-by-positive-face-compression.md`
and its Stage-2 positive survivor.

The original open request was to state and prove (a)/(b)/(c) at a generality that *contains* the three
corpus instances as corollaries — i.e., a single hypothesis set (divergent positive cofinal Gram +
finiteness of the observer) with the trichotomy as conclusion, not three analogies. First
unprovable point: a definition of "observer rendering finite" wide enough to cover multiplicative,
subtractive, and nonlinear (Schur-complement, operator-mean) compressions at once, yet strong
enough to force the trichotomy. If no such theorem exists, the falsification will exhibit a fourth
branch — which would be exactly a new route shape, and more valuable than the law.

**Why this is not renaming:** the trilemma, if proved at that generality, yields a decision
procedure for every future regularization proposal in every lane (check which branch it sits in),
and its failure yields a constructive fourth shape. Either outcome moves route search. It still
creates no positivity; W8 (the UV model) remains the only constructive target.

## 4. Alternating-formation collision and exact survivor

Static receivers and static obstruction classes were the wrong level. A candidate mechanism was
**failure-driven alternating formation**:

\[
 \text{marginal failure}
 \longrightarrow \text{unique multiplicative repair}
 \longrightarrow \text{transverse failure}
 \longrightarrow \text{next repair}.
\]

It comes with one exact global law. If `Phi_n` is formation mismatch and `A_n>=0` is generated
repair action, then

\[
 \Phi_0=\Phi_N+\sum_{n<N}A_n.
\]

Lean now proves both finite-history KL conservation and its route-independent properness
consequence: cofinal approximate recurrence of `Phi_n` forces every `A_n=0`. Functional reflection
exchanges the two repair types, while positive bipartite formation has exactly one invisible gauge
direction and is proper after quotienting it.

Hostile audit killed the claim that this is the first surviving field mechanism. The earlier
abelian-relaxation theorem already generates state-dependent legality, least repair, canonical
completion, recurrent observation, open lineage, and proper Green work from one source Laplacian.
Alternating marginal repair is narrower: `(r,c)` and the update schedule are supplied before the
recursion. It is therefore a Sinkhorn/Bregman **bridge**, not the field core.

The exact positive survivor remains useful: the Lean theorem proves finite-history action
conservation and the route-independent statement that cofinal approximate recurrence of a real
potential with nonnegative exact step action forces every action to vanish. The next field gate is
strictly higher: construct a cofinal source history whose own completion/admission failure generates
both the next legal operation and its work topology.

Paper and Lean:
`entropic-alternating-formation-mechanics/alternating-marginal-repair-action-gauge-properness-and-recurrent-selection-law.md`
and `HTGeometry.ConstitutiveEntropicAlternatingFormation`.

## 5. Queue (ordered)

1. **New mechanism gate:** Source-Response Signature Mechanics is now instantiated on the literal
   logarithmic prime-shift source.  Grade-one commutator response has a uniform all-prime lower
   bound.  Hostile word fusion then proves a new wall: grade-two antisymmetric response is injective
   compact/dense-nonclosed on source-certified crowded prime pairs, and every finite diagonal
   logarithmic/time-differential prolongation still fails.  Its forced singular survivor now repairs
   grades two through four: relative/Vandermonde exact-range division, subset-grade compensation,
   and causal Green inversion produce positive three-, seven-, and fifteen-stage formation laws
   with uniform all-prime pair/triple/quadruple frames.  The universal deletion--interpolation
   recursion now replaces factorial schedule enumeration.  An all-grade flag-determinant theorem
   further proves complete monotonicity, exact subset-phase conservation, and a frame at every
   fixed grade.  Hostile cofinal assembly then proves dense nonclosed range and rules out every
   scalar grade-only Hilbert topology.  Its positive survivor is now executed: all-grade
   probability formation is an exact isometry from `ell^1` coefficients to vector measures in
   total variation, with total mass as one contractive recovery; finite-horizon CDF observation is
   the nonproper quotient.  A common-recovery/Ward fusion has now been tested and falsified as a
   selector: normalized shape jets are vertical, all-Markov invariant reporters factor through
   mass, and affine Ward balance is Bartlett cancellation.  Its positive survivor is an all-order
   coefficient/shape splitting and exact Fisher/connection anomaly-migration law.  A higher
   twisted-coinvariant pivot has now constructed the source-restricted vertical reporter: integer
   Laplace characters reconstruct every zero-mass signed half-line current, and their finite
   inverse covariance-Gram energies exhaust Fisher information.  The same response predicts an
   exact origin-atom boundary for convolutional properness.  Remaining load-bearing work is literal
   physical current horizontal/vertical landing.  Direct character deconvolution nonproperness is
   no longer terminal: `I-M_nu` is globally proper for every nontrivial positive delay law and
   `I+M_nu` is always proper, so fixed/anti-fixed zero-mass currents vanish.  The pre-zero source
   comparison `functional-equation reflection = positive formation` has now been killed as a
   one-sided operator law: every positive involution is the identity, whereas nontrivial Laplace
   formation is strictly contractive.  Positive survivor ULF-CDM-2 proves the complete formation
   instead forces its marked Julia defect, unique homogeneous history, geometric recovery kernel,
   passive joint decoder, and convolution defect ledger; the kernel family reconstructs the
   source law.  The pre-zero gate is now physical **visible-only passive recovery** of the same
   current, or a source theorem annihilating the forced hidden history,
   the grade-five causal numerator,
   transport to the physical transverse module, and a complete-response null identity.
2. ~~Attack the trilemma's open core.~~ Closed by a fourth-branch witness. Formalize the positive
   face-compression classification, then ask only for **source-generated face motion** not already
   covered by formation-Laplacian mechanics.
3. ~~Read `RHTower`'s UV-corner modules lane-deep.~~ Closed negatively: finite prime quadratic
   corners are matrix-injective modulo compacts, so the compact face is zero. Test only genuinely
   infinite, nonlinear, smoothed, or repolarized successors.
4. Audit whether cofinal completion/admission itself can generate the next legal operation and its
   work, rather than receiving a supplied target or certificate sequence.
5. Require one source-generated history that simultaneously carries derived topology, work, and
   noncommuting charge transport before divisor specialization.
6. Keep route-local Schur, W9 second-jet, and moment-horizon tests parked until this higher formation
   gate either succeeds or is mathematically falsified.

## Log

- 2026-08-09 — created after user correction; producer-map card read to the end (§23); walls
  tabulated from proved corpus records; gas layer honestly re-scoped as instances, not
  explanations; trilemma frozen as the field's central-law candidate; rediscovery incident
  recorded.
- 2026-08-13 — frozen trilemma falsified by positive compression to a leading null face; strongest
  survivor promoted as a complete fixed-Gram classification; field search pivoted from static
  regularization types to source-generated carrier/face formation.
- 2026-08-13 — UV audit completed: finite distinct-prime quadratic corners are matrix-injective in
  the Calkin quotient, so no nonzero finite compact face exists. W8 now forces an infinite,
  nonlinear, smoothed, or repolarized mechanism rather than another finite carrier choice.
- 2026-08-13 — first mechanism-level successor proved and formalized: alternating marginal failure
  generates unique transverse repairs; exact action telescopes; cofinal approximate recurrence
  forces stationarity; reflection exchanges repairs; positivity is proper modulo one forced gauge.
- 2026-08-14 — Duhamel/Volterra pivot closed the supplied-response-map gap at paper level.  One
  cyclic source evolution now generates the ordered response tower, positive Gram response,
  inverse-cost response, and global closed-range test; functional equation is exactly neutral.
  Arithmetic source realization and the complete-response null law remain open.
- 2026-08-14 — arithmetic source realization closed at grade one, then failed sharply under
  grade-two formation.  Shrinking prime-log windows force compact orientation response after every
  finite diagonal logarithmic/time-differential prolongation.  Positive survivor: formation-grade properness spectrum plus an
  exact stretched-exponential lower growth law for any diagonal repair.
- 2026-08-14 — singular positive survivor executed rather than merely named.  Grade-two relative
  Green exactification gives a three-phase CDF and pair frame.  Grade-three hostile attack falsifies
  the repeated pair recipe, then proves the permutohedral successor: Vandermonde boundary,
  subset-sum denominator, causal numerator `2z+A`, seven-phase CDF, and triple frame.
- 2026-08-14 — grade-four stability gate closed.  First-letter deletion gives an exact recursive
  law for every formation numerator; `P_4` factors into a stable linear term and a quartic with a
  manifestly positive Hurwitz minor.  Its exact-range Green inverse yields the fifteen-phase CDF
  and quadruple frame.  Queue now begins at grade five rather than another route-specific object.
- 2026-08-14 — higher pivot closed all finite-grade existence at once: flag-determinant total
  positivity yields all-grade conservation and fixed-grade frames.  The cofinal tower is injective
  with dense nonclosed range, and no scalar arity weight can make it bounded and proper because
  low-prime and high-prime channels impose incompatible scaling.  Queue now starts with a
  source-generated tuple-adaptive topology, not another finite-grade normalization.
- 2026-08-14 — topology survivor closed without fitted tuple weights.  The complete subset-phase
  probability family is an `ell^1`-to-vector-measure total-variation isometry with common mass
  recovery.  Hilbert CDF observation alone causes the cofinal fracture.  Queue now begins with
  constructing the literal pre-zero signed current in this recovered range.
- 2026-08-14 — all-Markov reporter no-go was not accepted as terminal.  Restricting to the
  source-generated additive semigroup yields a complete twisted-character cotangent atlas;
  integer Laplace responses reconstruct vertical signed currents and inverse Grams conserve Fisher
  mass exactly.  Atomless convolution remains compact/dense-nonclosed, while positive origin mass
  is exactly the properness face.  Queue now asks for the physical landing and a source null
  identity, not another scalar reporter.
- 2026-08-14 — the atomless completion wall was attacked through the formation polynomial.
  `I-M_nu` is uniformly invertible off the identity law with positive Neumann Green inverse, while
  `I+M_nu` is always uniformly invertible.  A reflection parity becomes selective as soon as the
  source proves reflected current equals formed current.  This is now the exact comparison gate;
  functional-equation covariance or common-kernel lifting alone remains insufficient.
- 2026-08-14 — attacked the remaining reflection--formation comparison and proved it cannot hold
  as an identification of one-sided positive formation with an involution.  ULF-CDM-2 salvages a
  stronger generated law: Laplace formation uniquely forces the conservative defect/history
  double and common geometric recovery, which reconstructs the source measure.  Remaining gate is
  passive recovery from the visible physical formation without that history, or source
  annihilation of the history itself.
