# Stuck-route obstruction matrix — the field's target list

- **ID:** ULF-MATRIX-1
- **Stage:** 1-in-progress
- **Type:** PROGRAM DRIVER / OBSTRUCTION INVENTORY + FIELD-STATUS AUDIT
- **Source:** user correction 2026-08-09: the field must engage the corpus's stuck RH routes, not
  free-float; assembled from `rh-producer-map-corpus.md` §§14–23, the lane-elimination and
  five-lanes records, and the criterion classification
- **Status:** [DRIVER] [HONEST GAPS MARKED] [CENTRAL-LAW CANDIDATE FROZEN] [NOT RH] [NO LEAN]

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

## 3. Frozen central-law candidate: the regularization trilemma

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

`[OPEN CORE]` State and prove (a)/(b)/(c) as one theorem at a generality that *contains* the three
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

## 4. Queue (ordered)

1. Attack the trilemma's open core (§3): general statement + proof or fourth-branch witness.
2. Read `RHTower`'s UV-corner modules (`archimedeanPrimeEulerQuadraticCorner*`) lane-deep; only
   then ask whether the gas's trace-class depth-≥2 sector bears on W8 at all — no claim before
   reading.
3. Prove the §2 Schur-complement degeneracy cleanly (small, closes the last nonlinear gap of W3).
4. W9's second-jet test (the elimination map's named next test for the Lee–Yang lane).
5. Keep ULF-GAS-5's moment-horizon question parked behind its collision audit.

## Log

- 2026-08-09 — created after user correction; producer-map card read to the end (§23); walls
  tabulated from proved corpus records; gas layer honestly re-scoped as instances, not
  explanations; trilemma frozen as the field's central-law candidate; rediscovery incident
  recorded.
