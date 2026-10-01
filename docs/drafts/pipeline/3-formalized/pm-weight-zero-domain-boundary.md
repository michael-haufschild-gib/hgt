# Exact zero-weight boundary of the Fermi witness domain

- **ID:** pm-weight-zero-domain-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route PM; weighted multiplicity tomography; exponent-zero Mellin rigidity
- **Statement:** A weighted source witness at `a≤0` vanishes on `(0,1]`; for each `a>0`, a nonzero spurious source witness is admitted.
- **Novelty:** Internal source-domain statement; global novelty not claimed.

## Goal

Audit the endpoint required by a deformation argument from the zero-index domain to
`a=1/2`. Triviality at `a=0` cannot by itself control positive weights: admitted spurious
modes already have energy `1/(2a)`. Exact weighted multiplicity tomography describes
subsequent zero-admission thresholds but does not eliminate them. RH remains open.

## Gates

- [x] 0 → 1: literal source class and exact endpoint specified
- [x] 1 → 2: dependency-closed proof, including the endpoint integral argument
- [x] 2 → 3: actual-leaf build, direct audit, all eight declarations axiom-audited
- [ ] 3 → 4: standalone exposition and novelty review

## Proof to audit

1. At `a=0`, the admitted-zero set `1<Re rho<1` is empty. Weighted correlation
   cancellation therefore forces `w(t/2)=w(t)` without a zero-location premise.
2. Set `f(t)=|w(t)|²/t`. Its weighted integrability and self-similarity give
   `integral_0^(1/2) f = integral_0^1 f`. Thus its integral on `(1/2,1]` is zero.
   Nonnegativity and continuity there force `w=0` on that fundamental interval.
3. Repeated dyadic dilation carries each `t∈(0,1]` to `(1/2,1]`, proving `w(t)=0`.
4. For `a<0`, the weight dominates the zero weight on `(0,1]`; integrability by
   domination puts the same source witness in the zero-weight class.
5. For `a>0`, the already admitted spurious witness at mode `k=1` has pointwise norm
   one on `(0,1]`, so is nonzero. Its energy is `1/(2a)`, diverging at the endpoint.

All interval and scaling claims still require the matching Lean APIs. Do not infer
constancy of the index from this endpoint classification, or infer a uniform source
energy bound from pointwise membership at every positive weight.

## Prior research

`research "self similar weighted integrable vanishing endpoint" --any --module FermiNyman`
returned relevant weighted cancellation and exponent-zero Mellin growth receivers, but
no endpoint-vanishing statement among the returned hits. Search was partial (interrupted
text/source stages), with complete source inventory and mostly pending/stale compiler
metadata. All returned candidate/source statements were reviewed.

## Log

- 2026-09-30 — candidate recorded while final weighted tomography audits run. No new endpoint Lean code yet. Next source obligation is uniform control across a changing domain, not another assumption of index vanishing.

- Endpoint proof API reconnaissance: existing `dyadicSelfSimilar_mul_pow_half` and `exists_nat_pow_near_of_lt_one` transfer a zero fundamental interval to `(0,1]`. Mathlib source contains `Measure.eqOn_Ioc_of_ae_eq`, `integral_eq_zero_iff_of_nonneg`, and `Real.rpow_le_rpow_of_exponent_ge`; signatures still need scratch probes before use. The source-weight inequality is monotone in the required direction because `0<t≤1`. No endpoint formalization claim.
- 2026-09-30 continuation — revalidated current worktree, objective, and weighted profile. Previous turn classified as progress. Endpoint scratch now proves weight-domain monotonicity, unconditional self-similarity at zero, and vanishing via the fundamental-interval energy; compiler audit running. Probed the interval scaling, AE-to-continuous equality, nonnegative-integral and dyadic reduction APIs. The interval scaling lemma is generic over real normed spaces, so no complex coercion detour is needed. `integral_Ioc_add_Ioc` is unavailable; use `setIntegral_union` on adjacent intervals.
- The endpoint draft now includes the exact nontriviality equivalence for every real weight, the literal spurious energy `1/(2a)`, and unbounded energy in every interval `(0,ε)` using the fixed mode `k=1`. This explicitly rules out a uniform endpoint energy bound on all positive-weight source witnesses; it does not rule out a stronger, source-selected regularization. A separate deep corpus search is running for Möbius cancellation yielding dyadic Haar approximation, excluding Fermi modules to avoid returning only the receiver itself.

## Paper proof closure

[PROVED HERE] Weight inclusion follows from `t^(2b-1)≤t^(2a-1)` on `(0,1]` when
`a≤b`, with integrability transferred by domination. At zero, the weighted correlation
receiver has no admitted zeros and therefore gives self-similarity. For the nonnegative
integrable real function `f(t)=t^(-1)|w(t)|²`, substitution gives
`2 integral_0^1 f = 2 integral_0^(1/2) f`. Splitting adjacent intervals then yields zero
integral on `(1/2,1]`. AE vanishing plus continuity on that interval gives pointwise
vanishing, and dyadic rescaling carries it to every `t∈(0,1]`. This closes the only
endpoint measure-theory obligation. Weight inclusion handles every `a<0`.

For positive `a`, the already proved spurious admission theorem supplies mode `k=1`,
whose value at `t=1` is one. The existing exact weighted power integral gives energy
`1/(2a)`. Given any `ε>0` and real `M`, choose
`a=min(ε/2, 1/(4(|M|+1)))`. Then `0<a<ε` and `M<1/(2a)`. Thus even a single fixed,
actual source witness prevents a uniform endpoint energy bound on the whole class.

- Full endpoint scratch passed `lake env lean` exit 0 with empty diagnostics. New actual
  leaf `FermiNymanWeightDomainBoundary.lean` awaits targeted build and final direct/axiom
  audit. It contains the exact nontriviality equivalence and a hypothesis-free combined
  domain/energy capstone, `weightedFermiWitness_domain_boundary`.
- First independent approximation search completed with `partial: false`, no errors,
  complete source inventory, mostly pending/stale compiler coverage. All returned
  candidates/source statements reviewed. MenonHarmonicWindowBridge transfers ordinary
  windows to harmonic ones with an explicit endpoint error; it supplies no cancellation
  bound for the harmonic term. MobiusHaarRamareCoprimalityBudget gives only the cofactor
  cutoff bound `R`. Proposed Deninger Haar-`L²` and Boolean Möbius-response ingredients
  concern different objects and do not produce the dyadic Haar approximation. A second
  deep search now targets the literal critical-line `1+ζ D_N` mean-square approximation.

## Formal certificate

`RHTower.weightedFermiWitness_domain_boundary` in
`formal/GaloisForLFunctions/RHTower/FermiNymanWeightDomainBoundary.lean` proves the exact
nontriviality equivalence and unbounded fixed-mode energy in every positive parameter
neighborhood of zero. It has no external premise.

- Targeted `lake --old build +GaloisForLFunctions.RHTower.FermiNymanWeightDomainBoundary:olean`
  passed; new leaf built in 156s.
- Final `lake env lean` on the actual leaf passed, exit 0 with empty diagnostics.
- All eight new declarations audited in a separate `#print axioms` scratch, exit 0:
  exactly `propext`, `Classical.choice`, `Quot.sound`. Capstone type checked.
- All eight names have no outside duplicate in owned Lean sources; leaf wired.
- Generated indexes refreshed. `lint --check-generated` failed solely for 11 unrelated
  unwired modules listed below; no new-leaf finding or stale generated index.
- No full/umbrella build, numerical experiment, new axiom, proof hole, heartbeat increase,
  commit or push. Owned scratch files cleaned after results were recorded.

Global lint exceptions: `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
`CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
`CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
`MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
`SpeiserEventualEquivalence`, `ThetaMovingShellFirstOrderPhase`,
`ZetaZeroDensityPowerSaving`.

## Obstruction and positive survivor

- **Failed inference:** source membership at every positive weight supplies a uniform
  energy bound near weight zero, allowing triviality at zero to be transported by continuity.
- **Exact obstruction:** the fixed, nonzero, actual source witness `spuriousWitness 1` has
  energy `1/(2a)` for every `a>0`; this exceeds every fixed bound in every `(0,ε)`.
- **Positive survivor:** exact source-domain classification for all real weights, together
  with the exact energy law. These identify the singular domain boundary without assuming RH.
- **Status:** dependency-closed paper proof and all eight Lean declarations audited. This
  rejects the stated uniform-bound inference; it does not reject every source-selected
  regularization or prove anything about canonical index vanishing.

RH remains unproved. The subsequent raw-coefficient test is now closed with a formal positive
survivor: `5-failed/pm-raw-mobius-haar-tail-floor.md`. Active successor:
`1-in-progress/pm-log-smoothed-mobius-haar.md`.
