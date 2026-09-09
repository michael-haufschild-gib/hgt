# CCM-FU deep corpus search: cancellation mechanisms

- **ID:** `ccm-fu-deep-search-cancellation`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / applicability audit
- **Status:** Searches and three Lean signature checks completed; no new source inequality or RH proof.
- **Target:** Actual divisor source → uniformly bounded normalized signed Abel head → CCM-FU → RH.

## Exact obligation

Write `S(M)=mobiusDivisorSquareRootAbelMoment M`. The verified endpoint remains
`∃ B≥0, ∀ M≥2, |S(M)/M|≤B`, through
`riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded` in
`CCMFUSuzukiMobiusDivisorAbelProducer.lean`.

The original channel diagonal is already at most `722 M²`. Its signed cross
terms, or a bounded complete prime-processing history, still need control.
The arity identity accounts for copied-square costs but does not bound its
accumulated signed charge or the terminal empty head.

## Deep-search evidence

All five requests used `scripts/formal_tools.py research`, `--mode deep`,
`--any`, and no module or exclusion filter. The first allowed refresh; subsequent
requests used `--no-refresh`. Exact queries, OR interpretations, expanded queries,
ranked declarations, candidate lemmas, source methods and coverage metadata are
preserved in [search-evidence.json](ccm-fu-deep-search-cancellation/search-evidence.json).

| Search | Budget | Lexical matches / modules | Returned declarations / candidate lemmas / source arguments |
|---|---:|---:|---:|
| Complete signed Möbius/divisor Abel cancellation | 120 s | 139844 / 22221 | 25 / 25 / 25 |
| Polynomial-to-subpower growth with retained boundaries | 120 s | 323660 / 33826 | 25 / 0 / 0 |
| Signed dyadic contraction | 120 s | 27036 / 10230 | 12 / 12 / 12 |
| Accumulated cross terms and multiscale orthogonality | 120 s | 22058 / 7677 | 12 / 12 / 12 |
| Diagonal domination through almost orthogonality | 180 s | 68046 / 20104 | 12 / 12 / 12 |

Every request reported `partial=true`. Four reached their deadline while
filtering/judging; the second returned after about 66 seconds with interrupted
retrieval/decomposition stages. All five returned empty `proof_ideas` and
`ingredient_sets`; their absence is not evidence that no such argument exists.
The dyadic query's generated expansion drifted into group theory and was discarded.

One complete inventory snapshot reported 55,915 indexed files, including 46,518
Lean files and 9,397 prose files, with 719,312 declarations. Compiler metadata
was pending for all 46,518 Lean files. Semantic coverage was explicitly incomplete;
even the last request reported seven pending entries. These are tool coverage
reports, not exhaustive theorem-applicability checks. No corpus-wide absence claim
follows from this search.

## Candidate applicability

| Existing result | Useful mechanism | Remaining source obligation |
|---|---|---|
| `bourgain_subpower_of_twoThirds_recurrence`, `BourgainPowerScaleSubpower.lean` | A coarse power bound plus `b(x)≤Cδ x^δ b(x^(2/3))` for every `δ>0` gives every positive power saving. | Establish this recurrence for an actual source envelope, with constants uniform in cutoff. The theorem assumes the recurrence. |
| `bourgainSectionOne_recurrenceStep_subpower`, `BourgainSectionOneRecurrenceStep.lean` | Exact physical-volume cancellation costs only 256 in its local bilinear moment comparison. | Identify the actual divisor source with the specified four-curve phase-space moment, establish `BourgainSectionOneLocalDecouplingAt`, and retain the cost of reading the desired value from that moment. |
| `exists_initialEnergy_remainder_subpower`, `EulerDeletionCoprimeHeadSubpower.lean` | Complete coprime floor columns reduce to prime-supported counts; reciprocal weights make the remaining error subpower. | Its conclusion subtracts `harmonicQuadratic N * headMass N` and concerns residue heads. Neither that quadratic term nor the later tail is bounded by this theorem. |
| `exists_initialEnergy_remainders_subpower`, `EulerDeletionGcdHeadSubpower.lean` | The same remainder control sums over all gcds with their physical inverse-gcd weight. | Retains every harmonic quadratic coefficient and the later tail; does not control the divisor-Abel gcd cross sum. |
| `sampled_energy_le_of_correlation_bounds`, `HTGeometry/LargeValuesDuality.lean` | Duality converts actual diagonal, off-diagonal correlation and separation-row bounds into a sampled energy bound without differentiation. | Construct the source sampling matrix and prove its correlation and row bounds at the required scale. They are explicit premises, not consequences of duality. |
| `burnolDyadicPartialSum_sub`, `BurnolDyadicCoboundaryContraction.lean` | A literal two-scale coboundary telescopes with an exact geometric tail and an `L²` error bound. | No corresponding coboundary identity with a controlled remainder has been established for the complete signed Abel source. |

The first three signatures were checked together using one foreground
`lake env lean /tmp/ccm-deep-search.RWS4hk/CandidateCheck.lean` invocation and existing
oleans. It exited successfully. [Captured signatures](ccm-fu-deep-search-cancellation/lean-signatures.txt)
retain the actual premises and conclusions. This was signature verification,
not a new proof, re-audit of old axioms, or rebuild of these modules.

## Two precise transfer gaps

**Counting versus weighted defect.** For residue columns, complete inversion
gives a prime-supported count. For the actual CCM-FU source,
`coprime_moebius_primeFreeDivisorDefect` instead gives

```text
Σ_(d≤N, coprime(r,d)) μ(d) D(floor(N/d))
  = Σ_(n≤N, primes(n)⊆primes(r)) psiDefect(floor(N/n)).
```

The `n=1` term retains `psiDefect(N)` for every positive N. Bounding the number
of supported quotients does not bound this weighted signed sum. The exact Abel
transport in `MobiusDivisorCoprimeColumnTransport.lean` retains all these values.
Consequently the residue-head subpower theorem supplies a method to examine,
not an already-proved estimate for this source.

**Uniform coefficient bounds lose the needed cancellation.** A direct one-row
application of large-values duality is weighted Cauchy. More generally, an estimate
`|Σ a_d C_d|²≤K Σ C_d²` valid for every `|a_d|≤1` also holds for
`a_d=sign(C_d)`, so it requires `K≥(Σ |C_d|)²/Σ C_d²`. The existing
[positive-normalization certificate](../3-formalized/ccm-fu-positive-normalization-cost.md)
proves this ratio has order M for the actual source. Thus this uniform-coefficient
application cannot give a constant-factor diagonal ceiling. A useful transformed
correlation estimate must exploit the actual signed source before that information
is discarded. This identifies a limitation of the direct application, not a
retirement of every duality or almost-orthogonality argument.

## Next arithmetic test

The source-facing candidate remains a collective bound for the exact prime-release
correlation in `MobiusDivisorFixedCorePrimeCorrelation.lean`, allowing temporary
increases while controlling the complete energy. Its current absolute tail bound
contains `2*((3/5)*2^(P.card-1))²/T`; it is not uniform in a growing processed core.
Any scale-contraction proposal must remove that dependence through signed source
control, rather than insert it as a recurrence premise.

An all-epsilon bound on the normalized Abel head remains a possible weaker target;
this audit has not constructed its exact Lean implication to RH. Existing
all-epsilon sharp-window and aperture-transfer theorems concern explicitly different
quantities and cannot be silently substituted.

No numerical experiment, new Lean declaration, umbrella build or frontier-map edit
was made for this audit. RH remains unproved.
