# CCM-FU: deep search for cancellation with a growing prime core

- **Status:** Six unrestricted deep searches completed; no new arithmetic estimate or RH proof.
- **Chain:** Actual divisor source → uniform complete signed Abel bound → CCM-FU → RH.
- **Evidence:** [Full search responses](ccm-fu-deep-search-growing-core/search-evidence.json), [checked Lean signatures](ccm-fu-deep-search-growing-core/lean-signatures.txt).
- **Related work:** [Previous cancellation search](ccm-fu-deep-search-cancellation.md).

## Search scope and limitations

Every request used `--mode deep --any --no-refresh`, with no module filter.
Thus the lexical operator was OR, not the default multiword AND. Queries
described mechanisms or used one broad concept. The table records reported
search matches, not a count of proofs whose applicability was established.

| Query | Budget / elapsed | Matches / modules | Declarations / candidates / source arguments |
|---|---|---|---|
| Uniform cancellation under growing families of multiplicative difference operators | 120 / 96.8 s | 151086 / 30992 | 18 / 18 / 0 |
| Riesz product weighted mass prime frequencies cancellation | 120 / 120.0 s | 78946 / 13715 | 20 / 0 / 0 |
| Finite Euler product growth near shrinking frequency | 120 / 120.0 s | 78940 / 16412 | 20 / 20 / 20 |
| Control signed energy using arithmetic correlations between dilated copies | 120 / 120.0 s | 33715 / 8443 | 20 / 20 / 20 |
| Random ordering and cancellation of signed interactions | 120 / 120.1 s | 157629 / 31402 | 16 / 16 / 16 |
| discrepancy | 300 / 76.3 s | 490 / 176 | 12 / 12 / 12 |

All six reported `partial=true`. The discrepancy request completed with no
reported runtime error and only `semantic_index_incomplete` unfinished. The
others reported interrupted retrieval, deadline limits, or a disconnected
worker. No service was restarted. The last inventory reported 55,940 files,
46,540 Lean files, 720,486 declarations, and complete file inventory. Semantic
coverage was nevertheless only 2,167,371 ready entries of 2,331,213 expected.
The reported `pending=0` does not imply semantic completeness.

Compiler metadata remained largely pending: the last inventory reported 48
compiled snapshots, 43 stale snapshots, 5 errors, 43,709 pending, and 2,734
unavailable. The candidate listings therefore are discovery evidence, not
kernel verification of their current source bodies. Four selected signatures
were checked separately against cached Lean modules, as described below.

All `proof_ideas` lists were empty. Two requests returned one `ingredient_sets`
entry each. The difference-operator entry concerned distribution of subtraction
through differentiation and did not establish multiplicative source cancellation.
The discrepancy entry is assessed explicitly below. Neither entry was a proof.

## Candidate applicability

| Result inspected in source | What it actually supplies | Missing input for this problem |
|---|---|---|
| `GibbsGas.gibbsNormalizedCurrentEnergy_insert_add_dissipation` | Exact nonnegative dissipation in a finite Gibbs current, after division by its partition mass; its right side contains both dilation energies. | Identification with the literal divisor Abel source, plus the total mass and all-scale budget needed to recover an unnormalized head. Discarding dissipation does not give a one-state contraction. |
| `Sieve.MRBilinear_moebius_of_correlations` | A bilinear short-interval conclusion from `AveragedCorrelationSmall`, window growth and a square-root cap. | The averaged correlation hypothesis is explicit and unproved by this theorem. No such estimate was obtained for the actual Abel pairing. |
| `ccmActualHeadCoherentQuantileGammaProducer_le_sourceQuadratic` | A source-relative lower bound that keeps the completed prime–polar current coherent. | Its producer is `(2*gammaHardyPhaseRate 0+4)*norm(f)^2 - 2*chiSquare`. Positivity of that expression is still required; its displayed lower bound alone does not prove nonnegativity of the source quadratic. |
| `deletionSourceEnergy_mul_lt_independent` | Strict destructive overlap for `blockDeletionCoefficient` under the convergent Dirichlet weight, with the exact dilation coefficient retained. | This is an infinite weighted deletion source, not `C_d(M)`. A transfer must establish the literal source identity, physical cutoff, endpoint terms and required scale. None follows from the strict sign alone. |
| `ReversibleChain.abs_discrepancy_le` | Capacity times a negative-energy dual norm bounds a finite-chain discrepancy. | The chain/source identification and a uniform bound for the actual dual norm remain missing. This does not prove the weighted prime-neighbor cut inequality. |
| `abs_cell_discrepancy_le`, `CCMBVMuntzSummation.lean` | A cell error is bounded by cell width times the actual variation; variations sum over a partition. | Uniform variation of the changing signed source is not supplied. Replacing it by total unsigned variation again discards the needed cancellation. |
| `exists_periodicProductFejerTent_multiplicativeWindowDiscrepancy` | Translated-window control at an explicit Fourier cost under `¬VWMA` for the frequency vector. | Neither strong extremality for the needed source frequencies nor a uniform growing-dimensional Fourier cost is established here. |

The first four signatures passed one foreground
`lake env lean /tmp/ccm-core-search.NUvRjh/CandidateCheck.lean` run using existing
oleans. This verifies the available types and explicit premises; it is not a
new proof or a re-audit of their axioms. No module was rebuilt.

### The proposed discrepancy ingredient chain does not close

The search paired
`riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy`
with `chronologicalWeightedHeatError_discrepancy`, then proposed a cofinal
thermal-truncation step. Reading the actual statements exposes two gaps:

1. The Bernstein theorem assumes both nonnegative approximants and the full
   dimension-weighted square-discrepancy estimate `henergy`. Its proof converts
   that assumed estimate to an L1 bound by Cauchy–Schwarz.
2. The heat theorem estimates a weighted chronological heat residual from
   bounds `hprev` for earlier raw residuals. Its source, norm and indexing are
   different; no identification with Bernstein coefficient packets is given.

The final thermal theorem is an equivalence with RH. Its forward construction
uses RH. It cannot furnish an unconditional approximation schedule to discharge
the earlier hypothesis. Thus the proposed chain leaves the arithmetic estimate
unproved rather than obtaining it from the corpus.

## Growing-core calculation and prior-research correction

The fixed-core Mellin identities suggest retaining the squarefree density in
the product

```text
L_P(t) = product_(p in P) [1 - 2 sqrt(p)/(p+1) cos(t log p)].
```

The [spectral amplification candidate](ccm-fu-prime-prefix-spectral-amplification.md)
records a possible full-prefix lower bound and its unproved source-identification
steps. A targeted source search found that `MobiusCriticalPrimeBlockGammaBand`
already proves terminal-block resonance on a shrinking interval, and
`MobiusCriticalPrimeBlockResonance` supplies its prime-count budget. The new
obligation would be to pay all earlier factors and retain the changing density.

The actual-source increasing-order ceiling is already excluded in
[CCM-FU prime-pair energy](../5-failed/ccm-fu-prime-pair-energy.md), with a formal
[head asymptotic](../3-formalized/ccm-fu-late-prime-head-asymptotic.md).
Consequently another obstruction to that same ceiling is not selected for
formalization. Likewise the [half-selection obstruction](../5-failed/ccm-fu-bernoulli-prime-energy.md)
already excludes every fixed diagonal multiplier for independent averaging.
Neither result excludes a successful source-dependent order or proves the
final signed bound.

## Exact remaining arithmetic target

Write `C_d(M)=mu(d)*K_d(M)` for the literal channels. The corpus already gives
`sum C_d(M)^2 <= 722*M^2` and the exact gcd decomposition

```text
(sum C_d(M))^2 = sum C_d(M)^2 + sum_r G_r(M).
```

A uniform upper bound of order `M^2` for the complete signed cross sum would
therefore give the required `O(M)` head. No componentwise sign, fixed-core
limit, independent average or arbitrary-coefficient norm bound can be substituted
for that missing estimate. The prime-neighbor capacity candidate and adaptive
raw-energy history remain open; this search established neither.

No mathematical computation, new Lean declaration, axiom check, umbrella build,
or frontier-map edit was performed. RH remains unproved.

## Separate ordering search

An additional unrestricted deep OR query for `Steinitz` used a180-second
budget and returned after41.7seconds:15 lexical matches in5modules,8 listed
declarations,16 candidate lemmas,16 source arguments, no proof ideas and one
proposed ingredient set. It reported no runtime errors but incomplete semantic
coverage. [Complete response](ccm-fu-deep-search-growing-core/steinitz-search.json).

The returned normalization chain concerns rank-two number-field ideal classes,
not bounded vector partial sums. No prime-selection estimate follows from it.
The directly inspected `MobiusDivisorSquareRootTerminalOrder.lean` already
solves the scalar phase after all small primes are processed, but keeps both
endpoint energies in its ceiling. It leaves the interacting phase and the
final source bound open. No unrelated Steinitz infrastructure was added.

The separate [gcd-prefix diagnostic](ccm-fu-gcd-prefix-budget.md) was cancelled
before computation: archived data already have `G_1(1024)>D(1024)`, violating
its fixed constant-one bound at its first gcd prefix. Those are numerical
source values, not a new formal counterexample. The experiment script was
removed; no larger coefficient was substituted.
