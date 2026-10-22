# EWJ: source admission and norm exhaustion

- **ID:** EWJ-SOURCE-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Read-only `docs/reports/rh-current-frontier-map.md`, EWJ.
- **Statement:** Remove an actual source-admission or norm-exhaustion obstruction in the Euler/Wold third-jet route without importing a zero-divisor condition or the desired sign.
- **Contribution credit:** None yet. An estimate, receiver, renamed target, or existing result does not qualify.

## Plan

1. Inspect the native three-channel source, complete depth history, quotient character, and exhaustion topology.
2. Conjecture and attack independent admission mechanisms, retaining endpoint jets and transverse norm defects.
3. Write a dependency-closed paper proof before Lean. Directly audit any resulting module, check axioms, wire imports, and clean owned scratch.

Corpus-only mathematical evidence. No numerical experiments, web, novelty audit, historical research Markdown, added analytic premises, full builds, or heartbeat increases. One owned foreground Lean process at a time. Preserve concurrent changes.

## Initial questions

- Is the missing object the original source, its operator completion, or a moving-depth norm limit?
- Can a source-defined correction preserve the endpoint/forward channel while making the required exhaustion legal?
- Which finite-depth identities survive the topology needed by the RH receiver?

## Literal source and topology

The three source channels are the negative Euler Jordan mass, positive Wold Jordan mass,
and BV endpoint third jet, multiplied by the literal conormal short `S(c)=4‖c‖²`.
`PaperEulerWoldDepthHistory` already constructs their complete bounded diagonal history
without assuming a Xi zero exists. Its cofinal character is
`χ(a,b,d,c)=(8/3)‖c‖²(-a+b+2d)`.

`PaperEulerWoldCompactCharacter` and `PaperEulerWoldDepthCompression` already prove exact
essential norm `|χ|`, the complete compactness classification, and the iff for operator-norm
prefix exhaustion. The full endpoint channel has essential norm `(16/3)‖c‖²`. Finite clocks,
strong convergence, and one-history masked recovery do not remove this transverse gap.

These constructions are existing corpus results, not contributions of this turn. The selected
open problem requires a source law in the original completion that pays the transverse endpoint
or admits the required inverse-depth operation. Replacing operator-norm exhaustion by compact-open
convergence would not satisfy that problem.

## Conjecture and failure ledger

1. **Construct the zero-independent fixed history.** Already done by
   `paperEulerWoldHistoryOperator` and `paperEulerWoldDepthReporter_tendsto`; no divisor-existence
   assumption occurs in this construction. Reintroducing it would duplicate existing work.
2. **Exhaust every history in norm by finite depth.**
   `paperEulerWoldHistoryOperator_norm_compression_tendsto_iff` gives exactly
   `c=0 ∨ -a+b+2d=0`. The endpoint and transverse reporters lie outside this locus for
   nonzero coefficients. General compact mixing cannot change their character.
3. **Use all masks or a fixed solid history hull.**
   `paperEulerWoldDepth_uniform_masks` and `paperEulerWoldDepth_uniform_solidHull` already
   give these uniform limits, including on channels whose operator-norm gap persists.
   Uniformity inside a fixed hull is not uniformity on the unit ball.
4. **Cancel Euler and Wold before admitting the source.** Intrinsic Jordan selection already
   retains every prime label and Euler prime-power depth. Its negative and positive masses
   both tend to `2/3`; pre-compression variation tends to `4/3`, while post-compression
   variation tends to zero. Grade forgetting erases the surviving variation. This is an
   exact existing information-loss law, not a vanishing-source theorem.
5. **Choose a source-budgeted transverse reporter.** Already constructed: its character is
   exactly half the primitive budget. However,
   `not_eventually_sourceBudgeted_and_endpointDominating_linearReporter` excludes simultaneous
   budget control and domination of the literal endpoint. A new linear combination does not
   repair this missing comparison.
6. **Use the complete positive or canonical Krein-signed conservation split.**
   `sourceHorizontalWoldBVInteriorEnergy_add_endpointEnergy` fixes the positive total at
   `8‖c‖²`, above the primitive budget at every clock for nonzero `c`. The canonical signed
   split has limit `(8/3)‖c‖²`, still above that budget. Keeping both conserved pieces is
   necessary, but does not close their budget.
7. **Annihilate endpoint excess before choosing a positive order.**
   `SourceHorizontalEulerWoldIndefiniteEndpointAnnihilation` already constructs the unique
   diagonal counterleg `T-R`. It is cofinally negative; the signed block has trace `T`.
   Fundamental-symmetry rotation changes that trace to `2R-T` and overspends. Signed
   cancellation exists, but positive rotation does not preserve its budget advantage.
8. **Sew both Hardy orientations after endpoint scaling.** Their signed sewing defects cancel
   exactly. Nonetheless, `sourceHorizontalEndpointScaledHardy_both_moderate_iff_re_eq_half`
   says that both nontrivially scaled orientations enter the original bilateral source
   topology exactly on the critical line. Scalar normalization cannot repair this admission.
9. **Prove positive order on the source before residue selection.**
   `FrankensteinPreDivisorWoldOrbitCompletedSourceOrderFirewall` rules out the proposed local
   Loewner order and positive Gram-remainder conservation at every retained strict-right
   fibre once depth is large. Their global existence is RH-equivalent. Naming the order
   “pre-divisor” does not make it an independently proved source input.
10. **Admit the physical inverse-Wold operation through its trace graph.**
    `PrimeDepthBVWoldSourceNormalSchattenBridge` already identifies the physical squared
    Gamma deattenuation with multiplication by `p`. Depth-two Xi coefficients belong to
    its trace graph exactly on the line. Global graph admission is RH-equivalent, not a
    domain theorem supplied by the present finite-depth construction.
11. **Use cofinal equicontinuity or Banach–Steinhaus.** Deep centered anomalies tend to zero in
    all-prime `ℓ¹`, while exact inverse-depth transport returns `a*woldCoeff 1 p` at every
    depth. `cofinalSourceNormalEquicontinuity_iff_zero` and
    `nonempty_primeDepthBVWoldBarrelledSourceCertificate_iff` classify the proposed controls
    exactly by `a=0`. Pointwise boundedness on the completed source is the missing input;
    boundedness on algebraic finite packets does not supply it.
12. **Insert the horizontal weight as one holomorphic test.**
    `no_differentiable_sourceHorizontalWoldNormalizedPolarImaginaryProfile` rules this out:
    a holomorphic function depending only on the imaginary coordinate is constant, while
    the literal normalized Wold weight is not. A reflected second variable or an operator
    source is necessary.
13. **Promote the entire coefficient carrier to the required completion.**
    `SourceHorizontalWoldPrimeClockComplexCarrier` supplies an entire coefficient carrier;
    its source-faithfulness bridge is not present among its corpus references. The real
    finite-source prime-clock limit is already proved in `SourceHorizontalWoldPrimeClockProfile`.
    A contemplated compact-uniform complex bridge would concern the normalized window
    `t=u/log(p_N)`. It would not establish the original depth-history operator-norm
    exhaustion or realize the nonholomorphic horizontal weight. No such weaker bridge was
    implemented or counted as the requested hard-obstacle removal.
14. **Use compact-open source tightness to retain exact charge.**
    `XiHeatCassiniWoldOrbitChargeCompactOpenNoGo` constructs the precise obstruction:
    multiplicity-matched bubbles converge locally uniformly to Xi while retaining off-line
    reflected Wold charge. Compact-open scalar descent of that exact charge is RH-equivalent.
    Ordinary analytic convergence alone is not the missing marked-source topology.
15. **Pay the signed excess with the complete matched Suzuki current.**
    `SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall` retains the literal
    absolutely summable Route-O current. Every fixed coefficient-faithful compensation is
    null after cubic prime-clock normalization, leaving the same `(8/3)‖c‖²` limit. This
    excludes the tested fixed source scaling, not every possible moving arithmetic source.

## Positive-survivor and significance audit

The strongest positive statements exposed here are exact cofinal-character classification,
componentwise source admission with `A₊+R=2S`, intrinsic Jordan variation accounting, the unique
signed endpoint counterleg, and the exact physical inverse-depth multiplier. All are already
formalized. A second pass through signed blocks, inverse-depth graph domains, complete source
readouts, and nonlinear prime-clock carriers produced no new dependency-closed positive theorem.
**NO NEW POSITIVE SALVAGE FOUND in this tested batch.**

EWJ remains open. Do not retire the candidate, assert an unconditional off-line Xi zero, promote
the card, or award significant-contribution credit. No new theorem or source-domain construction
has yet removed the requested obstruction.

## Search record

- Deep search `Euler Wold third jets source history admission norm exhaustion compact quotient character`,
  budget 300 seconds: `partial:false`, no errors or unfinished stages. Its candidate lemmas were
  mostly generic Euler-characteristic/jet hits; source arguments recovered the actual Wold
  residue and conormal formulas. The proposed ingredient chain did not supply norm exhaustion.
- Deep search `Wold prime clock complex entire carrier compact uniform convergence all derivatives source finite deformation`,
  `--module SourceHorizontal`, budget 300 seconds: `partial:true`; `filter_and_judge` reported
  `local model returned incomplete or malformed JSON`. Available candidate lemmas, source
  arguments, proof ideas, and ingredient sets were inspected without restarting the search.
  The useful hits recovered the exact finite source/profile/holonomy identities; no retained
  norm-exhaustion theorem was supplied.
- Both inventories covered 73,164 source files completely. Compiler enrichment remained
  incomplete: 56,076 pending, 2,659 stale entries, background refresh running. Search metadata
  alone is not proof verification. Only Lean evidence was used; historical prose was ignored.

## Verification

- Imported 17 existing source modules and audited all 36 selected declarations with
  `#print axioms` in `/tmp/hgt_ewj_audit.lean`. Direct Lean invocation exited 0.
  Parsed output against the complete declaration manifest: 36/36 matched; every reported
  axiom belonged to `{propext, Classical.choice, Quot.sound}`; no `sorryAx` or error appeared.
- At audit start, all 17 selected module artifacts existed and were no older than their source
  files. This check concerns those artifacts, not global dependency freshness.
- Audited results include exact history/compression character, essential norm, uniform masks,
  Jordan variation, transverse budget gap, unique signed counterleg, bilateral moderation,
  completed-source order firewall, inverse-Wold trace domain, cofinal equicontinuity,
  barrelled-source certificate, holomorphic-profile obstruction, entire carrier, real
  prime-clock resummation, compact-open charge obstruction, and complete split conservation.
- No Lean source changed. These checks validate existing exclusions and positive survivors;
  they do not establish a new admission theorem or significant contribution.
- Final direct source check, from `formal/`:
  `lake --old env lean GaloisForLFunctions/RHTower/PaperEulerWoldDepthCompression.lean`
  exited 0 with empty output. No umbrella or full build was run.
- All owned search and Lean handles terminated. Removed and verified absence of all six
  owned `/tmp/hgt_ewj_*` scratch files. Saved handoff memory
  `rh/ewj-source-admission-audit-2026-10-17`.

## Gates

- [x] Literal source and original norms inspected.
- [ ] Independent producer or substantive obstruction removed.
- [ ] Dependency-closed paper proof.
- [ ] Exact Lean theorem, direct audit, umbrella wiring, and cleanup.
- [ ] Significant-contribution audit.

## Log

- 2026-10-17 — Selected previously unworked EWJ. Started documented deep corpus search `Euler Wold third jets source history admission norm exhaustion compact quotient character`, budget 300 seconds. Initial source reads show that each fixed three-channel reporter already has a bounded complete depth-history operator and an exact compact-quotient character.
- 2026-10-17 — Completed 15-mechanism source audit and second positive-salvage pass. Existing inverse-depth and completed-source admission formulations already carry critical-line or RH strength; the apparent entire-carrier bridge addresses a weaker topology. No qualifying new theorem retained. All 36 selected existing declarations passed the axiom audit.
