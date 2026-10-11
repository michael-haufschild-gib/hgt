# Edgewise concentration of the logarithmic transport correction

Status: formalized and natively audited.
Research sources: local Lean corpus only. No external novelty claim.

## Target

For n=r+1, A=k+2 and adjacent logarithmic gap g_i, let
T_i=(A/n)(1-Ag_i). The previous result controlled E_m[T]. Prove the
stronger E_m[(T-1/2)^2]->0 at k=2n^2+t(r), for every natural-valued offset.
Deduce vanishing tail mass at every fixed positive rational precision.
Transfer the squared-error law to actual optimal transport plans of all
mixtures, allowing arbitrary varying endpoints.

Audit the boundary between weighted and uniform concentration: prove that
the first edge correction tends to zero (for arbitrary starts), while the
last tends to one at quadratic starts. Thus the weighted concentration
theorem coexists with persistent extreme edges.

## Paper proof

Existing local deficit bounds imply i <= (A+n)(1-Ag_i) and
A(1-Ag_i)<=i+1<=n, with 1-Ag_i>=0. Thus 0<=T_i<=1 for ALL r,k.
When n^2<=A, n(1-Ag_i)<=1, hence |nT_i-i|<=1.
Write n(T_i-1/2)=(nT_i-i)+(i-r/2)-1/2. Two elementary square bounds give
n^2(T_i-1/2)^2 <= 4(i-r/2)^2+4. Average against edge mass:
R=E_m[(T-1/2)^2] <= (4H+4)/n^2, where H is the existing centered edge
second moment. At quadratic starts H/n^2<=e=sqrt((n+1)/2)/n.
Since n>=1, 1/n^2<=e. Therefore 0<=R<=8e->0.
For threshold 1/(q+1), tail mass <= (q+1)^2 R ->0.

For node pairs use squared correction error off the diagonal and zero on
the diagonal. This cost is symmetric. Existing canonical coupling cost
contraction identifies its expectation with R. The full-mixture coupling
cost identity multiplies it by delta=|a-b|<=1. Thus actual optimal-plan
squared error tends to zero uniformly over arbitrary endpoint sequences.

For i=0, the local upper deficit gives T_0<=1/n for every k. Since T_0>=0,
T_0->0 along arbitrary starts. For i=r, |nT_r-r|<=1 and T_r<=1 imply
|T_r-1|<=2/n at quadratic starts, hence T_r->1. These endpoints identify
the sharp distinction: transport mass concentrates, the entire edge set
does not collapse to a single correction value.

## Corpus audit and plan

- Prior first-correction closure metadata revalidated: no issues.
- Local correction/concentration search found no existing edgewise law.
- Existing edge-centered moment estimate and exact coupling-cost identities
  supply all mathematical inputs.
- Formalize local correction bounds and mean identity.
- Formalize squared-error estimate and tail/limit roots.
- Formalize actual transport-plan cost identity and uniform limit.
- Audit all declarations natively, standard axioms, imports/freshness,
  unique names, local root index, and formal lint.

## Verification log

- `WeilLogShiftEdgeLogCorrection`: five declarations passed native Lean
  without diagnostics, including unconditional unit-interval bounds.
- `WeilLogShiftEdgeCorrectionMoment`: four declarations passed native Lean
  without diagnostics; R <= (4H+4)/n^2 and R <= 8e established.
- `WeilLogShiftEdgeCorrectionLimit`: five declarations passed native Lean
  without diagnostics; mean-square and all fixed-precision tail limits proved.
- `WeilLogShiftCorrectionPlanCost`: seven declarations passed native Lean
  without diagnostics. Exact canonical expectation is R; every mixture's
  expectation is |a-b| R. Diagonal cost is zero. An initial diagonal simp
  mismatch was repaired by an explicit rewrite before the successful check.
- `WeilLogShiftCorrectionPlanLimit`: two declarations passed native Lean
  without diagnostics, including unconditional convergence for arbitrary
  natural-valued offsets and arbitrary varying mixture endpoint sequences.
- `WeilLogShiftEdgeCorrectionExtremes`: five declarations passed native Lean
  without diagnostics. First-edge correction tends to zero at arbitrary
  starts; last-edge correction tends to one at quadratic starts. An initial
  division-normalization failure was fixed with an explicit ring identity
  and monotonic multiplication.
- Metadata audit: six leaves, 28 public declarations (4 definitions,
  24 theorems), globally unique. All 12 incoming imports inspected; own and
  direct dependency objects fresh; leaf logs empty; each leaf wired once.
- Local root searches found all five roots, with no markers. Scoped diff
  and whitespace checks passed.
- Final native scratch audit passed: all 28 public declarations use only
  propext, Classical.choice, and Quot.sound. Eight API references also
  type-checked. All owned native jobs are terminal.
- Repository lint: 367 size warnings, 15 unrelated errors. Fourteen missing
  umbrella imports: RHTower.CCMParityTopLayerEvenFloor,
  CCMParityTopLayerNoGo, CCMParityTopLayerOddModel, CCMParityTopLayerOddTest,
  CCMParityTopLayerProjection, CCMParityTopLayerTransform,
  CCMPolarOddPrimeJumps, PaperEulerWoldCompactCharacter,
  PaperEulerWoldDepthHistory, WeilEvaporationLockRigidity,
  XiCriticalityEveryScale, XiSliceHeatTransferNoSlack;
  HTGeometry.PaperConvergentDiagonal, QKrawtchoukCompanionTriangular.
  Remaining error: sorry in CCMPolarOddPrimeJumps.lean:104,
  ccmPolarOddSource_eq_core_add_atoms. None belongs to this closure.

## Formal roots

- `WeilLogShiftEdgeCorrectionLimit.lean:12`:
  `tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_zero`.
- `WeilLogShiftEdgeCorrectionLimit.lean:57`:
  `tendsto_finiteWeilCanonicalEdgeLogCorrectionTailMass_zero`.
- `WeilLogShiftCorrectionPlanLimit.lean:26`:
  `tendsto_finiteWeilMixtureCoupling_log_correction_dispersion_zero`.
- `WeilLogShiftEdgeCorrectionExtremes.lean:50`:
  `tendsto_finiteWeilCanonicalEdgeLogCorrection_first_zero`.
- `WeilLogShiftEdgeCorrectionExtremes.lean:63`:
  `tendsto_finiteWeilCanonicalEdgeLogCorrection_last_one`.

All roots quantify structural data only; no unproved analytic premises.

## Audit artifacts

- `/tmp/hgt-edge-correction-metadata.py`
- `/tmp/hgt-edge-correction-declarations.json`
- `/tmp/hgt-edge-correction-incoming-imports.txt`
- `/tmp/hgt-edge-correction-final-audit.lean` and `.log`
- `/tmp/hgt-edge-correction-root-search.json`
- `/tmp/hgt-edge-correction-plan-root-search.json`
- `/tmp/hgt-edge-correction-lint.log`
- Six `/tmp/hgt-<Leaf>.log` native leaf logs.
