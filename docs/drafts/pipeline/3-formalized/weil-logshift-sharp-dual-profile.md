# Sharp dual profile of the common normalized receiver

Status: formalized; direct leaf and axiom audits passed, 2026-10-09.

## Corpus evidence and scope

Only local Lean sources consulted. `WeilLogShiftC0VanishingEnvelope` proves a
nonnegative C₀ envelope for every finite-dimensional linear C₀ family.
`WeilLogShiftC0PotentialOperator` supplies the actual common normalized operator
on the regular coefficient subspace, with a HasSum contract at every shift.
Local corpus search found these predecessors; exhaustive `rg` of WeilLogShift
leaves found no sharp dual profile. This is a corpus-relative extension, not a
claim of external novelty.

## Conjecture and dependency-closed paper proof

Let E be a finite-dimensional real normed space, X a topological space, and
S:E→ₗ C₀(X,ℝ). Define ℓₓ(a)=S(a)(x). Evaluation is linear; finite dimensionality
makes each ℓₓ continuous. The local mathlib theorem `continuous_clm_apply`
shows x↦ℓₓ is norm-continuous since each S(a) is continuous.

The previously proved envelope g≥0 satisfies |ℓₓ(a)|≤‖a‖g(x), so the operator
norm characterization gives ‖ℓₓ‖≤g(x). Since g tends to zero at infinity,
norm squeezing proves ℓₓ→0 there. Thus ℓ belongs to C₀(X,E*), and
q(x)=‖ℓₓ‖ belongs to C₀(X,ℝ).

For every c≥0, q(x)≤c iff |S(a)(x)|≤c‖a‖ for all a. Consequently q is the
pointwise smallest nonnegative norm envelope, independent of the basis used
to establish vanishing. Also q(x)=0 iff S(a)(x)=0 for every a. For the fixed S,
the supremum norm of q equals the operator norm of S: q(x)≤‖S‖ follows from
bounded evaluation; conversely |S(a)(x)|≤q(x)‖a‖≤‖q‖‖a‖, then take the two
operator/supremum norm bounds.

Apply this construction to the existing normalized operator on the actual
regular subspace L. Its dual profile gives a HasSum receiver directly valued
in L*. No extra analytic premise or convergence assumption is introduced.

For any positive response threshold ε and any amplitude bound R, choose
δ=ε/(1+max R 0)>0. Eventually q(x)<δ. Then every amplitude with ‖a‖≤R has
|S(a)(x)|<ε. Equivalently, every response at least ε outside that compact
region requires amplitude norm greater than R. This is uniform over all
regular amplitudes, including those selected as a function of the shift.

## Meaning and limits

The profile identifies the exact local sensitivity and common invisible
locus. It is canonical for a fixed normalization and amplitude norm, not
independent of those choices. No injectivity or explicit decay rate follows.
The amplitude escape conclusion is a receiver cost law, not an RH proof.

## Work log / remaining checks

- [x] Read predecessor Lean statements and proofs; check local API source.
- [x] Dependency-closed paper proof recorded before new Lean code.
- [x] Verify new mathlib names in a /tmp Lean scratch file.
- [x] Formalize dual profile, sharpness, zero locus, global norm identity.
- [x] Specialize actual regular receiver with HasSum and amplitude escape.
- [x] Direct leaf checks, all-public-declaration axiom audit, umbrella wiring.
- [x] Index and formal lint; record exact results and remove owned scratch.

## Formal result and verification

`formal/GaloisForLFunctions/RHTower/WeilLogShiftSharpDualProfile.lean`:

- `finiteDimensionalC0Dual`: actual evaluation, valued in the normed dual and C₀.
- `finiteDimensionalC0Dual_apply`: evaluation identity.
- `finiteDimensionalC0SharpProfile`: norm of that evaluation functional.
- `finiteDimensionalC0SharpProfile_le_iff`: exact smallest nonnegative bound.
- `finiteDimensionalC0SharpProfile_eq_zero_iff`: exact common invisible locus.
- `norm_finiteDimensionalC0SharpProfile`: sharp profile norm equals operator norm.
- `finiteDimensionalC0_response_cost_escapes`: uniform amplitude escape.

`formal/GaloisForLFunctions/RHTower/WeilLogShiftSharpDualReceiver.lean`:

- `exists_weilLogShift_sharp_dual_receiver`: one normalization, dual-valued C₀
  receiver on the actual regular coefficient subspace, sharp scalar profile,
  invisible-locus classification, amplitude escape, and an explicit HasSum
  contract for the paired-kernel series.

Both leaves passed `lake --old env lean <leaf> -o <olean>` with no warnings.
All eight public declarations passed a separate /tmp `#print axioms` audit;
each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
Both direct umbrella imports occur once, and both oleans postdate their sources.
`scripts/formal_tools.py index` exited 0; a module-filtered local search returned
all eight declarations in the intended modules.

Final `scripts/formal_tools.py lint` exited 1, with precisely four unrelated
unreachable-module errors and no proof-debt errors:

- `RHTower.LaguerrePolyaDivideRealZero`
- `HTGeometry.LaguerrePolyaImaginaryAxisBounds`
- `HTGeometry.PaperHomogeneousGeneratorIdeal`
- `HTGeometry.QKrawtchoukCompanionTriangular`

No full build, umbrella build, external search, numerical experiment, or
heartbeat adjustment. Initial elaboration failures involved reducibility of
linear-map and C₀/BCF coercions; explicit `change` and `simpa only ... using!`
resolved them without altering the paper statement.

## Follow-up: exact response cost

The minimum-cost conjecture is now proved and formalized in
[weil-logshift-exact-response-cost.md](weil-logshift-exact-response-cost.md).
Positive sensitivity gives an attained least norm |r|/q(y); zero sensitivity
permits only response zero. The unconditional budget criterion is 0≤A and
|r|≤Aq(y), stated directly with HasSum for the actual normalized series.
The full corpus-research objective remains active.
