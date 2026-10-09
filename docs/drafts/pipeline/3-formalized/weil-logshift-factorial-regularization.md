# Finite factorial powers cannot regularize late columns

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Global lint findings are recorded below.

## Target

Retain one common native late-column threshold. For every column beyond it, every integer `m≥0`, and every real exponential rate `A`, prove
`exp(-A*n)*|C(k,n)| / (n!)^m → ∞`.
Prove the analogous statement for each fixed real-shift moment-response column, with its square-root normalization and kernel factor. Consequently the corresponding signed factorial-and-exponentially damped series are nonsummable. No bound `D*exp(A*n)*(n!)^m` can control the whole tail of any such column.

The parameters `m`, `A`, and the shift must follow the common threshold quantifier. Do not weaken this to a threshold depending on the proposed regularization.

## Corpus audit

- `research 'factorial Gevrey normalization column' --any --mode lexical --module WeilLogShift --no-refresh --json`: fts5, 18 matches, ten eligible, seven modules. Returned native growth, response, and normalization facts; no factorial or Gevrey column theorem.
- Exhaustive source search for `factorial`, `Gevrey`, and `gevrey` in all WeilLogShift leaves found no match.
- Installed Lean `Mathlib/Data/Nat/Factorial/Basic.lean:182` proves `Nat.factorial_le_pow`: `n!≤n^n`.
- Installed Lean `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:449` proves `Real.isLittleO_log_id_atTop`: `log =o[atTop] id`.
- The preceding increment proves `exists_weilLogShiftRecoveryCoefficientColumn_quadratic_exponential_lower` and `exists_weilLogShiftRecoveryMomentResponse_quadratic_exponential_lower`. Both leaves compiled; all six public theorems passed the exhaustive standard-axiom audit.
- Concrete mathlib casts, factorial powers, logarithm/exponential identities, and little-o extraction still need scratch API checks before implementation.

## Dependency-closed paper proof

1. For any fixed integer `m` and any `η>0`, eventually `(n!)^m≤exp(η*n²)`. Indeed `n!≤n^n`, so for `n≥1`, `(n!)^m≤exp(m*n*log n)`. If `m=0`, the assertion is immediate. If `m>0`, the local little-o theorem gives eventually `log n≤(η/m)*n`, and multiplication by `m*n≥0` proves the exponent bound. Factorials are positive, so every division below is legitimate.
2. Choose `η=1/4`. The native coefficient envelope `c*exp(n(n+1)/2)` then yields
   `exp(-A*n)*|C(k,n)|/(n!)^m ≥ c*exp(n²/4+(1/2-A)*n)` eventually.
   The exponent eventually exceeds `n`; therefore the normalized coefficients tend to infinity.
3. For a fixed shift `y`, the already verified response envelope is
   `(c_y/(n+1))*exp(n(n+1)/2-(2*pi+1)*n)` eventually.
   After both normalizations, it is at least
   `(c_y/(n+1))*exp(n²/4+(1/2-A-(2*pi+1))*n)` eventually.
   This exponent eventually exceeds `2*n`. Since `n+1≤exp(n)` by local `Real.add_one_le_exp`, the normalized response dominates `c_y*exp(n)` and tends to infinity.
4. A summable signed sequence must have norm tending to zero, contradicting steps 2–3. This proves signed nonsummability, not merely absence of an absolute majorant.
5. If a tail bound by `D*exp(A*n)*(n!)^m` existed, multiplying and dividing by the positive normalizing factors would bound the sequence from step 2 or 3 by `D`, contradicting its divergence to infinity. No positivity assumption on `D` is needed for the contradiction.

These are consequences of checked corpus statements and elementary inequalities. There is no numerical experiment, external asymptotic estimate, Stirling premise, or new analytic assumption.

## Boundaries and exposed questions

- Formal target quantifies natural factorial powers. A bridge to any pre-existing definition of real-order Gevrey classes must be separately audited; do not claim that library-level bridge already exists.
- Early columns, especially column zero, remain outside the proven native tail threshold.
- No matching upper quadratic exponent or sharp Gaussian threshold is established.
- Further possible consequence: at most one amplitude on a late impulse line could satisfy any finite factorial-power majorant, even if its order and rate vary with the amplitude. This requires a separate argument combining two proposed majorants and a local novelty audit; it is not part of the present proved result.

## Plan

Verify the local factorial and little-o APIs, formalize the subquadratic factorial bound, then prove coefficient and response normalization results and their nonsummability/majorant consequences. Compile new leaves sequentially, wire them into the umbrella, audit every public declaration, refresh index, run lint, and remove owned scratch files.

### Local API note

The same checked logarithm source also exports `Real.tendsto_pow_log_div_mul_add_atTop (a b : ℝ) (n : ℕ) (ha : a ≠ 0)`. At `a=1`, `b=0`, and `n=1`, this directly gives `log(x)/x → 0`. Composing with natural casts may be simpler than extracting bounds from the little-o API. Verify the exact specialization in scratch Lean before use. Source lines 439–450 were read during the preceding increment; avoid re-reading the whole file.

## Current log — 2026-10-09

- Fresh corpus query `factorial normalization exponential column` (`--any --mode lexical --module WeilLogShift --no-refresh`) returned 82 matches, 43 eligible, 26 modules. Native new quadratic bounds were found; no factorial-normalization result was returned.
- New leaf paths `WeilLogShiftFactorialEnvelope.lean` and `WeilLogShiftFactorialRegularization.lean` were absent before implementation.
- Scratch verification covers the direct log-ratio limit, factorial-power upper bound, `Real.exp_nat_mul`, and the exact residual-quadratic inequality.
- Implementation can avoid a separate `m=0` branch: use the positive comparison scale `η/(m+1)`, together with `log(n)≥0` for `n≥1`. This proves the same uniform eventual factorial bound for every natural order.
- Plan: one envelope/model leaf, then coefficient/response runaway, signed nonsummability, and exclusion of every eventual factorial-power/exponential majorant. The common native column threshold remains before all normalization parameters.

### Compiled implementation checkpoint

Both new leaves compile/export cleanly. Eight public theorems cover the general factorial envelope, the normalized quadratic model, coefficient and response runaway, both signed nonsummability results, and exclusion of every eventual finite factorial/exponential majorant. All normalization parameters follow the common native threshold. Both imports are wired uniquely into the umbrella. Exhaustive axiom audit is running; index and lint follow it.

A separate paper argument now strengthens the earlier exposed question to a precise exceptional-fibre law allowing the shift, order, rate, prefactor, and cutoff all to vary with amplitude. The actual native kernel comparison and affine difference identity were checked. See `docs/drafts/pipeline/3-formalized/weil-logshift-factorial-impulse-rigidity.md`.

## Final verification — 2026-10-09

Both leaves compiled/exported cleanly, one foreground process at a time, using `lake --old env lean <leaf> -o <olean>`. No full or umbrella build. Every one of the eight public theorems passed the scratch `#print axioms` audit with exactly `propext`, `Classical.choice`, and `Quot.sound`; no warnings/errors. Both umbrella imports are unique. Index refresh succeeded and all eight public rows were checked individually. No old API, analytic premise, or resource limit was changed.

Formalized all planned results: arbitrary-positive-quadratic factorial envelope, factorial-normalized quadratic model, coefficient and response runaway under every natural factorial power and real exponential rate, both signed nonsummability consequences, and exclusion of every eventual majorant with any real prefactor and any tail cutoff. The common native threshold precedes every normalization parameter and shift.

Latest formal lint exited 1 with one unrelated umbrella-reachability error:

- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular

Neither new leaf has a lint finding. Early columns and any real-order Gevrey library bridge remain outside the claim.

The next independent paper proof and novelty audit are recorded in `docs/drafts/pipeline/3-formalized/weil-logshift-factorial-impulse-rigidity.md`: finite-factorial majorant sequences form a class closed under subtraction and scalar multiplication; some-shift membership reduces to origin; the native impulse difference law then forces at most one exceptional amplitude even when shift/order/rate/prefactor/cutoff vary. Both leaves and all 13 public declarations are now compiled and kernel-audited there.
