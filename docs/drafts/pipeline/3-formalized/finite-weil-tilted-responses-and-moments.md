# Finite Weil tilted quadratic responses and all mixed moments

Status: local Lean evidence checked; dependency-closed paper mechanism identified; formalization in progress.

## Target

Fix a subcritical base quadratic `Q` with diagonal coefficient `s<2`. For every quadratic perturbation `R` with diagonal coefficient `rho`, classify `E_Q exp(R)` along all actual finite depth sequences `2*(r+1)^2+t r`: limit `sqrt((2-s)/(2-s-rho))` for `s+rho<2`, divergence otherwise, and boundedness exactly in the subcritical half-space. Prove an unconditional extended-integral formula. Then prove convergence of every mixed moment `E_Q[X^p*Y^q]` to its explicit diagonal Gaussian moment at variance `1/(4-2*s)`, including limiting means and the full covariance matrix.

## Local evidence and paper proof

All mathematical sources are local Lean. `WeilLogShiftJointQuadraticCriticality` classifies the original joint quadratic partitions; `WeilLogShiftQuadraticTiltLaw` constructs actual normalized tilts and proves the ratio formula. Mathlib `integral_exp_tilted` makes `E_Q exp(R)=Z(Q+R)/Z(Q)` exact at every finite level. The denominator tends to a positive constant, so both finite limits and divergence transfer. The survivor is the complete remaining exponential region `s+rho<2`.

Choose a positive radial perturbation `eta=(2-s)/4`; its diagonal coefficient is `2*eta`, leaving a strict subcritical margin. Its expectations are uniformly bounded by the response theorem. The local `HTGeometry.abs_pow_le_const_mul_exp` bounds `(x^p*y^q)^2` by a constant times `exp(eta*(x^2+y^2))`, giving uniform second moments of every mixed monomial. Actual tilted laws integrate every real observable because their original support is finite. The explicit Gaussian target integrates every power, by local `memLp_id_gaussianReal`. `HTGeometry.WeakContinuousMomentTransfer` then upgrades the already-proved weak tilted-law limit to every mixed-moment limit. Gaussian mean and variance identities identify the limiting covariance matrix.

## Work and verification

1. Exact quadratic response identity and integrability for every actual tilted observable.
2. Complete response half-space: finite limit, divergence, extended integral, boundedness classification.
3. Polynomial exponential envelope and Gaussian power integrability; uniform mixed-square bounds.
4. All mixed moments and explicit means/covariances.
5. Native leaf builds, exact umbrella wiring, final native axiom audit, dependency freshness and incoming imports, full declaration indexing, and authoritative global lint.

No web, papers, numerical experiments, subagents, full builds, heartbeat increases, commits or pushes. Artifacts use `/tmp/hgt-weil-tilt-response-*`; leaf logs `/tmp/hgt-<Leaf>.log`.

## Native checkpoint

Five leaves are authored and wired provisionally: `HTGeometry.QuadraticExponentialMoments`, `RHTower.WeilLogShiftQuadraticTiltResponse`, `RHTower.WeilLogShiftQuadraticTiltResponseLimit`, `RHTower.WeilLogShiftQuadraticTiltMomentBounds`, and `RHTower.WeilLogShiftQuadraticTiltMoments`. The exact response/finite-integrability leaf compiles cleanly. Its initial `change` under `Integrable` hit the default unification budget; explicit probability-coercion simplification and measure/function arguments fixed it without increasing heartbeats. The response-limit leaf is under verification; the remaining three leaves await builds. The elementary square-root ratio lemma needs only the combined coefficient below two, not a separate base-coefficient hypothesis; its stronger algebraic statement is proved by the same division identity, while the probabilistic response still requires a subcritical base tilt.

Later checkpoint: `WeilLogShiftQuadraticTiltResponseLimit` and `QuadraticExponentialMoments` now compile with empty logs. The response proof transports its partition ratio pointwise with `Tendsto.congr`; direct simplification did not eta-expand function division. The polynomial bound rewrites the absolute value using an explicit nonnegativity fact. `WeilLogShiftQuadraticTiltMomentBounds` is being rechecked after adding beta reduction before its pointwise quadratic rewrite (owned native session `27272`; last observed child PID `24145`, empty log). Revalidate the handle/process before acting; do not restart merely because an observation expires. The final `WeilLogShiftQuadraticTiltMoments` leaf has not yet been built.

## Final closure — 2026-10-11

Status: formalized. Mathematical sources restricted to the local Lean corpus; no web or external papers.

All five new leaves compile natively with empty logs. The final scratch audit checks all 21 theorems and 25 API declarations; only `propext`, `Classical.choice`, and `Quot.sound` occur. Metadata audit verifies 11 direct dependency edges and all nine incoming imports, with no issues.

For base diagonal coefficient `s = a + 2*b + d < 2` and combined coefficient `S`, the actual finite tilted exponential response converges to `sqrt ((2-s)/(2-S))` for `S < 2`, and diverges to positive infinity for `S >= 2`. The exact boundedness criterion is `S < 2`. Every mixed moment converges to its centered Gaussian diagonal moment, with variance `1/(4-2*s)`; both coordinate means vanish and every actual covariance entry converges to this variance. These positive results include indefinite forms and every natural mixed-moment order.

All 21 declarations are present in the local index (9 response, 8 moment, 4 generic declarations). The index validator reports two manually reviewed false positives: the word “remaining” in module comments describing the diagonal/radial exponential margin. Neither is an unfinished proof. The existing global lint run reports seven errors outside these five leaves; no owned leaf is flagged.

Final proof correction: rewrite the NNReal variance coercion explicitly, then use ordinary simplification for the four `Fin 2` coordinate cases. No heartbeat increase or full build.

Artifacts: `/tmp/hgt-weil-tilt-response-metadata.py`, `/tmp/hgt-weil-tilt-response-final-audit.lean`, `/tmp/hgt-weil-tilt-response-final-audit.log`, `/tmp/hgt-weil-tilt-response-verify-audit.py`, the three `/tmp/hgt-weil-tilt-response-*-index.json` files, and `/tmp/hgt-weil-tilt-response-lint.log`.
