# WL finite barycentric signed lag means

- **ID:** WL-BM-20260929
- **Stage:** 1-in-progress
- **Type:** THEOREM candidate
- **Source:** WL frontier; newly proved arithmetic ramp and complete trivial-zero convexity, and `mul_log_chord_defect_le_of_lower_bound`.
- **Statement:** For every finite probability distribution on integer nodes `n_i>=r>=2`, with integer barycenter `k=sum w_i n_i`, the actual lag obeys `sqrt(k)*a_k <= sum w_i sqrt(n_i)*a_(n_i) + sum w_i(n_i-k)^2/(2r)`. The literal signed mean gives a pointwise upper receiver with variance loss; no estimate on that mean is assumed in the theorem.

## Plan
1. [x] Search current corpus; distinguish existing global signed mean from this finite local receiver.
2. [x] Derive complete paper law from finite Jensen and exact barycenter variance.
3. [x] Verify finite Jensen APIs in scratch; formalize exact variance inequality and closed fixed-schedule RH characterization.
4. [ ] Audit novelty, source, axioms, wiring and lint; then seek an actual-prime bound on the signed mean.

## Paper proof
Choose an integer cutoff `N` above every node and the barycenter. On `[r,infinity)`, the corrected real extension
`H(x)=x(1+gamma)-log(2pi)+[x^2/(2r)-x log x]+S(x)+R_N(x)`
is convex: the bracket has second derivative `1/r-1/x>=0`, the full trivial-zero series `S` is convex, and every actual von Mangoldt ramp in `R_N` is convex. At each integer `j<=N`, `H(j)=sqrt(j)*a_j+j^2/(2r)`.

Finite Jensen yields
`sqrt(k)*a_k+k^2/(2r) <= sum w_i [sqrt(n_i)*a_(n_i)+n_i^2/(2r)]`.
The probability and barycenter identities give
`sum w_i n_i^2-k^2=sum w_i(n_i-k)^2`.
Rearrangement proves the statement. It retains the signed lag values and only charges the variance of the chosen nodes. Symmetric moving windows are a special case; their variance is on the squared-radius scale.

For a fixed schedule of such distributions at every k, suppose the variance is at most `C*r_k*sqrt(k)`. Dividing the point law by `sqrt(k)` shows that a uniform upper bound M on the normalized signed means bounds all actual integer lags by `M+C/2`. Conversely RH bounds the means: the elementary nonnegative sum `sum w_i*(sqrt(n_i)-sqrt(k))^2` gives `sum w_i*sqrt(n_i)<=sqrt(k)`, and the existing RH sharp lag ceiling applies termwise. This gives a closed characterization for every fixed variance-controlled mean schedule. The geometric probability/variance conditions are independent of lag values; the signed-mean ceiling remains the producer's open task.

## Prior-research audit
`SuzukiIntegerLagMeanCriterion` already identifies the global endpoint-corrected SP-E prefix mean with an exact RH boundary. Its weights, moving endpoint and archimedean corrections differ from a finite probability mean at its own barycenter. `ChebyshevLagWindow` and `ChebyshevShortWindowLowerBound` instead squeeze integrals of `psi(t)/t^2` between endpoint Chebyshev values; they do not give this signed lag-mean upper interpolation. Exact source statements were inspected.

Search artifacts: `/tmp/wl-local-average-search-20260929.json` (hybrid, complete retrieval, snapshot coverage); `/tmp/wl-finite-jensen-search-20260929.json` (lexical, pending at initialization). Exact `rg` over Lean files found no finite local signed `integerLag` mean theorem. Public comparison and universal novelty remain unverified. No claim of a new RH producer.

## Log
- 2026-09-29: C11 strengthens the initially proposed symmetric-window mean to arbitrary finite probability means. C10 constant-level invariance is still in its owned foreground scratch check; this card records the next dependency-closed paper candidate before code.
- 2026-09-29: First scratch check exposed four Lean issues: `convex_Ici` uses type parameter `β`; the affine constant must be added in `linear_combination`; unfold the corrected extension before rewriting its ramp; specialize `Finset.le_sup` to `id`. Repaired all four. Extended the candidate to a dependency-closed fixed-schedule signed-mean RH characterization with exact ceiling `M+C/2`. Expanded lexical search found prior individual prime-lag and global SP-E mean laws, no identical finite-variance law. Deep search was partial (coverage pending), with adjacent outgoing-quantile barycentric debt and the already-inspected SP-E mean; do not infer universal novelty from incomplete coverage. Primary Suzuki and Mittermeier checkpoint sources were compared; the latter concerns convex checkpoint minima in logarithmic scale, distinct from this natural-scale upper mean law.
- 2026-09-29: Next scratch pass proves the corrected real-extension convexity, integer identity, full finite-variance lag inequality, weighted square-root bound and RH-to-mean direction. Only the mean-to-lag proof fails because `mul_le_mul_iff_left₀` puts the positive factor on the right while the exact lag inequality puts it on the left. Read actual order API and switched to `mul_le_mul_iff_right₀`; final scratch check running. Earlier mechanical repairs also specialized `mul_inv_cancel₀` to `G₀`, used the actual forward orientation of `Finset.sum_div`, and aligned a multiline calc. No mathematical change or heartbeat increase.
- 2026-09-29: Complete scratch exited 0 with no warnings or output. New 201-line production leaf `formal/GaloisForLFunctions/RHTower/WeilLagBarycentricMean.lean` copies the exact verified proofs, removes only API-check examples and adds documentation. Own umbrella import wired; targeted artifact build running. Public declarations: `sqrt_integerLag_le_finite_mean_add_variance`, `normalizedBarycentricLagMean`, `BarycentricLagMeanScheme`, `integerLag_bddAbove_of_barycentricMeanScheme`, `barycentricLagMeanScheme_characterization`. All-public axiom and final direct-source audits remain pending. No signed-mean producer proved; active RH goal continues.
- 2026-09-29: Targeted build exited 0, 8829 jobs with unchanged dependencies replayed; new leaf reported 43 seconds, no own warnings. All five public declarations passed `/tmp/wl-barycentric-mean-axioms.lean`: exactly `[propext, Classical.choice, Quot.sound]`. Closed capstone signature and axiom output captured at `/tmp/wl-barycentric-mean-axioms-final.txt`. Final direct source audit now running. No added mathematical axioms, computation oracle, incomplete proof or heartbeat override.
- 2026-09-29: Final `lake --old env lean GaloisForLFunctions/RHTower/WeilLagBarycentricMean.lean` exited 0 with empty output (`/tmp/wl-barycentric-mean-source-final.txt`). Own leaf and umbrella whitespace check passed. WL report updated to the actual finite signed mean law and its fixed-schedule receiver. Index/lint refresh pending; prior global lint errors remain out of scope. Active goal remains active; no uniform actual signed-mean estimate or unconditional RH proof/falsification claimed.
- 2026-09-29: Index refresh exited 0 and generated API/gaps/overview (`/tmp/wl-barycentric-mean-index-final.txt`). Authoritative global lint exited 1 with 14 unrelated unreachable modules (`/tmp/wl-barycentric-mean-lint-final.txt`), no owned module error or forbidden proof declaration. Thus own registration/audits are complete, global gate remains failing outside scope; universal novelty and the overall RH goal remain unresolved. Do not repair or wire unrelated modules.
