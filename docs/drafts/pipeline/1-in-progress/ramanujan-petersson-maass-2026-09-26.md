# Ramanujan-Petersson for level-one Hecke-Maass forms

- **ID:** RP-MAASS-20260926
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** User's exact target; `docs/meta/scientific-method.md` and `docs/meta/stroke-of-genius-method.md`.
- **Statement:** Every normalized level-one Hecke-Maass cusp form has unit-modulus Satake parameters at every prime.
- **Status:** No unconditional proof or falsification established.

## Acceptance

The final theorem must concern actual Maass cusp forms and their normalized Hecke eigenvalues. No added mathematical axioms, unproved analytic premises, computational certificates, or increased heartbeat limits. Check Lean in foreground, one process, using scratch files first and a leaf-module build only for final audit. A scalar parameter example is not a Maass counterexample.

## Work plan

- [x] Read session instructions, relevant memories, formal overview, and both research methods.
- [x] Search current corpus and inspect initial Satake/automorphic candidates.
- [x] Test the proposed Hecke-power route through source-checked conjecture/failure/pivot cycles.
- [x] Formalize the exact decay obstruction and positive paired-kernel survivor; audit source meaning and axioms.
- [x] Record precise remaining obstacle and verification status.
- [ ] Prove the missing actual-Hecke-power estimate, or produce a genuine Maass counterexample.

`update_plan` is not exposed in this session; this checklist holds task state.

## Frozen target and route questions

The user-supplied conjecture is fixed. Candidate sufficient estimates are [BRIDGE] claims, not replacements for it.

What would a scientist do here? Inspect exact assumptions, try to falsify each sufficient estimate, and identify where cusp automorphy enters. For every result: what does it mean for the whole route? Is the next task addressing individual finite-prime temperedness, or only nearby formal infrastructure?

First route to inspect: weak growth of high powers of an actual Hecke operator, followed by extraction of individual cusp eigenvalues. Current primary-source candidate: Unterberger, arXiv:2001.10956v16 (2026-02-12), especially Sections 7-8. Its abstract claims the target; this is evidence of a proposed proof, not a verified theorem.

Facts and no-gos are kept separately in `ramanujan-petersson-maass-2026-09-26-facts.md`.

## Direct attack: Hecke powers through phase-space kernels

### Candidate A: use existing Satake or bounded-operator results

Rejected as a completed proof. The retained Satake statements require unit modulus. The actual rational Maass trace has a bounded quotient-L2 action, but inspected estimates retain cover cardinalities. Deep method search finds spectral-radius arguments whose input is a power bound; it does not supply that bound for the actual Hecke operator. Whole-route consequence: the analytic estimate, rather than the final root-taking argument, is the task.

### Candidate B: rapid stationary-phase suppression

The proposed inference that a quadratic amplitude zero permits arbitrarily many integrations by parts fails. Define

`J(t) = integral_0^infinity x^2 exp(-(1-i*t)*x^2) dx`.

The existing Gaussian moment recurrence gives `J(t)^2*(1-i*t)^3 = pi/16`. Taking squared complex norms gives the exact positive survivor

`norm(J(t))^4*(1+t^2)^3 = pi^2/256`.

Consequently `q^4*norm(J(q^2))` is unbounded even on `q=2^n`. Indeed, if it were at most C, then for q>=1 the displayed identity and `1+q^4 <= 2*q^4` imply `(pi^2/256)*q^4 <= 8*C^4`. Powers of two are unbounded, a contradiction. This is a symbolic proof, with no numerical experiment.

The full-line Gaussian test is twice J by evenness. Finite vanishing order at a stationary point cannot justify rapid decay for general Schwartz amplitudes. This rejects that intermediate inference, not the final Ramanujan assertion or every possible proof through distributions. Lean: `HTGeometry/GaussianStationaryDecay.lean`; scratch and direct source checks passed with default heartbeats. Final build audit recorded below when complete.

### Candidate C: repair the kernel derivative before estimating

Set `L = y*d/dx + x*d/dy` and `K(a,b,x,y)=exp(i*(a*(x^2-y^2)+b*x))`. Since `L(x^2-y^2)=0`,

`L K = i*b*y*K`,

`L^2 K = (i*b*x-b^2*y^2)*K`.

Applying the first multiplier twice alone drops `i*b*x*K`. This is a product-rule error in the unpaired-kernel calculation; no automorphic hypothesis removes it. The transformation from phase-space Euler derivatives to this kernel vector field is a paper calculation here, not an installed Lean theorem about distributions.

**Positive survivor:** pairing b and -b gives

`L^2 K(a,b) + L^2 K(a,-b)`

`= -2 exp(i*a*(x^2-y^2)) * (b*x*sin(b*x) + b^2*y^2*cos(b*x))`.

For real a,b,x,y, its norm is at most `2*b^2*(x^2+y^2)`, by `abs(sin t)<=abs(t)` and `abs(cos t)<=1`. Thus opposite-phase pairing restores a quadratic factor in b, including the missing term. Lean: `HTGeometry/QuadraticPhaseTransport.lean`. The correction does not itself kill the whole route.

### Remaining hard step after the repair

For the scaled function `u_q(x)=q*u(q*x)`, its Fourier profile is `hat u(xi/q)`. The unweighted L1 norm scales by q and its second absolute moment by q^3. The corrected paired estimate uses products of these quantities and therefore gives a q^4 loss in this representation. A unit-modulus chirp preserves these absolute norms; it supplies no missing inverse power of q. This is a limitation of this estimate, not a proof that the actual oscillatory lattice sum grows as q^4.

To finish the route, one must bound the actual paired primitive-lattice sum uniformly after the allowed rational shear averages and dilation, or obtain another genuine subexponential bound for actual Hecke powers. No such estimate has been proved here. Neither new Lean module constructs a Maass form, excludes a non-tempered Maass eigenvalue, or improves a known exponent.

## Sources and coverage

- [Unterberger, v16](https://arxiv.org/html/2001.10956v16), Sections 7-8: proposed phase-space route inspected. Local failures above do not establish a counterexample to its final theorem.
- [Huang-Zhao, 2026](https://arxiv.org/abs/2605.09807): least-prime and density results concern weaker conclusions than the target.
- [Newton-Thorne, 2026](https://annals.math.princeton.edu/2026/203-1/p04): regular-weight Hilbert modular input.
- Searches include whole-index hybrid and deep queries for Maass/Satake, Hecke bounds, power-growth methods, Gaussian stationary phase, and Euler/Weyl commutators. All returned candidate/argument statements were screened; unrelated or conditional statements were not promoted. Some requests returned partial results, with source-only compiler status and incomplete semantic-coverage reporting. This is not an exhaustive verification of all corpus proofs.
- Temporary search records: `/tmp/rp_maass_deep_20260926.json`, `/tmp/rp_power_methods_20260926.json`, `/tmp/rp_hecke_bound_20260926.json`, `/tmp/rp_gaussian_methods_20260926.json`, `/tmp/rp_stationary_decay_20260926.json`, `/tmp/rp_euler_kernel_methods_20260926.json`, `/tmp/rp_paired_uniformity_20260926.json`.

## Direct-source continuation

### Candidate D: termwise decay on dyadic rational samples

[BRIDGE] Candidate under attack: a termwise decay estimate can replace cancellation in a dyadic rational average. Let `q=4*2^n`, `b=q/2+1`, and `z_n=b/q+z/q^2`. The integral matrix

`gamma_n = [[1-2*2^n, 2^n], [-2, 1]]`

has determinant one and sends `z_n` to `-1/2+(z/4)/(1+z/q)`, tending to `z/4-1/2`. Hence a continuous level-one automorphic function has values on this boundary-approaching sequence tending to its interior value at `z/4-1/2`. For a genuine nonzero Maass form choose `z=4*w+2` with `f(w) != 0`; then `q*norm(f(z_n))` is unbounded.

Paper proof is dependency-closed by matrix algebra, modular invariance, continuity, and geometric divergence. Scratch verification passed; installed module: `RHTower/MaassDyadicHorocycleReturn.lean`. The positive survivor is the exact modular-return limit for actual Maass forms. Lean also proves `z_n=(z+B)/Q` with `0<=B<Q` and `Q=2^(2*n+4)`, so these are literal prime-power residue samples.

This is NOT a bound or counterexample for a normalized Hecke eigenvalue. The correspondence to the distributional generator in the proposed phase-space proof is not supplied by this test. Whole-route consequence: cusp decay cannot justify uniform inverse-scale decay of individual boundary-approaching rational samples; arithmetic averaging must be retained. The proof uses continuity, automorphy and nonvanishing, not the Laplace or Hecke eigen-equations. Therefore it diagnoses a failed estimate without excluding non-tempered forms.

### Candidate E: improve the actual finite-cover operator estimate

[BRIDGE] The existing norm bound on `rationalHeckeConjugateFiberTraceLp` costs the fibre degree `d_2`. Corpus theorems identify its adjoint with a pullback whose norm scales exactly by `sqrt(d_2)`. Since adjoint preserves operator norm, the trace bound improves to `sqrt(d_2)`. Composing with the principal-side pullback yields the bound `sqrt(d_1)*sqrt(d_2)`, where `d_1,d_2` are the two actual common-cover degrees. The bound transfers to the identified trace of every genuine Maass source vector.

Scratch verification passed; installed module: `RHTower/MaassRationalHeckeNormBounds.lean`. Whole-route consequence: this removes an avoidable degree loss in the packaged correspondence estimate, but equal degrees still cost `d`, not `2*sqrt(p)`. No cusp-specific cancellation has entered this proof, so it is not a Ramanujan bound or an improvement to a previously known spectral exponent.

### Next discriminating step

Do not add further generic boundedness or scalar Satake interfaces. The missing estimate must use the interaction between cuspidality and the two different common-cover pullback images, or control the full arithmetic average without taking absolute values termwise. A uniform gain for either pullback alone cannot follow from its already exact square-root norm-scaling law. The two completed tests neither prove nor falsify that joint arithmetic estimate.

## Verification and implementation

- Scratch and direct-source `lake env lean` checks passed. Final leaf builds passed for `GaloisForLFunctions.HTGeometry.GaussianStationaryDecay` and `GaloisForLFunctions.HTGeometry.QuadraticPhaseTransport`; no umbrella or full build was run.
- Imported-module audit `/tmp/rp_final_axiom_audit_20260926.lean` passed. All nine new theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom mathematical axiom.
- Kernel proof optimization removed the broad `Mathlib.Tactic` import and replaced its terminal `nlinarith` with explicit multiplication monotonicity. Leaf build reported 5.9s after optimization versus 19s before; these are individual build observations, not controlled benchmarks. Default heartbeat/recursion limits were unchanged.
- Both new modules are imported by `HTGeometry.lean`. Scoped `git diff --check` passed; source scan found no forbidden proof holes or resource-limit overrides.
- `scripts/formal_tools.py index` completed. `scripts/formal_tools.py lint --check-generated` exited 1: unrelated concurrent modules `ThetaHauptmodulLogTranslation`, `ThetaPowerFourierExpansion`, `ThetaPowerHorocycleMass`, and `ThetaPowerModularTwoSidedBound` were not reachable from `RHTower`; `LEAN_API.md` and `LEAN_OVERVIEW.md` were reported stale. No global clean-lint claim is made.
- Final uniformity deep search returned partial results after 60s. Its candidate and argument statements supplied no usable bound on the actual paired primitive-lattice/shear sum. Generic uniform boundedness still requires the missing pointwise bounds.

The target remains unproved and unfalsified. The next mathematical attack must establish actual uniform cancellation or actual Hecke-power growth control, not further scalar Satake algebra.

### Direct-source audit

- `lake env lean /tmp/rp_dyadic_return_20260926.lean` and `lake env lean /tmp/rp_hecke_norm_20260926.lean` passed without heartbeat or recursion-limit overrides.
- Final leaf builds passed: `GaloisForLFunctions.RHTower.MaassDyadicHorocycleReturn` (4.8s) and `GaloisForLFunctions.RHTower.MaassRationalHeckeNormBounds` (39s). The latter replayed two existing unused-section-variable warnings in `SelbergMaassPrincipalTrace`, not warnings from the new module. No full or umbrella build was run.
- Imported-module audit `/tmp/rp_continuation_axiom_audit_20260926.lean` passed for all eleven new theorems. Their axiom sets are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
- Both modules are wired into `RHTower.lean`; scoped whitespace checks and forbidden-token scan passed. All owned Lean sessions exited.
- Index regeneration completed. The latest `lint --check-generated` still exits 1, now naming nine unrelated unwired modules and three stale generated files. Full captured diagnostics: `/tmp/rp_continuation_lint_20260926.log`. No global clean-lint claim is made.
- Current search evidence: `/tmp/rp_actual_hecke_20260926b.json`, `/tmp/rp_tempered_methods_20260926b.json`, `/tmp/rp_horocycle_method_20260926b.json`, `/tmp/rp_adjoint_bound_20260926b.json`. Returned candidates were screened; three requests were partial. Proofs rely on checked source declarations, not proposed ingredient sets.

## Cusp-cancellation continuation

### Candidate F: annihilate the residue branch by cuspidality

[BRIDGE, under test] Could the finite residue sum in the normalized Hecke equation vanish because the source is cuspidal? The actual Fourier projector retains an entire residue class, not only frequency zero (`SelbergMaassCharacterFourier.coefficient_upperCharacter`). The available `deck_average_zero` further assumes a Laplace eigenvalue in `(0,1/4)`; it is not an all-Maass cancellation theorem.

Direct cusp-specific attack: prove that for a nonzero level-one Maass cusp form, any real dilation `a>1`, and any complex scalar `c`, the identity `f(a*z)=c*f(z)` cannot hold at every point. Modular inversion changes dilation into inverse dilation. Thus such an identity forces `f(a^2*z)=f(z)`. Iteration contradicts actual cusp decay as `a^(2*n)*Im(z)` tends to infinity. This uses cuspidality, not just boundedness or a generic Hilbert-space norm.

Positive survivor proved in scratch: the exact dilation/inversion identity and the resulting absence of a scalar dilation eigenfunction. The proof actually needs only inversion invariance and cusp decay. Its specialization takes an actual `MaassCuspEigenform`, not an artificial scalar model. The direct corollary uses the existing `_root_.RHTower.heckeOp`: whenever `T_p f = mu*f` and `p>1`, some point has nonzero residue sum. If the residue sum vanished everywhere, the exact eigen-equation would give `f(p*z)=sqrt(p)*mu*f(z)`, contradicting dilation rigidity.

Installed as `RHTower/MaassDilationRigidity.lean`. This does not bound `mu`, prove a uniform correlation gap, or establish Ramanujan. The failure eliminated is exact branch annihilation, not the full arithmetic-cancellation route. Scratch failures were rewrite orientation and coercion mismatches, repaired with explicit identities; no resource limits were raised.

### Candidate G: infer spectral gain from Fourier energy conservation

Attempt: combine the full character Parseval decomposition, inversion transfer, and Cauchy-Schwarz to control the selected arithmetic channel. Source inspection gives the exact equality

`sum_r norm(inversionTransfer r s v)^2 = norm(characterProjection s v)^2`.

This preserves total column energy. It does not bound a specified channel by the smaller proportion required for Ramanujan. The actual coefficient version has the same limitation. Cuspidal large-height decay does not resolve it: the residue branch evaluates at height `y/p`, and its zero residue channel retains nonzero frequencies divisible by `p`.

Outcome: no source-specific quantitative gain proved. Nonvanishing from Candidate F cannot be promoted to a uniform bound. Whole-route bottleneck remains control of the full arithmetic average, or an equivalent actual Hecke-power estimate. No new eigenvalue bound or counterexample was obtained in this continuation; the auxiliary rigidity theorem is not a substitute for that missing estimate.

### Alternative amplification checks

The retained Sarnak-Xue pretrace theorem estimates a geometric ball integral of `abs(u)`, not prime-power Hecke moments. Using it here still needs a new arithmetic counting/amplification estimate. The symmetric-power files supply character identities and a degree-family criterion, while the prior global-lift card records the missing compatible general-Maass lifts. Trying tensor unitarity as the producer meets the existing exact `MaassTensorSquareMultiplicity` obstruction: opposite compact weights give arbitrarily many independent diagonal zero-weight vectors, so a finite symmetric-power packet still needs a selection/lift construction. These facts do not retire either global route.

Search records: `/tmp/rp_cusp_average_20260926c.json`, `/tmp/rp_hecke_amplification_20260926c.json`, `/tmp/rp_dilation_rigidity_20260926c.json`, and `/tmp/rp_cusp_correlation_20260926c.json`. All four deep searches returned partial results. Retained candidate statements were inspected in source; proposed ingredient sets were not treated as proofs. No absence-of-proof claim about the whole corpus follows.

### Dependency optimization and audit

The initial targeted build imported the entire Eisenstein analysis merely to use the generic `heckeOp` definition. It reached over 10,900 build jobs and began rebuilding changed upstream dependencies. The owned build was interrupted (exit 130), and its owned Lean child was confirmed gone before starting another Lean process.

Moved only the unchanged generic definition to `RHTower/HeckeOperatorBasic.lean`, preserving `_root_.RHTower.heckeOp`, its type, formula, and reducibility. `EisensteinHeckeOperator` now imports that definition; its proofs are unchanged. `MaassDilationRigidity` imports the lightweight module. All repository references were located; GL3's separately namespaced `heckeOp` is unrelated and untouched. Both new modules are wired into the umbrella.

Minimal-dependency scratch checks passed. The final `lake build GaloisForLFunctions.RHTower.MaassDilationRigidity` succeeded with 2,783 jobs; both new leaves reported 11s. These job counts document dependency reduction, not a controlled wall-clock benchmark. No heartbeat or recursion-limit override, proof hole, additional mathematical axiom, or numerical evaluation command was introduced.

The imported audit `/tmp/rp_dilation_axioms_20260926c.lean` passed for all five new theorems and the coordinate definition. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. A direct check of the existing Eisenstein source reported a missing upstream olean for `ThetaCuspHawkingMassDilationOrderBlindnessNoGo`, whose earlier owned compilation had been interrupted. A targeted build of `EisensteinHeckeOperator` is therefore needed to finish compatibility validation; no full or umbrella build is requested.
