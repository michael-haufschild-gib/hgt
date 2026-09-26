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

The imported audit `/tmp/rp_dilation_axioms_20260926c.lean` passed for all five new theorems and the coordinate definition. Each uses only `propext`, `Classical.choice`, and `Quot.sound`.

A direct check of the existing Eisenstein source initially reported a missing upstream olean for `ThetaCuspHawkingMassDilationOrderBlindnessNoGo`. The ensuing named-module Lake refresh expanded through many unrelated stale transitive dependencies. It was stopped after allowing its active compiler child to finish; both owned processes were confirmed gone. This refresh did not complete and is not reported as a passed audit.

The changed `EisensteinHeckeOperator.lean` was then successfully checked with `lake env lean`, emitting only its needed `.olean` and `.ilean` against the cached dependencies. No trace metadata was edited, no resource limits were changed, and no full or umbrella build was run. The new mathematical leaf's final Lake audit had already passed independently.

The combined-import regression `/tmp/rp_hecke_compatibility_20260926c.lean` passed with `lake env lean`: the original operator formula holds by `rfl`, six existing public operator lemmas remain available, and `heckeOp` has only the standard logical axiom trio. The unchanged direct consumer `EisensteinHeckeMaassSelberg.lean` also passed `lake env lean` with no diagnostics. These checks cover the relocated definition's actual call sites, not merely its isolated new import.

Index regeneration completed, updating `LEAN_API.md`, `LEAN_GAPS.md`, `LEAN_OVERVIEW.md`, and six changed search-index entries. Captured output: `/tmp/rp_dilation_index_20260926c.log`.

Final `scripts/formal_tools.py lint --check-generated` exited 1. Its only errors name two unrelated modules unreachable from the `RHTower` umbrella: `ShiftedDirichletPolynomialUniqueness` and `ShiftedDirichletTarget`. It reported no stale generated files or forbidden declarations. Large-file warnings concern existing modules. Full diagnostics: `/tmp/rp_dilation_lint_20260926c.log`. Scoped whitespace checks passed. All owned compiler, index, and lint sessions exited; the canceled broad refresh is not counted as successful verification.

Whole-route assessment: this continuation produced a cusp-specific rigidity theorem and refuted an exact-cancellation shortcut, but did not improve a normalized Hecke eigenvalue bound. The next discriminating target remains an estimate for the complete arithmetic average or actual Hecke powers. More nonvanishing, generic Hilbert bounds, or conditional Satake algebra cannot supply that estimate.

## Full-average quantitative attack

Previous turn classification: progress, from installed kernel-checked rigidity and verified dependency reduction; not progress on a normalized eigenvalue exponent. Frozen capstone remains unchanged.

Candidate H [BRIDGE, hostile test]: can periodicity, zero period mean, and arbitrarily rapid large-height decay force spectral radius at most two for the complete normalized Hecke operator? The inspected Eisenstein `heckeOp_tail` identity suggests a falsifier: its actual Fourier-Bessel tail at a positive real parameter has eigenvalue `p^u+p^(-u)`, not a freely assigned scalar. Test nonvanishing using positivity of real-order Bessel K and divisor coefficients; retain the full residue average. This is a test of a proposed sufficient estimate without modular inversion, not a proposed Maass counterexample. Positive survivor to audit: the exact nonzero, rapidly decaying, mean-zero Hecke eigenfamily and its supercritical spectrum.

Two preceding attempts did not produce the needed bound. `SarnakXueCounting.card_le` counts determinant-one congruence matrices; it does not count the determinant-prime-power correspondence. `KloostermanZeta` proves absolute convergence for sigma greater than 3/4, and `SelbergPeterssonKloosterman` supplies a Poincare-pairing formula, not an individual finite-place coefficient bound. The inspected global collision envelope still charges response energies; no requisite cancellation follows by dropping these factors. These are applicability failures, not impossibility theorems for either route.

Discriminating question: where must an eventual full-average estimate use global modular invariance in addition to cusp Fourier decay? If Candidate H fails, do not weaken Ramanujan or formalize another scalar-only criterion; identify the exact modular defect of the counterfamily and return to actual automorphic sources.

### Candidate H outcome and positive survivor

The proposed sufficient conditions are false. Scratch-checked witness:

`F_u(x,y) = sum_(n>=1) n^u (sum_(d|n) d^(-2u)) exp(2*pi*i*n*x) sqrt(y) K_u(2*pi*n*y)`.

For every real `u`, this is nonzero (strictly positive real part at `x=0,y>0`), one-periodic, zero-mean on each positive-height period, and uniformly exponentially decaying as height tends to infinity. The latter gives the actual `UpperHalfPlane.IsZeroAtImInfty` predicate, not only decay along a fixed vertical line. The local positive Laplace equation is `-y^2*(F_xx+F_yy)=(1/4-u^2)*F`. At every prime, the complete existing `heckeOp` satisfies `T_p F_u=(p^u+p^(-u))*F_u`.

For `u>0`, the real eigenvalue exceeds two. Exact iteration gives `T_p^k F_u=mu_p^k F_u`; for every positive `r<mu_p`, `norm(T_p^k F_u(0,1))/r^k` tends to infinity. The closed existential theorem specializes `u=1/4`, giving local Laplace eigenvalue `3/16`, uniform infinity-cusp decay, rapid fixed-line decay under every complex power weight, and supercritical full Hecke growth at every prime. This is a function-level countermodel, not a freely assigned Satake scalar.

Installed as `RHTower/EisensteinTailSpectrum.lean`, with an umbrella import. All scratch checks pass at default resource limits. One uniform-decay proof initially hit 200,000 heartbeats through definitional unfolding; an explicit uniform-bound lemma and typed eventual inequality removed that failure. No heartbeat/recursion setting was raised.

The separate `symmetric_tail_inversion_defect` theorem gives, for the two-sign tail and `Re(u)>1/2`, `tail(S*z)-tail(z)=constant(z.im)-constant((S*z).im)`. Its parameter sector and two-sign source differ from the closed one-sign `u=1/4` witness; it is not an audited inversion-defect formula for that witness. No modular-invariance theorem or actual Maass-source identification is supplied for the witness. Consequently this does not falsify Ramanujan, improve an eigenvalue exponent, or disprove a bound restricted to actual automorphic cusp forms.

Whole-route consequence: the local PDE, cusp decay, zero Fourier mean, and exact arithmetic eigen-equations do not by themselves yield spectral radius two. The missing argument must use the global automorphic constraints quantitatively. Candidate H is retired as a sufficient-condition route, with its exact nonzero eigenfamily as the positive survivor. The full automorphic cancellation route remains open here; further variants of this countermodel are not the next target.

Search evidence: `/tmp/rp_power_amplification_20260926d.json` reported complete retrieval with predominantly source-only compiler evidence; `/tmp/rp_modulus_cancellation_20260926d.json`, `/tmp/rp_tail_countermodel_20260926d.json`, and `/tmp/rp_inversion_boundary_20260926d.json` were partial. Candidate statements and necessary source proofs were inspected. Retrieval completeness is not a kernel audit or proof of absence elsewhere in the corpus.

### Full-average audit

- Final targeted `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.EisensteinTailSpectrum` passed (12,484 dependency jobs; new leaf 5.5s). Stale transitive dependencies were rebuilt serially; no full or umbrella build was run. Log: `/tmp/rp_tail_spectrum_build_20260926d.log`.
- `lake env lean /tmp/rp_tail_axioms_20260926d.lean` passed against installed oleans. All fourteen public theorem axiom sets are exactly `propext`, `Classical.choice`, and `Quot.sound`. The printed existential statement has no binders or unproved hypotheses. Its conclusion is the weakened-class countermodel, not the frozen Maass capstone.
- Source scan found no proof holes, custom mathematical axioms, numerical evaluation commands, or heartbeat/recursion overrides. Whitespace audit found one extra EOF blank line in the new file; removing it left the proof unchanged. The exact final source then passed the same named-module Lake build using cached dependencies (leaf reported 45s). Both timings are individual observations, not a benchmark. Final build log: `/tmp/rp_tail_spectrum_final_build_20260926d.log`.
- Initial index regeneration completed. The first global lint reported two unrelated unwired modules (`CircleHolomorphicPhaseSeamContraction`, `ThetaPowerSmoothDirichletBounds`) and stale generated API/overview files. Index and lint were repeated after the final whitespace edit; final results follow below.
- Final index regeneration completed. Final `scripts/formal_tools.py lint --check-generated` exited 1 with exactly two errors: unrelated `CircleHolomorphicPhaseSeamContraction` and `ThetaPowerErrorCesaroMeanSquare` are unreachable from the `RHTower` umbrella. No stale generated files or forbidden declarations were reported. Log: `/tmp/rp_tail_final_lint_20260926d.log`. This task's module is wired. All owned search, compiler, build, index, and lint sessions exited; old owned compiler/build PIDs were confirmed absent. No global clean-lint claim is made.

## Actual-source variance attack

### Candidate I: obtain the missing gain from finite-fibre variance

[BRIDGE, under test] Write A for principal pullback, B for conjugate pullback, T=B* for finite trace, and d_1,d_2 for their cover degrees. Existing exact identities give norm(Af)^2=d_1*norm(f)^2, norm(Bh)^2=d_2*norm(h)^2, and inner(u,BTu)=norm(Tu)^2. Expanding the squared norm, without estimates or division, predicts

`norm(d_2*Af - B(T(Af)))^2 + d_2*norm(T(Af))^2 = d_2^2*d_1*norm(f)^2`.

The conjectured saving is a lower bound for the first term, not its mere nonnegativity. In equal-degree notation d=p+1, the desired unnormalized bound 2*sqrt(p) would require that term to be at least `d*(p-1)^2*norm(f)^2`. This last specialization is a paper target, not an established identification of the corpus correspondence with the classical normalized Hecke operator.

Scientific test: verify the exact decomposition on actual Maass source vectors, then test existing cusp/deck identities for this quantitative lower bound. Do not treat the decomposition, a strict positive defect, or a rephrased inequality as an eigenvalue improvement. The general variance route is not retired merely because a tested sufficient estimate fails.

Source audit: `Gamma0MaassHeckeOperator.heckeH_maass` preserves automorphy, the Laplace equation, and cusp decay but states no norm saving. `SelbergMaassDeckAverage.deck_average_zero` is restricted to exceptional Laplace eigenvalues. The two `Arithmetic*Temperedness` modules inspected concern Euler--Gamma/Xi shell budgets, not Maass Hecke operators. New deep-search records: `/tmp/rp_global_pairing_20260926e.json`, `/tmp/rp_cover_angle_20260926e.json`, `/tmp/rp_maass_moment_20260926e.json`; all report nonpartial retrieval but predominantly pending/source-only compiler coverage. Proposed ingredient sets are not proofs.

### Candidate I result and next failed inference

The exact decomposition is proved in `RHTower/MaassRationalHeckeVariance.lean`, including actual Maass sources and an iff between every proposed squared correspondence bound and its exact residual threshold. Paper proof: expand the residual square, use adjointness for the cross term and exact pullback scaling for the two diagonal terms. No estimate is used. The division-free residual avoids inverse-degree case splits; explicit complex real-part identities avoid ambiguous scalar coercions.

Attempted quantitative closure fails at the source assumptions: available exceptional deck and boundary estimates require Laplace eigenvalue in `(0,1/4)`. They do not establish the residual threshold for an arbitrary level-one Maass source. Nonnegativity of the proved residual supplies only the existing degree bound. This is not a falsification of the quantitative threshold or a retirement of the variance route; the threshold remains unproved.

Second attempted inference: use different-eigenvalue orthogonality to control the cross pairing. This cannot apply as proposed: the rational pullbacks and complete Hecke transport preserve the original Laplace eigenvalue. The distinct-eigenvalue premise is absent. The positive survivor is already-proved spectral preservation, not new orthogonality. No orthogonality theorem is asserted.

Whole-route assessment: the exact actual-source identity specifies the needed quantitative estimate, but does not move the eigenvalue bound. Further algebraic rearrangement or generic Hilbert identities would not address the remaining obstacle. Next mathematical work must prove the residual threshold using global arithmetic information or find another actual-source power estimate. The classical prime-normalization identification is also not supplied by this new module.

### Variance audit

- Scratch `lake env lean /tmp/rp_variance_20260926e.lean` and installed-source `lake env lean GaloisForLFunctions/RHTower/MaassRationalHeckeVariance.lean` passed. Scratch failures were an unexpanded degree cast, an implicit inner-product scalar, and repeated rewrites of the same inequality. Explicit typed identities and separate implication proofs repaired them; default heartbeat/recursion limits were unchanged.
- Final `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassRationalHeckeVariance` passed, 8,934 dependency jobs with leaf reported 5.2s. Cached dependencies replayed unrelated warnings/information. No full or umbrella build was run. Log: `/tmp/rp_variance_build_20260926e.log`.
- Imported-module audit `lake env lean /tmp/rp_variance_axioms_20260926e.lean` passed. All four public theorem axiom sets are exactly `propext`, `Classical.choice`, and `Quot.sound`. Printed source theorem types contain actual Maass objects and no unproved analytic bounds. Log: `/tmp/rp_variance_axioms_20260926e.log`.
- New module is wired into `RHTower.lean`. Scoped whitespace checks and forbidden-token scan passed. Index regeneration completed. Final `scripts/formal_tools.py lint --check-generated` exited 1 with one unrelated error: `ThetaPowerFejerTransfer` is unreachable from the `RHTower` umbrella. No stale generated files or forbidden declarations were reported. Log: `/tmp/rp_variance_lint_20260926e.log`. No global clean-lint, target-proof, or improved-exponent claim is made. All owned search, Lean, build, index, and lint sessions exited.

## Joint oscillatory-factor attack

### Candidate J: compensate the dilation loss with both factors

[LOCAL REPAIR, scratch checked; not installed] Reopening the actual proposed phase-space estimate changes the discriminating test: failure of rapid decay for its second-moment factor does not determine the product of both factors. Set `I(t)=gaussianHalfMoment (1-i*t) 0` and `J(t)=gaussianHalfMoment (1-i*t) 1`. The source-checked Gaussian recursion predicts `I(t)*J(t)*(1-i*t)^2=pi/8`, hence `norm(I(t)*J(t))*(1+t^2)=pi/8`. Therefore `q^4*norm(I(q^2)*J(q^2)) <= pi/8`, in contrast to the proved unbounded one-factor quantity.

This is a symbolic Gaussian test, not a numerical experiment or an identification with an actual Maass operator. It can repair the model's joint nonresonant scaling but cannot establish uniformity for all Schwartz tests, the corrected Euler kernel, primitive-lattice summation, or rational-shear averages. If it passes, the whole-route question is whether the actual two phases remain jointly controlled throughout the arithmetic index set; do not infer a complete averaged estimate from the toy result.

Primary source rechecked: [Unterberger v16, Section 7](https://arxiv.org/html/2001.10956v16#S7), especially the passage from two oscillatory factors to a uniform bound. New searches: `/tmp/rp_primitive_average_20260926f.json` (partial) and `/tmp/rp_gaussian_joint_20260926f.json`. No proposed ingredient set is accepted without source and Lean verification.

Outcome: `/tmp/rp_joint_gaussian_20260926f.lean` passed `lake env lean` at default resource limits. The user redirected work away from auxiliary results. This lane is stopped, not mathematically falsified; no module or umbrella import was added. It supplied no improvement to an actual Maass eigenvalue bound.

## Direct bound attempt after redirect

Target remained subexponential prime-power coefficient growth for actual level-one Hecke-Maass cusp forms. The exact `Gamma0MaassHecke.maass_coefficient_heckeT` identity supplies Fourier transport, not that growth estimate. The deep search's proposed `exists_small_mode_of_subexponential` ingredient already assumes subexponential growth of a different sequence; it cannot produce the missing estimate. Kloosterman norm bounds and modular side-current cancellation do not close the attempted individual-eigenvalue argument. No global cancellation estimate was derived, and no improved exponent, proof, or falsification resulted.

Search records: `/tmp/rp_actual_growth_20260926g.json` and `/tmp/rp_global_cancellation_20260926g.json`. Both report nonpartial retrieval over the 59,712-file snapshot; most compiler metadata is pending or stale, and semantic coverage is unavailable. Candidate statements were inspected, not accepted from the search model's sufficiency label. This is not proof of absence elsewhere in the corpus. No Lean source edits or builds were made after the redirect; both owned search sessions exited.

## Direct representation attempt and impasse audit

Attempted closure: use the actual source's automorphic representation and rational Hecke orbit to exclude a non-tempered component at a finite prime. Source inspection of `MaassCyclicAutomorphicRepresentation` and `MaassRationalHeckeAutomorphicOrbit` establishes a real-place algebraic representation and rational-trace stability, not the required finite-place temperedness or weak-containment statement. The infinite-degree criterion in `SymmetricPowerDegreeFamilies` still needs compatible actual global lifts. No missing transfer or lift construction was derived. These routes are not mathematically falsified.

Search `/tmp/rp_finite_place_20260926h.json` returned nonpartial retrieval over 59,713 files, with semantic coverage unavailable. Its proposed ingredients supplied no finite-prime exclusion. No new Lean source, proof claim, or auxiliary module was added; owned search session 50832 exited successfully.

The previous turn is classified as no progress on the requested target. Recent thread finals were re-read: the full-Hecke-tail, variance, and direct-growth turns all leave the same quantitative global-arithmetic estimate unproved. The present representation attempt also leaves it unproved. This is an agent research impasse, not a theorem that the target is false or impossible. No justified proof-producing next step has been identified; another generic interface would not meet the user's redirect. Resumption needs a new concrete global argument or applicable external result, which must itself be verified rather than assumed. The goal is not complete.

## Resumed global-route loop: period functions

The user requested continued conjecture/proof-or-failure/pivot work. No auxiliary module is being substituted for the capstone. Current question: can global modularity be used before estimating the Hecke sum, through its period-function realization?

Primary sources: Lewis--Zagier, [Period functions for Maass wave forms I](https://arxiv.org/pdf/math/0101270), and Muehlenbruch, [Hecke operators on period functions](https://arxiv.org/html/math/0407081v2). These supply the classical correspondence and intertwiner, not Lean certificates or a Ramanujan estimate. The former's cusp bootstrapping argument explicitly gives psi(1)=0. The latter uses an unnormalized Maass Hecke operator; division by sqrt(m) is necessary for the present target.

### Candidate K: recover the spectrum from the forced zero

[BRIDGE ATTEMPT, paper calculation, not kernel checked] Write k=2^(-2s) and C=2^(s-1/2). The normalized degree-two period operator is

`H_2 psi(z) = C*(psi(2*z) + k*psi(z/2) + k*psi((z+1)/2) + (z+1)^(-2s)*psi(2*z/(z+1)))`.

The period relation is `psi(z)=psi(z+1)+(z+1)^(-2s)*psi(z/(z+1))`. Evaluation at one gives `(H_2 psi)(1)=C*(1+2*k)*psi(1)`, hence no spectral information for cusp forms. Differentiation and the same relation give

`(H_2 psi)'(1)=C*((2+k)*psi'(1)-2*s*psi(2))`.

For even inversion parity, psi'(1)=psi(2)=0. The next derivative instead gives

`(H_2 psi)''(1)=C*((4+k/2)*psi''(1)-4*(2*s+1)*psi'(2))`.

Thus these attempted scalar closures leave nonlocal values. This does not disprove all finite-jet methods or prove that the remaining terms are independent on the actual Maass space. No bound for their ratio was obtained. Positive survivor: explicit identification of the uncontrolled terms; no new target-level theorem to install.

An additional hostile test rejects the elementary positive envelope h(x)=1/(1+x). At Re(s)=1/2, the absolute four-branch operator at x=1 has value 7/6, exceeding 2*h(1)=1. This is a failure of this envelope on the ambient function space, not a Maass counterexample. Imposing the forced zero makes termwise absolute values even less informative at one: the cancellation between the values at two and one-half is essential.

### Candidate L: retain the paired branches

[BRIDGE, frozen for attack] Replace the four independent branches by paired expressions using the exact period relation before estimating. Seek a norm on the actual holomorphic cuspidal period space with normalized Hecke norm at most two at every prime. The norm must be defined independently of the desired Hecke spectrum, and its contraction must be derived, not assumed. A mere transfer of the Petersson norm or a spectral norm selected using Ramanujan would not be a new proof route. First discriminating test: derive the degree-two paired operator and determine whether both constituent operators preserve the cusp space and are contractive.

Whole-route questions: the cusp vanishing condition is used explicitly, unlike the previous purely local Fourier hypotheses. Does pairing truly remove arithmetic growth, or only relocate it into a nonlocal composition operator? Is the required norm estimate independently weaker than Ramanujan? Failure of either test requires another pivot, not a conditional Lean interface.

Search records so far: `/tmp/rp_resonant_average_20260926i.json` (partial) and `/tmp/rp_period_cohomology_20260926i.json` (nonpartial). No applicable period-function correspondence was found in the inspected candidates; this is not a corpus-wide absence claim. No new Lean source or build in this resumed loop.

### Candidate L outcome: exact energy, missing prime correlation

Restrict this paper calculation to Re(s)=1/2. No unproved extension to other spectral parameters is intended. Let H=L2((0,infinity),dx), `U psi(x)=psi(x+1)` and `V psi(x)=(x+1)^(-2s)*psi(x/(x+1))`. The cusp endpoint bounds imply psi belongs to H. Changes of variable give

`norm(U psi)^2 + norm(V psi)^2 = norm(psi)^2`.

Together with `psi=U psi+V psi`, this gives `Re inner(U psi,V psi)=0`. This is a derived identity, not a new primary conjecture. Let `D psi(x)=2^s*psi(2*x)`; D is unitary on H. The actual four-branch operator is

`sqrt(2)*H_2 psi = D psi + D^(-1) psi + U(D^(-1) psi) + V(D psi)`.

Writing these four vectors as a,b,c,d, their squared norms sum to `3*N+M`, where `N=norm(psi)^2` and `M=integral_(1/2)^2 norm(psi(x))^2 dx`. The desired bound needs the sum of their six real cross-pairings to be at most `(5*N-M)/2`. The established U/V pairing does not supply those D-dependent pairings. Neither D nor the paired summands have been proved to preserve the period space. Thus Candidate L remains an unclosed estimate, not a falsified general period-function route.

Hostile abstraction check: the coisometry identities and a unitary D alone cannot imply the desired estimate. If D is replaced by the identity and a nonzero vector satisfies `(U+V)psi=psi`, the displayed four-term expression becomes `3*psi`, yielding normalized size `3/sqrt(2)>2`. Such fixed vectors exist for the elementary even/odd coordinate coisometries on ell2(N): take w=(e_0-e_1), P=U+V, and `psi=sum_(n>=0) 2^(-n)*(P*)^n*w`. Here Pw=0, PP*=2I, the series converges, and Ppsi=psi. Its inner product with w is nonzero. This is a countermodel only to the stripped operator assumptions: it omits actual dilation relations such as `U D = D U^2`, holomorphy, and the actual Maass identification. It is not a Maass counterexample.

Whole-route consequence: changing to a period norm exposes a real conservation law, but replacing arithmetic dilation by an arbitrary unitary loses exactly the needed information. Do not formalize that abstraction as progress on the target. The full period route remains available only if its rational-dilation correlations can be controlled independently.

### Candidate M: continued-fraction energy packets

[BRIDGE, frozen for attack] The U/V mass partition iterates: each binary level retains the original total squared mass. Use a depth-L packet of all levels, whose squared norm is proportional to L, to seek an approximate intertwiner with a regular tree representation. The intended mechanism is that a bounded number of altered boundary levels would have negligible relative norm. Crucial falsifier: a determinant-prime map may change the infinite continued-fraction tail, not merely a bounded prefix. Test that arithmetic issue before building any packet or Lean abstraction.

### Candidate N: remove finite exceptional spectrum by oldforms

[BRIDGE, frozen for attack] Radulescu's [operator-algebra paper](https://arxiv.org/html/0802.3548v16) states a tempered essential-spectrum bound and allows isolated exceptions. Its stated finite-level extension is not yet audited here. Test whether copies of one hypothetical exceptional form at increasing levels force an infinite-dimensional exceptional eigenspace to which that bound applies. Necessary checks: use one fixed Hilbert space/operator, preserve the chosen prime operator, and justify compactness uniformly under the level limit. A bound separately at every finite level does not by itself meet those checks.

Searches `/tmp/rp_period_pairing_20260926j.json` (partial, judging unfinished) and `/tmp/rp_period_energy_20260926j.json` (nonpartial) were inspected, including source arguments and proposed ingredient groups. The latter's proposed disjoint-interval/vector-norm chain does not concern the actual Hecke cross-pairings. Its retrieval label is not a mathematical justification. No source-based contraction or period correspondence was obtained from these searches.

### Candidate M outcome: prime dilation changes the tail orbit

The proposed finite-prefix mechanism is false. A finite continued-fraction prefix is a product of integral matrices `[[a,1],[1,0]]`, hence is unimodular. Two real numbers with a common tail are therefore related by an integral Mobius map of determinant plus or minus one. For a transcendental positive x, an equality

`p*x = (a*x+b)/(c*x+d)`

would imply `p*c*x^2+(p*d-a)*x-b=0`. Transcendence forces c=b=0 and a=p*d. The unimodular determinant would then be `p*d^2`, impossible for an integer p>1. Thus prime dilation is not even a finite prefix replacement at such x, let alone a uniformly bounded replacement. This paper argument does not rule out a different approximate-intertwining construction; it falsifies this route's stated mechanism.

Positive survivor: the exact separation of the unimodular tail orbit from the prime-dilated point, and the unchanged level-by-level mass identity. Neither supplies control on the interaction between these two orbits. Enlarging the orbit space without proving that control would only move the missing estimate. No auxiliary Lean module was installed under the user's target-only redirect.

### Candidate N outcome: finite-level compactness does not pass to the limit

Even granting the external essential-spectrum claim, this inference fails. At a prime q distinct from p, the proposed oldform copies `f(q^j*z)` occupy increasing levels, not an infinite-dimensional exceptional eigenspace in a single fixed finite-level space. Finite multiplicity at each level is consistent with arbitrarily large multiplicity as level grows.

The missing operator implication has an exact countermodel: for fixed lambda>2, let P_n project onto the first n coordinates of ell2(N). Every `lambda*P_n` is compact, with essential norm zero, whereas its strong limit is `lambda*I`, with essential norm lambda. Thus even a uniform bound on the finite-stage essential norms does not pass through a merely strong limit. A uniform bound on exceptional ranks, independent of level, would be a different assertion; none was established for actual Hecke operators. This retires the proposed inference, not the operator-algebra research programme or the external theorem.

### Candidate O: weight raising instead of changing level

[BRIDGE ATTEMPT, not closed] Try to repeat one exceptional eigenvalue in infinitely many K-types at fixed level, then apply the essential bound on the full automorphic representation. The external statement inspected acts on the upper-half-plane Hilbert space, hence on weight zero. The enlarged space needs its own bound.

The existing source `HTGeometry/OrbitInductionEssentialization.lean`, `rectEssentialNorm_orbitInduction` and `shellResidual_essentialNorm`, states exactly that infinitely many orthogonal unitary copies of a nonzero local defect have essential norm equal to its local norm and are not compact. Its hypotheses include an infinite index set and the explicit blockwise unitary induction construction. It is not an already-proved identification with Maass K-types; it refutes automatic preservation of compactness under that proposed amplification. The source was read, not newly kernel-audited in this turn.

`RHTower/MaassDifferentialLadder.lean` supplies exact lowering-after-raising scalar identities for actual forms; the stated nonvanishing lemmas there are restricted to exceptional real-place eigenvalues. Returning a ladder to weight zero gives a scalar multiple of the original vector, not independent weight-zero copies. `MaassSpectralTransport` is algebraic spherical conjugation, not a bounded extension to all weights. No all-weight essential bound or uniform compact-error estimate was derived. The surviving actual ladder identities are already in the corpus; no duplicate theorem was added.

### Loop assessment

The loop tested: scalar jets, a positive envelope, paired period energy, continued-fraction packets, oldform amplification, and K-type amplification. These are distinct tests of proposed mechanisms, not six claimed breakthroughs. The period-energy route is new to this task's recorded attempts, but has not passed its decisive arithmetic-correlation test. Calling it a validated new proof route would be premature. Ramanujan remains unproved and unfalsified here; no normalized eigenvalue exponent improved.

Remaining exact period target at p=2: derive the six cross-pairing bound in Candidate L for the actual cuspidal period function, using the rational-dilation relations and holomorphic global constraints. All-prime control and an unconditional actual-Maass/Lean correspondence would still be required. Neither an arbitrary-unitary substitute nor a compact-error amplification meets that target.

Search `/tmp/rp_essential_oldform_20260926j.json` was partial with judging unfinished; its generated compact-picture Laplacian ideas concern the real-place model, not the Hecke compact-error estimate. `/tmp/rp_tail_orbit_20260926j.json` was nonpartial; its convergent/denominator ingredients do not identify prime dilation with a common tail. Both source-argument lanes and proposed groups were inspected. Coverage snapshots inventoried 59,719 files, with semantic coverage unavailable; no exhaustive-absence claim follows. All owned searches exited. No Lean source edits, Lean processes, resource-limit changes, numerical experiments, or builds were run during this loop.

## Direct period-correlation continuation

Previous-turn classification: progress in route discrimination, from concrete failed mechanisms that changed the next action; no progress on the requested eigenvalue bound. The current worktree still contains the unresolved period-correlation target. This continuation attacked that target rather than adding a generic Hilbert-space interface.

Inversion parity relates the four vectors in Candidate L in pairs, but does not bound their remaining mixed pairings. Conjugating translation by dilation converts one of them into a fractional-translation correlation. Mellin diagonalization controls dilation itself; it does not simultaneously diagonalize that translation or produce the required cancellation. No quantitative closure was derived. These observations are paper-level and are not newly kernel-checked theorems.

The current deep/method search `/tmp/rp_period_mellin_20260926k.json` completed nonpartially over a 59,720-file coverage snapshot, with semantic coverage unavailable. All candidate statements, source arguments, and the proposed ingredient group were inspected. The proposed `IsMellinFermiWitness.norm_correlationMellin_le` concerns a different correlation and requires orthogonality to every Fermi--Nyman generator; its definition was inspected in source. That hypothesis has not been established for a Maass period function. `SelbergMaassMixedLoss.mismatchPair_sq_le_losses` concerns finite-deck character projections and retains both transfer-loss energies. Its source contains no identification with the rational-dilation pairings needed here. The actual Hecke preservation and Fourier-transport candidates still supply identities, not a growth estimate.

External model checks did not supply a replacement bound. Kiming's [Hecke-model theorem](https://www.numdam.org/item/?id=AIF_2007__57_6_1863_0) gives an algebraicity-or-cohomology alternative, not absolute-value control of Hecke eigenvalues. Neither alternative was assumed to imply temperedness.

This continuation is classified as no progress on the requested result. The same missing actual-source arithmetic estimate remains; no proof-producing next step was established. The goal remains active and unmet. No Lean source was changed or compiled, no build or numerical experiment was run, and the owned search session 5455 exited successfully.

## Resumed blocked audit

Previous-turn classification: no progress. The current card and source were rechecked rather than relying on a stale goal summary. Search `/tmp/rp_final_frontier_20260926l.json` completed nonpartially over a 59,720-file snapshot, with semantic coverage unavailable. Its candidate, source-argument, and proposed-premise lanes supplied no applicable closure. This is not proof that no theorem exists elsewhere in the corpus.

The proposed `SelbergModalEnergy.maassCoefficient_bounded` was inspected in source: it bounds the height-dependent Fourier mode by boundedness of the actual form, not the normalized Hecke coefficient. Its proposed companion `SarnakXueDimension.dim_le` assumes an exceptional real-place eigenvalue. The current `SatakeEnergyBound` declarations assume parameter norm bounds, and `SelbergRamanujanBound` concerns Ramanujan sums. None discharges the frozen capstone.

The same missing quantitative arithmetic estimate persisted in three consecutive resumed turns: the six-mechanism loop, the direct period-correlation continuation, and this current-state revalidation. The first changed route selection through negative evidence; none closed the estimate. No actual Maass counterexample was produced. The seven earlier auxiliary modules and their audits do not certify the requested theorem. There is no capstone proof artifact on which a successful targeted build or axiom audit could establish completion.

Blocked-audit conclusion: the agent is at a research impasse, with no justified proof-producing next action identified. Further work requires a new mathematical argument or an applicable result to audit; repeated generic reductions would not advance the requested end state. The goal must not be marked complete. Request blocked status after this audit. No Lean source changes or builds in this turn; owned search session 61111 exited, and no owned Lean process was started.
