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

## Resumed trace-cancellation attack

The user requested continued mathematical attacks, not another search-only revalidation. Goal remains unmet. The active question is whether a positive spectral trace at the indices m=n=p^n has subexponential growth in n. A proof for a suitable fixed positive spectral weight would exclude an exponentially growing prime-power Hecke coefficient. No such trace bound is assumed.

### Candidate P: remove the ramified-modulus growth

[PAPER IDENTITY; not Lean checked] Let p be prime, R a positive integer, B any complex-valued function on positive reals, and S the ordinary Kloosterman sum. Define finite sums

`K_n(R) = sum_(1<=c<=p^n*R) S(p^n,p^n;c)/c * B(p^n/c)`,

`F_n(R) = sum_(1<=c<=p^n*R, p does not divide c) S(p^n,p^n;c)/c * B(p^n/c)`,

`E(R) = sum_(1<=d<=R, p divides d) S(1,1;d)/d * B(1/d)`.

Partition c=p^a*c0 with p not dividing c0. For a<=n, reducing the unit sum modulo c0 gives

`S(p^n,p^n;p^a*c0) = phi(p^a)*S(p^(n-a),p^(n-a);c0)`.

For a>n, put c=p^n*d. Reduction of units modulo d has p^n fibers because p divides d, giving `S(p^n,p^n;p^n*d)=p^n*S(1,1;d)`. The scaled cutoff then yields exactly

`K_n(R) = F_n(R) + (1-1/p)*sum_(k<n) F_k(R) + E(R)`,

`K_n(R)-K_(n-1)(R) = F_n(R)-F_(n-1)(R)/p` for n>=1.

Whole-route consequence: this does not improve an exponent. Polynomial bounds for F imply polynomial bounds for K, and the stable inverse recurrence reconstructs polynomially bounded F from polynomially bounded K. Passing to infinite sums also needs convergence. Positive survivor: arithmetic localization of the unresolved cancellation to moduli coprime to p, not a new Maass estimate. No originality claim or auxiliary Lean installation.

### Candidate Q: keep the two oscillatory factors together

[FROZEN FOR ATTACK] For p not dividing c, reindexing units gives `S(p^n,p^n;c)=S(1,p^(2*n);c)`. Before taking absolute values, combine the Bessel factors exp(plus/minus 4*pi*i*p^n/c) with the additive character in S. The exact ring identities are

`u+u^(-1)-2=(u-1)^2*u^(-1)`,

`u+u^(-1)+2=(u+1)^2*u^(-1)`.

Hostile test: these expressions are not quadratic polynomials in u; the inverse is not constant. Gaussian evaluation cannot be inferred from the displayed squares. The test must control the sum over both residues and moduli, including the transition c comparable to p^n where a large-argument Bessel expansion is not uniform. A local stationary-phase rewrite without that estimate does not meet the target.

### Candidate R: choose away the oscillatory tail

[FROZEN FOR ATTACK] Test whether a spectral weight h, nonnegative on the actual spectrum and nonzero at the selected form, can remove the leading large-argument Bessel oscillation. If positivity prevents that, test signed h rather than assuming spectral positivity survives. The discriminating quantity is the moment `integral t*tanh(pi*t)*h(t) dt`, which appears both in the diagonal and in the formal leading Bessel coefficient. A fixed-order asymptotic cannot be integrated over unbounded spectral t without an independent uniform remainder bound.

Input checks: search `/tmp/rp_hecke_trace_amplifier_20260926m.json` completed nonpartially over 59,738 inventoried files. Retrieved Kloosterman estimates either fix the modulus or assume coefficient majorants; none inspected supplies this varying-modulus trace bound. Proposed ingredient groups are unverified. The spectral formula was checked against Li--Young, Theorem 2.3, and the fixed-order Bessel expansion against DLMF 10.17.3; these external formulas are not Lean certificates.

### Candidate Q outcome: the residual phase is still arithmetic

[PAPER] At an odd prime modulus q not dividing N, write chi for the quadratic character, including chi(0)=0. The equation `u+u^(-1)-2=v` is equivalent to `u^2-(v+2)*u+1=0`. Its roots are automatically units and their number is `1+chi(v*(v+4))`. Consequently

`exp(-2*pi*i*2*N/q)*S(N,N;q) = sum_(v mod q) chi(v*(v+4))*exp(2*pi*i*N*v/q)`.

The constant Fourier term disappears because N is nonzero modulo q. Thus the square-over-unit rewrite has produced a quadratic-character transform, not the ordinary quadratic Gauss sum (whose multiplicity involves chi(v)). This identifies the missing arithmetic weight precisely. It does not bound its average over changing q, and does not rule out a more substantial reciprocity argument. No modulus cancellation or improved Maass bound was obtained.

### Candidate R outcome: separate positivity from the transition range

[PAPER, no Lean certificate] Use normalization

`B_h(x)=(2*i/pi)*integral_R t*h(t)*J_(2*i*t)(x)/cosh(pi*t) dt`.

For a fixed real even polynomial times a Gaussian, the large-x expansion gives

`B_h(x)=-(2/pi)*sqrt(2/(pi*x))*M_h*sin(x-pi/4)+O_h(x^(-3/2))`,

`M_h=integral_R t*tanh(pi*t)*h(t) dt`.

Uniformity check: DLMF 10.17.14 bounds the first Hankel remainder by a constant times `(1+t^2)/x * exp(C*(1+t^2)/x)`. After division by cosh(pi*t), both exponential prefactors are bounded. For sufficiently large x the fixed Gaussian dominates this remainder, so integrating the expansion is justified in this class. Nonzero h>=0 on the whole real line has M_h>0. It cannot eliminate this leading oscillation.

This is NOT a no-go for signed spectral weights. The continuous prime-power coefficient is a sum of n+1 unit-modulus terms. For a fixed weight integrable against the Eisenstein measure, its absolute contribution is at most a constant times `(n+1)^2`. Thus negativity on the continuous spectrum can be paid for without exponential growth; only cusp-spectrum positivity is needed for detection. A possible survivor is an even-degree orthogonal polynomial in t^2 times a Gaussian, with all its positive roots placed inside a gap in the cusp spectrum. Orthogonality would kill finitely many leading Bessel moments while preserving signs outside that gap. The required spectral input and quantitative normalization have not been kernel verified; this is a construction outline, not a finished theorem.

The next hostile test is independent of that construction. For any fixed continuous nonzero B choose `0<a<b` and delta>0 with `abs(B(x))>=delta` on [a,b]. In the p-coprime sum, moduli in `[N/b,N/a]` number `(1-1/p)*N*(1/a-1/b)+O(1)`. Therefore even the optimistic termwise square-root envelope satisfies

`sum_(p does not divide c) d(c)/sqrt(c)*abs(B(N/c)) >= C_(B,p)*sqrt(N)`

for all sufficiently large N, since d(c)>=1. This is a LOWER BOUND ON THE PROPOSED MAJORANT, not on the Kloosterman sum or spectral trace. At N=p^n it prevents this fixed-weight absolute-value method from giving polynomial growth in n. Arbitrarily strong fixed-x tail decay does not change the transition c comparable to N. This retires that proposed inference, not all test-function or trace methods. No new eigenvalue exponent follows.

### Candidate S: average an extra Hecke index before estimating

[ATTEMPTED PIVOT, PAPER] Multiplicativity suggests averaging coefficients at N*r, with p not dividing r, to turn lambda_j(N*r) into lambda_j(N)*lambda_j(r) and exploit geometric cancellation in r. The corpus's `KloostermanTerminalGeometricCancellation` genuinely controls a linear index average, but retains small phase denominators and does not itself control this trace.

For each c coprime to N there is an exact finite representation

`S(N*r,N*r;c)=sum_(v mod c) rho_(N,c)(v)*exp(2*pi*i*r*v/c)`,

where rho counts units z satisfying `z^2-v*z+N^2=0 mod c`. Proof: set z=N*u in the original unit sum and group by `v=N*(u+u^(-1))`. This keeps the arithmetic coefficients, unlike replacing them by arbitrary phases.

The proposed completion does not isolate one frequency. If r has scale R, the Bessel transition now has c of scale N*R. A smooth unrestricted r-average resolves frequencies only to scale c/R, hence to scale N. Equivalently, Poisson summation retains terms with `abs(v-k*c)` of order N; it does not force v=0. Restricting to r coprime to p subtracts the r=p*s average and adds its resonance centers; it does not make this frequency resolution finer. The resulting quadratic congruences have discriminants `v^2-4*N^2` across order N possible integer traces. This describes the size of the unresolved window, not a lower bound for its nonzero contribution. At N=p^n the window is still exponential in n. A bound for its signed weighted sum was not derived. This is a failure of the claimed automatic-completion saving, not a proof that all amplified trace methods fail.

Whole-route result: the ramified-modulus split, phase rewrite, weight cancellation, and extra-index completion have each been tested at their quantitative step. None yet supplies subexponential actual Hecke growth. The arithmetic task left by S is cancellation among the discriminant-weighted transition terms; merely installing the exact root-count identity would not solve it. No auxiliary Lean module is installed under the target-only redirect.

Checks: `Sieve/KloostermanSum.lean` uses the stated classical unit sum, and `kloostermanSum_unit_left` gives the unit-frequency reduction. `SelbergPeterssonKloosterman.petersson_kloosterman` is an unfolded Poincare-series pairing with explicit level and real-part restrictions, not the missing positive all-spectrum growth bound. Search `/tmp/rp_diagonal_phase_20260926n.json` completed with partial retrieval; proposed phase-symmetry obligations did not prove collective cancellation. Its owned session 85261 exited. No Lean process, build, numerical experiment, or heartbeat-limit change was used in this resumed batch.

External inputs: [Li--Young, Theorem 2.3](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/957D21B10686FBDDD2E7537C8D9B19D2/S0010437X11007366a.pdf/the-l2-restriction-norm-of-a-gl3-maass-form.pdf), [Li, Kuznetsov transforms in Section 2](https://annals.math.princeton.edu/wp-content/uploads/annals-v173-n1-p08-p.pdf), and [DLMF 10.17, including complex-order remainder bounds](https://dlmf.nist.gov/10.17). The new deductions above are this task's paper arguments; neither novelty nor Lean verification is asserted.

## Discriminant-reciprocity continuation

Previous-turn classification: progress in route discrimination, not progress in the Maass eigenvalue bound. The recorded finite identities and quantitative failed inferences change the next action: retain the discriminant weights and test genuine reciprocity, rather than repeat absolute-value estimates. The current card was re-read before continuing. Goal remains unmet.

### Candidate T: use prime-power factorization after switching divisors

[PAPER ATTEMPT] Seek to reduce the root-count polynomial `z^2-v*z+N^2`, N=p^n, to the corpus's factored quadratic family. Source inspection rejects the proposed direct application: `ReducedFrequencyMobiusAliasCollapse.quadraticCongruenceRoots` counts roots of `r*(r+h)=0`, not a general discriminant polynomial.

Integer splitting of the actual polynomial forces roots d,e with d*e=p^(2*n). Thus `v=plus/minus(p^j+p^(2*n-j))` for some 0<=j<=2*n. Conversely each such v splits. In a fixed window abs(v)<=C*N, writing j=n+d shows `p^d+p^(-d)<=C`; only a bounded number of these split traces occur as n grows. They cannot replace the order-N window of general discriminants. For instance v=2*N-1 has negative discriminant 1-4*N and is never an integer split for N>=1. This is an obstruction to this factorization shortcut, not a lower bound on the weighted trace.

Search `/tmp/rp_discriminant_reciprocity_20260926o.json` completed with partial retrieval; its suggested CRT uniqueness chain retains the factored-polynomial definition. It does not prove an estimate for the required signed nonsplit-discriminant family. Owned session 77136 exited.

### Candidate U: remove the nonsplit range through the test function

[FROZEN FOR ATTACK] Test a stronger, analytic replacement for divisor switching: can the cosine transform of the geometric test be supported only in the elliptic interval, while its Maass Bessel transform remains nonzero? Such localization could connect to holomorphic trace methods, but is useful only if it still detects the actual Maass form. The decisive test is the exact Bessel representation, not a guessed support property.

Set `F(y)=integral_(x>0) B(x)/x*cos(x*y) dx`. DLMF 10.9.8, subtracted at orders 2*i*t and -2*i*t, gives the improper-integral kernel identity

`(J_(2*i*t)(x)-J_(-2*i*t)(x))/sinh(pi*t) = -(4*i/pi)*integral_(u>0) cos(x*cosh(u))*cos(2*t*u) du`.

The sign is obtained directly by subtraction; a retrieved secondary formula had the opposite sign and is not used. For sufficiently regular B, the normalized Maass transform should therefore be `(2/pi)*integral_(u>0) F(cosh(u))*cos(2*t*u) du`. The pending test is whether the distributional/interchange justification holds for a smooth cosine-bandlimited test, and whether restricting F to abs(y)<1 kills the desired transform. No conditional interface or new Lean module is being installed in place of that test.

### Candidate T follow-up: reciprocal completion returns the original kernel

[PAPER] For an odd prime q not dividing N, let chi be the quadratic character, extended by zero. The root count for `z^2-v*z+N^2` is `1+chi(v^2-4*N^2)`. Finite Fourier transformation gives exactly

`sum_(v mod q) chi(v^2-4*N^2)*e(h*v/q) = S(N*h,N*h;q)-q*[h=0 mod q]`.

Proof: add the constant one to the character, enumerate the roots by the units z=N*u, and apply finite additive-character orthogonality to remove that constant. The zero frequency is -1. Every nonzero frequency is again a diagonal Kloosterman sum; h=1 is precisely the original kernel. Thus this completion is an exact round trip, not an independently stronger cancellation estimate. CRT multiplicativity does not change that conclusion. No new bound for the varying-modulus sum follows.

### Candidate U outcome: the proposed cutoff annihilates the Maass detector

[PAPER PROOF, not Lean] Let b be an even Schwartz function, B(x)=x*b(x) for x>0, and `F(y)=integral_(x>0) b(x)*cos(x*y) dx`. For a Kuznetsov test with B'(0)=0 additionally choose b(0)=0. Define

`M_B(t)=i/(2*sinh(pi*t))*integral_(x>0) (J_(2*i*t)(x)-J_(-2*i*t)(x))*b(x) dx`,

with the removable value at t=0. Then for abs(Im(t))<1/2 the identity under test is

`M_B(t)=(2/pi)*integral_(u>0) F(cosh(u))*cos(2*t*u) du`.

Interchange justification: truncate u at A. Fubini applies on this finite interval. Put a=2*abs(Im(t))<1 and split the x-dependent u-integral at `max(1,log(4/x))`. Integration by parts in the remaining phase x*cosh(u) gives, uniformly in A,

`abs(integral_0^A cos(x*cosh(u))*cos(2*t*u) du) <= C_t*(1+log_+(1/x)+x^(-a))`.

The initial interval has the same bound. This is integrable against abs(b(x)) on the positive half-line, including x=0 since a<1. Dominated convergence proves the displayed transform identity from DLMF 10.9.8; t=0 follows by the same bounds locally uniform in t. This supplies the missing justification rather than interchanging the two improper integrals formally.

If F vanishes for y>=1, the Maass transform is zero. Nonzero such admissible tests exist: choose a nonzero smooth even F supported inside (-1,1) with integral zero, and take its inverse cosine transform b. The zero integral gives b(0)=0. Therefore removing the entire hyperbolic side in this manner removes the desired spectral detector as well. The surviving exact statement is that the Maass response uses only F on the hyperbolic range; it is not an estimate for that response.

A stronger fixed-weight test uses the prime-power arithmetic. The only split ratios `v/(2*p^n)` above one are `(p^d+p^(-d))/2`. This set is locally finite. The remaining grid points v/(2*p^n) are dense in (1,infinity): any open interval contains a smaller interval avoiding those finitely many split ratios, then contains a sufficiently fine prime-power grid point. A continuous F that vanishes at every nonsplit positive-discriminant trace for all n consequently vanishes on [1,infinity), and hence has zero Maass transform. This rules out this exact fixed-weight annihilation strategy, not cancellation of a signed trace.

### Candidate V: allow the annihilating weight to vary with n

[ATTEMPTED PIVOT, PAPER] Keep fixed Y>1 and a fixed spectral parameter t with abs(Im(t))<1/2. Suppose F_n is C1 on [1,Y], vanishes above Y, vanishes at every nonsplit grid point v/(2*N) in [1,Y], and its Maass response is normalized to one. Here N=p^n. The number of excluded split grid points in [1,Y] is bounded independently of n. Every point of [1,Y] therefore lies within C_(p,Y)/N of a retained zero for sufficiently large n. The mean-value inequality gives

`sup_[1,Y] abs(F_n) <= C_(p,Y)/N * sup_[1,Y] abs(F_n')`.

Writing L=arcosh(Y), the exact transform identity gives

`1 <= (2/pi)*L*cosh(2*abs(Im(t))*L)*sup_[1,Y] abs(F_n)`.

Thus `sup abs(F_n') >= c_(p,Y,t)*N`. Moving the weight escapes the fixed-weight vanishing argument only with at least this derivative cost under the stated fixed-support conditions. This is not a lower bound for the actual trace, and does not preclude a method that controls the growing cost by some other argument.

Positive survivor check: take a smooth nonnegative bump psi supported in a short subinterval of (1,Y) on which `cos(2*t*arcosh(y))` is positive (real t; for purely imaginary t the factor is already positive). The functions `psi(y)*sin(2*pi*N*y)^2` vanish on the whole trace grid and have nonzero Maass response. Integration by parts in the cosine term of sin-squared shows that response tends to a positive constant, so normalization is bounded and the derivative cost is O(N). This confirms that exact moving-grid annihilation itself is possible; it does NOT give cusp-spectral positivity or a small geometric estimate. In fact F_n(1)=0 implies that the integrable real-line response has integral zero, so this nonzero response cannot be nonnegative on the entire real line. No conclusion about its signs at all actual cusp eigenvalues is asserted.

Whole-route assessment: reciprocal completion, fixed hyperbolic cutoff, and bounded-cost exact grid removal have failed their discriminating tests. The moving-filter survivor still lacks the actual cusp-spectrum positivity and quantitative signed arithmetic estimate needed for Ramanujan. No actual Maass eigenvalue bound improved, no counterexample was produced, and no capstone Lean certificate exists. These results are paper-level route evidence, not claimed original theorems or formal completion.

Source check: [DLMF 10.9.8](https://dlmf.nist.gov/10.9#E8) supplies the Bessel representation used above. Search `/tmp/rp_bessel_support_20260926p.json` returned nonpartial retrieval over 59,743 inventoried files; its suggested modified-Bessel decay chain does not prove this imaginary-order J transform or the missing arithmetic estimate. Source and compiler freshness remain distinct. Owned session 73856 exited. No Lean edits, builds, numerical experiments, or resource-limit changes in this continuation.

### Candidate W: actual cusp signs of the short-support moving filters

[PAPER DERIVATION, NOT LEAN] The hypothesis being tested is that V's nonnegative moving filter can have nonnegative response at every actual cusp eigenvalue even though its response changes sign on the real line. This fails when its hyperbolic support is sufficiently close to, but separated from, y=1.

Use the Fourier convention `h(r)=integral_R g(u)*exp(i*r*u) du`. Let g be nonzero, nonnegative, even, smooth and compactly supported in `0<abs(u)<b`. Take b below both the first hyperbolic length and `2*log(2)`. The modular trace formula and its explicitly combined scattering/parabolic expression are given in [Rudnick, Section 5.1, equations (5.1)-(5.4)](https://www.math.tau.ac.il/~rudnick/papers/modularCLT.pdf); [Stromberg, Section 2.6, equations (2.7)-(2.11)](https://arxiv.org/pdf/1106.5741) separately lists the identity, elliptic and scattering terms. The combined expression is important: leaving the scattering integral untreated would not justify the following sign conclusion.

Set `A2=integral_R g(u)/u^2 du`, `A1=integral_R g(u)/abs(u) du`, and `M=integral_R g(u) du`. The following derivation gives constants C1,C2 independent of g and b, with b bounded above by one fixed small radius:

`sum_discrete h(r_j) <= -A2/6 + C1*A1 + C2*M`.

1. The hyperbolic contribution vanishes by support. The scattering prime sum vanishes because its arguments are `2*log(m)`, m>=2. The terms proportional to g(0) vanish as well.
2. Write `r*tanh(pi*r)=abs(r)+R(r)`, where `R(r)=-2*abs(r)/(exp(2*pi*abs(r))+1)` is integrable. Abel regularization gives `integral_R h(r)*abs(r) dr = -2*A2`: the regularized Fourier kernel is `2*(epsilon^2-u^2)/(epsilon^2+u^2)^2`, and dominated convergence applies on the support away from zero. The identity coefficient is 1/12; the R contribution is bounded by `norm(R)_1*M`.
3. For a>0, [DLMF 5.9.16](https://dlmf.nist.gov/5.9#E16), Fourier inversion and `integral h=2*pi*g(0)=0` give `integral_R h(r)*digamma(a+i*r) dr = -2*pi*integral_0^infinity g(u)*exp(-a*u)/(1-exp(-u)) du`. Fubini is justified before separating the numerator: near u=0 it is bounded by a constant times `1+abs(r)`, integrable against the Schwartz function h. Combining a=1 and a=1/2 gives a whole-line parabolic kernel `1/(2*(exp(abs(u)/2)-1))`, bounded by `C1/abs(u)` on the fixed small interval.
4. The finitely many elliptic real-spectral weights are integrable. Since `abs(h(r))<=M` for real r, their combined contribution is bounded by `C2*M`.

Now `A1<=b*A2` and `M<=b^2*A2`. Choose b so that `c_b=1/6-C1*b-C2*b^2>0`. The discrete trace is at most `-c_b*A2<0`. Every imaginary spectral parameter has `h(i*tau)=integral g(u)*cosh(tau*u) du>0`; hence a negative term occurs at a real spectral parameter. Such an L2 eigenfunction is cuspidal: its constant Fourier mode has the form `y^(1/2)*(A*exp(i*r*log(y))+B*exp(-i*r*log(y)))`, or `y^(1/2)*(A+B*log(y))` for r=0, and square integrability with measure `dy/y^2` forces both coefficients to vanish. The modular surface has only one cusp.

Positive survivor: the total negative response on real cusp eigenvalues is at least `c_b*A2`, not merely nonzero. This is a quantitative local trace obstruction, derived from the full modular trace formula. Its paper proof uses that external theorem; neither that dependency nor this result was kernel-audited here. It is not a formally closed no-go certificate or a claim of literature novelty.

For V specifically, put `g_N(u)=F_N(cosh(u/2))/(2*pi)`. This gives exactly `h_N(t)=M_(B_N)(t)`. A fixed bump supported sufficiently close to y=1, but separated from it, satisfies W's support condition for every N. Consequently each of these moving filters is negative at some actual cusp spectral value, despite retaining its positive response at the chosen target. Whole route: this subfamily cannot serve as the required positive detector. The result does not exclude signed spatial filters or larger support.

### Candidate X: square the response to repair positivity

[PAPER TEST] For V's real even h_N, squaring gives a nonnegative real-spectral response. Its inverse Fourier transform is `g_N*g_N`. Choose an interval I of length ell>0 inside the positive-u bump on which its fixed envelope is positive. The sine-squared factor is positive except at isolated points. For every `abs(delta)<ell`, the overlap of I and delta+I has positive length, so `(g_N*g_N)(delta)>0`, for every N.

Take `delta_N=2*arcosh(1+1/(2*N))`, which tends to zero. The squared response's hyperbolic filter is therefore positive at the trace-grid point `(2*N+1)/(2*N)` for all sufficiently large N. For prime powers N>=3 this is nonsplit: if `4*N+1=(2*k+1)^2`, then `N=k*(k+1)`, and coprimality of consecutive integers forces the only positive prime-power case N=2. Squaring thus reintroduces a nonsplit arithmetic term that V had removed exactly.

Positive survivor: a whole neighborhood of the singular trace is filled by convolution, uniformly in N; this is stronger than loss of just one prescribed zero. Whole route: this positivity repair does not preserve the arithmetic cancellation mechanism. No statement that the resulting arithmetic sum is necessarily large follows.

### Candidate Y: shrink positive support through the singular trace

[PAPER CONSTRUCTION AND COST] The obstruction in W requires g(0)=0. There is a genuine escape from that condition: take a nonnegative even smooth bump kappa supported in [-1/2,1/2], with integral one; rescale `kappa_a(u)=kappa(u/a)/a`; and use the autocorrelation `g_a=kappa_a*kappa_a`. Its Fourier transform is `h_a(t)=hat(kappa)(a*t)^2`, nonnegative for real t and positive for purely imaginary t. For each fixed Maass parameter t_f, normalization to `h_a(t_f)=1` is bounded for sufficiently small a. The source construction by self-convolution already appears in `formal/GaloisForLFunctions/PNTPlus/Wiener.lean:3264`; it is not claimed as a new positivity construction.

Choose `a<2*arcosh(1+1/(2*N))`. Then the associated hyperbolic filter `F_a(y)=2*pi*g_a(2*arcosh(y))`, y>=1, vanishes at every trace-grid point strictly above 1. This statement concerns the hyperbolic restriction only; admissible extension below y=1 and the full arithmetic trace are not being silently assumed.

The cost can be proved without differentiating the rapidly varying filter. More generally let h be even, nonnegative on the entire real line, Schwartz, with smooth inverse Fourier transform supported in [-a,a]. Suppose `abs(h(t_f))=1`, and set `sigma=abs(Im(t_f))` and `M=integral_R h(t) dt`. Fourier inversion and positivity give

`abs(g(u)) <= g(0)=M/(2*pi)`,
`sup_R h <= a*M/pi`, and `M >= pi*exp(-a*sigma)/a`.

For `T=pi/(4*a)`, at most half of M lies in [-T,T]. Monotonicity of `t*tanh(pi*t)` for t>=0 therefore yields the explicit bound

`integral_R t*tanh(pi*t)*h(t) dt >= pi^2*exp(-a*sigma)*tanh(pi^2/(4*a))/(8*a^2)`.

The support condition implies `a^2<4/N` by `cosh(a/2)>=1+a^2/8`. For `sigma<=1/2`, the lower bound is at least a fixed positive constant times N. The 1/12 identity coefficient does not change that order. Conversely the normalized fixed-bump autocorrelations above have identity integral of order `a^(-2)`, by scaling and dominated convergence. Thus this positive construction has the stated order of cost, not an artifact of a derivative estimate.

Whole route: shrinking support supplies an actual positive hyperbolic detector, but its diagonal contribution has order at least N=p^n, not polynomial growth in n. This is a lower bound for this contribution under full real-line positivity, NOT a lower bound for a Hecke eigenvalue or the signed total trace. In particular it does not exclude cusp-positive weights that are negative on the continuous spectrum. That less restrictive positivity problem, together with quantitative control of the remaining signed arithmetic terms, is still unproved.

### Current audit after W-Y

The three tests address the actual detector/sign/cost obstacle left by V. They discriminate between failed constructions and a positive survivor, but produce no improved bound for an actual Hecke-Maass eigenvalue and no counterexample. The current methods still do not close the required global arithmetic estimate. No target certificate exists; no auxiliary Lean module was added to present these paper tests as completion.

Searches `/tmp/rp_short_wave_trace_20260926q.json` and `/tmp/rp_positive_filter_cost_20260926r.json` both completed with nonpartial retrieval over 59,744 inventoried files. This is retrieval coverage, not compiled coverage. The former suggested finite-cover Fourier transport rather than a complete spectral trace formula; the latter found the existing autocorrelation construction but no actual-Maass estimate resolving the cost. Its proposed ingredient chain remains unverified. Owned sessions 80086 and 26124 exited. No Lean process, numerical experiment, or resource-limit change was launched in this continuation. Formal integration/audit of W-Y has not been performed, and no formal no-go closure is claimed.

## Resumed attack: signed continuous spectrum

The previous tests changed the next action: Y assumed positivity on the entire real line, whereas the trace argument only needs positivity at actual cusp parameters. Failed candidates alone were not grounds to stop this research. The goal is active. The request for 3,000 conjectures has not been fulfilled; the following six mechanism tests are not relabeled as 3,000 independent conjectures. In the terminology of the scientific-method document, these are bridge candidates and hostile tests, not claimed new universal laws or claims of literature priority.

### Candidate Z: finitely many moments with actual cusp positivity

[PAPER CONSTRUCTION, NOT LEAN] For every finite m and every fixed actual cusp parameter t_f, there exists an even entire, strip-Schwartz h, positive at every cusp parameter, with h(t_f)=1 and

`I_k(h)=integral_R t^(2*k+1)*tanh(pi*t)*h(t) dt=0` for `0<=k<2*m`.

Here m>=1; the zero-order case needs no construction. Discreteness gives a closed interval [A,B] inside (0,infinity) containing no squared real cusp parameter. Put c in its interior. For L>0, let P_L be the monic orthogonal polynomial of degree 2*m for the positive measure

`d mu_L(x)=1_(x>0)*tanh(pi*sqrt(x))*exp(-L*(x-c)^2) dx`.

All its roots eventually lie inside (A,B). To justify this rather than assume it, rescale x=c+y/sqrt(L). Every rescaled moment tends to `tanh(pi*sqrt(c))*integral_R y^k*exp(-y^2) dy`, by dominated convergence, including the moving lower endpoint. The finite positive-definite Gaussian Gram matrix has nonzero determinant. The coefficient systems for the monic degree-2*m polynomials therefore converge. A root bound for monic polynomials with bounded coefficients bounds all rescaled roots. The roots are real and in the interval of orthogonality; after undoing the rescaling they lie in (A,B). The standard root-location fact is stated in [DLMF 18.2(vi)](https://dlmf.nist.gov/18.2#vi).

Set `h_L(t)=P_L(t^2)*exp(-L*(t^2-c)^2)`. Even degree makes P_L positive outside (A,B), so h_L is positive at all real cusp parameters and also at every purely imaginary parameter. Substitution x=t^2 gives exactly I_k(h_L)=0 for k<2*m. Its value at t_f is positive, permitting normalization. The quartic exponential gives rapid decay on each fixed horizontal strip, so admissibility is not limited to the real axis.

The corpus supplies genuine ingredients, not this actual-spectrum theorem: `OrthogonalMomentPolynomials.lean` defines the monic family and proves lower-degree orthogonality; `GaussianWindowMomentRescaling.lean` proves Gaussian rescaling and a bounded-density cooling limit. The shifted half-line measure, coefficient convergence, and actual cusp-spectrum application above were checked on paper, not in Lean. A prescribed finite set of imaginary residue zeros can also be imposed by a squared polynomial factor and incorporating it in the positive measure, provided t_f is not among those zeros.

Whole-route meaning: cusp positivity does NOT force the archimedean moment obstruction from full real-line positivity. Finite moment cancellation is possible. This construction alone says nothing about the signed arithmetic trace or constants uniform in m.

### Candidate AA: a uniformly controlled all-moment limit

[FAILED LIMIT, PAPER] Suppose normalized h_m as above had a common bound `abs(h_m(x+i*y))<=C*exp(-c0*x^4)` on a fixed strip containing t_f, with C,c0>0 independent of m. Local normal-family compactness gives a holomorphic limit h with h(t_f)=1. Dominated convergence passes every I_k to the limit. The finite signed measure on [0,infinity) with density `tanh(pi*sqrt(x))*h(sqrt(x))` has an entire Laplace transform, and all its moments vanish. The Laplace transform is identically zero; Fourier uniqueness makes h zero on the positive real axis, then throughout the strip. Contradiction.

Positive survivor: any normalized all-orders sequence must escape this common strip-decay bound. This is NOT a proof that its unweighted L1 norm or its Eisenstein cost must grow; candidate AD below specifically tests and rejects that stronger inference. Whole-route meaning: an infinite-order passage needs an explicit topology and tail control, not just separately vanishing moments.

### Candidate AB: cusp-only positivity with short wave support

[PAPER DERIVATION] Let h be real and even on the real line, Schwartz, with inverse Fourier transform supported in [-a,a], and suppose h>=0 at all real cusp parameters. There is a fixed a0>0 such that, for a<a0, any nonzero such h has `integral h>0`, even if h is negative between cusp parameters.

The actual source input is the cusp Weyl law with remainder `O(T/log(T))`, recorded in [Li--Sarnak, equations (1.2)-(1.4)](https://web.math.princeton.edu/sarnak/SarnakNumberPaper04.pdf). It implies that every interval (T,T+1] contains a real cusp parameter for all sufficiently large T. Thus the symmetric set of distinct real cusp parameters admits ordered Voronoi cells of uniformly bounded length D. No numerical eigenvalue or conjecture about simple spectrum is used.

Choose a fixed Schwartz reproducing kernel K with Fourier multiplier equal to one on [-1,1]. After scaling, `h=K_a*h` and `norm(h')_1<=a*norm(K')_1*norm(h)_1`. On a cell containing a sample s with h(s)>=0, `h_-(x)<=integral_[s,x] abs(h')`. Integration over cells yields

`integral h_- <= D*norm(h')_1 <= D*a*norm(K')_1*norm(h)_1`.

For small enough a the negative mass is strictly less than half the absolute mass. Hence `integral h>0`. In particular, a nonzero cusp-positive short-support response cannot have g(0)=0. This removes W's spatial nonnegativity hypothesis, within a possibly smaller support threshold.

Weighted version: write H(x)=h(x/a), M0=integral abs(H), M1=integral abs(x)*abs(H). Reproduction gives `sup abs(H)<=C*M0`; integrating over a sufficiently small fixed interval then gives `M0<=C'*M1`. Convolution with K' gives `integral abs(x)*abs(H')+integral abs(H')<=C''*M1`. The rescaled Voronoi cells have length at most a*D, so

`integral abs(x)*H_-(x) <= C*a*M1`.

Also `abs(x)*(1-tanh(pi*abs(x)/a))<=C0*a`. It follows that `I_0(h)>=a^(-2)*(1-C1*a)*M1`. Reproduction on a bounded complex strip bounds `abs(H(a*t_f))` by a constant times M1. Consequently normalization h(t_f)=1 forces `I_0(h)>=c_f/a^2` for sufficiently small a, without assuming positivity on the continuous spectrum. This extends Y's small-support diagonal cost to actual cusp-only positivity.

Positive survivor: quantitative comparison between the signed Plancherel integral and the absolute first moment for sufficiently short support. The full source-and-sampling argument remains paper-only. It does not exclude wider wave support.

### Candidate AC: the nonlinear trace grid has its own absolute cost

[PAPER DERIVATION] Fix N=p^n>=3 and define `u_k=2*arcosh(1+k/(2*N))`, k>=1. These are the positive hyperbolic trace-grid points. The spacing satisfies

`u_1^2<=4/N`,
`(u_(k+1)-u_k)^2<=1/(N*k)` for 1<=k<=N,
`(u_(k+1)-u_k)^2<=4/k^2` for k>=N.

Therefore the sum of squared gaps, including the initial gap, is `O((1+log(N))/N)`, uniformly in an upper cutoff. The split grid points are `2*d*log(p)` for 1<=d<=n. Their integer trace indices are isolated, and the first index k=1 is nonsplit for N>=3. Deleting isolated split nodes increases the squared-gap sum by at most a fixed factor, using `(x+y)^2<=2*(x^2+y^2)`.

If g is even, C1, compactly supported, and zero at all retained nonsplit nodes, integration of the distance-to-nearest-zero bound gives

`norm(g)_1 <= C*sup abs(g')*(1+log(N))/N`.

This includes the interval next to zero, where g(0) need not vanish, and the final interval ending at the boundary of support. For `h(t)=integral g(u)*exp(i*t*u) du`, support [-b,b], and `abs(h(t_f))=1`, Fourier inversion then gives

`integral abs(t)*abs(h(t)) dt >= c*exp(-b*abs(Im(t_f)))*N/(1+log(N))`.

This conclusion needs no spectral positivity. Combining it with AB, when b is fixed and sufficiently small, gives the same order lower bound for the SIGNED identity contribution of every cusp-positive exact nonsplit-grid annihilator. It covers signed g and g(0) nonzero, not merely V's sine-squared example.

Whole-route meaning: deleting the nonsplit terms under short fixed wave support cannot produce polynomial-in-n archimedean cost. Positive survivor: the exact nonlinear zero mesh controls an absolute spectral first moment. This is not a bound for the actual Hecke trace or eigenvalue. The proposed extension to a combined identity-plus-Eisenstein cost at arbitrary fixed support is not yet recorded as a theorem.

### Candidate AD: move corrections into high spectral gaps

[POSITIVE SURVIVOR, PAPER] The stronger claim suggested by AA, that arbitrarily many finite moment cancellations must incur large unweighted or low-weighted L1 cost, is false when the corrections are allowed to move to infinity. Here is a construction for every FIXED finite number K of moments. Its constants are not uniform in K.

Start with an even entire strip-Schwartz h0 positive on real and imaginary axes and normalized at t_f; for example a normalized `exp(-t^4)`. The Weyl law in the squared parameter x=t^2 has counting asymptotic x/12. It implies fixed-width empty intervals (c-d,c+d) in every sufficiently large interval [alpha*R,beta*R], for suitable fixed d>0 and any fixed 0<alpha<beta: otherwise uniformly smaller gaps would force a counting density greater than 1/12. Shrink the empty intervals to keep their endpoints outside the spectrum.

For a gap center c, use the two templates

`v_c^+(t)=exp(-L*(t^2-c)^2)`,
`v_c^-(t)=((t^2-c)^2-d^2)*exp(-L*(t^2-c)^2)`.

Both are nonnegative at all actual cusp parameters, including imaginary ones; the minus template is negative only when t^2 lies in the empty interval. Fix L so that `integral_R (v^2-d^2)*exp(-L*v^2) dv<0`. As c tends to infinity, substitution x=t^2 shows I_0(v_c^+) tends to a positive constant and I_0(v_c^-) to a negative constant. Normalize their absolute I_0 to one, calling the results w_c^+ and w_c^-.

Choose K separated intervals for c_j/R in a fixed positive compact interval. For odd j select the minus template at a gap center; for even j select the plus template. Then

`R^(-k)*I_k(w_(c_j)^sign) = sign*(c_j/R)^k + o(1)` for 0<=k<K.

The limiting coefficient system is a Vandermonde system. Its solution for right-hand side `(-I_0(h0),0,...,0)` has all coefficients strictly positive with this alternating choice of signs: the Lagrange coefficient at zero for the j-th ordered positive node has sign `(-1)^(j-1)`. Separation of the node intervals makes invertibility, positivity, and boundedness uniform in R. Perturbing to the actual moments and right-hand side `-R^(-k)*I_k(h0)` gives positive bounded coefficients a_j(R) for all sufficiently large R. Thus

`h_R=h0+sum_j a_j(R)*w_(c_j)^sign`

is positive at every cusp parameter and satisfies I_k(h_R)=0 for k<K exactly. Each correction has

`integral (1+abs(t))^epsilon*abs(w_(c_j)^sign(t)) dt = O_K(R^((epsilon-1)/2))` for 0<=epsilon<1.

It also tends to zero uniformly on each fixed complex compact set. Hence h_R(t_f) tends to one and division by that positive value gives exact normalization while retaining the moment zeros and cusp positivity. In particular, h_R tends to h0 in these low-weighted L1 norms despite having all K selected moments zero. Moment mass escapes to high parameters; this does not contradict AA.

The qualitative reciprocal-zeta growth needed to transfer the low-weighted estimate to the usual Eisenstein weight is supported by [Cully-Hugill--Leong, introduction and Corollary 4](https://arxiv.org/pdf/2312.09412). Only polylogarithmic growth is needed, not the paper's explicit numerical constants or verified finite zero heights. For the weight `abs(zeta(1+2*i*t))^(-2)`, the absolute correction cost tends to zero. This statement about a specified weight does not silently establish any missing normalization bridge in the corpus.

Whole-route meaning: finite archimedean moment cancellation can coexist with actual cusp positivity and a small continuous-spectrum correction. The fixed-gap construction's normalization explosion is not an intrinsic obstruction. This is one quantified family, not thousands of independent conjectures, and is not kernel-verified.

### Candidate AE: does the cheap correction remove the transition kernel?

[FAILED INFERENCE, PAPER] It does not. From the [Bessel series, DLMF 10.2.2](https://dlmf.nist.gov/10.2#E2), the Gamma recurrence and [DLMF 5.4.3](https://dlmf.nist.gov/5.4#E3), for real t and 0<x<=X one obtains

`abs(J_(2*i*t)(x)) <= exp(X^2/4)/abs(Gamma(1+2*i*t))`,
`abs(t*J_(2*i*t)(x)/cosh(pi*t)) <= C_X*sqrt(abs(t))`.

For the first inequality, the order-rising product has absolute value at least k! in the k-th series term. The second follows from `abs(Gamma(1+2*i*t))^2=2*pi*abs(t)/sinh(2*pi*abs(t))`. The value at t=0 is obtained by continuity. Consequently the forward transform B satisfies

`sup_(0<x<=X) abs(B_(h_R)(x)-B_(h0)(x)) <= C_X*integral sqrt(abs(t))*abs(h_R(t)-h0(t)) dt`,

which tends to zero by AD. After target normalization the same conclusion holds. Thus cancellation of any fixed finite list of archimedean moments leaves the Bessel transform unchanged on every fixed geometric interval in this construction. Whenever B_(h0) has a nonzero interval, R's absolute square-root-N majorant obstruction persists uniformly along R=R(N) tending to infinity. This is a lower bound for the absolute majorant, not for the signed arithmetic trace.

Positive survivor: a quantitative continuity estimate distinguishes moment cancellation at infinity from changing the actual kernel at c comparable to N. Whole-route meaning: the next attack must alter or directly control this transition contribution. Further finite moment cancellations alone are not evidence of a Ramanujan gain.

### Audit and next discriminating question

Z-AA resolve finite versus infinite moment cancellation; AB-AC constrain signed short-support exact filters; AD-AE supply a cheaper positive survivor and show precisely what it fails to change. No actual Hecke exponent improved and no Lean proof or falsification of the goal was produced. These are paper arguments with external spectral inputs, not formally closed no-go certificates. The 3,000-conjecture request remains incomplete; no count inflation is used.

The next discriminating question is whether a cusp-positive correction can change the Bessel kernel in the c-comparable-to-N range while controlling its continuous-spectrum cost and the remaining signed arithmetic sum. AE only excludes corrections small in the specified square-root-weighted L1 norm. It does not exclude corrections of bounded nonzero norm or an arithmetic cancellation argument.

Search `/tmp/rp_cusp_positive_moments_20260926s.json` completed nonpartially over 59,749 files; `/tmp/rp_cusp_sampling_20260926t.json` over 59,750. Retrieved Gaussian, orthogonal-polynomial and Fourier-derivative source statements were distinguished from the missing actual spectral applications. No complete Lean chain for Z-AE was returned or claimed. Sessions 85122 and 46931 exited. No Lean process, numerical experiment, added axiom, or heartbeat change was used.

### Candidate AF: polynomial-cost escaping corrections can change the transition profile

[FAILED BRIDGE, PAPER] AE assumed that the square-root-weighted L1 correction tends to zero. Allowing that norm to stay bounded, or even to grow polynomially with the lowest spectral frequency, still does not permit cancellation of a fixed nonzero transition profile against smooth tests.

Write `D=x*d/dx`, `A=-D^2-x^2`, and let phi be smooth with compact support in (0,infinity). The [Bessel equation, DLMF 10.2.1](https://dlmf.nist.gov/10.2#E1) gives

`A J_(2*i*t)(x)=4*t^2*J_(2*i*t)(x)`.

The operator A is formally symmetric for dx/x on compactly supported tests. Iterating integration by parts gives, for t nonzero,

`integral J_(2*i*t)(x)*phi(x) dx/x = (4*t^2)^(-m)*integral J_(2*i*t)(x)*(A^m phi)(x) dx/x`.

There are no boundary terms. The pointwise kernel bound in AE now implies the following quantitative positive statement. For any integrable spectral correction q supported in abs(t)>=T>=1, put `Mhalf(q)=integral sqrt(abs(t))*abs(q(t)) dt`. Then

`abs(integral B_q(x)*phi(x) dx/x) <= C_(phi,m)*T^(-2*m)*Mhalf(q)`.

Fubini is justified by AE on the fixed compact support of phi. Thus if Mhalf(q_T)=O(T^a) for any fixed a, B_(q_T) tends to zero against every such phi. The same conclusion holds for corrections with a nonzero low-frequency tail if that tail's Mhalf tends to zero and the high-frequency part obeys the stated bound.

If B0 is a fixed nonzero continuous profile on a compact interval, choose phi there with `integral B0*phi dx/x` nonzero. Uniform approximation B_(q_T) -> -B0 on that interval would contradict the preceding limit. More quantitatively, once the pairing cancels at least half its nonzero baseline value, Mhalf(q_T)>=c_(phi,m)*T^(2*m) for every fixed m. This is superpolynomial growth in the lowest spectral frequency; constants depend on m.

Whole-route meaning: scaling the escaping-gap corrections by a polynomial does not fix AE. This rules out smooth-profile cancellation, not cancellation at a finite arithmetic grid, not an oscillatory correction correlated with Kloosterman signs, and not a family without spectral escape. No cusp-positivity assumption was used, so adding it cannot rescue this particular bridge. The exact integration-by-parts estimate is the positive survivor. Its imaginary-order Bessel application is not Lean-verified.

### Candidate AG: delete each modulus separately with a Gaussian-class weight

[FAILED BRIDGE, PAPER] Exponential spectral decay puts the forward Bessel transform in a bounded holomorphic class where the reciprocal modulus grid is a uniqueness set. This also rules out deleting individual arithmetic summands while leaving a nonzero Bessel transform.

Assume

`Mpi(h)=integral sqrt(abs(t))*exp(pi*abs(t))*abs(h(t)) dt < infinity`.

The same Bessel series as in AE, now using the principal branch at Re(z)>0, gives for abs(z)<=X

`abs(t*J_(2*i*t)(z)/cosh(pi*t)) <= C_X*sqrt(abs(t))*exp(2*abs(t)*abs(arg(z)))`.

Since abs(arg(z))<pi/2, the forward transform B_h is holomorphic on the right half-plane and uniformly bounded on every right half-disc. Local dominated integration establishes holomorphy; the bound is `abs(B_h(z))<=C_X*Mpi(h)`. Every quartic-Gaussian weight used in Z or AD satisfies this condition individually. No uniform bound over those families is asserted.

For A>0, suppose B_h(A/c)=0 for every sufficiently large positive integer c. If B_h(r) is nonzero for some r>0, restrict B_h to the disc of radius r centered at r. Under z=r*(1+w), the sample zeros have disk coordinates

`w_c=A/(r*c)-1`, with `1-abs(w_c)=A/(r*c)` for sufficiently large c.

Their Blaschke defects have divergent sum. A bounded nonzero holomorphic disk function cannot have these zeros, a source-level theorem already available as `RHTower.summable_one_sub_norm_of_bounded_analytic_zeros_openDisk` in `SectorPrimeZeroUniqueness.lean` and used by `RHTower.not_bounded_analytic_zero_on_all_frequencyCayley` in `FrequencySectorBlaschkeCompleteness.lean`. Consequently B_h vanishes on the positive real axis, then on the right half-plane by analytic uniqueness. The application here is a paper argument, not an invoked Lean theorem.

The arithmetic refinement needs only prime moduli. For any prime q and integer frequencies m,n, the classical sum S(m,n;q) is nonzero. Indeed let zeta be a primitive q-th root and let a_j count units u with `m*u+n/u=j mod q`. If `sum_(j<q) a_j*zeta^j=0`, cyclotomic irreducibility forces all integer coefficients a_j to be equal. But their sum is q-1, which cannot equal q times an integer. This precise coefficient-equality fact is present in the inspected mathlib source `IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int` in `RingTheory/Polynomial/Cyclotomic/Roots.lean`. No quantitative lower bound for S follows.

Therefore, for fixed N>=1, termwise deletion

`S(N,N;c)*B_h(4*pi*N/c)=0` for all sufficiently large c

forces B_h to vanish identically: the prime sums are nonzero and the reciprocal primes have divergent sum. The same proof allows deletion of finitely many primes. This is stronger than requiring B_h itself to vanish at every modulus, but much weaker than ruling out cancellation BETWEEN moduli. It is not a statement that h=0, a lower bound for a signed trace, or a Ramanujan obstruction.

Positive survivors:

- Reciprocal integer samples, and even reciprocal prime samples alone, determine this bounded-holomorphic Bessel transform uniquely.
- The finite form is quantitative. If distinct zeros A/c map into abs(w)<=rho<1 in the disc centered at r, finite Blaschke division gives `abs(B_h(r))<=C_(2*r)*Mpi(h)*rho^(number of zeros)`. Normalization at this geometric point therefore forces an exponential-in-count complex-strip cost. Normalization h(t_f)=1 does NOT by itself give such a lower bound for B_h(r).
- The angular threshold matters. For every theta<pi/2 and A>0, choose L>pi*A*tan(theta). The function `exp(-L/z)*sin(pi*A/z)` is nonzero, holomorphic and bounded on abs(arg(z))<theta, yet vanishes at every A/c. The bound follows directly from `-L*cos(arg(z))+pi*A*abs(sin(arg(z)))<0`. Thus boundedness only on a narrower sector cannot justify the same uniqueness argument. This is a counterexample in the analytic class, not a constructed cusp-positive Bessel transform.

Whole-route meaning: Gaussian-class exact termwise deletion is not a new route. Viable alternatives must retain signed cancellation, use approximate deletion with its norm cost accounted for, or leave this exponential spectral class. AF additionally prevents a polynomial-cost high-frequency correction from cancelling a fixed smooth transition profile. Neither result supplies the missing signed arithmetic estimate.

### Audit after AF-AG

Deep mechanism search `/tmp/rp_transition_interpolation_20260926u.json` completed with nonpartial retrieval over 59,755 files; its proposed theta-gap chain was unrelated to the required Bessel estimate and was not used. The attempted `--mode method` command was rejected because supported modes are deep, hybrid and lexical; it launched no research job. The corrected deep mechanism search `/tmp/rp_blaschke_uniqueness_20260926v.json` returned partial results with the same inventory coverage. Its suggested harmonic-divergence chain was not verified or used. Direct source inspection found the applicable bounded-zero and cyclotomic coefficient statements instead.

The inspected `KloostermanPhysicalResidueModulusBilinear.lean` retains the signed modulus sum exactly and proves a fixed-modulus baseline; it explicitly leaves the Kuznetsov--Deshouillers--Iwaniec estimate for later. No arithmetic saving was extracted from that identity. AF-AG remain paper-level bridge tests with the exact Bessel/analytic applications unformalized; the no-go closure requirement has not been discharged in Lean. No improved actual Hecke exponent, unconditional target certificate, or completed 3,000-conjecture catalogue exists. Owned search sessions 16288 and 1682 exited, and no Lean process was launched in this continuation.

## Signed arithmetic continuation

The previous turn changed the next action by excluding specific filter mechanisms; it was research progress, not a formal advance. The present target is the actual signed modulus sum. Existing coprime collision estimates were inspected with their energy factors retained. `KloostermanGlobalCollisionCoprime.lean` bounds collisions by twice the squared aggregate source energy, and its large-sieve corollary retains the classical source-length plus modulus-squared scale. `KloostermanCoprimeProductPeriodCompletion.lean` supplies exact cancellation over a product period, not over a short arbitrary interval. These are genuine ingredients, not the missing individual diagonal estimate.

### Candidate AH: average the exponent over a complete multiplicative orbit

[FAILED APPLICATION, PAPER] For an odd prime q and the quadratic character chi, elementary additive-character orthogonality gives the positive identity

`(1/(q-1))*sum_(a in F_q^*) S(a,a;q) = (1+q*chi(-1))/(q-1)`.

To check it, exchange the sums. The inner sum over a is q-1 when u+1/u=0 and -1 otherwise; the number of such units u is 1+chi(-1). Thus complete nonzero-residue averaging really does reduce the square-root-sized individual baseline to a bounded average. If p generates F_q^*, averaging S(p^k,p^k;q) over a complete period yields exactly this expression. No primitive-root assertion for any family of q is assumed.

The transition weight does not provide that period. A fixed block B supported in [a,b] inside (0,infinity) makes B(p^k/c) nonzero only for k in an interval of length log(b/a)/log(p), independently of c. In contrast, for q not dividing p, `r=ord_q(p)` satisfies `q<=p^r-1`, hence `r>=log(q+1)/log(p)`. At q comparable to p^n this period grows at least linearly with n. The complete-period identity cannot be applied to the bounded-width exponent window. This is failure of that inference, not a proof that the short weighted orbit has no cancellation.

Positive survivor beyond the displayed mean: if `abs(B(x))<=C*min(x^a,x^(-b))` with a,b>0 and ell=log(c)/log(p), the sum of abs(B(p^k/c)) over abs(k-ell)>=L is at most

`C*(p^(-a*L)/(1-p^(-a)) + p^(-b*L)/(1-p^(-b)))`.

Each side is a geometric series. This is an absolute kernel-tail bound for one modulus, not a uniform negligible bound after summing all moduli. The remaining short-orbit cancellation is unproved.

### Candidate AI: short-order moduli already have an acceptable absolute bound

[DERIVED BRIDGE, KERNEL-VERIFIED AS DESCRIBED BELOW] Fix an integer p>=2 and a finite order-ratio cutoff k. Define U(p,R) as the union, over 1<=r<=R, of the positive divisors of p^r-1. Every modulus with a positive multiplicative period at most k*n belongs to U(p,k*n). For every epsilon>0,

`card U(p,k*n) <= C_(p,k,epsilon)*(p^n)^epsilon`.

Proof: the divisor bound gives `card U(p,R)<=R*C_delta*(p^R)^delta`. Set delta small enough in terms of k and epsilon and absorb the factor n into the remaining positive exponential exponent. The r=0 term may be included because the positive-divisor finset of zero is empty. No primality of p is required, and k=0 is harmless.

The elementary Kloosterman bound `abs(S(m,l;c))<=phi(c)<=c` then proves an actual arithmetic estimate: for ANY subset Q of these short-period moduli and ANY weights satisfying `abs(w_c)<=1/c`, the absolute summand mass, and hence the signed sum, is O_((p,k,epsilon))((p^n)^epsilon), uniformly in the two integer frequencies m,l. Thus this part of the coprime trace can be removed at an acceptable subpower cost without invoking Weil. On a fixed Bessel transition block, its bounded kernel changes only the constant.

This is stronger for formal implementation than the initially considered prime-only counting argument: it includes composite moduli and needs only the corpus's elementary Kloosterman bound and proved divisor bound. A sharper O(N^(-1/2+epsilon)) transition estimate follows on paper from the full classical Weil bound, but is not the theorem selected for Lean and will not be claimed kernel-verified.

Whole-route meaning: bounded multiplicative-order ratio is not where a superpolynomial prime-power trace obstruction can remain. The complement has order/n unbounded and still requires signed cancellation. Controlling this subset alone does NOT improve an actual Hecke exponent or prove Ramanujan. This is one derived arithmetic bridge, not multiple conjectures obtained by varying p,k or epsilon.

### AI formal certificate and scope audit

Installed `formal/GaloisForLFunctions/RHTower/Sieve/KloostermanShortOrderModuli.lean`, imported by the existing RHTower umbrella. The implementation follows the corpus convention that index q denotes modulus q+1. Its four public theorems are:

- `mem_shortOrderModuli_of_dvd`: every positive period r<=R with q+1 dividing p^r-1 enters the finite set.
- `card_shortOrderModuli_le`: explicit divisor-bound estimate at a finite cutoff R.
- `shortOrderModuli_subpower`: for fixed p>=2, k and epsilon>0, one positive constant works for EVERY n.
- `shortOrder_kloosterman_subpower`: the same uniform constant bounds the sum of absolute weighted classical Kloosterman summands, for every subset of the short-period set, all integer frequencies, and every weight with norm at most 1/(q+1).

Thus the result is an unconditional arithmetic theorem with domain and weight conditions, not a theorem assuming an unproved cancellation estimate. It is NOT a closed proof of the user goal: the large-order complement and its connection to an improved actual Maass eigenvalue bound remain unresolved. The stronger Weil-based decay rate discussed above and AH's orbit-mean identity were not formalized in this module.

Validation: the full scratch proof passed `lake env lean /tmp/rp_short_order.lean` after one ambiguous natural-to-real cast was explicitly typed. No heartbeat or recursion limit was changed. Final targeted command `lake build GaloisForLFunctions.RHTower.Sieve.KloostermanShortOrderModuli` passed; no full or umbrella build was run. Imported-module audit `lake env lean /tmp/rp_short_order_audit.lean` passed: the definition and all four theorems depend only on propext, Classical.choice and Quot.sound. No added axiom or numerical experiment was introduced; arithmetic proof steps use ordinary kernel-checked tactics.

`scripts/formal_tools.py lint` exited 1: its sole reported error was the unrelated module `GaloisForLFunctions.RHTower.XiSymmetricDiscIndexParity` being unreachable from the RHTower umbrella; it also reported existing large-file warnings. That module was not changed. Do not report a clean global lint gate. Scoped whitespace checking passed. Owned scratch, build, audit and lint sessions all exited.

Search `/tmp/rp_signed_modulus_20260926w.json` completed nonpartially over 59,757 inventoried files and `/tmp/rp_prime_power_orbit_20260926x.json` over 59,759. Suggested symmetry and expansion chains were not mistaken for cancellation bounds. The [2025 Blomer--Risager--Shparlinski paper, Theorems 1.1 and 1.3](https://arxiv.org/pdf/2411.17823) supplies averaging over arithmetic frequencies; those statements do not supply an individual diagonal prime-power estimate. The [Sarnak--Tsimerman formulation](https://web.math.princeton.edu/sarnak/LinnikSelbergApr07.pdf) identifies a stronger signed-modulus conjecture, not an unconditional input available to this proof.

The next unresolved arithmetic range is the complement of every fixed bound ord_c(p)<=k*n. The new certificate isolates that range but does not control it. No actual Hecke exponent improved, no Maass counterexample exists in this work, and the request for 3,000 conjectures remains unfinished. Goal remains active.
