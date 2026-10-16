# SZ: universal Gamma source core

Status: formalized and directly verified in Lean, 2026-10-16. Source of truth: current Lean corpus.

Contribution: the literal finite Gamma packets form a common core for every positive parameter family. Their joint graph closure equals the simultaneous cancelled-equation graph. In particular, the actual two-leg synthesis has minimal = maximal, with no extra source-domain or common-core hypothesis. Previous closed unbounded Gamma synthesis is established input, not this task's contribution.

Completed work:
1. Search current Lean corpus for actual Ward/Robin source obstructions and cross-route mechanisms.
2. State concrete conjectures, attack them, record failures and positive survivors.
3. Prove the surviving structural statement on paper, then formalize the exact result.
4. Direct foreground Lean audit, axiom audit, umbrella wiring, lint and cleanup. No full builds.

Initial evidence: the literal Gamma-completed Ward wall is prime minus regular screw continuum (`SuzukiWardAtomicContinuousLightWeld`). Negative cross interactions require comparable lags (`SuzukiCompletedWardCancellativeBand`). The actual aperture Wronskian retains physical-shell and metric-response terms (`CCMSuzukiCrossApertureProjectiveWronskian`). Affine sewing preserves common far-prime channels (`SuzukiAffineSewnWeilRobinFarTailFactorization`). These identities do not discharge the remaining signed source law.

Conjecture ledger:

1. Far regular mass or affine sewing might remove the signed Ward channel. Rejected by the exact current Lean laws above; no duplicate theorem added.
2. Direct prime cutoffs might automatically approximate every solution of the cancelled Gamma row equations. Not justified: the uncancelled rows are unbounded. Output tail shifts acquire Jacobi normalization ratios, so ordinary coordinate convergence does not give graph convergence.
3. **Proved: minimal equals maximal for the actual two-leg Gamma source.** The graph closure of all literal finite packets equals the closed cancellation-equation graph. This removes the gap between these two source realizations without imposing a source regularity hypothesis.

Paper mechanism for conjecture 3:
- Write the surviving tail coefficients as c_j = sqrt(normalizedCentralBinom(j+3)); their squares satisfy the exact central-binomial recurrence.
- The identity sum_{j=0}^M a_j = (2M+1)a_M, together with monotonicity of a_j, gives sum of any N consecutive coefficients ending at M at most 2N*a_M.
- Therefore the mean squared norms of normalized backward tail shifts is uniformly controlled. Finite tails vanish under sufficiently large shifts; approximation by finite tails then shows these mean squared norms tend to zero. Select arbitrarily large shifts whose norm tends to zero.
- On the arithmetic side use D_n(pe)=1-r(pe)^n. Since p*(1-r) <= 2, p*D_n <= 2n. Thus the actual bounded feature operator applied to the bounded multiplier p*D_n gives a pair in the minimal graph, by continuity from finite packets.
- Telescope the cancellation equations: the output-tail discrepancy of this pair is exactly the normalized backward shift. D_n*u tends to u by square-summable domination. The first surviving coordinate is fixed continuously by the first cancelled row, so it converges too.
- Hence every maximal graph pair is a limit of minimal graph pairs. The reverse inclusion is already proved. No extra output/source hypotheses remain in the graph equality.

This is a domain/completion theorem, not the unresolved signed prime--polar--Gamma Ward comparison. The individual graph equality now passes direct Lean audit.

Formal status: `SuzukiGammaJacobiTailCore.lean`, `SuzukiCausalDepthGammaSourceRegularization.lean`, `SuzukiCausalDepthGammaMaximalSource.lean`, `SuzukiCausalDepthGammaCesaroSource.lean`, and `SuzukiCausalDepthGammaJointCore.lean` pass direct `lake --old env lean -j 1` audits and are wired into `RHTower.lean`. Together they prove the exact tail identity, admissible regularization, minimal = maximal, full-sequence Cesàro graph convergence, and the universal joint core. No umbrella build was run.

4. The same literal finite source packets form a **joint graph core for every finite family of Gamma parameters**. The radial input multiplier is parameter-independent. The first paper proof summed the finitely many nonnegative output-tail energies and selected one sequence of good shifts. This finite-family construction was superseded by the stronger full-sequence theorem in step 5, which proves this result too. The common-domain/completion ambiguity in mixed-aperture pairings is removed.

5. **Proved: Cesàro averages of the radial regularizers converge in every Gamma graph norm along the full sequence.** The mean tail energy tends to zero. The cancelled first row controls the mean squared first-coordinate error by that tail energy and the already convergent input. Jensen's finite-sum inequality then makes the norm of the mean full output error tend to zero. This gives one explicit parameter-independent approximation scheme, and a common finite-packet core for arbitrary parameter families in the product graph topology. It does not assert uniform convergence over an unbounded parameter set. The exact result is formalized in the Cesàro and joint-core modules.

Dependency-closed paper proof of conjecture 5:

For a maximal graph pair `(u,v)`, put `e_n = v - B_n u`, where `B_n` is the bounded literal source synthesis after multiplication by `p(1-r^n)`. Put `b_j = |v_(j+1)|^2`, and let `E_n` be its Jacobi tail energy. The exact tail identity and vanishing arithmetic output coordinates give `||e_n||^2 = |e_n(0)|^2 + E_n`, and `|e_n(1)|^2 <= E_n`. The first cancelled row gives `c_1 e_n(0) = q_n + c_0 e_n(1)`, where `q_n = <R_0,u-D_n u> -> 0`. Consequently,

`c_1^2 ||e_n||^2 <= 2|q_n|^2 + (2c_0^2+c_1^2) E_n`.

Here `c_1>0`. The means of both terms on the right tend to zero: the first by Cesàro convergence, the second by the proved Jacobi tail theorem. Hence the mean squared full error tends to zero. Finite Cauchy--Schwarz and the norm triangle inequality give `||N^(-1) sum_(n<N) e_n||^2 <= N^(-1) sum_(n<N) ||e_n||^2`, so the averaged output converges to `v`. The averaged input converges to `u` by Cesàro convergence of `D_n u`.

For an arbitrary parameter family `(h_j,a_j)`, every regularized pair `(D_n u,(B_n(h_j,a_j)u)_j)` belongs to the joint finite-packet closure: its map from `u` is continuous into the product, and every coordinate basis input maps to a scalar multiple of the same literal joint column. Finite averaging preserves this closed linear space. The averaged inputs converge to `u`, and the outputs converge componentwise by the preceding argument, hence in the product topology. Closedness gives inclusion of the entire simultaneous equation graph in the joint finite-packet closure. The reverse inclusion follows because every literal column satisfies each continuous cancelled equation. This proves equality for arbitrary parameter families, and in particular for the full positive parameter plane.

The source regularizer is explicit and independent of both the parameters and the output: on arithmetic inputs, for `N>0`, its multiplier is `1 - N^(-1) sum_(n<N) r^n`. Infinite parameter families use product topology, not a uniform norm. A sequence of regularized sources is proved; finite-packet approximation of an uncountable joint graph is a closure/net statement, not an asserted single sequence of finite packets.

Capstones:
- `RHTower.suzukiGammaTwoLegClosedGraph_eq_equationGraph`.
- `RHTower.tendsto_suzukiGammaCesaroSynthesis`.
- `RHTower.suzukiGammaJointClosedGraph_eq_equationGraph`.
- `RHTower.suzukiGammaUniversalSourceCore`, with no hypotheses or parameters, specializes the joint equality to the entire positive parameter plane.

Verification:
- Each of the five modules passed foreground `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.olean GaloisForLFunctions/RHTower/<Module>.lean`.
- A separate `/tmp` audit through `lake --old env lean -j 1` checked six main declarations. Every dependency set is exactly `[propext, Classical.choice, Quot.sound]`. No added axioms or open analytic premises.
- All five imports appear in `RHTower.lean`. No full or umbrella builds; no heartbeat increases; no numerical experiments.
- `git diff --check` passed for the task files.
- `scripts/formal_tools.py index` refreshed `formal/LEAN_API.md`, `formal/LEAN_GAPS.md`, `formal/LEAN_OVERVIEW.md`, and the Lean search index. Research scratch files were removed after audit.
- Repository-wide `scripts/formal_tools.py lint` ran and was rerun after index refresh. Both runs report only the same six errors, all unrelated unwired modules: `MobiusDivisorCompactClockSource`, `MobiusDivisorCompactClockTailSeparation`, `PaperThetaNativeMeyerCompleteness`, `PaperThetaNativeQuantileComparison`, `PaperThetaNativeRootTransport`, and `XiNewtonDiscCurvature`. None of the five new SZ modules is reported.

Remaining boundary: this does not prove the signed prime--polar--Gamma Ward comparison, and does not place the non-square-summable coherent sharp source into this Hilbert space. The removed obstruction is the minimal/maximal and simultaneous-core ambiguity for the actual Gamma Hilbert source operators.
