# Evidence

## Corpus search
- `research 'half integer counting boundaryMeasure' --module Weil --budget-seconds 60`: complete hybrid search, no lexical hits, source-only receiver/measure candidates; older-generation coverage snapshot, semantic coverage not measured.
- `research 'canonical Weil spectral measure quantization monodromy integer mass' --mode deep --budget-seconds 90 --json`: partial, pending coverage; no useful proof ideas or ingredient sets. Available candidate/source rows inspected. Broad spectral matches were mostly irrelevant.
- `research 'interval mass Poisson boundary limit primitive phase' --module Weil --budget-seconds 60 --json`: complete; found fixed-width counting identities, local mass bounds and Poisson representation; no shrinking-width interval theorem located.
- `research 'Stieltjes inversion Poisson interval measure' --budget-seconds 60 --json`: complete; finite-measure Poisson/Stieltjes and unrelated probability Poisson results. No direct canonical interval inversion located. Absence in these searches is not a theorem of absence.
- Exact `rg` checks in Weil modules for interval/phase boundary limits; no identical theorem found.
- `research 'Weil positive L-data integrality Booker degree' --budget-seconds 60 --json`: complete; no source quantization producer located.
- `research 'Weil entire meromorphic completion square diffuse' --budget-seconds 60 --json`: complete; generic meromorphic-completion residue receiver still requires the continuation germ. No canonical-source detector located.
- `research 'boundaryMeasure singular absolutely continuous diffuse Weil' --module Weil --budget-seconds 60 --json`: complete, generation 1276396; canonical measure, atom comparison, supplied atomic-series and supplied-decomposition results located. No general singularity producer located. The new interval-phase theorem is already discoverable by research search.
- `research 'canonical Weil measure singularity Lebesgue decomposition arithmetic discrete Fourier support' --mode deep --budget-seconds 90 --json`: complete, generation 1276448. Proposed ingredient set was ordinary Lebesgue decomposition; no proof ideas. Candidate and source-argument rows inspected; no arithmetic density-vanishing argument located. Compiler coverage mostly pending/source-only; not a certification of candidate applicability.
- `research 'two Weil positive inputs finite coefficient perturbation difference rigidity coercive' --module Weil --budget-seconds 60 --json`: partial, no candidate/source rows. Broadened with lexical `coercive --module Weil --any` and exact source `rg`; read `WeilLinearTwistQuantization.lean:977` and checked the Λ-based perturbation statements.
- `research 'Weil positive completed primitive univalent Noshiro Warschawski' --budget-seconds 60 --json`: complete; no relevant primitive/reflection theorem among returned candidate/source rows. No absence claim beyond this search.
- `research 'Weil producer theta Mellin functional equation boundary reflection completed exponential' --module Weil --budget-seconds 60 --json`: complete, generation 1276475. Found `OddWeilFunctionRigidity.coeffTheta_weil_defect_relation` and `weil_defect_rigidity`. Read the structure and theorem: odd extension alone does not glue across the critical line; the latter receiver additionally requires a holomorphic transformed defect and vanishing radial residues. Preserve these obligations in the next source cycle.

## Existing declarations read
- `HalfIntegerMassRigidity.vonMangoldt_and_riemannHypothesis_of_half_integer_counting`: full-measure endpoint receiver, not a producer.
- `WeilSpectral.ofReal_re_weilContinuation_eq`: canonical Poisson law throughout Re s>1/2.
- `WeilSpectral.integrable_inv_one_add_sq`: weighted integrability.
- `WeilSpectral.tendsto_mul_re_weilContinuation_atom`: exact singleton radial extraction.
- `WeilSpectral.tendsto_log_norm_reciprocalZeta_div_log`: arbitrary atom equals reciprocal producer's radial exponent; fractional exponents not excluded.
- `WeilSpectral.setIntegral_re_weilContinuation_eq`: fixed width 3/2 count from 0 to T.

## External primary-source audit, 2026-10-07
- Favorov, [Generalized Fourier quasicrystals, almost periodic sets, and zeros of Dirichlet series](https://arxiv.org/abs/2311.02728), 2023. Opened abstract: unit zero-counting masses and bounded spectrum are part of its setup. Does not supply canonical Weil mass quantization.
- Perelli, [Converse theorems: from the Riemann zeta function to the Selberg class](https://arxiv.org/abs/1605.02354), 2016/2017. Opened authoritative survey; supports parent-theory audit of converse-theorem direction.
- Favorov, [Application of methods of quasicrystals theory to entire functions of exponential growth](https://arxiv.org/abs/2504.03365), 2025. Opened record; investigates zero measures of entire functions, not construction of a single-valued canonical Weil determinant.
- Gesztesy–Tsekanovskii, [On Matrix-Valued Herglotz Functions](https://arxiv.org/abs/funct-an/9712004), discovered as parent theory for measure inversion. Full theorem audit still pending.
- Booker, [L-functions as distributions](https://arxiv.org/html/1308.3067), Definition 1.3(A3): discrete spectral support and finitely many noninteger masses are hypotheses. Its classification therefore cannot supply the missing quantization without first establishing those hypotheses.
- Suzuki, [Weil's quadratic form via the screw function](https://arxiv.org/html/2606.09096v1), June 2026 posting, displayed August 24 revision. Read Theorem 1.5 and Corollary 1.6: finite-aperture self-adjoint extensions have real characteristic zeros; the global limiting identification is conjectural. Does not derive arbitrary canonical Weil mass quantization. Our inference: finite-aperture eigenvalue multiplicities cannot be substituted for canonical spectral weights without a proved identification and limit.
- Suzuki, [On the Hilbert space derived from the Weil distribution](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/on-the-hilbert-space-derived-from-the-weil-distribution/FD33EBD117A6B448053450DD8D62ADB6), November 2025. Read model-space/de Branges setup: innerness of the Xi quotient is under RH; Clark masses depend on the derivative of the inner function, not solely eigenvalue multiplicity. This does not produce innerness for an arbitrary arithmetic input.

## Tool limitations / validation
Serena symbol retrieval attempted for `integrable_inv_one_add_sq`; returned “path is ignored” for the Lean file. Use source reads and Lean name probes; do not modify Serena project configuration.

Successful foreground commands, from `formal/`:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationKernel.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationKernel.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationBoundaryPhase.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationBoundaryPhase.lean
lake --old env lean GaloisForLFunctions/RHTower/WeilWorkQuantizationBoundaryPhase.lean
lake --old env lean /tmp/wp04_audit.lean
```

Final direct leaf and scratch audit exited 0. Scratch audit checked used mathlib names and printed axioms for `intervalPhaseKernel_le_weight`, `tendsto_integral_intervalPhaseKernel`, `setIntegral_re_weilContinuation_interval`, `tendsto_re_weilContinuation_interval`, `exists_fullMeasure_interval_phase`, and `tendsto_exp_four_mul_interval_phase`: only `propext`, `Classical.choice`, `Quot.sound`. No added axioms or heartbeat changes. Audit output retained in `lean-audit.txt`.

`scripts/formal_tools.py lint` exited 1: unreachable `WeilWorkDeficitRecovery`, `WeilWorkHigherDenominatorCentralTest`, `WeilWorkPBAPNullRepair`, `WeilWorkSingularArithmeticSharpReciprocal`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`; existing large-file warnings. These are outside WP04 write scope. No WP04 reachability/proof-debt error reported. Own imports added to `RHTower.lean`; no umbrella build. `git diff --check` passed for that file.

No numerical computations. No full builds. No commits or pushes.

## Theta-defect source audit, 2026-10-07

Additional research searches inspected candidate lemmas and source arguments:

- Theta-defect deep search: partial; useful source hit `coeffTheta_weil_defect_relation`, no usable proof ideas. Exact source reads supplied the dependency audit.
- `Weil positive conductor lower bound constant Herglotz density`: complete; no general density-floor exclusion found among returned results.
- `Weil positive coefficient square sum logarithmic bound variance`: complete; found existing primitive-set/dyadic mean-square estimates and log-square deviation rigidity.
- Follow-up dyadic search: complete; exact proposed star-resonator inequality already proved in `WeilPrimitiveSetMeanSquare.lean`.
- `Weil positive uniform density Dirac comb prime powers square root perturbation`: partial; finite/countable perturbation and lacunary rigidity hits. Those compare with Λ and do not establish rigidity between two arbitrary cone inputs. No proved comb deformation or contradiction obtained.
- `canonical completed exponential outer factor boundary modulus integer Dirichlet support inner function`: partial; no applicable source innerness theorem among inspected candidate/source rows. Exact `rg` did not find an outer-factor argument in the Weil files searched. This is limited search evidence, not an absence theorem.

Exact source findings:

1. `OddWeilFunctionRigidity.coeffTheta_weil_defect_relation` gives the theta defect; `weil_defect_rigidity` requires its radial residues to vanish. Oddness across the line is not analytic continuation across it.
2. `WeilDefectBohrZetaLaw.lean:148`, `tendsto_mul_weilLaplace_bohr`, computes the radial residue at each positive integer from `(1 ∗ (lam − Λ))(n) + 2β`. It retains continuation, summability and the base radial limit. The spectral-measure version at line 291 also has explicit `SpectralMeasureData`; do not silently substitute arbitrary canonical μ without paying its support/data conditions.
3. `WeilHerglotzPhaseLockRigidity.lean:319–323` divides the completed function by `s(s−1) Γℝ(s)`. Its exponential Gamma decay is cancelled in this normalization. `exists_poly_bound_lineG` at line 391 gives a polynomial bound; it does not give the required signed radial cancellation.
4. `ZetaMassSublinearRigidity.lean:155`, `norm_atomLaplace_le_decay`, bounds the atom transform by `(3/2)|ζ(1/2+iu)| |τ|^(−1/2) exp(−|u| Re τ/|τ|)`. At `τ = ε + i n`, fixed `n ≥ 1`, this is not a uniform integrable majorant as `ε → 0`. The spectral tail cannot be discarded. `HamburgerTwistedRadialDefect` already permits signed cancellation; another absolute-value receiver would not advance that frontier.
5. `WeilPrimitiveSetMeanSquare.lean:43,295` already proves the primitive-set star bound and the dyadic bound from positivity. The latter allows square mass of order `N log² N`; the deviation hypothesis of `WeilFullConeLogSquareMassRigidity` requires polylogarithmic square mass. No conversion was proved.

Verdicts: the claim that exponential Gamma decay survives the displayed normalization is **FALSE**; this kills that shortcut, not the source conjecture. The source conjecture **SURVIVES PRELIMINARY ATTACK** and remains unproved. The star mean-square conjecture is **REDISCOVERED**. Positive survivors are the existing damped transform bound, exact arithmetic residue law, and signed radial receiver, already formalized in the cited modules. No new theorem is claimed from these audits. The density-comb idea was exploratory and has no completed proof.

Primary-source follow-up: Kaczorowski–Molteni–Perelli, [A converse theorem for Dirichlet L-functions](https://sites.unimi.it/molteni/research/papers-pdf/23-molteni-A_converse_theorem_for_Dirichlet_L-functions.pdf), Comment. Math. Helv. 85 (2010), 463–483, introduction and hypotheses (i)–(iii). Opened the primary PDF: analytic continuation and the functional equation are supplied, not consequences of a general positive Weil measure. This audit therefore supplies no source quantization. The Miller–Schmid distribution paper's publisher page returned 403; the Oliver repository page returned no readable theorem text; neither was treated as a verified theorem source. The measures-with-locally-finite-support primary page presented a browser check, likewise no theorem audit.

No source code changed in this cycle, so the previous successful WP04 leaf audits were not rerun. Search processes exited before their scratch outputs were cleaned up. The exact conjecture and unresolved moving-tail step are retained on the working card.

## Arbitrary finite remainder cycle, 2026-10-07

Research searches: signed-tail query returned partial coverage and mostly unrelated candidates; finite atomic-tail and sign-change queries completed; sharp-PNT query completed; finite-measure-remainder deep query returned partial coverage. Inspected candidate/source rows and exact source declarations rather than treating missing hits as a nonexistence theorem.

Exact query strings, in that order:

1. `signed radial theta defect spectral tail cancellation arithmetic Weil positive` (deep).
2. `producer Dirichlet coefficients mean square critical line fractional spectral finite total mass` (hybrid).
3. `Weil positive sign changes oscillation coefficient partial sum square root` (hybrid).
4. `WeilPositiveFull sharp unsmoothed partial sums coefficients square root prime number theorem` (hybrid).
5. `integer atomic spectral measure finite remainder singular continuous boundary radial phase rigidity` (deep).

All five reported `refresh.complete=false` because the background indexer was running, and semantic coverage `not_measured` due reporting budget. Completion above means request completion, not exhaustive or fresh corpus coverage. Source reads and subsequent Lean checks remain authoritative for applicability.

- `WeilFractionalMassSummableRigidity.fractional_mass_summable_rigidity` covers summable nonnegative fractional atoms with ordinates tending to infinity. Polynomial-tail improvement is therefore already superseded. `WeilFractionalTwoSidedRigidity` and `WeilAbelianTwistPowerRigidity` further handle subpower variation. Verdict **REDISCOVERED** for the initial tail improvement.
- `WeilMixedSpectrumRigidity` and `WeilConeMixedSpectrumRigidity.vonMangoldt_and_riemannHypothesis_of_mixed_spectrum` require a diffuse continuation continuous on the closed half-plane. This is a real unmet premise for an arbitrary finite singular-continuous measure or accumulating fractional atoms.
- `HamburgerTruncatedRadialIntegral.exists_bound_truncated_radial` (line 464) requires `ContinuousAt G` throughout the closed half-plane. Its rectangle proof uses that hypothesis at the critical edge. The candidate's paper proof instead uses rectangles whose left edge is strictly interior, followed by dominated radial limits. No unchanged application of the old theorem is claimed.
- `WeilFullConeSquareRootPNT.norm_sqrt_pnt_sub_le` is a compact autocorrelation smoothing estimate. `WeilProducerPerronExplicitFormula.tsum_lamC_mul_max_eq` is logarithmically weighted. Neither was used as an unsmoothed signed-deviation PNT. `WeilWorkSingularArithmeticSharpReciprocal` concerns reciprocal coefficients, not λ.
- Booker's [primary text](https://arxiv.org/html/1308.3067), Definition 1.3(A3) and §3.2, was revisited: discrete spectral support is a premise, and degree-one periodicity follows after the reflected contour identity. Searches combining Hamburger converse theory with finite spectral remainder / total variation / singular-continuous measure found no directly applicable primary theorem. This is limited novelty evidence only.

Candidate F and its detailed proof are in `FINITE-REMAINDER.md`. Checks on paper: the reflected Gamma quotient is `2Γ(z)/(2π)^z`; the two residues are `−β` and `−β/(πτ)` in the left-line identities; the negative-half-line phase is `exp(iπμ{0}+2πiM) exp(−2πiν[−2t,∞))`; layer-cake superlevels are bounded intervals for every positive layer height. The proof keeps the moving spectral tail through a uniform truncated contour estimate. Finite remainder is the explicit alternative in an intrinsic dichotomy, not an assumed solution of general WP04. Formal verification and novelty gate remain pending.

Concurrent corpus update noticed during the lint audit: `WeilWorkSettledPhaseTrace.lean` now contains a parallel source primitive and almost-everywhere boundary trace, plus source statements for reflection and compact L¹ convergence. Its `tendsto_sourceTrace_of_nonatom` excludes zero and atomic endpoints; `tendsto_sourceTrace_ae` states the resulting almost-everywhere limit. These were inspected as source, not independently compiled here. Our endpoint-inclusive construction proves trace existence at every height. The generic trace construction is therefore partly duplicated in the current corpus and remains **BRIDGE / classical**, not a novelty claim. Future work should reuse applicable checked contour or compact-convergence results if they become available, rather than duplicate them. No edits were made to the parallel file.

Fourth-cycle direct leaf commands both exited 0 without warnings:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationEndpointPhase.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationEndpointPhase.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialBoundary.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialBoundary.lean
```

Both new leaves are wired into `RHTower.lean`. No umbrella build. The new lint run exited 1, reporting eight unrelated unreachable leaves: `WeilWorkDeficitFourierTransport`, `WeilWorkPBAPMomentPackets`, `WeilWorkSettledPhaseTrace`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`, plus existing large-file warnings. No `WeilWorkQuantization*` lint error was reported. The different list reflects the shared working tree; no unrelated files were changed here. Search scratch outputs and finished proof prototypes were removed after their processes had exited; exact queries and useful source findings are retained above.

Final scratch command `lake --old env lean /tmp/wp04-radial-audit.lean` exited 0. Eight principal new declarations were axiom-audited; all use only `propext`, `Classical.choice`, and `Quot.sound`. Mathlib name probes passed with explicit universe levels on polymorphic `have := @Name` checks. The audit output is retained in `radial-lean-audit.txt`; scratch source removed after exit. Scoped whitespace checks produced no findings. No own Lean process remains. Main WP04 and candidate F's rigidity theorem remain open.

## Radial contour cycle, 2026-10-07

Deep query `canonical Weil radial boundary trace uniformly bounded truncated signed integral contour without boundary continuity` completed (`partial=false`), with refresh incomplete (`background_indexer_running`) and semantic coverage `not_measured` / reporting budget. Inspected declaration, candidate-lemma, and source-argument rows. Hits included the existing closed-edge contour bound and parallel trace work; none of the inspected hits supplied the canonical signed contour estimate without boundary continuity. This is limited search evidence, not exhaustive absence.

The primary [Burnol 2012 text](https://arxiv.org/html/1106.4749v2), *Two extensions of Hamburger's theorem*, Theorem 1 and Corollary 2, assumes meromorphic continuation to the whole plane, finitely many poles, growth, and a reflected right-half-plane condition. Theorem 2 also assumes global meromorphic continuation. It does not pay the canonical source's boundary-continuation obligation. Search results for purported general RH arguments were not used as verified mathematics.

The existing `TruncatedRadial.exists_bound_truncated_radial` proof was split into an interior rectangle argument and a radial-limit passage. The generic rectangle prototype passed Lean. `WeilWorkQuantizationRadialGrowth.lean` then passed its direct foreground leaf audit: normalized arithmetic completion; interior square-root growth; measurable locally bounded quotient trace; compact contour convergence. The denominator majorant is continuous on a narrow closed strip avoiding 0 and 1; horizontal monotonicity dominates the numerator there. This supplies local domination without assuming the boundary trace is continuous. Canonical contour assembly is being audited separately. Verdict remains **BRIDGE** within candidate F; no standalone scientific novelty claim.

Next receiver audit: `HTGeometry.inverse_mellin_shift` works on any strictly interior closed strip and keeps the same right-line Mellin data. `critical_line_inverse_mellin` and `critical_line_even_theta_relation_defect` currently require continuous critical-edge data. The next source proof must first obtain uniform decay for `PhaseLockRigidity.bigEG` up to the open edge, then take the radial limit. A new right-edge Dirichlet representation is unnecessary: `LSeries_dirichletExp` and the current phase-lock proof already supply the actual coefficient series.
