# Evidence

## Twelfth/thirteenth cycles: full resonances and periodic winding

- Completed AP-mechanism and Hamburger-main-kernel deep searches inspected every candidate/source row; neither yielded a source closure. Toeplitz and periodic-lock deep searches returned partial results, with 68,495/68,496 indexed files and semantic retrieval unfinished. The periodic query also left filtering and decomposition unfinished. No absence claim follows.
- The annulus-log/Laurent-factor query completed with partial=false, 68,508 indexed files. Inspected all returned candidate/source rows. `Bottcher.exists_log_on_annulus`, `Bottcher.winding_zpow_circle`, and `HTGeometry.LaurentAnnulus` provide relevant classical machinery. The generated ingredient set leaves winding zero as an obligation; it is not a rigidity proof.
- The lexical `periodic phase --module Weil` query returned the existing `vonMangoldt_and_riemannHypothesis_of_ap_settled_atomic_phase`. Its exact statement was read: it retains a discrete spectral representation and excludes nonzero rational resonances. It does not cover L1.
- Read the exact source critical energy theorem `WeilSingularArithmetic.exists_forwardCoeff_critical_energy_le`, including its coefficient definition. It gives polynomial growth on q-power chains after q^{-j/2} normalization. The equality of its coefficients with `dirichletExp(lamLog lam)` is a pointwise below-two truncation identity, already used in the source subpolynomial proof.
- Primary external sources opened: [Nolasco–Castro](https://arxiv.org/abs/math/0511127), including its PDF mean-motion statement; [Câmara](https://arxiv.org/abs/1710.11572); [Câmara–Malheiro–Partington](https://link.springer.com/article/10.1007/s00025-020-01323-z), full HTML factorization and kernel statements; [Rodman–Spitkovsky](https://arxiv.org/abs/0804.1945), abstract. The Wiener–Hopf factorization mechanism is classical. No scientific novelty is claimed for it or for the contour prerequisite.
- L1's exact statement, attack, normalization and complete paper argument are in RESONANT-PERIODIC.md. The m=1 radial limit fixes the nonzero normalization, so the argument does not depend on an unverified explicit main-kernel evaluation. Dominated convergence over coefficients removes the need for a uniform nonresonant gap. General L and WP04 remain open.
- `WeilWorkQuantizationTwistContour.lean` passed its final direct command `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationTwistContour.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationTwistContour.lean`, exit 0. One informational `ring_nf` suggestion appeared; no error. Six declarations, import wired. All six declarations passed the standard-axiom audit; complete output is saved in twist-contour-lean-audit.txt. ResonantTerms subsequently passed its final direct leaf audit with exit 0 and no diagnostics; five declarations are wired. All five use only the three standard axioms (resonant-terms-lean-audit.txt). The corrected WeilWorkQuantizationResonance leaf passed its final direct audit with exit 0 and no diagnostics; thirteen declarations are wired. All thirteen declarations use only the three standard axioms (source-resonance-lean-audit.txt). WeilWorkQuantizationFrequencySum then passed its clean final direct audit and is wired. All three declarations use only the three standard axioms (frequency-sum-lean-audit.txt). WeilWorkQuantizationPhaseCoupling passed its final direct audit, then a clean rerun after removing two redundant tactics. All three declarations are wired and use only the three standard axioms (phase-coupling-lean-audit.txt). No full periodic-rigidity theorem is claimed.
- New `scripts/formal_tools.py lint` exited 1, with eleven unrelated unreachable modules: WeilPaperGammaPartition, WeilWorkSingularArithmeticCanonicalGaussian, WeilWorkSingularArithmeticGaussianError, WeilWorkSingularArithmeticGaussianShift, WeilWorkSingularArithmeticPoleCancellation, WeilWorkSingularArithmeticSignedConvolution, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Existing size warnings remain; no WP04 error. Those unrelated files were not modified.

### Off-integer shortcut rejected during source assembly

An attempted shortcut would extend the radial equations to arbitrary
positive real radii and declare every noninteger reflected residue zero.
The exact source identity rules out that inference: the reflected
Laplace series has coefficients `dirichletExp(lamLog lam)(n+1)`, not unit
coefficients. Integer imaginary shifts preserve every exponential; at
noninteger shifts the unknown additive twists of those coefficients
remain. Periodicity alone supplies no vanishing theorem there.

The positive survivor is the exact source identity already formalized in
`quantization_reflected_defectLaplace_eq`: arbitrary-radius residues are
controlled by additive Abel means of the actual coefficients. Combined
with shifted arithmetic resonances, this suggests a possible relation
between additive and multiplicative spectra, but no new closure theorem
or off-integer vanishing claim is made. L1's proof uses only integer radii
and is unaffected. The adjacent deep corpus query about zero density and AP nonvanishing
returned partial=true, 68,525 indexed files, unfinished filter_and_judge
with malformed local-model JSON, incomplete refresh, and unmeasured
semantic coverage. All twenty candidate and twenty source rows were
inspected, including a compact follow-up after initial output truncation.
The proposed ingredient set substitutes a near-one zero-free region for
the requested density statement; it does not close the argument. Generic
strip-AP and zeta facts were found, with their premises retained. No
application or absence claim follows.

Latest lint after wiring FrequencySum exited 1 with eight unrelated
unreachable modules: WeilPaperPacketPrimeMasks, WeilWorkSettledPhasePowerLogMoment,
WeilWorkSingularArithmeticGaussianBound, ApertureConeCalculus,
ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal,
BoundaryCoronaCStarAlgebra. No WP04 error. Existing size warnings remain.
No unrelated module was edited.

The subsequent exact annihilator-mechanism deep query completed with
partial=false, 68,535 indexed files, no unfinished stage/error, incomplete
background refresh, and unmeasured semantic coverage. All twenty candidate
and twenty source rows were inspected. Relevant existing machinery remains
LaurentAnnulus, AnnulusRoot, and C1-loop winding certificates; unrelated
finite Toeplitz matrix definitions do not supply the analytic annihilator.
The generated ingredient set still asks for a log-branch/winding proof and
is not a closure theorem. No absence claim follows.

After wiring PhaseCoupling, the final lint pass exited 1 with eleven
unrelated unreachable modules: WeilWorkDeficitXiApproximationCost,
WeilWorkHigherDenominatorLogResidue, WeilWorkSettledPhasePowerCoefficients,
WeilWorkSettledPhasePowerEnergy, WeilWorkSettledPhasePowerLogMoment,
WeilWorkSingularArithmeticGaussianBound, ApertureConeCalculus,
ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal,
BoundaryCoronaCStarAlgebra. No WP04 error; no unrelated changes.

## Eleventh-cycle continuation: resonant AP attack

- `research "almost periodic mean motion phase logarithm resonant density" --mode deep --budget-seconds 300 --json`: partial=false; 68,488 inventoried/indexed files; compiler applicability mostly source-only, refresh incomplete, older-generation snapshot, semantic coverage not measured. All 20 candidate and 20 source-argument rows inspected. Generic AP machinery was found, not a source resonance-collapse theorem. The suggested `feNeutralLogDensity` ingredient set did not establish its proposed link to the actual source and was rejected.
- Read the exact AP radial statement and decomposition in `WeilAlmostPeriodicLockRigidity` (260–380), its plain/nonresonant limits (187–225), the shifted edge (115–205) of `WeilLinearTwistQuantization`, and the source reflected-residue leaf. The exponential factor `exp(ω/4)` is retained in NEXT-CONJECTURE.md. No full resonant source limit is claimed.
- Read STATUS MUST-688–692 with their explicit hypotheses. MUST-690 excludes nonzero rational resonances in its rigidity conclusion; MUST-692's summary is not a stronger theorem. Read the AP/dilation and Gamma-rational parent statements; no supplied decomposition or Gamma-algebraic relation was derived from the source.
- Kaczorowski–Molteni–Perelli, [A converse theorem for Dirichlet L-functions](https://sites.unimi.it/molteni/research/papers-pdf/23-molteni-A_converse_theorem_for_Dirichlet_L-functions.pdf), 2010: opened primary PDF, introduction and defining conditions. The standard converse retains continuation, growth and functional-equation hypotheses. It does not identify an arbitrary AP multiplier with a constant root number or supply the missing source reflection.
- Jessen–Tornehave, [Mean motions and zeros of almost periodic functions](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5656-11511_2006_Article_BF02392225.pdf), Acta Mathematica 77 (1945): primary indexed excerpt states the nonvanishing AP mean-motion theorem. Full PDF opens timed out; no claim of a full-paper audit. That classical reduction controls phase amplitude, not variation, and is not a proof of L. Broad follow-up searches were largely irrelevant; novelty remains unconfirmed.
- K's final scoped whitespace check and new-file whitespace checks passed. Owned eleventh-cycle prototype/search/audit scratch files were removed after their processes exited; the 26-declaration audit is retained in `phase-variation-lean-audit.txt`. No live owned build process remains.

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

The follow-up deep query `canonical Weil radial trace inverse Mellin theta contour identity without continuous critical boundary` completed with `partial=false`; refresh was incomplete because the background indexer was running. Its twenty candidate lemmas and twenty source arguments were mostly unrelated geometry/CCM results, with no applicable radial inverse-Mellin source theorem among the inspected rows. Rephrased as lexical `inverse_mellin_shift`: eight declaration hits, including the exact `HamburgerThetaDefect.lean:38` theorem and the horizontal-bound helper in `ConverseThetaRelation`. Direct source reads verified their strip hypotheses. The deep search's request completion does not imply fresh compiled coverage.

Self-audit for this cycle: significant scientific novelty remains unproved. The checked analytic mechanism is classical; its role is to remove a genuinely unpaid source premise in candidate F, rather than rename a receiver. The contour construction addresses the moving-tail step directly; no effort-based deferral was used. The next step is the actual radial Mellin/theta identity and finite-measure phase comparison. Infinite irregular remainder is still the unaddressed alternative in full WP04.

The final lint snapshot also exposed a new parallel source file, `WeilWorkSettledPhaseMellinTrace.lean`. Its exact declarations include `exists_decay_sourceRemainder`, `tendsto_integral_norm_remainderTrace_sub`, and `integral_sourceRemainder_eq_boundary`. The last is precisely the weighted whole-line boundary shift needed next. Source statements and the shift proof were inspected; its compiled object was absent at this check, so applicability is not yet compiler-verified here. The two primitive definitions use the same normalized exactness choice; check definitional equality of their completions, then almost-everywhere equality of their traces by uniqueness of radial limits. Prefer reusing this source module once checked over duplicating its decay/shift proof. No edits were made to that file. This further narrows the next independent obligation to integrating the actual Dirichlet/Mellin data and the finite-remainder phase comparison.

Final commands, sequential foreground Lean processes, all exited 0 without warnings:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialGrowth.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialGrowth.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialContour.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialContour.lean
lake --old env lean /tmp/wp04-contour-audit.lean
```

The last scratch file audited all thirty declarations from both new leaves and probed the used mathlib composition, compact-bound, dominated-convergence, interval-integrability, change-of-variable, and squeeze names. Every audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. Full output: `contour-lean-audit.txt`. Both leaves wired into `RHTower.lean`; no umbrella build. Scoped whitespace check was clean.

`scripts/formal_tools.py lint` exited 1. Reported unreachable modules were `WeilWorkSettledPhaseMellinTrace`, `WeilWorkSingularArithmeticGrowthComparison`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`, with pre-existing large-file warnings. No quantization module was reported. These unrelated files were left untouched.

## Sixth cycle: source Mellin integration, 2026-10-07

Previous turn classified **PROGRESS**: two compiled leaves supplied canonical C1 and fixed-window vanishing. Current compiled objects and umbrella wiring now exist for `WeilWorkSettledPhaseMellinTrace`. A scratch probe verified definitional equality of its completion with `quantizationCompletion`, and its weighted boundary-shift theorem uses only the three standard axioms. The first probe had a namespace typo in an unrelated `#check`; no completion-equality or axiom error occurred.

Research query `sourceRemainder theta radial Mellin boundary --module WeilWork` returned partial results, with incomplete refresh due the running background indexer. Inspected all twenty candidate rows; they include the exact source boundary shift and no already-instantiated coefficient-theta identity. Source arguments were empty. Exact source reads establish the reusable hypotheses; missing search hits are not an absence theorem.

Primary-source audit: the two narrow arXiv searches returned no hits. Reopened [Burnol 2012](https://arxiv.org/html/1106.4749v2) and [Booker, L-functions as distributions](https://arxiv.org/html/1308.3067). The former still supplies global meromorphic continuation as a hypothesis; the latter's spectral discreteness/integrality conditions remain stronger than arbitrary finite positive remainder. Neither eliminates candidate F's unpaid source phase comparison. Mellin integration itself remains **BRIDGE**, with no standalone novelty claim.

The exact source identity being formalized is the radial inverse-Mellin formula at the end of FINITE-REMAINDER.md. The proof uses `inverse_mellin_shift` only on its right line, then the now-compiled weighted trace shift and a checked y=2t change of variables. Thus no critical-edge continuity premise is imported.

The second deep query, `finite positive remainder integer atomic floor measure phase layer cake rigidity --mode deep --budget-seconds 300 --module Weil`, completed with `partial=false` and incomplete refresh. All twenty candidate lemmas and twenty source arguments were inspected; most concerned unrelated floor/CCM constructions. `MonotoneTwistLock.integral_layerDensity` was useful, but its existing source vanishing theorem retains closed-edge continuity. A follow-up lexical query, `'"atomic floor" "integer atomic" "finite remainder" "residual mass"' --any --mode lexical --module Weil`, used FTS5: seven total hits, six returned eligible declarations, four modules. The six returned rows were inspected. They were finite prime-side/Rankin/CCM remainders and the already-inspected near-integer atomic theorem with ordinates tending to infinity. No intrinsic atomic-floor construction was supplied by these hits; this remains limited search evidence.

The radial Mellin and theta leaf audits now pass. The latter proves a common polynomial bound for the original and reflected traces, reflection of the Mellin kernel, the even theta defect, and both Hamburger/Laplace identities. It retains β and y=2t throughout. Scratch failures were confined to cast/namespace/local-definition normalization; the final direct source audit passed without warnings. The layer-cake prototype also passed: the old proof's continuity was used only to obtain measurability after the contour bound, so source measurability suffices. Fixed-window vanishing replaces its separate compact kernel estimate.

Next source construction has one explicit API restriction: `Measure.sub_add_cancel_of_le` requires a finite subtrahend, not merely a sigma-finite one. `Measure.restrict_sub_eq_restrict_sub_restrict` permits finite cancellation on bounded intervals. This pays the interval decomposition for κ and μ−κ without assuming κ has finite total mass. The mathematical candidate remains unchanged.

The broader obstruction was also attacked through deep query `infinite residual spectral mass monotone phase arithmetic radial cancellation without limiting phase --mode deep --budget-seconds 300 --module Weil`. It completed with `partial=false`, refresh incomplete, older-generation coverage snapshot, and semantic coverage unmeasured. All twenty candidate rows and twenty source-argument rows were inspected after reducing the verbose search output. The relevant source arguments recover the existing Abelian/subpower/variation rigidity routes: an unbounded phase need not settle, but those results still require a quantitative sublinear growth bound and closed-edge data. No such bound for the actual residual measure was supplied by these hits.

Rejected the search tool's unverified proposed ingredient set: decay of `sourceRemainder` is decay of the Gamma-completed analytic Mellin remainder, not decay of the positive residual measure ν. Likewise, `exists_tendsto_im_quantizationLogPrimitive` takes η→0 at a fixed height; it gives no phase limit as height tends to infinity. Combining those two statements does not prove radial cancellation in the moving tail. Positive lesson: keep the spectral residual measure, completed analytic remainder, and two limit parameters distinct. Candidate F remains the current exact target; the quantitative infinite-phase case remains open.

Final commands, sequential foreground Lean processes, each exited 0 without warnings:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialMellin.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialMellin.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialTheta.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialTheta.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialLayerCake.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialLayerCake.lean
lake --old env lean /tmp/wp04-mellin-theta-audit.lean
```

The last command probes toolchain names and audits every one of the twenty-six declarations from the three new leaves. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Output retained in `mellin-theta-lean-audit.txt`. All nine finished leaves are wired; no full or umbrella build. Scoped whitespace checks had no findings.

Fresh `scripts/formal_tools.py lint` exited 1 on eight unrelated unreachable modules: `WeilWorkPBAPPacketFourier`, `WeilWorkSingularArithmeticMeanComparison`, `WeilWorkSingularArithmeticSquareSummability`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. Existing large-file warnings also remain. No quantization module error appeared; unrelated files were left untouched.

## Seventh cycle: actual integer floor and finite remainder, 2026-10-07

Deep query `integer atomic floor measure subtraction bounded interval counting finite singular remainder --mode deep --budget-seconds 300 --module Weil` completed with `partial=false`, refresh incomplete due to the background indexer, older reported coverage, and unmeasured semantic coverage. All twenty candidate-lemma and twenty source-argument rows were inspected. Existing atomic domination requires an already-atomic measure; no actual canonical floor construction was found among these hits or the subsequent source-text search. The construction is a classical BRIDGE, not an independent novelty claim.

`WeilWorkQuantizationIntegerFloor.lean` passed its direct leaf audit without warnings and is wired. It constructs the floor measure below μ, proves natural-valued mass on every finite-mass measurable set, pays subtraction locally, and proves every residual atom has mass below one. The residual-phase prototype derives the actual phase without dividing by a boundary trace. Missing compiled objects for EndpointPhase and RadialContour interrupted its checks; both unchanged leaves were restored individually, with exit 0. No full or umbrella build was run.

The primary [Bondarenko–Radchenko–Seip Fourier interpolation paper](https://link.springer.com/article/10.1007/s00365-022-09599-w) was opened and its introduction and Theorem 2.1 inspected. Its interpolation hypotheses and locally finite sequences do not derive discreteness of an arbitrary canonical boundary measure. A Patterson PDF returned 404 and a PMC page required a CAPTCHA; neither was treated as inspected evidence.

The follow-up crystalline-measure search located [Favorov's 2024 paper](https://jmag.ilt.kharkiv.ua/index.php/jmag/article/download/1076/jm20-0279e/1173) and [2025 preprint](https://arxiv.org/abs/2504.03365). The first starts from locally finite integer-weighted measures; the second starts from an entire almost periodic function and its zero multiplicities. These directions do not supply the missing integer mass or entire continuation from our source. This hypothesis comparison supports keeping F alive; it does not certify novelty. Irrelevant ham-sandwich and moment-problem hits were discarded.

Final rigidity assembly can reuse `AbelianTwist.vonMangoldt_and_RH_of_coeff_eq_one`, which needs no closed-edge continuity. For the arithmetic step, both canonical Hamburger identities and the existing periodic-residue receiver suffice. The complete assembly argument is appended to FINITE-REMAINDER.md. Its Lean prototype is pending verification; no claim of a compiled rigidity conclusion is made at this point.

Final commands, sequential foreground Lean processes, all exited 0 without warnings:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationIntegerFloor.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationIntegerFloor.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationResidualPhase.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationResidualPhase.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationFiniteRemainderRigidity.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationFiniteRemainderRigidity.lean
lake --old env lean /tmp/wp04-finite-remainder-audit.lean
```

All thirty-four declarations in the three new leaves passed the scratch axiom audit, with only `propext`, `Classical.choice` and `Quot.sound`. Toolchain name probes passed. Full output is retained in `finite-remainder-lean-audit.txt`. The final source-only dichotomy is `quantization_rigidity_or_infinite_residual`. Its proof pays the finite-measure phase hypotheses, proves all arithmetic radial residues of the reflection error vanish, applies periodic coefficient rigidity, and reuses the existing coefficient-one receiver. Twelve finished leaves are wired. No full or umbrella build was run.

Fresh lint exited 1 on eight unrelated unreachable modules: `WeilWorkDeficitCoefficient`, `WeilWorkDeficitZeroTransport`, `WeilWorkHigherDenominatorQuotientGrowth`, `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. Existing size warnings remain. No quantization-module error appeared; unrelated files were left untouched.

The follow-up lexical query `boundaryMeasure vonMangoldt integer mass canonical equality --mode lexical --any --module Weil` returned twenty declaration rows, five exploration rows and seven markers, all inspected. It supplies no deep source arguments or semantic coverage report. `WeilWorkHigherDenominatorMultiplicity.boundaryMeasure_vonMangoldt_integer_counting` and its singleton-multiplicity formula support the expected zero-or-infinite residual corollary after canonical-source identification. That is a bridge corollary of F, not a new significant conjecture.

Cycle self-audit: the actual-source finite-remainder theorem moves the inspected corpus frontier; novelty beyond the literature is still provisional. The analytic prerequisites are classical. No effort-based deferral occurred. The full goal remains open because no source theorem excludes infinite residual mass. Next investigation must distinguish diffuse/fractional disorder from an artifact of always rounding atoms downward: infinitely many atoms just below integers can give infinite floor remainder even when their signed distance to integer counting is summable. Check the existing signed nearest-integer and subpower parent results before choosing a new conjecture.

Next-cycle deep query `canonical source finite signed measure nearest integer spectral remainder singular continuous subpower phase rigidity without boundary continuity --mode deep --budget-seconds 300 --module Weil` completed with `partial=false`, incomplete refresh (`background_indexer_running`), an older coverage snapshot and semantic coverage `not_measured`. All twenty candidate and twenty source-argument rows were inspected in compact form after the initial verbose output truncated. The proposed ingredient set merely asks to establish phase lock; it does not prove it. Hits retain closed-edge continuity or atomic representation premises. Direct reads of the two-sided and mixed-spectrum parent statements confirm the stronger growth range α<1, rather than merely finite remainder.

Conjecture G and its first unpaid refined remainder estimate are recorded in NEXT-CONJECTURE.md. `tendsto_layer_remainder_pow` chooses η=(1−α)/2 and uses `exists_norm_prodF_le_rpow`; the current canonical square-root bound does not suffice for every α<1. Its parent boundary bound `exists_norm_phiG_le_rpow_small` derives a producer subpolynomial estimate and then uses edge continuity for horizontal comparison and compact control. Those uses must be replaced by actual radial-limit arguments. Broad external searches found no directly applicable signed-measure converse; reopened Burnol and Booker retain the previously audited continuation/spectral premises. Novelty remains provisional. No new Lean for G was written.

## Eighth cycle: actual subpolynomial trace, 2026-10-07

Deep query `canonical radial trace subpolynomial growth infinite spectral remainder sublinear power variation rigidity --mode deep --budget-seconds 300 --module Weil` completed with partial=false, no unfinished stages and no errors. All twenty candidate-lemma and twenty source-argument rows were inspected, including compact follow-up after verbose output truncated. Coverage reported all 68,404 inventoried files indexed, but refresh was incomplete (`background_indexer_running`); most compiler records were pending or stale. The proposed ingredient set still asks for phase lock and is not a proof. Direct source reads verify that the relevant power/variation parents assume joint critical-edge continuity.

The primary [Raghunathan paper, Beyond the extended Selberg class: d_F≤1](https://arxiv.org/html/2005.11381) was opened and its setup inspected. Its P2/P3 require entire continuation after multiplication by a polynomial and a functional equation. It therefore does not supply those properties for the arbitrary canonical source. The [Balasubramanian–Raghunathan sequel](https://arxiv.org/abs/2011.07525) was inspected at abstract level only; it concerns degrees between one and two in the same enlarged setting. Broad searches for arbitrary spectral remainders returned no directly applicable converse. This supports no novelty certification.

The actual subpolynomial bridge uses the existing producer theorem, a uniform Gamma ratio retaining horizontal displacement, and actual horizontal monotonicity. Bounded-height control comes from the already compiled square-root strip estimate. It needs no Phragmén–Lindelöf extension or continuous boundary. All five declarations passed a scratch check; final leaf/axiom audits are recorded below when complete. Paper proof: SUBPOLYNOMIAL.md. Verdict BRIDGE, not independent scientific novelty.

SUBLINEAR-REMAINDER.md now closes conjecture G on paper. The refined remainder can be derived from finite rectangle inequalities, compact radial convergence and the lower-height limit, avoiding a horizontal boundary integral. The existing off-resonant arithmetic bound, generic measurable layer-cake theorem and main-term scaling then apply. Its formal proof remains incomplete. No supplied residual-growth hypothesis is being asserted from hW.

Final direct leaf command and scratch axiom audit both exited 0 without warnings:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationSubpolynomial.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationSubpolynomial.lean
lake --old env lean /tmp/wp04-subpolynomial-audit.lean
```

All five declarations use only propext, Classical.choice and Quot.sound; output retained in `subpolynomial-lean-audit.txt`. The 226-line leaf is wired, bringing the finished quantization leaves to thirteen. Scoped whitespace check passed. Fresh lint exited 1 on six unrelated unreachable modules: WeilWorkPBAPCriticalResonator, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal and BoundaryCoronaCStarAlgebra, plus existing size warnings. No quantization issue appeared. No full build, umbrella build, raised heartbeat or mathematical computation was used.

Self-audit: sharpened actual-source growth is a verified bridge, not certified scientific novelty. G's paper proof is complete but its Lean proof is not. Next cycle formalizes the refined rectangle/remainder estimate and measurable cumulative phase, then the arithmetic coefficient comparison. Full WP04 still needs source control of infinite residual mass. No difficulty-based deferral; own completed scratch files removed.

## Ninth cycle: refined actual remainder, 2026-10-07

The actual refined remainder leaf passed its final direct `lake --old env lean -o ...` audit, exit 0 without warnings, and is wired. The proof retains the difference of the two vertical rectangle integrals, passes to the radial trace on a finite interval, then sends the lower height to minus infinity. Arithmetic right-edge expansion and resonant-term subtraction give every positive exponent up to one. This removes the parent's critical-edge-continuity premise from the needed estimate.

The radial-power prototype subsequently passed scratch compilation. Its final leaf audit is running. Cumulative-phase and reflected-residue prototypes are prepared but unchecked; the final coefficient assembly remains unchecked. They are not claimed as formal results.

Deep search `actual radial trace refined contour remainder measurable boundary sublinear phase --mode deep --budget-seconds 300 --module Weil` completed with partial=false, no unfinished stages; all twenty candidate and twenty source rows were inspected. Coverage inventoried/indexed 68,412 files, but refresh remained incomplete while the indexer ran and most compiler records were pending/stale. The proposed ingredient set was unverified. Inspected parents still require edge continuity or a supplied atomic representation. Broad external search returned no new applicable converse; Booker's primary PDF was reopened and Definition 1.3(A3) rechecked: discrete support and finitely many noninteger masses are assumed. These are not automatic for the canonical measure.

Process correction: an API probe was inadvertently still returning a running handle when the first rectangle scratch check launched. The next poll confirmed the probe had exited; subsequent Lean checks were serialized explicitly. No process was restarted on timeout. Probe failures were namespace lookup errors, corrected against actual source. No full/umbrella build or heartbeat increase.

The exact-statement follow-up first returned irrelevant hits; rephrasing located [Oliver's Notes on Low Degree L-Data](https://arxiv.org/pdf/1601.05009), whose Definition 2.1(3) and Theorem 2.4 were inspected. The definition retains discrete support and finitely many noninteger masses. Theorem 2.4 recalls Booker's multiplicity-one equivalence for an entire L-datum with o(T) total spectral mass. Our ν is only an integer-floor remainder: no arithmetic L-datum structure for κ or ν has been proved. Applying that theorem directly to ν would import an unpaid hypothesis. [Booker's original Definition 1.3(A3)](https://arxiv.org/pdf/1308.3067) was also rechecked. The inspection supports the distinction from these parents; it does not certify novelty against all literature.


Final commands, one foreground Lean process at a time after the recorded initial probe correction, all exited 0 without warnings in their final versions:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialRemainder.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialRemainder.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialPower.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRadialPower.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationCumulativePhase.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationCumulativePhase.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationReflectedResidue.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationReflectedResidue.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationPowerRigidity.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationPowerRigidity.lean
lake --old env lean /tmp/wp04-power-residual-audit.lean
```

The final assembly passed first with one deprecated `push_neg` warning. Replacing it with `push Not` and rerunning the final direct leaf removed the warning. All thirty-two declarations in the five new leaves were enumerated and axiom-audited; every report contains only propext, Classical.choice and Quot.sound. Complete output: `power-residual-lean-audit.txt`. G's final alternative has hW as its only substantive input. All eighteen finished leaves are wired. Scoped whitespace check passed. No full or umbrella build, added axiom, raised heartbeat or mathematical computation.

Fresh lint exited 1 with sixteen unrelated unreachable modules: WeilPaperPacketRealification, WeilWorkHigherDenominatorFinitePoleMellin, WeilWorkHigherDenominatorQuotientMellin, WeilWorkHigherDenominatorThetaDefect, WeilWorkPBAPCriticalCoefficients, WeilWorkPBAPCriticalDatum, WeilWorkPBAPCriticalKernel, WeilWorkPBAPCriticalLaplace, WeilWorkPBAPCriticalResidue, WeilWorkPBAPCriticalResonator, WeilWorkPBAPCriticalWindow, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal and BoundaryCoronaCStarAlgebra. Existing file-size warnings remain. No quantization error; unrelated sources were left untouched.

The cycle's self-audit was posted in chat. The inspected corpus frontier moves from finite remainder to arbitrary sublinear power mass, with no critical-edge-continuity premise. Scientific novelty remains provisional; the analytic mechanisms are classical. No effort-based deferral. The main source obligation remains open, so the next cycle pivots from stronger receivers to source degeneration H.

## Preparation for the next source cycle

Deep query `canonical spectral residual mass source growth sublinear arithmetic phase singular continuous quantization --mode deep --budget-seconds 300 --module Weil` completed with partial=false and no unfinished stages/errors. All twenty candidate and twenty source-argument rows were inspected after compacting the verbose output. Coverage reported 68,432 indexed files, refresh incomplete due to the background indexer, mostly pending/stale compiler records and unmeasured semantic coverage. Its proposed residual estimate used the already-defined ξ divisor, which has not been identified with arbitrary μ; that inference is rejected.

Follow-up lexical query `continuous density linear residual phase slope quantization canonical measure --mode lexical --any --module Weil` returned twenty declarations, five exploration rows and six markers, all inspected. Direct reads of the linear-twist parent confirm its continuous-edge and sublinear-residual premises. The jittered positive source permits noninteger real positions and a negative atom, so it does not satisfy the arithmetic support required by hW. STATUS MUST-573 already rules out broad independent random integer constructions; no such construction is proposed here.

Deep query `positive Herglotz strict constant lower bound conductor one integer Dirichlet support --mode deep --budget-seconds 300 --module Weil` returned partial=true with interrupted text/source stages. All twenty candidate and twenty source rows were inspected. Coverage reported 68,436 files, incomplete background refresh and unmeasured semantic coverage. Available hits locate the exact Herglotz representation, short-interval support consequences and the χ₈ conductor obstruction. None supplies general source degeneration. Ordinary Dirichlet convergence does not by itself supply the proposed strict spectral bound.

The primary [Samaris paper, Dirichlet series with positive real part](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BF1ED9621CFA4D82B3F1CFD80F84F6AE/S000497270001176Xa.pdf/dirichlet-series-with-positive-real-part.pdf) was opened; its definition and Theorem 2 were inspected. It treats normalized pure exponential series converging absolutely throughout its half-plane. The positive-real function here contains Gamma and polar terms; their subtraction does not preserve positivity. This is not an applicable degeneration theorem. Broad searches otherwise returned mostly irrelevant hits, which were discarded. H survives this preliminary attack but has no paper proof or Lean theorem. NEXT-CONJECTURE.md records its exact quantifiers, competing possibility, first open core and next experiment.

## Tenth cycle: source degeneration attack and quiet scales

The exact source-degeneration search returned partial=true (malformed local judge JSON); all twenty candidate and twenty source rows were inspected. The trace-zero and quiet-scale deep searches returned partial=false, no unfinished stages, with incomplete background refresh and unmeasured semantic coverage. All returned candidate/source rows were inspected; automated ingredient sets remain unverified. The trace-zero proposal confuses continuity on interior vertical lines with critical-edge continuity and does not identify the arbitrary canonical measure with the ξ divisor. The quiet-scale proposal recovers the existing global growth receiver; it supplies no source growth bound.

Direct audits of full-cone near-null positive definiteness and the exposed-point result show they constrain the deviation from Λ. They do not make the ζ radical near-null for arbitrary λ. Prime-blind duality is a feasibility criterion, not energy vanishing. The critical Gamma/pole boundary gives b≤a and does not remove a constant spectral floor when a=b=1. Conductor and Mertens obstructions retain their special source/premise restrictions. Thus H remains unproved.

Primary literature audit reopened Booker's 2015 L-functions as distributions (https://arxiv.org/pdf/1308.3067), Definition 1.3 and Theorem 1.6. Its discrete support and finitely many noninteger masses are explicit; the o(T) criterion concerns an entire L-datum, not an arbitrary integer-floor remainder. Miller's Highest-Lowest Zero (https://arxiv.org/pdf/math/0112196) treats completed automorphic L-functions with continuation and a functional equation, also unpaid for the arbitrary source. Broad sparse/Abelian queries returned irrelevant hits and were rephrased; no applicable exact quiet-scale result was found. This is provisional literature coverage, not proof of novelty.

Candidate J and its dependency-closed capped-phase proof are recorded in QUIET-SCALES.md before Lean formalization. J strengthens G by excluding arbitrarily late sublinear quiet scales. Its proof does not establish source degeneration or eliminate the eventual lower-growth branch.

J's combined scratch prototype checked every source-localization and filtered-residue declaration; three remaining local errors in power algebra and simplification were corrected. The final direct LocalPhase and generalized PowerRigidity module audits then exited 0 without warnings. QuietScales also exited 0, with one informational tactic suggestion; a JSON diagnostic pass is locating it before the final axiom audit. Both new leaves are wired; no umbrella build.

During those audits, the next source refinement H2 was made exact in NEXT-CONJECTURE.md: mass-one nonnegative smooth mixtures with every integer-log coordinate zero and critical a=b=1 energy arbitrarily close to zero from above. It is unproved. The existing normalized critical-null theorem requires a<b; it gives no uniform Gamma-energy control as a tends to b, so a limiting argument at equality is not justified. The new deep critical-floor query returned partial=false and no unfinished stages; all twenty candidate and twenty source rows were inspected. Coverage reported 68,459 files, incomplete background refresh and unmeasured semantic coverage. The proposed wall-integral/packet-repair ingredient does not connect to critical mass-one degeneration. Follow-up lexical search located the exact definitions but no critical constant classification.

The September 2026 revision of [Zhu's compact-window paper](https://arxiv.org/html/2608.24827v2) studies the fixed Λ Weil form. Its asymptotic variational upper bound assumes RH, and its trial functions do not satisfy our exact integer-null mixture constraint. Thus it does not establish H2 for arbitrary source weights. No computations from that paper were run. [Chenevier's automorphic conductor work](https://arxiv.org/pdf/1802.05066) uses cuspidal representations and Rankin–Selberg L-functions; these hypotheses are unavailable for the canonical arbitrary source.

The capped source proof, arbitrary-filter comparison and final J alternative are now fully audited. Final commands, serialized one foreground Lean process at a time, all exited 0 without warnings or diagnostics:

```sh
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationLocalPhase.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationLocalPhase.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationPowerRigidity.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationPowerRigidity.lean
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationQuietScales.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationQuietScales.lean
lake --old env lean /tmp/wp04-quiet-audit.lean
```

The initial successful QuietScales audit emitted an informational `ring_nf` suggestion. A JSON diagnostic pass located it in the power-exponential helper; replacing the unnecessary ring step with the exact `neg_mul` rewrite removed it. No heartbeat increase. All nineteen declarations in the three changed files were axiom-audited, each depending only on propext, Classical.choice and Quot.sound. Full output: quiet-scales-lean-audit.txt. Existing G statements remain public wrappers around the generalized comparison, avoiding duplicate contour proofs. All twenty finished leaves are wired. Scoped whitespace checks passed.

Fresh lint exited 1 on nine unrelated unreachable modules: WeilPaperCauchyDeficitProfile, WeilWorkHigherDenominatorWeightedIntegral, WeilWorkSingularArithmeticPolePerron, WeilWorkSingularArithmeticSummatory, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal and BoundaryCoronaCStarAlgebra. Existing size warnings remain. No quantization-module error; unrelated sources left untouched.

The self-audit was posted in chat. J advances the inspected corpus from global sublinear growth to arbitrarily late quiet scales; its scientific novelty remains provisional. The final theorem adds no phase, support, continuity, growth, or continuation premise to hW. It does not exclude linear or faster residual growth and does not solve WP04. H2, the next exact source question, remains unproved. The lexical critical-floor follow-up was repeated with per-module cap removed; all seven hits were inspected and contain no critical constant classification.

Cleanup complete: every owned process exited; all twenty tenth-cycle temporary search/proof/audit files were removed explicitly after preserving the axiom report. Main goal remains active. Current handoff memory: research/weil-work-04-quiet-scales.

## Eleventh cycle: margin correction and intrinsic phase variation

H2 was identified as the existing open prime-blind LP margin problem in STATUS CANNOT-496. RESULT and NEXT-CONJECTURE now say REDISCOVERED; no new theorem or classification of the margin was proved. The normalized a<b null-mixture theorem has no uniform Gamma-energy control at a=b. `abs_energy_nullRepair_sub_le` controls repair by a weighted defect budget but does not make that budget small. `geometric_completion_uniform_positive_floor` excludes obtaining a vanishing total energy from the audited coherent geometric family.

Deep queries used the documented command directly: `normalized integer null mixture critical archimedean energy infimum zero uniform coercivity constant slack`; `approximate C-PIN prime blind null mixture energy margin repair budget geometric completion coercivity` (both module Weil); `prime blind Carlson room regular rho integral t squared logarithmic threshold uniqueness Jensen`; `canonical nearest integer signed residual total variation quiet scales singular continuous accumulating atoms rigidity` (module Weil). The first three completed with partial=false; the last returned partial=true, unfinished semantic_retrieval. Coverage snapshots reported 68464/68468 files, background refresh incomplete, semantic coverage unmeasured, and many source-only declarations. All returned candidate/source rows were inspected; unverified ingredient sets were not used as proofs. Exact source reads and exhaustive rg within Weil modules supplied the applicability checks.

External primary checks: Connes–Consani, Spectral triples and zeta-cycles (https://doi.org/10.4171/LEM-1049; arXiv:2106.01715), constructs near-null tests for the fixed zeta form; its spectral theorem concerns critical-line zeros and does not supply integer-null tests for arbitrary weights. Their archimedean trace paper (https://arxiv.org/abs/2006.13771) likewise does not pay that condition. Gaisin–Gaisin, Levinson-type theorem and Dyn’kin problems (2023, https://www.mathnet.ru/php/archive.phtml?jrnid=sm&option_lang=eng&paperid=9802&wshow=paper), identifies the classical log-log majorant ancestry of the proposed Carlson-room refinement. No new Carlson theorem was claimed or formalized. That possible refinement remains unproved here. Booker (https://arxiv.org/abs/1308.3067) retains discrete/almost-integral spectral premises. Broad searches did not establish novelty of the new source obstruction.

K now targets the actual unit-circle phase variation, defined with mathlib variationOnFromTo. The exact statement, parent comparison and dependency-closed paper argument are in PHASE-VARIATION.md. The prior two-sided fractional receiver assumes an explicit discrete spectrum escaping to infinity and a global power bound; the lock-variation receiver assumes a differentiable phase and continuous boundary. Neither directly supplies K for arbitrary radial source traces. New Lean work starts only after that paper proof. Full WP04 and H/H2 remain open.

K formal audit: all three direct commands `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean GaloisForLFunctions/RHTower/<leaf>.lean` exited 0 without warnings. Leaves: WeilWorkQuantizationPhaseVariation, WeilWorkQuantizationVariationLocal, WeilWorkQuantizationVariationRigidity. All 26 definitions/theorems passed a scratch #print axioms audit; only propext, Classical.choice and Quot.sound occur. Final type explicitly has hW as its sole substantive input. The full output is retained in phase-variation-lean-audit.txt. All three imports added to RHTower.lean; no umbrella/full build or heartbeat increase.

Latest `scripts/formal_tools.py lint` exited 1 on ten unrelated unreachable leaves: WeilPaperGammaReflection, WeilWorkHigherDenominatorPoissonAnalytic, WeilWorkSingularArithmeticCauchyReflection, WeilWorkSingularArithmeticGaussianPairing, WeilWorkSingularArithmeticHerglotzPairing, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Existing large-file warnings remain. No quantization-module error appeared. These unrelated files were not modified.

Next-route search `almost periodic reflected lock phase resonant rational frequencies integer coefficients rigidity --mode deep --budget-seconds 300 --module Weil --json` returned partial=true, unfinished filter_and_judge, coverage 68481 files, stale snapshot/semantic coverage warnings. All candidate/source rows inspected. Exact reads confirm ap_lock_rigidity needs no nonzero rational resonance and a continuous edge; lock_phase_rigidity needs a smooth subpower phase; boundary/infinite dilation rigidity imposes a convergent dilation representation of λ. None was treated as a producer of those premises. No theorem for arbitrary resonant analytic almost-periodic canonical phases was found; the search is partial, so this is not an absence claim.


Thirteenth-cycle checkpoint: five new leaves, thirty declarations, all
final direct leaf and standard-axiom audits passed. The actual-source
resonance comparison, full weighted frequency sum and nonzero constant
resonant sums are verified. L1's q-chain/winding assembly and full WP04
remain open. New-source and scoped whitespace checks passed. Owned
completed scratch/search/audit files were removed after terminal exit;
no owned build/search process remains. No full or umbrella build ran.

## Fourteenth cycle: q-chain and winding continuation

Deep query `canonical periodic resonant phase winding q powers forward coefficient critical energy`
(module Weil, budget 300 seconds) completed with partial=true, semantic_retrieval unfinished
(Qdrant HTTP 408), 68,537 indexed files, older-generation coverage snapshot and unmeasured
semantic coverage. Background refresh remained incomplete. All 20 candidate statements,
20 source-argument statements, the one proposed transfer and ingredient set were inspected.
The actual critical energy and resonance-constant statements are relevant; power-coefficient
energy is a broader family but supplies no phase representation. Parity-wall decompositions,
two-mode energy and fixed-zeta facts do not supply the missing arbitrary-source winding input.
The import/API scratch check exited 0. No exhaustive absence claim follows from this search.

Primary external checks: Câmara–Partington, *Toeplitz kernels and model spaces*
(2017, https://arxiv.org/abs/1711.04511), confirms the classical Toeplitz-kernel parent;
no novelty is claimed for factorization. Nakamura's *L-functions with Riemann's functional
equation and the Riemann hypothesis*
(https://jxiv.jst.go.jp/index.php/jxiv/preprint/download/238/version/291/964/797)
was inspected for possible converse counterexamples. Its introduction distinguishes
relaxed pole conditions and functions without ordinary Dirichlet-series representations.
Those examples do not provide arbitrary WeilPositiveFull sources with the canonical
normalization used here. They were not treated as counterexamples or as a uniqueness proof.

Cycle 14 formal results: QChain and LaurentInverse passed clean final direct leaf audits using `lake --old env lean -o ... <leaf>`. All 22 declarations passed scratch axiom audits, with only propext, Classical.choice and Quot.sound. Reports: qchain-lean-audit.txt and laurent-inverse-lean-audit.txt. Both imports are wired; no full or umbrella build. A temporary elaboration timeout was repaired by supplying the explicit formal-series receiver and radius coercion; no heartbeat setting was changed. A redundant ring normalization was replaced by associativity/commutativity. Full L1 remains a paper result, not a Lean theorem. These steps close formal dependencies and do not independently certify scientific novelty.

Fresh cycle-14 lint exited 1 with ten unrelated unreachable modules; no quantization-module error. Existing large-file warnings remain. Exact errors:

- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBesselBoundary
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticHarmonicSign
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellin
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellinBound
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoleSign
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureConeCalculus
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureConeWinding
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureLogTranslation
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra

The nine hgtl7 self-audit answers were posted in chat: no independent scientific novelty is certified by these two formal components; classical factorization is reused explicitly; actual-source q-chain verification advances the formal frontier; full L1 and arbitrary-phase WP04 remain open; next work is the annihilator, double-series interchange and actual monotone winding. No effort-based deferral, extra axiom or heartbeat increase occurred. All 20 candidate and 20 source-argument statements were inspected, with partial search coverage retained.

Cycle-14 cleanup complete: all owned processes reached terminal exit; all 21 owned temporary files were removed after audit preservation. Scoped whitespace checks passed. Thirty finished leaves remain wired; no full or umbrella build. Goal remains active.

## Fifteenth cycle: absolute pairing and coefficient annihilation

Deep query `Laurent analytic annulus winding Fourier coefficient convolution annihilator`
completed with partial=false, no unfinished stages and no reported errors (117.58 seconds).
Coverage: 68,555 indexed files; 52,062 compiler-pending and 2,660 stale-source entries,
43 compiled snapshots. Coverage snapshot was older-generation; semantic coverage remained
unmeasured and background refresh incomplete. All 20 candidate statements and all 20
source-argument statements were inspected. No proof ideas; one unverified ingredient set.
The annulus logarithm and winding declarations are relevant. Most Laurent-coefficient hits
concern meromorphic germs, not the bilateral coefficients of an annular analytic function.
Neither these hits nor the proposed ingredient set supplies the required infinite pairing.
No exhaustive absence claim is made.

Primary external audit: Câmara, *Toeplitz operators and Wiener–Hopf factorisation: an
introduction* (2017, https://arxiv.org/pdf/1710.11572), Section 5 and Theorem 5.1, supplies
the classical factorization/index parent. Its Hardy-space premises cannot be silently
applied to the polynomial-growth arithmetic sequence. The direct first-moment bound in
RESONANT-PERIODIC.md pays that passage without this assumption. Câmara–Kliś-Garlicka–Ptak,
*General Toeplitz kernels and (X,Y)-invariance*
(https://doi.org/10.4153/S0008414X23000196), abstract inspected; full text was not available
in that view. Its general kernel framework does not itself identify the canonical
arithmetic source. No novelty is claimed for scalar factorization or Fubini.

Cycle 15 formal results: Pairing, CircleCoefficient and PositiveFactor each passed a clean
final foreground command `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean GaloisForLFunctions/RHTower/<leaf>.lean`.
The scratch axiom audit exited 0. All eighteen public declarations and their dependencies,
including three private helpers, use only propext, Classical.choice and Quot.sound. Full
report and final source-obstruction type: pairing-factor-lean-audit.txt. All three leaves
are wired into RHTower.lean. No full/umbrella build, numerical experiment, extra axiom,
heartbeat increase or recursion-limit change occurred. The final theorem explicitly
retains the representation premise; it is not the unrestricted WP04 conclusion.

The paper pairing bound was sharpened to two first moments and the injective map
(l,j)↦(l,l−j). This matches the audited linear source-coefficient bound. Circle coefficient
extraction now proves every column of the annihilator, including the constant coefficient,
and pays each infinite integration and summation. The actual source excludes the precise
positive analytic factorization. The periodic symbol, normalized annular logarithm and
actual monotone winding still require Lean verification before L1 is complete.

Fresh cycle-15 lint exited 1 with six unrelated unreachable modules; no quantization-module
error. Existing large-file warnings remain. Exact errors:

- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilPaperNullSamplingSpace
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureConeCalculus
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureConeWinding
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureLogTranslation
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra

All nine hgtl7 answers were posted in chat. Scientific novelty is not established by these
formal dependencies; the classical parent is explicit. The actual arithmetic/analytic
interface advances, while full L1 and arbitrary-phase WP04 remain open. No work was deferred
for cost. The next cycle must construct the periodic analytic symbol and annular logarithm,
then identify actual winding; no representation producer may be silently added to hW.

Useful inspected next-step API: Complex.differentiableOn_tsum_of_summable_norm in mathlib
Analysis/Complex/LocallyUniformLimit.lean:171. On q⁻¹<|z|<q, each |z^k|≤q^|k|, so the
existing coefficient moment is already a uniform analytic-series bound on the entire open
annulus. This avoids constructing two separate formal power series. API still needs its
scratch Lean probe before use. Bottcher.AnnulusRoot.exists_log_on_annulus:101 requires a
zero logarithmic-derivative integral; the normalization proof at lines 373–438 constructs
g(z)z^{-N} and pays that condition. It can be adapted without treating a supplied winding
condition as an unconditional source theorem.

Cycle-15 cleanup complete: all owned processes reached terminal exit; all six temporary
search/proof/audit/lint files were explicitly removed after preserving evidence. Scoped
whitespace checks passed. Thirty-three finished leaves remain wired. No owned build or
search process remains. Main goal remains active.

## Sixteenth cycle: the actual periodic symbol and its annular logarithm

Deep query `analytic periodic Laurent symbol winding logarithm monotone cumulative phase rigidity`
completed in 112.01 seconds with partial=false, no errors or unfinished stages. All 20
candidate statements and 20 source-argument statements were inspected. Coverage: 68,576
indexed files, 52,078 compiler-pending and 2,660 stale entries; older-generation snapshot,
semantic coverage unmeasured, background refresh incomplete. Relevant hits recover actual
cumulative monotonicity and the continuous-log winding increment. Elliptic and meromorphic
Laurent periodicity results, fixed archimedean winding, and discrete fractional-tail phases
do not supply the missing arbitrary-source periodic winding. The one ingredient set is
unverified and was not treated as a proof. No exhaustive absence claim.

Current primary audit: Ohrysko, *Norm-Controlled Inversion in Measure Algebras*, September
2026 (https://arxiv.org/html/2609.27714v1), Theorem C/2.29 and Section 2.4. Its Toeplitz
estimate assumes a Wiener symbol, a normalized lower bound and zero winding. The logarithm
and one-sided factorization are classical inputs to that argument. It provides no
representation or zero-index producer from hW. The distinction between inversion of a
symbol and inversion of its Toeplitz operator reinforces retaining the explicit coefficient
annihilator proved in cycle 15. No dependence on the new norm-control theorem is introduced.

Burnol, *Deux extensions de Théorèmes de Hamburger*, 2012
(https://arxiv.org/pdf/1106.4749), Theorem 1 and Corollaries 1–2, was rechecked as the converse
parent. Its weakened converse still assumes global meromorphic continuation with finitely
many poles, growth and reflected-half-plane control. Those are not consequences of merely
writing the actual measurable lock phase, and were not silently inserted here.
The proposed L1 verdict remains SURVIVES PRELIMINARY ATTACK; its scalar analytic machinery
is BRIDGE, not independently novel science. The complete L1 paper is being formalized.


Second cycle-16 deep query `positive locally finite measure cumulative exponential phase
continuity atom subunit no atoms`, module Weil, completed in 81.16 seconds, partial=false,
no errors or unfinished stages. All 20 candidate and 20 source-argument statements and the
proposed ingredient set were inspected. Coverage: 68,589 indexed files; 52,090 compiler-pending,
2,660 stale; semantic coverage unmeasured and background refresh incomplete. No returned
candidate pays the actual cumulative-continuity obligation. The suggested partial exponential
sum is not the actual phase and was rejected. Direct mathlib inspection found
`tendsto_measure_Icc_nhdsWithin_right'` and monotone one-sided limits, yielding the local
subunit-interval proof now recorded in RESONANT-PERIODIC.md. This is a classical bridge,
not a new scientific claim.


Preparatory general-AP query `almost periodic Wiener Hopf mean motion canonical Weil phase
rational resonant coupled coefficient` completed in 226.64 seconds: partial=false, no errors
or unfinished stages. All 20 candidate and 20 source-argument statements, one transfer idea
and one ingredient set were inspected. Coverage: 68,603 indexed files, 52,102 compiler-pending,
2,660 stale; semantic coverage unmeasured and background refresh incomplete. The retrieved
Wiener–Hopf sech commutator and photonic harmonic are unrelated to the actual phase. Generic
Bohr-AP stability and existing nonresonant main-term scaling do not pay the missing index
argument. The generated transfer/ingredient proposals were rejected as inapplicable. A narrower
query for noninteger arithmetic radial residues was started; no AP generalization is claimed.


Narrowed query `noninteger radial residue arithmetic reflection`, module Weil, completed
in 143.22 seconds: partial=false, no errors or unfinished stages. All 20 candidate and
20 source-argument statements, two transfer proposals and the ingredient set were
inspected. Coverage: 68,605 indexed files, 52,104 compiler-pending, 2,660 stale; semantic
coverage unmeasured and background refresh incomplete. Relevant hits retain the actual
reflected theta identity and integer-height residues. They do not prove vanishing at
noninteger heights. The finite-residual-mass transfer proposal cannot be applied to the
arbitrary source. No absence theorem follows from retrieval.

Direct inspection also reconfirmed that WeilProducerZetaQuotientBohrRecurrence requires
an actual bounded zeta quotient, and WeilFullConePoissonCountingIdentity only controls
the fixed-width smoothed count. Neither supplies the missing periodic/AP phase or
unsmoothed integer count. In particular, a noninteger reflected radial residue encodes
additive twists of the actual forward coefficients; it cannot be declared zero merely
because the untwisted summatory function has a main term. This remains an unpaid source
obligation, not a valid shortcut for generalizing L1.


Cycle 16 final verification: all five new leaves passed clean foreground direct audits
with `lake --old env lean -o <olean> <leaf>` and are wired into RHTower.lean. Thirty-eight
finished quantization leaves total. All 23 new public declarations and their dependencies,
including the private circle-membership helper, use only propext, Classical.choice and
Quot.sound. Full output and final hW-only alternative: periodic-rigidity-lean-audit.txt.
No full/umbrella build, numerical experiment, added axiom or heartbeat change occurred.
Scoped whitespace checks passed.

The proof constructs the actual represented symbol, annular logarithm and nonpositive
winding. Subunit local residual mass plus continuous exponential phase forces the
monotone cumulative lift to be continuous. Its difference from the analytic logarithm
is a constant deck translation; nonpositive winding bounds the actual cumulative phase
and pays the existing rigidity receiver. L1 is fully formalized; general L and WP04 remain
OPEN. External scientific novelty remains provisional, distinct from formal novelty.

Fresh authoritative lint exited 1 with fifteen unrelated unreachable modules:

- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionAmplitude
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionDecay
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionFourier
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionGeometry
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorMovingKernel
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorNonstationary
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorScaledBessel
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionBound
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionCanonical
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionMasks
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureConeCalculus
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureConeWinding
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureLogTranslation
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra

No quantization-module error. Other agents' files were not modified.

All nine hgtl7 answers were posted in chat. Next-cycle plan: attack general AP rigidity,
retaining all rational resonances and auditing any use of noninteger radial residues.
The reflected theta identity makes those residues additive-twist questions, not automatic
zero limits. Do not treat the periodic theorem as a representation producer or full WP04.

Cycle-16 cleanup completed after all owned Lean/search/lint sessions reached terminal exit.
Twelve temporary proof/search/audit files were explicitly removed after preserving results.
The cycle-17 frontier search is a new owned process; no prior build remains.


## Seventeenth cycle: beyond integer-logarithmic periods

Current primary-source audit began with Nakamura, *L-functions with Riemann’s functional
equation and the Riemann hypothesis*
(https://jxiv.jst.go.jp/index.php/jxiv/preprint/download/238/version/291/964/797),
Introduction §1.1–1.3 and Theorem 1.1. Its comparison examples explicitly fail the ordinary
Dirichlet-series requirement; they do not supply our normalized positive integer-supported
source. This reinforces auditing support and normalization when varying the period, rather
than treating a matching functional equation as a source construction.

Nolasco–Castro, *Factorization theory for Wiener–Hopf plus Hankel operators with almost
periodic symbols* (https://arxiv.org/pdf/math/0511127), Sections 1–2 and Theorem 5.1,
was rechecked. The mean-motion decomposition is classical; the operator theorem uses
its specified factorization and operator spaces. It supplies neither the arithmetic
coefficient vector nor the missing source residue identities. The MathNet PDF attempt
returned an internal error and was not used as evidence. No new scientific claim yet.

Cycle-17 deep query `periodic phase rational logarithm conductor winding rigidity`, module
Weil, completed in 136.70 seconds: partial=false, no errors or unfinished stages. All
20 candidate and 20 source-argument statements and the one unverified ingredient set
were inspected. Coverage: 68,612 indexed files, 52,111 compiler-pending, 2,660 stale;
semantic coverage unmeasured and background refresh incomplete. Returned applicable
results recover L1 itself; the existing AP receiver retains its nonresonance and
continuous-edge premises. No returned result proves the arbitrary real-base extension.
L2 and its first rational-ratio attack are recorded in ARBITRARY-PERIODIC.md; no new
Lean is authorized by an incomplete paper proof.

### Cycle 17 rational-period attack and survivor

Deep search `rational dilation Blaschke periodic resonance coefficient energy conductor --module Weil`:
61.37s, partial=false, no unfinished stages/errors; 68,617 indexed files, 52,114 compiler-pending,
2,660 stale. All 20 candidate and 20 source statements inspected. The unverified ingredient set
only proposed q-power resonance plus uniqueness; it does not extend the integer-base argument.
Deep search `periodic residual measure absolutely continuous spectral density arithmetic support --module Weil`:
81.48s, partial=false, no errors; 68,620 files, 52,116 compiler-pending, 2,660 stale.
All 40 candidate/source statements and the unverified residual-bound ingredient set inspected;
none supplies vanishing density. Deep search `Dirichlet exponential coefficients depend divisibility powers logarithm support lacunary`:
58.64s, partial=false, no errors; 68,621 files, 52,117 compiler-pending, 2,660 stale.
All 40 statements inspected; the suggested cyclic-loop/logarithm mapping is inapplicable.
All three report unmeasured semantic completeness and incomplete background refresh; no absence claim.

Exact source reads: AbsoluteConvergenceRigidity:536ff proves absolute deviation/n rigidity;
ThreeHalvesLacunaryRigidity:778ff proves arbitrary deviations on a three-halves lacunary set vanish;
SingularArithmeticForwardCoefficients:55ff supplies the exact logarithmic convolution.
Mathlib MaxPowDiv and VonMangoldt supply composite-base valuation and Λ*ζ=log.
The rational Blaschke warning model has a complete symbolic paper audit in ONE-SIDED-RATIONAL.md,
including the full critical coefficient energy bound. It refutes only projected-row rigidity.
The strongest survivor is exact classification of all one-sided rational row solutions as ζ*b
with b supported on numerator powers; full positivity then rules out every nontrivial member.
L2+ paper proof is closed; no new Lean has yet been written. Full L2 remains open.

External exact searches for one-sided Dirichlet converse, rational dilation, and Weil lacunary
rigidity returned no directly applicable primary theorem. Rechecked Burnol (arXiv:1106.4749,
Theorem 1 and Corollaries) and Nolasco–Castro (arXiv:math/0511127): their continuation/growth or
factorization premises are not supplied by this phase representation. This is a parent-theory
audit, not evidence that the source result is absent from all literature. Scientific novelty provisional.

Cycle 17 formal progress: RationalResonance passed clean final direct leaf audit and is wired.
RationalRows classification passed its direct leaf audit; adding the full solution-space iff now
requires a fresh audit. Power-divisor quotient and source logarithmic support scratch work pending.
`OperatorTailDirichletMatroid.logWeight_leibniz` was located by exhaustive rg and read; reuse it
rather than reproving the classical finite-convolution derivation. No full or umbrella build.


Cycle 17 final leaf audits: RationalResonance, RationalRows (including the complete iff),
PowerDivisors, LogarithmicSupport and RationalRigidity all exited 0 with no diagnostics.
Each was checked with `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean GaloisForLFunctions/RHTower/<leaf>.lean`.
All five are wired exactly once; no full or umbrella build. The final source-only theorem is
`quantization_rigidity_or_no_oneSided_rational_phase`. Twenty-public-declaration standard-axiom
and mathlib-name audit is running in /tmp. Source-only scope remains explicit.

Fresh authoritative lint exited 1. Its eight errors are unrelated unreachable modules:
- GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionSpatial
- GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCosineMellin
- GaloisForLFunctions.RHTower.WeilWorkSettledPhaseFiniteMellin
- GaloisForLFunctions.HTGeometry.ApertureConeCalculus
- GaloisForLFunctions.HTGeometry.ApertureConeWinding
- GaloisForLFunctions.HTGeometry.ApertureLogTranslation
- GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal
- GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra
No quantization-module error. Existing repository size warnings remain. Unrelated files were not modified.

Cycle 17 closure: all twenty public declarations and their dependencies passed the /tmp axiom
and mathlib-name audit with only propext, Classical.choice, Quot.sound; complete output and
exact solution-space/source-only types saved in rational-rigidity-lean-audit.txt. Scoped whitespace
check passed. Five new leaves, forty-three total, wired exactly once. All nine hgtl7 answers posted.
Scientific novelty beyond inspected corpus/literature remains provisional. Next cycle targets
actual two-sided rational finite blocks; do not assume their invertibility or a phase producer.
No numerical experiment, full build, umbrella build, commit, new axiom or heartbeat override.

After every owned process returned a terminal exit, removed 13 named cycle-17 scratch/search files; audit and search evidence preserved. Finished .olean files retained for downstream leaf checks.

## Cycle 18: bilateral rational phases and negative harmonic mass

Fresh deep queries: `two sided rational phase finite Toeplitz kernel coefficient support Bohr fibre positivity` (module Weil, 300 seconds) and `Weil positive deviation supported multiples fixed divisor rough coprime rigidity` (300 seconds). Full selected results and coverage saved in `cycle18-search-evidence.json`. First query partial at semantic retrieval, 68,643 inventoried/indexed files, older coverage snapshot and unavailable semantic coverage; second query complete with the same freshness warnings. All returned candidate and source statements were inspected. Proposed ingredient sets are unverified suggestions, not proof. Lexical follow-up `Toeplitz singular kernel geometric --any --module WeilWorkQuantization` found no new block-invertibility result.

Exact source audit: `WeilFibreBochnerLaw.twistFibreSum_nonpos_of_weilPositiveFull` still requires NotchSmall. `WeilWorkSingularArithmeticHarmonicSign.exists_nonpos_tendsto_coneDeviation_harmonic` pays ordinary signed convergence only. Neither gives absolute negative harmonic mass. `WeilOneSidedConvergenceRigidity` already proves endpoint one-sided harmonic-deficit rigidity. `WeilPrimeDeficitSetRigidity.summable_nonprime_vonMangoldt_div` pays proper-prime-power harmonic summability. The multiples-of-prime law suggested a first route but is unnecessary in the final paper proof.

Primary external audit, 2026-10-08:
- Câmara–Partington, *Toeplitz kernels and model spaces*: https://eprints.whiterose.ac.uk/125692/1/proc-iwota17-nov27_revised.pdf . Coburn and finite-dimensional kernel classifications concern infinite Hardy-space operators; they do not establish invertibility of every finite arithmetic compression.
- *On kernels of Toeplitz operators*: https://link.springer.com/article/10.1007/s13324-020-00436-6 . This remains parent operator theory, not an actual-source rational-phase producer.
- Connes–Consani, *Quasi-inner functions and local factors*: https://arxiv.org/pdf/2008.10974 . The introduction and main theorem concern compact off-diagonal Hardy-space multiplication blocks for products of specified local factors. They do not assert positivity of arbitrary coefficients or finite-section invertibility.
Fresh targeted searches found no direct source-rigidity theorem with L2h's exact premises; this is not an absence or independent-novelty proof. Unverified search hits and numerical material were not used.

Paper survivor L2h: actual bilateral rational phases force rigidity or divergent negative harmonic source mass. Proof in BILATERAL-RATIONAL.md. General signed L2 and full WP04 remain open. No finite-block invertibility or noninteger additive-twist cancellation is assumed.

Cycle 18 follow-up search: `Weil positivity eventually equal von Mangoldt at primes signed composite deviation rigidity --module Weil --mode deep --budget-seconds 300` completed in 123.7 seconds, with older coverage snapshot/unmeasured semantic coverage warnings. All candidate/source statements inspected; saved with the other searches. The exact prime-support and signMult-alignment premises are not automatic. This motivates P18 in NEXT-CONJECTURE.md; P18 remains open.

Cycle 18 nine-part hgtl7 audit (also posted in chat):
1. L2h is a new source-phase reduction relative to the inspected corpus; independent scientific novelty remains provisional.
2. Classical Toeplitz theory was parent material; endpoint harmonic rigidity was found and reused, not re-proved.
3. The actual rough-resonance/prime-agreement connection was not supplied by literature lookup alone.
4. The represented nonnegative/finite-negative-mass class closes; general signed quantization does not.
5. The next target is signed composite mass, not finite-block invertibility or more generic phase regularity.
6. This cycle produced a complete proof and new formal declarations, not just searches.
7. No step was deferred by effort or context estimates.
8. Full WP04 remains the hard target; P18 directly attacks the source obstruction isolated here.
9. Fresh deep/lexical searches and exact source reads preserved all unpaid notch, sign and convergence premises.

Final cycle-18 verification: both leaves passed clean direct `lake --old env lean -o ... <leaf>` checks, each wired once. All seven public declarations and dependencies passed the scratch axiom audit with only propext, Classical.choice, Quot.sound; full output and source-only theorem type in bilateral-rational-lean-audit.txt. Scoped whitespace checks passed. Global lint exit 1: fifteen unrelated unreachable modules, no quantization error. RHTower: WeilWorkHigherDenominatorInversionConstant, WeilWorkHigherDenominatorInversionSpatial, WeilWorkHigherDenominatorInversionTrace, WeilWorkSettledPhaseCosineMellin, WeilWorkSettledPhaseFiniteMellin, WeilWorkSettledPhaseRationalBound, WeilWorkSettledPhaseRationalProfiles, WeilWorkSingularArithmeticForwardEnergyLimit, WeilWorkSingularArithmeticLogMoment, WeilWorkSingularArithmeticLogMomentLimit. HTGeometry: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Existing large-file warnings remain. No full builds, numerical computations, commits or pushes.


## Cycle 19: prime-agreement audit and arithmetic frequency selection

All four searches are preserved in cycle19-search-evidence.json. Deep queries
covered eventual prime agreement/signed composites, bilateral rational finite
blocks, and finite-prime depletion. All three completed without errors or
unfinished stages; older coverage snapshots and unmeasured semantic coverage
remain explicit. All returned candidate/source statements were inspected.
The bilateral query took 84.5 seconds; the depletion query took 50.3 seconds.
The lexical quantization query and exhaustive rg found the existing row and
class-restricted receivers, not a general arithmetic-frequency selection result.
Generated ingredient sets remained unverified; primeCoeffLE_supp describes a
prime projection and does not prove prime support for λ.

P18 remains OPEN. Exact source reads retained the signMult alignment/absolute
bad-part premise in WeilPrimeDeficitSetRigidity, NotchSmall and gcd-harmonic
limits in WeilConeNotchBochnerLaw, and coefficient nonnegativity in the
multiples-of-prime theorem. The new shared ForwardEnergyLimit source gives a
finite logarithmic critical energy limit, not its value one and not absolute
negative harmonic mass. No new Lean audit of that shared leaf is claimed.
Finite Toeplitz compression invertibility remains unproved. No proposed local
symbol perturbation was promoted to a counterexample.

Primary external audit (2026-10-08): Farmer 2021,
https://arxiv.org/pdf/2101.02771, Definition 1.1 and Theorem 1.1; Soundararajan
2002, https://arxiv.org/abs/math/0210299; Farmer–Pitale–Ryan–Schmidt,
https://aimath.org/jmm2014/a1farmer/section1.html, Theorem 1.1. The inspected
multiplicity-one results retain Euler products and global analytic hypotheses
not obtained from hW. Booker, https://arxiv.org/pdf/1308.3067, Definition 1.3,
retains a discrete spectral divisor and cannot pay quantization in advance.
Schoolmann 2020, https://doi.org/10.1002/mana.201800542, supplies parent
Dirichlet-frequency theory, not the actual source's normalized resonance law.
These targeted checks establish premise differences, not independent novelty
or an exhaustive absence claim.

L3 and L3p are dependency-closed on paper in ARITHMETIC-SPECTRUM.md. The exact
source-only alternatives retain every represented frequency and require an
active nonzero rational-log frequency, hence a rational positive power of
every periodic base, unless rigidity and RH hold. Countable repeated zero
frequencies are summed together; irrational roots of rationals remain open.
Lean implementation and final audit pending at this entry.


Cycle 19 final verification: ArithmeticSpectrum passed clean final direct
`lake --old env lean -o ... <leaf>` audit. All four public declarations and
dependencies passed scratch mathlib-name/axiom audit, using only propext,
Classical.choice and Quot.sound. Full output and both source-only theorem
types: arithmetic-spectrum-lean-audit.txt. Wired once; forty-six finished leaves.
No full or umbrella build. Scoped whitespace checks passed before closure.

Authoritative lint exited 1 with eight unrelated unreachable modules:
- RHTower.WeilPaperMixtureKernelEnergy
- RHTower.WeilWorkSettledPhaseCoprimeCosineBound
- RHTower.WeilWorkSettledPhaseCoprimeDeviation
- HTGeometry.ApertureConeCalculus
- HTGeometry.ApertureConeWinding
- HTGeometry.ApertureLogTranslation
- HTGeometry.ApertureOpenHistoryIdeal
- HTGeometry.BoundaryCoronaCStarAlgebra
No quantization-module error; existing large-file warnings remain. Unrelated
files were not modified. A targeted read of the new coprime-deviation statement
found a bounded real Abel value near one for every fixed coprime mask; it does
not state zero, absolute harmonic convergence, or D19. No independent build of
those shared leaves is claimed.

Cycle 19 nine-part hgtl7 audit (also posted in chat):
1. L3/L3p add source restrictions to the inspected corpus; independent scientific significance is unestablished.
2. Multiplicity-one literature supplied no missing premise; retain and reuse the premise audit.
3. Frequency selection is elementary after PhaseCoupling; four declarations are not a quantization solution.
4. Bases with no rational positive power are excluded; P18 remains open.
5. Exact arithmetic resonance matters; signed composite deviations remain uncontrolled.
6. Much of the cycle tested unsuccessful P18 routes; their precise gaps are recorded.
7. No hard step was omitted because of effort estimates; no closure proof was found.
8. Next attack the actual divisibility gap through full positivity, beyond further class restrictions.
9. Inspected Gibbs, notch, energy and new coprime-mask statements; retained every unpaid premise.

After all owned processes returned terminal exits, removed eight named cycle-19 scratch/search files. Durable search and audit evidence retained; finished leaf .olean retained for downstream checks.

## Cycle 20 closure, reconciled during cycle 21

T20 and signed bilateral rational L2 are fully formalized. The actual reflected
Laplace identity gives B(x+1)=B(x) for every positive real height. Rational
translation eliminates every nonzero signed harmonic, with no sign or negative
harmonic-mass premise. Four new direct leaves and twenty-five declaration/axiom
checks passed; all dependencies use only propext, Classical.choice and Quot.sound.
Complete paper and audit: PERIODIC-RESIDUES.md and periodic-residues-lean-audit.txt.
The earlier L2h obstruction remains valid but no longer describes the frontier.
RESULT.md's stale introductory open-L2 statement was corrected this cycle.


## Cycle 21: exact residue inversion and rational harmonic support

Verdict: PROGRESS. T21 is fully formalized; L4 has a closed paper proof and
an unformalized final rational-base reindexing. Full WP04 remains OPEN.

The complete real-height residue is the forward Dirichlet dilation of bounded
normalized frequency mass. The actual reciprocal coefficient series inverts
that dilation at exponent 3/2. Absolute double summability is proved before
regrouping, so no resonance chain is dropped. Unit translation removes every
irrational positive radical resonance; inversion therefore removes aggregate
irrational mass from every radical-supported countable phase. Nonradical
scales have zero mass by the represented support, eliminating a redundant
target-radical premise. Periodic frequency injectivity and L3p then force
every active periodic harmonic of a nonrigid source to have rational scale.
The final alternative has only the original hW as source input.

Paper: RADICAL-PERIODS.md. The radical arithmetic is classical; primary audit
read Perucca's Linear relations among radicals, arXiv:2511.02498. Kneser's
real-field criterion is parent theory, not a new claim. Independent scientific
novelty of the actual-source application remains unestablished. Five compact
corpus searches, including source arguments and proposed ingredient sets, are
preserved in cycle21-search-evidence.json. Compiler/index coverage is recorded;
search hits are not themselves treated as verified theorems.

Final direct commands, each run in formal with --old and no umbrella build:
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantization<Leaf>.olean GaloisForLFunctions/RHTower/WeilWorkQuantization<Leaf>.lean`
Leaves: DirichletInverse, DilationInverse, RadicalTranslation, RadicalResidues,
FrequencyMass, RadicalMass. All six final commands exited 0 without diagnostics.
The initial FrequencyMass elaboration hit the default heartbeat limit; explicit
sum-interchange equalities and scalar normalization removed it. No limit was raised.
All six imports occur once in RHTower.lean; fifty-six quantization leaves total.

Final /tmp scratch audit checked every one of twenty-nine declarations and its
transitive axiom set after strengthening the countable endpoint. It exited 0;
all sets are contained in {propext, Classical.choice, Quot.sound}. Complete
output: radical-mass-lean-audit.txt. Targeted forbidden-declaration/limit scan
and diff whitespace check found no issue.

Authoritative `scripts/formal_tools.py lint` exited 1 with seven unrelated
unreachable modules, no quantization-module error:
- RHTower.WeilWorkSettledPhaseLocalPolynomialModels
- RHTower.WeilWorkSettledPhaseLocalPolynomialPeriods
- HTGeometry.ApertureConeCalculus
- HTGeometry.ApertureConeWinding
- HTGeometry.ApertureLogTranslation
- HTGeometry.ApertureOpenHistoryIdeal
- HTGeometry.BoundaryCoronaCStarAlgebra
Existing large-file warnings remain. No unrelated source was changed.

Nine-part hgtl7 self-audit, also posted in chat:
1. T21 strengthens the inspected corpus's support restriction; independent scientific novelty is unestablished.
2. Radical algebra and Dirichlet inversion are classical bridges, not standalone discoveries.
3. Actual phase/residue coupling and full infinite-sum cancellation supply the new corpus result.
4. Every active periodic harmonic has rational scale; previously only one arithmetic harmonic was forced.
5. Finish rational-base reindexing, then return to the unrestricted phase producer.
6. Exact residue inversion and aggregate irrational mass elimination were gained.
7. No hard step was omitted on effort grounds; infinite resonance chains were retained.
8. A represented-phase obstruction was resolved; arbitrary-source quantization remains unsolved.
9. Corpus forward/reciprocal series, resonance limits, radical algebra and subgroup machinery were inspected with all premises retained.

Next: formalize the rational-exponent subgroup generator and reindex into the
already proved L1/L2 receivers. NEXT-CONJECTURE.md records the inspected, still
scratch-unverified generator/reindex APIs. No extra representation premise has
been promoted to a source theorem.

## Cycle 22: arbitrary real-periodic class closed

Verdict: PROGRESS. L4 is proved in Lean, with no restriction on real base r>1.
The source-only endpoint is quantization_rigidity_or_no_real_periodic_phase.
No representation is supplied from arbitrary hW; unrestricted WP04 stays OPEN.

RationalPeriodReindex (80 lines, three declarations) forms the rational-exponent
subgroup, takes a positive cyclic generator and reindexes the full weighted
series. RealPeriodicRigidity (88 lines, three declarations) handles reduced
rational bases and assembles L3p/T21/L1/L2. The subgroup and rational reduction
are classical BRIDGE work; the complete actual-source class closure advances
the inspected corpus. Independent scientific novelty remains unestablished.

Both final commands, run serially in formal, exited 0 without diagnostics:
- lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRationalPeriodReindex.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRationalPeriodReindex.lean
- lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilWorkQuantizationRealPeriodicRigidity.olean GaloisForLFunctions/RHTower/WeilWorkQuantizationRealPeriodicRigidity.lean

The complete /tmp name/type/axiom audit exited 0. All six transitive axiom sets
contain only propext, Classical.choice and Quot.sound. Full output is
real-periodic-lean-audit.txt. Every one of fifty-eight quantization leaves is
wired exactly once. No full/umbrella build, numerical experiment, heartbeat
increase, commit or push was used. Targeted declaration/limit and whitespace
scans found no owned issue.

Authoritative lint exited 1 on seven unrelated unreachable modules:
- RHTower.WeilWorkHigherDenominatorCutoffPairing
- RHTower.WeilWorkSettledPhaseCoprimeCombinations
- HTGeometry.ApertureConeCalculus
- HTGeometry.ApertureConeWinding
- HTGeometry.ApertureLogTranslation
- HTGeometry.ApertureOpenHistoryIdeal
- HTGeometry.BoundaryCoronaCStarAlgebra
No quantization error was reported; unrelated source was left untouched.

External parent audit: Ernvall-Hytonen–Odžak–Smajlović, *On a class of periodic
Dirichlet series with functional equation* (2020), primary PDF
https://www.mathos.unios.hr/mc/index.php/mc/article/view/3418/634 . Its degree-one
finite Fourier characterization assumes global continuation, a completed scalar
functional equation and periodic arithmetic coefficients. Those are not the
canonical residual-phase premise and have not been produced from hW.
SOURCE-MEAN-COMPACTNESS.md records the separately inspected AP factorization
and physical-boundary counterexample papers with their precise premise gaps.

Three compact searches are saved in cycle22-search-evidence.json. All returned
partial=false; compiler metadata mostly remains pending/source-only and refresh
reports the running indexer. Candidate, source-argument and proof-idea sections
were inspected; fixed-line reciprocal mean square and weighted settled-phase
receiver signatures were verified in their source. No search hit was treated
as an unconditional boundary producer.

P22 is a new exact source conjecture, not a theorem: positive-time mean-square
finite-frequency approximation of the actual circle phase. A diffuse chirp
defeats generic positivity/local regularity/counting-growth arguments. The
existing absolute trace/kernel estimate loses ε^(-p), so the separate transfer
from B² approximation to radial cancellation also remains unpaid. No P22 Lean
was written before a paper proof. Its verdict is SURVIVES PRELIMINARY ATTACK;
scientific novelty is unestablished.

Nine-part hgtl7 self-audit, also posted in chat:
1. L4 closes the inspected corpus's arbitrary real-periodic class; independent scientific novelty is unestablished.
2. Subgroup classification and AP factorization are classical. They were treated as bridges, not discoveries.
3. The actual-source assembly needed T20/T21 and both rational receivers; merely finding a classical periodic-series theorem does not provide its premises.
4. The real-base restriction is gone. The arbitrary-source quantization frontier remains open.
5. Pivot from more represented classes to the physical boundary orbit and actual signed approximation error.
6. L4 was completed; the source audit also isolated a concrete boundary-limit obstruction and quantitative radial loss.
7. No step was omitted on effort grounds. Every new declaration and dependency was audited.
8. The represented-class gap was closed; the hardest source producer was attacked but remains unproved.
9. Three fresh corpus searches and direct premise audits distinguish fixed-line mean-square results from a boundary phase producer.

## Cycle27 evidence — 2026-10-08

Four full-corpus deep queries completed without partial results; all
candidate and source-argument statements were inspected. Inventories range
from68824 to68834 files. Compiler freshness is mixed; semantic coverage is
unmeasured and refresh reports a running background indexer. Complete
query records, proof ideas and ingredient sets are preserved in
cycle27-search-evidence.json. No global absence claim is inferred.

Direct source reuse: centered_forward_dirichletConvergesAt,
norm_dirichletSum_sub_partialSum_le, exists_forward_regularPart,
differentiableOn_dirichletSum and the toolchain's zeta regularization.
Serena symbol lookup rejected both owned Lean paths as ignored; edits used
the read source and patches. API probes preceded implementation. Two final
direct leaf checks were clean. All ten public declarations and dependency
closures use only propext, Classical.choice and Quot.sound. Exact commands,
source hashes and full axiom output are saved in both finite-part audit files.

External applicability: [Brevig--Kouroupis, September2026](https://arxiv.org/html/2609.35496v1)
requires square-summable coefficients and gives iterated fixed-line means.
It does not establish the actual joint boundary/height limit. The attempted
arXiv2510.05793v2 HTML retrieval failed; no result was inferred from it.
[Flajolet--Gourdon--Dumas, Theorem4 and Section3](https://specfun.inria.fr/dumas/Publications/FlGoDu95.pdf)
provides the classical Mellin singularity parent, with Gaussian divisor
sums already among its examples. This defeats a claim of new methodology.
[Kaneko](https://arxiv.org/abs/2109.12495) treats zeta/primitive-character
mixed moments, and [Balkanova--Frolenkov](https://ddd.uab.cat/pub/pubmat/pubmat_a2023v67n2/pubmat_a2023v67n2p611.pdf)
treat Maass symmetric-square families; neither inspected scope supplies
the missing realization for arbitrary hW.

T26 and T27 have complete paper proofs, pending their exact Lean
formalizations. C28 remains an open physical centered-energy conjecture.
All nine hgtl7 self-audit answers are in the cycle27 card and were posted
in chat. Verdict BRIDGE; independent scientific novelty unestablished.

## Cycle28 evidence — 2026-10-08

Four fresh deep queries are retained in cycle28-search-evidence.json.
The Mellin query completed; double-pole, actual critical coefficient and
centered full-cone queries returned partial results. Inventories range
68842--68850 files. Compiler records remain mixed (many pending, stale or
unavailable), semantic coverage is unmeasured, and background refresh is
incomplete. Relevant retrieved source signatures/proofs were inspected;
no global absence or exhaustive semantic coverage is claimed.

Reused exact Mellin/Gamma, absolute source convolution and Bochner norm
interchange machinery. GaussianMellin has 240 lines, nine public
declarations, and only the original hW as a source premise in its source
capstones. Final direct --old leaf audit is clean. Current-toolchain API
probes and every public dependency closure pass; standard axioms only.
The first combined scratch audit had unresolved universe parameters in
generic API probes; explicit universe levels repaired the scratch file.
No source proof changed, and the final scratch audit exited0. Complete
output and source hash are in gaussian-mellin-lean-audit.txt.

All 66 owned quantization leaves are wired once. No umbrella/full build.
Formal lint exited1 with 367 size warnings and nine unreachable modules
outside this package; no quantization error. Serena symbol retrieval
rejected the owned Lean path as ignored, so edits used patches to the
read source. No heartbeat increases, added axioms or numerical experiments.

Primary audits: [Flajolet--Gourdon--Dumas](https://specfun.inria.fr/dumas/Publications/FlGoDu95.pdf)
is the Mellin parent. [Broucke--Hilberdink, Appendix B](https://arxiv.org/html/2409.06301v1#Sx1)
explicitly contains the coefficient/Bessel lower-bound mechanism; its
main mean theorem has sign and counting hypotheses absent here. This
defeats any new-method claim for T28/T29. The inspected
[Fejer--Riesz paper](https://arxiv.org/abs/2609.03855) and
[Dirichlet-group Riesz means](https://arxiv.org/abs/1908.06458) require
Hardy-space inputs and do not establish such membership for our source.

T28/T29 are dependency-closed paper proofs, pending Lean: actual Gaussian
coefficient recovery, rigidity-or-linear-energy, and the quantitative
logarithmic lower comparison. Their exact error retains integer frequency
separation. T26's double-pole main and T27 remain pending. The new priority
is the pole-free physical comparison and missing C25 upper half. The hard
C28 source energy estimate and unrestricted WP04 remain OPEN.
All nine hgtl7 answers were posted in chat and recorded in the card.

## Cycle29: actual centered Gaussian boundary

Three finished leaves: CenteredSource (198 lines, 15 public declarations),
CenteredGaussian (177 lines, 9), GaussianFourier (67 lines, 3). Each final
`lake --old env lean -o ... <leaf>` exited zero with no diagnostics.
All 27 public declarations and dependency closures printed only propext,
Classical.choice and Quot.sound. The combined scratch API/axiom audit
also exited zero. Complete commands, hashes and output are preserved in
centered-source-gaussian-lean-audit.txt. All 69 quantization leaves are
wired exactly once; no umbrella or full build.

Three corpus searches preserved in cycle29-search-evidence.json. Gaussian
coefficient and centered-forcing searches completed; the latter mostly
returned inapplicable matches. Rephrased with WeilWork module filter and
powerCoeff mechanism: this partial search returned exact PowerEnergy,
ForwardVariance and coprime-variance inputs. Source inspection retained
the open-power-disk restriction and parameter-dependent constants. No
variance-zero inference is justified. Compiler inventory reports many
pending/stale/source-only entries; semantic completeness is unmeasured.

Primary external checks: [Ramachandra 1974](https://www.numdam.org/article/ASNSP_1974_4_1_1-2_81_0.pdf),
[Suzuki 2023](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms.12785),
and [Gaussian/Bessel comparison](https://arxiv.org/html/2409.06301v1).
No inspected result supplies the arbitrary-source C28 bound. Gaussian
extraction is classical; verdict BRIDGE, novelty gate unmet.

Final lint exited one: five unreachable HTGeometry leaves
(ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra), plus 367 existing
size warnings. No owned quantization error; unrelated files unchanged.
No added source premises, axioms, heartbeat overrides or numerical jobs.

## Cycle30: actual coefficient recovery and linear energy alternative

GaussianRecovery (132 lines, four public declarations),
GaussianCoefficientLimit (109 lines, two), and GaussianEnergy (223 lines,
eleven) passed clean final direct leaf audits with --old. No umbrella or
full build. The actual boundary moment equals its absolutely convergent
logarithmic Gaussian coefficient sum; one summable scale-uniform majorant
pays the limit at each positive integer. Literal trace measurability,
conjugation, Gaussian square integrability and exact half-line normalization
then give |B(T,ell)|^2<=2E(T)/(T sqrt(pi)). A nonzero centered coefficient
therefore forces positive linear energy at every sufficiently large scale;
otherwise the existing exact coefficient-rigidity assembly gives lambda=Lambda
and RH. The final alternative has only hW as substantive source input.
T28 assertions1/3 are now compiled; assertion2 and quantitative T29 remain
pending, as do T27, C25-upper, C28 and common-endpoint quantization.

Recovery's six declarations passed the final standard-axiom audit; full
commands, hashes, scratch API source and output are retained in
gaussian-recovery-lean-audit.txt. Energy's eleven declarations and API probes
also passed; full output and hash are in gaussian-energy-lean-audit.txt. Prototype repairs concerned conjugation notation, function
rewrites, real/complex casts and a recursive simplification; no mathematical
premise or heartbeat limit changed. Final leaf checks emit no warnings.
All 72 quantization leaves are wired exactly once. Scoped whitespace check
passed. Latest lint exits1: 367 existing size warnings and seven unrelated
unreachable leaves (WeilPaperArithmeticProductPenalties,
WeilWorkSettledPhaseCenteredConvolution and five HTGeometry leaves).
No quantization error; unrelated sources unchanged.

Four deep searches are preserved in cycle30-search-evidence.json, including
all candidate/source-argument rows. All requests completed with partial=false;
compiler inventory remains mostly pending/stale and semantic coverage
unmeasured. The Bessel search mostly returned special-function Bessel
identities; its suggested ingredient set is inapplicable. The actual
weighted-Bessel theorem it found requires compact support and continuity.
The zero-variance follow-up confused zero-index coefficients and unrelated
matrix centering with vanishing of the entire source; no such inference
was adopted. Direct source inspections remain authoritative.

C30's exact statement and attacks are in ZERO-VARIANCE-RIGIDITY.md.
Generic zeta plus a Dirichlet monomial disproves the analytic-data shortcut,
not the full-positive conjecture. Current ValuationZeroFree supplies
one-prime local nonvanishing; this stronger source statement was inspected,
not independently rebuilt. Joint coefficient faithfulness/prime exhaustion
is still unpaid. Exposed-point rigidity requires equality of its fixed
functional, and regular-deviation rigidity requires closed-strip continuation
of the logarithmic deviation; neither is inferred from zero variance.

External primary audit: [Broucke--Hilberdink Appendix B](https://arxiv.org/html/2409.06301v1#Sx1)
contains the classical coefficient/Bessel lower mechanism. The September2026
[local Hardy embedding preprint](https://arxiv.org/html/2609.11560v2)
claims an embedding for Hardy norms with unweighted coefficients. Our
available energy is weighted by 1/n; normalizing coefficients moves its
trace to Re(s)=1. No critical-line upper estimate follows, and no unverified
preprint theorem was imported. Exact C30 searches supplied no verified
matching classification; this is not an originality/absence claim.
Verdict BRIDGE for the formal work, SURVIVES PRELIMINARY ATTACK for C30.
All nine hgtl7 answers were posted in chat and copied to the card.

## Cycle31: finite Gaussian comparison and exposing-variance attack

Three new leaves passed clean direct `lake --old env lean -o ... <leaf>`
audits: GaussianGram (195 lines, thirteen public declarations),
GaussianBessel (134 lines, two), GaussianFiniteEstimates (89 lines, two).
All seventeen declarations passed the /tmp API/axiom audit with only
propext, Classical.choice and Quot.sound. Exact commands, final hashes,
audit source and complete output: finite-gaussian-bessel-lean-audit.txt.
All 75 quantization leaves wired exactly once; no umbrella/full build.
Missing GaussianShift object restored by a direct leaf audit, source unchanged.

The source result completes T28: every finite positive-index coefficient
set supplies its full asymptotic Gaussian energy lower bound. The proof
uses actual recovered moments and the exact finite Gram matrix. The
quantitative finite estimate separates moment-recovery and off-diagonal
errors. T29's uniform arithmetic estimates and growing cutoff remain
unpaid, as do T27 and every proposed source upper bound.

Five deep searches retained in cycle31-search-evidence.json, including
all candidate/source rows, ingredient proposals and freshness metadata.
The first two were partial; the last three had complete source inventory,
with mostly pending/stale compiler data and unmeasured semantic coverage.
Proposals that assumed RH, both signs of Weil positivity, spectral support
on zeta zeros, or an unproved kernel bound were rejected as source proofs.

Finite-prime confinement was REDISCOVERED in WeilFiniteSupport; that exact
existing Lean rigidity theorem is the positive survivor. WeilLogSummable
already covers log-summable and sparse deviations. Direct source reads
of valuation factorization/endpoints show their cofactor aggregation;
zero variance does not automatically isolate individual coefficients.
New quantitative C31 is stated and attacked in
EXPOSING-VARIANCE-COERCIVITY.md, without a proof claim or formal receiver.

Primary external checks are linked in the two result notes: classical
Broucke--Hilberdink Bessel comparison; Saksman--Seip boundary counterexamples;
Brevig--Kouroupis--Perfekt boundary-limit cautions; multiplicative/uniqueness
parents; current Suzuki and Connes--Consani--Moscovici operator frameworks.
Their missing source or normalization premises were kept explicit. No
numerical experiment or unverified theorem was imported.

Latest lint exits1: six unrelated reachability errors, 367 existing size
warnings, no quantization error. Exact errors retained in the audit.
All nine hgtl7 answers posted in chat and copied to the card. Novelty beyond
corpus/literature remains unestablished; checked bridge progress is not a
solution of WP04.

After all owned Lean, search and lint handles reached terminal exits,
removed all 24 named Cycle31 temporary files. Durable audit/search evidence
and finished leaf objects retained. Scoped trailing-whitespace check passed.
No live owned build remains; goal remains active.
