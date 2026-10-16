# CHMD exact even spectral nullspace — verified 2026-10-16

Goal remains ACTIVE: unconditional premise-free RH via CHMD is not proved. Read the active goal attachment on each new turn. User requires a significant structural contribution per turn, no external web/novelty check, no old research Markdown, no numerical experiments, one owned foreground build/check at a time, no full/umbrella builds, final `lake env lean` audits, no heartbeat increases, exact scratch cleanup.

Card: `docs/drafts/pipeline/3-formalized/chmd-even-spectral-nullspace-2026-10-16.md`.

## New structural result

On the ORIGINAL maximal CHMD SourceGraph, let C_p be literal cosine Fourier readout and g=constantLift 1. Define EvenGraphSource p by a.e. evenness (Lebesgue) of the literal source phiDoobTest p.val.fst. Define evenSpectralNullspace = even p with C_p(z)=0 at EVERY Xi zero.

For EVERY p in this set, c=Re C_p(i/2):
- B(p,q)=-2*c*Re C_q(i/2) for every graph q.
- p-2*c*g belongs to the FULL signedRadical (annihilates all graph vectors, not merely even ones).
- E(p)=-2*c^2.
- 2*c is the UNIQUE real coefficient whose ground subtraction belongs to signedRadical.
- Unconditional set equality: evenSpectralNullspace = {p | EvenGraphSource p and exists c,r in signedRadical, p=c*g+r}.
- Unconditional set equality: even part of signedRadical = joint kernel of all Xi-zero cosine samples and the polar cosine sample.
- Actual ground is even and belongs to evenSpectralNullspace, F_g(z)=XiC(z), C_g(i/2)=1/2.

This closes the previous missing radical converse for the full even completed graph. It does NOT establish primitive positivity, exclude nonreal Xi zeros, supply a stable infinite cardinal expansion, or identify radical with closure of known theta critical translates. Odd-sector detection is separate. No external novelty claim.

## Proof mechanism

For |Im z|<=1/2, exp(i*z*x)/cosh(x/2) is bounded by 2. Its L2(mu) real/imaginary parts define uniformly bounded graph CLMs, identified with the absolutely integrable literal paperFT of phiDoobTest psource. Compact C2 test q has absolutely summable mult*F_q(±gamma) by actual EF_zero_sum_summable, also applied to q(-x). Thus mixed zero operators are summable in OPERATOR NORM. Compact energy polarization, with both diagonals and mixed series proved summable first, yields B(p,testLift q)=mixedGraphFunctional q p. Actual compact graph-core density extends the first slot to arbitrary p. WARNING: this is a mixed formula with ONE COMPACT SLOT, not a proved absolutely convergent arbitrary-p/arbitrary-q diagonal expansion. For even zero-silent p, mixed zero terms vanish and the polar expression extends in q by density, giving full signed-radical decomposition.

## New leaves and APIs

All namespace RHTower.CHMDDoobGraph, six imports wired exactly once into RHTower.lean; root reaches via MainTheorems.
1. CHMDComplexKernelReadout: complexKernelReadout, integrable_complexKernel_source, complexKernelReadout_eq_integral, weighted_source_kernel, stripReadoutBound, norm_complexKernelReadout_le, opNorm_complexKernelReadout_le.
2. CHMDStripFourierReadout: fourierKernel, graphFourierReadout (literal paperFT), graphFourierReadoutCLM (strip), integrable_graphFourierReadout_source, graphFourierReadoutCLM_apply, continuous_graphFourierReadout, norm_graphFourierReadoutCLM_le, graphFourierReadout_of_source/testLift, conj_graphFourierReadout, EvenGraphSource, graphFourierReadout_neg_of_even, graphCosineReadout_eq_half_fourier, graphFourierReadout_eq_cosine_of_even, graphFourierReadout_real_of_re_zero.
3. CHMDMixedZeroOperator: gammaOf_mem_closedStrip, summable_compactFourierCoeffs and _neg, mixedZeroOperator, norm_smul_graphFourierReadoutCLM_le, norm_mixedZeroOperator_le, summable_mixedZeroOperator, graphMixedZeroTerm, summable_graphMixedZeroTerm, tsum_mixedZeroOperator_apply, mixedGraphFunctional, mixedGraphFunctional_eq.
4. CHMDGraphMixedExplicitFormula: conj_paperFT_plus_pole/minus_pole, Wsummand_add_compact, W_add_compact, compact_sourcePair_eq_mixed, sourcePair_testLift_eq_mixed.
5. CHMDGraphPolarReadout: graphCosineReadout_pole/pole_im, sourcePair_ground_eq_graphCosine, graphCosineReadout_ground_pole, ground_source_eq_inverse_theta, evenGraphSource_ground, graphFourierReadout_ground, graphCosineReadout_ground (strip).
6. CHMDEvenSpectralNullspace: evenSpectralNullspace, groundResidual, ground_mem_evenSpectralNullspace, graphMixedZeroTerm_eq_zero_of_even_nullspace, graphFourierReadout_poles_of_even, even_nullspace_pair_compact, even_nullspace_pair, groundResidual_mem_signedRadical, even_nullspace_energy, radical_graphCosineReadout_pole_zero, even_radical_iff_samples_zero, ground_coefficient_eq_of_residual_radical, even_nullspace_unique_ground_coefficient, evenSpectralNullspace_eq_ground_add_radical, even_signedRadical_eq_joint_kernel.

## Verification and process

666 lines / 69 declarations. All six targeted `lake --old build` checks pass. All six FINAL DIRECT `lake env lean <leaf>` checks exit 0 with no warnings. All 69 declarations printed for axioms via /tmp: ONLY propext, Classical.choice, Quot.sound. 92 `have := @Name` probes pass. Six source hashes unchanged through final audit and cleanup. Prior GraphCosineReadout/UniversalCardinalPairing/ContinuousOrbitProjection hashes unchanged from previous memory.

`formal_tools.py index` exits 0, 9 changed indexed modules including concurrent work. Global lint exits 1 ONLY for five unrelated modules missing RHTower umbrella reachability: CHMDPolarJumpForm, DeningerMeyerCohomologyExponential, DeningerMeyerConvolutionTopology, DeningerMeyerGaugeJets, PaperThetaConvolutionGauge. None of our six leaves flagged; do not overwrite unrelated concurrent work to mask this. Previous PaperThetaSpatialSolvability lint failure is no longer current.

All owned processes terminal; all 30 owned scratch files deleted and verified absent. No full builds, umbrella builds, commit/push, numerical computations, web, or heartbeat changes. update_plan/multi_tool_use.parallel unavailable; card and Promise.allSettled used. No subagents authorized. Serena excludes Lean files; rg/apply_patch fallback used.

## Lean lessons

- Generic `NormSMulClass ℂ (SourceGraph →L[ℝ] ℂ)` does NOT synthesize here although NormedSpace does. Use `ContinuousLinearMap.opNorm_smul_le` and `opNorm_add_le`; do not raise heartbeats.
- Supply `(E := SourceGraph →L[ℝ] ℂ)` to Summable.of_norm_bounded to avoid costly inference.
- Evaluation of a CLM series: `Summable.mapL (ContinuousLinearMap.apply ℝ ℂ p) hs`, `(ContinuousLinearMap.apply ℝ ℂ p).map_tsum hs`. NO Summable.apply / ContinuousLinearMap.tsum_apply.
- Reflected compact support: hc.comp_homeomorph (Homeomorph.neg ℝ), not hc.comp_neg.
- Explicit complex ContDiff test types prevent comp/coercion mismatch when rewriting tsum_add. Include map_add before conjugate Fourier sum simplification.
- For hk.re/im.coeFn_toLp, change RCLike projections explicitly to Complex.re/im before rw.
- Specify `graphCosineReadout_eq_half_fourier (testLift f hf hc)` explicitly; `_` may rewrite the wrong graph vector's polar sample.
- `integral_withDensity_eq_integral_toReal_smul` is ROOT namespace, not MeasureTheory.
- `riemannKernelReal_neg` resides in RHTower.WeilExcess, not RHTower; evenness also follows by simp only [riemannKernelReal, abs_neg].
- AE reflection uses `(Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae`.

## Audited source hashes

CHMDComplexKernelReadout aa7e8c32535e42e6de9d6dc7fde2bc297c0e5eb86b3efd8fac40008368ecbe2f
CHMDStripFourierReadout ba56d8bf602c215843fff7ed2cac973960e3ecfe5235382ee44c3db6aee7234d
CHMDMixedZeroOperator 6ef41a1a6d640f8704f26f2315e832347acf0c0c48a543aeaa99820751782dbf
CHMDGraphMixedExplicitFormula 80be0752aa4a160d14241017c6a200886fb4196df014975552808cb603b7e8e5
CHMDGraphPolarReadout b70717f77978adff8ce7fa28e2c10df8cc9e64ffdb47a35482a071623c1c95a0
CHMDEvenSpectralNullspace a2cdae9df54c6b06a4a7fb2d1fcef16f25e5b9747b9f2b8d92368cffd76b09e9
