# Full Pauli spectral jet transfer — 2026-09-28

Goal remains ACTIVE and UNSOLVED: Brown–Susskind same-draw growth–plateau–first recurrence for ordinary time-independent fixed-q local Hamiltonians. Decisive growing-replica incidence-normalized action bound, occupied image and all fibre sheets after budget-dependent initial cutoff, remains unproved. Do not substitute scalar spectral nonresonance or finite-type detection for this bound.

## Current user focus / constraints
Latest request: optimize Lean, NO heartbeat hacks. No git, subagents, full/umbrella builds; one foreground owned Lean process; scratch lake env lean checks, only missing dependency oleans. Custom hybrid/deep corpus search mandatory before new work. Requested hgt-fields-medalist skill path is absent; announced and used user's conjecture/proof/fail workflow and previously read l7 phases. No scientific-method or update_plan tools available.

## Integrated and verified
New file formal/GaloisForLFunctions/HTGeometry/TwoLocalPauliSpectralJetLaw.lean (365 lines); umbrella import currently HTGeometry.lean:11681, immediately after TwoLocalCommonSpectralChartJetLaw.

- commonReferencePauliMatrix n p = commonReferenceSpectralMatrix n + sum of ALL real Pauli coefficients of weight <=2; includes simultaneous noncommuting perturbations, not merely a star-slice ensemble.
- commonReferenceSpectralMatrix_eq_pauli: reference itself is sum of onsite Z terms with existing ternary fields. No nonlocal reference offset.
- commonReferencePauliMatrix_isHermitian: all parameters give Hermitian matrices.
- commonReferencePauli_branch_real: each analytic matrix-space branch is real near parameter zero; proved from actual characteristic determinant and Hermitian charpoly factorization.
- orderedStarCouplingDeriv_eq_iteratedFDeriv, mixedStarSpectralDeriv_eq_iteratedFDeriv: literal recursive coordinate/second-transverse derivatives equal Frechet jet evaluations. Proof uses local smoothness, update HasDerivAt, and multilinear evaluation.
- starPauliDirectionMap embeds Xi and ZZij directions into full Pauli coefficient space. Exact matrix expansion and star equality proved entrywise via existing Pauli label lemmas.
- commonReferencePauliAction_star_jet: exact equality between existing star spectral response and full-family iterated Frechet derivative.
- capstone balanced_real_character_fullPauli_jet_detection: for every n and nonzero balanced real spectral covector k, exists i,S, jet order |S|+2 <= n+1 with absolute actual full-family derivative at parameter zero >= sqrt(sum_x k_x^2). No assumed nondegeneracy or suppression bound.

This closes a formal interface gap, NOT a claimed novel physical theorem. No quantitative uniform radius in n, no quenched growing-replica bound, no circuit-tube estimate, no global fibre control, no first-return law proved here. Do not claim the missing incidence inequality follows.

## Optimization / validation
All code uses default heartbeats/recursion; no set_option overrides. Explicit sum/Pauli rewrites replace broad unfolding, exact add_assoc replaces unnecessary ring, unused simplifier rules removed. Removed unused KleinbockMargulis import. Local simpa using! is needed for two coercion/instance-sensitive equalities (continuous matrix map at zero; jet transfer); plain simpa printed identical but failed unification.

Scratch /tmp/hgt-local-jet-transfer.OXj3eO/Transfer.lean checked with lake env lean, final session12941 exit0, zero warnings. All 15 new public theorem #print axioms audits: only propext, Classical.choice, Quot.sound. Copied exact checked source (excluding scratch-only audit commands) via apply_patch; verified byte-for-byte equality. No umbrella/full build. Missing common spectral chart dependency olean produced once with targeted lake env lean -o; existing frame source optimization from previous turn had already been checked, not re-audited.

Lint session68386 exit1: 14 unrelated unreachable modules (CCM aperture/exponential-ramp/retained-chain, Moebius mollified, ThetaRateLaplaceBernstein, ZetaZeroDensityPowerSaving, AbelianZetaGas SocleChamberLaw/SocleMomentGenerating, RateMobiusInversion) and pre-existing large-file warnings. New leaf wired correctly. Do not fix other agents' wiring without scope.
Scratch files deleted with apply_patch, exact directory removed with rmdir. All owned Lean/search/lint sessions finished; process check found no owned scratch Lean. No git used.

## Research inspections this turn
Deep/hybrid searches included broad sublevel, Ising diagonal transverse, uniform spectral derivative neighborhood, and method query finite derivative nondegenerate good functions filtered KleinbockMargulis. Partial/coverage/freshness varies; not exhaustive. Actual sources inspected, not cards. Important available next theorem: KleinbockMargulis.Nondegenerate.prop_3_4 gives uniform IsGood exponent 1/(d*l), all affine covectors, from genuine finite-order Frechet nondegeneracy. New transfer supplies the underlying full-Pauli jet certificate with l=n+1, but explicit application (source finite-coordinate reindexing + projective output/balanced covectors) NOT yet formalized. This still would not solve growing-replica coarea mass and is not a novelty claim.

Broad recent arXiv inspection: 2609.20785, Boolean Small-Ball Inequalities for Discrepancy Theory (Akbas/Sra, Sep17). Replica amplification of existence of Boolean signings yields LOWER probability/small-ball bounds under variance/column-energy conditions; NOT an upper tail for nonlinear static spectral maps. No claim of direct applicability or imported theorem.

Useful previous memories: mem:quantum_recurrence/uniform_star_jet_detection_and_default_limit_optimization_2026_09_28; finite_transverse_excursion_gap_audit_2026_09_08; static_ensemble_coverage_barrier_and_novelty_kill_2026_08_10. Static source dimension/Haar design coverage routes alone do not solve full circuit union.
