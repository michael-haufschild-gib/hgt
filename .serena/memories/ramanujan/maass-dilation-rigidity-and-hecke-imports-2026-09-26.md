# Maass dilation rigidity and lightweight Hecke imports

Target RP for actual normalized level-one Hecke-Maass forms remains unproved and unfalsified here. Own card/facts: `docs/drafts/pipeline/1-in-progress/ramanujan-petersson-maass-2026-09-26{,-facts}.md`.

## Kernel-checked facts
- `formal/GaloisForLFunctions/RHTower/MaassDilationRigidity.lean`, namespace `GaloisForLFunctions.RHTower.MaassDilationRigidity`: `zero_of_cusp_inversion_dilation` proves inversion invariance plus cusp decay forces any scalar expanding-dilation eigenfunction to vanish. Identity a*S*a=S gives F(a^2*z)=F(z); iteration and cusp limit force F=0, without division by scalar or function values.
- `not_maass_dilation_eigenfunction` specializes to actual nonzero level-one `MaassCuspEigenform`, with no Laplace-range restriction.
- `hecke_residue_sum_ne_zero`: if that actual source satisfies existing normalized Hecke eigen-equation and p>1, residue sum is nonzero somewhere. Identical vanishing would force f(p*z)=sqrt(p)*mu*f(z). This is NOT a bound on mu, NOT pointwise nonvanishing, and NOT RP.
- Finite Fourier projection retains a residue class, not just frequency zero. `SelbergMaassDeckAverage.deck_average_zero` requires Laplace eigenvalue in (0,1/4). Inversion-transfer energy conservation alone supplies no selected-channel quantitative gain. Next target remains full arithmetic cancellation or actual Hecke-power growth; generic nonvanishing does not advance that bound.

## Optimization and verification
- Unchanged public `_root_.RHTower.heckeOp` definition moved to lightweight `HeckeOperatorBasic.lean`; `EisensteinHeckeOperator` imports it, with all proofs unchanged. Existing type/formula/reducibility preserved. Both new modules wired into RHTower umbrella. No heartbeat/recursion override.
- Final `lake build GaloisForLFunctions.RHTower.MaassDilationRigidity` passed, 2783 jobs; old heavy import reached >10900. Not a controlled runtime benchmark.
- Five new theorem axiom sets and coordinate definition only use standard propext/Classical.choice/Quot.sound. Audit `/tmp/rp_dilation_axioms_20260926c.lean`.
- Changed Eisenstein source compiled with `lake env lean` to its required olean/ilean. Combined-import API/formula regression `/tmp/rp_hecke_compatibility_20260926c.lean` and direct consumer `EisensteinHeckeMaassSelberg.lean` passed `lake env lean`.
- A targeted legacy Lake refresh expanded into a huge unrelated stale dependency rebuild; stopped after active child finished, processes reaped. It did NOT complete. Do not restart it or claim it passed. No trace metadata edited, no full/umbrella builds.
- Index regenerated. Latest `lint --check-generated` exited1 only for unrelated unwired `ShiftedDirichletPolynomialUniqueness` and `ShiftedDirichletTarget`; `/tmp/rp_dilation_lint_20260926c.log`. No stale generated file/forbidden-declaration errors. All owned sessions exited.

Four deep searches `/tmp/rp_{cusp_average,hecke_amplification,dilation_rigidity,cusp_correlation}_20260926c.json` were partial. Source candidates checked; no exhaustive absence claim. Preserve shared concurrent work and other researchers' logs.