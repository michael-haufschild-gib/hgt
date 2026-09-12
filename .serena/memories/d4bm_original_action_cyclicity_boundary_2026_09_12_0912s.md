# Verified original action cyclicity; RH remains unproved

Active unbounded goal: unconditional closed Lean proof/falsification RH via HB. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Do not mark goal complete or blocked.

User: analytical only; no computations, Git, launch.sh, subagents, #print axioms or resource-limit increases. One owned foreground Lean/Lake process. Scratch lake env lean; exact leaf lake build only. No umbrella/dependency/full builds. Frontier map READ ONLY. Every turn assess new results across entire chain. Broad/deep/method corpus search directly, no implementation/help prep.

Previous source exchange: see `mem:hawking_bm_literal_source_reflection_and_physical_cyclicity_2026_09_12_0912r`. Actual physicalPerturbation(q,b,aS,aV) uses omega=I*physicalRate(q,b), u=center(q)=rho-1/2. Source/field reflection swaps branches with unchanged independent amplitudes. physicalPerturbation_first_source_zero already proves original linear Einstein equation.

## Added and checked this turn

1. formal/GaloisForLFunctions/HTGeometry/CoordinateEinsteinCyclicAction.lean (453 lines), namespace GaloisForLFunctions.HTGeometry.EinsteinCyclicVariation.
- family 132: complete jet J + Σ a_k U_k via normed product coordinates, k:Fin3.
- weight 159: exp(log(det G(a)/det J)/2), ONE fixed reference.
- density 163: weight*(scalar G−2Λ).
- bulk 206: weight*Σij (G⁻¹ Uk G⁻ᵀ)_ij*(Einstein G+ΛG)_ij.
- boundary 212: weight*EinsteinActionBoundary.divergence G Uk.
- parameterDeriv 249: fderiv ℂ f a (Pi.single k 1).
- paired_cyclicity_defect 397:
  ∂i∂j bulk_k − ∂i∂k bulk_j = ∂i∂j boundary_k − ∂i∂k boundary_j, at0.
- cubicAction 420 = ∂i∂j bulk_k − ∂i∂j boundary_k.
- cubicAction_eq_density_third 425 = −∂i∂j∂k original density.
- cubicAction_cyclic 439: C_ijk=C_ikj.

Geometric hypotheses are explicit nondegeneracy and metric/first-jet symmetry of J and each Uk. No field equation or boundary-cancellation premise. The proof derives original EH first variation near0, proves smoothness on fixed determinant-log branch, differentiates twice, and uses mixed derivative symmetry. It does not define a defect tautologically. Private smooth scalar/inverse helpers were needed because existing corresponding helpers are private. No heartbeat or recursion options.

2. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCyclicActionBoundary.lean (160 lines), namespace RHTower.D4BMCyclicAction.
- modes 25: three independent original Xi-labelled physicalPerturbation fields.
- jets 29: actual ofMetricField at ExteriorPoint.
- metricFamily 98: literal background + Σ a_k modes_k, BEFORE spatial differentiation.
- metricFamily_jet 103: full field-to-jet equality, all ordered second coordinate derivatives retained.
- physical_cubicAction_cyclic 130: concrete C_ijk=C_ikj at actual BM background with Λ=−3.
- physical_cubicAction_eq_density_third 145: concrete C=−third EH density variation.
Physical theorems have no supplied regularity, nondegeneracy, symmetry, field equation or cancellation premises. These intrinsic properties are proved from original metric recipe and exterior chart. They concern the actual affine three-mode family, not a complete nonlinear causal solution.

Both leaves passed scratch lake env lean with default limits. Exact isolated leaf audits passed: core84s, physical65s, each only one new Lean leaf (2 jobs incl config). Imported caches reused (core25 project deps; physical3952); never rebuilt dependencies/umbrellas. Installed each source+five matching .olean/.ilean/hash/.trace artifacts, appended corresponding HTGeometry.lean and RHTower.lean imports. Formal lint passed with pre-existing large-file warnings. Do not repeat these audits.

## Practical Lean details
- literal_contDiffAt signature in ThetaCuspHawkingBMFullLinearEinsteinEquation.lean is (p:ExteriorPoint) FIRST, then omega u aS aV, then i j. Wrong order causes unification explosion; fixed explicit args, not resources.
- Matrix.sum_apply handles matrix finite sums; Finset.sum_apply can cause instances-transparency errors at Matrix aliases.
- Pass (fun i j => exterior_metric_contDiffAt p i j) to C² fieldSpace_add, because n is implicit after i,j.
- D4BMFullLinearEquation.fieldSpace_add and D4BMCorrectedMetricSource.fieldSpace_smul proved finite-family jet extraction.
- mode symmetry from covariantMetricExpression_symm evaluated on original primitives. First symmetry from equality of scalar field component functions before coordDeriv.
- Keep ComplexCoordinateMetricTwoJet.toSpace/ofSpace/einsteinComponent qualified where competing opens exist.
- Do not name a derivative function 'partial' (reserved).
- Two leaves keep generic smoothness proof away from huge physical imports, improving checks.

## Whole-chain consequences and hard unresolved problem
Local bulk-and-boundary cubic symmetry is now derived from original action. This DOES NOT discharge the Peierls receiver's global hcyclic. Receiver ThetaCuspHawkingBMSourceFixedPeierlsReflectionRigidity.lean, d4BMXiSourceFixedPeierls_BM_incidence_forces_criticalLine, needs ONE pairing, symmetric source B, causal Delta, cyclicity for all fields including sourced response directions, causal skewness, and actual candidate incidence at q/reflection. Previous source exchange supplies hp/hm at fixed amplitudes only.

Next concrete work:
1. Identify second variation of bulk with frozen pairing of original quadratic residual when E0 and first residual directions vanish. Leibniz produces weight/inverse derivatives times E0/E1; these need exact discharge with original on-shell source theorem. Do not merely assume a bilinear B or replace observable.
2. Relate boundary cyclicity defect to variation of the ORIGINAL volume-weighted symplectic current. Required convention differentiates volumeRatio(J,Y,t)*actionSymplectic(affine J Y t,X,Z), not bare actionSymplectic.
3. Global common-cutoff integration must include original volume measure, every boundary component, sourced response fields and actual left-QNM probe. Formal boundary divergence has NOT been identified with a bare radial endpoint. Source center(q)=rho−1/2 differs from physicalAngularParameter(q)=(rho−1)/2.
4. If full original incidence matches normalized BM candidate, source-reflection/Peierls receiver may force criticality. If boundary survives, it belongs in that incidence and the SAME fixed-clock observable; do not assume cancellation or silently alter candidate. Nonzero global angular/radial coupling, actual causal reciprocity, extinction, RH remain unproved.

Research card updated: docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md, section 'Original action cyclicity with its boundary divergence' (around2080; other concurrent work may shift lines). Frontier and universal STATUS unchanged.

Broad/deep/method searches used symplectic divergence, action cyclicity, fderiv symmetry, mixed variations, vanishing residual products, Peierls. Some deep coverage partial; candidate/source/method views inspected, actual applicable declarations verified in Lean. Broad Peierls search complete inventory57248 files but most compiler metadata pending/source-only; do not confuse inventory coverage with compiled applicability. Broad arxiv terms variational/transgression found arxiv2606.08659 and2608.01105, abstract-only relevance; no gravitational theorem taken from them.

Owned build/search sessions all completed. Cleanup of 0912s scratch/search/audit files is performed at end of this turn; do not recreate/re-audit unless code changes.