# Exact boundaries of the classical foundation claims

- **ID:** biscale-classical-boundaries-1810
- **Stage:** 3-formalized
- **Parent:** [field programme](../1-in-progress/biscale-field-development-1810.md), item 2
- **Type:** CORRECTION / CLASSICAL REDUCTION; defect, counterexample and zero-set reduction formalized

## Hyperbolic formula and actual counterexample

For every real continuous compactly supported source `f`, every real `α,x`, put `C=h_(cosh(α·)f)(x)`, `S=h_(sinh(α·)f)(x)`, and `H=cosh(αx)h_f(x)`. The existing addition-formula proof gives `C−S=H`. Hence the exact defect in the incorrectly claimed squared identity is

`C²−S²−H²=2HS`.

Since `cosh(αx)>0`, the squared identity holds exactly when `h_f(x)=0` or `h_(sinh(α·)f)(x)=0`. At zero lag the defect is `2 h_f(0) h_(sinh(α·)f)(0)`, which is nonnegative.

Take the already-constructed actual smooth source `SharpCycle.seed`, and `α=1`, `x=0`. Its origin energy is strictly positive. At `u=1/4`, both the seed and `sinh(u)` are positive. The square of their product is continuous, compactly supported, nonnegative, and nonzero there, so its integral is positive. The defect is therefore strictly positive: this is a source-level counterexample, not a numerical evaluation or a choice of abstract correlation values.

The capstone header now states the correct sum-factor formula and its correct union of zero loci. No theorem body in that capstone needed correction.

## Additive energy already determines the joint zero set

For `K=1`, the multiplicative energy sum is empty. Substituting this into the existing joint-zero theorem proves, for all `N,f`,

`additiveStepEnergy N f=0 ↔ f is constant on [1,N]`.

Consequently, for every `K,N,f`,

`biScaleJointEnergy K N f=0 ↔ additiveStepEnergy N f=0`.

This conclusion says nothing about the optimal nonzero coercivity constant. That quantitative interaction remains item 7.

## Existing reductions to reuse

- In `AbstractBiScaleSystemAndSchurKreinCoupling`, `inner_scaledFrameResidual_eq` and `norm_sq_scaledFrameResidual_eq` express the residual Gram matrix after finite orthogonal projection. The proof of `abstract_schur_krein_residual_coupling` then applies `abs_real_inner_le_norm` to the two residual vectors and cancels `R²`; its `R=0` branch proves every frame vector zero. This is precisely residual Cauchy–Schwarz, including the singular case.
- In `OriginAllocationUniquenessAndCoupledSphereGain`, `origin_pair_lagrange_defect` is the two-dimensional Gram determinant identity. `origin_pair_support_eq_iff` and `origin_allocation_cost_eq_lower_iff` derive the support and equality conditions from it. On the stated positive-total strata, equality forces the allocation ratios. Boundary strata must retain their separate equality conditions; the positive-total uniqueness theorem does not assert uniqueness there.
- Hyperbolic multiplier composition follows the addition formula; the so-called Casimir divides the already-proved difference by its positive `cosh` factor and returns the original autocorrelation. It does not supply another independent invariant.

These facts delimit the foundations. Mixed-valuation recovery and quantitative observation bounds have conclusions beyond these identities, but their novelty requires separate comparison with higher-correlation reconstruction and phase retrieval.

- [x] `ClassicalFoundationBoundaries.lean` passes its direct artifact-producing `lake --old env lean -j 1` audit with exit 0 and no diagnostics.
- [x] All six public theorems have no mathematical premise binders. Clean `/tmp` axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Leaf wired without compiling the umbrella.
- [x] Corpus index refreshed. Formal lint checked: no owned wiring or proof-placeholder errors; the global gate fails on concurrent package-root `TransHorizonIncidenceMechanics.lean` placement, outside this component's scope.
- [x] [All boundary allocation cases](biscale-allocation-boundaries-1810.md) are formalized and pass the final named-source audit. `pair_support_eq_iff` requires zero determinant and nonnegative dot product; `allocation_eq_iff` separates the zero-total case, where every vector must vanish. These cover the actual nonnegative block sizes by substituting their absolute values.
- [x] Item-2 mathematical accounting complete: residual projection/Cauchy–Schwarz, allocation norm geometry, hyperbolic addition/defect and additive-only joint zero-set rigidity are explicit. Mixed quintic recovery and raw noisy recovery have conclusions beyond these identities, without an originality claim.
