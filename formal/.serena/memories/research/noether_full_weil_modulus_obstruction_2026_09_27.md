# Full arithmetic and CCM modulus obstruction (2026-09-27)

Continuation of `mem:research/noether_three_positive_energies_small_gap_kernel_orientation_2026_09_27` and `mem:research/noether_cut_conservation_exact_weil_ground_criterion_2026_09_27`.

RH is not proved or falsified. Goal remains active, completion only on formal RH proof. No extra axioms, sorry, numerical experiments, or heartbeat overrides. Own foreground leaf audits only, one at a time. No full or umbrella build.

## New completed leaf modules

1. `GaloisForLFunctions/RHTower/ThetaRealGroundPolarization.lean`.
   - namespace `RHTower.ThetaSourceWard`.
   - `thetaComplexify phi = phi.postcompCLM Complex.ofRealCLM` for real Schwartz phi.
   - `thetaRealArithmeticQuadratic phi = thetaFullArithmeticQuadratic (thetaComplexify phi)`.
   - For real Schwartz phi,psi ordered by every supported difference x in psi, y in phi satisfying x-y>0, and avoiding log n for n>=2, prove literal full polarization:
     `Q(phi+psi)-Q(phi-psi) = 4*thetaGammaPolarGroundCrossPairing phi psi`.
   - `thetaRealArithmeticQuadratic_ordered_difference` first gives one-sided lag product integral; every ground mass and Gamma diagonal difference cancels by disjointness; every prime cross difference cancels by atom avoidance. n=0,1 handled by log n=0.
   - `thetaOrderedGroundCross_eq_pairing` transports positive-lag integral to two-variable pairing with shear `(u,x)->(u+x,x)`, using actual measure-preserving equivalence. Integrand vanishes for u<=0 by ordered supports. No Fubini/divergent-integral shortcut.
   - Final `thetaRealArithmeticQuadratic_disjoint_polarization` combines these.

2. `GaloisForLFunctions/RHTower/ThetaArithmeticModulusObstruction.lean`.
   - `exists_compact_thetaArithmetic_modulus_increase`: actual compact real Schwartz f,g, g=|f| pointwise, equal theta ground mass, and Q(f)+c M(f)<Q(g)+c M(g) for EVERY scalar c.
   - Construct f=phi-psi, g=phi+psi using nonnegative disjoint positive cross witness and exact full polarization.
   - `exists_thetaArithmetic_modulus_increase` forgets compactness.
   - `not_thetaArithmetic_modulus_contracts c` for every scalar mass shift.

3. `GaloisForLFunctions/RHTower/CCMThetaModulusObstruction.lean`.
   - namespace `RHTower`.
   - `ccmThetaSourceOfCompactRealProfile a phi hc hs` constructs literal smooth compact CCM source u(x)=k(x)*phi(x), with support in aperture.
   - `ccmThetaGroundProfile_ofCompactRealProfile`: division by positive actual k returns thetaComplexify phi exactly.
   - `exists_ccmSmooth_modulus_increase`: exists positive aperture and actual compact smooth complex CCM sources u,v with v(x)=norm(u(x)), equal physical L2 norm squared, and full restricted Weil Q(u)+c norm(u)^2<Q(v)+c norm(v)^2 for EVERY c.
   - This upgrades earlier regular-kernel sign witness to COMPLETE RH-equivalent arithmetic form; all prime/Gamma/pole terms present.
   - `not_ccmSmooth_modulus_contracts c`.
   - `ccmSmoothLocalPotentialEnergy V u = integral V(x)*norm(u(x))^2`, for V:C(R,R).
   - `integrable_ccmSmoothLocalPotentialDensity`: finite because source compact and V continuous.
   - `exists_ccmSmooth_modulus_increase_all_local_potentials`: ONE fixed compact smooth pair defeats modulus contraction after EVERY continuous local potential. Potentials cancel pointwise because moduli agree.

## Strengthened earlier leaf

`ThetaGammaPolarKernelOrientation.lean`: existing positive-cross construction now exposes compactness in `exists_disjoint_positive_compact_thetaGammaPolarGroundCrossPairing`. All old support/atom avoidance/integrability/strict positive cross conclusions retained, plus HasCompactSupport phi and psi. Original `exists_disjoint_positive_thetaGammaPolarGroundCrossPairing` preserved as a corollary, so old API unchanged.

## Interpretation and remaining mathematics

This is NOT a negative Q witness and NOT a falsification of RH. Positive semidefinite quadratic forms can fail modulus contraction. The result rules out the strategy of making this exact form satisfy modulus contraction by scalar mass shifts or continuous local multiplication potentials. It also rules out an off-diagonal nonpositive-kernel argument in actual theta ground coordinates.

Next real task: quantitative mixed-term estimates, not sign-only positivity. For two real source directions with positive diagonals a=Q(u),d=Q(v), mixed B, a negative direction occurs if B^2>a*d. The corpus already contains finite Schur criteria; search to avoid merely repackaging them. No concrete strict determinant violation or universal bound obtained here.

Useful existing translation infrastructure found through corpus search: `CCMRestrictedWeilFullTranslationCovariance.lean`, public `ccmRestrictedWeilSourceQuadratic_translate_full {a b} h (hab:a+abs h<=b) u`: full source quadratic translation invariant on whole domain, including poles. Together with small-aperture gap it may give diagonal bounds for narrow bumps separated in large apertures. Need quantify atom-free bump widths versus cross growth before suggesting falsification.

## Validation

All four changed/new leaves individually passed foreground `lake --old env lean Leaf.lean -o .lake/build/lib/lean/.../Leaf.olean`; fresh oleans emitted. Original polarization reaudited after the orientation strengthening. No warnings in final audits. Three new leaves wired into RHTower umbrella, already imported by MainTheorems. Eleven endpoint #print axioms checks passed, every one depends only on propext, Classical.choice, Quot.sound. Audit scratch work/noether_modulus_axioms.lean deleted and absence checked. Index refresh succeeded (1 changed; concurrent chats had indexed earlier additions). git diff --check passed. Global lint --check-generated reports only four unrelated concurrent unwired modules: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving. No generated staleness or our own unreachable modules. No own live process remains. Together with earlier batch this logical turn produced seven new audited/wired leaves; no RH proof or falsification.

## Lean lessons

- Use `add_apply`/`sub_apply`, not deprecated SchwartzMap.add_apply/sub_apply.
- `simp only [definition, hsq, thetaComplexify_apply]` can unfold inner terms before matching hsq. First `unfold definition; rw [hsq,hsq]`, then simplify casts.
- For custom MeasurableEquiv structure, measurable_toFun proof needs `change Measurable (fun p:Real*Real => ...)` before fun_prop.
- Explicit `rw [thetaContinuousLinkMeasure]` before `Measure.restrict_prod_eq_prod_univ`; rw did not unfold abbrev by itself.
- IsCompact union of two tsupports gives `.isBounded.exists_pos_norm_lt`; convert norm real to abs for common aperture.
- Compact profile source constructor: support inclusion from nonzero product implies phi nonzero; `hc.mono` and `closure_mono` handle compactness/tsupport.
- Final scalar-add strict inequality was simplest `linarith` from hlt0; simp around add_lt_add_right unexpectedly oriented addition differently.
