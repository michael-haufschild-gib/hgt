# Cycle 26 complete: strict total mass, actual radial/angular defect, scoped periodic toy

Selberg all-congruence 1/4 goal ACTIVE and UNPROVED. Prior turn is progress, not blocked. No assumed lower bound, core inverse, lift, new axiom or admission.
See mem:selberg/actual-core-stokes-and-quarter-form-2026-09-08 for cycle25 standard-area Green and complete Qcore+B+S identity.

## Durable state
Parent docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecturing-loop.md updated with completed26 and next27.
Paper/audit docs/drafts/pipeline/3-formalized/selberg-positive-mass-and-radial-defect.md.
Failed shortcut with positive salvage: docs/drafts/pipeline/5-failed/selberg-scalar-norm-energy-reconstruction.md.
Old cycle25 card now links to completed strict-mass proof; do not repeat mass positivity as a remaining gap.

## 3 finished modules (formal/GaloisForLFunctions/RHTower)
### SelbergMaassTraceMass,178 lines
Imports TraceArea + Mathlib.NumberTheory.Modular only.
density_continuous on ℍ from density_contDiffOn and continuous_coe.
density_pos_interior: actual nonzero density point, exists_smul_mem_fd, density_invariant, fd_eq_closure_fdo and positive open set yield z∈fdo with D(z)>0.
massDensity p := D(ofComplex(point p1 p2))/p2², nonnegative and continuousAt positive heights.
coreMass_pos_of_interior: z∈fdo, D(z)>0, z.im<Y => coreMassY>0; support∩domain is a neighborhood, hence positive Lebesgue measure with actual core integrability.
exists_coreMass_pos: ∃Y≥1 coreMassY>0.
sliceMass: literal unit-period hyperbolic trace slice.
horizontal_mass_slice: full domain slice above1 =sliceMass using actual period1.
coreMass_decomposition: fixed lower side part +∫1..Y sliceMass.
tailMass_nonneg all actual f.
totalMass_eq_one: λ∈(0,.25),Y≥1 => coreMassY+tailMassY=coreMass1+tailMass1, using integral_interval_add_Ioi and actual tail integrability.
totalMass_pos line163: same source and cutoffs => STRICT totalmass>0.
core_boundary_strict_neg line171: actual exceptional source,T≥0 => Qcore(expT)+boundarySum(T)<0 from prior upper bound and strict mass.
This is a necessary property of an exceptional source, NOT a contradiction/proof of Selberg.

### SelbergMaassTraceRadial,232 lines
Imports TraceBoundary + mathlib InnerProductSpace.Calculus and Calculus.LocalExtr.Basic.
Actual definitions: directionalEnergy E_v=∑normSq(D_vFq), realPairing P_v=∑Re(D_vFq*conjFq), radialResidual R_v(c)=∑normSq(D_vFq-c*Fq) for REAL c.
current_eq_realPairing proves actual C_v=D_vD=2P_v from actual normSq differentiation/finite sum.
radialResidual_expansion: R_v(c)=E_v-c*C_v+c²D.
radialSlope c_v=C_v/(2D).
radialResidual_minimization D>0: R_v(c)=R_v(c_v)+D*(c-c_v)².
radialResidual_nonneg, radialResidual_minimum_unique, radialResidual_eq_zero_iff (every component derivative equals the same real c times its value).
amplitude :=sqrt(D∘ofComplex); amplitude_dir from actual sqrt chain rule when D>0.
directionalEnergy_decomposition, directionalEnergy_eq_amplitude_add_residual.
angularEnergy A=R_1(c1)+R_I(cI), nonnegative.
gradientDensity_eq_radial_add_angular /quarterDensity_eq_radial_add_angular at D>0: full energy =actual scalar-amplitude energy+A.
DO NOT assert amplitude smooth at common zeros.
current_zero_of_density_zero from nonnegative actual D local minimum.
density_mul_directionalEnergy and density_mul_gradientDensity line177 hold EVERYWHERE (including zeros): D*G=(C1²+CI²)/4+D*A. No norm-smoothness premise.
angularEnergy_eq_zero_iff classifies both derivative directions being componentwise radial with common real slopes.
trace_fisher_identity line218 holds everywhere: D*ΔD=(C1²+CI²)/2+2D*A-2λD²/y².
This retains the actual Maass equation/eigenvalue. It is NOT a nonnegative core/Bessel estimate.

### SelbergScalarPhaseToy,97 lines
Imports TraceEnergy+mathlib ExpDeriv, no old broad research.
phaseField c z=exp(I*(c*z.re)).
phaseField_contDiff, normSq=1, actual dir1=I*c*F, normSq derivative=c², literal scalar amplitude constantly1 and derivative0.
integer_phase_periodic n: c=2πn gives F(z+1)=F(z).
scalar_trace_does_not_determine_energy line81: explicit two smooth period-one fields at n0 andn1 have identical scalar squared norms and strictly different actual derivative energies at every z.
IMPORTANT SCOPE: toy fields NOT Maass, NOT cusp, NOT inversion-invariant. It refutes norm-only reconstruction for smooth periodic fields only. DOES NOT refute source recovery of G from ΔD and λ (already proved cycle25). No assertion that D+Maass equation loses full energy. No explicit zero-mean toy integral theorem was added.
Positive salvage is actual source radial residual/minimizer/zero classification+Fisher identity above. No whole-route no-go.

## Corpus-grounded derivation
Queries integral positive continuous and fundamental domain => LevinsonLittlewoodZeroCount positive support and PeterssonInnerProductLevelOne.eq_zero_of_peterssonInner_self_eq_zero (read1..160), modular domain closure method; Mathlib.NumberTheory.Modular actual exists_smul_mem_fd and fd_eq_closure_fdo.
Queries Gram determinant, Fisher phase, Lagrange identity => ProjectiveQuantumFisherValue (read1..160), ConstitutivePolarAmplitudeFisherPhase (read phase/polar sections177..216,550..615), RiemannGaussian/SymmetricPickSchur two-coordinate Lagrange square (90..116), XiResolventTraceCauchySchwarz pair identity(80..110). Source formulas adapted with narrow imports; DON'T IMPORT these modules that import Mathlib/research umbrellas.

## Next actual task, cycle27
Main missing theorem remains source-derived NONNEGATIVE lower bound for Qcore+B. Strict physical mass now finished.
Construct actual normalized finite-family direction and modular S/T component constraints; keep original zero Fourier means and angular residual. Scalar norm does not preserve signed/complex mean constraint, and norm regularity at common zeros needs care.
Prior Schur/DtN formulas do not produce actual blocks, inverse, or coercivity; must construct/prove actual response if using them.
Potential sharper source-specific test: actual sqrt(trace) has positive horizontal mean somewhere, so it cannot inherit the original vanishing Maass constant term. Not yet formalized; existing Mass interior positivity and Mean constant-term results provide concrete path. Avoid mere generic conditional Selberg wrapper.
Exact radial/angular identity gives invariants, not sign proof; don't automatically assume positive pointwise angular quarter bound. Retain all original source constraints.

## Audit terminal
All3 scratch and direct source lake env lean checks passed without warnings.
Three sequential LEAN_NUM_THREADS=1 lake build <module> final audits passed, rebuilt only named target; no full/umbrella builds. Logs /tmp/selberg_trace_mass_build.log (6.3s), /tmp/selberg_trace_radial_build.log (68s), /tmp/selberg_scalar_phase_build.log (3.1s). Cached dependency warnings/info replayed, no new warning.
46 publicdefs/theorems audited by lake env lean /tmp/selberg_mass_radial_axioms.lean. 46reports, none missing, no errors, only propext/Classical.choice/Quot.sound or none. Logs /tmp/selberg_mass_radial_axioms.log and declarationlist /tmp/selberg_mass_radial_declarations.txt.
All3 wired in RHTower around16242 and indexed; corpus returns totalMass_pos andtrace_fisher_identity. Whitespace checks passed.
LATEST authoritative global lint FAILED ONLY unrelated UNTRACKED UNWIRED HTGeometry.FokasLenellsUniformization. Prior5cycle25errors resolved concurrently. Not edited/wired. Logs /tmp/selberg_mass_radial_index.log, /tmp/selberg_mass_radial_lint.log. Don't claim global lint pass.
All task-owned Lean/build handles terminal0. No task commit/push. Shared tree other work preserved.

## Toolchain details
One task foreground Lean invocation at a time; poll same live handle terminal before next. No stale processes owned.
Actual continuousAt composition sometimes guesses partial point x y: supply explicit f:=funp:ℝ×ℝ=>pointp.1p.2.
Typed hi:IntegrableOn F(domainY) before Fubini rw avoids lambda transparency mismatches.
dir_sum then finite sum congr works; simp_rw with normSq_dir + quotientForm produced tactic-instance transparency error. Use individual hq proof and sum_congr.
ContDiffAt.norm_sq ℝ +normSq_eq_norm_sq verifies complex squared norm smoothness.
Use root smul_apply not deprecated ContinuousLinearMap.smul_apply.
Pure-phase ContDiff proof needs explicit Complex.ofRealCLM.contDiff.comp(...), fun_prop cannot infer that coercion here.
Literal function comp simplification Function.comp_apply needed for phase derivative ring.
Mass/Radial/Toy source and scratch all verified; don't repeat audits without changes.