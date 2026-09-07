# HB actual interior elliptic H² regularity — 2026-09-07

Goal active; RH unproved. Frontier map docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md remains READ ONLY, untouched. No new universal-law STATUS entry identified. Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

## Verified concrete progress
For the ACTUAL full-forcing weakResponse constructed previously, EVERY compact smooth interior localization is planar Sobolev H², its actual Laplacian is L², and its Fourier transform has an L¹ representative. No supplied regularity/differential equation/critical-line premise in final actual result. Full source and BOTH cutoff commutator terms retained. This is actual interior regularity, not global smoothness or physical causality.
Prior domain construction: `mem:hawking_bm_constructed_modular_energy_domain_weak_response_2026_09_07`. Prior full forcing: `mem:hawking_bm_full_angular_forcing_and_xi_modularity_2026_09_07`.

Four canonical leaves (full paths under formal/GaloisForLFunctions):
- RHTower/ThetaCuspHawkingBMInteriorDistributionEquation.lean: 213 lines, 10 public theorems, namespace RHTower.D4BMModularCore.
- RHTower/ThetaCuspHawkingBMPlanarLocalDomain.lean: 206 lines, 5 public, same namespace.
- HTGeometry/PlanarSobolevLaplacianGain.lean: 42 lines, 2 public, namespace GaloisForLFunctions.HTGeometry.
- RHTower/ThetaCuspHawkingBMInteriorEllipticRegularity.lean: 230 lines, 11 public, modular namespace.

Proof card docs/drafts/pipeline/3-formalized/hb-interior-elliptic-regularity.md has dependency-closed paper argument and exact audit status. Live hb-global-angular-resolvent.md updated; prior modular-energy-domain proof card's remaining bridge links this H² result. No other route docs, no frontier/status changes.

## Exact construction
Original mu=UpperHalfPlane.volume.restrict fd (dxdy/y²), Space=Lp ℂ 2 mu. V=energyDomain, J=embedding. Actual h=weakResponse q branch, both actual Xi branches. L=parameter q branch. F=forcingVector q branch, complete mixed cusp-subtracted Einstein forcing, no truncation.

InteriorTest.derivative and conjugate construct smooth compact tests. InteriorTest.modularField periodizes g globally; modularField_eq on closed fd and modularField_deriv on open fdo prove actual values/derivatives. InteriorTest.energyTest uses frameGraph of periodized conj(g). energyTest_scalar is ae conj(g); energyTest_gradient is exactly massTest(derivative g dir_i). Existing completed testConstraint then moves BOTH derivatives onto g. full_response_distribution_equation and full_response_integral_equation give complete native second-order distribution equation.

InteriorTest.localValue g u z=g(z)*u(ofComplex z). Any compact interior localization of any u:Space is planar L², proved as follows (critical mechanism):
- Under nu=map coe mu, y^n*g*u is L² for all n: smooth compact coefficient y^n*g is globally bounded, multiply mapped u via MemLp.of_le_mul.
- n=2 case is L¹ under finite nu. Rewrite map_measure_eq and apply integrable_withDensity_iff_integrable_smul to cancel y²/y². This gives planar L¹ of g*u on cell, then globally via zero support outside cell.
- n=1 norm² case cancels y²/y² to give planar square integrability. Use the prior L¹ measurability with memLp_two_iff_integrable_sq_norm. No unproved global ofComplex measurability or continuous representative needed.
- InteriorTest.localValue_memLp and full_response_local_L2 apply to h, both completed gradients, and F.

InteriorTest.mulSmooth g a ha is the compact product test. InteriorTest.divHeight g n is g/y^n: smooth by positive height on support and identically zero germs off support; also smooth across real axis. scalar_planar converts native g*u moment to planar (g/y²)*u; height_sq_planar cancels native y². laplacianTest packages the literal sum of two directional second derivatives as a compact interior test. full_response_planar_equation gives Delta_E h=(Lh+F)/y² distributionally.

InteriorTest.localVector g u is actual planar L² vector; localDistribution g u is its tempered distribution (not an interface). localDistribution_apply pairs with original representative and arbitrary Schwartz psi.
mass_planar: inner(massTest g,u)=integral (g/y)*u.
flux_planar: inner(fluxTest g v,u)=integral partial_v(g)*u.
energyDomain_planar_derivative: integral (g/y)*D_i h + integral partial_i(g)*Jh=0 for EVERY h:V.
Applying this to g*psi proves literal product weak derivative:
localDistribution_derivative: partial_i T(g,Jh)=T(partial_i g,Jh)+T(g/y,D_i h).

full_response_planar_gradient applies original full weak forcing equation to actual energyTest. Apply it to g*psi and separate exact product derivative to prove:
full_response_local_current_divergence:
sum_i partial_i T(g/y,D_i h)=sum_i T(partial_i g/y,D_i h)+L*T(g/y²,Jh)+T(g/y²,F).
Actual Complex.orthonormalBasisOneI and distributional Laplacian sum then prove full_response_local_laplacian:
Delta T(g,Jh)=sum_i T(partial_i²g,Jh)+2*sum_i T(partial_i g/y,D_i h)+L*T(g/y²,Jh)+T(g/y²,F).
Every RHS term is a proved planar L² distribution. No omitted commutator and no assumed classical derivatives of h.

Generic besselPotential_two_planar proves exact mathlib normalization B_2 u=u-(2*pi)^(-2)*Delta u using Fourier multiplier addition and actual Laplacian symbol. planar_sobolev_gain_two: u,Delta u in H^s imply u in H^(s+2), via Bessel composition. This theorem has standard analytic input hypotheses; final ACTUAL response discharges all internally.
full_response_local_laplacian_L2 gives actual L² representative of localized Laplacian. full_response_local_H2 applies gain at s=0. full_response_local_fourier_L1 applies mathlib Sobolev Fourier embedding calculation: real dim ℂ=2<2*2.

## Validation — do not redo old checks
All seven development scratch modules passed lake env lean, no diagnostics. Four EXACT canonical source leaves individually final audited via lake build <module> in cache-only package: 6.8s,22s,2.5s,10s. Only these4 new leaves compiled; dependencies reused. Exact canonical/audit source equality checked, each umbrella import occurs once. Exactly8 new olean/ilean artifacts exclusively installed and compared. No umbrella/full/dependency builds.
Exactly28 NEW public theorem axioms audited ONCE via lake env lean scratch; all and only propext,Classical.choice,Quot.sound. No diagnostics. Do not re-audit prior29,23,27 or these28 without actual changes requiring it.
Index regenerated. Scoped whitespace clean. Global lint NOT passed: first run saw unrelated MontgomeryPrimeSideBounds missingimport+2 sorry placeholders; current file then changed and placeholders disappeared. Final refreshed index+lint run reported only unrelated missing umbrella import RHTower.MontgomeryPrimeSideBounds and stale formal/LEAN_API.md during concurrent source edits. No errors in the4 new leaves. Preserve unrelated ongoing work; do not wire unverified others' source merely to turn lint green.
All owned Lean/Lake/index/lint handles terminal. Owned scratch /tmp/hb-angular-regularity.sgaSMi, cleanup at end after bounded nonsymlink inventory. No computations/experiments, commits, subagents. Frontier untouched.

## Next actual hard steps
Bootstrap higher interior Sobolev regularity and construct a smooth representative of THIS actual weak response. Current mathlib Analysis/Distribution/Sobolev.lean has MemSobolev.mono, .lineDerivOp, .laplacian, .fourier_memL1 and bounded Fourier multiplier preservation. It lacks the needed generic physical-space smooth-coefficient Sobolev multiplication/bootstrap argument; prove it rather than assume it. The Bottcher/Brolin/WeylLemma corpus result requires a CONTINUOUS weakly harmonic function and does not directly discharge this variable-coefficient L² response. Potential route: integer derivative characterization + Leibniz yields compact smooth multiplier preservation; localize with nested cutoffs, use actual commutator and gain2 recursively. Alternatively obtain actual continuous representative from Fourier L¹ then establish further regularity rigorously. Do not treat H² or Fourier L¹ alone as C∞.
Next global obligation: carry weak equation/regularity across joined modular seams and stabilizer/orbifold charts using original FULL globally modular core, not interior-Dirichlet closure. Build global cusp-cutoff extension (naive chi(y)H0 only cellwise), assemble full angular field, prove physical vector metric causal/horizon/radial/gauge/left-QNM conditions. SS/VV sectors and independent fixed Hawking-clock extinction remain open; no RH conclusion supplied.

## Exact Lean repairs worth reusing
SchwartzMap.smooth takes an ENat argument: use psi.smooth ⊤ (not bare smooth or smooth ∞ with current scopes). ContDiffAt.div only same scalar/codomain; for real smooth complex quotient use hf.mul (hg.fun_inv hne). off-support constant smoothness needs explicit c:=(0:ℂ). isClosed_closure, not recalled isClosed_tsupport. fderiv support lemmas need explicit f:=fun x=>fderiv ... x v to avoid interpreting linear-map input v as spatial variable. sum_inner is correct; inner_sum_left absent. integral_finsetSum is current (old integral_finset_sum deprecated). add_apply/smul_apply replace deprecated ContinuousLinearMap variants.
Avoid `change` through large distribution multiplier maps; prove instantiated multiplier_add then `simpa only [Pi.add_def,...] using hm`, eliminating isDefEq timeouts. RCLike.real_smul_eq_coe_smul (K:=ℂ) handles mixed real/complex Fourier normalization. Complex.coe_orthonormalBasisOneI rewrites basis to ![1,I]; basis equality is not rfl. Distribution lineDerivOp evaluates at -partial psi, so rw map_neg explicitly. LineDeriv.lineDerivOp_add and module tactic close final exact cutoff algebra.
