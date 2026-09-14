# Full temporal/metric/QNM matching: complete finite-time boundary attached

RH and full matching remain unproved. Frontier map is READ ONLY. No numerical computations, Git, launch.sh, #print axioms, heartbeat increases, full/dependency/umbrella builds. One owned foreground Lean/Lake process at a time. See `mem:rh/hb-original-compact-cusp-time-0914cd` for compact source restoration.

## Authoritative new state
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalModularOrbit.lean` now 1351 lines. Namespace `RHTower.D4BMOriginalModularOrbit`.
- `mode_static_top_flux` line1083 proves actual independent-frequency static complete boundary reduction, retaining forcedContact.
- `mode_complete_boundary_time_transfer` line1276 proves on 0<a<=b,R>1,Y>0, nonreal w:
  integral_a^b (B0-B1/f)/R^2 = [-lambda*[T(U,W)]_a^b + w*integral_a^b (mu*T(W,U)-T(Delta U,W)-2lambda*T(U,W)-R^3*T(F,W)/f)]/(R^2*f).
  U actual sourceScalar, W actual modeScalar, F complete originalForcing, f=R^2-1,lambda=mu-2,T=topFlux.
  Full forcing sign positive in C(U)=Delta U-2U+R^3 F/f. Both original endpoints preserved. Every compact temporal/angular integral and Fubini premise derived from actual exterior smoothness. Reader radial derivatives and source temporal derivatives disappear from this integrated boundary.
- New private helpers: top_integrable, partial_scale_germ, mode_normal_contact, mode_normal_time, coordinate_line_diff, normal_orbit, modeTopDensity, modeTopDensity_integrable, modeCompleteTopFlux_integral, mode_static_top_density, top_rectangle_continuous, top_time_swap, top_time_integrable, time_point_integrable, time_point_transfer, top_time_inner_integrable, top_time_transfer, top_forced_decomposition.

Clean scratch passed; isolated exact leaf audit passed 99s/2jobs without warnings. No dependency builds; 4540 existing dependency oleans copied into isolated cache, package caches symlinked. Source SHA256 675f599e2ac27a75414455b22dc20da213a17dd073a18597383cc2363d281bcf. Audited .olean 4098936bytes; 5 target artifacts copied back, bytes verified. Existing RHTower umbrella import line17792. Lint sole unrelated error remains unreachable Sieve.KloostermanGlobalCollisionCoprime; 159 existing large-file warnings. Do not fix other agents' module.

## Exact next bridge, paper proved but not Lean
Own fact log F199 updated to formal; F200 added analytical compact-time complete cusp boundary consequence. Matching card section 'Complete compact-time cusp boundary — paper consequence, Lean pending'.
For W=ell(p)*S_r, S_r~c_r y^beta, U~sum A_i(p)y^alpha_i and original forcing F~sum F_i(p)y^alpha_i, complete integrated coefficient:
K_i = [-lambda*beta*c_r*[ell*A_i]_a^b + w*c_r*integral_a^b ell*((mu*alpha_i-beta*alpha_i*(alpha_i-1)-2lambda*beta)*A_i-beta*R^3*F_i/f)]/(R^2 f).
F_i=(forcingValueCoefficient+forcingLaplacianCoefficient*alpha_i*(alpha_i-1))*principalAmplitude_i.
F198 source angular jets uniform over bounded null rectangles; original forcing splits exactly into bounded time coefficients times fullSquarePotential and its angular Laplacian (OriginalMetricCusp.original_forcing_laplacian line179). Reader amplitude bounded compact time, native reader tails uniform. In logheight, normal derivative=e^-k d_k, Delta=e^2k d_X^2+d_k^2-d_k. These yield uniform rapidly decaying remainder for all four F199 transfers, hence integral complete B minus sum K_i exp((alpha_i+beta-1)k) ->0.
OriginalCuspFlux.fluxExponent_nonzero_original excludes every constant exponent for original diagonal/reflected readers, independent temporalw. Thus compact-time complete boundary finite part zero. NOT Lean yet; a=0 and unbounded time/horizon remain open. This is next direct full-matching bridge, not a replacement goal.

## Relevant source facts / pitfalls
OriginalReaderEquation.modeScalar_value line548: W=exp(-w*(p-tortoise R))*radiusLift(modeProfile)(R)*literal angular scalar. radiusLift=R*g(tortoise R), NOT g/R. Multiplying verified static density by f=dR/dx gives exactly the card's D_w=mu exp(-w(p-x))g[lambda(m_p+wm)+wF/z_h], z_h=f/R^2, after source-period restoration. The first-moment unbounded corner -J1-Klog2 remains analytically specified but original-current attachment open.
Lean: ContDiffAt smooth order infinity is (infinity:NatInfinityOmega), not top omega; use `(show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)` in `.of_le`. `ContinuousOn.intervalIntegrable_of_Icc` ordinary argument order is hab then hcontinuous (dot syntax relocates latter). `deriv_add` rewrite may require change to explicit function addition. orbitDerivative W0 under coordDeriv needs function-level equality to coordDeriv1 W. Top bounds -1/2 vs -(1/2) normalize with neg_div. MeasureTheory.intervalIntegral_intervalIntegral_swap (Prod.lean498) directly handles compact rectangles.

## Research scope
Broad/deep corpus searches inspected candidates/source arguments/methods/ingredients: most source_only; Fubini found applicable actual rectangle helpers, corner search partial and no complete-action theorem. Broad arXiv memory/resolvent queries found 2608.31172v1 (superfluid zero zeroth moment/nonzero first-moment memory at EFT order) and2602.19981v1 (operator-valued scattering for time-dependent memory medium). Neither supplies an HB premise; links/scope in own matching card.
Last experiment-review turn added no proof. This turn is verified progress. All owned Lean/Lake/search/lint handles terminal. Own /tmp/hb-ce-* paths are being removed after memory save. No subagents. Goal stays active.