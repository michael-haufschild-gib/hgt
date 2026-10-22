# BAG actual compact Mellin coefficients and Euler attachment

2026-10-06,01ax. Next hard local obligation after compact parameter multiplier.
Construct the actual coefficient family, not an assumed uniform derivative
budget. On E=QuadrantLogSpace choose a fixed smooth physical cutoff chi, equal
to1 on a neighborhood of[1/4,4]^2, with compact support inside(1/8,8)^2.
Choose a compact smooth parameter cutoff eta equal to1 near[1,2]^2.
The actual joint coefficient is
 A(sigma,x)=eta(sigma)*chi(x)*exp(sigma0*log(x0)+sigma1*log(x1)).
For every sigma in[1,2]^2 this agrees exactly with the desired weighted
physical cutoff. Prove joint smoothness: on tsupport chi both coordinates
are positive; off tsupport chi the complete product is locally zero.
Prove joint compact support in tsupport eta times tsupport chi. This pays
the compact C1 data required by the new uniform multiplier theorem.

First Euler coefficients are -xi*partial_i A and -xi*A. Smooth directional
derivatives preserve compact support, as the corpus D4BMModularCore
InteriorTest.derivative proof explicitly implements with fderiv_right,
clm_apply, HasCompactSupport.fderiv_apply and tsupport_fderiv_apply_subset.
Therefore their uniform fractional multiplier constants follow from joint
compactness as well. The exact product/chain rule then transfers first log
derivatives while retaining the physical first derivative of f. Combine
with LocalLogFractionalEnergy and DirectionalGagliardoFourier to reach the
needed1<s<3/2 local Mellin energy. Actual exterior attachment remains separate.

Search69915 /tmp/bag-compact-mellin-multiplier-search-01ax.json nonpartial,
66802allindexed,noerrors,index1255384,coverage1255396=current;
semanticcoverageunmeasured; all20candidate20source+ingredientsetread.
Useful existing native general cutoff theorem:
RHTower.D4BMRetardedCompactWeakRealization.exists_contDiff_cutoff in
ThetaCuspHawkingBMRetardedCompactWeakRealization.lean:33-77, source read and
compiled olean present. This gives compact smooth support in any prescribed
open set and value1 near a compact. PhysicalLogChart/PositiveQuadrantMellinLines
have pointwise smooth/Schwartz structure but do not give uniform moving
Schwartz budgets. Use the new fractional estimates instead.

Proof construction underway; no closed actual weighted H^s transfer claimed.
Remaining BAG hard problems include full Mellin tails, lower-growth completed
arithmetic envelope, moving-test cancellation/full sharp-action bridge,
growing moments/cofactors and deterministic common-height return. RH open.

2026-10-06 01ax complete coefficient/Euler scratch34458/log05 PASS.
Actual fixed physical cutoff is1 on an OPEN neighborhood of the stationary
box and has compact support strictly inside the positive quadrant. Joint
parameter cutoff equals1 throughout the complete[1,2]^2 parameter box.
Actual joint coefficient has proved global smoothness/compact support and
exact agreement with chi(x)*exp(sum sigma_i log x_i) on those parameters.
Both literal first Euler coefficients are smooth/compact with support inside
the original coefficient support. All three coefficient types have a
parameter-uniform admitted fractional spectral bound from the new multiplier
leaf. Exact first log derivative now proved, retaining both coefficient
and physical input derivatives. Four key public axiom prints standard3.
Earlier failures: explicit toLp order, projection scalar instances, endpoint
metavariables in open-box topology, ENNReal notation scope, and function
composition beta-reduction. No heartbeat/resource increases or mathematical
assumptions were introduced. Current log06 appends the common physical
support bound, uniform L2 mass, and exact Schwartz realization. Production
closure not yet asserted; full H^(1+theta) energy assembly remains next.

2026-10-06 01ax actual compact Mellin localization CLOSED.
CompactMellinLocalization343/API21: production56153 emptyPASS, all21 imported
axioms10859 standard3, index75708PASS/importonce/scoped diffcheckPASS.
Lint30292:362warnings,18 unrelated unreachable, no ownedfinding; exactnames
P2/P3 bag-actual-compact-mellin-localization. Actual A,B_i,C_i, uniform mass
and fractional bounds, exact first Euler law and exact Schwartz realization
are closed. Full log H^(1+theta) assembly is active in
P1 bag-local-mellin-sobolev-transfer; no RH/endgame closure claimed.
