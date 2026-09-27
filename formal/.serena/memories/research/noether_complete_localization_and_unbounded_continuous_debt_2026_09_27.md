# Full-source localization, bounded prime errors, and Noether separation — 2026-09-27

## Goal/status
Active user goal is RH proof via arithmetic conservation and Noether in both directions. RH remains UNPROVED and UNFALSIFIED. Do not complete goal. Previous turn classified progress; this turn also substantive verified progress. No blocker: next work concerns compensated continuous/local energy, not missing user input. No literature novelty claim.

Repo /Users/michael/Documents/code/hgt/formal. One own foreground Lean process at a time, no full/umbrella builds, numerical computations, sorry, new mathematical axioms, heartbeat increases, commits/pushes, or subagents. Preserve concurrent changes and builds. Final audits lake --old env lean <leaf> with -o corresponding .olean for consumers. Search actual Lean through ../scripts/formal_tools.py research and rg, not cards. Session init/manual/docs/l7 already done earlier. Parent memory `mem:research/noether_arbitrary_prime_island_profiles_2026_09_27` contains previous support-region result.

## Main new mathematics
Every actual compact smooth complex CCM source u has a CONSTRUCTED finite localization into arbitrarily narrow pieces with zero remainder, preserving physical L2 mass exactly. Each split retains sin(theta)*u and passes cos(theta)*u to the next split. Exact complete energy balance:
Q(u) = Q(remainder) + sum Q(pieces) - P_total + C_total.
P_total and C_total are actual convergent prime and signed Gamma/pole integrals, no bounds postulated.

All split errors combine into ONE common weight W(x,y)=2(1-K(x,y)), with 0<=W<=4 INDEPENDENT of split count. K is the overlap of the unit channel vectors (all sine pieces plus final cosine remainder). This is proved algebraically, not by simulation.

For a complete cover whose pieces fit radius delta balls, if dist(x,y)>=2delta then the combined weighted correlation equals exactly 2 Re(u(y)*conj u(x)). Long-range arithmetic correlations cannot disappear through finer local splitting.

At fixed aperture, existing small-total-support coercivity allows ANY requested margin L. Combined with constructed finite cover and mass conservation, local energy sum can exceed L*mass(u) for every L. Thus for every nonzero physical source, signed localization debt P_total-C_total is unbounded above under choice of finite localization. A fixed source already known to have strictly positive full Q exhibits this.

Sharper separation: for EACH fixed source u, EVERY chain has |P_total|<=K(u), where K(u)=4*integral |original prime cross density| is finite. Hence C_total can lie below ANY real bound under refinement, even on a positive actual source, although W stays in [0,4]. The singular continuous integral is not controlled by the pointwise bound alone; convergence of each finite chain was proved separately.

The compensated quantity remains controlled for EVERY finite chain:
|Q(remainder)+sum Q(pieces)+C_total-Q(u)| <= K(u).
It equals P_total before taking absolute values. The missing RH step is a SIGN/lower bound for the compensated local-plus-continuous energy relative to the prime contribution. Positive local pieces or conservation alone do not provide it.

Finally the SAME positive source can be chosen with the existing constructed global Noether/Newton phase flow. Its literal action has time-translation symmetry and conserved mechanical energy, while its localization continuous totals are unbounded below. This separates a genuine Noether charge from artificial localization error budgets.

## Eight new verified/wired modules
1. CCMFiniteLocalizationChain.lean
- ccmLocalizationRemainder, ccmLocalizationPieces, ccmLocalizationPrimeTotal, ccmLocalizationContinuousTotal recursively on List Schwartz(R,R).
- ccmLocalization_mass_conservation uses physical embedding norm squared, not form norm.
- ccmLocalization_energy_conservation exact balance above.
- remainder zero if input zero at x, or any list angle has cos(theta x)=0.
- tsupport_ccmSinLocalizedSource_subset_angle; ccmLocalizationPieces_support.

2. CCMFiniteLocalizationCover.lean
- exists_schwartz_localizing_angle c delta hd: compact angle, tsupport inside ball(c,delta), value pi/2 on ball(c,delta/4).
  Uses smooth Urysohn separator zero outside ball(c,delta/2), pi/2 on closedBall(c,delta/4); closure lies strictly inside ball(c,delta).
- exists_ccmFiniteLocalization_cover delta hd u: compactness finite subcover of tsupport u, list of angles, all pieces in radius delta balls, remainder identically zero. Actual construction, no partition premise.
- ccmSmoothSourcePhysicalMass_eq_zero_of_pointwise.
- exists_ccmFiniteLocalization_positive_assembly: exists universal delta,C>0, every aperture/source has angles with compactness, small pieces, zero remainder, mass conservation, C*mass<=sum local Q, exact full energy identity.

3. ThetaLocalizationChainWeight.lean
- thetaLocalizationChainOverlap []=1; K(theta::rest)=sin(theta x)sin(theta y)+cos(theta x)cos(theta y)K(rest).
- thetaLocalizationChainWeight=2(1-K).
- abs overlap<=1, weight>=0 and <=4.
- weight_cons = original two-channel weight + cos(theta x)cos(theta y)*remaining weight.
- cos/sin localized correlation formulas.
- ccmLocalization_correlation_conservation: remainder correlation + sum piece correlations = K*original correlation.

4. CCMLocalizationChainArithmetic.lean
- ccmThetaChainCross=W*Re(u(y)conj u(x)); exact cons decomposition.
- abs cross <=4*norm(u y)*norm(u x).
- ccmThetaChainPrimeDensity=Lambda(n)/sqrt(n)*chainCross(x,x+log n).
- ccmThetaChainContinuousDensity=full thetaGammaPolarScalingKernel(h)*chainCross(x,x+h).
- integrability of BOTH densities by finite recursive decomposition into established integrable single-split densities. Do not use W<=4 to infer integrability at continuous diagonal.
- ccmLocalizationPrimeTotal_eq_integral and ccmLocalizationContinuousTotal_eq_integral.

5. CCMLocalizationLongRange.lean
- small-ball correlation zero at distance>=2delta.
- ccmThetaChainCross_eq_twice_correlation_of_far for complete localization into delta balls.
- exists_ccmFiniteLocalization_arithmetic_reserve: every source gets compact angles, mass equality, C*mass<=Q(u)+primeIntegral-continuousIntegral, W in [0,4], exact far correlation, and exact iff Q(u)<0 iff sum local Q < primeIntegral-continuousIntegral. This is NOT an RH proof; the comparison is not assumed or proved globally.

6. CCMLocalizationUnboundedDebt.lean
- exists_ccmFiniteLocalization_prescribed_reserve a u L: for arbitrary real L, finite compact angles with mass conservation, sum Qpieces>=L*mass, exact balance.
  Uses exists_ccmSmooth_smallSupport_coercivity a L; choose support ball radius delta/4 and Real.volume_ball=ofReal(2r), discard positive half-form-norm term only in lower bound.
- ccmLocalization_signed_debt_unbounded u hmass B: actual primeIntegral-continuousIntegral>B, preserves mass, W bounds.
- exists_positive_ccmSource_unbounded_localization_debt: closed actual positive-Q witness, physical mass positive, unbounded signed debt. This is not a negative-Q witness.

7. CCMLocalizationPrimeBudget.lean
- ccmThetaPrimeCrossDensity_physical: original ground prime cross density equals Lambda/sqrt times physical correlation, all theta factors cancel.
- chainPrimeDensity_eq_weight_mul original density.
- ccmLocalizationPrimeBudget u=4*integral norm(original prime cross density), nonnegative.
- abs_ccmLocalizationPrimeTotal_le_budget: uniform over ALL finite chains.
- ccmLocalization_continuous_total_unbounded_below u hmass R, with compact angles, mass preserved, W bounds.
- exists_positive_ccmSource_bounded_prime_unbounded_continuous_localization: closed positive source, one K bounds all prime totals, continuous integral below every R available.

8. CCMNoetherLocalizationSeparation.lean
- ccmLocalization_compensated_energy_bound: unconditional all-source/all-chain bound above (including remainder).
- ccmSourcePhaseLagrangian u theta q v=v²/2-ccmPhaseLocalizationEnergy u theta q.
- ccmSourcePhaseAction=interval integral of this literal Lagrangian.
- ccmSourcePhaseAction_time_translation: shifts trajectory and endpoints exactly.
- ccmSourcePhase_noether_charge: v*dL/dv-L =v²/2+actual phase energy.
- exists_ccmNoether_positive_flow_unbounded_localization: same actual positive source has B>0, literal L differs from arithmeticPhaseLagrangian B only by Q(u), time-translation action symmetry, constructed global flow with conserved full energy, constructed Newton trajectory, bounded all-chain prime totals, and continuous totals arbitrarily negative on mass-preserving finite localizations.

## Corrected existing documentation (proof statements/bodies unchanged)
IMSLocalizationWeilForm.lean: header overstated scalar/pointwise lemmas as a fully constructed arithmetic IMS theorem and global reduction to a missing local spectral gap. Corrected to actual scope; points to CCMThetaArithmeticLocalization for exact arithmetic identity/convergence.
IMSBootstrapObstruction.lean: header claimed every IMS bootstrap impossible, but proved only a model budget threshold and comparison with L0>=1/2. Removed false comment `1/2 < 0.4994` and unsupported universal impossibility claim. Formal lemmas and names preserved. This model does NOT bound actual signed error below by the model budget.

## Verification and processes
All 8 new modules passed clean final leaf audits, with fresh .olean. Successful terminal sessions: chain68401, cover29063, weight88643, chainArithmetic91521, longRange25724, unboundedDebt63812, primeBudget32760, NoetherSeparation53848.
Both comment-edited legacy leaves also passed with fresh objects: IMSLocalizationWeilForm72133; IMSBootstrapObstruction87600.
25 #print axioms checks passed in LocalizationChainAxiomAudit.lean, session39722 exit0; EVERY list exactly propext, Classical.choice, Quot.sound. Scratch removed. No own live Lean build.
All eight imports wired in RHTower.lean; no umbrella build. Index98151 exit0,4 changed (concurrent chats index other changes too). Global lint12808 finished exit1: unrelated unreachable RHTower MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving; HTGeometry CompletedPseudoDiffOpAdicCompleteness, BoundedSplitting, ContractingLattice, ForwardHull, SemilinearAut, VectorArtinian, VectorLattice, DifferentialVariationalOppositeBoundaryPair. Also stale LEAN_API/LEAN_OVERVIEW due concurrent changes after first index. Final index57329 completed exit0, regenerated LEAN_API/LEAN_GAPS/LEAN_OVERVIEW and reported0 changed/0 removed (database had already incorporated concurrent source updates). No repeated global lint; its unrelated unwired-module failures remain. All own build/audit/index/lint processes are terminal. All own imports confirmed, Noether capstone at umbrella19818. No live own Lean build or lint process. No commit/push. Preserve prior intentional tracked TriangleAxiomAudit.lean deletion and all unrelated concurrent edits.

## Lean/API lessons
- List.sum_le_sum accepts (forall i in list, f i<=g i), then yields sum(map f)<=sum(map g).
- List.sum_map_mul_left list f r moves fixed scalar out of mapped sum.
- List.sum_eq_zero takes forall r in list,r=0; for map use List.mem_map to recover source.
- For Integrable (density u []), simp may make no progress through function-valued def. First prove density u []=0 by funext/simp, rw equality, exact integrable_zero _ _ _.
- IsCompact.elim_finite_subcover returns Finset centers and subset biUnion. Use mem_iUnion₂, Finset.mem_toList, List.mem_map.
- Physical ToAperture norm vs embedding norm: `change` at ccmPhysicalMass_localization / smallSupport coercivity works; do not confuse with form norm.
- Private circle-overlap proof uses two-square identity + sin²+cos²=1 and k²<=1, via sq_le_one_iff_abs_le_one.
- Theta ground cross density physical conversion uses thetaPrimeLinkDensity_eq_real, then ccmThetaGroundProfile_cross, with ring to reassociate.
- Noether velocity derivative: convert! (((hasDerivAt_id v).pow 2).div_const 2).sub_const E using 1; simp. Avoid unused simp argument ccmSourcePhaseLagrangian and unnecessary <;>.

## Next research direction
Develop a lower bound on the compensated sum (local energies + signed continuous correction) retaining its cancellation BEFORE comparison with the uniformly bounded prime contribution. Noether charge conservation alone does not sign this compensated quantity. Long-range correlations survive exactly, so any putative localization argument must address them. The newly proved unbounded continuous error on a positive Noether source invalidates proposals that try to infer RH/falsification from the sign or magnitude of an isolated localization correction. Do not repeat those failed simplifications or merely state another conditional RH endpoint.
