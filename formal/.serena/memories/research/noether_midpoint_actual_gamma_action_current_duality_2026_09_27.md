# Midpoint reflection: actual Gamma action/current duality and source-energy cancellation

Active goal remains RH proved formally via arithmetic conservation/Noether. RH NOT proved; keep active. Previous turn (deleted tower energy/Mellin) classified progress; this turn also progress: four new fully audited leaves, 35 public theorems. Repo /Users/michael/Documents/code/hgt/formal. No subagents, commits, pushes, full/umbrella builds, numerical experiments, sorry/new axioms, heartbeat increases. One own foreground Lean process at a time. All own processes terminal, audit scratch removed.

## Current-state discoveries and route choice
Read current direct Lean in CCMCoherentReflectedCancellation and CCMCoherentPhaseCostReduction (concurrent work; did NOT modify either). ReflectedCancellation was fresh compiled, later both wired by other work. Existing identity: for arbitrary complex SoninL2 source f, delta=U_r f-f, the real pairing with U_-s f+U_(r+s)f vanishes. Applies to full prime sum plus signed terminal field. PhaseCostReduction projects out its supported reflected direction; no source positivity assumed. This gave a direct signed-current bridge, complementary to prior deleted-force coefficient work. No cards read. Corpus searches for reflected coherent norm / translation packet reflection / midpoint gauge coherent found no duplicate of new results.

## Four new leaves / exact results
### 1. CCMCoherentMidpointEnergy.lean (7 public,122 lines)
Imports CCMCoherentReflectedCancellation.
- norm_sq_real_translation_packet_reflection: for every finite I, real c_i,s_i, real r, complex f, norm(sum c_i U_(r+s_i) f)^2 = norm(sum c_i U_-s_i f)^2. No parity/reality assumption on f. Proof expands inner products, uses translation adjoints and real-inner symmetry.
- norm_sq_ccmActualHeadReflectedCoherentField: full reflected field R has same squared norm as completed field V, including oriented terminal. Uses Option indexing to include terminal atom in same packet.
- Odd O=(V-R)/2; Even E=(V+R)/2, definitions ccmActualHeadMidpointOddField / EvenField.
- ccmActualHeadCoherentField_eq_midpoint_parts: V=O+E.
- re_inner_increment_midpointEven_zero: Re<delta,E>=0.
- re_inner_increment_midpointOdd: Re<delta,O>=Re<delta,V>.
- norm_sq_ccmActualHeadCoherentField_midpoint_split: norm V^2=norm O^2+norm E^2.
- norm_sq_ccmActualHeadMidpointOddField_le.

### 2. CCMCoherentMidpointGauge.lean (9 public,127 lines)
Imports MidpointEnergy and existing CCMActualHeadCoherentQuantileGammaPhaseSquare.
- re_inner_ccmActualHeadMidpoint_odd_even_zero: Re<O,E>=0.
- gauge field V_theta=O+theta E (complex cast of real theta); theta1=actual V, theta0=O.
- re_inner_increment_midpointGauge: full real current conserved for every theta.
- norm_sq_ccmActualHeadMidpointGaugeField: norm V_theta^2=norm O^2+theta^2 norm E^2.
- ccmActualHeadMidpointOddField_minimizes_gauge_norm.
Let g=ccmGammaHigherBinetModeDensity |r|, k=ccmGammaHigherBinetDualDensity |r|. Both zero at r0, reciprocal off0.
- GaugeAction A(theta)=norm(sqrt(g) delta+sqrt(k) V_theta)^2-k norm V_theta^2.
- ccmActualHeadMidpointGaugeAction_invariant theta eta.
- hasDerivAt_ccmActualHeadMidpointGaugeAction: derivative0 every theta.
- ccmActualHeadMidpointGaugeAction_eq_actual_terms: A(theta)=g*TranslationDefect(|r|,f)+2 Re<delta,V>. All r, including singular zero clock.
These are field-parameter variational identities, NOT a proved conservative time-evolution or coercive energy estimate.

### 3. CCMCoherentMidpointGammaReduction.lean (12 public,196 lines)
Defines OddGammaCost C_odd=integral norm O^2*k; EvenGammaCost C_even similarly; OddGammaSquare Phi_odd=integral norm(sqrt(g)delta+sqrt(k)O)^2.
Proves integrability of both costs for all T,N,f; both nonnegative.
- ccmActualHeadCoherentGammaCost_midpoint_split: old complete cost C=C_odd+C_even.
- OddGammaCost_le_full.
- integrable_ccmActualHeadMidpointGaugeAction for canonical f=ccmArchimedeanFormToAperture a u, any finite N and theta.
At actual N=floor(exp(2a))+1 and T=2a:
- integral_ccmActualHeadMidpointGaugeAction =2G+2J, G=actual higher Binet mode energy, J=literal completed quantile current.
- ccmRestrictedWeilSourceQuadratic_eq_midpointGaugeAction: Q=(2 gammaHardyPhaseRate0+4) norm f^2-G+integral A(theta), every theta.
- ccmActualHeadMidpointOddGammaSquare_eq_actual_terms: Phi_odd=2G+2J+C_odd.
- ccmActualHeadCoherentGammaPhaseSquare_midpoint_split, line165: old Phi=Phi_odd+C_even.
- ccmRestrictedWeilSourceQuadratic_eq_midpointOdd_normalForm, line180:
  Q=(2 gammaHardyPhaseRate0+4) norm f^2+Phi_odd-G-C_odd.
Thus entire even energy cancels EXACTLY from phase square and subtracted cost; terminal and cross-prime terms retained.
Domain regularity comes from actual CCMArchimedeanFormDomain; no unknown cancellation, positivity, or RH assumed.

### 4. CCMGammaCurrentActionDuality.lean (7 public,109 lines)
General action on arbitrary field v:
ccmGammaIncrementAction f r v=norm(sqrt(g)delta+sqrt(k)v)^2-k norm v^2.
- ccmGammaIncrementAction_eq: A(v)=g*TranslationDefect(|r|,f)+2 Re<delta,v>, all r.
- ccmGammaIncrementAction_eq_iff_current_eq, line53: A(v)=A(w) iff Re<delta,v>=Re<delta,w>.
- ccmGammaIncrementAction_add_real_smul: A(v+theta z)=A(v)+2 theta Re<delta,z>.
- hasDerivAt_ccmGammaIncrementAction_add_real_smul: derivative=2 Re<delta,z>.
- ccmGammaIncrementAction_translation_invariant_iff, line83: (forall theta,A(v+theta z)=A(v)) iff Re<delta,z>=0.
- ccmGammaIncrementAction_midpointGauge identifies preceding literal gauge action by rfl.
- ccmGammaIncrementAction_midpointEven_invariant: actual arithmetic E supplies explicit continuous translation symmetry, based at arbitrary v.
This gives both directions of action/current correspondence for THIS concrete field action. Do not describe it as a general converse Noether theorem or assert unproved Euler-Lagrange dynamics.

## Remaining mathematical target
Q positivity still requires G+C_odd <= Phi_odd+(2 gammaHardyPhaseRate0+4) norm f^2 for every actual form-domain source. Nonnegativity of Phi_odd alone does NOT imply this. No pointwise signed Chebyshev square-root bound, no RH proof/counterexample obtained. Existing deleted-prime critical coefficient energy and Mellin estimates remain valid from preceding memory; no direct theorem yet connects them to this new phase gap.
Potential next work: derive exact spectral/sine representation of O, including actual terminal coefficient, and exploit its centered phase zero at frequency0 rather than discarding interference. For real coefficient packet A(xi), the candidate odd symbol is (A(xi)-exp(i*r*xi)*conj(A(xi)))/2; signs must be checked against U convention. This is unformalized. Explore connection to the N+T carrier-length cost of earlier Mellin transfer. Another possible infrastructure: full real-current quotient/minimum norm projection onto delta; search corpus first, do not merely restate gap as a hypothesis. Gauge symmetry removes an invisible channel but does not automatically bound the remaining signed current.

## Audits / repository state
Each leaf final audited with lake --old env lean FILE -o .lake/build/lib/lean/... .olean, exit0 no warnings. Four fresh objects verified; four imports exactly once in GaloisForLFunctions/RHTower.lean. Combined35 #print axioms audit exit0 with only [propext, Classical.choice, Quot.sound]. Scratch /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/CCMMidpointAxiomAudit-o8qnuecb.lean removed. No own scratch/process remains. Sources have no forbidden constructs/trailing whitespace; umbrella git diff --check passed. New leaves untracked at final status; no commits/pushes by us.
Index succeeded (LEAN_API/GAPS/OVERVIEW and search DB). Global lint --check-generated exit1:16 unrelated unwired modules and stale LEAN_API/LEAN_OVERVIEW under concurrent edits. No own leaf errors. Unwired RHTower: MobiusTwoJetBlockTaylor, MobiusTwoJetCofactorPacket, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, STCPrimeLogSquarePoleScaling, XiGaussianQuadraticSplitting, XiGaussianTransverseMomentBudget, ZetaZeroDensityPowerSaving. HTGeometry: ExponentialFeatureTangentSpace, FixedAdjoinIndependentDescent, FunctionFieldJetBasis, FunctionFieldJetExtension, FunctionFieldJetField, MaurerCartanFixedFields, MaurerCartanJetCoordinates. Do not wire unrelated unfinished work or repeatedly regenerate during concurrency.

## Lean repairs learned
- After norm_add_sq or norm_sq_eq_re_inner (complex), explicitly rewrite RCLike.re_eq_complex_re before Complex.mul_re / linarith. RCLike.re and Complex.re otherwise remain separate atoms or fail syntactic rewrite.
- inner_re_symm needs explicit (𝕜:=ℂ) and vectors sometimes.
- Option.elim takes option first: fun o : Option Nat => o.elim terminal (fun n => log n). Finset.sum_insertNone handles full packet.
- To prove AEStronglyMeasurable half-sum/difference, unfold field then provide hc:AEStronglyMeasurable(fun _ : Real => ((1/2:Real):Complex)); hc.smul handles function subtraction/addition. Leaving scalar metavariable untyped fails.
- CompletedQuantileCurrent_eq_integral_coherentField has expanded cell+terminal expression, not the later named def; final rfl closes after rewriting integral.
- ccmActualHeadTranslationDefect_abs only replaces abs r by r; unfold ccmActualHeadTranslationDefect before polynomial tactics.
- (hasDerivAt_id theta).const_mul caused real Module/AddCommGroup instance diamond. Specialized hasDerivAt_const_mul (x:=theta) c, then .const_add, compiled directly.
