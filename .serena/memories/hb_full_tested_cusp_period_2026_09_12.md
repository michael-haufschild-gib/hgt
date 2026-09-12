HB source-extinction goal remains ACTIVE and OPEN; RH and fixed-clock extinction have NOT been proved. User forbids heartbeat/depth/transparency hacks, #print axioms theatre, numerical computations, full/umbrella builds. One foreground Lean per agent. Use corpus research deep/method retrieval and verify actual source. No commits/push. Shared tree: do not touch other agents' modules/frontier map.

Completed new leaf:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticFullTestedCuspPeriod.lean
namespace RHTower.D4BMQuarticFullTestedCuspPeriod.
SHA256 e4e2f2efc0c15ec211def51df61969ee227614025ce295ceda872a541d147bde.
5 public theorems, 5 public definitions, around 248 lines.
Scratch /tmp/hb-full-tested-cusp-period.lean passed with lake env lean. Final exact isolated leaf lake build passed (66 seconds) via formal/.lake/hb-extinction-scratch/audit-leaf.py using only cached imports; copied matching oleans/hashes back. No new heartbeat/depth/transparency override. Umbrella imported leaf once at line17471. Index refreshed once (4 changed files), all10 API rows verified. scripts/formal_tools.py lint --check-generated PASSED exit0 (prior unrelated unreachable modules now resolved externally). Audit dir hb-quartic-leaf-audit-t1q3b6s4 removed. All owned processes terminal: scratch8661, search57249, audit58314, index81242, lint36492. No processes to resume.

Proof chain theta -> Xi -> retained spin two -> physical causal radial/left-QNM action -> fixed common Hawking-clock extinction -> RH. Previous result (see mem:hb_response_cusp_finite_part_2026_09_12) gave sourceDeterminedPeriod for each of3 physical weighted means on each branch. New result attaches complete original physical scalar-test remainder, rather than replacing test by principal.

Definitions:
testedTailCuspDensity q b y = mean_x(testedResponseTail q b (physicalAngularParameter q) ![x,y]) / y^2.
nativeTestedTailPeriod q b a = actual native quotient integral of that complete testedResponseTail restricted to Im z>a, a:Ioi3.
fullTestedCuspDensity q b y = mean_x(scalar physicalParam * fullSquarePotential q * fullAngularField q b)/y^2.
fullTestedCuspCounterterm = Lambda(rho-1)*sum_i principalAmplitude_i*responseCounterterm_bi.
fullTestedCuspFinitePart = nativeTestedTailPeriod + Lambda(rho-1)*sum_i principalAmplitude_i*sourceDeterminedPeriod_bi(a).

Public:
testedTailCuspDensity_integrable line88: L1 on Ioi3, discharged from actual native L1 theorem with exact chart/Fubini.
nativeTestedTailPeriod_eq line100: equals integral_a∞ testedTailCuspDensity.
fullTestedCuspDensity_eq line134: full density=tail density + Lambda*sum Ai y^(vi-2)*fullMean.
fullTestedCusp_restoration line216: finite cutoff full integral-counter =
 integral tail + Lambda sum Ai [J_i(c)-J_i(particular)(c)-J_i(native)(c)-J_i(a)+sourceCounter_i(a)-integral_a^c sourceTailDensity_i]/physicalGap_i.
fullTestedCusp_period_tendsto line228: full restored pairing -> fullTestedCuspFinitePart.

Private cusp_mean_integrable gives general native-L1→height-mean-L1 using rectangle[-1/2,1/2]×IoiL (L≥1) subset original cellChart, integrable_withDensity_iff_integrable_smul, Complex measure-preserving real product chart, and hf.integral_prod_right. Do not duplicate if future source-Q² specialization can be added efficiently to same leaf, but any edit requires new audit. General helper has admission premise; public results specialize original data with all admission discharged. Native indicator identity uses integral_cusp_field_from.

Proof-engineering:
- Avoid IntervalIntegrable.sum here: ENormedAddMonoid instance diamond produced mismatch. Use pair ⟨integrable_finsetSum _ (fun i _=>(hi i).1), integrable_finsetSum _ (fun i _=>(hi i).2)⟩ directly.
- In subset mono_set final proof, intro y hy; change 3<y; exact lt_trans a.2 hy prevents metavariable mismatch.
- Indicator normalization: explicit change under mean then congrArg(fun f:ℝ→ℂ=>mean f/(y:ℂ)^2) (funext(fun x:ℝ=>if_pos(show (a:ℝ)<y from hy))). simp under mean made no progress.
- Full-mean continuity supplied by (average_hasDerivAt (fullAngular q b ∘ ofComplex) (fullAngular_smooth q b).planar_contDiffOn hp).continuousAt.
- Weighted mean moments interval integrable by cpow derivative and full-mean continuity.
- No zero assigned to native remainder, native homogeneous coefficient, or lower jet.

Paper card docs/drafts/pipeline/3-formalized/hb-full-scalar-tested-response-cusp-period.md. Active card docs/drafts/pipeline/1-in-progress/hb-source-contact-spin-two-balance.md appended exact proof, search applicability and final audit.

Research this turn:
full-tested-cusp-period-search.json and full-tested-angular-current-search.json under formal/.lake/hb-extinction-scratch, both deep cached300s and partial. Inspected declarations, source arguments, methods, proof ideas, ingredient sets. First found exact cusp field integral; used source+Lean. Second found common source formal-transpose divergence (ThetaCuspHawkingBMCommonSourceGreen.lean:354, PRIVATE common_green), full circle Green current_finite_integral (:505), and Eisenstein Stokes helpers restricted to absolute-convergence parameter subtype. Not a ready theorem on current physical test. A generated method on cusp-top DEFINITION misleadingly suggested evaluating integral; treated only as definition.

New broad primary literature checked:
https://arxiv.org/html/2608.22171v1 (Aug23 b^k symplectic), sections3.1 and3.6-3.7: finite-part residue machinery keeps defining-function jets; reduction needs Hamiltonian/odd-leading data, not verified for theta complex-power causal action. No imported vanishing.
https://arxiv.org/html/2609.09282v1 (Sep8 unequal scalar scattering): pseudo-physical discontinuity not controlled by physical unitarity; numerical results/extra Omnes ansatz not unconditional HB law. No numerical work used.

Next HARD task: full physical scalar-tested angular current balance, local Q² finite part, all independent channels/boundaries. Exact planar product rule psi divJ = div(psi J) - gradpsi·J. Horizontal periodicity alone doesn't delete test-derivative work or upper/lower tested currents. New response finite parts provide actual work terms for comparison; no cancellation yet. Existing reducedSourceWork = coeffTrue*alphaTrue Q ATrue + coeffFalse*alphaFalse Q AFalse + squareWorkCoefficient Q². Incoming radial clock identity retains -p/3 div angularResponseGreen + div reducedSourceCurrent - reducedSourceWork/y².

Read original angularResponseGreen in ThetaCuspHawkingBMIncomingClockTranslation.lean:197:
beta ∂H*(K+Q) - alpha ∂K*(H+Q).
Private gradientCurrent in QuarticResponseWork:37:
Q*(a∂H+b∂K+c∂Q).
Do NOT drop Q terms.
Possible finite-part Green integration route must derive derivative-test work, admission and cusp counterterms for complete currents, then compare all periods. Generic causal response, finite-part existence, and covariance assumptions cannot produce extinction by themselves; no premise wrapper claiming RH.