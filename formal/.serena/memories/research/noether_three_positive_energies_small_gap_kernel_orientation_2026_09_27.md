# Three positive ground energies, a proved small-aperture gap, and kernel orientation

## Status
Active goal still requires RH proof; no proof/falsification obtained. Previous goal turn is progress: 4 new Lean modules final-audited green, all wired; 11 endpoint axiom checks green with only propext, Classical.choice, Quot.sound. No new axioms/sorry/native computations/heartbeat changes. No commit/push. One foreground Lean process at a time. Repo /Users/michael/Documents/code/hgt/formal. Other chats edit/build/commit concurrently; preserve their changes. No subagents.

See `mem:research/noether_cut_conservation_exact_weil_ground_criterion_2026_09_27` for exact full Weil identification, cut-current positivity, and RH energy criterion. Older Noether memories cover reciprocal action symmetries, conserved currents, Newton flow, and generic positivity counterexamples.

## New leaves, all green
1. ThetaPositiveScalingEnergies.lean
2. ThetaPositiveScalingRigidity.lean
3. CCMThetaThreeEnergyComparison.lean
4. ThetaGammaPolarKernelOrientation.lean
All compiled using lake --old env lean ... -o .lake/build/lib/lean/...olean, no full builds, wired in RHTower.lean. Audit scratch work/noether_positive_energy_axioms.lean removed. Index refresh succeeded (2 changed sources; concurrent refreshes had already indexed others). Global lint --check-generated completed with only 4 unrelated concurrent unwired RHTower modules: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving. No generated staleness reported. All our new leaves wired; no own running process or scratch remains.

## Separate energies
Namespace RHTower.ThetaSourceWard. k=actual theta source, general S:ThetaSource for energy infrastructure. All profiles chi:SchwartzMap R C.
- thetaPolarScalingDensity S chi (u,x)=2*cosh(u/2)*S.k(x)*S.k(x+u)*norm(chi(x+u)-chi(x))^2.
- thetaGammaScalingDensity S chi (u,x)=exp(-u/2)/(1-exp(-2u))*S.k(x)*S.k(x+u)*normDelta^2.
- thetaPolarScalingEnergy / thetaGammaScalingEnergy integrate these over thetaContinuousLinkMeasure=(volume.restrict(Ioi0)).prod volume.
- thetaContinuousLinkMeasure_ae_pos available for product AE support.
- Both densities absolutely integrable. Pole proof uses bounded chi, source-pair exponential decay, and 2cosh(u/2)*exp(-2u)<=2exp(-u) for u>=0. Gamma proof subtracts the already integrable signed Gamma/pole density from integrable pole density; no divergent integral splitting.
- Exact signed decomposition thetaGammaPolarScalingEnergy_eq_polar_sub_gamma.
- Both positive energies nonnegative.

## Strictness / zero modes
ThetaPositiveScalingRigidity:
- thetaPolarScalingEnergy_eq_zero_iff: E_pole(S,chi)=0 iff chi=0.
- thetaGammaScalingEnergy_eq_zero_iff: E_Gamma(S,chi)=0 iff chi=0.
- Corresponding pos_iff chi!=0.
- thetaPrimeScalingEnergy_schwartz_eq_zero_iff: complete prime energy on Schwartz chi=0 iff chi=0.
Proof: zero integral of nonnegative density => AE zero; theta link measure is restriction of product Lebesgue to open Ioi0 x univ; continuity there upgrades to pointwise. Positive coefficient then forces ALL forward increments zero. Schwartz decay at cocompact infinity excludes nonzero constants. Prime uses existing two-period rigidity plus same Schwartz-constant lemma.
Useful Mathlib API: MeasureTheory.Measure.eqOn_open_of_ae_eq (qualified namespace); Measure.prod_restrict; chi.tendsto_cocompact and NeBot(cocompact R). A pointwise constant identity must be turned into function equality before rewriting Tendsto.

## Three-energy RH criterion and actual verified comparison range
Namespace RHTower. CCMThetaThreeEnergyComparison:
- ccmRestrictedWeilSourceQuadratic_eq_three_theta_energies:
  Q_CCM(u)=Eprime(u/k)+EGamma(u/k)-Epole(u/k).
- riemannHypothesis_iff_thetaThreeEnergyComparison:
  RH iff forall positive apertures a and complex smooth compact interior source u,
  Epole(u/k)<=Eprime(u/k)+EGamma(u/k).
- thetaGroundNormSq_ccmProfile_eq_physical: ground weighted norm equals physical CCM L2 norm squared.
- exists_small_aperture_thetaThreeEnergy_gap:
  exists delta>0,c>0, forall a with a<delta, forall smooth complex u,
  Epole(u/k)+c*thetaGroundNormSq(u/k)<=Eprime(u/k)+EGamma(u/k).
This is an ACTUAL unconditional inequality on an entire nonempty aperture range, not a conditional reduction. It transfers existing SuzukiSmallApertureGroundEnergy coercivity. Choose a0=delta_old/2 with positive ground energy; antitonicity bounds every smaller aperture below by that same positive c. Use ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source and exact source identity.
Remaining gap: extend to all apertures with critical comparison constant1. Strict positivity of the three individual energies does not imply their comparison.

## Conjecture tested / known obstruction identified and transported
Tempting idea: the ground form might be controlled by pointwise nonpositive off-diagonal coupling / a positivity-preserving semigroup. Corpus search found the relevant obstruction already formalized, so did NOT recreate bump construction:
GaloisForLFunctions/RHTower/SuzukiScrewDisjointCrossCoupling.lean, namespace GaloisForLFunctions.RHTower (different from plain RHTower).
- screwRegularForm f h = integral_(x,y) screwRegularKernel(x-y)*f(y)*h(x).
- exists_disjoint_positive_screwRegularForm for apertures>a_threshold/2 constructs nonnegative C-infinity compact f,h with disjoint supports, ordered separated supports beyond threshold, every support difference avoiding all log n (n>=2), and strict positive regular cross integral.
- not_satisfiesBeurlingDeny_screwRegularForm_add_smul proves no scalar shift repairs the regular-form first Beurling-Deny sign condition. This is a REGULAR cross-form statement; do not overclaim a new full-quadratic modulus theorem without the full mixed-form bridge.

ThetaGammaPolarKernelOrientation ties it to new ground energies:
- thetaGammaPolarScalingKernel_eq_screw for u>0: mu(u)=screwRegularKernel(u), directly via screwRegularKernel_eq_tailForm and cosh exponentials.
- thetaGammaPolarScalingKernel_pos_iff_threshold for u>0: mu(u)>0 iff u>screwSignThreshold.
- thetaGammaPolarScalingKernel_neg_below_threshold for 0<u<threshold.
Threshold=log plasticRoot, root of rho^3-rho-1=0 (existing corpus).
- thetaGammaPolarGroundCrossPairing phi psi for REAL Schwartz profiles := integral_(x,y) mu(x-y)*k(x)*k(y)*phi(y)*psi(x).
- exists_disjoint_positive_thetaGammaPolarGroundCrossPairing:
  exists nonnegative real Schwartz phi,psi with disjoint supports, all ordered support differences >threshold and avoiding every log n>=2, absolutely integrable displayed cross density, and strict positive pairing.
Proof takes existing compact f,h, phi=f/k,psi=h/k (smooth and compact since k smooth positive); kernel equality on ordered support and cancellation of k denominators recover existing positive screwRegularForm. Integrability follows because the Bochner integral is proved positive and integral_undef would force zero otherwise.
The existential statement does NOT currently retain compact-support proofs or explicit common aperture, though the construction has both. If needed for next full mixed-form comparison, strengthen the witness statement or reuse original disjoint bump theorem instead of assuming every Schwartz profile compact.

## Next meaningful work
Quantify mixed cross terms versus diagonal energies. Positive off-diagonal terms are compatible with PSD; this does NOT falsify RH.
Possible infrastructure to build:
1. Exact mixed/polarized ground-energy identity on pairs of CCM core sources, using existing sesquilinear CCM form and explicit correlation source distribution.
2. Connect the above regular cross witness to actual complete Q(phi+psi)-Q(phi-psi)=4B, including zero prime pairing (support differences avoid atoms) and zero diagonal pairing (disjoint supports). This would formalize modulus-order failure for the COMPLETE ground quadratic. It is not yet done.
3. Test 2x2 Gram determinant bounds B^2<=Q(phi)Q(psi), a quantitative condition which survives positive cross coupling. Need avoid mistaking positive cross sign for negative determinant.
4. Existing small-aperture gap now gives proved diagonal control for compact bump sources; their translations retain physical self energy, while prime gaps force narrowing of atom-free separated bumps. For large gap t, regular kernel grows ~exp(t/2), but allowed widths shrink with log-prime spacing, so naive 'large separation makes cross exceed diagonals' is unsupported. This is an analytical observation, not a formal theorem in this batch.
5. Keep active RH goal; do not mark complete for these intermediate results.

## File/API notes
- HasCompactSupport.mul_right has no g argument; create explicitly typed lambda product then use hc.mul_right.
- simp with source positivity sometimes fails to rewrite nonzero k because of reducibility; explicit And.left / pair using typed ground_ne_zero closes support equality.
- For function subtraction use Integrable.sub then .congr and Pi.sub_apply; Integrable.fun_sub does not exist.
- ContinuousOn.pow must be parenthesized as argument to .mul; otherwise Lean parses the exponent as argument to the whole expression.
- Open scoped BoundedContinuousFunction for arrow superscript-b notation.
- Use actual verified file paths via rg --files; several intuitive leaf names do not exist.
