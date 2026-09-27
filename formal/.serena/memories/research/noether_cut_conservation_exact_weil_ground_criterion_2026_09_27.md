# Noether cut conservation and exact Weil ground-energy criterion

## Goal and status
Active research goal remains open; completion only when RH is proved. No RH proof or falsification obtained. Continue conjecture/proof/failure loop. Main advance: the previously provisional theta relative form is now identified exactly with the existing CCM restricted Weil quadratic on every complex smooth compact source, and its energy comparison is proved equivalent to RH. No claim of literature novelty.

Repo /Users/michael/Documents/code/hgt/formal. Other chats concurrently edit/build/commit; preserve their work. No commit/push by this chat. No subagents. See `mem:research/noether_prime_gamma_ground_difference_newton_flow_2026_09_27` and older Noether memories for source equations, Newton flow, prior counterexamples, and kernel estimates.

## Nine new leaves, all final-audited green
Every leaf checked individually with `lake --old env lean GaloisForLFunctions/RHTower/<leaf>.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean`. No full/umbrella builds. All nine wired in RHTower.lean; GaloisForLFunctions/MainTheorems.lean imports it (line28).
1. ThetaGammaPolarCrossingCurrent
2. ThetaGammaPolarCrossingExchange
3. ThetaPrimeGammaCutEnergy
4. ThetaGammaPolarDiagonalIntegral
5. ThetaFullArithmeticGroundForm
6. CCMThetaArithmeticCorrelation
7. CCMThetaPrimeArithmetic
8. CCMThetaContinuousArithmetic
9. CCMThetaGroundRHCriterion
Also exposed/reused two formerly private helpers in ThetaGammaPolarScalingEnergy (final audited green): thetaSource_shiftPair_decay and thetaGammaPolar_damped_square_bound. No new axioms, sorry, numerical computation, or heartbeat changes.

13 endpoint #print axioms checks all return only propext, Classical.choice, Quot.sound, including both RH equivalences and source-form equality. Audit scratch work/noether_cut_weil_axioms.lean removed. No own build still running after that audit. Index refresh succeeded (8 changed sources). Global lint --check-generated completed with errors only for 7 unrelated concurrent unwired modules: RHTower.MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving; HTGeometry.GaussianGridHasseEnvelope, GaussianGridSamplingAlgebra, GaussianStripSamplingError. No generated-file staleness reported in this lint. All our modules wired and scratch removed. No own running process remains. git diff --check for umbrella passed.

## Actual source / continuous current
Namespace RHTower.ThetaSourceWard unless noted. k=thetaCuspFullSource; S=thetaCuspTiltSource; mu(h)=thetaGammaPolarScalingKernel h = 2*cosh(h/2)-exp(-h/2)/(1-exp(-2h)).

C_S(x) := integral over h>0 of mu(h)* integral y=x..x+h S.k(y)*S.k(y-h).
- thetaGammaPolarCrossingTerm, thetaGammaPolarCrossingCurrent definitions.
- Measurable term; absolute convergence for every ThetaSource and x.
- Uniform h-majorant C^2*(2*abs h+1/2)*exp(-abs h/2).
- Each fixed-shift crossing term and complete C_S tend0 atTop.
- Fixed-shift derivative =mu(h)*S.k(x)*(S.k(x+h)-S.k(x-h)).

ThetaGammaPolarCrossingExchange defines literal thetaGammaPolarSourceTerm x h = gammaSourceTerm x h + both polarSourceTerm(+/-1/2)x h.
- integrable source, integral=A(x)=thetaArchimedeanShiftSource x.
- norm bound G(h)+C0*exp(abs x)*(exp(-h/2)+exp(-3h/2)).
- thetaGammaPolarCrossingDerivative x h = Re[k(x)*(T(x,h)-T(-x,h))].
- Pointwise equals mu(h)*k(x)*(k(x+h)-k(x-h)); singular diagonal cancels BEFORE integration.
- Locally uniform derivative majorant allows dominated differentiation.
- hasDerivAt_thetaGammaPolarCrossingCurrent x: C_actual'(x)=Re[k(x)*(A(x)-A(-x))].

## New unconditional positive cut law
J is existing fullPrimeShiftNoetherCurrent S S. Define Q(x)=Re J(x)-C_actual(x) as thetaPrimeGammaCutEnergy.
- Q'(x)=-2*x*k(x)^2.
- Q tends0 atTop; moment 2*x*k(x)^2 absolutely integrable.
- Q(x)+integral_0^x 2*t*k(t)^2 =Q(0).
- Q(x)=integral_{t>x}2*t*k(t)^2 exactly.
- Q(-x)=Q(x), Q(x)>0 for EVERY real x.
- thetaGammaPolarCrossingCurrent_lt_prime.
This is positivity of the literal crossing-current difference at every threshold. Mixed-cut positivity is NOT established. A direct identification of discontinuous threshold profiles with the Schwartz-profile energy remains additional infrastructure; do not claim that part is already formalized.

## Full arithmetic identity (now fully integrated)
ThetaGammaPolarDiagonalIntegral:
- thetaGammaPolarSourceDiagonal chi reflected (h,x) = k(x)*Re T((if reflected then -x else x),h)*norm(chi x)^2.
- Both jointly integrable on thetaContinuousLinkMeasure=(volume.restrict(Ioi0)).prod volume.
- Proof uses k decay2, source majorant and bounded chi, hence a product exponential majorant.
- Fubini gives forward/reflected source marginals.
- Measure-preserving skew translation (h,x)->(h,x+h) handles target endpoint.
- Literal continuous diagonal integral equals integral k ReA normchi^2 plus reflected marginal.

ThetaFullArithmeticGroundForm:
- thetaGroundNormDensity chi x=k(x)^2*normchi(x)^2=norm(k(x)*chi(x))^2; integrable.
- Literal thetaGammaPolarQuadraticDensity integrable (diagonal + compensated difference).
- Its diagonal integral =thetaPrimeGammaScalingDiagonal chi+2*archConstant.re*thetaGroundNormSq chi.
- thetaFullArithmeticQuadratic chi := integral literal continuous quadratic -2*archConstant.re*thetaGroundNormSq chi -2*thetaPrimeScalingCross S S chi.
- thetaFullArithmeticQuadratic_eq_relative.
- thetaFullArithmeticQuadratic_eq_energy_difference: Qfull=Eprime-Econtinuous for every complex Schwartz chi. This keeps the singular Gamma integrand compensated.

## Exact CCM comparison (all normalizations proved)
These leaves in namespace RHTower, open ThetaSourceWard.
For a:SuzukiPositiveAperture and u:CCMComplexSmoothInteriorSource a, chi=ccmThetaGroundProfile u=u/k (earlier module), and H=ccmComplexSmoothCrossCorrelation u u.

CCMThetaArithmeticCorrelation:
- integrable source norm squared and complex shifted cross product.
- H(h)=integral u(x+h)*conj(u(x)).
- ReH(0)=integral normu^2; ReH(-h)=ReH(h), no real/even source assumption.
- Ground continuous quadratic pointwise reconstructs physical quadratic.
- Integral in x =2*a(h)*ReH(0)+2*mu(h)*ReH(h), a=exp(-2h)/(1-exp(-2h)).
- For h>0 equals -Re(ccmArchimedeanGaussCancellationKernel H h)+2*cosh(h/2)*Re(H(h)+H(-h)).

CCMThetaPrimeArithmetic:
- Re primeCoefficient n=criticalMellinAtomWeight n for every n including0,1.
- Literal prime cross density reconstructs weight*Re(u shifted*conju).
- Full count-times-volume integral becomes exact finite sum n in Icc2 floor(exp(2a)); discarded terms vanish by sharp source support, not estimates.
- thetaPrimeScalingCross_ccmProfile_twoSided matches both conjugate CCM prime channels with factor2.

CCMThetaContinuousArithmetic:
- ccmThetaPolarCorrelation u h=(Hh+H(-h))*2cosh(h/2), compact support in[-2a,2a], integrable.
- Integral over Ioi0 exactly Ioc0(2a).
- Integral continuous quadratic = -Re integral Gauss kernel +Re pole correlation integral.
- theta_archConstant_ccmGroundNorm proves exact Euler/logpi constant, not approximation.
- thetaGammaPolarQuadratic_ccmSource_eq: integralquad-constant =Re(pole integral-ccmArchimedeanWeilDistribution H).

CCMThetaGroundRHCriterion:
- ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic.
- ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference.
- riemannHypothesis_iff_thetaGroundEnergyComparison:
  RiemannHypothesis iff forall a and smooth complex core u,
  Econtinuous(u/k) <= Eprime(u/k).
- Converse extends positivity from dense smooth source range to full archimedean form domain via continuity, then existing parity-pole RH criterion.
- not_riemannHypothesis_iff_thetaGroundEnergyViolation:
  not RH iff exists a,u with Eprime(u/k)<Econtinuous(u/k).
This closes the previous missing full-form identification. The comparison is still unproved; no negative witness known.

## Next research directions, not completed facts
1. Develop mixed-cut kernel / second variation. Diagonal cut positivity alone is insufficient; generic Noether positivity counterexamples already exist in previous batch.
2. Split signed Econtinuous into Epolar-EGamma, separately nonnegative finite energies. This would express RH as Epolar <= Eprime+EGamma on complete smooth core. Integrability infrastructure can reuse source pair exponential decay, Schwartz increment bound, and current convergence bounds. Search corpus first to avoid duplicates.
3. Formalize threshold-step energy representation and mixed cut combinations; current Qcut is geometric crossing difference, not yet a theorem about extended nonsmooth-profile energy.
4. Attempt actual arithmetic comparison through mixed kernels / domination, learning from failures. Do not substitute equivalence for proof or claim the research goal achieved.

## Lean repair/API notes
- Use `push Not`, not deprecated `push_neg`.
- Real/complex continuous-linear-map casts often need convert! and Complex.reCLM_apply.
- Names Complex.re_ofNat/im_ofNat, not ofNat_re/ofNat_im; Complex.mul_im often needed after mul_re.
- Complex.mul_conj +Complex.ofReal_re+Complex.normSq_eq_norm_sq replaces nonexistent Complex.mul_conj_re.
- For function-level integral_add/sub/neg, give typed raw-lambda Integrable proofs; Pi functions and Function.comp may block rw.
- IntegrableOn realpart conversion sometimes needs explicit `change Integrable ... (volume.restrict(Ioi0))` before simp RCLike.re_to_complex.
- Explicit μ:=volume for integral_add_right_eq_self and chi.integrable when inference is stuck.
- rw integral_add_right_eq_self with explicit lambda when integrand is norm(f(x+h))^2.
- Rewrite Complex.re of a finite sum through `←Complex.reCLM_apply, map_sum`, then simplify.
- Bool source index: simplify Bool.false_eq_true and reduceIte before fun_prop.
- Do not guess paths. Main umbrella at GaloisForLFunctions/MainTheorems.lean. Use rg --files.
