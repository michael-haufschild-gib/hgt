# Conjugate-Diagonal Geometry (CDG)

Namespace `GaloisForLFunctions.ConjugateDiagonalGeometry`; umbrella `ConjugateDiagonalGeometry.lean`; 61 modules. All results
unconditional; every reading is evaluated on the actual zeta divisor with multiplicities, without simplicity, separation or
zero-free hypotheses.

## 1. Motivation

On the zero divisor there are two pairings: the conjugate diagonal $(\rho,\bar\rho)$, which gives the positive **collided form**
$D(f)=\sum m_\rho|\hat f(\rho)|^2$, and the reflection graph $(\rho,1-\rho)$, which gives the Weil form computed by the explicit
formula. Their coincidence is the critical-line statement (APol capacity identity $\Re W=D-\Delta$). CDG studies the collided side
as an object of its own: its translation defect measures off-line depth, and the programme shows that $D$, every depth moment,
local zero counts and horizontal collision charges are computed by positive integrals of literal arithmetic data — theta
amplitudes and their first moments — with explicit error certificates. The comparison with the reflection side stays open.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Depth kernel | `depthKernel` | $k(L,d)=2\cosh(2dL)-2=4\sinh^2(dL)$ |
| Compact tests | `CompactTest`, `sourceTranslate`, `sourceTwist` | $C^2$ compactly supported $f$; translation; ordinate modulation |
| Depth, weight | `zetaDepth`, `zetaWeight` | $\delta_\rho=\Re\rho-\frac12$; $m_\rho|\hat f(\rho)|^2$ |
| Hecke defect | `heckeDefect`, `depthTail`, `depthSecondMoment` | $E(f,L)=\sum w_\rho k(L,\delta_\rho)$ |
| Depth dispersion | `depthDispersion` | $D(E(2L)-4E(L))-E(L)^2$ |
| Source kernel | `sourceDepthKernel` | $|\hat f(z)|^2k(L,\Re z-\frac12)^j$ on the spectral plane |
| Cutoffs | `sourceCutoff`, `stripSourceCutoff`, `sourceLocalCutoff` | radial exhaustion; fixed-width strip exhaustion; local bump at $(c,r)$ |
| Regularized ξ potential | `xiLogPotential`, `xiCurvatureDensity` | $\frac12\log(|\xi|^2+\varepsilon)$; $\varepsilon|\xi'|^2/(|\xi|^2+\varepsilon)^2\ge0$ |
| Current and trace | `xiCurrentPairing`, `zetaSourceTrace` | $(2\pi)^{-1}\int\log|\xi|\,\Delta\varphi$; $\sum m_\rho\varphi(\rho)$ |
| Universal weight | `universalSourceWeight` | $W(z)=e^{(\Re z)^2}/(1+(\Im z)^2)^2$ |
| Regulator schedules | `commonSourceIndex`, `explicitSourceRegulator`, `polynomialSourceRegulator` | error-tested index; $e^{-e^{(n+1)^4}c_n}$; $e^{-M(n+1)^{20}}$ |
| Theta amplitudes | `thetaSourceAmplitude`, `thetaSourceFirstMoment`, `thetaSourceCurvature` | $\int\theta e^{(1/2-z)x}=\xi(z)$; first moment $=-\xi'$ |
| Finite theta source | `finiteThetaSourcePotential`, `finiteThetaSourceCurvature`, `explicitThetaIntegerCutoff`, `polynomialThetaIntegerCutoff` | $N$ integer theta summands |
| Readings | `commonSourceReading`, `explicitSourceReading`, `finiteThetaSourceReading`, `polynomialThetaSourceReading`, `polynomialThetaLocalReading` | positive integrals cutoff·test·curvature |
| Reference tail | `sourceReferenceTail` | $\sum(1-\chi_n)m_\rho/(1+|\gamma(\rho)|^2)$ |
| Canonical log mass | `xiCanonicalLogMass` | planar log potential of the canonical divisor |
| Collision kernel | `horizontalCollisionGaussian`, `collisionWindowPairTest`, `finiteThetaCollisionReading` | $e^{-q\Delta y^2}(1-e^{-q\Delta x^2})$ |
| Forcing cost | `companionCost` | majorant of the companion-forcing theorem |

## 3. Language

- **Collided / reflection pairing**: $(\rho,\bar\rho)$ vs $(\rho,1-\rho)$; conjugation, $s\mapsto1-s$ and $s\mapsto1-\bar s$ are kept distinct.
- **Source reading**: positive integral of a test against an arithmetic curvature density; defined without zero coordinates.
- **Window**: ordinate $|\tau|\le n/2$ and Hecke/physical aperture $a+j|L|\le c\log(n+1)$.
- **Current error / tail error**: Green-identity error inside the cutoff vs omitted divisor mass outside it.
- **Stage**: cutoff index $n$ chosen before test, order and motion.
- **Computed vs posited**: a formula must evaluate the object without its desired sign.

## 4. Mechanisms

**A. Defect calculus**
1. Centred translation multiplies $\hat f(\rho)$ by $e^{L(\rho-1/2)}$ ⇒ $D(T_Lf)+D(T_{-L}f)-2D(f)=\sum w_\rho k(L,\delta_\rho)$.
2. $k\ge4L^2d^2$, $k(2L)=4k+k^2$, Chebyshev tail $k(L,b)\cdot\text{tail}\le E$; pairwise variance identity for two scales.

**B. Source currents**
3. Poincaré–Lelong for entire ξ: $\int\log|\xi|\Delta\varphi=2\pi\sum m_\rho\varphi(\rho)$; Green identity needs compact support only on the test.
4. Regularization $\frac12\log(|\xi|^2+\varepsilon)$ has Laplacian $2\varepsilon|\xi'|^2/(|\xi|^2+\varepsilon)^2$; local $L^1$ convergence from log-integrability.
5. Theta identities: bilateral Laplace transform of the theta source is ξ, its first moment is $-\xi'$.
6. Positivity of the density: readings are monotone, linear, dominated ⇒ one weight $W$ fixes the mass and recovers every dominated test.

**C. Quantitative control**
7. Second-translation recurrence raises moment order; Laplacians of moments bounded by $4^j$ times a square envelope.
8. Cauchy on the unit circle: values and derivatives of moved transforms; on a fixed strip the ordinate costs nothing.
9. Error splits: current error $\le\frac12B\cdot$(local log error), tail $\le C\cdot$sourceReferenceTail.
10. Canonical factorization + planar log kernels: $\int_{|z|\le n+2}\log^2|\xi|\le C(n+1)^6$ ⇒ prescribed regulators.
11. Finite theta prefix: potential stability $|\Delta\log|\le$ tail·envelope²$e^{-(N+1)^2}/\eta$; prefix $N$ chosen so $(N+1)^2$ beats the regulator scale.
12. Reference tail ≤ Lorentzian zero mass ≤ $(16/n)\Re(\xi'/\xi)$ at width point ≤ $(16/n)(C+\log(n+4))$.
13. Regularity: a $C^{k+2}$ test pays Hecke aperture $(2k+2)\log(n+1)$.

**D. Localization and collisions**
14. Bumps between disc indicators bracket enclosed multiplicity; integer multiplicity gives a two-radius threshold detector.
15. Gaussian collision kernel → indicator of distinct points with equal ordinate; positivity telescopes separate row/column
    errors into a pair-current error; rounding recovers the integer charge.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Hecke defect = symmetric second difference of $D$ | `heckeDefect_eq_second_difference` | proved |
| Defect controls tails and the second moment; doubling law | `depthKernel_mul_tail_le`, `four_mul_secondMoment_le`, `heckeDefect_double` | proved |
| Two scales read depth variance; equality ⇔ one absolute depth | `heckeDefect_sq_le_two_scale`, `depthDispersion_eq_zero_iff` | proved |
| ξ current = divisor trace; exhaustion recovers $D$ and $E$ | `sourceCurrentReading_eq_trace`, `tendsto_sourceCurrentReading_collided`, `tendsto_sourceCurrentReading_heckeDefect` | proved |
| Positive source metric = collided form; first moment = defect | `xiSourceMetric_eq_collided`, `xiSourceMoment_one_eq_heckeDefect` | proved |
| One weight dominates every compact transform and is summable on the divisor | `normSq_tr_le_universalSourceWeight`, `summable_universalSourceWeight` | proved |
| One schedule recovers all dominated tests, norms and moments | `tendsto_commonSourceReading_of_dominated`, `tendsto_commonSourceReading_depth_moment` | proved |
| Literal theta integrals recover all depth moments | `thetaSourceAmplitude_eq_xi`, `thetaSourceFirstMoment_eq_neg_deriv_xi`, `tendsto_thetaSourceMomentReading` | proved |
| Local trace brackets disc multiplicity | `sourceLocalTrace_mass_sandwich` | proved |
| Uniform moving-window recovery (common / explicit / theta) | `commonSourceReading_uniform_moving_moments`, `explicitSourceReading_uniform_moving_moments`, `thetaSource_uniform_moving_moments` | proved |
| Polynomial log-square bound for ξ | `exists_xi_log_square_polynomial_bound` | proved |
| Explicit regulator local error $\le(\pi(n+2)^2/2+8C(n+1)^6)e^{-(n+1)^4}$ | `exists_explicitSourceLocalError_bound` | proved |
| Reference tail $\le(16/n)(C+\log(n+4))$ | `sourceReferenceTail_le_log_div` | proved |
| Arithmetic error certificate for theta readings | `exists_explicitThetaSource_logarithmic_error_bound` | proved |
| Finite theta prefixes recover every compact current | `tendsto_finiteThetaSourceReading_compact`, `finiteThetaSource_uniform_moving_moments` | proved |
| One stage for all normalized tests in a growing aperture | `exists_finiteThetaSource_aperture_error_bound`, `polynomialThetaSource_uniform_test_aperture_moments` | proved |
| Regularity pays logarithmic apertures; smooth tests admit all | `source_regularity_moving_trace_tail_le`, `thetaSource_uniform_smooth_log_windows` | proved |
| Uniform zero detector on discs of radius $(16(n+1)^6)^{-1}$ | `exists_polynomialThetaLocalReading_error_bound`, `polynomialThetaLocalReading_uniform_zero_detector` | proved |
| Integer theta prefixes read the horizontal collision charge exactly | `tendsto_finiteThetaCollisionReading`, `eventually_floor_finiteThetaCollisionReading` | proved |
| Conductor horizon and companion forcing are disjoint for $0\le\delta\le\frac12$ | `forcing_requires_exponential_aperture`, `conductor_forcing_disjoint` | proved |

## 6. Tools

**Developed**
- Kernel and Green calculus: `depthKernel_double`, `laplacian_radialLogPotential`, `laplacian_real_holomorphic_comp`,
  `source_green_identity`, `laplacian_normSq_holomorphic`, `source_laplacian_mul`.
- Currents: `xi_realDivisorPairing_eq_carrier`, `xiCurrentPairing_eq_trace`, `tendsto_integral_xiCurvatureDensity`,
  `abs_xiCurvatureReading_sub_current_le_of_pos`, `tendsto_xiLocalLogError`.
- Cutoffs: `stripSourceCutoff_eq_one_of_strip_im_le`, `abs_stripSourceCutoff_laplacian_le`, `abs_sourceLocalCutoff_laplacian_le`,
  `stripSourceCutoff_mul_local_eq`.
- Transform bounds: `norm_tr_le_sourceGaussian`, `shiftedSourceTransform_disc_bound`, `shiftedSourceTransform_strip_bound`,
  `normSq_tr_strip_le_sourceTestSize`, `norm_tr_le_sourceRegularitySize`.
- Moments: `sourceDepthKernel_second_difference`, `abs_laplacian_cutoff_moving_moment_le`,
  `abs_laplacian_stripCutoff_aperture_moment_le_global`.
- Tails: `sourceDepthKernel_moving_tail_bound`, `tendsto_sourceReferenceTail`, `sourceAperture_moving_trace_tail_le`,
  `stripSource_aperture_moving_trace_tail_le`.
- ξ logarithm: `exists_abs_log_norm_gaussianXi_canonical_bound`, `xi_log_sq_canonical_integrable_bound`.
- Finite theta: `abs_finiteThetaSourcePotential_sub_xi_le`, `abs_finiteThetaSourcePotential_sub_xi_le_strip`,
  `exists_uniform_finiteTheta_compact_current_error`, `tendsto_thetaTestStage_error`,
  `abs_finiteThetaProductSourceReading_sub_finitePair_le`, `exists_finiteTheta_pair_current_error`.
- Collisions: `horizontalCollisionGaussian_error`, `exists_xiWindowGaussianPairSum_error`, `finiteThetaCollisionReading_error`.

**To build**
- A prime-side upper bound for the Hecke defect at $L\asymp\log T$ (the readings compute it, they do not bound it).
- An arithmetic correspondence acting as conjugation on the divisor (Frobenius at infinity), linking $(\rho,\bar\rho)$ to $(\rho,1-\rho)$.
- A structural bound $\Delta\le D$ uniform in depth and aperture.
- Bounds on the collision charge (below two) from the finite theta reading.
- Selection estimates at the zero spacing; exceptional-set control for the odd detector at zero ordinates.

## 7. Open questions

1. Is there a prime-side estimate of the Hecke defect at logarithmic scale, i.e. a zero-density statement read through $E$?
2. What arithmetic structure realizes conjugation on the zero divisor, so that the collided form becomes a Weil form?
3. Can the finite theta collision reading be bounded independently of the divisor, giving simplicity-type information?
4. Can the zero detector be pushed below the zero spacing (radius $\ll1/\log T$) with polynomial resources?
5. Which positive survivor remains between the conductor horizon and the forcing aperture?
6. Does two-scale dispersion rigidity combine with another scale to force depth zero?

## 8. Traps

| Trap | Fact |
|---|---|
| A positive sum of squares is Hecke invariant | Invariance under translation is exactly vanishing of the defect, i.e. RH for the tested zeros |
| Computing $D$ arithmetically bounds $\Delta$ | The readings recover the collided side only |
| Two Hecke scales force zero depth | Equality means one absolute depth shell, not depth zero |
| A spectral definition of a norm is an arithmetic metric | It must be evaluated from arithmetic data, as the theta readings do |
| An existence theorem with the desired sign as a field is progress | Circular |
| Finite certificates justify cofinal limits | Each limit here carries its own error certificate and tail bound |
| The explicit formula applies to antiholomorphic arguments | Needs new justification; the collided form is not holomorphic in the test |
| Companion forcing reaches the conductor horizon | Disjoint at every height for $0\le\delta\le\frac12$ |
| Zero detection needs isolated zeros | Bracketing by integer multiplicity needs no separation |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 17 (Poincaré–Lelong data, theta cusp amplitude bounds, Laplace/Lorentzian zero mass, Gaussian ξ growth, collision charge, deep-zero Hodge index) |
| HTGeometry | 9 (complex Laplacian, Green identity, planar log kernels, regularized log stability, pairwise variance) |
| ArithmeticPolarization | 2 (collided form, translation, elliptic localization) |
| ArithmeticCastelnuovoSeveri | 1 (zeta carrier vs ξ-zero copies) |

| Used by | Modules |
|---|---|
| RenormalizedBiarithmeticGeometry | 3 (depth distribution, two-scale rigidity, finite theta metric) |
| ArithmeticElectrostatics, HilbertianExplicitFormulas | 1 each (depth distribution; finite theta readings) |
| MainTheorems | umbrella import |

| Neighbour | Relation |
|---|---|
| ArithmeticPolarization | defines the two pairings, capacity identity and Hecke defect; CDG computes the collided side |
| BiarithmeticGaugeGeometry | central ceilings and positive deformations on the coupled class |
| ArithmeticEffectivityTheory | soft vs selective counting; the readings are counts that see the divisor |
| RenormalizedBiarithmeticGeometry | continues the Hecke moment problem and dyadic amplification of the defect |
| ArithmeticElectrostatics | reads the Hecke defect as a moment of inertia |
| HilbertianExplicitFormulas | uses finite theta readings for the resolvent depth |

## 10. Big picture

CDG settles the question "can the conjugate-diagonal side be computed from arithmetic?" in the affirmative and with
quantitative force: the collided form, every depth moment, the Hecke defect, local zero counts on discs shrinking polynomially
with height, and the horizontal collision charge are all limits of positive integrals of literal theta data, with polynomial
resources and explicit error certificates, uniformly over moving windows and growing apertures.

What this tells the RH effort is where the difficulty is not. Reading the divisor is solved; the depth information is
present in computable positive quantities. What is missing is a mechanism that forces those quantities to take their
critical-line values — an upper bound for the Hecke defect from the prime side, or a structure identifying the conjugate
pairing with the reflection pairing. Positivity of the collided side is free; its translation invariance is RH. The
conductor-forcing gap and two-scale shell rigidity show that local forcing and moment comparisons alone do not close it.
