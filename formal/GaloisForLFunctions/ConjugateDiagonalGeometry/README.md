# Conjugate-Diagonal Geometry (CDG)

Namespace `GaloisForLFunctions.ConjugateDiagonalGeometry`; umbrella `ConjugateDiagonalGeometry.lean`.

**Question.** Arithmetic constructions can evaluate a positive trace on the **conjugate diagonal** $(\rho,\bar\rho)$ of the zero
divisor; the explicit formula computes the **reflection pairing** $(\rho,1-\rho)$. Their coincidence on the zero divisor is the
critical-line assertion. What arithmetic geometry, trace identity or selective count connects the two? Assuming their
compatibility would assume the missing theorem.

---

## 1. Why the conjugate diagonal

With $\rho=\tfrac12+\delta_\rho+i\gamma_\rho$, multiplicity $m_\rho$, centred transform $\hat f$:
- the **collided form** $D(f)=\sum m_\rho|\hat f(\rho)|^2\ge0$ by construction;
- the **Weil form** $W(f)$ pairs transforms by functional-equation reflection and is computed by the explicit formula.

Capacity identity (APol): $\Re W=D-\Delta$, $\Delta\ge0$ the reflection disagreement. Positivity of $D$ does not bound $\Delta$; an explicit
formula for $W$ does not make it positive.

**Symmetric Hecke defect.** Centred translation $T_L$ multiplies $\hat f$ by $e^{L(\rho-1/2)}$, so
$D(T_Lf)+D(T_{-L}f)-2D(f)=\sum m_\rho(2\cosh(2\delta_\rho L)-2)|\hat f(\rho)|^2$: a positive measure of off-line depth; at $L\propto\log T$ a weighted
zero-density statistic; vanishing for a separating class is RH. An arithmetic *evaluation or upper bound* of it is a
substantive target even short of vanishing.

**Arithmetic source currents.** Literal finite theta prefixes give entire amplitudes $A_N$ and positive densities
$\eta|A_N'|^2/(\pi(|A_N|^2+\eta)^2)$; with prescribed prefixes, regulators and cutoffs they recover the actual multiplicity-weighted
collided trace and its depth moments. So $D$ and the Hecke defect *are* computed from arithmetic data (in the limit); the
comparison with the reflection pairing remains the capacity problem.

---

## 2. Objects and conventions

Spectral surface with independent coordinates $(s,t)$: conjugate diagonal $(\rho,\bar\rho)$, reflection graph $(\rho,1-\rho)$. Keep
conjugation, holomorphic reflection $s\mapsto1-s$ and Rosati reflection $s\mapsto1-\bar s$ distinct.

| Object | Lean (declaration or module) |
|---|---|
| Hecke defect, depth kernel, depth dispersion | `heckeDefect`, `depthKernel`, `depthDispersion_eq_zero_iff` |
| Xi source current and moments | module `XiSourceCurrent`; `xiSourceMoment_one_eq_heckeDefect` |
| Finite / polynomial theta source readings | `finiteThetaSourceReading`, `polynomialThetaSourceReading` |
| Common source regulator; fixed-strip exhaustion | modules `CommonSourceRegulator`, `StripSourceCutoff` |
| Local readings on shrinking discs | `exists_polynomialThetaLocalReading_error_bound` |
| Conductor–forcing gap; zeta depth distribution | modules `TheConductorForcingGap`, `ZetaDepthDistribution` |

Also used: two-variable kernels and diagonal traces; the correspondence algebra (normalized Hecke graphs, archimedean flow,
localizers $\sigma_\gamma$); prime gauge torus and $(+1,\times p)$; arithmetic counts and quadratic limits; completed and height-coupled
positive systems; escape measures and phase kernels.

A spectral definition of a norm is an object, not an arithmetic computation of it. A model identity is a calibration, not
a theorem about the zeta divisor.

| Distinction | Consequence |
|---|---|
| Positive / equivariant | Either can hold without the other |
| Collided / Rosati | Conjugate and reflection pairings need not coincide |
| Computed / posited | A formula must evaluate the object without its desired sign |
| Hyperbolic / elliptic / unipotent | Local type determines what positivity sees |
| Resonant / localizing | A special scale is not a correspondence isolating an unknown zero |
| Even / odd sector | Even sector positive at off-line pairs; odd sector can detect them |
| Gauge invariant / charged | Orbit information does not select the arithmetic point |
| Count / selective count | A positive quadratic limit can be identical on every fibre |
| Outward / inward deformation | Positivity can split a central double zero without its reverse |
| Classification / exclusion | Describing an escape state does not rule it out |
| Average / individual zero | Exceptional sets must be controlled at the selection scale |

---

## 3. Mechanisms

1. **Second-difference calculus** of $D$ under Hecke translation: the defect is a depth moment.
2. **Source currents from theta prefixes**: entire amplitudes, positive regularized densities, Green testing; integer truncation
   and logarithmic regularization separated.
3. **Fixed-strip exhaustion**: one bump stretched only in ordinate; Cauchy control on a fixed vertical strip is
   ordinate-independent, so every depth moment costs only $e^{\text{(support + Hecke displacement)}}$.
4. **Regularity pays the tail**: a compact test with $r$ derivatives pays the logarithmic window of width $(2r-2)\log(n+1)$; the
   omitted divisor tail is paid by the summable xi reference density.
5. **Polynomial schedules**: one integer majorizing bump derivatives fixes regulator scale and number of theta atoms, both
   polynomial in height, with no zeros used.
6. **Local bracketing**: bumps between concentric disc indicators bracket actual divisor mass with multiplicity; integer
   multiplicity turns a fixed threshold into a two-radius detector.

---

## 4. Pillar theorems

1. **Hecke defect = second difference = first source moment** (`heckeDefect_eq_second_difference`, `xiSourceMoment_one_eq_heckeDefect`).
2. **Source readings converge to the Hecke defect** (`tendsto_sourceCurrentReading_heckeDefect`, `tendsto_commonSourceReading_heckeDefect`).
3. **Polynomial integer-prefix theta sources recover all normalized tests** in a growing physical and Hecke aperture, with
   multiplicities and no critical-line or separation assumption (`polynomialThetaSource_uniform_test_aperture_moments`,
   `polynomialThetaSourceReading_error_le`).
4. **Uniform local readings** bracket shrinking-disc divisor counts in a growing height window (`exists_polynomialThetaLocalReading_error_bound`).
5. **Conductor–forcing gap** made precise (module `TheConductorForcingGap`); two-scale depth rigidity (`TwoScaleDepthRigidity`).

---

## 5. Traps

- A positive sum of squares does not establish Hecke invariance.
- A norm obtained by declaring spectral vectors orthogonal is not an arithmetic metric.
- An existence theorem whose object contains the desired sign as a field is circular.
- A one-variable explicit formula cannot be applied to an antiholomorphic argument without new justification.
- A finite trace identity does not justify an infinite trace; a finite certificate does not justify a cofinal limit.
- Computing $D$ arithmetically is not bounding $\Delta$: the readings recover the collided side only.
- The conductor horizon and the forcing aperture are distinct; neither theorem extrapolates into the gap.

---

## 6. Open problems (the eleven questions)

| Question | Required advance |
|---|---|
| Frobenius at infinity? | An arithmetic correspondence acting as conjugation on the zero divisor |
| What computes $D$? | Done in the limit by source currents; open: a prime-side upper bound for the Hecke defect at $L\asymp\log T$ |
| What selects the zeta fibre? | A fibre-dependent counting polarization equal to the Rosati form there |
| Where does section rank grow? | Section spaces escaping rank-one and product-lattice collapse |
| Elliptic localization across the horizon? | Odd-detector sign laws at zero ordinates with exceptional-set control |
| Non-archimedean charge? | Positivity whose separating margin is successor holonomy |
| What pays the capacity? | A structural proof of $\Delta\le D$, uniform in depth and aperture |
| Is the coupled class bounded at the centre? | Central-order ceilings (BGG) |
| Where does escape mass go? | Completeness when the real-part supremum is unattained, incl. infinite-height mass |
| How does an average select a zero? | Selection estimates at the zero spacing |
| What supplies the base? | A tensor structure with loss independent of the power |

Directions: **defect and density** (relate the Hecke defect to depth distributions; test two-variable or non-holomorphic
carriers such as truncated Eisenstein norms, proving they compute the intended trace); **elliptic forcing** (make the
conductor/forcing gap precise; exceptional-set estimates for the odd detector at actual zero ordinates); **successor charge**
(when one- and two-prime flipped twins lose positivity, and how the margin deteriorates with aperture).

## 7. Tools to build

Conjugate-diagonal explicit formulas; arithmetic Hermitian correspondence spaces with computed flow laws; selective
counting polarizations; elliptic localization beyond the conductor horizon; non-archimedean charged positivity;
central-order ceilings; oscillatory capacity bounds; selection estimates at zero spacing.

## 8. Place in the research and contribution standard

| Programme | Interface |
|---|---|
| ArithmeticPolarization | The two forms, capacity identity, Hecke defect, collision, localizers |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Intersection forms, Hodge index; orbit forms, orientation indices |
| ArithmeticCorrespondencePositivity, ArithmeticPositiveDuality | Weil layers; capacity and source selectivity |
| MultiplicativePositivityGeometry, StripBochnerWeilForcing | One-variable rigidity, anchors, forcing |
| ArithmeticCorrelationGeometry, BiarithmeticGaugeGeometry | Gauge orbit/point, successor holonomy, twins |
| ArithmeticEffectivityTheory | Counts, quadratic limits, soft vs selective polarization |
| BezoutValuationIncidence | Single-scale theta-prefix transfer and VK ceiling |

CDG owns constructions involving both spectral coordinates and their arithmetic interpretation. A contribution names the
positive and spectral sides, local type, gauge charge, parameter range and arithmetic content; reports on the battery
(pole-order relaxations, planted quartets, Beurling systems, golden datum, Liouville/sign-flipped/dominated twins,
height-coupled deformations, nonzero theta characteristics, escape models); and records the positive survivor of every
negative result. Definitions and equivalences are infrastructure, not progress on their endpoints.
