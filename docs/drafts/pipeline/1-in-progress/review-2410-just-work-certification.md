# Certification of the review's routine mathematical inputs

- **ID:** review-2410-just-work-certification
- **Stage:** 1-in-progress
- **Type:** formalization and integration programme
- **Source:** `docs/reports/review-2410/hard-obstacles-summary.md`, §2.1 J1–J8.
- **Statement:** Certify the exact existing analytic inputs, paper results, concrete-source specializations, and finite certificates listed in J1–J8, without adding an arithmetic sign or an unproved premise.

## Scope and acceptance evidence

| Task | Required result | Evidence required |
|---|---|---|
| J1 | Four named integration targets and every recently wired family in §2.1 | Current umbrella imports; direct leaf checks; transitive axiom audit of public declarations |
| J2 | Distinct APT majorant names; usable explicit kernel-shape results | Both leaves check; joint import compatibility; public-declaration axiom audit |
| J3 | All-length Heath–Brown pair-sum bound; sharp all-k S₂ family | Exact published statements proved with no analytic premise; source checks and axiom audit |
| J4(i) | Negative smooth compact Weil witness with aperture at most C δ⁻²(4+|γ|)³⁸ | Exact theorem or verified stronger theorem with a proved specialization, including smoothness |
| J4(ii) | Sharp CHMD generator-domain admission and bounded arithmetic commutator | Concrete operators, exact graph identity, domain and action theorems |
| J4(iii) | Common-window strong-L² Gamma-liminf and constant recovery | Joint limit theorem retaining Gamma, prime and both polar terms |
| J4(iv) | Literal high-dyadic-family strict deficit | Concrete unsmoothed family; finite energy and strict positivity derived |
| J5 | Concrete compact-source Fourier decay, integrability, collars, derivative bounds | Explicit source and aperture-dependent constants, all premises proved |
| J6 | Visibility, collars, windows, (1/2,75), centered-prime ranges | Symbolic certified bounds for selected canonical sources; no numerical experiment |
| J7 | All named dictionaries applied where their input is proved | Exact source instances and conclusions; no assumed missing estimate |
| J8 | Existing finite certificates checked in the listed classes | Explicit corpus objects and kernel proofs; no certificate search or cofinal claim |

## Source choices

Use canonical corpus objects: the universal compact spline for lag/width work,
the actual compact critical family for Suzuki and collar work, and existing
finite witness objects for certificate checks. Select applicable source-specific
variants when a dictionary has a different domain. Never invent missing
arithmetic estimates to make a dictionary applicable.

## Exact concrete targets

- **Spline inputs:** `U_a(x)=splineProbe(4x/a)`, for every a>0. Prove nonzero
  C² compact support in [-a,a], `|U_a|≤exp(4)/2`,
  `|U_a'|≤3exp(4)/a`, `∫|U_a'|≤6exp(4)`, and
  `∫U_a²≤a exp(8)/2`. Retain the exact scaled Fourier variable `(a/4)r`,
  quartic decay, and the weighted Fourier and Gamma integrability conclusions.
- **Critical scales:** channel-to-slope allowances `125000·10¹⁵` and
  `66000·10⁸`; polynomial-window allowance `363000·10¹⁵` and exponent
  `10⁻²¹`. The quarter-radius, quarter-depth visibility probe retains its
  supplied loudness parameter. Centered rows use δ=1/10, ε=1/2, C=2:
  exponents 11/10, 283/170, 71/120, and coefficient 8; P₀ remains existential.
- **Dictionary sources:** the unscaled universal spline for the width reading,
  the radius-1/5 spline, its odd part, the aperture
  chain 1/10, 1/5, 3/10, and the actual half-damped Möbius receiver.
  Conclusions include the 1/5000 terminal margin, compensated constant
  -1/5000, empty hull and quotient rank zero, prime-two heat window
  `a≤1/(32n)`, exact Suzuki tangent, odd-cone Riemann–Roch allocation,
  graded cost `75 exp(1/5)∫F²`, and the scale-four Lefschetz identity.
- **Finite certificates:** golden span and tower dimension two; canonical
  triangle and packed graph; radical horizon five (states dividing 30);
  Hausdorff orders 0–3; four central-slice quadratic Jensen tests; five
  positive theta moments and four adjacent inequalities; heat-Hankel ranks
  1–4 at time κ/4; stack `[(1,1),(2,1/2),(1,1)]`.

## Current evidence and gaps

- J7's global HF ceiling application has no proved input. Its exact premise
  `∀ᶠ L in atTop, windowCeiling L ≤ exp(L/2)+B(1+L)` implies RH, as proved in
  `PrimeWindowCeilingRHCriterion`. The already proved dictionary can be
  audited, but claiming an unconditional application would cross the stated
  scope. Local and graded allocation instances remain available.

- The report predates existing imports of `CHMDSharpWindowNodalConvergence`,
  `LambdaRingEffectivityAndHeckeLefschetzRigidity`, and
  `SuzukiCriticalL2Arithmetic`; preserve these imports.
- APT's two `envelopePrimeMajorant_one_eq` declarations have different right-hand
  sides and quantifiers. The all-natural rpow formula is named
  `envelopePrimeMajorant_one_eq_rpow`; the restricted sqrt formula keeps its name.
- The centered-heat target includes a C∞ compact complex witness and the
  power-38 aperture bound. The certified cluster-horizon bridge includes both
  and proves the stronger quadratic bound. Both theorem cards are in stage 3;
  the alternative centered-heat derivation remains a paper proof, without
  a separate novelty claim or a claim that its particular derivation is formalized.
- J3 is not discharged by `guthMaynardLargeValuesBound_holds`: the requested
  pair-sum and all-k statements must each be checked independently.
- All 22 integration leaves in `logs/just-work-2410/inventory.json` passed
  canonical leaf checks and transitive axiom audits of 440 public declarations.
  Every recorded source hash matches the current source. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur. Per-leaf commands, source hashes,
  declaration lists, and outputs are retained in `logs/just-work-2410/`.
  This includes the explicit-collar module's 76 declarations and the
  linear-window module's 23 declarations. Their joint import also passed,
  with both majorant declarations checked together; evidence is in
  `logs/just-work-2410/APTJointImport.json`.
- Concurrent work now supplies `CHMDSharpGeneratorDomain` and the literal
  `SuzukiCriticalLiteralFamilyContraction` result. The former's formalized
  card records domain admission, exact action, skew-adjointness, a uniform
  commutator bound, and completed leaf/axiom checks. Preserve that work.
- J4(ii) and J4(iv) have exact stage-3 certificates:
  `chmd-sharp-generator-boundary-domain.md` and
  `sz-critical-family-literal-source-deficit-2026-10-24.md`.
  The latter derives finite energy and positivity for the literal
  `criticalTruncatedTest`; no smoothing or assumed source-energy premise
  remains. Their declared final checks and standard-axiom audits cover the
  requested statements. Imported oleans are absent for these leaves, as
  expected when no dependent file needs them.
  Current source hashes match those certificates; reuse evidence is in
  `logs/just-work-2410/J4ExistingCertificates.json`.
- `SuzukiCriticalMovingPrimaryEnergy` supplies the varying-source Fatou
  inequality. `SuzukiCriticalMovingWindowDeficit` supplies joint convergence
  of the signed compact-window correction and closes J4(iii).
- The canonical spline already has support radius 4, gauge derivative bound
  `exp(4)/2`, integrated gauge derivative bound `4 exp(4)`, mass bound
  `2 exp(8)`, and Fourier bound `cosh(1)^4/(1+r^2)^2` in
  `SplineProbeFiniteShiftBounds`. These are the selected concrete J5 inputs.

## Lean evidence

- J3 certificate: `3-formalized/heath-brown-all-length-dilation-closure.md`.
  `RHTower/Sieve/HeathBrownPairSumAllLengths.lean` proves the exact
  `heathBrownPairSumBound_holds` endpoint. Its full-source scratch check and
  all seven public transitive axiom audits passed. The canonical leaf check
  passed and the owning umbrella imports it once.
  `RHTower/Sieve/GuthMaynardSharpSTwo.lean` supplies the sharp all-k S₂ family
  and Proposition 12.1. Its full-source check, all three public axiom audits,
  and canonical final check passed; the owning umbrella imports it once.
- J4(i) uses the existing cluster horizon followed by complete-form
  mollification. `TheRoutesMeasureOneAperture.contDiff_top_smooth` gives
  actual infinite smoothness; its support and complete-energy convergence
  lemmas retain an arbitrarily small aperture enlargement. The certified
  `xi_ne_zero_of_im_sq_le` height floor removes the horizon's height premise.
  The proved bound is stronger: `a ≤ C δ⁻²(4+|γ|)²`. Set
  `u=K(4+|γ|)/δ`, `a=u²`, with
  `K=exp(6)+10⁹(A+1)` for the cluster-horizon constant `A≥1`.
  The inequalities `log(u²)²≤16u` and `log(|γ|+306)≤77(4+|γ|)`
  discharge the horizon condition; smoothing enlarges the radius by at
  most one, paid by `a+1≤2u²`. This is a direct coarse consequence of the
  existing horizon, with no novelty claim. The required power-38 result
  follows since `4+|γ|≥1`. The full-source check and all three public axiom
  audits passed in `SquareRootThreshold/SmoothWeilDetectorPolynomialAperture.lean`.
  The canonical final check passed; the owning umbrella imports it once.
  Exact paper proof and novelty audit:
  `3-formalized/cluster-horizon-smooth-polynomial-detector.md`.
- The current corpus contains `RHTower/Suzuki/SuzukiCriticalMovingWindowDeficit.lean`,
  with the exact joint extended-Weil liminf and constant recovery on arbitrary
  a.e. common windows `[a,b]`. All 17 public declarations passed the full-source
  axiom audit and the canonical final check. The owning umbrella imports it once.
  The additional
  compact-family uniformity theorem retains a supplied common Weil floor and
  does not produce a global sign.
- `BiScaleUncertainty/ExplicitApertureSplineInputs.lean` supplies 17 public
  declarations and is imported once by its umbrella. Its Gamma proof uses
  the Fourier autocorrelation identity directly, avoiding the incompatible
  `localPair` exports from two intersection-theory modules. The revised source
  requires a canonical check and its included 17 axiom reports.
- Concrete dictionary instances are in
  `ArithmeticOrientationTheory/ConcreteSourceDictionaries.lean`, with explicit
  `#print axioms` checks. Direct canonical checking remains required.
- `ArithmeticOrientationTheory/ConcreteReceiverScales.lean` passed the full-source
  check and all seven public axiom audits. It proves the stated threshold,
  visibility and centered-prime scales. Its canonical final check passed;
  the owning umbrella imports it once.
- `ArithmeticOrientationTheory/ConcreteFiniteSourceCertificates.lean` passed the
  full-source check and all 13 public axiom audits, covering every selected finite
  object above. Its canonical final check passed; the owning umbrella imports it once.
- The concrete dictionary instances use the radius-`1/5` spline and its odd
  part, the finite aperture chain `1/10, 1/5, 3/10`, and the actual
  half-damped Möbius receiver. The finite transport is bounded; no
  unbounded-aperture sign or sub-half damping estimate is asserted.

## Verification rules

Use only foreground, sequential `lake --old env lean` leaf checks from `formal/`.
Build only a missing imported olean or a new module needed by another file.
Do not compile umbrellas. No additional axioms, analytic premise interfaces,
trusted computation, or resource-limit increases. Preserve concurrent work.

## Gates

- [x] Exact J1–J8 inventory and concrete source-selection policy.
- [x] J1 integration leaves wired, checked, and audited.
- [x] J2 joint import compatibility checked after the name repair.
- [x] J3 exact published bounds formalized and audited.
- [x] J4 exact four paper results formalized or subsumed with checked bridges.
- [ ] J5 revised concrete source inputs checked after removing the conflicting import.
- [x] J6 concrete constants and ranges certified.
- [ ] J7 applicable dictionaries certified; global HF premise classified separately.
- [x] J8 existing finite certificates certified.
- [ ] Final current-state requirement audit; owned scratch cleaned.

Knowledge facts and failure modes: `logs/just-work-2410-knowledge.md`.
