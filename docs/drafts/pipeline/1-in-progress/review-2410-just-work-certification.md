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
- The centered-heat paper card says its proof was removed as redundant with
  `zeta_hodge_index_cluster_horizon`. Exact smooth-witness and aperture coverage
  still require inspection; a novelty verdict is not a theorem audit.
- J3 is not discharged by `guthMaynardLargeValuesBound_holds`: the requested
  pair-sum and all-k statements must each be checked independently.
- All 22 integration leaves in `logs/just-work-2410/inventory.json` passed
  canonical leaf checks and transitive axiom audits of 440 public declarations.
  Every recorded source hash matches the current source. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur. Per-leaf commands, source hashes,
  declaration lists, and outputs are retained in `logs/just-work-2410/`.
  This includes the explicit-collar module's 76 declarations and the
  linear-window module's 23 declarations; their joint import remains to be checked.
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
- `SuzukiCriticalMovingPrimaryEnergy` supplies the varying-source Fatou
  inequality. This is only the positive primary part of J4(iii); joint
  convergence of the signed compact-window correction is still required.
- The canonical spline already has support radius 4, gauge derivative bound
  `exp(4)/2`, integrated gauge derivative bound `4 exp(4)`, mass bound
  `2 exp(8)`, and Fourier bound `cosh(1)^4/(1+r^2)^2` in
  `SplineProbeFiniteShiftBounds`. These are the selected concrete J5 inputs.

## Pending proof sources

- J3 paper proof: `2-fully-proven/heath-brown-all-length-dilation-closure.md`.
  Assembled unchecked Lean drafts are
  `/tmp/hgt-just-work-heath-brown-closure.lean` and
  `/tmp/hgt-just-work-sharp-s2.lean`. These are the sources to check and repair;
  their separate preparation fragments are not independent certificates.
- J4(i) can use the existing cluster horizon followed by complete-form
  mollification. `TheRoutesMeasureOneAperture.contDiff_top_smooth` gives
  actual infinite smoothness; its support and complete-energy convergence
  lemmas retain an arbitrarily small aperture enlargement. The certified
  `xi_ne_zero_of_im_sq_le` height floor removes the horizon's height premise.
  The proposed bound is stronger: `a ≤ C δ⁻²(4+|γ|)²`. Set
  `u=K(4+|γ|)/δ`, `a=u²`, with
  `K=exp(6)+10⁹(A+1)` for the cluster-horizon constant `A≥1`.
  The inequalities `log(u²)²≤16u` and `log(|γ|+306)≤77(4+|γ|)`
  discharge the horizon condition; smoothing enlarges the radius by at
  most one, paid by `a+1≤2u²`. This is a direct coarse consequence of the
  existing horizon, with no novelty claim. The required power-38 result
  follows since `4+|γ|≥1`. Both still require Lean verification.
  Exact paper proof and novelty audit:
  `2-fully-proven/cluster-horizon-smooth-polynomial-detector.md`.
- Unchecked complete drafts now cover the polynomial detector aperture
  (`/tmp/hgt-just-work-polynomial-aperture.lean`), the full moving-source
  Suzuki theorem (`/tmp/hgt-just-work-suzuki-moving-signed.lean`), explicit
  aperture-scaled spline inputs (`/tmp/hgt-just-work-spline-aperture-inputs.lean`),
  finite source certificates (`/tmp/hgt-just-work-finite-source-certificates.lean`),
  explicit ranges (`/tmp/hgt-just-work-explicit-ranges.lean`), and concrete
  dictionary instances (`/tmp/hgt-just-work-concrete-dictionaries.lean`).
  These are proof candidates, not certified results. Their canonical leaf
  checks and transitive axiom audits remain required.
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
- [ ] J2 joint import compatibility checked after the name repair.
- [ ] J3 exact published bounds formalized and audited.
- [ ] J4 exact four paper results formalized or subsumed with checked bridges.
- [ ] J5–J7 concrete inputs, bounds and applications certified.
- [ ] J8 existing finite certificates certified.
- [ ] Final current-state requirement audit; owned scratch cleaned.

Knowledge facts and failure modes: `logs/just-work-2410-knowledge.md`.
