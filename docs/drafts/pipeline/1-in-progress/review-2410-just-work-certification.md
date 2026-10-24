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
- The explicit-collar module's 76 public declarations and the linear-window
  module's 23 public declarations have passed transitive axiom audits and
  canonical leaf checks. Joint import compatibility remains to be checked.
- Concurrent work now supplies `CHMDSharpGeneratorDomain` and the literal
  `SuzukiCriticalLiteralFamilyContraction` result. The former's formalized
  card records domain admission, exact action, skew-adjointness, a uniform
  commutator bound, and completed leaf/axiom checks. Preserve that work.
- `SuzukiCriticalMovingPrimaryEnergy` supplies the varying-source Fatou
  inequality. This is only the positive primary part of J4(iii); joint
  convergence of the signed compact-window correction is still required.
- The canonical spline already has support radius 4, gauge derivative bound
  `exp(4)/2`, integrated gauge derivative bound `4 exp(4)`, mass bound
  `2 exp(8)`, and Fourier bound `cosh(1)^4/(1+r^2)^2` in
  `SplineProbeFiniteShiftBounds`. These are the selected concrete J5 inputs.

## Pending proof sources

- J3 paper proof: `2-fully-proven/heath-brown-all-length-dilation-closure.md`.
  Unchecked Lean drafts are `/tmp/hgt-just-work-heath-brown-all-lengths.lean`,
  `/tmp/hgt-just-work-heath-brown-cover-body.lean`,
  `/tmp/hgt-just-work-sharp-s2-body.lean`, and
  `/tmp/hgt-just-work-sharp-s2-endpoints.lean`.
- J4(i) can use the existing cluster horizon followed by complete-form
  mollification. `TheRoutesMeasureOneAperture.contDiff_top_smooth` gives
  actual infinite smoothness; its support and complete-energy convergence
  lemmas retain an arbitrarily small aperture enlargement. The certified
  `xi_ne_zero_of_im_sq_le` height floor removes the horizon's height premise.

## Verification rules

Use only foreground, sequential `lake --old env lean` leaf checks from `formal/`.
Build only a missing imported olean or a new module needed by another file.
Do not compile umbrellas. No additional axioms, analytic premise interfaces,
trusted computation, or resource-limit increases. Preserve concurrent work.

## Gates

- [x] Exact J1–J8 inventory and concrete source-selection policy.
- [ ] J1 and J2 checked and audited.
- [ ] J3 exact published bounds formalized and audited.
- [ ] J4 exact four paper results formalized or subsumed with checked bridges.
- [ ] J5–J7 concrete inputs, bounds and applications certified.
- [ ] J8 existing finite certificates certified.
- [ ] Final current-state requirement audit; owned scratch cleaned.

Knowledge facts and failure modes: `logs/just-work-2410-knowledge.md`.
