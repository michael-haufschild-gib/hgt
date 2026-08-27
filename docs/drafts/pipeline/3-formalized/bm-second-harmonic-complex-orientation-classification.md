# BM second-harmonic complex-orientation classification

- **ID:** HB-BM-COC
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + NO-GO + POSITIVE SURVIVOR
- **Parent:** HB
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION]` Reflected canonical BM currents have a unique complex relative cancellation coefficient. It is nonreal on every Xi fibre; all real signed weights and all fixed bioriented complex weights cancel only trivially.

## Goal

Attack missing augmented Peierls source incidence after Hermitian norm-square weights failed. Classify
full complex reflection-cancellation hyperplane and determine whether real sign-indefinite or fixed
complex orientation can supply missing functional-equation-odd seam.

## Gates

- [x] 0 → 1 in-progress: complex-orientation conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: exact ratio, nonreal phase, real rigidity, reflection reciprocity
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

Write `λ(q)` for canonical BM complementary exponent and
`J(q) = -λ(q)` for exact regular/complementary polarized current. On every Xi fibre,

`λ(q) + λ(Jq) = 8n+5`,

`Im λ(Jq) = -Im λ(q) ≠ 0`, while both real parts are positive. Therefore

`a J(q) + b J(Jq) = 0  ↔  b = a r(q)`,

where `r(q) = -λ(q)/λ(Jq)`. Moreover `Im r(q) ≠ 0`, `r(Jq)=r(q)⁻¹`, real `a,b`
force `a=b=0`, and a single ordered complex pair `(a,b)` cancelling at both `q` and `Jq` also
forces `a=b=0`.

## Complete paper proof

Nonvanishing of denominator follows from its positive real part. Division solves linear cancellation
equation uniquely. If ratio were real, multiplying it by reflected exponent and comparing imaginary
parts forces its real value to be one. Comparing real parts then says one positive real part is
negative of another, contradiction. Reflection exchanges numerator and denominator, giving inverse
ratio. A fixed bioriented cancellation would force ratio equal to its inverse; hence its square is
one, so it is `±1`, contradicting nonzero imaginary part.

## Hostile review and novelty verdict

- Birmingham--Mokhtari derive exact topological-black-hole QNM frequencies and hypergeometric
  structure, but not this Xi-reflection source-orientation classification.
- Current sourced Teukolsky and conserved-current literature treats nonlinear sources, Green
  functions, and complex-frequency currents, but narrow searches found no negative exponent-quotient
  law, all-real-weight rigidity, or bioriented cancellation theorem.
- Algebra after exact exponent/current identities is elementary. Novel content is precise terminal
  classification for this coefficient-faithful HB producer class.

Verdict: abstract two-vector cancellation `[REDISCOVERED]`; BM/Xi complex orientation law and
Peierls-source consequence `[NEW] [CLASSIFICATION]`, external priority provisional.

Primary audit: Birmingham--Mokhtari, arXiv:hep-th/0609028; Green et al., arXiv:2210.15935;
Spiers--Pound--Moxon, arXiv:2305.19332; Spiers, arXiv:2402.00604.

## No-go closure

- **Exact killing mechanism:** real reflection weights cannot absorb opposite nonzero imaginary
  exponent parts while respecting simultaneous positive real parts.
- **Strongest positive survivor:** ordered complex cancellation exists uniquely and transforms
  covariantly by inversion under reflection.
- **New insight:** surviving augmented Peierls incidence must be divisor-dependent and
  reflection-covariant with a genuinely complex phase. Hermitian, signed-real, and fixed bioriented
  source laws are exhausted.
- **Status:** dependency-closed paper proof and Lean formalization complete.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicComplexOrientationClassification.lean`
- Exponent geometry:
  `d4BMXiPlusPlusComplementaryExponent_im`,
  `d4BMXiPlusPlusComplementaryExponent_reflect_im`
- Exact complex cancellation line:
  `d4BMXiReflectionComplexWeightedRegularComplementaryCurrent_eq_zero_iff`
- Nonreal phase and real rigidity:
  `d4BMXiReflectionComplexCancellationRatio_im_ne_zero`,
  `d4BMXiReflectionRealWeightedRegularComplementaryCurrent_eq_zero_iff`
- Reflection covariance and bioriented no-go:
  `d4BMXiReflectionComplexCancellationRatio_reflect`,
  `d4BMXiReflectionComplexWeightedCurrent_bioriented_eq_zero_iff`
- Direct `lake env lean` passed.
- Targeted module build passed.
- `#print axioms`: standard theorem dependencies only; no project axiom introduced.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from exact reflection exponent sum, positive-real-part theorem, and
  nonzero Xi height in Lean corpus.
- 2026-08-27 — complex cancellation classification and Lean proof completed.
