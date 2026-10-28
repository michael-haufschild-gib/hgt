# Arithmetic Lorentzian Geometry (programme card)

- **ID:** ALG
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/fable2.md §4
- **Statement:** Develop the combinatorial Hodge theory of the affine monoid of ℤ: positivity of Weil's form by closure.

## Goal
Folder `formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/`, umbrella
`ArithmeticLorentzianGeometry.lean`, README = foundational doc. Answer Q1–Q5 of fable2 §4, build
the tools listed there, record no-go survivors.

## Status
All modules compile cleanly (`lake --old env lean`), are wired into the umbrella, and their main
theorems depend on standard axioms only. Co-editor modules: PolarGluingAndDispersion,
TheHalfDefectIsTheOptimalHodgeRepair; the README's extended scope is theirs — keep their text.

- Calculus and theorems: LorentzianFormsAtDegreeTwo, TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity,
  TheHodgeIndexTricklesDown, TheMetzlerDichotomy, LorentzianPolynomialsAndTheTuranLayer.
- Gauge and sign: TheSignIsAGaugeFixing, TheSuccessorConnectionIsTheArchimedeanGaugeField,
  LocalFactorsAndTheEulerProductClosure, FrobeniusIsConformalHeckeIsABoost.
- 𝔽_q calibration: TheFrobeniusLadderIsMetzler; TheTrickleDownInequalityIsTheSquareRootCount (TD_π on
  all ladders ⇔ square-root count; hyperelliptic curves trickle down via Stepanov);
  TheLocalFactorTricklesDownByRamanujan (depth 2g−1 decides; genus one: depth one ⇔ |a| ≤ 2√q,
  depth zero never decides; Kloosterman factor trickles down by Weil's bound).
- Atomic family of ζ: TheAtomicFormIsMetzlerBelowTheSpacing; TheOverlapFrustratesTheMetzlerGauge;
  TheMetzlerThresholdOfTheOverlapRatioIsOne (overlap law; threshold exactly K = 1);
  TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing (tilted margin μ_m ≥ 1 + (m/8N) log m pays the pole:
  signed Weil positivity, Hodge index, TD_π, links at K ≤ c★, uniformly in N; twist-blind);
  TheUniformMarginPaysThePoleOnlyUpToARootLogarithm (uniform margins fail at fixed K);
  TheTiltedMarginPaysThePolarDispersion (Gram = tilted model + NSD residual; dispersion ≤ reserves);
  TheAtomicMetzlerPropertyIsSelective; HyperbolicityIsBlindTheSignIsNot (every sign twin hyperbolic
  at K ≤ c★; Liouville twin hyperbolic, not Metzler); TheTowerDeficitIsARowSum.

## Open
- Window c★ < K < 1: TD_π for the Metzler Gram; the Markov form loses positivity along the pole
  vector n^{−1/2} (top of P_N, RAPT), paid by the pole term only in the Euler gauge; needed: a gap on
  its complement (cf. card selective-positivity-on-separated-atoms, gate C4).
- K > 1: primitive gap, or a non-atomic Metzler basis.
- Conformal correspondence with λ ≠ 1; product closure of Lorentzian polynomials; exhaustion.

## Findings so far
- Degree 2: Lorentzian = Hodge index (no gain); nef shift makes any finite Gram nonneg (trap).
- Gauge: ε(n/m)P(m,n) = ε(n) conj ε(m) P(m,n) ⇒ every twin's prime kernel is gauge-equivalent to
  Euler's; sign hypothesis needs a second, gauge-rigid kernel (archimedean).
- OQ2 as stated is false: n^{iτ} is a non-periodic torus point with prime form unitarily equivalent
  to Euler's; correct locus modulo archimedean characters.
- Beurling systems: nonneg coefficients + Euler product, can violate RH ⇒ multiplicative-only closure blind.
- Canonical atomic intersection form has negative diagonal ⇒ not a Hessian of a nonneg polynomial;
  only domination available.

- Metzler Hodge index (Lean): connected Metzler Q, D=Q1>0: hyperbolic ⇔ Q[v] ≤ Σ(Qv)_i²/D_i ⇔ hyperbolic links;
  diagonal unrestricted. Converts one-positive-square (not sum-closed) into NSD of Q − QD⁻¹Q (sum-closed).
  Euler-point intersection Gram is Metzler in canonical coords (P+J ≥ 0, pole row ≥ 0); twins are not in any gauge.
