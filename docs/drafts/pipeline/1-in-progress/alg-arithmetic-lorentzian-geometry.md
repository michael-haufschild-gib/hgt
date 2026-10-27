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

## Module plan (status: todo / done)
DONE: LorentzianFormsAtDegreeTwo, TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity, TheHodgeIndexTricklesDown (all clean, wired in umbrella).
1. LorentzianForms — degree-2: hyperbolic ⇔ revCS ⇔ no PD plane ⇔ NSD on hyperplane; Loewner
   domination; pullback; product of nonneg linear forms; sums fail; CND ⇒ hyperbolic; CND sums.
2. TheArithmeticHodgeIndexIsHyperbolic — hermPosIndex ≤ 1 ⇔ complex revCS; RH ⇔ revCS for scaling
   surface cycles (via ACS riemannHypothesis_iff_one_positive_square); nef shift trap.
3. TheHodgeIndexTricklesDown — 3-tensor, hyperbolic links ⇒ Q[v] ≤ (Qv)ᵀD⁻¹(Qv); connected ⇒ posIndex ≤ 1.
4. TheSignIsAGaugeFixing — twisted prime kernel = gauge conjugate of Euler; pairwise-positive kernel
   forces constant gauge; nonneg gauge for both ⇔ ε(p)=1 on primes ≤ N.
5. LorentzianPolynomials — coefficient definition, bivariate ⇔ ULC, disjoint products, derivatives.
6. Multiplicative closure blindness (Beurling/fake datum).
7. 𝔽_q calibration of trickle-down on Frobenius ladder (OQ3).
8. Successor defect of atomic prime form (M2 lemma).
9. Torus positivity locus mod archimedean characters; eventual successor flatness ⇒ Euler.

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

## Log
- 2026-10-27 — created; README first draft written.
