# S6F positive-entire lower-jet boundary flux

- **ID:** S6F-BNF-LOWER-JET
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/theta-rank-three-direct-parabolic-determinant.md`
- **Statement:** Strict source positivity, entire analyticity, and the complete reflected jet through
  order eight do not determine rank-three singular-face crossing orientation.

## Goal

Test the proposed finite spectral-flux closure

```text
positive entire source + current reflected moments through order eight
→ positive singular-face boundary flux
→ global strict native D1
→ finite TCD/S6F rank-three gate
→ cofinal all-order Hankel/Bezoutian landing
→ Weil positivity
→ RH.
```

This is weaker than the active theta-specific boundary-flux conjecture: it deliberately asks
whether generic positivity/analyticity or a positive-moment interpretation can supply the missing
orientation without using the literal theta ninth-jet dynamics.

## Gates

- [x] 0 → 1 in-progress: exact source-compatible perturbation and proof-chain audit
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: closed Lean theorems in
  `ThetaCuspFullReflectionEighthBoundaryNinthJetTorsorNoGo`
- [ ] 3 → 4 publication-ready: standalone note and external priority review

## Approach

Use the positive entire family

```text
F_c(z) = cosh(z) exp(c z^9 / 9!).
```

The exponential gauge is invisible through order eight at the origin and changes the ninth jet by
exactly `c`. The common lower jet is

```text
(f₀,…,f₈) = (1,0,1,0,1,0,1,0,1),
```

so the reflected even moments are exactly `(1,2,8,32,128)`. Their rank-three Hankel determinant
vanishes and the leading rank-two minor equals `4`. The shift direction is `(0,0,0,0,2c)`, hence
the canonical null-line crossing is `32c` and the determinant first variation is `8c`.

## No-go closure

- **Exact killing theorem/mechanism:**
  `reflectedBoundaryNinthJetCrossingSign_not_determinedBy_lowerJet` proves no predicate of the
  depth-eight jet can determine crossing sign. The stronger realization theorem
  `exists_positiveEntire_reflectedBoundaryNinthJetCrossing_eq` gives every prescribed real
  crossing value inside a family whose real restriction is strictly positive everywhere and whose
  complex extension is entire.
- **Strongest positive survivor:** **ninth-jet torsor law**
  `reflectedBoundaryNinthJetCrossing_eq`: at the fixed strict-head singular face, crossing is
  exactly `32c`. Thus the missing orientation is one affine top-jet coordinate, not an unidentified
  property of the current Hankel face.
- **New insight:** S6F boundary flux cannot be obtained from source positivity, entire analyticity,
  lower reflected moments, or any positive spectral representation that forgets the literal ninth
  source jet. The surviving route must use theta-specific ninth-jet dynamics—equivalently the
  projective drift—or prove D1 without boundary orientation.
- **Status:** `[PROVED HERE][FORMALIZED]`. Closed Lean module, no hypotheses, no axioms added.

## Novelty audit

- `[CORPUS]` Existing `exists_signedEvenHankelThree_singular_strictHead_negativeCrossing` only
  gives arbitrary moment/direction data. Existing `crossingSign_not_determinedBy_hankelFace`
  varies an abstract moment extension. Neither realizes the sign freedom by one strictly positive
  entire source with fixed lower derivative jet.
- `[LITERATURE]` Salazar's order-moment criterion
  ([arXiv:2606.31647](https://arxiv.org/abs/2606.31647)) derives Hankel positivity from positive
  exponential/Mellin representations; it does not orient a singular reflected face after a flat
  odd analytic gauge. Belton--Guillot--Khare--Putinar
  ([arXiv:2006.16213](https://arxiv.org/abs/2006.16213)) classify total-positive Hankel kernels and
  preservers, but not this finite-jet crossing torsor. Basor--Chen
  ([arXiv:math-ph/0509043](https://arxiv.org/abs/math-ph/0509043)) study positive analytic weight
  perturbations asymptotically, not exact finite-jet boundary orientation.
- No exact positive-entire fixed-lower-jet rank-three crossing classification was found in the
  searched corpus or primary literature as of 2026-08-31. Priority claim remains provisional
  pending expert review.

## Log

- 2026-08-31 — positive exponential-mixture conjecture rejected by existing theta Laplace no-go;
  pivoted to flat-gauge hostile test.
- 2026-08-31 — exact ninth-jet torsor proved and formalized; lower-jet spectral-flux route retired.
