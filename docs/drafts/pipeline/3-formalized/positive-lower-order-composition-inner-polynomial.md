# Positive lower order forces polynomial inner factors at finite order

- **ID:** POSITIVE-LOWER-COMPOSITION-20261008
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`

## Statement

Let F,g:C→C be entire. If F has `PositiveLowerOrder` and F∘g has `FiniteOrderEnvelope`, then g is polynomial. These are the exact existing corpus definitions, not new assumptions about actual Xi. The hypothetical covering projection still needs its own positive-lower-order proof.

## Prior corpus

`HTGeometry/PolyaCompositionMaximum.exists_polya_constant` gives an absolute composition maximum inequality. `IteratedExponentialGrowthHeight` defines positive lower order. `PolynomialAntiderivative.exists_polynomial_of_polynomial_growth` recognizes entire polynomials from a global polynomial norm bound. `CompositionGrowthHeight` handles growth-height addition but does not provide this arbitrary-inner-factor conclusion. Corpus searches found no exact declaration; external novelty is unverified and no novelty claim is made.

## Complete paper proof, with global constants

Choose δ>0 and R0 so every R≥R0 admits u with |u|≤R and exp(R^δ)≤|F(u)|. Write |F(g(z))|≤exp(C(1+|z|)^d), with C≥0 and d a natural number. Let c>0 be the corpus's Pólya constant, b=|g(0)|, and choose a natural N with Nδ≥d. Choose K≥1, K≥R0 and K^δ≥C·3^d+1. Put M=(K+(c+1)b)/c.

Claim |g(z)|≤M(1+|z|)^N for every z. Otherwise set v=1+|z|, r=2v, H=|g(z)|−b, R=K v^N. The contrary inequality implies R+b<cH and H>0. Apply Pólya to G(w)=F(w+g(0)) and h(w)=g(w)−g(0), since |h(z)|≥H and |z|≤r/2. It yields z' with |z'|<r and |G(w)|≤|F(g(z'))| whenever |w|≤cH.

Choose u from the positive-lower-order bound at R (R≥R0). Since |u−g(0)|≤R+b<cH,
exp(R^δ)≤|F(u)|≤|F(g(z'))|≤exp(C·3^d v^d).
But v≥1 and Nδ≥d imply R^δ=K^δ v^(Nδ)≥(C·3^d+1)v^d>C·3^d v^d, a contradiction. Thus the global polynomial norm bound holds, and the corpus's polynomial-growth theorem makes g polynomial.

No compactness patch, translated lower-order theorem or additional growth premise is needed.

## Formalization and actual Xi consequence

- `HTGeometry/PositiveLowerOrderCompositionRigidity.lean`: `exists_polynomial_inner_of_positiveLowerOrder_comp` proves the exact paper theorem.
- `RHTower/XiFiniteCriticalFactorRigidity.lean`: `finiteOrderEnvelope_xi` transports the existing order-one bound. `xi_ne_comp_of_positiveLowerOrder_finite_critical_values` proves that actual Xi cannot equal F∘g when F,g are entire, F has positive lower order, and F has finitely many critical values. It uses the new polynomial-inner theorem plus Xi's proved infinite critical-value set.
- Both source modules wired to theorem-area umbrellas.
- Leaf build PASS: `lake build --old +GaloisForLFunctions.RHTower.XiFiniteCriticalFactorRigidity`, 11098 jobs. Only replayed dependency warnings; no new-source warning.
- Scratch generic theorem checked with zero warnings. Three-declaration axiom audit: PASS, only propext, Classical.choice, Quot.sound. Final direct checks of both actual source files: PASS, exit 0 with empty logs `/tmp/hgt-finite-order-inner-final.log` and `/tmp/hgt-xi-factor-rigidity-final.log`.

This eliminates that intrinsic class of outer factors. It does not prove the hypothetical transcendental covering projection belongs to the class: completing/uniformizing the cover and deriving positive lower growth remain active obligations. RH remains unproved; external novelty unverified.

- 2026-10-09 validation: regenerated formal index; global lint FAIL on ten unrelated unreachable modules (RHTower.CCMFullGroundZeroSideEigen, MobiusRieszNormalizedEscape; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, PaperFourierLLogL.Compress.Search, PaperFourierLLogL.Finite.Law, PaperFourierLLogL.HeightLayers). No own-source failure. See `/tmp/hgt-xi-factor-rigidity-lint.log`.
