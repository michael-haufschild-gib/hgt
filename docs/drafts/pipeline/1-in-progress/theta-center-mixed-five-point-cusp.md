# Theta center-mixed five-point cusp

- **ID:** TCD-C12-FIVE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** rh-current-frontier-map.md · route TCD
- **Statement:** For every aperture `a > 0`, the equispaced five-node Gram matrix of the theta center-mixed density is positive definite on a punctured neighborhood of the coalesced node.
- **Status:** `[RANK-FIVE SOURCE SEAM PAPER-PROVED] [RANK-FIVE SOURCE SEAM LEAN-PROVED] [GLOBAL D1 OPEN]`

## Goal

Close rank five in the TCD cofinal positive-definiteness programme. The target is source-pure: it uses the already formalized theta cusp source and center-mixture representation, not RH or a zero-free hypothesis. Rank five is the first step not controlled by the proved second--sixth reflected Hankel curvature.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus-driven decomposition

For an even kernel sampled at `0,h,2h,3h,4h`, reversal symmetry splits the five-by-five Toeplitz Gram form into an odd block of dimension two and an even block of dimension three.

- The odd block's first nonzero coalesced coefficient is governed by the already proved strict second--sixth signed reflected Hankel determinant.
- The even block's first nonzero coefficient is governed by the signed three-by-three reflected jet matrix
  ```text
  [[ J0, -J2,  J4],
   [-J2,  J4, -J6],
   [ J4, -J6,  J8]].
  ```
- Corpus search found `integral_twoByTwo_det_pos` but no corresponding strict three-by-three integral-mixing theorem. It found all-order matrix spectral machinery only under stronger spectral-representation or separation hypotheses not yet established for this center mixture.

## Conjecture loop

### D1 — global source eighth-Hankel curvature

For every real source coordinate, the signed three-by-three reflected jet matrix above is positive definite. In normalized complete-log coordinates
`A = -ℓ₂`, `B = -ℓ₄`, `C = -ℓ₆`, `D = -ℓ₈`, its determinant is an explicit polynomial. The existing sixth-curvature proof supplies the leading two principal minors; new burden is the determinant involving `D`.

Attack: extend corpus likelihood-score and Bell-transfer infrastructure from order six to order eight, prove symbolic score identities, derive analytic rational tail bounds, and clear the resulting polynomial chamber in Lean. No numerical interval certification.

**Seam result `[PROVED HERE]`.** The self-dual modular ODE closes two further jet steps. For modular mass `M`, scale `R`, and `X=R²`, the signed rank-three determinant is exactly `M⁶ P₁₂(X)`. After `X=191/10+y`, every coefficient of `P₁₂(191/10+y)` is strictly positive. Since the actual source satisfies `X>191/10` and `M>0`, the complete theta source has strict signed rank-three reflected eighth-jet curvature at `x=0`. This is an exact rational polynomial proof, not interval arithmetic. Global continuation remains D1.

### D2 — strict three-by-three mixture law

If D1 holds pointwise for the reflected source field, integrate its quadratic forms against the positive center-mixed radial weight. Prove strict positivity of the integrated matrix, then its determinant. This generalizes the corpus theorem `integral_twoByTwo_det_pos` by one rank.

### D3 — five-point parity cusp

Formalize reversal-parity congruence, Taylor jets through the first nonzero even and odd block determinants, and positivity on a punctured right neighborhood. Expected smoothness burden is order twelve. Build generic center-product jets if explicit differentiation becomes duplicative.

### Pivot criteria

If D1 is false, prove the exact sign obstruction and audit D2 directly: pointwise failure need not imply failure after positive mixing. If the center determinant is also false, extract the sharp aperture/radial boundary or maximal rank-four survivor before retiring this branch. Missing order-eight or order-twelve infrastructure is not a pivot criterion.

## Novelty collision audit

Closest August 2026 item is Planat--Solé's second-level concavity theorem for the classical Xi kernel. Its inequality uses derivatives through order eight and may be algebraically related to one principal-minor expression. Before any novelty claim, compare its exact transformed kernel and determinant polynomial with D1 and with the center-mixture theorem. No corpus theorem currently proves D1--D3.

Exact comparison now separates the statements. Planat--Solé prove negativity of the successive-derivative Hankel determinant `det(s^(i+j))_(0≤i,j≤2)` for `s(t)=Φ(√t)` in radial-square coordinate, equivalently strict log-concavity of `s'²-ss''`. D1 is positivity of the signed even reflected-product jet determinant of `u↦Φ(x+u)Φ(x-u)` in logarithmic source coordinate, for every center `x`. Derivative order overlaps, but kernel, coordinate, determinant, and sign differ. The seam theorem above is therefore not obtained from their result.

## Lean artifacts

- `HilbertMetric/ReflectionEighthJet.lean`: exact eighth reflected product jet and even-log determinant polynomial.
- `HTGeometry/PolynomialODEJetRankThreeClosure.lean`: exact ten-jet self-dual ODE elimination.
- `RHTower/PrimeArchThetaModularDifferentialClosure.lean`: actual theta-source modular connector.
- `RHTower/ThetaCuspFullReflectionEighthHankelSeam.lean`: strict source seam theorem.

## No-go closure

- **Exact killing theorem/mechanism:** open
- **Strongest positive survivor:** open
- **New insight:** rank five separates exactly into previously closed odd rank-two curvature and a new even rank-three eighth-jet determinant.
- **Status:** active paper/Lean conjecture loop

## Log

- 2026-08-27 — created directly in 1-in-progress after corpus audit; D1 selected as hardest source-pure open core.
- 2026-08-27 — exact reflected eighth-jet determinant identity and strict rank-three modular-seam theorem proved in Lean; global D1 continuation remains active.
