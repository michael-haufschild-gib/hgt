# HB mixed-Casimir pole-fill landing

- **ID:** HB-C-A.9x-e
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (HB surviving scalar-normalization producer; map read-only)
- **Statement:** The unique four-Xi pole-fill correction of the literal diagonal triple-Eisenstein source is the mixed four-channel Casimir multiplier below; it has exact leg-separation rank three, equals `2800` at `(P,Q)=(2,5)`, and makes every allowed analytic-family scalar value land on the canonical vertex.

## Goal

Close the surviving HB burden

```text
source-derived corrected canonical four-Xi scalar normalization
  -> C-A.9u balanced landing
  -> negative BM -> left QNM -> HC94 source/clock
  -> horizon-boundary cocycle -> source-global gain equality -> RH.
```

This card attacks the first arrow. It must produce the correction before continuation or
specialization, prove the forced `2800` calibration at an honest absolute-convergence point, and
classify the correction's minimal source-interaction complexity.

## Gates

- [x] 0 → 1  in-progress: corpus/literature audit, source-pure statement, exact attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem package, targeted `lake build`, axiom audit
- [ ] 3 → 4  publication-ready: standalone theorem and Lean certificate

## Frozen conjecture

Put

```text
c(s)   = s(s-1)/2,
A(P,Q) = 2P+Q-1,
C(P,Q) = 2P-Q,
K(P,Q) = c(A(P,Q)) c(Q)^2 c(C(P,Q)).
```

Here `c(s)` is one half of the centered Eisenstein Casimir eigenvalue. The conjecture has four
closed parts.

1. **Mixed-discriminant law.** For `x=2P-1`,

   ```text
   K(P,Q) = Q^2(Q-1)^2/16
            * (x^2-Q^2) * (x^2-(Q-1)^2).
   ```

2. **Exact three-channel law.** Writing `H(Q)=Q^2(Q-1)^2/16`,

   ```text
   K(P,Q) = x^4 H(Q)
            - x^2 H(Q)(Q^2+(Q-1)^2)
            + H(Q)Q^2(Q-1)^2.
   ```

   No sum of at most two arbitrary separated terms `f_i(P)g_i(Q)` agrees with `K` throughout the
   strict unfolding chamber `1 < Re(P)` and `2 Re(P) < Re(Q)`. Thus its leg-separation rank is
   exactly three.

3. **Forced calibration.** `K(2,5)=2800` (and `K(2,2)=10`, recovering the earlier independent
   audit point).

4. **Corrected source landing.** Multiplying the literal `(2,5)` unfolded source, or any allowed
   analytic-family regularized value, by `K(2,5)` gives the canonical four-Xi scalar vertex.
   Applying the literal C-A.9u Bochner coefficient then gives the canonical balanced spin-two
   vertex.

## Attack and hostile-audit record

- Corpus search used `scripts/formal_tools.py research` for pole filling, mixed Casimir,
  factorization, actual unfolded source, and four-Xi normalization. Existing corpus proves only
  fixed ratios `10`, `2800`, the literal-source no-go, and C-A.9u residual reduction. It contains no
  generic mixed multiplier, source-channel decomposition, or rank-two obstruction.
- Literature through 2026-08-29 contains Zagier's regularized triple-Eisenstein four-Xi product.
  That makes the generic four-Xi identity a known bridge, not the novelty claim. Searches found no
  source-side mixed-Casimir pole-fill operator or exact separation-rank classification.
- Failed candidate: claim the four-Xi product itself as new. Rejected because Zagier already gives
  it.
- Pivoted candidate: rule out only one legwise product `f(P)g(Q)`. Strengthened because the exact
  polynomial exposes three separated channels and supports a sharp rank classification.

## Paper proof `[PROVED HERE]`

- `c(s)` is half the centered Casimir eigenvalue by
  `thetaCuspHawkingEisensteinGeometricEigenvalue_centered`.
- Expanding the four factors of `K`, pairing `A(A-1)` with `C(C-1)`, gives the two mixed
  discriminants. Expanding them gives the displayed three-channel law.
- The three-channel law proves separation rank at most three.
- Any two-channel separated representation makes every `3 x 3` evaluation determinant vanish:
  each evaluation matrix is a sum of two rank-one matrices. Evaluate at `x=2,3,4` (that is,
  `P=3/2,2,5/2`) and `Q=6,7,8`; all nine points lie in the strict chamber. The three-channel
  formula factors this matrix as

  ```text
  V * C * diag(H(6),H(7),H(8)),
  V rows = (x^4,x^2,1),
  C columns = (1,-(Q^2+(Q-1)^2),Q^2(Q-1)^2).
  ```

  Here the squared coordinates are `4,9,16`, so `det(V)=-420`. The three columns of `C` are
  `(1,-61,900)`, `(1,-85,1764)`, `(1,-113,3136)` and `det(C)=-8736`. Finally
  `H(6)H(7)H(8) != 0`. Thus the determinant is nonzero, contradicting every two-channel
  representation. Together with the explicit upper decomposition, separation rank is exactly
  three.
- Direct factor evaluation gives `K(2,5)=28*10^2*1=2800`.
- Existing source theorem gives `canonical=2800*literalSource`, while boundary rigidity makes every
  allowed analytic-family value equal that source. Substitute the forced multiplier.

## No-go closure

- **Exact killing theorem/mechanism:** Lean theorem
  `no_d4BMTwoChannelLegwisePoleFillNormalization`: no rank-at-most-two separated external-leg
  correction equals the forced multiplier on the full strict unfolding chamber.
- **Strongest positive survivor:** Exact rank-three mixed-Casimir decomposition and corrected
  canonical scalar and C-A.9u balanced landing at `(2,5)`.
- **New insight:** HB pole filling is neither an external-leg normalization nor a two-channel
  boundary repair. The smallest surviving source correction has three interaction channels and is
  forced by the four intermediate Casimir eigenvalues.
- **Status:** Formalized in
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinMixedCasimirPoleFillLanding`.
  Targeted module build passes. Axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`. Umbrella import is wired. Global lint's remaining unreachable-module errors name
  unrelated concurrent modules; this module is not among them.

## Log

- 2026-08-29 — created in 1-in-progress after known Zagier-identity candidate was rejected and the
  mixed-Casimir rank-three conjecture survived hostile audit.
- 2026-08-29 — `[PROVED HERE]`: exact rank-three factorization/no-go, forced calibration, unique
  corrected scalar landing; scratch Lean compile green.
- 2026-08-30 — Lean formalization complete. Targeted `lake build` green; standard-axiom audit green;
  imported by `GaloisForLFunctions.RHTower`.
- 2026-08-30 — extended through C-A.9u: Lean theorems
  `d4BM_mixedCasimirCorrectedActualUnfoldedSource_balanced_eq_canonical` and
  `d4BM_twoFiveMixedCasimirCorrectedBalancedValue_eq_canonical`; targeted rebuild and axiom audit
  green.
