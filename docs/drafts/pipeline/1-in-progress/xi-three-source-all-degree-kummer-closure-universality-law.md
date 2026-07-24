# Xi three-source all-degree Kummer closure universality law

- **ID:** xi-three-source-all-degree-kummer-closure-universality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of differentiated-Xi, Hedenmalm, and differentiated
  theta-cusp Kummer collision/completion theorems
- **Statement:** A common analytic Kummer cover of any one of the three source pairs at any one
  nontrivial degree forces common covers of every nontrivial degree for all three source pairs.

## Goal

Identify the source- and degree-independent phase behind three independently formalized Kummer
interfaces:

1. `xi` with `deriv xi` on the right half-plane;
2. `XiC` with `XiC + I * deriv XiC` on the centered upper half-plane;
3. the theta-cusp Fourier--Laplace source with its derivative on its right-zero band.

The result must transfer existence across different domains, different second sources, and
arbitrary output degree rather than restating one fixed-degree RH criterion.

## Gates

- [x] 0 → 1 in-progress: fresh symbol-graph edge, complete source read, corpus research search,
  source-pure statement
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean checks and umbrella verification
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `riemannHypothesis_of_xiDerivativeCommonKummerRootRightHalf`
- `riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf`
- `riemannHypothesis_of_thetaCuspDerivativeCommonKummerRootRightZeroBand`
- `xiDerivativeCommonKummerRootRightHalf_of_rh`
- `xiHedenmalmCommonKummerRootUpperHalf_of_rh`
- `thetaCuspDerivativeCommonKummerRootRightZeroBand_of_rh`

## Proof

**[PROVED HERE]** Fix input degrees `dXi`, `dH`, and `dTheta`, all greater than one. Assume at
least one of the corresponding three common-root interfaces is inhabited. The matching collision
theorem yields RH, regardless of which source supplied the witness.

Now fix any output degree `e > 1`. In particular `e ≠ 0`. Under RH, the differentiated-Xi
completion theorem constructs common degree-`e` roots of `xi` and `deriv xi` on the right
half-plane. The Hedenmalm completion theorem constructs common degree-`e` roots of `XiC` and its
Hedenmalm source on the centered upper half-plane. The theta completion theorem constructs common
degree-`e` roots of the theta-cusp Fourier--Laplace source and its derivative on the right-zero
band. Since `e` was arbitrary, every nontrivial output degree is simultaneously inhabited in all
three geometries. ∎

## Strict gain over corpus endpoints

Existing theorems close one source and one degree through RH. The new law erases both choices:
one cover can be supplied by any source at any nontrivial degree, while the conclusion changes
domain, changes second observable, and freely changes degree. This is a genuine transfer law
rather than a conjunction of unchanged endpoint statements.

## Lean formalization

Dependency-safe terminal halves:

- `anyKummerCollision_allDifferentiatedSourceCoversUniversality` in
  `GaloisForLFunctions.RHTower.XiDerivativeKummerRootRH`;
- `anyKummerCollision_allHedenmalmSourceCoversUniversality` in
  `GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH`.

Together their identical antecedent yields all three conclusion families. Both modules are
already imported by `GaloisForLFunctions/RHTower.lean`.

Exact verification:

- `lake env lean GaloisForLFunctions/RHTower/XiDerivativeKummerRootRH.lean`
- `lake env lean GaloisForLFunctions/RHTower/XiHedenmalmKummerRootRH.lean`

Both passed without warnings.

## Novelty audit

Post-proof searches found derivative-zero RH reformulations, de Branges spaces attached to Xi,
theta/Laplace models, and unrelated classical Kummer functions and varieties. They did not find
an all-degree transfer theorem between common analytic roots of the three source pairs used here.
Relevant comparison points:

- Sondow--Dumitrescu, “A monotonicity property of Riemann's xi function and a reformulation of the
  Riemann Hypothesis”: `https://arxiv.org/abs/1005.1104`
- Badonova, “On a de Branges space related to the Riemann zeta function”:
  `https://doi.org/10.18287/2541-7525-2024-30-2-7-11`
- de Branges, “The Riemann Hypothesis for the Vibrating String”:
  `https://www.math.purdue.edu/~branges/vibrating-string.pdf`

Novelty remains a negative-search conclusion, not a claim of bibliographic completeness.

## Log

- 2026-07-23 — generated after reading the post-LAW438 derivative/Hedenmalm terminal edge and the
  theta completion theorem in the derivative module.
- 2026-07-23 — corpus research found the six directional component theorems but no all-source,
  all-degree closure.
- 2026-07-23 — dependency-closed proof completed before Lean implementation and literature search.
- 2026-07-23 — dependency-safe halves formalized in the two terminal completion modules; both
  exact-file checks passed and existing RHTower umbrella wiring retained.
- 2026-07-23 — post-proof literature audit found no exact or equivalent law.
