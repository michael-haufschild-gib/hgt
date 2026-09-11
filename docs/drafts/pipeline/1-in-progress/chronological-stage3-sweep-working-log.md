# Working log: chronological stage-2 → stage-3 sweep

Goal: formalize unconditionally, in Lean, every proven theorem on every card in
`docs/drafts/pipeline/2-fully-proven/chronological/`, wire into the umbrella, then move the card
to `3-formalized`. No hypotheses, no axioms, no simplifications.

## Card inventory (16) and formal state at sweep start (2026-09-11)

| # | Card | Lean state at start | Outstanding formal obligations |
|---|---|---|---|
| 1 | delayed-moment-obstruction | formalized + audited (219 decls) | verify nothing on card is paper-only; promote |
| 2 | equivariant-recovery | formalized + audited (38 decls) | verify; promote |
| 3 | finite-tail-obstruction | **Lean pending** (weighted Mellin + weighted boundary certificates exist) | whole Hilbert separation / annihilation / critical-zero argument |
| 4 | fusion-spectrum | formalized (FusionCapacity/Heat/Mellin/Divisor, CubicJoin) | n-fold join ≃ S^(2n−1) sphere-homotopy reading |
| 5 | graded-hilbert-defect | formalized + audited (102 + 36) | verify; promote |
| 6 | growing-moment-source | **Lean pending** | bounded array + matched moments + jet + L²/uniform decay |
| 7 | homogeneous-boundary | formalized (66 decls) | Chebyshev optimizer theorem, positive optimal gaps, root-sum formula |
| 8 | monotone-coalescence | formalized + audited (51 + 39) | verify; promote |
| 9 | observation-cusp | formalized + audited | literal 3-variable ideal-quotient presentation; graded dimension formulas |
| 10 | observation-recovery | formalized + audited (9 decls) | verify; promote |
| 11 | observation-repair | formalized + audited (93 decls) | explicit finite Gamma/power-sum formula |
| 12 | path-cochain-reduction | **not formalized** | path independence complex, K/q/J identities, shift iso, base cases, multiplicities |
| 13 | recovery-exponential-rate | **not formalized** | weighted potential theory: support equation, F-functional, weighted Chebyshev rate, equilibrium measure |
| 14 | recovery-shift | formalized (45 decls) | moment identities |
| 15 | recovery-uniform-spectrum | **not formalized** | uniform growth limit + exact spectral disc |
| 16 | weighted-coefficient-duality | formalized (36 decls) | general Chebyshev optimizer, simultaneous coefficient duality, uniqueness |

## Keystone dependency

Cards 7, 13, 15, 16 all reduce to one missing classical input: **weighted Chebyshev
existence / alternation / uniqueness** for the norm
`N_k(R) = sup_{r∈[0,1/4]} W(r)^k |R(r)|`, `W(r) = 1 − √(1−4r)`, on polynomials of degree ≤ k,
with the weight vanishing at the left endpoint. Corpus search (`research`, hybrid + lexical +
`--any`) finds **nothing**: no equioscillation, no best-approximation alternation, no weighted
Chebyshev module anywhere in mathlib or the corpus. So it must be built.

Existing reusable corpus assets for this:
- `ChronologicalTensor/CubicWeightedInterval.lean` — `cubicRadialWeight`, `cubicWeightedIntervalNorm`,
  `cubicHomogeneousRecoveryErrors_interval` (recovery errors = weighted norms on `{natDegree ≤ k+1, coeff k = 1}`).
- `ChronologicalTensor/CubicWeightedProfile.lean` — dehomogenization, edge ratio.
- `ChronologicalTensor/CubicGradedRecovery.lean` — attained positive minimum over normalized residuals
  (`cubicGradedRecoveryGap_attained`, `_positive`).

## Build order

1. `HTGeometry/Approximation/WeightedChebyshev.lean` — general weighted sup-norm on `Icc a b`
   with a continuous nonnegative weight whose positivity set is infinite: norm is attained,
   is a genuine norm on `degree ≤ k`, monic minimizer exists.
2. `.../WeightedChebyshevAlternation.lean` — `best ⇒ k+1 alternating extreme nodes`
   (block/ν-function construction + perturbation), and `alternating ⇒ best` (de la Vallée Poussin),
   hence uniqueness.
3. `.../WeightedChebyshevCoefficient.lean` — Lagrange coefficient duality, all-coefficients-nonzero,
   equality case, uniqueness of the normalized minimizer.
4. Cards 16, 7 close. Then 15 (needs 13's rate), 13 (potential theory), 12, 3, 6, and the
   gap items of 4, 9, 11, 14.

## Progress

- 2026-09-11: inventory taken, keystone identified, corpus searched. Starting step 1.

## Keystone build: `HTGeometry/WeightedMinimax/` (new, general weighted Chebyshev theory)

Nothing of this existed in mathlib or the corpus (searched: `research` hybrid/lexical/`--any` for
equioscillation, alternation, best approximation, weighted Chebyshev — zero hits).

| Leaf | Status | Content |
|---|---|---|
| `Basic.lean` | **builds** | `IsWeight`, `wsup`, attainment, seminorm/norm/`ProperSpace` on `degreeLT ℝ (n+1)`, `coeffSet n j`, `exists_coeffSet_minimizer`, `exists_monicDeg_minimizer` |
| `SignRealization.lean` | **builds** | finite sign realization by induction on the node count (degree = number of sign changes, plus the alternating index chain and the terminal-ray invariant); `step_mono`, `step_mono_lt`, `exists_monotone_enumeration` |
| `Perturbation.lean` | **builds** | `extremeSet`, the improving perturbation `exists_wsup_lt_of_sign_match`, and `exists_sign_mismatch_of_minimizer` |
| `PolyRoots.lean` | **builds** | coefficient signs of `∏(X−r)` with positive roots; `coeff_ne_zero_of_positive_roots` (the Haar property of `{deg ≤ n, coeff j = 0}` on the positive half-line); `eq_prod_X_sub_C_of_monic`; IVT roots from alternation; `exists_sign_realizing_coeffKer` |
| `Alternation.lean` | **builds** | **weighted alternation theorem** `exists_alternating_extreme_chain`: a monic minimizer of degree `n` has `n+1` extreme nodes with alternating sign |
| `Coefficient.lean` | in progress | roots of the minimizer, `coeff_mul_wsup_le` (coefficient duality), `exists_extremeSet_card`, uniqueness, normalized optimizer, root-sum normalization |

Proof architecture of the alternation theorem (the classical greedy/block construction was replaced
by a shorter route): minimality ⟹ no lower-degree sign-matching correction (perturbation) ⟹ by
strict separation in `ℝ^n` the origin lies in the closed convex hull of the signed weighted moment
vectors of the extreme points ⟹ by the corpus's `exists_atomic_of_mem_closure_convexHull`
(`HTGeometry/FiniteAtomicCubature.lean`, Carathéodory in coordinates) the origin is a genuine finite
convex combination ⟹ the finite sign-realization lemma forces at least `n` sign alternations among
those points.

## Promotions (2026-09-11)

`WeightedMinimax` (6 leaves) + `CubicChebyshevOptimizer` all build; 95 new declarations axiom-audited
(only `propext`, `Classical.choice`, `Quot.sound`); all seven wired into `HTGeometry.lean`;
authoritative lint clean for them. `CubicRecoveryMoments` adds 13 more, likewise audited and wired.

Moved to `3-formalized`:

| Card | What closed it |
|---|---|
| weighted-coefficient-duality | new `WeightedMinimax` theory + `CubicChebyshevOptimizer` |
| homogeneous-boundary | same (its one remaining obligation was the optimizer theorem) |
| observation-recovery | already complete: verified all 9 `CubicRecovery` declarations cover every card claim |
| equivariant-recovery | already complete: verified 38 declarations across the four named leaves |
| monotone-coalescence | already complete: verified 39 + 51 declarations, incl. `cubicMonotoneCapacity_unitBall` |
| graded-hilbert-defect | already complete: per-leaf declaration counts re-verified against the card's table (102) |
| delayed-moment-obstruction | already complete: all seven named capstones verified in the 16 `RecoverySurgery` leaves; moved as `-paper` alongside its existing certificate, whose stale `Source` link was fixed |
| recovery-shift | new `CubicRecoveryMoments`: the moment identity `γ_n = (δ_n/δ_0)²`, its recursion, positivity and the `16^(-n)` support bound |

Remaining (8): finite-tail-obstruction, fusion-spectrum, growing-moment-source, observation-cusp,
observation-repair, path-cochain-reduction, recovery-exponential-rate, recovery-uniform-spectrum.

### Next: observation-repair

Only gap is the explicit finite Gamma/power-sum formula
`R_k(s) = Γ(s)[k^(1−s)/(1−s) − Σ_{n=1}^k n^(−s)]` on `0 < Re s < 1`. Existing assets:
`cubicFiniteKernel_factor` (`cubicFiniteKernel k t = (1−e^{−kt})·cubicCuspKernel t`),
`cubicFiniteKernel_converges`, `cubicFiniteKernel_mellin_tendsto`, and
`fusionBoseKernel_mellin`. Plan: split the kernel as
`(1−e^{−kt})/t − Σ_{n=1}^k e^{−nt}` — the second piece is a *finite* sum of scaled Gamma
integrals, needing no Fubini; the first reduces by `mellin_comp_mul_left` to
`mellin ((1−e^{−t})/t) s = Γ(s)/(1−s)`, which is one Fubini over `Ioi 0 × Ioo 0 1` against
`∫_{Ioi 0} t^{s−1}e^{−xt} dt = Γ(s)x^{−s}`.

## Promotions, round 2

| Card | What closed it |
|---|---|
| observation-repair | `CubicRepairGamma` (13 decls): scaled Gamma integral + Fubini reference term ⟹ `cubicFiniteKernel_mellin_gamma` |
| observation-cusp | `CubicCuspPresentation` (25 decls): `cuspEvalHom_range` + `cuspEvalHom_ker = span{W²−V³}`, i.e. the presentation by the first isomorphism theorem, plus `CubicCuspHilbert` (14 decls): graded dimensions and the three Hilbert-series identities as formal power series |

Note on the presentation: mathlib's `HasQuotient R (Ideal R)` instance is **not found** for triple-nested
`Polynomial` rings in this toolchain (`Polynomial (Polynomial (Polynomial ℝ)) ⧸ I` fails to
synthesize; double nesting and `MvPolynomial (Fin 3) ℝ` both work). The presentation is therefore
stated as surjectivity onto `cubicCuspAlgebra` together with the exact kernel, which is the
presentation.

## Remaining 6, with the real obstacle in each

| Card | Obstacle |
|---|---|
| growing-moment-source | whole construction: bounded arrays with matched Möbius prefix and growing odd-moment matching, plus the jet and the `L²([δ,∞))`/uniform decay |
| finite-tail-obstruction | whole construction: the `L²([1,2])` separation, exact discrete annihilation, and the critical-zero obstruction (Hardy is corpus-owned) |
| path-cochain-reduction | whole construction: path independence complexes, the `K`/`q`/`J` identities, the occupation-degree shift isomorphism, base cases, all-degree multiplicities |
| fusion-spectrum | only the sphere-homotopy *interpretation* of arbitrary join powers. The card's own status and the stage-3 certificate both record that the formal Euler chain deliberately avoids it (`fusedCubicReducedEuler_eq n = -1` is proved from actual finite face sets). Formalizing it needs a topological or homological join theory that mathlib does not have |
| recovery-exponential-rate | weighted potential theory: support equation, `F`-functional, equilibrium measure, and the Balogh–Bertola weighted Chebyshev asymptotic |
| recovery-uniform-spectrum | needs the rate constant from the exponential-rate card; the uniform growth bound and the spectral-disc argument are otherwise self-contained Hilbert-space work |

## Round 3: the path-cochain reduction (card 12), phase 1 done

New leaf `HTGeometry/PathIndependenceCochain.lean` — **builds, wired, 25 declarations all
axiom-audited**. It supplies the card's computational core:

* `IsPathFace n σ` (members `< n`, no two adjacent), closed under `erase`; `IsTailSet τ`
  (members `≥ 3`).
* `pathFaceSign_zero`, `pathFaceSign_one`, `pathFaceSign_insert_of_lt`,
  `pathFaceSign_insert_self` — the incidence signs at the two lowest vertices.
* `pathCone` (`K`), `pathTailMap` (`q`), `pathIncl` (`J`) exactly as displayed on the card.
* `pathTailMap_pathIncl` : **`qJ = id`**.
* `pathCoboundary_insert_of_min` : `δf (insert a τ) = f τ − ∑_v sign(τ,v) f (insert a (τ \ v))`
  for `a` below every member of `τ` — the workhorse for the two sign identities.
* `pathTailMap_simplicialCoboundary` : **`qδ = −δq`** on tail sets.
* `simplicialCoboundary_pathIncl` : **`δJ = −Jδ`** on path faces.
* `simplicialCoboundary_pathCone_add` : **`δK + Kδ = id − Jq`** on path faces. Three cases:
  `0 ∈ σ` and `1 ∈ σ` are single-term sums (`Finset.sum_eq_single`), and the remaining case is
  *exactly* the corpus's `simplicialCoboundary_simplicialCone_add` at base vertex `0`, since
  `pathCone` and `simplicialCone F 0` agree on every set missing `1`.

### Corpus assets found (do not rebuild these)

`HTGeometry/SimplicialCochainComplex.lean` already has the reduced simplicial cochain complex of an
arbitrary finite complex in every degree: `faceSign` with all its erase/antisymmetry lemmas,
`simplicialCoboundary` (+ `ₗ`), `δ² = 0`, the occupation grading `cardCochains F c` with
`simplicialCoboundary_mem_cardCochains`, and the complex's cochains as the quotient by
`faceVanishingCochains`, with `complexCoboundaryₗ` and its `δ² = 0`.
`HTGeometry/SimplexConeContraction.lean` has the cone homotopy `δK + Kδ = id` for an arbitrary base
vertex and `fullSimplex_exact`. `HTGeometry/HochsterCohomologyEquiv.lean` has reduced cohomology as
a subquotient (`inducedCocycles`, `inducedCoboundaries`, `inducedReducedCohomology`).

### Phase 2 (card 12, still open)

1. Graded cochain modules of the path complex. Use the corpus's quotient pattern with a
   path-specific kernel `pathVanishing F n := {f | ∀ σ, IsPathFace n σ → f σ = 0}` (a submodule,
   `δ`-stable because faces are erase-closed), graded by intersecting with `cardCochains F j`.
2. Cocycles / coboundaries / reduced cohomology in occupation degree `j`, then the induced maps
   `q` and `J`; the four identities above make them inverse on cohomology with a shift of one in
   occupation degree.
3. The tail relabeling: an order-preserving bijection `{3,…,n−1} → {0,…,n−4}` transporting the
   incidence signs, giving `H̃^(j+1)(Ind P_(n+3)) ≅ H̃^j(Ind P_n)`.
4. Base cases `n = 0, 1, 2` (for `n = 1` use `fullSimplex_exact`), then the all-degree multiplicity
   classification (one class in occupation `j` for `n = 3j` or `n = 3j−1`, none for `n = 3j+1`) and
   the paired trace at `n = 2d−1`.
