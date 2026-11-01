# Hodge Theory without Varieties over ℤ (HWV)

Namespace `GaloisForLFunctions.HodgeTheoryWithoutVarieties`; umbrella `HodgeTheoryWithoutVarieties.lean`;
11 modules. In the review this field was called *the arithmetic Kähler package*. Everything is
unconditional. Theorems named `riemannHypothesis_iff_*` are equivalences and are not proofs of RH.

## 1. Motivation

Every positivity producer in the corpus has one of three types, and each type has a proved limit.

- **Estimates** stop at the detection edge. The universal regime of the complete Weil family ends at
  overlap `(log N)^{1/19}`. A statement proved without zero information also holds for data with
  off-line zeros, so it cannot cross their edge (EHT).
- **Counts** stop short of square-root precision.
- **Selectors** separate `ζ` from its twins, but each is a margin on a partial form.

A fourth type proved Hodge–Riemann relations where no variety exists:
- McMullen for simple polytopes;
- Adiprasito–Huh–Katz for matroids;
- Elias–Williamson for Soergel bimodules;
- Garland's method for buildings.

These proofs share one shape. There is a self-similar family of finite-dimensional quadratic forms
with a Kähler class. Local Hodge–Riemann on stars or links gives hard Lefschetz, and a deformation
from a base point where Hodge–Riemann is known transports the signature. No step is an estimate
against a vanishing ground energy.

HWV builds this package for the divisibility–successor complex of `[1, N]`:
- Weil's form is the intersection form;
- the pole packet is the Kähler class;
- `v₁^⊥` is the primitive part.

RH is Hodge–Riemann on the primitive part at RH-complete overlap. The programme asks which parts of
the package exist over `ℤ`, proves them, and proves where the package needs input it does not have.

The answer is sharp. The package exists in large part:
- the complex is self-similar, since stars are lower horizons;
- the counterterm is the boundary flux, and the divisor identity selects `Λ`;
- deep stars are Hodge–Riemann with margin `log d`;
- deformation needs hard Lefschetz only on the positive locus;
- the gluing over the nerve is an exact Möbius formula.

It fails at exactly one place. Local positivity must be glued across the shallow stars and the
coprime pairs. The gluing signs are those of the Möbius function, whose signed sum is the Euler
characteristic of the nerve and equals the Mertens function. Hard Lefschetz along the overlap flow
is RH.

## 2. Objects

Conventions: forms are real symmetric matrices on a finite index set; primitive means `x ⬝ᵥ v = 0`;
Weil's sign convention, Hodge–Riemann = `W ≥ 0` on primitive vectors.

| Object | Lean | Meaning |
|---|---|---|
| Kähler package | `HodgeRiemann`, `StrictHodgeRiemann`, `HardLefschetz` | `W ≥ 0` on `v^⊥`; `W > 0` on `v^⊥ ∖ 0`; `W` nondegenerate on `v^⊥` |
| Weighted dilation complex | `dilationForm`, `dilationEnergy`, `degreeDiagonal`, `inDegree`, `outDegree` | `P^λ_N`, its Laplacian `J^λ_N`, degrees `in(n) = (λ ∗ 1)(n)`, `out(M) = Σ_{k≤M} λ(k)/k` |
| Star of `d` | `starRestrict`, `starPullback`, `starEmbed`, `starPull` | multiples of `d`; identified with horizon `⌊N/d⌋` |
| Boundary flux | `starFlux` | `(λ ∗ 1)(dm) − (λ ∗ 1)(m)`: weight entering the star at `dm` |
| Self-similar counterterm | `SelfSimilarFlux` | flux into every star constant along the star |
| Renormalized prime form | `renormalizedPrimeForm` | `(log N − γ)|x|² − P_N(x)` |
| Star resolution | `starOverlap` | `c' = c⌊N/d⌋/N`, the overlap at which the star of `d` lives |
| Kähler class of the complete family | `poleClass` | the pole conductor `v₁` as a function on the horizon |
| Liouville property | `LiouvilleAt` | primitive zero modes of a hyperplane-positive form have zero pole defect |
| Links | `TowerNeighbor`, `DilationAdj`, `linkGraph` | neighbours of `n`; adjacency by prime-power ratio |
| Nerve of the star cover | `squarefreeNerve`, `nerveEulerChar` | sets of primes with product `≤ N`; signed face count |
| Euler-product tower | `towerMass`, `towerWeight`, `towerEnergy`, `valuationStep`, `pvar` | truncated geometric tower, its Dirichlet form, variance |
| Depth constant | `depthConstant` | `C₀ = γ + log 4 + 4` |
| External | RAPT `completeWeilMatrix`, `completeWeilEnergy`, `poleDefect`, `atomicWeilForm`; EHT `PositiveAt`, `HyperplanePositiveAt`, `Admissible`; ACoT `jumpEnergy`, `mertensDiagonal`, `coupling`, `lap` | the forms the package is built on |

## 3. Language

- **Kähler package**, **primitive**, **HR / strict HR / HL**: as in §2.
- **Lefschetz path**: a continuous family of packages over a connected parameter space. It is
  **crossing-free** on its HR locus if HL holds wherever HR holds.
- **Base point**: a parameter where HR is known.
- **Star** of `d`: the multiples of `d`; its **depth** is `d`. **Deep** stars have `d` large compared
  with the overlap; **shallow** stars have `d ≲ c`.
- **Link** of `n`: its dilation neighbours. **Tower**: the neighbours along one prime.
- **Boundary flux**: weight entering a star from outside. **Self-similar counterterm**: constant flux.
- **Gluing**: the part of a form that the star restrictions do not see. Here it is the coprime part
  together with the Möbius-signed overlaps of the stars.
- **Nerve**: the simplicial complex of sets of primes whose stars meet.
- **Harmonic packet**: a primitive zero mode. **Liouville property**: harmonic packets are trivial.
- **Edge-valid**: an identity, induction or integer invariant, valid at every resolution.

## 4. Mechanisms

**A. Kähler packages** (`TheKahlerPackage`).
1. *Strictness.* HR ∧ HL ⇔ strict HR (`strictHodgeRiemann_iff`). A primitive vector of zero energy
   for a form that is `≥ 0` on the primitive part pairs to zero with every primitive vector
   (`bil_eq_zero_of_hodgeRiemann`).
2. *Transport.* The HR locus of a continuous family is closed (`isClosed_setOf_hodgeRiemann`). The
   strict HR locus is open, because the primitive unit sphere is compact
   (`isOpen_setOf_strictHodgeRiemann`). So on a preconnected parameter space, HR at one point and HL
   on the HR locus give HR everywhere (`hodgeRiemann_transport`, `hodgeRiemann_transport_on`). HL
   is needed only where HR already holds.
3. *Crossing.* A family that loses HR has a parameter with HR and without HL
   (`exists_crossing_of_hodgeRiemann_of_not`).
4. *Hodge index.* HR on a hyperplane means `−W` has at most one positive square
   (`isHyperbolic_neg_of_hodgeRiemann`).
5. *Lefschetz step.* Adding one atom is a Schur complement (mathlib `Matrix.PosDef.fromBlocks₁₁`).

**B. Self-similarity** (`StarsAreLowerHorizons`, `StarsOfTheCompleteWeilFamily`).
6. *Polarization for every weight.* `P^λ = degree diagonal − J^λ`, with in-degree `λ ∗ 1`
   (`dilationForm_eq`).
7. *Stars are lower horizons.* `P^λ_N(F·1_{dℕ}) = (1/d) P^λ_{⌊N/d⌋}(F(d·))` for every weight
   (`dilationForm_starRestrict`). In Weil coordinates the prime kernel depends only on ratios
   (`weilPrimeKernel_mul_mul`, `atomicWeilForm_starRestrict`).
8. *The counterterm is the boundary flux.* The degree diagonal and the Laplacian of a star pick up
   the same flux `in(dm) − in(m)` (`degreeDiagonal_starRestrict`, `dilationEnergy_starRestrict`).
   For `Λ` the flux is `log d` at every vertex (`starFlux_vonMangoldt`), so the renormalized prime
   form on the star is the renormalized form at `⌊N/d⌋` plus `(log N − log⌊N/d⌋)` times the mass
   (`renormalizedPrimeForm_starRestrict`). The running counterterm `log N − γ` pays exactly the
   flux.
9. *Stars of the complete family.* Weil's form is translation invariant for every weight. The
   atoms on the star of `d` are the atoms of horizon `⌊N/d⌋` moved by `log d`, so the star
   embedding is an isometry from the family at `(c⌊N/d⌋/N, ⌊N/d⌋)` to the family at `(c, N)`
   (`completeWeilEnergy_starEmbed`, `weilQuadTw_atomicTest_starRestrict`). Positivity descends
   to stars, on all vectors and on the primitive part (`positiveAt_div`, `twinPositiveAt_div`,
   `hyperplanePositiveAt_div`).

**C. Local Hodge–Riemann** (`TheDepthOfAStarIsItsEnergy`, `StarsOfTheCompleteWeilFamily`).
10. *Depth law.* On the star of `d`, at every horizon, `R_N ≥ (log d − C₀)|x|²`
    (`renormalizedPrimeForm_starRestrict_ge`). Asymptotically the bound is `(log d − ε)|x|²`, and
    `(log d + 2 log 2 − ε)|x|²` on primitive pullbacks
    (`eventually_renormalizedPrimeForm_starRestrict_ge`,
    `eventually_renormalizedPrimeForm_starRestrict_ge_primitive`). Depth costs `log d`.
11. *Deep stars sink into the universal regime.* For the tilted spline, every star with
    `⌊N/d⌋ ≥ M₀` and `1 ≤ c⌊N/d⌋/N < (log ⌊N/d⌋)^α` is positive, at every resolution `(c, N)`
    (`exists_star_positive_tiltedUnitSpline`).
12. *Depth and conductor are dual.* RAPT's completed conductor energy is
    `E_m(c) = φ(m)⁻¹ Σ_{d ∣ m} μ(m/d) d E(c/d)`: the conductor-`m` mode is governed by the pole
    energy at the star overlaps `c/d` of the divisors of `m`. Stars and conductors degenerate in the
    same order, by `c ↦ c/d`.

**D. Gluing** (`TheMoebiusGluingOfStars`, `TheNerveOfTheStarCover`, `TheLinksSplitIntoTowers`).
13. *Möbius gluing.* For every form on `[1, N]`,
    `Q(x) = Q_cop(x) + Σ_{2≤d≤N} (−μ(d)) Q(x·1_{dℕ})` (`quadratic_moebius_gluing`). For the
    complete family each star term is the family at the star resolution
    (`completeWeilEnergy_moebius_gluing`).
14. *The prime form is a cone glued to its stars.* Coprime pairs of the prime kernel all contain
    the vertex `1` (`weilPrimeKernel_eq_zero_of_coprime`), so
    `P_N(x) = 2x₁ Σ_k P(1,k)x_k + Σ_{d≥2}(−μ(d)) P_{⌊N/d⌋}(x(d·))`
    (`atomicWeilForm_moebius_recursion`). This is an exact recursion over the nerve.
15. *The nerve.* A set of primes has a common star vertex iff its product is `≤ N`
    (`exists_common_star_iff`). The signed face count of the nerve is the Mertens function
    (`nerveEulerChar_eq_mertens`). RH is the half-power growth bound on it
    (`riemannHypothesis_iff_nerveEulerChar`), and unconditionally it is `Ω±(√N)`
    (`nerveEulerChar_omega_pm_sqrt`).
16. *Links split into towers.* Neighbours of `n` on two distinct prime towers are never adjacent
    (`not_dilationAdj_of_towerNeighbor`), while each tower is a clique
    (`dilationAdj_of_towerNeighbor_same`). Every link is disconnected
    (`not_preconnected_linkGraph_of_pos`). Over a curve, positions are degrees and the links are
    complete (`degreeLink_adj`).

**E. Künneth** (`TheEulerProductTensorizes`).
17. *Exact tensorization.* The two-factor Efron–Stein inequality (`pvar_prod_le`) gives the Künneth
    step for spectral gaps: Poincaré constants `λ` on two factors give `λ` on the product
    (`gap_prod_ge`). Functions of one coordinate show that the product gap is at most each factor
    gap (`pvar_prod_comp_fst`).
18. *The tower gap.* On the box `0 ≤ a ≤ A` with weights `r^a/Z`, the tower energy dominates
    `ℓ Z` times the variance term by term (`towerEnergy_ge`). The valuation step attains this
    (`towerEnergy_valuationStep`), so the gap is exactly `ℓ Z`. With `ℓ = log p` and
    `r = p^{−σ}` it tends to `log p/(1 − p^{−σ})`. For the Euler-product measure the gap of the
    dilation complex is therefore `min_p log p/(1 − p^{−σ})`. It is attained at `p = 2` and equals
    `2 log 2` at `σ = 1`, which is RAPT's horizon gap.

**F. Selection** (`TheDivisorIdentitySelects`).
19. *Classification.* A counterterm is self-similar iff the weight vanishes off prime powers and is
    constant on every tower (`selfSimilarFlux_iff`). The mechanism is the one-prime step: the new
    divisors of `pn` contain the single prime power `p^{v_p(n)+1}` (`inDegree_mul_prime_sub`).
20. *Twists.* `Λω`, with `ω` completely multiplicative and `ω(p) ≠ 0`, is self-similar iff `ω ≡ 1`
    on primes (`selfSimilarFlux_twist_iff`). Every prime flip and the Liouville twist break it.

**G. Liouville and the Lefschetz operator** (`TheLiouvilleProperty`, `TheLefschetzCandidates`).
21. *Dilation Liouville.* Zero dilation energy forces a constant packet
    (`eq_of_dilationEnergy_eq_zero`). A primitive packet with zero energy vanishes
    (`eq_zero_of_dilationEnergy_eq_zero_of_primitive`, `eq_zero_of_poleDefect_eq_zero_of_primitive`).
22. *Liouville is hard Lefschetz* (`liouvilleAt_iff_hardLefschetz`).
23. *Transport along the overlap flow* (`hyperplanePositiveAt_of_liouville`): the complete family is
    a continuous Kähler family (`continuousOn_completeWeilMatrix`).
24. *Under RH there are no zero modes.* Atomic tests are faithful
    (`eq_zero_of_atomicTest_eq_zero`), and Weil's form is positive definite under RH
    (`completeWeilEnergy_pos_of_riemannHypothesis`, `hardLefschetz_of_riemannHypothesis`).

## 5. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| **Links.** What are the links of the arithmetic complex, and which satisfy local HR? | The simplicial links split into prime-tower cliques, so Garland and trickle-down cannot start (ALG: connectivity is necessary). The correct local objects are **stars**. They are exact copies of lower horizons, with the counterterm shifted by the boundary flux. They satisfy local HR unconditionally with margin `log d − C₀`, and for the complete family once they sink into the universal regime. Finite sieves (RAPT, one positive direction) and conductor sectors (RAPT repayment) are the dual local objects, by depth–conductor duality. Single towers cannot be links: one prime tower already sees every right zero (ACS). | `not_preconnected_linkGraph_of_pos`, `atomicWeilForm_starRestrict`, `renormalizedPrimeForm_starRestrict`, `renormalizedPrimeForm_starRestrict_ge`, `exists_star_positive_tiltedUnitSpline` |
| **Lefschetz operator.** Dilation generator, overlap derivative or coupling Laplacian? | **Dilation**: HL is free (an isometric embedding of a lower resolution). It transports positivity downward and creates none: every deep star is positive, yet without RH the whole form fails infinitely often. **Overlap flow**: HL on its HR locus over `[1, 2(log N)^β]` is exactly RH, and without RH primitive zero modes appear infinitely often. **Coupling Laplacian**: HL is free for `t > 0` and the index is `κ(K_ζ)` throughout, but the base point `t = 0` is the zero form. No candidate is a free Lefschetz operator with an HR base point. | `dilation_transports_downward`, `not_rh_gluing_failure`, `riemannHypothesis_iff_liouville_along_the_overlap_flow`, `frequently_exists_primitive_zero_mode_of_not_rh`, `couplingLaplacian_transports_the_index` |
| **Shell degree.** Is there a Lefschetz-type decomposition paying it jointly with the pole? | Yes on every finite conductor sector at fixed overlap. RAPT's repayment writes the shell-completed conductor energy as `(2/(Mφ(m))) Σ_{(a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂|²`, graded by the coprime shell index `a` and positive term by term. It degenerates, `E_m(c) → 0`, in the order of the conductors, and by depth–conductor duality in the order of the stars. Joint payment uniform in the conductor is the open estimate (review Σ-3). Structurally the problem sits on shallow stars and low conductors, `d, m ≲ c`. | RAPT `hasSum_completedConductorEnergy`, `tendsto_completedConductorEnergy_atTop`; HWV §4.12 |
| **Base point and path.** Can the universal regime be the base point and the overlap flow the path? | Yes, and the mechanism is exact. The universal regime gives positive definiteness at overlap `1`. Transport needs HL only on the HR locus. The resulting criterion, the Liouville property along the overlap flow, is equivalent to RH. | `hodgeRiemann_transport_on`, `hyperplanePositiveAt_of_liouville`, `riemannHypothesis_iff_liouville_along_the_overlap_flow` |
| **Function-field model.** Buildings, Ramanujan complexes, or Frobenius on commensurable towers? | Frobenius on commensurable towers: the degree lattice of the curve. There the links are complete, stars are translates, and the selection identity holds, since `Λ_C ∗ 1 = deg · log q` is additive. The flow stabilizes at window `2g` (EHT, ACS Pontryagin law). Garland-type local-to-global statements concern spectral gaps of Laplacians. Their exact arithmetic counterpart, the Euler-product Künneth step, gives the gap `2 log 2` of the dilation Laplacian, not Weil positivity. Buildings are therefore not the model of the Hodge index. | `degreeLink_adj`, `gap_prod_ge`, `towerEnergy_valuationStep`; EHT `windowEdge_le_card`; ACS `pontryagin_law_curve` |
| **Liouville test.** Must a primitive zero mode at the first failure have vanishing jump and affine energies? | Vanishing jump energy alone forces it to be zero, so the Liouville property is exactly HL on the positive locus. Along the overlap flow it is equivalent to RH, and without RH it fails infinitely often. The positive survivor is ACoT's localization: primitive zero modes have bounded jump energy and lie in a finite conductor sector. | `liouvilleAt_iff_hardLefschetz`, `riemannHypothesis_iff_liouville_along_the_overlap_flow`, `frequently_exists_primitive_zero_mode_of_not_rh`; ACoT `jumpEnergy_add_half_affine_le_of_nonpos` |

## 6. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Strictness; transport with HL on the HR locus; crossing | `strictHodgeRiemann_iff`, `hodgeRiemann_transport_on`, `exists_crossing_of_hodgeRiemann_of_not` | proved |
| Polarization for every weight | `dilationForm_eq` | proved |
| Stars are lower horizons (prime form, Weil coordinates) | `dilationForm_starRestrict`, `atomicWeilForm_starRestrict` | proved |
| The counterterm is the boundary flux; renormalized star law | `starFlux_vonMangoldt`, `jumpEnergy_starRestrict`, `mertensDiagonal_starRestrict`, `renormalizedPrimeForm_starRestrict` | proved |
| Stars of the complete family; positivity descends | `completeWeilEnergy_starEmbed`, `positiveAt_div`, `hyperplanePositiveAt_div`, `twinPositiveAt_div` | proved |
| Depth law: local HR with margin `log d` | `renormalizedPrimeForm_starRestrict_ge`, `eventually_renormalizedPrimeForm_starRestrict_ge_primitive` | proved |
| Local HR on deep stars of the complete family | `exists_star_positive_tiltedUnitSpline` | proved |
| Self-similar counterterms classified; only `ζ` among twists | `selfSimilarFlux_iff`, `selfSimilarFlux_twist_iff` | proved |
| Links split into towers | `not_dilationAdj_of_towerNeighbor`, `not_preconnected_linkGraph_of_pos` | proved |
| Möbius gluing; the prime form is a cone glued to its stars | `quadratic_moebius_gluing`, `atomicWeilForm_moebius_recursion`, `completeWeilEnergy_moebius_gluing` | proved |
| Nerve: Euler characteristic = Mertens; RH ⇔ half-power growth; `Ω±(√N)` | `nerveEulerChar_eq_mertens`, `riemannHypothesis_iff_nerveEulerChar`, `nerveEulerChar_omega_pm_sqrt` | proved; equivalence |
| Künneth step for gaps; sharp tower gap | `gap_prod_ge`, `towerEnergy_ge`, `towerEnergy_valuationStep` | proved |
| Liouville = HL; RH ⇔ Liouville along the overlap flow | `liouvilleAt_iff_hardLefschetz`, `riemannHypothesis_iff_liouville_along_the_overlap_flow` | proved; equivalence |
| Lefschetz trichotomy | `not_rh_gluing_failure`, `frequently_exists_primitive_zero_mode_of_not_rh`, `couplingLaplacian_transports_the_index` | proved |

## 7. Tools

**Developed.**
- Kähler-package calculus on real symmetric matrices: strictness, open/closed loci, compactness of
  the primitive sphere, transport and crossing on preconnected sets, the Hodge index bridge.
- Weighted dilation complexes for arbitrary weights: degree diagonals, Laplacians, polarization,
  the target fibration by divisor antidiagonals.
- Star calculus: restriction and pullback, sums over multiples (`sum_Icc_star`,
  `sum_dilationPairs_star`), boundary flux, star embedding of Euclidean horizon vectors
  (`starEmbed`, `starPull`, `starEmbed_starPull`), star overlap.
- The complete Weil family as a continuous Kähler family (`poleClass`,
  `completeWeilEnergy_eq_qf`, `hyperplanePositiveAt_iff_hodgeRiemann`,
  `continuousOn_completeWeilMatrix`).
- Faithfulness of atomic tests and strict positivity under RH.
- Möbius gluing of quadratic forms over common divisors (`sum_moebius_common_divisors`).
- Nerve calculus: faces as squarefree integers, Möbius on products of distinct primes.
- Link graphs and tower invariants along walks (`towerNeighbor_of_walk`).
- Variance calculus for finite probability weights: pair form, convexity, total variance,
  two-factor Efron–Stein; truncated geometric towers.

**To build.**
- A gluing inequality for the coprime part `W_cop` against the Möbius-signed star terms, with a
  constant independent of `N`.
- The affine (successor) analogue of the boundary flux for the non-ratio matrix, and its pairing
  with the coprime gluing.
- The exact layered Künneth decomposition at the horizon: valuation layers `p^a` as lower horizons
  of the `p`-deleted complex, coupled only through `p`-towers.

## 8. Open research topics

1. **The coprime gluing form.** In the Möbius formula every star term is a lower-resolution family,
   and the deep ones are positive. Is the coprime part of the complete form at `(c, N)` controlled
   by the stars of depth `≤ c`? A positive answer with level-independent constants is the
   inductive step that the package lacks.
2. **Shallow stars.** Local HR with an explicit margin on stars of depth `d ≲ c`, i.e. for the
   low-conductor band of review Σ-4.
3. **Signed nerve.** Is there a weighting of the faces of the nerve for which the gluing signs
   become nonnegative? Such a weighting is a positive refinement of the Mertens function, and must
   be RH-hard in view of `riemannHypothesis_iff_nerveEulerChar`.
4. **Successor flux.** Successor edges cross star boundaries, except those with shift divisible by
   `d`. Locate the shell degree in the flux between stars, and compare it with the dilation flux
   `log d`, which the counterterm pays exactly.

## 9. Traps

| Trap | Truth |
|---|---|
| Local HR on every star gives global HR | Deep stars are positive unconditionally; without RH the whole form still fails infinitely often (`not_rh_gluing_failure`) |
| Trickle-down applies to the dilation complex | Its links are disconnected (`not_preconnected_linkGraph_of_pos`); ALG shows connectivity is necessary |
| Local forms can be summed over the star cover | The gluing is alternating, with signs `−μ(d)`; the signed face count is the Mertens function |
| Dilation is a Lefschetz operator | It is an isometric embedding of lower resolutions; it transports positivity downward and creates none |
| HL along the overlap flow is softer than RH | Needed only on the HR locus, and still equivalent to RH |
| Self-similarity of stars is arithmetic | Geometric self-similarity holds for every weight (`twinPositiveAt_div`); only the counterterm flux selects |
| A self-similar counterterm forces `Λ` | It forces a generalized von Mangoldt weight, constant on towers; the archimedean matching fixes the weights `λ(p)` |
| The Liouville property asks for two vanishing energies | Zero jump energy alone kills a primitive vector; Liouville is HL |
| An exact Künneth gap proves positivity | It gives the gap of the dilation Laplacian, `2 log 2`, below the pole; the RH content is in the successor and archimedean parts at growing overlap |
| The topology of the nerve is softer | Its Euler characteristic is the Mertens function: half-power growth is RH |

## 10. Context

| Neighbour | Interface |
|---|---|
| EdgeHodgeTheory | edges, crossings, continuity in the overlap, positivity descending to lower horizons at fixed width, curve window edge |
| ArithmeticCouplingTheory | dilation pairs, jump energy and Mertens diagonal; localization of nonpositive packets; coupling homotopy |
| RenormalizedArithmeticPotentialTheory | complete Weil matrix, pole defect and its kernel, spectrum ends, pole top, gap `2 log 2`, completed conductor energies |
| RenormalizedIntersectionTheory | Hodge index at logarithmic overlap (the receiver of the Liouville equivalence) |
| CriticalArithmeticCorrelationTheory | positive definiteness on the power-log window (the base point) |
| ArithmeticLorentzianGeometry | quadratic and bilinear forms, hyperbolicity, trickle-down and its necessary connectivity |
| ArithmeticCastelnuovoSeveri | faithfulness of translates, Weil positive definiteness under RH, curve data |
| SpacingScaleHarmonicAnalysis | Weil's quadratic form and translation invariance for every weight |
| RHTower | Littlewood's Mertens criterion and the `Ω±(√x)` theorem for the Mertens function |

HWV takes the edge (EHT), the packet identity (ACoT) and the renormalized spectrum (RAPT), and
asks what a Kähler-package proof would need from them. Its new structure is the star:
- a self-similarity on the vertex side, dual to RAPT's conductors;
- the counterterm read as a flux;
- an exact gluing over a nerve whose topology is the Mertens function.

## 11. Success criteria

| Criterion | Status |
|---|---|
| Exactness: identities and inductions valid at the edge | Star laws, flux, Möbius gluing, nerve, transport and Liouville equivalence are identities or equivalences |
| Local HR | Proved on deep stars (prime form with margin `log d − C₀`; complete family in the universal regime); open on shallow stars |
| Arithmetic hard Lefschetz | Classified: free for dilation and coupling Laplacian, RH for the overlap flow |
| Level independence | Exact for the Euler-product Künneth step (gap `2 log 2`); the gluing step has no level-independent bound |
| Selectivity through `Λ ∗ 1 = log` | Self-similar counterterms classified; `ζ` is the only self-similar twist |
| Compatibility with the no-gos | Local forms do not sum (alternating Möbius gluing); single towers are not links |
| Calibration over `𝔽_q` | Commensurable degree lattice: complete links, trivial flow (EHT, ACS) |

## 12. What counts as a contribution

A contribution proves, in Lean and without hypotheses, one of the following:
- a structural identity of the arithmetic complex (star, flux, gluing, link or nerve law);
- a local Hodge–Riemann statement on an explicit substructure;
- a transport theorem with its exact hypotheses;
- an exact boundary, i.e. an equivalence with RH or a no-go with its positive survivor.

Estimates against a ground energy, numerical certificates, and restatements of neighbouring
programmes do not count.

## 13. Big picture

Over `ℤ` the divisibility complex has much of a Kähler package. Its stars are lower horizons, and
Weil's counterterm is precisely the flux into them; the divisor identity `Λ ∗ 1 = log` is what makes
that flux constant, and it selects `ζ` among all twists. Depth costs `log d`, so deep stars are
Hodge–Riemann without any zero information. The deformation mechanism is exact: hard Lefschetz is
needed only on the positive locus, and the universal regime is a valid base point.

What a variety would supply and `ℤ` does not is the gluing. The towers do not meet in links, so
Garland's method has no start. The stars meet along the nerve, and the exact Möbius formula glues
them with alternating signs whose total is the Mertens function. Every RH-free statement in the
package, local positivity, flux and transport, is proved. The two places where RH reappears are the
hard Lefschetz property of the overlap flow and the half-power growth of the nerve's Euler
characteristic. A proof in this framework must therefore be a gluing theorem: positivity of the
coprime part of the complete Weil form against the Möbius-signed shallow stars, with constants
independent of the level. That is the inductive step which Hodge theory without varieties supplies
in the cases where it works, and it has a precise target over `ℤ`.
