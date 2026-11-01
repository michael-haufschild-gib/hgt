# Edge Hodge Theory of the Scaling Surface (EHT)

Namespace `GaloisForLFunctions.EdgeHodgeTheory`; umbrella `EdgeHodgeTheory.lean`. Everything is
unconditional. Theorems named `riemannHypothesis_iff_*` are equivalences, `riemannHypothesis_of_*`
implications into RH; neither is a proof of RH.

## 1. Motivation

Renormalized intersection theory (RIT) and adelic Krein geometry (AKG) place the Frobenius-graph
geometry on the scaling surface of `ℤ` and locate the missing sign: RH is the renormalized Hodge
index, positivity of the pairing of scaling correspondences on the pole-orthogonal hyperplane
`v₁^⊥`. Every reformulation inside that geometry — Castelnuovo–Severi at rational scales, the
Künneth square, every Hadamard power, the glued test index, the heat homotopy — reproduces RH
exactly, and every estimate stops at the same place.

That place has a structure. The pairing is computed at **finite resolution**: atoms of a profile
`φ` of width `w` at the points `log n`, `n ≤ N`; at overlap `c = wN` this is the complete Weil matrix
`W_{φ,c,N}`. As the resolution grows the family passes from a **universal regime**, where positivity
is proved without zero information, to an **RH regime**, where positivity is equivalent to RH.
Between them lies the **detection edge**, near `τ(c) log N ≈ 1` with `τ` the Fourier tail of the
profile.

The obstruction at the edge is logical, not technical. A positivity statement proved without zero
information holds for every datum sharing that information, including data with off-line zeros, so
it is valid only where those data are not yet seen. No refinement of estimates crosses the edge,
and signature calculus cannot either, since every index reformulation is RH. What can cross is a
statement that holds at the edge **by structure**. EHT is the theory of the degenerating family
`W_{φ,c,N}` and of the three kinds of statement that hold by structure: **identities**, **inherited
polarizations** and **integer invariants**.

The model is Hodge theory of degenerations, where positivity survives in the limit by structure
(nilpotent-orbit and `SL₂`-orbit theorems). The scaling surface has the corresponding ingredients:
a limit structure at fixed overlap (the Ramanujan-graded completed conductor energies),
one-parameter flows (overlap, horizon, heat) with integer invariants (Hodge defect, Krein–Langer
index, collision charge), and a hyperbolic plane (boost and conformal successor) acted on by
`SL(2, ℝ)`. EHT determines which of these survive across the edge, proves what they give, and
proves where they cannot give more.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Admissible profile | `Admissible` | `C²`, supported in `[0, 1]`, `∫φ ≠ 0`, `∫φ² > 0` |
| Complete Weil matrix and energy | `RenormalizedArithmeticPotentialTheory.completeWeilMatrix`, `completeWeilEnergy` | Weil's form on the atoms of width `c/N` at `log n`, `n ≤ N`, atom-mass normalized |
| Positivity at a resolution | `PositiveAt`, `HyperplanePositiveAt`, `TwinPositiveAt` | on all vectors; on `v₁^⊥`; for a twisted weight |
| First failure | `firstFailure` | least overlap `c ≥ 1` at which a property fails, `⊤` if none |
| Edge | `edge`, `hyperplaneEdge`, `twinEdge` | first overlap at which the family is not positive semidefinite |
| Horizon family of a test | `horizonGram`, `horizonDefect` | Weil Gram matrix of `f(· − log n)`, `n ≤ N`, and its negative squares |
| Threshold | `horizonThreshold` | first horizon at which the horizon family has a negative square |
| Seen right zeros | `ArithmeticOrientationGeometry.seenRightZeros` | zeros right of the line at whose spectral points the test's transform is nonzero |
| Krein–Langer index | `HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel` | `κ(K_ζ)` = number of zeros right of the line |
| Limit structure | `limitForm` | `Σ_m E_m(c) y_m²`, `E_m` the completed conductor energies |
| Window edge of a curve | `windowEdge` | first window of Frobenius graphs whose span defect has a negative square |
| Straight path | `straightPath` | `t ↦ (1 − t)A + t·1` |
| Defect involution | `defectInvolution` | `ρ ↦ 1 − ρ̄`: conjugation composed with reflection |
| Collision charge | `RHTower.xiHorizontalCollisionCharge` | Fredholm index of an integer-theta Wiener–Hopf operator |
| Balance overlap (sinc) | `TransMetzlerWeilPositivity.sincCriticalOverlap` | least `c ≥ 1` with `τ(c) log N ≤ 1` |

## 3. Language

- **Resolution**: a pair (width `w`, horizon `N`), or (overlap `c = wN`, horizon `N`). The complete
  Weil family is the section `w = c/N` of the plane of resolutions.
- **Universal regime**: resolutions at which positivity is a theorem. **RH regime**: schedules at
  which eventual positivity is equivalent to RH.
- **Edge**: the first failure of positivity, as a function of the horizon (overlap coordinates) or
  of the width (threshold coordinates). Under RH it is at infinity.
- **Edge-valid statement**: one that holds at every resolution, edge included — an identity, an
  inherited polarization or an integer invariant. An estimate against the ground energy is not.
- **Limit structure**: the fixed-overlap limit of the family in Ramanujan coordinates.
- **Inherited polarization**: positivity of the finite-resolution form deduced from the polarization
  of its limit with a loss of a fixed fraction of the limit's gap.
- **Ground energy and quantum**: `E₁(c)`, the energy of the pole conductor, and `1/log N`, the scale
  at which zeros enter the normalized form.
- **Conserved charge** of a test: the number of right zeros it sees; the limit of its horizon defect.
- **Crossing**: a point at which a path of forms is degenerate; integers change only there.
- **Window**: the set of tests whose Weil positivity follows from positivity of a family; for the
  sinc profile its radius is `½ log K − O(1)` at the multiple `K` of the balance overlap.
- **Frobenius at infinity**: a correspondence acting as conjugation on the zero divisor.

## 4. Mechanisms

**The edge logic.**
1. An estimate holds for a class of data sharing its input; its universal regime is contained in
   the positivity region of every member, so it lies below the edge of every off-line member. Only
   a statement whose class contains no off-line datum can cross the edge.

**Nesting at fixed width.**
2. At fixed width the atoms up to `N` are among the atoms up to `N' ≥ N`, so the horizon Gram
   matrices are principal submatrices of each other: positivity is a threshold in `N`, the Hodge
   defect is nondecreasing, and the complete Weil matrix at `(c, N)` is positive iff `N` lies below
   the threshold of the atom of width `c/N`.
3. Integer windows carry the whole index of a kernel on `ℚ_{>0}` (a common denominator turns
   rational positions into integers, and Weil's form is translation invariant); the orbit kernel of
   a real test has one negative square per seen right zero. So the horizon defect converges to the
   seen count.
4. On a complex combination of real tests Weil's form is the sum of its values on the real and
   imaginary parts, which are again real atomic tests: complex and real positivity agree.

**Identities.**
5. Repayment: each completed conductor energy is a positive Fourier integral, so the limit
   structure is polarized by an identity; the pole conductor is its ground state.
6. Shells: on the boost hyperplane the glued archimedean state is Weil's dilation form plus the
   squares of the half-line shells.

**Degeneration.**
7. The completed conductor energies tend to `0` with the overlap. Along any growing schedule the
   limit structure degenerates; in the universal regime a polynomial fraction of it is inherited,
   in the RH regime nothing is.

**Integers.**
8. The negative index is lower semicontinuous, `n₊ + n₋ + n₀` is the dimension, so near a matrix of
   nullity `n₀` the index rises by at most `n₀`; at nondegenerate points it is locally constant and
   along nondegenerate paths constant. A reading within `1/2` of a continuous function is constant.
9. Kronecker inertia: `n₋(G ⊗ G) = 2 n₊(G) n₋(G)`.
10. Right zeros pair under conjugation, so a finite Krein–Langer index is even.

**Profile covariance.**
11. The RH regime starts where the synthesis error, read in the density `log N`, vanishes:
   `c_N⁴/log N → ∞` for every `C²` profile, `(log log N)^α`, `α > 1`, for Denjoy–Carleman profiles,
   a divergent multiple of `L(log L)²` for the sinc profile; Gevrey class `≤ 1` admits no compactly
   supported profile.

**Selection and calibration.**
12. Every admissible profile sees every prime flip at bounded overlap, while the edge of `ζ` grows.
13. Over `𝔽_q` the span defect is constant from window `2g` on: detection happens at bounded
   resolution.

## 5. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| What is the limiting structure of `W_{φ,c,N}`, and is it polarized on `v₁^⊥` by an `SL₂`-type mechanism? | At fixed overlap the limit is the Ramanujan-graded form `Σ E_m(c) y_m²`, polarized by the repayment identity, with the pole conductor as ground state. Along every growing schedule it degenerates to `0`; for the tilted spline a polynomial floor `K/c⁷` is inherited throughout the universal regime, and at the RH-complete schedules the ground energy tends to `0` while positivity is RH. The `SL₂`-type structure (pole pair of the boost–successor plane) is blind on `v₁^⊥`: adding it with any weight leaves the Hodge index unchanged. | `tendsto_ramanujan_quasimode`, `limitForm_nonneg`, `ground_mul_sum_sq_le_limitForm`, `tendsto_limitForm_comp`, `tiltedSpline_inheritance_and_degeneration`; `RenormalizedIntersectionTheory.renormalizedHodgeIndex_add_polePair_iff` |
| Why is the edge at `τ(c) log N ≈ 1`, and what changes there? | The balance overlap `c*_N` is of order `L(log L)²` for the sinc profile; at the multiple `K` of it the family controls every test of support radius `½ log K − O(1)`: the visible window opens at the balance and is empty below it. In the plane of resolutions the edge is the graph of the threshold; for the tilted spline it lies above `(log 1/w)^α/(2w)` unconditionally and, without RH, below `N` at the widths `2(log N)^β/N` infinitely often. | `sinc_edge_balance`, `sinc_window_opens`, `positiveAt_iff_lt_horizonThreshold`, `eventually_lt_horizonThreshold_powerLog`, `frequently_horizonThreshold_le_of_not_rh` |
| Is there a monotone or conserved quantity controlling the Hodge defect along the resolution flow? | Yes. At fixed width the horizon defect is nondecreasing and converges to the number of right zeros the atom sees, reaching it at a finite horizon when finite; for spline atoms of every width this is `κ(K_ζ)` (HKT). Along the heat flow the defect is nonincreasing, dropping by one per collision (RIT). | `horizonDefect_mono`, `iSup_horizonDefect`, `exists_horizonDefect_eq`; `HeckeKreinToeplitz.negIndex_zetaKernel_eq_iSup_shrinkGram`, `RenormalizedIntersectionTheory.antitoneOn_boostPolarIndex_heat` |
| What is Frobenius at infinity? | The defect involution `ρ ↦ 1 − ρ̄` fixes exactly the critical line; a conjugation identifying the collided and reflection pairings exists on `ζ` iff RH, and its failure is counted by `κ(K_ζ)`, one per moved zero on the right. Over `𝔽_q` it is the circle reflection of the Frobenius eigenvalues, and the span defect counts the eigenvalues it moves outside the circle. As a Hecke similitude of the collided polarization it is again RH. | `defectInvolution_eq_self_iff`, `riemannHypothesis_iff_defectInvolution_trivial`, `negIndex_zetaKernel_eq_encard_moved`, `circleReflect_eq_self_iff`, `hermNegIndex_spanGram_eq_card_moved`, `frobeniusAtInfinity_iff` |
| Does Weil's dilation form on `ℓ = 0` admit a shell identity, and is it the edge limit of the universal-regime decompositions? | The glued archimedean state is the dilation form plus shell squares at every resolution (AKG). The universal-regime decompositions are the limit structure, which degenerates to `0` along every growing schedule, so the dilation form at the edge is not their limit. A positivity identity for the dilation form at an RH-complete resolution is RH (RIT). | `AdelicKreinGeometry.hermQuad_gram_weilArchState_shell`, `tendsto_limitForm_comp`, `RenormalizedIntersectionTheory.riemannHypothesis_iff_completeWeil_hodgeIndex_log` |
| Is `κ(φ_c) − 1` an index computed by deformation to a model? | Along a crossing-free path the index is constant; a crossing-free path to the identity exists iff the form has no negative and no null direction; regularized, iff it has no negative square. For the spline horizon families RH is the existence of such deformations at every horizon, and without RH every deformation crosses from some horizon on. An index computed by deformation to a positive model is the sign itself. | `hermNegIndex_eq_of_isPreconnected`, `exists_crossingFree_path_to_one_iff`, `forall_exists_crossingFree_path_add_iff`, `riemannHypothesis_iff_spline_regularized_deformation`, `eventually_not_exists_crossingFree_path_of_not_rh` |

## 6. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| RH is an infinite edge, for every admissible profile | `riemannHypothesis_iff_forall_edge_eq_top`, `riemannHypothesis_iff_eventually_edge_eq_top` | equivalences |
| Edge dichotomy and ceiling: without RH every admissible profile has its edge below `2(log N)^β`, `β > 1/4`, infinitely often | `edge_dichotomy`, `frequently_edge_le_of_not_riemannHypothesis` | unconditional |
| Universal regime and edge window of the tilted spline: edge `≥ (log N)^α`, `α < α*`, and `→ ∞`; without RH in `[(log N)^α, 2(log N)^β]` infinitely often | `eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline`, `tendsto_edge_tiltedUnitSpline`, `frequently_edge_mem_window_of_not_riemannHypothesis` | unconditional |
| Hyperplane edges: below every power of `log N` for smooth profiles, below `2(log N)^β`, `β > 1/2`, for the tilted spline, infinitely often without RH | `frequently_hyperplaneEdge_le_of_smooth`, `frequently_hyperplaneEdge_le_tiltedUnitSpline`, `riemannHypothesis_iff_eventually_hyperplaneEdge_eq_top` | unconditional; equivalence |
| The edge selects `ζ` from its prime-flip twins | `eventually_twinEdge_primeFlip_le`, `edge_selects_zeta_from_prime_flips` | unconditional |
| Horizon flow: monotone defect, conserved charge = seen right zeros, stabilization, positivity = vanishing defect, threshold infinite iff nothing seen | `horizonDefect_mono`, `iSup_horizonDefect`, `exists_horizonDefect_eq`, `horizonDefect_eq_zero_iff`, `horizonThreshold_eq_top_iff` | unconditional |
| The edge is a threshold curve: section theorem, width positivity = seeing, divergence of the detection horizon | `positiveAt_iff_lt_horizonThreshold`, `forall_positiveAt_width_iff`, `tendsto_horizonThreshold_tiltedUnitSpline` | unconditional |
| The threshold curve hugs the hyperbola `wN = 1` within log-power factors | `eventually_lt_horizonThreshold_powerLog`, `frequently_horizonThreshold_le_of_not_rh` | unconditional |
| Integers along paths: semicontinuity, local constancy, path invariance, precision below `1/2`, deformation to a model | `eventually_le_hermPosIndex`, `eventually_hermNegIndex_le_add_nullIndex`, `eventually_hermNegIndex_eq_of_nullIndex_eq_zero`, `hermNegIndex_eq_of_isPreconnected`, `eq_of_abs_sub_lt_half_of_isPreconnected`, `exists_crossingFree_path_to_one_iff` | unconditional |
| Index by deformation of the spline horizon families | `riemannHypothesis_iff_spline_regularized_deformation`, `eventually_not_exists_crossingFree_path_of_not_rh` | equivalence; unconditional |
| No softening at resolution: Künneth defect `2 n₊ n₋`; RH iff the Künneth squares of the integer spline atoms are positive; otherwise defect `≥ 2` eventually | `hermNegIndex_kronecker_self`, `riemannHypothesis_iff_kunneth_horizon`, `eventually_two_le_kunneth_of_not_rh` | unconditional; equivalence |
| Limit structure: quasimodes, repayment polarization, pole ground state, degeneration along every growing schedule; inheritance and degeneration for the tilted spline | `tendsto_ramanujan_quasimode`, `limitForm_nonneg`, `ground_mul_sum_sq_le_limitForm`, `tendsto_limitForm_comp`, `tiltedSpline_inheritance_and_degeneration` | unconditional |
| Frobenius at infinity | `riemannHypothesis_iff_defectInvolution_trivial`, `negIndex_zetaKernel_eq_encard_moved`, `hermNegIndex_spanGram_eq_card_moved`, `frobeniusAtInfinity_iff` | equivalences; unconditional |
| The window opens at the balance; profile covariance and the quasi-analytic boundary | `sinc_edge_balance`, `sinc_window_opens`, `profile_covariance_of_the_edge` | unconditional; equivalence |
| Integer readings as edge detectors: horizon defects `≤` collision charges; vanishing charges give positivity at every resolution; charges `≤ 1` give RH | `exists_fredholmIndex_eq_collisionCharge`, `horizonDefect_le_iSup_collisionCharge`, `positiveAt_of_collisionCharge_eq_zero`, `riemannHypothesis_of_collisionCharge_le_one` | unconditional; implication |
| Calibration over `𝔽_q`: the flow is trivial — edge `∞` iff Weil's bound, otherwise `≤ 2g`; defect constant from `2g`; the golden datum is seen at window `2` | `windowEdge_eq_top_iff`, `windowEdge_le_card`, `hermNegIndex_spanGram_stable`, `two_le_windowEdge`, `windowEdge_goldenDatum`, `edge_bounded_over_curves_and_unbounded_over_integers` | unconditional |

## 7. Tools

**Developed.**
- First failures of properties of overlaps and their calculus (`firstFailure` and its lemmas);
  edges, hyperplane edges and twin edges of resolution families.
- Krein-space spectral flow for finite families: two-sided semicontinuity of the inertia, local
  constancy, path invariance on preconnected sets, crossing bounds, the rounding principle,
  deformation along straight paths, eigenvalue shifts.
- Horizon families of arbitrary real tests: nesting, monotone defect, conserved charge, thresholds,
  and the real/complex positivity bridge `re_weilFull_eq_re_add_im`.
- The section theorem linking overlap and threshold coordinates.
- Limit structures: the Ramanujan-graded limit form and its degeneration along schedules.
- Kronecker inertia applied to resolution families.
- The defect involution over `ℤ` and its circle-reflection analogue over `𝔽_q`.
- Integer readings: collision charges as Fredholm indices bounding every horizon defect.

**To build.**
- Asymptotic expansions of the limit structure along the overlap degeneration: the rescaled limit
  `E_m(c)/E₁(c)`, for regularly varying ground energies a Jordan-totient weight structure.
- A conductor-graded edge: the overlap at which `E_m(c) log N ≈ 1`, and its relation to the edges on
  the orthogonal complements of the first Ramanujan vectors.
- Renormalized determinants and the running counterterm `log N − γ` along the flows.
- Continuity of the complete Weil family in the overlap, to apply path invariance along the overlap
  flow at fixed horizon.

## 8. Open research topics

1. The exact edge exponent of the tilted spline, bracketed in `[α*, ¼]`; the threshold curve
   between `(log 1/w)^α/(2w)` and `2(log N)^β/N`.
2. Inheritance of the limit polarization on `v₁^⊥` past the universal regime: a signed estimate on
   the subthreshold conductor block `m ≲ c` at floor scale.
3. A positivity identity for Weil's dilation form on `ℓ = 0` indexed by conductors and shells.
4. A crossing-free homotopy of the glued state to an index-one model for a structural reason.
5. A height-uniform bound on the collision charges below `2`.
6. Selection of maximal-margin infinite flip twins by the edge.

## 9. Traps

| Trap | Fact |
|---|---|
| Positivity at fixed overlap is progress toward RH | It holds unconditionally with a gap; it is the universal regime |
| A sharper estimate eventually crosses the edge | An estimate valid for a class with an off-line member stops below that member's edge |
| The limit structure polarizes the edge | It degenerates to `0` along every growing schedule |
| The `SL₂`/Borel structure carries the sign on `v₁^⊥` | The pole pair can be added with any weight without changing the hyperplane index |
| A crossing-free homotopy to a positive model is an independent proof | It exists iff the starting form is positive and nondegenerate |
| Smoother profiles soften the problem | They lower the RH regime to `L(log L)²`; positivity there is still RH, and the quasi-analytic boundary stops the descent |
| Künneth or Hadamard powers soften the sign | The Künneth defect is `2 n₊ n₋`; positivity of the Künneth squares at every horizon is RH |
| The edge depends on how the zeros are seen at each overlap separately | At fixed width it is a single threshold in the horizon, finite iff the atom sees a right zero |
| A finite collision charge of `1` is possible | Right zeros pair; charges `≤ 1` everywhere give RH |
| Frobenius at infinity is a symmetry to build first | Its existence on `ζ` is RH; its failure is the Hodge defect |
| Over `𝔽_q` one also needs a resolution flow | The flow is trivial: detection by window `2g` |

## 10. Context

EHT sits between the two halves of the RH map: the estimate routes of class C1 (HF, SRT, AIP, ACT,
ACS, SC, RW, EWU, OWU, CHMD), which grow unconditional positivity with resolution, and the identity
and index routes (SC, WD, RIT, AKG, HKT), which reproduce RH exactly. Its objects are the walls
`Σ-1` (positivity on `v₁^⊥` across the edge), `Σ-4` (the exact edge of the tilted spline), `Σ-5` (an
identity for the dilation form), `Σ-10` (collision charge below `2`) and the selection wall `Γ-5`.

| Neighbour | Interface |
|---|---|
| RenormalizedIntersectionTheory | Hodge index at growing overlap, pole blindness, heat homotopy, positive index of `K_ζ` |
| RenormalizedArithmeticPotentialTheory | complete Weil matrix, completed conductor energies, receivers at logarithmic overlap, prime-flip detection |
| CriticalArithmeticCorrelationTheory | the universal regime: fixed, bounded, iterated-logarithmic and power-of-log overlap |
| TransMetzlerWeilPositivity | balance overlap and windows of the sinc profile |
| HeckeKreinToeplitz | Krein–Langer index, integer windows, orbit kernels, spline atoms at every width, quasi-analytic boundary, collision bound |
| ArithmeticOrientationGeometry | seen right zeros, parity of right zeros |
| AdelicKreinGeometry | archimedean shell identity, pole–successor plane |
| ArithmeticPolarization, ConjugateDiagonalGeometry | collided polarization and Hecke similitudes; integer-theta Fredholm indices |
| ArithmeticCastelnuovoSeveri, HTGeometry | curve data and the span defect; Hermitian and Kronecker inertia |

## 11. Success criteria

| Criterion | Status |
|---|---|
| Edge validity: positivity statements are identities, inherited polarizations or index computations | The pillars are identities (repayment, shells), integer statements (thresholds, conserved charges, path invariance, Künneth inertia, collision readings) or equivalences; no estimate against the ground energy is used beyond the universal regime |
| Calibration over `𝔽_q` with quantized exponents; the golden datum fails where the Hodge index fails | `windowEdge_eq_top_iff`, `windowEdge_le_card`, `windowEdge_goldenDatum` |
| The single square comes from the archimedean place | pole blindness on `v₁^⊥` (RIT); the hyperplane carries the whole index |
| No softening at degree two | `riemannHypothesis_iff_kunneth_horizon`, `eventually_two_le_kunneth_of_not_rh` |
| Integrality | thresholds and charges are integers; `eq_of_abs_sub_lt_half_of_isPreconnected`, `riemannHypothesis_of_collisionCharge_le_one` |
| Selectivity | `edge_selects_zeta_from_prime_flips`; maximal-margin infinite twins open |
| Profile covariance | `profile_covariance_of_the_edge`, `sinc_edge_balance` |

The field is developed when each question of §5 has a Lean theorem that answers it — an equivalence,
a classification or a no-go — and each tool of §7 is used by a pillar. It succeeds when a positivity
statement on `v₁^⊥` is proved at an RH-complete resolution by an edge-valid mechanism.

## 12. What counts as a contribution

- A Lean theorem, unconditional, in this folder, wired into the umbrella.
- It is a statement about the degenerating family — its edge, threshold, limit, flows, integers,
  selectivity or calibration — or a tool that a pillar uses.
- It says which kind of statement it is: identity, inherited polarization, integer invariant,
  estimate (and in which regime), equivalence with RH, or no-go.
- New objects are built from integers, adeles and Weil's data, never from zero copies.

## 13. Big picture

The family of complete Weil matrices is a degenerating family with a precise shape. At fixed width
it is nested in the horizon, so positivity is a threshold and the Hodge defect is a monotone
integer converging to a charge only the zeros can carry: the number of right zeros the atom sees,
`κ(K_ζ)` for spline atoms. The complete Weil matrix at overlap `c` is the section `w = c/N` of the
plane of resolutions, and the edge is where this section crosses the threshold curve. Under RH the
threshold is at infinity on every line; without RH it is finite exactly on the lines whose atom sees
an off-line zero, recedes to infinity as the atoms shrink, and lies within log-power factors of the
hyperbola `wN = 1`.

The structures that hold by identity live on the limit: the Ramanujan-graded completed conductor
energies are positive Fourier integrals with the pole as ground state. But the limit degenerates
along every growing schedule, and the hyperbolic `SL₂`-plane of the pole is blind on `v₁^⊥`, so
neither carries a gap into the RH regime. The structures that hold by integrality survive
everywhere — thresholds, conserved charges, path invariance, Künneth inertia, collision readings —
and each of them, read at an RH-complete resolution, is RH: deformation to a positive model is the
sign, the Künneth square is the sign, Frobenius at infinity is the sign, collision readings below `2`
are the sign. Over `𝔽_q` the same theory has a trivial flow and detects every violation at window
`2g`; over `ℤ` the flow is genuine because infinitely many critical zeros surround any off-line pair.
What remains is a statement that holds at the edge by structure and sees the zeros there: an
inherited polarization on `v₁^⊥`, an identity for the dilation form, or an integer reading bounded
below `2` for a structural reason.
