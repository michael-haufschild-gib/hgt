# Prime-triplet distance-three research log

Scope: current re-audit of the prime-factor opposite-sign pairing route. This file records only
facts and no-gos checked during this investigation. It excludes conjectures, plans, analogies,
search dumps, and unproved interpretations. Labels distinguish mathematical scope; a method no-go
does not retire mechanisms outside its stated hypotheses.

## 2026-09-12

### Facts

- **FACT-001 — Three toggles reverse squarefree Möbius sign.** For finite prime supports `S,T`,
  `card (S △ T) = 3` implies
  `μ(product S) = -μ(product T)`. Lean:
  `RouteEThreeToggleCommonNeighborRigidity.routeE_threeToggle_reverses_moebius` in
  `formal/GaloisForLFunctions/RHTower/RouteEThreeToggleCommonNeighborRigidity.lean`.

- **FACT-002 — Common-neighbor separation is exactly local.** If `T` is distance three from both
  `S` and `U`, then
  `card (S △ U) = 2 * card ((S △ T) ∩ (S △ U))`; hence the source separation is one of
  `0,2,4,6`. Lean: `routeE_threeToggle_common_neighbor_exact_overlap` and
  `routeE_threeToggle_common_neighbor_separation_cases` in the same module.

- **FACT-003 — Distance-six codegree is aperture-independent.** If `card (S △ U) = 6`, common
  distance-three neighbors are in bijection with three-subsets of `S △ U`; their number is
  `Nat.choose 6 3`. Lean: `mem_routeEThreeToggleDistanceSixCommonNeighbors_iff` and
  `card_routeEThreeToggleDistanceSixCommonNeighbors` in the same module.

- **FACT-004 — Full-cube codegrees at the remaining collision distances grow with aperture.** In a
  finite ground set `G` of size `d` containing `S ∪ U`, write `h = card (S △ U)`. A common neighbor
  is uniquely `S △ A`, where `card A = 3` and `card (A ∩ (S △ U)) = h/2`. Therefore its full-cube
  count is
  `choose(h,h/2) * choose(d-h,3-h/2)` for `h ∈ {0,2,4,6}`. In particular, distance-two count is
  `2 * choose(d-2,2)`, distance-four count is `6 * (d-4)`, and distance-six count is `20`.
  Status: dependency-closed finite-set proof on paper; only distance six is Lean-certified.

- **FACT-005 — Matching defect is the exact scalar gate.** Every matching in the distance-three
  graph pairs opposite Möbius signs, so the Mertens sum is bounded by unmatched cardinality. An
  all-scale `O_epsilon(x^(1/2+epsilon))` unmatched bound yields the corresponding Mertens bound and
  RH. Source:
  `formal/GaloisForLFunctions/RHTower/RouteEParityColumnLoadCircularityNoGo.lean` and
  `docs/drafts/pipeline/5-failed/prime-triplet-distance-three-matching-conjecture.md`.

- **FACT-006 — Product supports are a shifted threshold complex with Mertens Euler
  characteristic.** The squarefree support downset `K_x = {S : product S ≤ x}` has alternating
  face sum `M(x)`. The exact two-adic reduction puts this sum on odd squarefree supports with
  `x/2 < product S ≤ x`. Lean:
  `formal/GaloisForLFunctions/RHTower/MertensOddWindowKnapsack.lean`.

- **FACT-007 — Recent strong Bollobás inequality needs a separate cross-intersection
  certificate.** Huang--Wang prove
  `sum_i choose(|A_i|+|B_i|-2t,|A_i|-t)^(-1) ≤ 1` from
  `|A_i ∩ B_i| ≤ t` and `|A_i ∩ B_j| > t` for every `i ≠ j`. The theorem also gives a Boolean
  boundary interpretation. A Hall-deficient family in the product-threshold distance-three graph
  does not, by definition alone, supply these ordered cross-intersection hypotheses. Primary source:
  [Huang--Wang, *A Proof of Füredi's Conjecture*](https://arxiv.org/html/2609.11742v1).

- **FACT-008 — Minimal Hall failure is a connected deficiency-one circuit.** Let `A` be
  inclusion-minimal with `card N(A) < card A`. Every proper `B ⊂ A` satisfies Hall. Applying this
  to `A \ {a}` gives `card N(A \ {a}) ≥ card A - 1`, while
  `N(A \ {a}) ⊆ N(A)` and `card N(A) ≤ card A - 1`. Hence all inequalities are equalities:
  `card N(A) = card A - 1` and `N(A \ {a}) = N(A)` for every `a`. Every receiver has at least two
  incident sources, and the graph joining sources that share a receiver is connected; otherwise
  its proper components would each satisfy Hall and their disjoint neighborhoods would sum to at
  least `card A`. Status: dependency-closed finite proof on paper; not yet Lean-certified.

- **FACT-009 — Hall deficiency is transversal-matroid nullity.** Give the source vertices the
  transversal matroid in which a set is independent exactly when it can be matched injectively into
  receivers. Hall's deficiency formula gives
  `rank(A) = card A - max_{B ⊆ A}(card B - card N(B))`. Thus replacing matching deficiency by
  matroid or generic-incidence nullity is an exact reformulation, not a new estimate. Corpus
  determinant infrastructure starts from a `LinearFamilyHall` premise and derives a nonzero
  determinant; it does not prove that premise. Source:
  `formal/GaloisForLFunctions/HTGeometry/HallKrausDeterminantCapacity.lean`.

- **FACT-010 — Mertens is the top parity coefficient of a logarithmic Boolean halfspace.** Let
  `P_x` be the primes at most `x` and
  `K_x = {S ⊆ P_x : ∑_{p∈S} log p ≤ log x}`. Unique factorization gives
  `M(x) = ∑_{S∈K_x} (-1)^card(S)`, equivalently `M(x) = 2^card(P_x) * hat(1_{K_x})(P_x)` in the
  normalized Walsh convention. The corpus also has the exact tilted finite identity converting the
  parity-energy Fourier sum into its Euler product. Lean source:
  `formal/GaloisForLFunctions/RHTower/RouteESourceFaithfulEulerTiltUnitShell.lean`, theorem
  `routeEParityEnergyFourierSum_eq_eulerProduct`.

- **FACT-011 — The square-root seam has an exact largest-prime recursion.** If `Y > 0` and
  `X < Y^2`, every squarefree integer at most `X` has zero or one prime factor larger than `Y`.
  Therefore
  `M(X) = M_fri(X,Y) - ∑_{Y<p≤X} M(floor(X/p))`, where `M_fri(X,Y)` is the Möbius sum over
  `Y`-smooth integers at most `X`. No coprimality correction is needed in the prime sum because
  `floor(X/p) < Y < p`. Lean source: theorem `mertensLargePrimeSector_eq`, recorded in
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-e-mobius-friable-u2-seam-charge.md`.

- **FACT-012 — The squarefree product complex is shifted.** Order prime coordinates increasingly.
  If `q` is occupied, `p<q` is unoccupied, and a support product is at most `X`, replacing `q` by
  `p` multiplies the product by `p/q<1`; the new support remains in `K_X`. Thus `K_X` is a shifted
  simplicial complex. This order structure is source-specific, but by itself supplies no parity
  estimate (NOGO-017).

- **FACT-013 — A fixed finite prime reservoir separates every injective tuple at one
  source-dependent index.** For an injective `m : Fin k → Fin N`, with `k,N ≠ 0`, Lean proves that
  one of `k*(k*k-k)+1` fixed Bertrand-reservoir primes makes reduction of the tuple injective. The
  proof chooses a prime not dividing the directed difference product. Downstream use covers all
  tuples by summing over every reservoir index and pays the full reservoir multiplicity. Lean:
  `exists_vinogradovAvoidingReservoirIndex` in
  `formal/GaloisForLFunctions/RHTower/Sieve/VinogradovAvoidingPrime.lean` and
  `vinogradov_injective_energy_le_reservoir_cover` in
  `formal/GaloisForLFunctions/RHTower/Sieve/VinogradovReservoirRecurrence.lean`.

- **FACT-014 — Prescribed Möbius signs occur with unbounded normalized supply in every positive
  subpower half-power window.** For fixed `0<β<1`, either sign `σ∈{±1}`, and every fixed constant
  `C`, Lean proves eventually at least
  `C * H(Z)/log Z` integers of sign `σ` in `(Z,Z+H(Z)]`, where
  `H(Z)=ceil(sqrt Z * exp((log Z)^β))`. It also derives an eventual cardinality injection from
  primes in that window into its `μ=1` integers. Lean: `route_e_marker_hall_law_all` and
  `route_e_marker_hall_injection_all` in
  `formal/GaloisForLFunctions/RHTower/Sieve/RouteEMarkerHallLawAll.lean`.

- **FACT-015 — One-sided equal-window Hall reduces exactly to consecutive intervals.** For finite
  integer sets `E,T`, a source injection satisfying `e < f(e) ≤ e+H` exists iff every interval
  `[a,b]` obeys `card(E∩[a,b]) ≤ card(T∩(a,b+H])`. Lean:
  `hasForwardWindowMatching_iff_intervalCondition` in
  `formal/GaloisForLFunctions/HTGeometry/ForwardWindowHallMatching.lean`.

- **FACT-016 — Cofactor-amplified E3 targets have an exact factorization decoder.** In the proved
  E3 construction, `q=t*p₁*p₂*p₃`, the full `p₁` band is excluded from `t`, and `p₂,p₃` lie above
  the cofactor cutoff for `η<1/6`. Thus `t` is recovered from the prime factors of `q` below the
  cutoff outside the excluded band, while the remaining small factor identifies the dyadic
  `p₁` slice. Distinct cofactors and slices therefore give disjoint physical targets. Paper proof:
  `docs/drafts/pipeline/2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md`; its parity,
  scale-separation, slice-count, and unsigned-mass layers are Lean-formalized as recorded there.

- **FACT-017 — Product truncation can retain a fixed proportion of variable-breadth harmonic
  mass.** The finite collision/log-moment estimate in
  `RouteEProductTruncatedReservoirMass.lean` gives the explicit lower bound for truncated
  elementary-symmetric mass; its cofinal specialization proves that the permitted product-bounded
  reservoirs retain at least `7/10` of the full divided harmonic mass. This resolves row harmonic
  entropy for that reservoir schedule, not physical column balance. Lean:
  `productTruncatedHarmonicMass_lowerBound_of_normalizedLosses` and
  `sevenTenths_fullMass_le_productTruncatedMass`.

- **FACT-018 — Complementary breadths obey an exact convolution.** If low-reservoir breadth is
  `b`, rough-token breadth is `k-b`, and their divided masses are `S^b/b!` and
  `R^(k-b)/(k-b)!`, summing over every `0≤b≤k` gives exactly `(S+R)^k/k!`. Thus fixed-breadth loss
  is repaired at the unsigned row-mass level by varying both breadths with fixed total grade.
  Lean: `routeEDividedBreadthWeight_sum_eq` in
  `formal/GaloisForLFunctions/RHTower/RouteEEntropyComplementBreadthMixture.lean`.

- **FACT-019 — Weighted Hall deficits have a sharp chi-square rate.** For normalized positive
  source and target laws, a Hall cut with neighbor mass `b∈(0,1)` and deficit `δ` forces canonical
  projection distance squared at least `δ²/(b(1-b))`; exact weighted Hall is equivalent to zero
  projection distance. Therefore a strict-half projection target requires every cut deficit to be
  `X^(-1/2+o(1))*sqrt(b(1-b))`. Lean:
  `weightedHallDeficit_sq_div_le_projectionDistanceSq` and the zero-distance equivalence in
  `formal/GaloisForLFunctions/RHTower/RouteEWeightedHallProjectionDuality.lean`.

- **FACT-020 — Independent replica parity ANOVA has an exact one-copy floor.** For `M>0`
  independent Bernoulli replicas of a binary component with activation probability `q`, the mean
  squared empirical histogram bias is exactly
  `(1-2q)^2 + 4q(1-q)/M`. Across independent components these factors multiply and are at least
  the square of the original one-copy product parity mean. Lean:
  `routeE_independent_replica_localANOVA_eq` and
  `routeE_independent_replica_productANOVA_floor` in
  `formal/GaloisForLFunctions/RHTower/RouteEIndependentReplicaANOVAFloor.lean`.

- **FACT-021 — Every monotone all-right short-window supply already contains a left-window
  supply with unchanged count.** If `h` is monotone and `2h(y)≤y`, the right window based at
  `y-2h(y)` lies inside `(y-2h(y),y)`. Thus applying the same factorization predicate at the shifted
  base gives a numerical predecessor within `2h(y)` without changing parity, freshness, or token
  count. Lean: `routeE_rightWindow_subset_leftWindow`,
  `routeE_leftWindow_card_ge_rightWindow_card`, and the real-scale inclusion in
  `formal/GaloisForLFunctions/RHTower/RouteERightToLeftWindowTransfer.lean`.

- **FACT-022 — Bidirectional load-gradient energy is exactly mismatch-divergence energy.** For
  complete row kernels `P,Q`, put `R=(P+Q)/2` and `D=Q-Pᵀ`. Then
  `1-columnLoad_R(i)=(rowSum_D(i)-columnSum_D(i))/2`; hence every weighted squared load-gradient
  energy of `R` is exactly one quarter of the corresponding squared gradient energy of
  `div D`. This permits an order-one hydrodynamic mismatch profile and isolates shifted-window,
  normalization, cutoff, seam, and physical-collision discrepancies as the arithmetic producer.
  Lean: `routeE_one_sub_averageColumnMass_eq_half_mismatchDivergence` and
  `routeE_weightedAverageColumnGradientEnergy_eq_quarterMismatchDivergenceEnergy` in
  `formal/GaloisForLFunctions/RHTower/RouteEApproximateTransposeDivergence.lean`.

### No-gos

- **NOGO-001 — Signed column-load cancellation is circular.** For every row-stochastic kernel
  supported on sign-reversing edges,
  `2 * Σ_i sign(i) = Σ_j sign(j) * (1 - columnLoad(j))`. Thus declaring a kernel or transport does
  not reduce the original signed sum. Lean:
  `formal/GaloisForLFunctions/RHTower/RouteEParityColumnLoadCircularityNoGo.lean`.

- **NOGO-002 — Strict-half column-defect control already contains RH.** The required all-scale
  strict-half-power bound on total column defect implies the Mertens criterion and RH. It cannot be
  counted as an intermediate cancellation theorem. Lean: the RH implication in
  `RouteEParityColumnLoadCircularityNoGo.lean`.

- **NOGO-003 — Acyclic/discrete-Morse pairing has linear critical mass.** For the natural
  squarefree product complex, odd squarefree `n ∈ (x/2,x]` yield independent missing-simplex
  boundary classes. Total Betti number is `Ω(x)`, so every acyclic discrete-Morse matching has
  `Ω(x)` critical faces. Scope: acyclic/topological matchings only; arbitrary non-acyclic
  distance-three matchings are not excluded. Source:
  `docs/drafts/pipeline/5-failed/prime-occupation-discrete-morse-reheating.md`.

- **NOGO-004 — Fixed or disjoint triple hierarchies leave linear unmatched mass.** A fixed triple
  has a positive-density crossing shell. More generally, any pairwise-disjoint prime-triple
  hierarchy has a positive-density set of squarefree states that occupy a safe lower pattern in
  every block; toggling any prescribed block crosses the cutoff. Scope: fixed/disjoint-block rules,
  including first-fit and mutual-admissibility variants. Source:
  `docs/drafts/pipeline/5-failed/prime-triplet-distance-three-matching-conjecture.md`.

- **NOGO-005 — Sublinear numerical transport leaves linear unmatched mass.** For every fixed
  `theta < 1`, a positive-density family of sufficiently smooth squarefree states in `[X/2,X]` has
  no distance-three neighbor within numerical displacement `X^theta`. Scope: matchings restricted
  to uniformly sublinear numerical jumps. Same source as NOGO-004.

- **NOGO-006 — Cutoff-independent persistent matching cannot have RH-scale crossing defect.** For
  a single global distance-three matching restricted at every cutoff, integrating boundary
  crossings over the smooth states contradicts an `O_epsilon(x^(1/2+epsilon))` crossing bound.
  Scope: one persistent global matching; a separately rewired matching for each cutoff is not
  excluded. Same source as NOGO-004.

- **NOGO-007 — Pairwise degree/codegree estimates do not yield coefficient-one Hall expansion.**
  Corpus reservoir constructions attain the relevant half-density row/codegree exponents while
  retaining an `x^{o(1)}` load loss and potentially macroscopic additive deficit. Scope: arguments
  using only row degrees and pairwise codegrees. Source:
  `docs/drafts/pipeline/3-formalized/route-e-three-toggle-common-neighbor-rigidity.md` and the
  Route E row-degree/codegree modules cited there.

- **NOGO-008 — Strong Bollobás is not a premise-free Hall theorem for this graph.** Its conclusion
  cannot be applied until a Hall-deficient source family is converted into set pairs satisfying
  both self- and every ordered cross-intersection condition. Current distance-three collision
  identity supplies only pairwise symmetric-difference constraints, not that certificate. Scope:
  direct invocation of the theorem; a future source-specific certificate is not excluded.

- **NOGO-009 — Minimal Hall circuits need not have all-pairs receiver overlap.** Take sources
  `s1,s2,s3`, receivers `t12,t23`, and neighborhoods
  `N(s1)={t12}`, `N(s2)={t12,t23}`, `N(s3)={t23}`. The full source family is minimally deficient:
  its neighborhood has size two, while every proper subfamily satisfies Hall. Its source collision
  graph is the path `s1--s2--s3`, so `s1` and `s3` have no common receiver. Therefore minimality
  supplies connected overlap only, not Huang--Wang's condition for every ordered pair. Scope:
  automatic conversion from Hall minimality; product-threshold arithmetic could still force an
  additional certificate.

- **NOGO-010 — Generic incidence rank and determinant capacity do not independently bound the
  defect.** Transversal nullity is exactly maximum Hall deficiency (FACT-009), and the corpus's
  determinant-capacity theorem assumes `LinearFamilyHall`. Proving small nullity or a nonzero
  maximal minor without a separate arithmetic rank lower bound is the original Hall target in
  linear-algebraic form. Scope: generic rank/determinant reformulation; a new theorem using the
  actual logarithmic prime weights is not excluded.

- **NOGO-011 — Generic weighted-halfspace Fourier decay is false.** Give `d` Boolean coordinates
  equal weight one and retain the down-set `card S ≤ 1`. It has `d+1` states and signed parity sum
  `1-d`, so its relative parity bias is `|1-d|/(d+1) → 1`. Therefore monotonicity, halfspace form,
  and positive weights alone cannot yield cancellation of the top Walsh coefficient. Scope:
  weight-agnostic halfspace theorems; the distinct arithmetic weights `log p` remain available.

- **NOGO-012 — Generic Gibbs dependence properties do not create Möbius cancellation.** The exact
  squarefree exponential Gibbs law is log-submodular, yet sparse independent Bernoulli laws can
  have parity expectation tending to one, and the three-prime partition polynomial fails real
  stability for large tilt. Thus negative-dependence labels, pairwise covariance, real stability,
  or positive carrier mass cannot by themselves bound parity at RH scale. Scope and exact models:
  `docs/drafts/pipeline/5-failed/route-e-squarefree-exponential-gibbs-parity.md`.

- **NOGO-013 — Fourier and energy-regression forms are receivers without a new boundary estimate.**
  The exact Euler-product/Fourier and odd-subset product-difference identities expose the parity
  coefficient but do not bound it. The physical-shell regression programme's stronger Gaussian
  saddle claim is not dependency-closed, and its established determinant scale is only
  `X^(-o(1))`, not a square-root saving. Hence scalar Fourier, covariance, or regression control
  does not advance the proof unless it first exploits interaction across the moving multiplicative
  boundary. Sources: `RouteESourceFaithfulEulerTiltUnitShell.lean`,
  `RouteEPhysicalShellParityEnergyRegression.lean`, and the corresponding pipeline card.

- **NOGO-014 — Scalar largest-prime renewal cannot bootstrap a power saving.** In the weighted
  sup norm `|f(t)| ≤ t^alpha`, the positive operator
  `T f(X) = ∑_{Y<p≤X} f(X/p)` has norm `∑_{Y<p≤X} p^(-alpha)`. For every fixed `alpha<1`, PNT and
  partial summation make this asymptotic to `X^(1-alpha)/((1-alpha)log X)`, so it diverges. Hence
  strong induction through FACT-011 fails at every strict power-saving exponent, including
  `1/2+epsilon`; taking absolute values over primes loses almost linear size. Source:
  `route-e-squarefree-exponential-gibbs-parity.md`, equations `(G46m)`--`(G46o)`.

- **NOGO-015 — The literal prime tail has no prime-index oscillation to feed a large sieve.** Exact
  grouping gives
  `∑_{Y<p≤X} M(floor(X/p)) = ∑_k M(k) * card{p : Y<p≤X, floor(X/p)=k}`.
  The bucket multiplicities are nonnegative. Bare regrouping therefore creates no orthogonal prime
  phases, and Cauchy--Schwarz replaces the target by an unproved square-root-scale `L^2` bound for
  `M(k)`. Scope: direct prime-parameter orthogonality or Cauchy--Schwarz; a new arithmetic transform
  with an independently bounded off-diagonal kernel is not excluded.

- **NOGO-016 — Static multiplicative rectangles conserve each seam sector's signed mass.** For a
  coprime Möbius checkerboard rectangle wholly in the zero/one-large-prime boundary, the signed
  corner sum is zero separately in breadth zero and breadth one. Thus a sector-closed fractional
  rectangle cover cannot transfer the large opposite seam charges; only corners crossing the
  moving physical cutoff can contribute flux. Lean:
  `mobiusParityRectangle_zeroLargePrime_cornerSum_eq_zero` and
  `mobiusParityRectangle_oneLargePrime_cornerSum_eq_zero` in
  `formal/GaloisForLFunctions/RHTower/MobiusMultiplicativeRectangleCubature.lean`.

- **NOGO-017 — Actual large-prime slices have asymptotically maximal local parity bias.** On the
  empty-small-prime slice of `B_X={p prime : sqrt X<p≤X}`, the product cutoff admits exactly the
  empty set and the singleton sets: every product of two block primes exceeds `X`. Its signed
  parity sum is `1-card(B_X)` and its unsigned mass is `1+card(B_X)`; PNT gives
  `card(B_X)→∞`, so relative bias tends to one. Hence distinct `log p` weights, shiftedness, and
  within-block compression cannot yield local parity mixing. Any successful proof must couple
  large-prime occupancy to nontrivial small-prime spectators before averaging or taking norms.

- **NOGO-018 — One balanced E3 core with multiplicative pre-cofactors lacks strict-half physical
  capacity.** If targets have shape `t*p₁*p₂*p₃` and strict-half displacement forces
  `T*P=U^o(1)`, their physical count in one dyadic scale is at most
  `O(U*log T*log log P/log² U)=o(U*log log U/log U)`. This is below the ordinary defect budget
  allowed by the available mean-square estimate. Counting labeled representations cannot improve
  physical target capacity. Scope: one balanced E3 core with one total multiplicative pre-cofactor;
  non-collapsed higher-rank targets remain open. Paper proof and exact hostile current:
  `docs/drafts/pipeline/5-failed/route-e-strict-half-e3-cofactor-capacity-ceiling.md` and
  `formal/GaloisForLFunctions/RHTower/MobiusBlockDefectEnergy.lean`.

- **NOGO-019 — Cut Hardy--Ramanujan recursion cannot bootstrap the central exact-omega layer from
  level one in square-root intervals.** After `s` steps ending at level `j`, its prime-power error
  exceeds the interval length when `s≈(j+1)/3`; starting from the proved level-one estimate reaches
  only `j=O(1)`, not `j≈log log X`. Scope: this recursion as a bootstrap; Shiu's tilted rough sum
  and any independently supplied upper central layer remain open. Exact derivation:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-e-two-sided-off-normal-wold-breadth-transport.md`,
  section “Reach of the cut recursion”.

- **NOGO-020 — Unquantified one-sided near-unit load is too weak for strict-half ANOVA.** A ceiling
  `columnLoad≤1+ε` gives chi-square at most `ε`, sharply, so `ε=o(1)` does not reach
  `X^(-1+o(1))`; one-sided load needs `ε≤X^(-1+o(1))`, while two-sided relative balance needs
  error `≤X^(-1/2+o(1))`. Scope: conversion from load bounds to the chi-square endpoint; a direct
  unmatched-mass estimate enters linearly and has a different rate law. Source:
  `route-e-weighted-hall-anova-projection-duality-law.md`.

- **NOGO-021 — Independent replica productization cannot create Möbius cancellation.** FACT-020
  shows that increasing replica order removes only a nonnegative `1/M` variance correction and
  converges to the unchanged one-copy parity-bias square. Scope: independent Bernoulli/Euler
  averaging of histogram cells; aperture-conditioned or otherwise correlated component histories
  remain open. Paper/Lean card:
  `docs/drafts/pipeline/5-failed/route-e-independent-replica-productization.md`.

- **NOGO-022 — Replica orbit cardinality does not control parity bias.** A binary singleton cell
  with `C` components and `M>2` slots has orbit size `M^C` but bias `(1-2/M)^C`, bounded below by
  `exp(-2C/(M-2))`. Vanishing physical curvature plus exact cancellation therefore forces
  `C/(M-2)→∞`; power-size entropy at bounded component density is insufficient. Scope:
  bounded-density singleton histories; unbounded-density and non-singleton conditioned histories
  survive. Lean: `formal/GaloisForLFunctions/RHTower/RouteEComponentHistorySparseDensityNoGo.lean`.

- **NOGO-023 — A strict-half cube mixed difference is not an `H`-local edge estimate.** The
  parity-coalesced full-terminal relation explicitly permits numerical jumps `X^(1-o(1))`; its
  `X^(-1/2+o(1))` cost is the full odd mixed difference. Therefore it cannot be inserted into the
  two-sided column-load conductance theorem, whose first term requires every supported edge to
  have `H=X^(1/2+o(1))`. Scope: this direct theorem composition only. The high-order cube consumer
  and the product-truncated whole-anchor relation with genuinely strict-half edges both survive.
  Sources: sections 4–5 of `route-e-grade-recurrent-sparse-reservoir-cube-admission.md` and Theorem
  B of `route-e-two-sided-column-load-gradient-pairswitch-law.md`.

- **NOGO-024 — Exact transpose reversal cannot manufacture column balance.** If a proposed
  downward kernel is exactly the transpose of an upward kernel and the downward rows have mass
  one, then the upward columns already have mass one. Scope: exact transpose identification only;
  approximate transpose survives, with its precise remaining producer given by the divergence in
  FACT-022. Lean: `routeE_columnMass_eq_one_of_transpose_rowMass` in
  `formal/GaloisForLFunctions/RHTower/RouteEApproximateTransposeDivergence.lean`.
