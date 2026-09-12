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
