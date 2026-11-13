# Mixing Arithmetic of the Floor Trees (MAFT)

Namespace `GaloisForLFunctions.MixingArithmeticOfTheFloorTrees`; umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Specification: §2.9 of
[the review-1311 summary](../../../docs/reports/review-1311/obstacles-summary.md). Programme card:
`docs/drafts/pipeline/1-in-progress/maft-mixing-arithmetic-of-the-floor-trees.md`.

Every theorem named here is proved in Lean without added hypotheses; a theorem named
`…_of_riemannHypothesis` takes RH as its stated antecedent and serves only as calibration: it
tells what a proof must produce, not how. **AGZ**, **LST**, … mark theorems of other folders,
**[C]** published mathematics not in the corpus, **open** a statement not proved.

## 1. Motivation

At finite scale the Riemann hypothesis is a statement about one explicit matrix per window. On the
unit blocks `(a, a + 1]` of a window `W = (R, R + J]`, Weil's form of a step packet is twice the
product of its two charges plus the **neutral part** `N_W`. Off the diagonal `N_W` is minus the
jets, which join every pair of blocks, and minus the contacts of the **floor maps**
`b ↦ ⌊b/k⌋` with the weights `Λ(k)/k`. RH holds iff `N_W` has exactly one negative square on every
window with `R ≤ J` (AGZ).

A symmetric matrix with negative off-diagonal entries is minus the generator of a positive
dynamics. Conjugation by its positive ground vector `φ` turns `N_W` into the generator of a
reversible Markov chain on the blocks — the **Doob chain** of the window — shifted by the least
eigenvalue `−μ_W`. So RH at finite scale is a Poincaré inequality: *the spectral gap of the Doob
chain of every window is at least its binding energy `μ_W`*. Three facts fix what a proof of it
must use: the binding of two halves has rank proportional to the block size; weakened or twisted
contacts give a second bound state; the matrix is cooperative. MAFT studies the chain: its gap,
its binding energy, its cuts, its comparison with the chains of its parts, its limit at infinite
block size.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| window, neutral part | `neutralWindow Q R J` (AGZ) | blocks `R, …, R + J − 1`, ratio `ρ = (R + J)/R`, contacts up to `Q` |
| ground vector | `exists_pos_eigenvector`, `exists_groundVector_neutralWindow` | `φ > 0`, `N φ = λ φ`, `λ` the least eigenvalue |
| binding energy | `−λ` | the depth of the ground state |
| Doob chain | `doobConductance`, `doobEnergy`, `doobMean`, `doobMass` | weights `φ_i²`, conductances `c_{ij} = −N_{ij} φ_i φ_j`, Dirichlet form `E` |
| cut | `doobWeight`, `doobCut` | `π(S)`, `C(S) = Σ_{i ∈ S, j ∉ S} c_{ij}` |
| overlap of a window | `overlapWhole`, `joinColumns` | `(R, 2D + b]` as left end `(R, D]`, dyadic middle `(D, 2D]`, right end `(2D, 2D + b]`, `D = R + a` |
| conditional energies, coupling | `overlapLeftEnergy`, `overlapRightEnergy`, `overlapCoupling` | Schur complements over the middle: `S₁`, `S₃`, `X = K − P₁ᵀ M⁻¹ P₂` |
| test packets | `rootPacket`, `blockRange`, `windowPlane` | `a^{−1/2}`; an interval of blocks; the refined plane of the blocks `(2, 3]`, `(3, 4]` |
| margin bound | `marginBound Q` | `c₀ = max(N(2,2), N(3,3)) + |N(2,3)|` |
| ends of a long window | `bottomMass`, `topMass` | the mass on the blocks `a` with `K a < R + J`, and on the blocks `b ≥ KR` |
| pole capacity | `poleCapacity R J` | `J/√(R(R + J)) + log ρ = √ρ − 1/√ρ + log ρ` |
| spread copies | `spreadTest`, `threeSpread`, `planeTest`, `firstCharge` | `β((u − d)/L)`; three copies `3L` apart; the plane of vanishing first charge `A(f) = ∫ f e^{−u/2}` |
| floor-tree component | `floorTreeComponent`, `componentIndicator` | the blocks `c, 2c, 2c + 1` of `(R, R + J]` with `R ≤ c`, `R + J ≤ 3c`, `2c + 1 < 3R` |
| restricted ground state | `restrictTo` | `φ_S`, the ground vector on a set `S` of blocks and `0` off it |
| reflected packet | `reflectPacket` | `u ↦ g(c − u)` |
| pole-free profile | `poleFreeProfile` | `f₀ = U − κ(U(· + 1) + U(· − 1))`, `U` the cubic B-spline, `κ = 1/(2 cosh ½)`: even, both charges zero, it sees every zero off the line |
| states of the two ends | `twoEndOdd`, `twoEndEven` | `f₀(u + v/2) ∓ f₀(u − v/2)`: antisymmetric and symmetric copies at distance `v` |
| lag structure | `lagStructure` (SRT) | `S(v) = W(f₀, f₀(· − v))`, the zeros seen through the profile at lag `v` |
| margin bounded below | `MarginBoundedBelow C` | every plane of smooth packets on a window contains a nonzero packet with `N ≥ −C · mass` |

## 3. Language

- A **bound state** is a negative square of `N_W`; the **binding energy** is `−λ`; the **gap** is the
  least nonzero rate of the Doob chain; the **margin** is gap minus binding energy, the second
  eigenvalue of `N_W`.
- A **bottleneck** is a cut whose conductance is small against `μ π(S) π(Sᶜ)/π`; the **share** of a
  set `S` of blocks is `μ π(S)/π(W)`, the part of the binding energy its weight entitles it to.
- The **pole capacity** of a window is the largest value of the pole term on packets of unit mass.
- The **even** and **odd sectors** are the packets symmetric and antisymmetric under the reflection
  about the centre of the window (infinite block size).
- A lower bound is **self-improving** if any constant in it forces the sharp constant: a bounded
  margin forces a nonnegative one.
- The **parts** of a window are two overlapping windows that share a dyadic middle; the
  **conditional coupling** of the two ends is their coupling after the middle is eliminated.
- The **ends** of a long window are its first and last dyadic windows.
- The **tower** of a window is its family of block sizes; **infinite block size** is its limit,
  Weil's form on all packets of the logarithmic interval.
- A floor map is **shallow** if its tree has depth one in the window (`k > √ρ`), **long** if `k`
  is of the size of the ratio.

## 4. Mechanisms

**The Doob form.**
1. *Ground state transform* (`bilin_mul_eq_doob`): `N(φf, φf) = λ Σ φ_i² f_i² + E(f)`; a positive
   eigenvector belongs to the least eigenvalue (`lam_mul_sum_sq_le_bilin`); the least eigenvalue
   has a positive eigenvector when the entries off the diagonal are negative
   (`exists_pos_eigenvector`).
2. *Poincaré form of one bound state* (`hermNegIndex_le_one_iff_poincare`): at most one negative
   square iff `E(f) ≥ μ Σ φ_i² f_i²` for every `f` centred for `φ²`. RH iff this holds for the Doob
   chain of every window with `R ≤ J` (`riemannHypothesis_iff_forall_doob_poincare`); a window that
   contains a dyadic window binds its ground state (`eigenvalue_neg_of_pos_eigenvector`).
3. *Bottlenecks* (`two_le_hermNegIndex_of_bottleneck`): a cut with `C(S) π(W) < μ π(S) π(Sᶜ)` gives
   a second bound state; the test is the centred indicator of `S`.

**Gluing through the overlap.**
4. *The overlap law* (`hermNegIndex_overlapWhole_eq_iff`, `hermNegIndex_neutralWindow_overlap_eq_one_iff`):
   the dyadic middle is invertible with one bound state (`isUnit_neutralWindow_dyadic`), and by
   Haynsworth's additivity the window holds one bound state iff its two parts do and the
   conditional coupling is a contraction, `(uᵀXv)² ≤ (uᵀS₁u)(vᵀS₃v)`. Every contact and jet between
   the two ends enters only `X`. The positive cone of the two-well law is replaced by a forward
   Cauchy–Schwarz inequality on the whole space.
5. *The recursion* (`riemannHypothesis_iff_forall_overlap_contraction`): both parts are shorter than
   the window, so by induction on the length from the windows of ratio `≤ 103/50`, RH holds iff
   every conditional coupling of every window with `R ≥ 34` is a contraction. Refinement does not
   lower the index of the neutral part (`hermNegIndex_neutralWindow_le_refined`).

**The scale.**
6. *Without floor trees* (`sum_neutralBlock_one_ge`, `le_eigenvalue_of_prime_free`): the jump
   integral of the archimedean form is nonnegative because `h(x) ≤ h(0)`
   (`packetAutocorr_le_zero`), so the neutral part without contacts is at least
   `A(0) = −(γ + π/2 + log 8π)` times the mass on every window at every block size: the jets alone
   bind at most `5.4`.
7. *Each tree adds a Chebyshev term* (`sum_floorMap_le`, `sum_contact_le`, `le_eigenvalue_of_contacts`):
   a parent has at most `k` children and a child one parent, and the Schur test with weights
   `1/√k`, `√k` bounds the contact form of `k` by `2Λ(k)/√k`. So
   `−λ ≤ γ + π/2 + log 8π + 2 Σ_{2 ≤ k ≤ Q} Λ(k)/√k`.
8. *Lower bounds* (`eigenvalue_mul_harmonic_le`, `eigenvalue_le_twoEnds`): the packet `a^{−1/2}` on the
   coarsest member of the tower gains `Λ(k)/√(2k)` from the children of the root block; the packet
   on the two dyadic ends of `(R, 20mR]` gains the contacts of the floor maps of `6m ≤ k ≤ 15m`,
   which join the ends: `−λ ≥ −N(1,1) + (2/(15√(10m)))(ψ(15m) − ψ(6m))`, and Chebyshev's bounds
   (`psi_sub_psi_ge`) make this a fixed multiple of `√m`. Under RH also
   `−λ ≤ 2√(J (log(R + J) − log R)/R)` (`neg_eigenvalue_le_of_riemannHypothesis`).
   **So the binding energy of a window of ratio `ρ` has the exact order `√ρ`, and all of it but
   `5.4` is created by the floor trees, chiefly by the long floor maps that join the two ends.**
9. *The ground state at the two ends* (`sum_longMap_le`, `binding_le_short_add_long`,
   `sq_binding_excess_le`): a floor map of `k ≥ K` joins a parent with `Ka < R + J` to a child
   `b ≥ KR`, and the weighted Schur test bounds its contacts by `√k (bot/s + s·top)`. Hence
   `(μ + A(0) − 2 S_{<K})² (Σ φ²)² ≤ 4 S_{≥K}² · bot(φ) · top(φ)`, `S_{<K}`, `S_{≥K}` the Chebyshev
   sums `Σ Λ(k)/√k` below and above `K`: with `K = ρ/M` the ground state carries a fixed fraction of
   its mass within the factor `M` of each end.
10. *The pole capacity* (`blockDegree_le_inv_sqrt`, `two_mul_charges_le_poleCapacity`,
    `binding_add_packetForm_le`): the neutral part is Weil's form minus the poles
    `2 (Σ σ d)(Σ σ)`, and on unit mass the poles are at most `cap = √ρ − 1/√ρ + log ρ`
    (`poleCapacity_eq_sinh`; `d_a ≤ 1/√(a(a + 1))` is `t ≤ sinh t`). So `μ Σ φ² + W(φ) ≤ cap Σ φ²`
    without hypothesis: binding energy and Weil's form of the ground packet share the pole
    capacity. Under RH `μ ≤ √ρ − 1/√ρ + log ρ` at every block size
    (`neg_eigenvalue_le_poleCapacity_of_riemannHypothesis`), the sharp leading constant; a window
    binding beyond its capacity carries an off-line zero (`not_riemannHypothesis_of_poleCapacity_lt`).

**The margin.**
11. *Bounded margin* (`exists_doob_test_le`): on every window `(2r, 2r + J]`, `J ≥ 2r`, the refined
   plane of the blocks `(2, 3]`, `(3, 4]` carries the fixed form of these blocks; it meets the
   hyperplane orthogonal to `φ`, so some centred `f` has `E(f) ≤ (μ + c₀) Σ φ²f²`. The gap is at most
   the binding energy plus the absolute constant `c₀`. Under RH the Poincaré constant lies in
   `[μ, μ + c₀]` (`poincare_constant_mem_of_riemannHypothesis`): gap and binding energy, both of
   order `√ρ`, agree up to a bounded margin, and RH is the sign of that margin.
12. *Calibration: under RH the margin tends to zero* (`exists_plane_neutralForm_le_of_riemannHypothesis`):
    at infinite block size the neutral form is Weil's form of the zeros on the hyperplane `A = 0`,
    hence nonnegative under RH (`neutralForm_nonneg_of_charge_eq_zero`). Three copies of a fixed
    profile spread over the scale `L`, `3L` apart, have transforms `L β̂(Lγ)`; as every zero has
    `|γ| ≥ 2`, their Weil form is `O(L^{−2})` times the coefficients while their mass is `L` times
    them (`re_zetaW_threeSpread_le`, `integral_threeSpread_sq`). The first charge moves by `e^{−3L/2}`
    from copy to copy, so `a(g₀ − E g₁) + b(g₁ − E g₂)` has `A = 0` (`firstCharge_planeTest`). On
    this plane `0 ≤ N ≤ C L^{−3} · mass`: the margin of a window of length `8L` lies between `0`
    and any `ε > 0` once `L` is large.

**What the trees cannot do alone.**
13. *Components* (`floorContact_eq_zero_of_component`, `doobEnergy_component_eq_prime_free`,
    `poincare_component_of_le_one`): if `R ≤ c`, `R + J ≤ 3c` and `2c + 1 < 3R`, the parent `c`
    has no parent and no child under `k ≥ 3` in `(R, R + J]`, and its children `2c, 2c + 1` have no
    other parent and no child: the three blocks form a component of the floor trees. Such `c` exist
    for every ratio below `9/2`, about `(7R − 2J)/6` of them (`r` of them on `(6r, 24r]`,
    `component_ratio_four`). The dilation process — the Doob chain without the jets — has no gap
    below ratio `9/2`; on these indicators the Doob energy is that of the jets alone, and one bound
    state forces the jets to bind a number of components proportional to the block size.

**Cuts.**
14. *The cut law* (`doobCut_eq`, `doobCut_bottleneck_iff`): summing the eigenvalue equation over
    `S`, the conductance of a cut is `C(S) = μ π(S) + N(φ_S, φ_S)`: the binding the part receives
    from the window minus the binding it holds. So `S` is a bottleneck iff
    `−N(φ_S, φ_S)/π(S) > μ π(S)/π(W)`, i.e. iff the part binds its piece of the ground state more
    strongly than its share of the binding energy. With one bound state no part does
    (`share_law_of_hermNegIndex_le_one`), so under RH every set of blocks of every window holds at
    most its share (`share_law_of_riemannHypothesis`).

**Infinite block size.**
15. *The functional equation reflects every window* (`packetForm_reflect`, `neutralForm_reflect`):
    Weil's form depends on a packet only through its autocorrelation and the product of its
    degrees, both invariant under `u ↦ c − u`; with the translations (AGZ, `packetForm_translate`)
    the window form at infinite block size has the symmetry group of the line. The reflection of
    `[log R, log ρR]` is `x ↦ ρR²/x`; it does not preserve step packets, so it belongs to the limit
    of the tower. The shallow floor maps, `log k` at least half the window, are selective
    (`shallow_contact_selective`): they raise every packet with one node at the centre and lower
    every packet of one sign.
16. *The odd sector* (`neutralForm_of_odd`, `riemannHypothesis_iff_forall_odd_neutralForm_nonneg`):
    the reflection splits the window form into an even and an odd sector. On a packet odd about
    the centre the charges satisfy `B = −e^{c/2} A` (`integral_mul_exp_of_odd`), so the pole term
    is the square `+2 e^{c/2} A²` and `N = W + 2 e^{c/2} A²`. Under RH the odd sector carries no
    bound state; without RH an odd pole-free packet of negative Weil form exists (RHTower). So
    **RH iff the odd sector of every window is unbound**: the binding energy and the one bound
    state live in the even sector, where the pole term is a negative square of rank one, and the
    second bound state that RH excludes is odd.

**Self-improvement.**
17. *Landau from both sides* (`riemannHypothesis_of_lagStructure_le`,
    `riemannHypothesis_of_le_lagStructure`): the profile `f₀` sees every zero off the line, so a
    one-sided bound on its lag structure `S(v)`, from above or from below, forces RH. On the two
    states of the ends the neutral form is `N(f₀(· + v/2) ∓ f₀(· − v/2)) = 2 Re S(0) ∓ 2 Re S(v)`
    (`neutralForm_twoEndOdd`, `neutralForm_twoEndEven`), at mass at most `4 ∫ f₀²`. Hence **the
    odd sector is unbound iff it is bounded below by some multiple of the mass**
    (`riemannHypothesis_iff_odd_sector_bddBelow`), and the rate at which the odd states of the
    two ends sink measures the zeros: for `0 ≤ θ < ½`, every zero has `|Re ρ − ½| ≤ θ` iff
    `N(o_v) ≥ −C e^{θ v}` for all `v ≥ 0` (`zetaZeroWidth_le_iff_twoEndOdd_rate`).
18. *The margin self-improves* (`riemannHypothesis_iff_margin_bddBelow`): without RH, `S` is
    unbounded above and below, so the antisymmetric state at one lag and the symmetric state at
    another are both as deep as we like. They are odd and even about the same centre, hence
    orthogonal for the neutral form (`neutralForm_even_add_odd`: the reflection fixes the form and
    sends `e + t o` to `e − t o`) and for the mass; their plane lies below any multiple of the mass.
    **RH iff the margins of all windows are bounded below**: a second bound state is either absent
    or of unbounded depth.
19. *At finite block size* (`riemannHypothesis_iff_neutralWindow_margin_bddBelow`): RH iff for
    some `C` every window matrix `N_W + C` with `R ≤ J` has one negative square, i.e. iff the
    Poincaré constant of every Doob chain is at least its binding energy minus `C`. A lower
    bound on the step packets passes to the comb, to all divisors through the block averages, and
    to the zeros on the samples of the translated odd state
    (`riemannHypothesis_iff_packetForm_stepPacket_bddBelow`); a step packet below `−C` times its
    mass gives, on a window `(1, 2M]`, the plane of AGZ (refinement, far window, block one) on
    which `N + C` is negative (`exists_two_le_hermNegIndex_neutralWindow_add`). The windows
    `(1, 2M]` suffice (`riemannHypothesis_iff_initialWindow_margin_bddBelow`); they are the leading
    principal minors of one infinite matrix, and **RH is the finiteness of its second eigenvalue**.
    With the bounded margin (mechanism 11) the margin of the window matrices lies in `[0, c₀]`
    under RH and is unbounded below otherwise.
20. *The exponent is the abscissa* (`exists_packetForm_stepPacket_ge_sqrt`,
    `zetaZeroWidth_le_of_packetForm_stepPacket_ge`): on the step packets of a window of ratio
    `3K + 1`, Weil's form is at least `−C √K` times the mass without hypothesis (the jets bind at
    most `5.4`, the trees at most `2 Σ_{k ≤ ρ} Λ(k)/√k ≤ 68 √K`, the pole term is at least
    `−2√K` by weighted Cauchy–Schwarz). A bound `−C K^θ` with `θ < ½` forces `|Re ρ − ½| ≤ θ`
    for every zero: the transfer of mechanism 19 at one ratio controls the lag structure at the
    lags `v ≲ log K` (`two_re_lagStructure_le_of_packetForm_ge`), and the rate law of the
    antisymmetric state reads the growth `e^{θ v}`. The trivial exponent `½` is the trivial strip,
    a power saving `ρ^{½ − δ}` is the quasi-Riemann hypothesis, RH is a bounded loss.
21. *The rate of the margin* (`zetaZeroWidth_le_of_marginRate`): at infinite block size, if every
    plane of packets on `[−L, L]` contains a nonzero packet with `N ≥ −C e^{2θL}` times its mass,
    `θ < ½`, then `|Re ρ − ½| ≤ θ` for every zero. The plane pairs the antisymmetric state of the
    two ends with the **binding state** `U(· + v/2) + U(· − v/2)`, `U` the spline: its charges are
    `2 cosh(v/4) A(U)` (`charges_twoEndSpline`), so its pole term is at least `2 e^{v/2} A(U)²`,
    while its sum over the zeros is `2 Re S_U(0) + 2 Re S_U(v) = o(e^{v/2})` because every zero
    has `Re ρ < 1` (`tendsto_two_re_lagStructure_mul_exp`). Parity diagonalizes the plane also
    with charges (`neutralForm_even_add_odd_charged`). In Doob terms: a Poincaré inequality
    `gap ≥ μ − C ρ^θ` with loss `ρ^θ = o(μ)` is a zero-free strip.

## 5. Pillar theorems

| Pillar | Lean |
|---|---|
| Poincaré form of one bound state; RH as the Poincaré inequality of every Doob chain | `hermNegIndex_le_one_iff_poincare`, `riemannHypothesis_iff_forall_doob_poincare` |
| Bottleneck criterion | `two_le_hermNegIndex_of_bottleneck` |
| Overlap gluing law; RH as the contraction of every conditional coupling | `hermNegIndex_neutralWindow_overlap_eq_one_iff`, `riemannHypothesis_iff_forall_overlap_contraction` |
| Archimedean floor; Chebyshev ceiling of the binding energy | `le_eigenvalue_of_prime_free`, `le_eigenvalue_of_contacts` |
| Binding energy of order `√ρ` from the two ends | `eigenvalue_le_twoEnds`, `psi_sub_psi_ge`, `eigenvalue_mul_harmonic_le` |
| The ground state charges both ends | `sq_binding_excess_le` |
| Binding energy and Weil's form share the pole capacity; calibration: under RH `μ ≤ √ρ − 1/√ρ + log ρ` | `binding_add_packetForm_le`, `neg_eigenvalue_le_poleCapacity_of_riemannHypothesis` |
| Calibration: under RH the margin of a long window tends to zero | `exists_plane_neutralForm_le_of_riemannHypothesis` |
| RH iff the odd sector of every window carries no bound state | `riemannHypothesis_iff_forall_odd_neutralForm_nonneg` |
| The odd sector self-improves; its rate is the abscissa of the zeros | `riemannHypothesis_iff_odd_sector_bddBelow`, `zetaZeroWidth_le_iff_twoEndOdd_rate` |
| RH iff the margins are bounded below, at infinite and at finite block size; the windows `(1, 2M]` suffice | `riemannHypothesis_iff_margin_bddBelow`, `riemannHypothesis_iff_neutralWindow_margin_bddBelow`, `riemannHypothesis_iff_initialWindow_margin_bddBelow` |
| RH iff Weil's form on step packets is bounded below by a multiple of the mass | `riemannHypothesis_iff_packetForm_stepPacket_bddBelow` |
| The trivial exponent `½` of the window matrices; a saving in the exponent is a zero-free strip | `exists_packetForm_stepPacket_ge_sqrt`, `zetaZeroWidth_le_of_packetForm_stepPacket_ge` |
| A margin of exponential rate `θ < ½` is a zero-free strip (infinite block size) | `zetaZeroWidth_le_of_marginRate` |
| Bounded margin; Poincaré constant in `[μ, μ + c₀]` under RH | `exists_doob_test_le`, `poincare_constant_mem_of_riemannHypothesis` |
| Floor-tree components below ratio `9/2` | `floorContact_eq_zero_of_component`, `doobEnergy_component_eq_prime_free`, `poincare_component_of_le_one` |
| The cut law; under RH every part holds at most its share of the binding | `doobCut_eq`, `doobCut_bottleneck_iff`, `share_law_of_riemannHypothesis` |
| Reflection symmetry at infinite block size | `packetForm_reflect`, `neutralForm_reflect` |

## 6. Questions

| # | Question | Status |
|---|---|---|
| 1 | **B192**: one bound state of `(R, 3R]`, `(R, 4R]` at every block size from the true contacts of `2`, `3` | open; worked in AGZ. In MAFT terms: the conditional coupling of the overlap with dyadic middle `(3R/2, 2R]` is a contraction |
| 2 | Which cut is the bottleneck | exact criterion: `S` is a bottleneck iff its part binds more than its share `μ π(S)/π(W)` (`doobCut_bottleneck_iff`); under RH no part does; at large ratio the ground state charges both ends (`sq_binding_excess_le`); the cut of a window of ratio three is open |
| 3 | Comparison of a window with its parts through the floor trees | answered by the overlap law: exact, of full rank, with the trees between the ends in `X` |
| 4 | A curvature bound for the floor trees | open |
| 5 | The gap of the dilation process | answered below ratio `9/2`: zero, with a number of components of three blocks proportional to the block size; the mixing that RH needs on them comes from the jets; from ratio `9/2` on these components disappear and the gap is open |
| 6 | Does the margin have a limit along the ratios; does a uniform lower bound force RH | a uniform lower bound forces RH, at infinite block size (`riemannHypothesis_iff_margin_bddBelow`) and for the window matrices (`riemannHypothesis_iff_neutralWindow_margin_bddBelow`); calibration: under RH the margin lies in `[0, c₀]` and tends to `0` at infinite block size; the limit at finite block size is open |
| 7 | The order of the binding energy and which floor maps carry it | answered: `√ρ`; carried by the long floor maps joining the two ends; under RH at most the pole capacity `√ρ − 1/√ρ + log ρ`; the unconditional leading constant is open |
| 8 | A recursion along doublings | answered in overlap form: a window reduces to two shorter parts and one contraction; the balanced split sends the ratio `ρ` to `2(1 + ρ)/3` and `3ρ/(1 + ρ)` |
| 9 | Which exponent `θ` in `𝔚 ≥ −C ρ^θ` on the step packets of ratio `ρ`, or in a margin `−C ρ^θ`, is true | `θ = ½` for `𝔚` unconditionally (`exists_packetForm_stepPacket_ge_sqrt`); `θ < ½` implies the zero-free strip `|Re ρ − ½| ≤ θ`, for `𝔚` on step packets (`zetaZeroWidth_le_of_packetForm_stepPacket_ge`) and for the margin at infinite block size (`zetaZeroWidth_le_of_marginRate`); RH is `θ = 0`; any `θ < ½` is open |

## 7. Tools

**Developed.** The Doob chain of a symmetric Metzler matrix with its Perron vector; the Poincaré and
bottleneck forms of one bound state; real Haynsworth additivity for block matrices with transposed
couplings; the overlap decomposition of a window with its reindexing; refinement monotonicity of
the neutral index; the archimedean floor through the Lévy representation; the weighted Schur test
for floor maps; the root and two-end packets with Chebyshev's bounds; the refined coarse plane;
floor-tree components; the long-map Schur test between bottom and top; the pole capacity through
`t ≤ sinh t`; the cut law; reflection of packets and the parity split; spread copies of a profile
and the zero sum under RH with `|γ| ≥ 2`; the pole-free profile and the states of the two ends;
Landau's argument from both sides on a lag structure; the transfer of a fixed lower bound from
step packets through the comb to the zeros; the plane of AGZ with the mass.

**To build.** The Doob chain at infinite block size as an operator; canonical paths and comparison of
Dirichlet forms across the dyadic cuts; transfer of infinite-block-size statements to large block
sizes through the smoothing of step packets (AGZ, `tendsto_packetForm_mollify`); quantitative
versions of the overlap law (margins of `S₁`, `S₃` and the norm of `X`).

## 8. Traps

| Trap | Truth |
|---|---|
| The floor trees mix by themselves | Below ratio `9/2` they split into components of three blocks; the dilation process has no gap |
| The jets carry the binding | Without the trees the binding energy is at most `γ + π/2 + log 8π`; with them it grows like `√ρ` |
| The prime `2` decides every ratio | At large ratio the binding is carried by the long floor maps of integers of the size of the ratio |
| A bounded number of test functions across a cut decides | The binding has rank proportional to the block size (AGZ); the components below ratio `9/2` are proportional to the block size |
| Gap and binding energy are of different orders | Both are of order `√ρ` and differ by at most `c₀`: only the sign of a bounded margin is at stake |
| RH leaves room: the margin is bounded away from zero | Under RH the margin of long windows tends to `0` at infinite block size; no argument can rest on a uniform positive margin |
| The binding energy may reach the Chebyshev ceiling `4√ρ` | Under RH it is at most the pole capacity `√ρ − 1/√ρ + log ρ`; the trees reproduce the pole |
| Gluing needs the positive cone | Through a dyadic middle the two-well inequality becomes a forward contraction on the whole space |
| A Cheeger bound suffices | Cheeger loses a square, and the margin is bounded: only constants matter |
| The Poincaré inequality must be proved with the sharp constant | An additive loss is free: gap `≥ μ − C` for one `C` and all windows forces gap `≥ μ` |
| A deep second bound state can be confined to a few windows | The margin self-improves: a second bound state of one window forces second bound states of unbounded depth |
| The reflection acts on step packets | It maps unit blocks to reciprocal blocks; it is a symmetry of the limit only |

## 9. Open research topics

- The contraction of the conditional coupling at ratio three (B192) and at the balanced split of
  every ratio; norms of `X` against `S₁`, `S₃`.
- The converse of the exponent laws: whether `|Re ρ − ½| ≤ θ` gives `𝔚 ≥ −C ρ^θ` on the step
  packets of ratio `ρ`, or a margin `−C ρ^θ`.
- The rate of the margin at finite block size: the plane of the binding state and the
  antisymmetric state transferred to the window matrices (the plane of AGZ lives on windows of
  unbounded ratio and does not see the rate); the block averages of the comb give the needed
  one-sided bound.
- Strategies with an additive loss: a comparison or path argument that proves gap `≥ μ − C`
  suffices; which of the known losses (the margin bound `c₀`, the archimedean floor `5.4`, the
  overlap contraction) are additive.
- The unconditional leading constant of the binding energy: the pole profile `e^{±u/2}` on the two
  ends against the prime number theorem; the deficit `cap − μ` as a reading of the zeros.
- The shape of the ground state between the two ends.
- Curvature of the Doob chain; canonical paths through the long floor maps.
- The odd sector at finite block size: the reflection does not preserve step packets, so the
  parity split holds only in the limit of the tower; which floor maps decide the odd sector.

## 10. Context

| Programme | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ (AGZ) | the block matrix, neutral part, tower, certified windows, rank law, weakened contacts, two-well law, packet form |
| HTGeometry | Hermitian inertia, Sylvester, Haynsworth |
| ArithmeticLorentzianGeometry (ALG) | Metzler forms and trickle-down |
| SelectiveArithmetic (SA), HodgeTheoryOfAFixedPart (HFP) | selective weights; the pairing at finite scale |
| SelectivePositivityAndThresholdLaws (SPTL) | parity sectors and the selective refutation below `103/50` |
| LatticeSectionTheory (LST) | the regional logarithmic spectrum of the jets |
| RHTower | the Lévy density and the constant `A(0)` of the archimedean form; the odd and even pole-weight windows (`WeilParityPoleWeightWindows`), of which the odd-sector law is the case `β = 0`; the zeros have ordinate at least `2` |
| SquareRootThreshold (SRT) | tempered zero configurations; RH as the critical-line property of the zero configuration; lag structures, two-bump tests and Landau's argument from above |
| SurfaceOfSpecZ | Landau's argument from below on the lag structure |
| HodgeTheoryOfAFixedPart (HFP) | the comb at finite scale: samples of packets, block averages, the limit to the zeros |
| ArithmeticOrientationGeometry (AOG) | one generic orbit decides RH; the negative index of Weil Gram matrices on translates counts the zeros right of the line, the natural route to a converse of the vanishing margin |

## 11. Success criteria

The field is developed when the Doob chain of every window is a Lean object with its inertia law
(done); the scale of binding energy and gap is proved (done up to constants, and under RH the
upper constant is the pole capacity); the comparison of a
window with its parts is exact (done); cut, curvature and path methods are each either proved to
give the gap or refuted by a theorem calibrated on twisted contacts; and the questions of §6 are
answered or reduced to named estimates.

## 12. What a contribution must be

- **X1** a statement about the chain, proved without the zeros.
- **X2** consistent with the calibration: gap `≥` energy on the certified windows; gap `<` energy at
  ratio four with the weights of `2` and `3` in `[−5/2, 19/40]` and for the Liouville twist.
- **X3** no bound through a bounded number of test functions across a dyadic cut.
- **X4** stable under refinement of the blocks: at every block size or at infinite block size.
- **X5** every inequality names the tree edges it uses.
- **X6** it reproduces the curve case, in which the trickle-down inequality on Frobenius ladders is
  the one-sided point count (ALG).
