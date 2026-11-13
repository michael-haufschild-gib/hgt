# Mixing Arithmetic of the Floor Trees (MAFT)

Namespace `GaloisForLFunctions.MixingArithmeticOfTheFloorTrees`; umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Specification: §2.9 of
[the review-1311 summary](../../../docs/reports/review-1311/obstacles-summary.md). Programme card:
`docs/drafts/pipeline/1-in-progress/maft-mixing-arithmetic-of-the-floor-trees.md`.

Every theorem named here is proved in Lean without hypothesis. **AGZ**, **LST**, … mark theorems of
other folders, **[C]** published mathematics not in the corpus, **open** a statement not proved.

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
| floor-tree component | `floorTreeComponent`, `componentIndicator` | the blocks `c, 2c, 2c + 1` of `(6r, 24r]`, `8r ≤ c < 9r` |
| reflected packet | `reflectPacket` | `u ↦ g(c − u)` |

## 3. Language

- A **bound state** is a negative square of `N_W`; the **binding energy** is `−λ`; the **gap** is the
  least nonzero rate of the Doob chain; the **margin** is gap minus binding energy, the second
  eigenvalue of `N_W`.
- A **bottleneck** is a cut whose conductance is small against `μ π(S) π(Sᶜ)/π`.
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

**The margin.**
9. *Bounded margin* (`exists_doob_test_le`): on every window `(2r, 2r + J]`, `J ≥ 2r`, the refined
   plane of the blocks `(2, 3]`, `(3, 4]` carries the fixed form of these blocks; it meets the
   hyperplane orthogonal to `φ`, so some centred `f` has `E(f) ≤ (μ + c₀) Σ φ²f²`. The gap is at most
   the binding energy plus the absolute constant `c₀`. Under RH the Poincaré constant lies in
   `[μ, μ + c₀]` (`poincare_constant_mem_of_riemannHypothesis`): gap and binding energy, both of
   order `√ρ`, agree up to a bounded margin, and RH is the sign of that margin.

**What the trees cannot do alone.**
10. *Components* (`floorContact_eq_zero_of_component`, `doobEnergy_component_eq_prime_free`,
    `poincare_component_of_le_one`): on `(6r, 24r]` only the trees of `2` and `3` act, and the
    blocks `c, 2c, 2c + 1`, `8r ≤ c < 9r`, form `r` components of the floor trees. The dilation
    process — the Doob chain without the jets — has no gap; on these indicators the Doob energy is
    that of the jets alone, and one bound state at ratio four forces the jets to bind `r` components,
    a number proportional to the block size.

**Infinite block size.**
11. *The functional equation reflects every window* (`packetForm_reflect`, `neutralForm_reflect`):
    Weil's form depends on a packet only through its autocorrelation and the product of its
    degrees, both invariant under `u ↦ c − u`; with the translations (AGZ, `packetForm_translate`)
    the window form at infinite block size has the symmetry group of the line. The reflection of
    `[log R, log ρR]` is `x ↦ ρR²/x`; it does not preserve step packets, so it belongs to the limit
    of the tower.

## 5. Pillar theorems

| Pillar | Lean |
|---|---|
| Poincaré form of one bound state; RH as the Poincaré inequality of every Doob chain | `hermNegIndex_le_one_iff_poincare`, `riemannHypothesis_iff_forall_doob_poincare` |
| Bottleneck criterion | `two_le_hermNegIndex_of_bottleneck` |
| Overlap gluing law; RH as the contraction of every conditional coupling | `hermNegIndex_neutralWindow_overlap_eq_one_iff`, `riemannHypothesis_iff_forall_overlap_contraction` |
| Archimedean floor; Chebyshev ceiling of the binding energy | `le_eigenvalue_of_prime_free`, `le_eigenvalue_of_contacts` |
| Binding energy of order `√ρ` from the two ends | `eigenvalue_le_twoEnds`, `psi_sub_psi_ge`, `eigenvalue_mul_harmonic_le` |
| Bounded margin; Poincaré constant in `[μ, μ + c₀]` under RH | `exists_doob_test_le`, `poincare_constant_mem_of_riemannHypothesis` |
| Floor-tree components at ratio four | `doobEnergy_component_eq_prime_free`, `poincare_component_of_le_one` |
| Reflection symmetry at infinite block size | `packetForm_reflect`, `neutralForm_reflect` |

## 6. Questions

| # | Question | Status |
|---|---|---|
| 1 | **B192**: one bound state of `(R, 3R]`, `(R, 4R]` at every block size from the true contacts of `2`, `3` | open; worked in AGZ. In MAFT terms: the conditional coupling of the overlap with dyadic middle `(3R/2, 2R]` is a contraction |
| 2 | Which cut is the bottleneck | tool: the bottleneck criterion; at large ratio the binding sits on the two ends, so the cut between them carries the conductance of the long floor maps; the cut of a window of ratio three is open |
| 3 | Comparison of a window with its parts through the floor trees | answered by the overlap law: exact, of full rank, with the trees between the ends in `X` |
| 4 | A curvature bound for the floor trees | open |
| 5 | The gap of the dilation process | answered at ratio four: zero, with at least `r` components at block size `6r`; the mixing that RH needs on them comes from the jets |
| 6 | Does the margin have a limit along the ratios | it is bounded above by `c₀` on every window; under RH it lies in `[0, c₀]` while gap and binding energy grow like `√ρ`; whether its limit is `0` is open |
| 7 | The order of the binding energy and which floor maps carry it | answered: `√ρ`; carried by the long floor maps joining the two ends |
| 8 | A recursion along doublings | answered in overlap form: a window reduces to two shorter parts and one contraction; the balanced split sends the ratio `ρ` to `2(1 + ρ)/3` and `3ρ/(1 + ρ)` |

## 7. Tools

**Developed.** The Doob chain of a symmetric Metzler matrix with its Perron vector; the Poincaré and
bottleneck forms of one bound state; real Haynsworth additivity for block matrices with transposed
couplings; the overlap decomposition of a window with its reindexing; refinement monotonicity of
the neutral index; the archimedean floor through the Lévy representation; the weighted Schur test
for floor maps; the root and two-end packets with Chebyshev's bounds; the refined coarse plane;
floor-tree components; reflection of packets.

**To build.** The Doob chain at infinite block size as an operator; canonical paths and comparison of
Dirichlet forms across the dyadic cuts; a parity decomposition of the index at infinite block size;
quantitative versions of the overlap law (margins of `S₁`, `S₃` and the norm of `X`).

## 8. Traps

| Trap | Truth |
|---|---|
| The floor trees mix by themselves | At ratio four they split into components of three blocks; the dilation process has no gap |
| The jets carry the binding | Without the trees the binding energy is at most `γ + π/2 + log 8π`; with them it grows like `√ρ` |
| The prime `2` decides every ratio | At large ratio the binding is carried by the long floor maps of integers of the size of the ratio |
| A bounded number of test functions across a cut decides | The binding has rank proportional to the block size (AGZ); the components at ratio four are proportional to the block size |
| Gap and binding energy are of different orders | Both are of order `√ρ` and differ by at most `c₀`: only the sign of a bounded margin is at stake |
| Gluing needs the positive cone | Through a dyadic middle the two-well inequality becomes a forward contraction on the whole space |
| A Cheeger bound suffices | Cheeger loses a square, and the margin is bounded: only constants matter |
| The reflection acts on step packets | It maps unit blocks to reciprocal blocks; it is a symmetry of the limit only |

## 9. Open research topics

- The contraction of the conditional coupling at ratio three (B192) and at the balanced split of
  every ratio; norms of `X` against `S₁`, `S₃`.
- The limit of the margin along the ratios; whether a uniform lower bound on the margin already
  forces RH (an off-line zero should drive the margin of long windows to `−∞` at the rate
  `e^{(β − 1/2) log ρ}`).
- The ground state of a long window: concentration of `φ²` on the two ends.
- Curvature of the Doob chain; canonical paths through the long floor maps.
- The parity sectors of the window form at infinite block size and the sign of the shallow floor
  maps on them.

## 10. Context

| Programme | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ (AGZ) | the block matrix, neutral part, tower, certified windows, rank law, weakened contacts, two-well law, packet form |
| HTGeometry | Hermitian inertia, Sylvester, Haynsworth |
| ArithmeticLorentzianGeometry (ALG) | Metzler forms and trickle-down |
| SelectiveArithmetic (SA), HodgeTheoryOfAFixedPart (HFP) | selective weights; the pairing at finite scale |
| SelectivePositivityAndThresholdLaws (SPTL) | parity sectors and the selective refutation below `103/50` |
| LatticeSectionTheory (LST) | the regional logarithmic spectrum of the jets |
| RHTower | the Lévy density and the constant `A(0)` of the archimedean form |

## 11. Success criteria

The field is developed when the Doob chain of every window is a Lean object with its inertia law
(done); the scale of binding energy and gap is proved (done up to constants); the comparison of a
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
