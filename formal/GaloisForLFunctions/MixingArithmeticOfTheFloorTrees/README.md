# Mixing Arithmetic of the Floor Trees (MAFT)

Namespace `GaloisForLFunctions.MixingArithmeticOfTheFloorTrees`; umbrella
`MixingArithmeticOfTheFloorTrees.lean`; 21 modules.

Every theorem named here is proved in Lean without added hypotheses. A theorem named
`…_of_riemannHypothesis` has RH as its stated antecedent and is **calibration**: it says what a
proof must produce, not how to produce it. Theorems of other programmes are marked by their
programme (AGZ, SRT, …).

## 1. Motivation

At finite scale the Riemann hypothesis is a statement about one explicit symmetric matrix per
window. Cut a window `W = (R, R + J]` into unit blocks `(a, a + 1]`. Weil's form of a step packet
on these blocks is twice the product of its two charges plus a quadratic form `N_W`, the
**neutral part**. Off the diagonal `N_W` is minus two kinds of contact: the **jets**, which join
every pair of blocks through the archimedean place, and the **floor maps** `b ↦ ⌊b/k⌋`, which join
a block to its parent under division by `k` with the weight `Λ(k)/k`. RH holds iff `N_W` has
exactly one negative square on every window with `R ≤ J` (AGZ).

Three facts about this matrix fix the shape of any proof. Its induction step has full rank: the
binding of two halves has rank proportional to the block size. It is selective: weakened or
twisted contacts produce a second bound state. It is cooperative: every entry off the diagonal is
negative. A symmetric matrix with negative off-diagonal entries is minus the generator of a
positive dynamics. Conjugation by its positive ground vector `φ` turns `N_W` into a reversible
Markov chain on the blocks, the **Doob chain** of the window, shifted by the depth `μ_W` of the
ground state. RH at a window becomes a Poincaré inequality:

> *the spectral gap of the Doob chain of every window is at least its binding energy.*

MAFT studies these chains: their gaps, their binding energies, their cuts, how a window's chain
compares with the chains of its parts, and their limit at infinite block size, where the floor
tree of `k` becomes the dilation `x ↦ kx`. The programme turns RH into a mixing problem and asks
which part of the arithmetic does the mixing.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window, neutral part | `neutralWindow Q R J` (AGZ) | blocks `R, …, R + J − 1`, ratio `ρ = (R + J)/R`, contacts of `k ≤ Q` |
| Ground vector, binding energy | `exists_pos_eigenvector`, `exists_groundVector_neutralWindow` | `φ > 0` with `N φ = λ φ`; `μ = −λ` |
| Doob chain | `doobConductance`, `doobEnergy`, `doobMean`, `doobMass` | weights `φ_i²`, conductances `c_{ij} = −N_{ij} φ_i φ_j`, Dirichlet form `E` |
| Cut | `doobWeight`, `doobCut`, `restrictTo` | `π(S)`, `C(S) = Σ_{i ∈ S, j ∉ S} c_{ij}`, the ground vector restricted to `S` |
| Overlap of a window | `overlapWhole`, `overlapLeftEnergy`, `overlapRightEnergy`, `overlapCoupling` | left end, dyadic middle, right end; the Schur complements `S₁`, `S₃` over the middle and the conditional coupling `X` |
| Pole capacity | `poleCapacity R J` | `√ρ − 1/√ρ + log ρ`, the largest pole term on packets of unit mass |
| Ends of a long window | `bottomMass`, `topMass` | the mass of `φ` within a factor `K` of the bottom and of the top |
| Margin bound | `marginBound Q` | the absolute constant `c₀` of the blocks `(2, 3]`, `(3, 4]` |
| Floor-tree component | `floorTreeComponent`, `componentIndicator` | three blocks `c, 2c, 2c + 1` joined to nothing else by the trees |
| Pole-free profile | `poleFreeProfile` | `f₀ = U − κ(U(· + 1) + U(· − 1))`, `U` the cubic B-spline: even, both charges zero, it sees every zero off the line |
| States of the two ends | `twoEndOdd`, `twoEndEven`, `twoEndSpline` | `f₀(u + v/2) ∓ f₀(u − v/2)`; the binding state `U(u + v/2) + U(u − v/2)` |
| Lag structure | `lagStructure` (SRT) | `S(v) = W(f₀, f₀(· − v))`: the zeros seen through the profile at lag `v` |
| Margin hypotheses | `MarginBoundedBelow`, `MarginRate` | every plane of packets on a window has a nonzero packet with `N ≥ −C` (resp. `−C ρ^θ`) times its mass |
| Dilation process | `dilationForm`, `dilationVar` | the floor trees at infinite block size: `x → kx` at rate `Λ(k)`, back at `Λ(k)/k`, reversible for `dx` on `(1, Q]` |
| Jump calculus | `jumpGen`, `carre`, `gammaTwo`, `treeJumps`, `treeRate`, `treeJump` | the generator `Σ w_i (f(u + a_i) − f(u))`, its carré du champ `Γ` and its iterate `Γ₂` |

## 3. Language

- A **bound state** is a negative square of `N_W`. The **binding energy** `μ` is the depth of the
  ground state. The **gap** is the least nonzero rate of the Doob chain. The **margin** is the gap
  minus the binding energy, i.e. the second eigenvalue of `N_W`.
- A **bottleneck** is a cut whose conductance is small against `μ π(S) π(Sᶜ)/π(W)`. The **share**
  of a set `S` of blocks is `μ π(S)/π(W)`, the part of the binding energy its weight entitles it
  to.
- The **parts** of a window are two overlapping windows that share a dyadic middle. The
  **conditional coupling** of the two ends is their coupling after the middle is eliminated.
- The **ends** of a long window are its first and last dyadic stretches. A floor map is **long**
  if `k` is of the size of the ratio, so that it joins the two ends.
- The **tower** of a window is the family of its block sizes. **Infinite block size** is the
  limit of the tower: Weil's form on all packets of the logarithmic interval.
- The **even** and **odd sectors** are the packets symmetric and antisymmetric about the centre
  of the window, at infinite block size.
- A lower bound is **self-improving** if any constant in it forces the sharp constant. Its
  **rate** is the exponent `θ` of a loss `C ρ^θ`.
- A **common return** is a frequency `t` at which every rotation `t log k`, `k ≤ Q`, is close
  to `2πℤ`.

## 4. Mechanisms

### 4.1 RH is a Poincaré inequality

The ground state transform `N(φf, φf) = λ Σ φ_i² f_i² + E(f)` (`bilin_mul_eq_doob`) writes the
neutral part as the binding energy plus a Dirichlet form. A positive eigenvector belongs to the
least eigenvalue, and one exists because the matrix is cooperative (`exists_pos_eigenvector`).
So `N_W` has at most one negative square iff `E(f) ≥ μ Σ φ_i² f_i²` for every `f` centred for
`φ²` (`hermNegIndex_le_one_iff_poincare`). RH iff this holds for the chain of every window with
`R ≤ J` (`riemannHypothesis_iff_forall_doob_poincare`).

Cuts are governed by one identity. Summing the eigenvalue equation over `S` gives
`C(S) = μ π(S) + N(φ_S, φ_S)` (`doobCut_eq`): a cut conducts the binding its part receives from
the window minus the binding the part holds by itself. So `S` is a bottleneck iff its part binds
its piece of the ground state more strongly than its share (`doobCut_bottleneck_iff`). A
bottleneck gives a second bound state (`two_le_hermNegIndex_of_bottleneck`). Under one bound
state no part exceeds its share (`share_law_of_hermNegIndex_le_one`).

### 4.2 A window is glued from its parts through its dyadic middle

The neutral part on a dyadic window is invertible with one bound state
(`isUnit_neutralWindow_dyadic`). Haynsworth additivity over this middle gives the **overlap law**
(`hermNegIndex_neutralWindow_overlap_eq_one_iff`): a window holds one bound state iff its two
parts do and the conditional coupling is a contraction, `(uᵀXv)² ≤ (uᵀS₁u)(vᵀS₃v)`. Every contact
and every jet between the two ends enters only `X`. The positive cone of the two-well law becomes
a Cauchy–Schwarz inequality on the whole space. Both parts are shorter than the window, so
induction from the windows of ratio `≤ 103/50` gives: RH iff every conditional coupling of every
window with `R ≥ 34` is a contraction (`riemannHypothesis_iff_forall_overlap_contraction`).
Refinement of the blocks never lowers the index (`hermNegIndex_neutralWindow_le_refined`).

### 4.3 The floor trees create the binding, at the scale √ρ

Without floor maps the binding is bounded. The jump integral of the archimedean form is
nonnegative because the Lévy kernel `h` satisfies `h(x) ≤ h(0)`, so the jets alone bind at most
`γ + π/2 + log 8π < 5.4` at every block size (`le_eigenvalue_of_prime_free`). Each floor map adds
at most a Chebyshev term. A parent has at most `k` children and a child has one parent, so the
Schur test with weights `1/√k`, `√k` bounds the contacts of `k` by `2Λ(k)/√k`
(`le_eigenvalue_of_contacts`).

The long maps reach this order. On the two dyadic ends of `(R, 20mR]`, the floor maps of
`6m ≤ k ≤ 15m` join bottom to top, and Chebyshev's lower bound turns their contacts into a fixed
multiple of `√m` (`eigenvalue_le_twoEnds`, `psi_sub_psi_ge`). **The binding energy of a window of
ratio `ρ` has the exact order `√ρ`, and all but a bounded part of it is created by the long floor
maps that join the two ends.** The ground state follows the binding. A weighted Schur test on the
long maps gives `(μ + A(0) − 2S_{<K})² ≤ 4 S_{≥K}² · bot(φ) · top(φ)` (`sq_binding_excess_le`), so
`φ` carries a fixed fraction of its mass near each end.

The binding has a ceiling read from the pole. The neutral part is Weil's form minus the pole term
`2(Σσd)(Σσ)`, and on unit mass the pole term is at most the pole capacity: `d_a ≤ 1/√(a(a + 1))`
is the inequality `t ≤ sinh t` (`two_mul_charges_le_poleCapacity`). Hence
`μ Σφ² + W(φ) ≤ cap · Σφ²` without hypothesis (`binding_add_packetForm_le`): binding energy and
Weil's form of the ground packet share the capacity. Under RH `μ ≤ √ρ − 1/√ρ + log ρ`
(`neg_eigenvalue_le_poleCapacity_of_riemannHypothesis`), and a window that binds beyond its
capacity carries an off-line zero (`not_riemannHypothesis_of_poleCapacity_lt`).

### 4.4 Only the sign of a bounded margin is at stake, and any loss is a zero-free strip

*The margin is bounded above.* On every window `(2r, 2r + J]` with `J ≥ 2r`, the refined plane of
the blocks `(2, 3]`, `(3, 4]` meets the hyperplane orthogonal to `φ`. Some centred `f` therefore
has `E(f) ≤ (μ + c₀) Σφ²f²` (`exists_doob_test_le`): gap `≤ μ + c₀`, with `c₀` absolute. Gap and
binding energy are both of order `√ρ` and differ by a bounded amount. Calibration: under RH the
margin lies in `[0, c₀]` (`poincare_constant_mem_of_riemannHypothesis`) and tends to `0` on long
windows at infinite block size (`exists_plane_neutralForm_le_of_riemannHypothesis`). There, three
spread copies of one profile have Weil form `O(L^{−2})` against mass `L`, since every zero has
ordinate at least `2`.

*The margin is self-improving.* The profile `f₀` sees every zero off the line, so Landau's
argument works from both sides. A one-sided bound on the lag structure `S(v)`, from above or from
below, forces RH (`riemannHypothesis_of_lagStructure_le`, `riemannHypothesis_of_le_lagStructure`).
The two states of the ends realize `S`: `N(f₀(· + v/2) ∓ f₀(· − v/2)) = 2 Re S(0) ∓ 2 Re S(v)` at
bounded mass (`neutralForm_twoEndOdd`, `neutralForm_twoEndEven`). Without RH both states are as
deep as we like at suitable lags. One is odd and the other even about the same centre, so they are
orthogonal for the neutral form (`neutralForm_even_add_odd`) and for the mass. Their plane lies
below any multiple of the mass. **RH iff the margins are bounded below**
(`riemannHypothesis_iff_margin_bddBelow`): a second bound state is absent or of unbounded depth.

*The same holds for the window matrices.* A lower bound on step packets passes through the comb
to all divisors and, through the block averages, to the zeros
(`riemannHypothesis_iff_packetForm_stepPacket_bddBelow`). Conversely, a step packet below `−C`
times its mass yields, on a window `(1, 2M]`, a plane on which `N + C` is negative
(`exists_two_le_hermNegIndex_neutralWindow_add`). So RH iff for some `C` every `N_W + C` has one
negative square (`riemannHypothesis_iff_neutralWindow_margin_bddBelow`), and the initial windows
`(1, 2M]` suffice (`riemannHypothesis_iff_initialWindow_margin_bddBelow`). These are the leading
principal minors of one infinite matrix: **RH is the finiteness of its second eigenvalue.** In
Doob terms, gap `≥ μ − C` on all windows forces gap `≥ μ`
(`riemannHypothesis_iff_forall_doob_poincare_sub`).

*The rate of the loss is the abscissa of the zeros.* Unconditionally, Weil's form on step packets
of ratio `3K + 1` is at least `−C√K` times the mass (`exists_packetForm_stepPacket_ge_sqrt`). The
jets cost a constant, the trees `O(√K)`, and the pole term at least `−2√K`. A loss `C K^θ` with
`θ < ½` confines every zero to `|Re ρ − ½| ≤ θ`
(`zetaZeroWidth_le_of_packetForm_stepPacket_ge`). The same law holds for the margin
(`zetaZeroWidth_le_of_marginRate`): pair the antisymmetric state of the ends with the binding state
of the spline. Its charges are `2 cosh(v/4) A(U)` (`charges_twoEndSpline`), so its pole term grows
like `e^{v/2}`, while its zero sum is `o(e^{v/2})` because every zero has `Re ρ < 1`
(`tendsto_two_re_lagStructure_mul_exp`). Parity diagonalizes the plane even with charges
(`neutralForm_even_add_odd_charged`). For the window matrices: if `N_W + C K^θ` has one negative
square on every window of ratio `3K + 1`, every zero has `|Re ρ − ½| ≤ θ`
(`zetaZeroWidth_le_of_neutralWindow_marginRate`). Samples, block averages and block functions
carry the plane to the comb uniformly on all divisors. The trivial exponent `½` is the trivial
strip, a saving `ρ^{½ − δ}` is a quasi-Riemann hypothesis, and RH is a bounded loss.

### 4.5 The functional equation splits every window into two sectors

Weil's form depends on a packet only through its autocorrelation and the product of its degrees,
and both are invariant under `u ↦ c − u` (`packetForm_reflect`, `neutralForm_reflect`). With the
translations this gives the window form at infinite block size the symmetry group of the line. The
reflection of `[log R, log ρR]` is `x ↦ ρR²/x`, which does not preserve step packets, so the
splitting belongs to the limit of the tower. On a packet odd about the centre the charges satisfy
`B = −e^{c/2}A` (`integral_mul_exp_of_odd`), so the pole term is the positive square `2e^{c/2}A²`.
**RH iff the odd sector of every window is unbound**
(`riemannHypothesis_iff_forall_odd_neutralForm_nonneg`). The ground state lives in the even
sector, where the pole term is a negative square of rank one, and the second bound state that RH
excludes would be odd. The odd sector self-improves (`riemannHypothesis_iff_odd_sector_bddBelow`),
and its rate measures the zeros exactly: for `0 ≤ θ < ½`, `|Re ρ − ½| ≤ θ` for every zero iff
`N(o_v) ≥ −C e^{θv}` for all `v ≥ 0` (`zetaZeroWidth_le_iff_twoEndOdd_rate`).

### 4.6 The floor trees bind but do not mix

*Below ratio `9/2` they fall apart.* If `R ≤ c`, `R + J ≤ 3c` and `2c + 1 < 3R`, the blocks
`c, 2c, 2c + 1` form a component of the floor trees of `(R, R + J]`
(`floorContact_eq_zero_of_component`). Such `c` exist at every ratio below `9/2`, in number
proportional to the block size. On their indicators the Doob energy is that of the jets alone
(`doobEnergy_component_eq_prime_free`). One bound state therefore forces the jets to bind a number
of components proportional to the block size (`poincare_component_of_le_one`).

*At infinite block size they have no gap, for every `Q`.* By Dirichlet's simultaneous
approximation there are arbitrarily high frequencies `t` at which every rotation `t log k`,
`k ≤ Q`, returns close to `2πℤ`. There the wave `cos(t log x)` is moved by no floor map, while it
keeps a quarter of the mass as variance (`dilationForm_le_of_no_gap`). The common returns are the
frequencies at which `Σ_{k ≤ Q} Λ(k) k^{it}` is near its maximum `ψ(Q)`.

*Their curvature is exactly zero.* The dilation process is a translation-invariant jump process
in `u = log x`. Its iterated carré du champ is a sum of squares of second differences,
`Γ₂(f) = ¼ Σ_{i,j} w_i w_j (Δ_iΔ_j f)²`, because the cross terms cancel under the exchange of the
two jumps (`gammaTwo_eq`). So `CD(0, ∞)` holds (`gammaTwo_nonneg`). No `CD(κ, ∞)` with `κ > 0`
holds (`not_curvature_pos`): on a wave plus a linear function at a common return, the linear part
keeps `Γ` away from zero and has no second differences, while the wave's second differences are
`O(η²)`.

Together: the trees create the binding energy but none of the mixing. **Whatever spectral gap
the Doob chains have must come from the jets, at the frequencies where the prime rotations
resonate.**

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Poincaré form of one bound state; RH as the Poincaré inequality of every Doob chain | `hermNegIndex_le_one_iff_poincare`, `riemannHypothesis_iff_forall_doob_poincare` | equivalence |
| Cut law and bottleneck criterion | `doobCut_eq`, `doobCut_bottleneck_iff`, `two_le_hermNegIndex_of_bottleneck` | unconditional |
| Overlap law; RH as the contraction of every conditional coupling | `hermNegIndex_neutralWindow_overlap_eq_one_iff`, `riemannHypothesis_iff_forall_overlap_contraction` | unconditional; equivalence |
| Archimedean floor and Chebyshev ceiling of the binding energy | `le_eigenvalue_of_prime_free`, `le_eigenvalue_of_contacts` | unconditional |
| Binding energy of order `√ρ`, carried by the long maps; the ground state charges both ends | `eigenvalue_le_twoEnds`, `sq_binding_excess_le` | unconditional |
| Binding energy and Weil's form share the pole capacity | `binding_add_packetForm_le` | unconditional |
| Gap at most binding energy plus an absolute constant | `exists_doob_test_le` | unconditional |
| RH iff the margins are bounded below, at infinite and at finite block size; the initial windows suffice | `riemannHypothesis_iff_margin_bddBelow`, `riemannHypothesis_iff_neutralWindow_margin_bddBelow`, `riemannHypothesis_iff_initialWindow_margin_bddBelow` | equivalence |
| Exponent `½` of the window matrices; a margin of rate `θ < ½` is the zero-free strip of width `θ` | `exists_packetForm_stepPacket_ge_sqrt`, `zetaZeroWidth_le_of_marginRate`, `zetaZeroWidth_le_of_neutralWindow_marginRate` | unconditional |
| Reflection; RH iff the odd sector is unbound; the odd rate is the abscissa | `neutralForm_reflect`, `riemannHypothesis_iff_forall_odd_neutralForm_nonneg`, `zetaZeroWidth_le_iff_twoEndOdd_rate` | unconditional; equivalence |
| The floor trees do not mix: components below `9/2`, no gap of the dilation process, curvature zero | `floorContact_eq_zero_of_component`, `dilationForm_le_of_no_gap`, `gammaTwo_nonneg`, `not_curvature_pos` | unconditional |
| Calibration: under RH `μ ≤ cap`, the margin lies in `[0, c₀]` and tends to `0` | `neg_eigenvalue_le_poleCapacity_of_riemannHypothesis`, `poincare_constant_mem_of_riemannHypothesis`, `exists_plane_neutralForm_le_of_riemannHypothesis` | calibration |

## 6. Questions

| # | Question | Status |
|---|---|---|
| 1 | One bound state of `(R, 3R]` and `(R, 4R]` at every block size from the true contacts of `2` and `3` (B192) | open; worked in AGZ. In MAFT terms: the conditional coupling over the dyadic middle `(3R/2, 2R]` contracts |
| 2 | Which cut is the bottleneck | criterion: a part binding more than its share; under one bound state none does; on long windows the ground state charges both ends. The cut at ratio three is open |
| 3 | How the chain of a window compares with the chains of its parts | answered by the overlap law: exact, of full rank, with all contacts between the ends in `X` |
| 4 | A curvature bound for the floor trees | answered: the curvature is exactly `0`; a curvature argument must use the jets |
| 5 | The gap of the dilation process on `(1, Q]` | answered: zero for every `Q`, at the common returns; at finite block size zero below ratio `9/2` |
| 6 | Whether the margin has a limit and whether a uniform lower bound forces RH | a uniform lower bound forces RH, at infinite and at finite block size; under RH the margin tends to `0` at infinite block size; the limit at finite block size is open |
| 7 | The order of the binding energy and which floor maps carry it | answered: `√ρ`, carried by the long maps between the ends; the unconditional leading constant is open |
| 8 | A recursion along doublings | answered in overlap form: two shorter parts and one contraction per window |
| 9 | The true exponent of the loss | `½` unconditionally; any `θ < ½` gives the strip `|Re ρ − ½| ≤ θ`; RH is `θ = 0`; every `θ < ½` is open |

## 7. Tools

**Developed.**
- Doob chain of a symmetric Metzler matrix with its Perron vector; Poincaré and bottleneck forms
  of one bound state; the cut law.
- Real Haynsworth additivity for block matrices with transposed couplings; overlap decomposition
  of a window; refinement monotonicity.
- Archimedean floor through the Lévy representation; weighted Schur tests for floor maps, between
  bottom and top; root and two-end packets with Chebyshev's bounds; the pole capacity through
  `t ≤ sinh t`.
- Reflection of packets and the parity split, with and without charges.
- Pole-free profile, states of the two ends, binding state of the spline; Landau's argument from
  both sides on a lag structure; rate laws.
- Transfer of lower bounds and of rates from step packets through the comb to the zeros; the plane
  of two negative squares on the initial windows.
- Jump calculus: carré du champ and `Γ₂` of translation-invariant jump generators; simultaneous
  return frequencies of the rotations `t log k`.

**To build.**
- The Doob chain at infinite block size as an operator, with its jets.
- Canonical paths and comparison of Dirichlet forms across dyadic cuts; trickle-down for the Doob
  chains (ALG).
- Quantitative overlap law: margins of `S₁`, `S₃` against the norm of `X`.
- A Doob energy of the jets on the waves `cos(t log x)` at the common returns.

## 8. Traps

| Trap | Truth |
|---|---|
| The floor trees mix by themselves | Components below ratio `9/2`; no gap of the dilation process for any `Q`; curvature `0` |
| The jets carry the binding | Without the trees the binding is below `5.4`; with them it grows like `√ρ` |
| The prime `2` decides every ratio | On long windows the binding is carried by maps of `k` of the size of the ratio |
| A bounded number of test functions across a cut decides | The binding has rank proportional to the block size, and so do the components |
| Gap and binding energy are of different orders | Both are of order `√ρ` and differ by at most `c₀` |
| RH leaves room: a uniform positive margin | Under RH the margin of long windows tends to `0` at infinite block size |
| The binding may reach the Chebyshev ceiling `4√ρ` | Under RH it is at most the pole capacity `√ρ − 1/√ρ + log ρ` |
| Gluing needs the positive cone | Through a dyadic middle it is a Cauchy–Schwarz contraction on the whole space |
| A Bakry–Émery bound for the trees gives the gap | Their curvature is exactly `0` |
| A Cheeger bound suffices | Cheeger loses a square, and only constants inside a bounded margin matter |
| The sharp constant must be proved | Any additive loss is free; a loss `o(ρ^{½})` of power type is already a zero-free strip |
| A deep second bound state can be confined to a few windows | It forces second bound states of unbounded depth |
| The reflection acts on step packets | It maps unit blocks to reciprocal blocks; it is a symmetry of the limit only |

## 9. Open research topics

- **The jets at the returns.** A lower bound for the Doob energy of the jets on the waves at the
  common returns of `t log k`, against the binding energy, is the input the floor trees cannot
  supply.
- **Converse of the rate laws.** Does a zero width `θ` give a margin `≥ −C ρ^{θ + ε}` on the
  window matrices? For the odd states of the ends it does; for all packets it is open.
- **Strategies with an additive loss.** A comparison or path argument proving gap `≥ μ − C`
  suffices. Which of the known losses (the margin bound, the archimedean floor, the overlap
  contraction) are additive?
- **The contraction of the conditional coupling** at the balanced split of every ratio, and at
  ratio three (B192).
- **The leading constant of the binding energy** without RH: the deficit `cap − μ` as a reading of
  the zeros.
- **The finite-block-size gap** of the dilation process from ratio `9/2` on.
- **The odd sector at finite block size**, where the reflection is not available: which floor
  maps decide it.

## 10. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | AbsoluteGeometryOfSpecZ 16, RHTower 7, SquareRootThreshold 6, HTGeometry 3, HodgeTheoryOfAFixedPart 1, SurfaceOfSpecZ 1, CohomologyOfWindowsOfSpecZ 1, ArithmeticCastelnuovoSeveri 1, WindowVisibilityLaw 1, SpacingScaleHarmonicAnalysis 1 |
| Used by | MainTheorems |

| Neighbour | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ (AGZ) | the block matrix, neutral part, tower, certified windows, rank law, weakened contacts, two-well law, packet form; B192 |
| HTGeometry | Hermitian inertia, Haynsworth, alternating inertia of exponential kernels, Dirichlet's simultaneous approximation |
| RHTower | the Lévy density and `A(0)` of the archimedean form; parity pole-weight windows, of which the odd-sector law is the case `β = 0`; the ordinates of the zeros are at least `2` |
| SquareRootThreshold (SRT), SurfaceOfSpecZ | zero configurations, lag structures, Landau's argument from above and from below, zero width |
| HodgeTheoryOfAFixedPart (HFP) | the comb at finite scale: samples, block averages, the limit to the zeros |
| CohomologyOfWindowsOfSpecZ, ArithmeticCastelnuovoSeveri | short windows carry one negative square; the complete Weil source transfer |
| ArithmeticLorentzianGeometry (ALG) | Metzler forms and trickle-down, the curve case |
| ArithmeticOrientationGeometry (AOG) | one generic orbit decides RH; its rate is the depth of the deepest seen zero, the infinite-orbit form of the rate laws here |
| SelectiveArithmetic (SA), SelectivePositivityAndThresholdLaws (SPTL) | the selective ladder; parity sectors and the selective refutation below `103/50` |

## 11. Big picture

MAFT makes the finite form of RH a statement about Markov chains and finds that its content is
qualitative. The neutral part of every window is a Doob chain shifted by its binding energy.
Binding energy and gap are both of order `√ρ`, the gap exceeds the energy by at most an absolute
constant, and RH is the statement that it does not fall below. That statement is self-improving:
a uniform loss forces the sharp inequality, and a loss of power `θ < ½` already gives the
zero-free strip of width `θ`. A proof may therefore be lossy in every constant and in a power of
the ratio. It may not lose the full `√ρ`, which is what every unconditional bound loses, and
which is the trivial strip.

The arithmetic splits cleanly. The floor trees create the binding energy: without them it is
below `5.4`, with them it grows like `√ρ`, through the long maps that join the two ends of a
window. But they create none of the mixing. At finite block size they fall into components below
ratio `9/2`. At infinite block size the dilation process has no gap for any `Q` and curvature
exactly zero, both because of the waves `cos(t log x)` at the frequencies where the rotations
`t log k` return together. Whatever gap the chain has must come from the jets at those
frequencies, where `Σ_{k ≤ Q} Λ(k) k^{it}` is near its maximum `ψ(Q)`. The functional equation adds a symmetry at infinite block size: the ground state is even,
the bound state RH excludes would be odd, and the odd sector measures the zeros exactly through
its rate.

The open core of the field is the interaction of jets and trees at the common returns. It is a
single, explicit, lossy estimate whose power-saving version is already a theorem about the zeros.

## 12. Success criteria

The field is developed when:
- the Doob chain of every window is a Lean object with its inertia law (done);
- the scale of binding energy and gap is proved (done up to constants; under RH the upper constant
  is the pole capacity);
- the comparison of a window with its parts is exact (done);
- cut, curvature and path methods are each either proved to give the gap or refuted by a theorem
  (curvature refuted for the trees; cuts reduced to the share law; paths open);
- the questions of §6 are answered or reduced to named estimates.

## 13. What a contribution must be

- **X1** A statement about the chain, proved without the zeros.
- **X2** Consistent with the calibration: gap `≥` energy on the certified windows; gap `<` energy
  at ratio four with the weights of `2` and `3` in `[−5/2, 19/40]` and for the Liouville twist.
- **X3** No bound through a bounded number of test functions across a dyadic cut.
- **X4** Stable under refinement of the blocks: at every block size or at infinite block size.
- **X5** Every inequality names the tree edges and the jets it uses. An argument that uses only the
  trees proves no gap.
- **X6** It reproduces the curve case, in which the trickle-down inequality on Frobenius ladders
  is the one-sided point count (ALG).
- **X7** Its loss is `o(ρ^{½})`. A bound that loses the full `√ρ` is the trivial strip.
