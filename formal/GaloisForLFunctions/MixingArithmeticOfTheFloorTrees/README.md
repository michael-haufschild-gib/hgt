# Mixing Arithmetic of the Floor Trees (MAFT)

Namespace `GaloisForLFunctions.MixingArithmeticOfTheFloorTrees`; umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Specification: §2.9 of
[the review-1311 summary](../../../docs/reports/review-1311/obstacles-summary.md). Programme card:
`docs/drafts/pipeline/1-in-progress/maft-mixing-arithmetic-of-the-floor-trees.md`.

Every theorem named as proved is proved in Lean without hypothesis. **corpus** marks a theorem of
another folder, **[C]** published mathematics not in the corpus, **open** a statement not proved,
**expected** a statement supported by a computation in the text below but not yet proved.

## 1. Motivation

At finite scale the Riemann hypothesis is a statement about one explicit matrix per window. On the
unit blocks `(a, a + 1]` of a window `W = (R, R + J]`, Weil's form of a step packet is the product
of its two charges plus the **neutral part** `N_W` (AGZ, `sum_blockMatrix_eq_charges_add_neutral`).
`N_W` has negative entries off the diagonal: the jets join every pair of blocks, and the
**floor maps** `b ↦ ⌊b/k⌋` join a block to its images, with the weights `Λ(k)/k`. RH holds iff
`N_W` has exactly one negative square on every window with `R ≤ J` (AGZ,
`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`).

A symmetric matrix with negative off-diagonal entries is minus the generator of a positive
dynamics. Its lowest eigenvector `φ` is positive, and conjugation by `φ` turns `N_W` into the
generator of a reversible Markov chain on the blocks, shifted by the lowest eigenvalue `−μ_W`:

  `N_W(φf, φf) = −μ_W Σ_a φ_a² f_a² + ½ Σ_{a,b} w_{ab} φ_a φ_b (f_a − f_b)²`

(AGZ, `sum_sum_mul_eq_doob`). So a window holds one bound state iff the spectral gap of this
**Doob chain** is at least its **binding energy** `μ_W`: RH at finite scale is a Poincaré
inequality whose constant is the binding energy of the window, for a chain that moves along the
jets and along the floor trees.

Three theorems of the corpus fix what any proof of that inequality must use. It has **full rank**:
a coupling of the two halves of a window of ratio four that carries the binding has rank
proportional to the block size (AGZ, `two_le_hermNegIndex_lowered_model_of_rank`). It is
**selective**: with the contact of `2` weighted in `[−4, 0]`, or with the Liouville twist, every
window of ratio three holds two bound states (AGZ, `two_le_hermNegIndex_reweighted_of_ratio_three`,
`two_le_hermNegIndex_liouville`). It is **cooperative**: the off-diagonal entries are negative,
so the problem is one of a positive operator. The object that these three describe — a positive
dynamics on the blocks that moves along the floor trees — has not been studied as a chain: its
gaps, its bottlenecks, its comparisons, its limit at infinite block size. MAFT studies it.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| window, block, ratio | `neutralWindow Q R J` (AGZ) | blocks `R, …, R + J − 1`; ratio `ρ = (R + J)/R`; `Q ≥ ρ` sees every contact |
| weights | `blockWeight`, `blockJet`, `floorContact`, `floorGraph` (AGZ) | `w_{ab} = J(a, b) + Σ_k (Λ(k)/k)[⌊b/k⌋ = a]` |
| potential | `blockPotential` (AGZ) | row sums `V_a = Σ_b N_{ab}` |
| floor tree of `k` | `floorGraph k` (AGZ) | `b — ⌊b/k⌋`; for a prime `p` the `p`-ary ancestor tree of the integers |
| ground vector, binding energy | to define | `φ_W > 0`, `N_W φ_W = −μ_W φ_W`, `−μ_W` the least eigenvalue |
| Doob chain | to define | measure `π_a = φ_a²`, conductances `c_{ab} = w_{ab} φ_a φ_b` |
| Dirichlet form, gap | to define | `E_W(f) = ½ Σ c_{ab}(f_a − f_b)²`; `γ_W` the least nonzero eigenvalue of `E_W` against `π` |
| margin | to define | `m_W = γ_W − μ_W = λ₂(N_W)`; one bound state iff `m_W ≥ 0` |
| cut, conductance | to define | `S ⊂ W`; `C(S) = Σ_{a ∈ S, b ∉ S} c_{ab}` |
| jet chain, contact chain | to define | the Doob chain with only the jets, only the floor trees, as conductances |
| dilation limit | to define | the window at infinite block size: functions on `(1, ρ]`, jets the kernel `¼(1/|x − y| + 1/(x + y))`, the tree of `k` the dilation `x ↦ kx` with weight `Λ(k)` |
| reweighted window | `reweightedNeutral ω` (AGZ) | the contact of `k` weighted by `ω(k)` |

## 3. Language

- A **bound state** of `W` is a negative square of `N_W`; the **ground state** is `φ_W`.
- The **binding energy** `μ_W` is the depth of the ground state; the **gap** `γ_W` is the rate at
  which the Doob chain mixes; the **margin** is their difference.
- A **well** is a nonnegative packet with negative energy; two wells on disjoint blocks are
  **bound** if their coupling is at least the geometric mean of their depths (AGZ: one bound state
  iff all disjoint wells are bound).
- A **bottleneck** is a cut whose conductance is small against the binding energy.
- A **selective edge** is a floor-map edge whose weight decides a bound state: the statement is
  true at the true weight and false at a twisted or weakened one.
- The **tower** of a window is the family of its block sizes under refinement (translation by
  `log m`); a statement **at every block size** holds on the whole tower.
- **Shallow** floor maps are those of `k > √ρ`, which have depth one in the window; **deep** ones
  have depth at least two.

## 4. Mechanisms

**Known (corpus).**
1. *Charges, potential, Dirichlet form.* `N_W` is a potential plus the Dirichlet form of the jets
   and the floor trees; the form does not increase under `σ ↦ |σ|`; a minimizer has one sign and
   both charges nonzero (AGZ).
2. *Tower.* The neutral part is invariant under refinement; a statement on coarse blocks holds on
   every finer tower member; the index at every block size is the index of Weil's form on all
   step functions of the window (AGZ).
3. *Narrow and dyadic windows.* No bound state for `16J ≤ R`; exactly one for `R ≤ J ≤ 53R/50`, at
   every block size (AGZ).
4. *Gluing.* Through charges or through models of bounded rank the halves of a window of ratio
   four do not glue (AGZ). Hodge index form: one bound state iff disjoint wells are bound (AGZ).
5. *Metzler regimes.* Narrow windows are in the stability regime; windows of ratio at least two
   in the hyperbolic regime, where one positive square of `−N_W` is the trickle-down inequality
   (ALG).
6. *Selectivity below `103/50`.* On log-length `0.724` the Liouville-twisted odd sector fails
   while ζ's full sector is positive (SPTL,
   `exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`).

**To develop.**
7. *Ground-state transform as an inertia law.* `N_W` is congruent to `E_W − μ_W π`; the bound
   states are the slow modes of the Doob chain; one bound state is the Poincaré inequality with
   constant `μ_W`.
8. *Cuts.* A cut with `C(S) < μ_W π(S) π(S^c)/π(W)` gives a second bound state; the cut criterion
   is the Hodge index inequality on the restrictions of the ground state.
9. *The scale.* In log coordinates the tree of `k` is the translation by `log k` with weight
   `Λ(k)/√k`. On the packet flat in `log x` the floor trees lower the energy by
   `(2/L)Σ_{k ≤ ρ} Λ(k) k^{−1/2} log(ρ/k)`, `L = log ρ`, while the jets contribute `O(1)`: the
   binding energy is of order `√ρ/log ρ` at least (**expected**), and under RH at most
   `2(ρ − 1)/√ρ` (Cauchy–Schwarz on the charges). The floor-tree conductance of the middle cut
   is of the same order `√ρ`. So at large ratio the gap and the binding energy are of one order,
   both created by the shallow floor maps of the primes of size `ρ^{1−o(1)}`; the jets, whose
   regional kernel has the harmonic spectrum (LST, `regionalLogOperator_legP`), mix at a bounded
   rate.
10. *Dilation limit.* At infinite block size the window form is a function of the
    autocorrelation of the test: it is invariant under translation and under the reflection of
    the window (the functional equation), and the trees of `k` become dilations.

## 5. Questions

1. **B192** (shared with AGZ): one bound state of `(R, 3R]` and `(R, 4R]` at every block size
   from the true contacts of `2` and `3`.
2. Which cut of a window is the bottleneck of its Doob chain, and how does its conductance
   compare with the binding energy along the ratios?
3. A comparison of the chain of a window with the chains of its parts through the floor trees: a
   Doob-chain form of gluing that survives the rank law.
4. A curvature bound for the floor trees with the weights `Λ(k)/k`, or a theorem that no
   curvature bound of the classical kinds gives the gap.
5. The gap of the dilation process on `(1, ρ]`: of the floor trees alone, of the jets alone, and
   of the full chain at infinite block size.
6. Whether the margin `m_W` has a limit along the ratios, and its sign.
7. The exact order of the binding energy and of the gap as `ρ → ∞`: which floor maps carry them.
8. A recursion along doublings (M4): a statement on `(R, 2^n R]` that implies the one on
   `(R, 2^{n+1} R]` and whose step has full rank.

## 6. Tools

**Available.** The ground-state transform; Haynsworth inertia additivity and response matrices
(HTG, AGZ); Sylvester's law of inertia (HTG); the tower under refinement; the closed forms of the
block matrix (AGZ); the regional logarithmic spectrum (LST).

**To build.** The Doob chain of a window as an object; Poincaré and Cheeger inequalities for it;
comparison of Dirichlet forms and canonical paths across cuts; the contact Mellin calculus of the
floor trees in log coordinates; the dilation limit with its symmetries.

## 7. Pillar theorems

| Pillar | Statement | Status |
|---|---|---|
| Inertia of the Doob chain (M1) | `hermNegIndex N_W` = number of eigenvalues of the Doob chain below `μ_W`; one bound state iff `γ_W ≥ μ_W` | open |
| Cut criterion | a bottleneck below the binding energy gives a second bound state | open |
| Scale law | binding energy and floor-tree conductance are of order `√ρ` up to `log ρ` | open |
| Dilation limit | the window form at infinite block size with its translation and reflection symmetry | open |
| First selective sign (B192) | one bound state at ratio three from the tree of `2` | open (AGZ) |

## 8. Traps

| Trap | Truth |
|---|---|
| The floor trees mix by themselves | Below ratio four a middle range of blocks has no floor map at all; the trees are forests of small components there |
| Sizes of the contacts bind | Weakened contacts hold two bound states (AGZ) |
| A bounded number of test functions across a cut decides | The binding has rank proportional to the block size (AGZ) |
| The prime `2` decides every ratio | At large ratio the binding energy and the conductance are carried by the shallow floor maps of large primes |
| The jets carry the gap | The jet chain mixes at a bounded rate; the binding energy grows with the ratio |
| A Cheeger bound suffices | Cheeger loses a square; gap and binding energy are of one order, so only constants matter |

## 9. Context

| Programme | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ (AGZ) | the block matrix, the neutral part, the tower, the certified windows, the rank law, weakened contacts, the Hodge index form |
| ArithmeticLorentzianGeometry (ALG) | Metzler forms, trickle-down, hyperbolic links |
| SelectiveArithmetic (SA) | selective weight systems and the selective ladder |
| HodgeTheoryOfAFixedPart (HFP) | the pairing on real divisors at finite scale |
| SelectivePositivityAndThresholdLaws (SPTL) | parity sectors and the first selective refutation below `103/50` |
| LatticeSectionTheory (LST) | the regional logarithmic spectrum |
| ArithmeticCriticalityTheory (ACT) | Doob transforms and ground states of arithmetic jump operators on the line |

## 10. Success criteria

The field is developed when: the Doob chain of every window is a Lean object with its inertia law;
the scale of binding energy and gap is proved; the dilation limit and its symmetries are proved;
cut, comparison and curvature methods are each either proved to give a gap bound or refuted by a
theorem calibrated on twisted contacts; and the questions of §5 are answered or reduced to named
estimates.

## 11. What a contribution must be

- **X1** a statement about the chain, proved without the zeros.
- **X2** consistent with the calibration: gap `≥` energy on the certified windows; gap `<` energy at
  ratio four with the weights of `2` and `3` in `[−5/2, 19/40]` and for the Liouville twist.
- **X3** no bound through a bounded number of test functions across a dyadic cut.
- **X4** stable under refinement of the blocks: at every block size or in the dilation limit.
- **X5** every inequality names the tree edges it uses.
- **X6** it reproduces the curve case, in which the trickle-down inequality on Frobenius ladders is
  the one-sided point count (ALG).
