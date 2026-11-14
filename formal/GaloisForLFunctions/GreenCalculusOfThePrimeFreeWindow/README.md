# Green Calculus of the Prime-Free Window (GCW)

Namespace `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow`; umbrella
`GreenCalculusOfThePrimeFreeWindow.lean`. Every statement below with a Lean name is a theorem of
this folder unless a neighbour is named (MAFT = MixingArithmeticOfTheFloorTrees, AGZ =
AbsoluteGeometryOfSpecZ). Statements under "Open" are not theorems.

## 1. Motivation

At finite scale the Riemann hypothesis is one statement per window: the neutral part `N_W` of
Weil's form on the step packets of `W = (R, R + J]`, `R ≤ J`, has exactly one negative square
(AGZ). The overlap law (MAFT) turns this into a recursion. Write `W = (R, 2D + b]`, `D = R + a`,
as a left end `(R, D]`, the **dyadic middle** `(D, 2D]` and a right end `(2D, 2D + b]`. Then `W`
holds one bound state iff, after the middle is eliminated, the form left on the two ends is
nonnegative. Ratio `ρ` goes to `ρ²/2` in one step; RH is this inequality at every step.

Everything in a step passes through one matrix, the inverse of the neutral part of the dyadic
middle. Two facts make it an object of its own.

* **It is prime-free and universal.** Between two blocks of `(D, 2D]` no floor map `b ↦ ⌊b/k⌋`,
  `k ≥ 2`, acts. The middle is the archimedean matrix at block size `D` (a logarithmic potential
  and the jets), the same for every window that contains it and for every cutoff `Q`.
* **The primes enter a step only as boundary maps.** Up to ratio three the only contact is that
  of the prime `2`; it sends the left end into the top sliver of the middle and the bottom sliver
  of the middle into the right end.

The calculus is the potential theory of this one family of matrices, with the arithmetic as
boundary data. It does not prove a step. It determines the mediator (sign structure, size,
monotonicity), turns a step into inequalities between explicit forms, and proves which
inequalities cannot work.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Dyadic middle `M_D` | `primeFreeMiddle D` | neutral part on the blocks `D, …, 2D − 1`; equals `neutralWindow Q D D` for every `Q` |
| Potential `V_D` | `middlePotential D` | row sums of `M_D`; `M_D = V_D +` a Dirichlet form with the jets as conductances |
| Binding energy, ground vector | `bindingEnergy D`, `groundVector D` | `M_D φ_D = −μ_D φ_D`, `‖φ_D‖ = 1` |
| Green matrix `G_D` | `greenMatrix D` | `M_D⁻¹` |
| Positive part `G₊` | `greenPositive D` | `G_D + φ_D φ_Dᵀ/μ_D`, the Green matrix on `φ_D^⊥` |
| One bound state | `OneBoundState M φ μ c` | symmetric, `Mφ = −μφ`, `μ > 0`, `M ⪰ c > 0` on `φ^⊥` |
| Couplings, end form | `endCoupling`, `endForm` | `P`: middle to the two ends; `N_e`: neutral form of the two ends |
| Schur complement of the middle | `overlapSchur` | `S = N_e − Pᵀ G_D P`, the form the ends see |
| Jets, contacts, pencil | `endJet`, `endContact`, `pencilSchur` | `P(t) = −𝒥 − t𝒞`; `t = 1` the window, `t = 0` no primes, `t = −1` the sign twin |
| Level | `overlapSchurLevel`, `overlapCouplingLevel` | the same objects for `N + C` |
| Excess of a step | `windowExcess`, `schurStepExcess` | least `x ≥ 0` with `S_C + x ⪰ 0`; its supremum over all steps of ratio `ρ` |
| Tower | `refineMatrix m D` | isometry from block size `D` to `mD` with `ιᵀ M_{mD} ι = M_D` |
| Degrees, pole plane | `middleDegree D`, `withPoles M p q` | `d_i = log(1 + 1/(D + i))`; `M + p ⊗ q + q ⊗ p` |
| Weil's form on the middle | `weilMiddle D`, `weilGreen D` | `𝔚_D = M_D + d ⊗ 𝟙 + 𝟙 ⊗ d`, positive definite; `𝒢_D = 𝔚_D⁻¹` |
| Pole pairings | `degreeEnergy`, `degreeCharge`, `middleCapacity` | `α = ⟨d, G_D d⟩`, `β = ⟨d, G_D 𝟙⟩`, `γ = ⟨𝟙, G_D 𝟙⟩` |
| Attraction of the ends, dressed middle | `endAttraction`, `dressedMiddle` | `Σ = P N_e⁻¹ Pᵀ`, `M̃ = M_D − Σ` (narrow ends) |
| Adjacent windows | `adjacentCoupling Q R J j` | coupling of `(R, R + J]` to `(R + J, R + J + j]`; the window `(R, R + J + j]` is the block form of the two |
| Gap | `HasGap M c` | `M ⪰ c` on a hyperplane: the second eigenvalue is at least `c` |

## 3. Language

- A **bound state** is a negative square of a neutral part. A window is **bound** if it holds
  exactly one.
- The **bound-state channel** of the middle is `−φ_D φ_Dᵀ/μ_D`, the **positive channel** is `G₊`.
  Through the first the ends repel, through the second they attract.
- The **charge** of a packet is its sum. A packet is **charge-free** if its charge vanishes; a
  **sliver** is a set of blocks of the middle whose complement still binds.
- The Schur complement of the middle is its **Dirichlet-to-Neumann form**: the least energy of
  the window over the middle packets, as a form on the ends. The **dual** elimination removes
  the ends and leaves a form on the middle, the **dressed middle**.
- A **step** is one application of the overlap law; the **first step** is `a ≤ 3R/100`,
  `b ≤ 3(R + a)/50`, where both parts lie in the certified range `J ≤ 53R/50`.
- The **level** `C` shifts a neutral part by `C` on the diagonal; the **margin** of a window is
  the least level at which it holds at most one bound state; the **excess** of a step is the
  margin it adds.
- The **gap** of a window is a lower bound of its neutral form on a hyperplane. A window with
  `R ≤ J` and a gap `≥ 0` is bound; a **floor** is a gap on the complement of the ground vector.
- A **thin end** of a window is an adjacent window of relative width `1/K`: `K j ≤ R + J`.
- The **dipole** is the mixed jet–contact term `𝒥ᵀ G_D 𝒞`; the **sign twin** reverses the
  contact of `2`, hence the dipole, and nothing else.

## 4. Mechanisms

1. **The middle is archimedean.** `neutralWindow Q D D` does not depend on `Q`
   (`neutralWindow_dyadic_eq`): inside a dyadic window `max < 2 min`.
2. **Two channels.** `G_D = −φ_Dφ_Dᵀ/μ_D + G₊`, `G₊ ⪰ 0`, `G₊φ_D = 0`. The Schur complement is
   `N_e + (Pᵀφ_D)(Pᵀφ_D)ᵀ/μ_D − PᵀG₊P` (`overlapSchur_form_eq_channels`).
3. **The Green matrix is negative only along the charge.** `G_D V_D = 𝟙`, and
   `⟨w, G_D w⟩ = (Σw)²/(D · N(1,1)) + ⟨w₀, G_D w₀⟩` with `w₀` charge-free and `N(1,1) < −1`
   (`greenMatrix_form_eq_charge`). On charge-free packets and on slivers `G_D` is positive
   definite.
4. **Duality.** For a form with one bound state, `⟨w, M⁻¹w⟩ ≥ 0` iff `w^⊥` contains a nonzero
   vector of nonpositive energy (`OneBoundState.inv_form_nonneg_iff`). The class is closed under
   inversion (`OneBoundState.inv`): depth `1/μ`, floor `1/‖M‖`.
5. **Monotonicity.** The Green form grows with the window (`inv_form_submatrix_le`) and along
   the tower (`greenMatrix_form_le_refined`); so does the binding energy
   (`bindingEnergy_le_refined`). A bound at one block size passes to every divisor.
6. **Levels.** Below `μ_D` the middle keeps one bound state at every level, the Schur complement
   grows at least at unit speed in the level (`schur_add_diagonal_mono`), and the loss of a step
   is additive: parts with margin `≤ C < μ_D` and conditional coupling of norm `≤ x` give a
   whole with margin `≤ C + x` (`hermNegIndex_overlapWhole_add_diagonal_le_one`).
7. **The pencil of the prime two.** `S(t) = N_e − 𝒥ᵀG_D𝒥 − 2t 𝒥ᵀG_D𝒞 − t² 𝒞ᵀG_D𝒞`. The contacts
   land in slivers, so `𝒞ᵀG_D𝒞 ⪰ 0` and `t ↦ S(t)` is concave: the admissible weights of the
   prime two form an interval. `S(t) − S(−t)` is `−4t` times the dipole.
8. **The pole plane absorbs the bound state.** `𝔚_D = M_D + d ⊗ 𝟙 + 𝟙 ⊗ d` is positive definite
   exactly because the pole matrix `[[α, 1 + β], [1 + β, γ]]` of the Green pairings is negative
   definite (`OneBoundState.withPoles_pos_iff`). Its inverse is `G_D` minus the rank two term of
   the pole matrix, and `G_D ⪯ 𝒢_D`.
9. **The ends dress the middle.** Narrow ends (`16a ≤ R`, `8b ≤ R + a`: the first two steps of
   the ladder) hold no bound state. Eliminating them leaves `M̃ = M_D − P N_e⁻¹ Pᵀ`: every
   coupling is negative and `N_e⁻¹` preserves positivity, so the ends add an attraction between
   any two blocks of the middle. The window and `M̃` hold the same number of bound states.
10. **A thin end is stiff.** On `(R, R + J]` with `KJ ≤ R` every block has potential at least
   `log K − 2`: the density `log R` against half the jets, `log J`. Two adjacent windows are
   coupled with norm at most `B = 24 + 2 Σ_{k ≤ Q} Λ(k)` at every block size (Hilbert's
   inequality for the jets, Schur's test for the contacts). A corner of stiffness `s` against a
   coupling `B` costs `ε` of a floor `c` as soon as `s ≥ c − ε + B²/ε`: an end of relative width
   `δ` costs at most about `B²/log(1/δ)`.
11. **Continuity.** The gap decreases with the window and is lower semicontinuous by 10. At
   block size `KR` one block is a thin end, so a bound range with a common gap grows block by
   block; the refinement tower returns the conclusion to every block size. The bound range can
   end only where the gap of the bound windows closes.

## 5. Pillar theorems

**P1 One bound state of the middle.** `oneBoundState_primeFreeMiddle`: `M_D` has one bound state
with floor `1/5000` at every `D ≥ 1`; `−N(1,1) ≤ μ_D < 3` (`one_lt_bindingEnergy`,
`bindingEnergy_lt_three`).

**P2 The overlap law in Green form.** `hermNegIndex_neutralWindow_eq_one_iff_overlapSchur`: the
window is bound iff `S ⪰ 0`. `riemannHypothesis_iff_forall_greenForm`,
`riemannHypothesis_iff_forall_overlapSchur_nonneg`, `riemannHypothesis_iff_overlapSchur_bddBelow`.

**P3 A priori bounds.** `−1 ⪯ G_D ⪯ 5000` (`greenMatrix_form_ge`, `greenMatrix_form_le`); both
conditional energies of the first step are `⪰ 1/5000`
(`schur_floor_of_charge_cancellation`, `overlapLeftEnergy_floor`); a conditional coupling of
norm `≤ 1/5000` gives the first step
(`hermNegIndex_neutralWindow_eq_one_of_firstStep_coupling_le`).

**P4 Sign and size of the Green matrix.** Charge formula (`greenMatrix_form_eq_charge`);
`‖w‖² ≤ (8 log 2D + 21)⟨w, G_D w⟩` on charge-free packets and
`‖w‖² ≤ (152 log 2D + 453)⟨w, G_D w⟩` on slivers (`greenMatrix_form_ge_of_sum_eq_zero`,
`greenMatrix_form_ge_of_sliver`); the diagonal is `Θ(1/log D)` (`greenMatrix_diag_bounds`), so
no bound `O(1/D)` holds on the slivers (`not_exists_sliver_inv_bound`).

**P5 The additive loss law.** `hermNegIndex_overlapWhole_add_diagonal_le_one`,
`riemannHypothesis_of_level_function`: a level function with values in `[0, 1]` whose
increments dominate the conditional couplings proves RH.

**P6 Excess and ladder.** `schurStepExcess` is bounded by closed-form envelopes at every block
size and is monotone in the ratio; `iteratedRatio k = 2 (103/100)^(2^k)` passes ratio three at
the fourth step; `riemannHypothesis_iff_globalTowerLevel_zero`: RH iff every cumulative excess
vanishes, iff the cumulative excesses stay below the binding energy.

**P7 The pencil.** `pencilSchur_form`, `contactGreen_nonneg`, `pencilSchur_form_interp`,
`hermNegIndex_reweighted_eq_one_of_between`. On `(R, 3R]` all admissible weights have one sign:
the window and a reweighting with a weight `≤ 0` of the prime two are never both bound
(`not_hermNegIndex_eq_one_of_weight_nonpos`), and no bound that is invariant under `𝒞 ↦ −𝒞`
proves a bound window (`signTwin_obstruction`).

**P8 Monotone towers.** `inv_form_submatrix_le`, `greenMatrix_form_le_refined`,
`greenMatrix_form_refined_le`, `bindingEnergy_le_refined`.

**P9 The pole criterion and Weil's Green matrix.** `OneBoundState.withPoles_form_eq`,
`OneBoundState.withPoles_pos_iff`; `degreeEnergy_neg`, `poleDet_pos`, `degreeCharge_lt`;
`‖w‖²/(2 log 2D + 5) ≤ ⟨w, 𝒢_D w⟩ ≤ 5000‖w‖²` (`weilGreen_form_ge`, `weilGreen_form_le`);
`riemannHypothesis_iff_forall_weilSchur_nonneg`: RH iff on the ends of every window Weil's form
dominates the form of the couplings in the positive matrix `𝒢_D`.

**P10 The dual overlap law.** `endForm_form_ge`: ends with `16a ≤ R`, `8b ≤ R + a` are `⪰ 3/4`
with no certificate. `hermNegIndex_neutralWindow_eq_dressedMiddle`;
`hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle_wells_bound`: such a step is the Hodge
index inequality of the dressed form on positive packets of the middle without a common block.
On the first step each end alone leaves one bound state
(`hermNegIndex_dressedMiddle_left_eq_one`, `hermNegIndex_dressedMiddle_right_eq_one`).

**P11 Small blocks.** `hermNegIndex_neutralWindow_eq_one_of_firstStep_small`: the first step
holds for `R ≤ 33`.

**P12 The stiffness of a thin end.** `log_sub_two_le_blockPotential_of_thin`,
`neutralWindow_form_ge_of_thin`: `N ⪰ log K − 2` on `(R, R + J]`, `KJ ≤ R`, `K ≥ 16`.
`dotProduct_adjacentCoupling_mulVec_sq_le`: adjacent windows are coupled with norm `≤ B`.
`exists_oneBoundState_neutralWindow_of_thin_tail`: one bound state with floor `c` on
`(R, R + J]` gives one bound state with floor `c − ε` on `(R, R + J + j]` when `K j ≤ R + J` and
`log K ≥ c − ε + B²/ε + 2`. `thin_attraction_form_le`: the attraction of a thin end is
`⪯ 676/(log K − 2)`. `exists_oneBoundState_neutralWindow_beyond_certified`: the certified range
is not sharp at any block size.

**P13 The continuity method.** `hermNegIndex_neutralWindow_eq_one_of_gap`: fix the cutoff and a
bound `a/b` for the ratio; if the bound windows of ratio `≤ a/b` have a common gap `c > 0`,
every window of ratio `≤ a/b` is bound. `exists_bound_window_without_gap`: an unbound window is
preceded, at no larger ratio, by bound windows without gap `c`, for every `c > 0`.
`riemannHypothesis_of_gap_of_bound_windows`: a common positive gap of the bound windows at
every cutoff gives RH. The estimate is asked only of windows that are already bound.

## 6. Tools

**From the corpus.** Haynsworth additivity (`hermNegIndex_fromBlocks_transpose`), the overlap
decomposition (`neutralWindow_submatrix_overlapEquiv`), the certified floor on charge-free
packets (`sum_neutralBlock_ge_of_short`, `sum_blockMatrix_ge_of_short`), refinement
(`sum_neutralBlock_refine`), negativity off the diagonal (`neutralBlock_neg`), two wells and the
Hodge index inequality on the positive cone (`hermNegIndex_le_one_iff_forall_wells_bound`), sink
counts (`hermNegIndex_le_one_add_card_sinks`), narrow windows
(`one_lt_blockPotential_of_narrow`).

**Built here.**
- `OneBoundState`: forms, inverse, channels, reversed Cauchy–Schwarz
  (`OneBoundState.reverse_cauchy_schwarz`), positivity on the form-orthogonal complement of a
  negative vector (`OneBoundState.form_pos_of_orthogonal_neg`), duality, inversion, levels.
- Completing the square over either corner of a block matrix
  (`dotProduct_fromBlocks_mulVec_eq_schur`, `dotProduct_fromBlocks_mulVec_eq_corner_schur`);
  Haynsworth over a positive corner (`hermNegIndex_fromBlocks_eq_of_corner_floor`).
- The Dirichlet principle for the positive channel (`positiveChannel_ge`).
- Compression and domain monotonicity of inverses at equal index
  (`inv_form_le_of_isometry`, `inv_form_submatrix_le`).
- Rank two perturbations: the pole normal form and its inverse (`poleSolution`).
- Positivity of the inverse of a positive definite matrix with entries `≤ 0` off the diagonal
  (`inv_mulVec_nonneg_of_offDiag_nonpos`).
- Norms of the boundary maps, uniform in the block size (`dotProduct_endCoupling_mulVec_sq_le`,
  `dotProduct_adjacentCoupling_mulVec_sq_le`; Hilbert's inequality without integrals, Schur's
  test), Gershgorin for the middle (`primeFreeMiddle_form_le`).
- A window as the block form of two adjacent windows (`neutralWindow_submatrix_finSumFinEquiv`,
  `neutralWindow_form_eq_head_tail`); the stiff corner lemma
  (`fromBlocks_form_ge_of_stiff_corner`); one bound state from a floor on any hyperplane
  (`exists_oneBoundState_of_pos_eigenvector_of_hyperplane`); `HasGap`.

## 7. Questions and open topics

| # | Question | Status |
|---|---|---|
| 1 | Two-sided bounds for the sliver blocks of `G_D` | answered: positive definite, between `1/(C log 2D)` and `5000`; the order `1/log D` is attained |
| 2 | A lower bound for `μ_D` uniform in `D` | answered: `1 < −N(1,1) ≤ μ_D < 3`, nondecreasing along the tower |
| 3 | The first step | open; three normal forms (P2, P7, P10), small blocks (P11), the threshold `1/5000` (P3); reduced to a common gap of the bound windows of ratio `≤ 10609/5000` (P13) |
| 4 | The excess of a step as a function of the ratio | defined, bounded, monotone (P6); additive (P5); a thin step loses at most `B²/log(1/δ)` of the floor (P12); no bound below the binding energy |
| 5 | The Green kernel of the continuum form in closed form | open; normal forms only (mechanisms 2, 3, 8) |

**Open.**
- *The superposition of two attractions.* `M_D − Σ₁` and `M_D − Σ₂` each hold one bound state.
  The first step is the same for `M_D − P N_e⁻¹ Pᵀ`, whose attraction is `Σ₁ + Σ₂` up to the
  jets between the ends. No inequality of the corpus compares the three.
- *The sign of the dipole.* Any proof of a step at ratio three must use it; on the first step it
  is not known whether it must.
- *An excess below the binding energy.* The envelopes of P6 carry the factor `5000`, the
  reciprocal of the certified floor. The dual law bounds the attraction by `(4/3)‖P‖²`, which
  is no better than the bound of the margin by the norm of the coupling.
- *The a priori gap.* P13 asks for a lower bound of the gap of a window from the fact that it
  is bound. The Hodge index inequality on a bound window gives a gap `≥ 0` and no more.
- *The converse of the continuity method.* Whether RH gives a common gap of the windows of a
  cutoff is not known. It is strict decrease of the gap in the ratio: a zero mode of a window
  that is a zero mode of a larger bound window would have to vanish.
- *Wide ends bind.* The dual law needs ends without bound states; the threshold ratio of a
  bound window is not determined.
- *The continuum.* The Green forms of the tower increase and are bounded, so they converge on
  every step packet; the limit, the Green form of `log|x| + log|p|` on an interval of ratio two,
  is not constructed as an object, and no closed form is known.
- *The composition formula.* A window is the block form of two adjacent windows (P12), and of
  its middle and ends; the Green matrix of the whole in terms of the Green matrices of the
  parts is not stated.

## 8. Traps

| Trap | Truth |
|---|---|
| The certified floors give the first step | They need a conditional coupling of norm `≤ 1/5000`; adjacent jets are `≈ 0.69` |
| A perturbation from the certified range reaches the first step | It reaches ends of relative width `exp(−6760003)`: adjacent windows couple with order one, and an end of width `δ` has stiffness `log(1/δ)` (P12) |
| A chain of thin ends reaches a fixed ratio | The losses `B²/log(1/δ)` are not summable over a chain of fixed total width |
| The certified range `J ≤ 53R/50` is sharp | Windows beyond it are bound with floor `1/10000` at every block size (P12) |
| An a priori gap of the bound windows is less than RH | It implies RH (P13); whether RH implies it is open |
| The Green matrix decays like `1/D` on the slivers | Its diagonal is `Θ(1/log D)` everywhere (P4) |
| The Green matrix is indefinite in many directions | It is negative only along the charge; on charge-free packets it is positive definite (P4) |
| A bound for `G₊` in operator norm suffices | The only uniform bound is `5000`; smooth packets give mediated couplings of order one |
| The sizes of the contacts decide a step | Jet form and contact form are the same for the sign twin; the dipole decides (P7) |
| The middle sees the primes | No floor map acts inside a dyadic window |
| Weil's form and the neutral part have the same mediator | `𝒢_D = G_D +` a positive rank two term; `𝒢_D` is positive definite, `G_D` is not (P9) |
| The middle must be the block that is eliminated | Narrow ends can be eliminated; wide ends bind (P10) |
| A model of the middle of bounded rank suffices | Rank-`r` models of the gluing fail (AGZ) |
| The loss may be multiplicative | Only an additive loss below `inf_D μ_D` iterates (P5) |

## 9. Context

| Neighbour | Interface |
|---|---|
| MixingArithmeticOfTheFloorTrees | the overlap law, margins and exponent laws; GCW studies the mediator of its step |
| AbsoluteGeometryOfSpecZ | block matrix, neutral part, tower, certified windows, two wells, sink counts, twisted contacts |
| HTGeometry, HeckeKreinToeplitz | Hermitian inertia, index comparison |
| Certificate programmes | the floor `1/5000` at ratio `2.06`; a certificate at aperture `½ log(10609/5000)` would give the first step directly |

Route of the finite-scale picture: certificate at one aperture → every block size → overlap
recursion → margin and exponent receivers. GCW is the analysis of the one inequality the
recursion asks for at each step, and of the loss it may afford.

## 10. Big picture

**Developed.** The mediator is a Lean object with its channels, its sign structure, two-sided
bounds, monotonicity in the window and along the tower; the binding energy is pinched between
absolute constants; the loss law is a theorem; the pencil separates `ζ` from its sign twin at
ratio three; the pole plane and the dual elimination give two further normal forms of a step;
thin ends are stiff, the gap of a window is lower semicontinuous, and the bound range ends only
where the gap of the bound windows closes.

**Not reached.** A step. Success for the programme is a proof of the first step with a stated
excess. P13 names one input that gives it: a common gap of the bound windows of its range.

**What a contribution must be.**
- **C1** Uniform in the block size, or monotone along the tower.
- **C2** It reproves part of the certified range without the certificate, or bounds its own loss
  there.
- **C3** It fails for the sign twin and for contact weights in `[−5/2, 19/40]`, or it concerns
  the middle alone.
- **C4** It uses the full rank of the middle.
- **C5** It produces an excess per step, not only a sign.
- **C6** No statement about a finite list of windows; no constant improved without a change of
  conclusion.
