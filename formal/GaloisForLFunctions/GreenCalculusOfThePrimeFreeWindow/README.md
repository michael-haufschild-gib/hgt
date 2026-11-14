# Green Calculus of the Prime-Free Window (GCW)

Namespace `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow`; umbrella
`GreenCalculusOfThePrimeFreeWindow.lean`. Every statement below with a Lean name is a theorem of
this folder unless a neighbour is named (MAFT = MixingArithmeticOfTheFloorTrees, AGZ =
AbsoluteGeometryOfSpecZ, WTZ = WindowTowerOfSpecZ). Statements under "Open" are not theorems.

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
boundary data. It determines the mediator (sign structure, size, monotonicity), turns a step
into inequalities between explicit forms, proves which inequalities cannot work, and says what
a step is in the continuum: the ground energy of Weil's form on one aperture.

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
| Floor of Weil's form | `WeilFloor A c`, `EvenWeilFloor`, `OddWeilFloor` | `𝔚(F) ≥ c ∫F²` on the real `C²` tests supported in `[−A, A]`; on the even tests; on the odd tests |
| Ground energy of an aperture | `ccmRestrictedWeilGroundEnergy A` (RHTower) | the infimum of Weil's form on the unit tests of `[−A, A]`; strictly decreasing in `A` |
| Floor on step packets | `StepFloor Q A c`, `PencilStepFloor w Q A c` | `c Σσ² ≤ 𝔚(σ)` on the step packets of every window inside `A`, at every block size; the same for the pencil |
| Pencil of the prime two | `pencilStepForm w`, `pencilCombForm w`, `pencilWeilForm w` | Weil's form with the contact of `2` weighted by `w`, on step packets, combs (`doubleContact`: `Σ c_m c_{2m}`) and smooth tests; `w = 1` is `ζ`, `w = −1` the sign twin |

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
- A window `(R, R + J]` **lies inside the aperture** `A` if `log((R + J)/R) < 2A`: its step
  packets are tests of Weil's form on an interval of length less than `2A`.
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
12. **A window is a test interval.** On charge-free packets the neutral part of `(R, R + J]` is
   Weil's form of a step packet. So the ground energy of an aperture is a floor of every
   window inside it on its charge-free packets, at every block size. The ground vector of the
   middle cancels the charge of the ends, so the same number bounds the Schur complement on
   the ends from below: it is the excess of the step. Weil's form splits into even and odd
   tests on the aperture; the split is made on smooth tests, parity is not a symmetry of step
   packets.
13. **The sign gives the gap.** The ground energy decreases strictly with the aperture.
   Nonnegative at `A`, it is positive at every smaller aperture, and all windows inside have a
   common positive gap.
14. **The comb carries a floor back to the tests.** A floor on the step packets of a window is,
   up to `η`, a floor of Weil's form on the block functions of its comb `(RB, (R + J)B]` for all
   large `B`. Far from the origin (`log R ≥ C_Q²/η + κ`) the form of a divisor is at least the
   form of its block averages plus `κ` times the mass of the rest, so the floor passes to every
   divisor of the comb. The samples of a `C²` packet at the scale `rB` live on the comb of a
   window inside the aperture, and the comb form tends to the sum over the zeros.
15. **The pencil passes through the comb.** The contact of two on a comb, `2 log 2 Σ c_m c_{2m}`,
   is bounded by the mass, so the block averages carry it up to the mass of the rest. On block
   functions of even block size it is exactly the graph of the floor map of two (half of a block
   doubles into one block, half into the next); on samples it is a Riemann sum of
   `∫ f(u) f(u + log 2)`. Mechanism 14 therefore holds for `𝔚 + (1 − w) C₂` at every weight `w`.
   Inside a window of ratio `≤ 3` every reweighting of the contacts is the pencil at its weight
   of two, and below `log 3` the Liouville twist of Weil's functional is the pencil at `w = −1`.

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
`hasGap_neutralWindow_iff`: a window has the gap `c` iff `N_W − c` has at most one negative
square (Poincaré inequality of the Doob chain); the gap of `(mR, mR + mJ]` is a gap of
`(R, R + J]` (`hasGap_neutralWindow_of_hasGap_refined`).

**P14 The ground energy of an aperture is a gap of every window inside it.**
`hasGap_neutralWindow_of_le_groundEnergy`: if `log((R + J)/R) < 2A` and `R + J < (Q + 1)R`,
the neutral part of `(R, R + J]` is at least the ground energy of `A` on its charge-free
packets. `overlapSchur_form_ge_of_floor`, `greenForm_add_excess_le_of_floor`: a floor `c ≥ 0`
of a window on its charge-free packets gives `B G₊ Bᵀ + c ⪯ N_e + (Bφ)(Bφ)ᵀ/μ` on the ends.
`WeilFloor.of_even_of_odd`: a floor is needed on the even and on the odd tests only.
`riemannHypothesis_iff_exists_gap_neutralWindow`, `riemannHypothesis_iff_gap_of_bound_windows`:
RH holds iff at every cutoff the windows have a common positive gap, iff the bound windows
have one. The continuity method of P13 loses nothing.

**P15 The first step.** WTZ proves the floors `1/2000` and `1/50000` of Weil's form on the
odd and on the even tests of the aperture `1881/5000`, and `log(10609/5000) < 2 · 1881/5000`.
`hermNegIndex_neutralWindow_firstStep`, `hasGap_neutralWindow_firstStep`: every window of ratio
at most `10609/5000` has exactly one bound state and the gap `1/50000`, at every block size and
for every cutoff `Q ≥ 2`. `greenForm_firstStep`: on the two ends of a window of the first step
`B G₊ Bᵀ + 1/50000 ⪯ N_e + (Bφ)(Bφ)ᵀ/μ`. `hermNegIndex_dressedMiddle_firstStep`: the middle
dressed by both ends holds one bound state. `schurStepExcess_eq_zero_of_le_groundEnergy`: if
`log(ρ²/2) < 2A` and `ρ²/2 < Q + 1`, the excess of the steps of ratio `ρ` vanishes at every
level `C ≥ −c`, for `0 ≤ c < 1/5000` at most the ground energy of `A`;
`schurStepExcess_firstStep`, `levelAt_one`: the first step has no excess down to the level
`−1/50000`, and the ladder to ratio three starts at its second step without loss.

**P16 The ground energy of an aperture is the floor of Weil's form on the windows inside it.**
For `Q ≥ e^{2A}`, `stepFloor_iff_le_groundEnergy`: `c ≤ E(A)` iff `c Σσ² ≤ 𝔚(σ)` on the step
packets of every window inside the aperture, at every block size; equivalently on their block
matrices (`le_groundEnergy_iff_forall_blockWindow_form_ge`). `WeilFloor.of_stepFloor`: a floor on
those step packets is a floor on the `C²` tests of every smaller aperture (mechanism 14).
`exists_stepPacket_lt_of_groundEnergy_lt`: below every level above `E(A)` some window inside,
at some block size, carries a step packet. `groundEnergy_nonneg_iff_forall_weilSchur_nonneg`:
for `Q ≥ 2`, `E(A) ≥ 0` iff the overlap law in the normal form of Weil's form (P9) holds on every
window inside the aperture. A step in Weil's normal form is the sign of one ground energy, no
less and no more.

**P17 The sign twin fails the first step of Weil's form.** `pencilWeilForm_ge_of_stepFloor`,
`exists_stepPacket_pencil_lt`: the transfer of P16 holds for the pencil at every weight `w`
(mechanism 15). `reweightedPacketForm_stepPacket_eq_pencilStepForm`: on windows of ratio `≤ 3`
a reweighting `ω` of the contacts is the pencil at `ω(2)`, for every cutoff `Q ≥ 2`.
`exists_firstStep_window_signTwin_lt`: for every `Q ≥ 2` and every `ω` with `ω(2) = −1`, some
window of ratio `≤ 10609/5000`, at some block size, carries a step packet with
`Σ σ_j σ_l W_ω(R + j, R + l) < −(1/1000) Σ σ_j²`, where `ζ` has the floor `1/50000` (P15). The
witness is the odd test of the aperture `181/500` on which the Liouville twist of Weil's
functional is negative (SelectivePositivityAndThresholdLaws). A proof of the first step in
Weil's normal form must use the sign of the contact of two.

## 6. Tools

**From the corpus.** Haynsworth additivity (`hermNegIndex_fromBlocks_transpose`), the overlap
decomposition (`neutralWindow_submatrix_overlapEquiv`), the certified floor on charge-free
packets (`sum_neutralBlock_ge_of_short`, `sum_blockMatrix_ge_of_short`), refinement
(`sum_neutralBlock_refine`), negativity off the diagonal (`neutralBlock_neg`), two wells and the
Hodge index inequality on the positive cone (`hermNegIndex_le_one_iff_forall_wells_bound`), sink
counts (`hermNegIndex_le_one_add_card_sinks`), narrow windows
(`one_lt_blockPotential_of_narrow`), Weil's form of a step packet against the ground energy
(`groundEnergy_mul_nested_mass_le_packetForm_of_log_lt`), the ground energy as a function of
the aperture (RHTower and ArithmeticContinuationAndCriticalEnergy: strictly decreasing,
positive at every aperture iff RH), the floors of the two sectors at the aperture `1881/5000`
(WTZ).

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
  (`exists_oneBoundState_of_pos_eigenvector_of_hyperplane`); `HasGap` and its equivalence with
  the margin (`hasGap_iff_hermNegIndex_add_diagonal_le_one`).
- The transfer from an aperture to the windows inside it: floors, gaps, the excess of a step,
  its levels (`neutralWindow_floor_of_le_groundEnergy`, `overlapSchur_form_ge_of_floor`,
  `overlapSchurLevel_nonneg_of_floor`).

## 7. Questions and open topics

| # | Question | Status |
|---|---|---|
| 1 | Two-sided bounds for the sliver blocks of `G_D` | answered: positive definite, between `1/(C log 2D)` and `5000`; the order `1/log D` is attained |
| 2 | A lower bound for `μ_D` uniform in `D` | answered: `1 < −N(1,1) ≤ μ_D < 3`, nondecreasing along the tower |
| 3 | The first step | answered: it holds at every block size with the excess `1/50000` (P15). It is the floor of Weil's form at the aperture `1881/5000` carried to the matrices (P14); no bound for `G_D` enters. In Weil's form it fails for the sign twin (P17) |
| 4 | The excess of a step as a function of the ratio | defined, bounded, monotone (P6); additive (P5); a thin step loses at most `B²/log(1/δ)` of the floor (P12); zero, down to the level `−c`, as long as `ρ²/2` lies inside an aperture of ground energy `≥ c` (P15); a common gap of the bound windows is RH (P14); in Weil's normal form a step at every block size is the sign of the ground energy of its aperture (P16) |
| 5 | The Green kernel of the continuum form in closed form | open; normal forms only (mechanisms 2, 3, 8) |

**Open.**
- *A proof of a step through the middle.* P15 obtains the first step from the aperture. No
  proof from the Green matrix is known: `M_D − Σ₁` and `M_D − Σ₂` each hold one bound state,
  the first step is the same for `M_D − P N_e⁻¹ Pᵀ`, whose attraction is `Σ₁ + Σ₂` up to the
  jets between the ends, and no inequality of the corpus compares the three without the floor
  of the aperture.
- *The sign of the dipole on the neutral part.* Any proof of a step at ratio three must use it
  (P7), and so must any proof of the first step in Weil's form (P17). Whether the neutral part
  of the sign twin holds a second bound state on the first step is not decided: the witness of
  P17 is odd and its charge is not controlled.
- *The later steps.* By P14 and P15 the steps at the ratios `2.25, 2.53, 3.21` are the ground
  energies of the apertures `½ log(ρ²/2)` of the preceding ratios. An excess that does not come
  from the aperture is not known: the envelopes of P6 carry the factor `5000`, and the dual
  law bounds the attraction by `(4/3)‖P‖²`.
- *The converse at one aperture for the neutral part.* For Weil's form it holds (P16). One bound
  state of every neutral window inside an aperture is not known to give a nonnegative ground
  energy there: the neutral part differs from Weil's form by the pole plane, and the proof of
  AGZ uses windows far outside the aperture.
- *An a priori gap from boundness.* The Hodge index inequality on a bound window gives a gap
  `≥ 0` and no more; a positive lower bound from boundness alone is RH (P14).
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
| The certified range `J ≤ 53R/50` is sharp | Windows up to ratio `10609/5000` have the gap `1/50000` at every block size (P15) |
| An a priori gap of the bound windows is less than RH | It is RH (P13, P14) |
| The first step is a statement about the Green matrix | It is the ground energy of one aperture; the Green form of the step is a consequence (P14, P15) |
| Parity splits the window matrices | It splits Weil's form on the smooth tests of a symmetric aperture; a step packet has no parity |
| One bound state of the windows inside an aperture is the sign of its ground energy | For Weil's form on the windows inside it, it is (P16). For the neutral part only the sign gives the bound state (P14); the converse is known for all apertures together (AGZ) |
| Below ratio three the first step is decided by the sizes of the contacts | The sign twin has the same sizes and fails it in Weil's form (P17) |
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
| WindowTowerOfSpecZ and the certificate programmes | floors of Weil's form on an aperture: `1/5000` at ratio `2.06`, the two sectors at `1881/5000`. GCW carries a floor at an aperture to every window inside it, as a gap and as the excess of the step (P14) |
| RHTower (CCM), ArithmeticContinuationAndCriticalEnergy | the ground energy of an aperture, its strict monotonicity, RH as its sign |
| HodgeTheoryOfAFixedPart | the comb of a window, block averages, samples of a packet: the way back from step packets to smooth tests (P16, P17) |
| SelectivePositivityAndThresholdLaws, SquareRootThreshold | the Liouville twist of Weil's functional and its odd witness at `181/500`; below `log 3` the twist is the pencil at `w = −1` (P17) |

Route of the finite-scale picture: certificate at one aperture → every block size → overlap
recursion → margin and exponent receivers. GCW is the analysis of the one inequality the
recursion asks for at each step, and of the loss it may afford.

## 10. Big picture

**Developed.** The mediator is a Lean object with its channels, its sign structure, two-sided
bounds, monotonicity in the window and along the tower; the binding energy is pinched between
absolute constants; the loss law is a theorem; the pencil separates `ζ` from its sign twin at
ratio three; the pole plane and the dual elimination give two further normal forms of a step;
thin ends are stiff, the gap of a window is lower semicontinuous, and the bound range ends only
where the gap of the bound windows closes. The first step holds at every block size with the
excess `1/50000`; the excess of a step is bounded by the ground energy of its aperture; RH is
a common positive gap of the bound windows. The ground energy of an aperture is exactly the
common floor of Weil's form on the windows inside it, so a step in Weil's normal form is its
sign; the first step of Weil's form fails for the sign twin.

**Not reached.** A proof of a step from the Green matrix of the middle: the first step comes
from the floor of Weil's form at its aperture, and the calculus carries it to the matrices.
The steps at the ratios `2.25, 2.53, 3.21` wait for the ground energies of their apertures. A
closed form of the Green kernel.

**Success.** A step proved with a stated excess (reached for the first step, through the
aperture); a proof of a step that uses the middle and fails for the sign twin (open); an
excess that sums below the binding energy along the ladder (open, and RH).

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
