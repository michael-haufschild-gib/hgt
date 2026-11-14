# Green calculus of the prime-free window (GCW) — programme card

- **ID:** gcw-programme
- **Stage:** 1-in-progress
- **Type:** programme (review-1311 obstacles-summary §2.9, §2.21; B194, B195, A162)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.9
- **Lean:** `formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/`, umbrella
  `formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow.lean`, README in the folder.

## Goal
Potential theory of the inverse `G_D` of the neutral part of the dyadic window `(D, 2D]`, the
mediator of the overlap law (MAFT `hermNegIndex_neutralWindow_overlap_eq_one_iff`). Questions:
(1) two-sided bounds of the sliver blocks of `G_D` uniform in `D`; (2) lower bound for `μ_D`;
(3) first overlap step in Green form; (4) excess per step; (5) closed form of the Green kernel.

## Notation
`F(n) = n log n`, `ΔF(m) = F(m+1) − F(m)`, `D(n) = Δ²F`, `κ = γ + log 2π`.
`N⁰(x,y) = δ ϱ(x) − ½(D(x+y+1) + D(|x−y|))`, `ϱ(x) = ΔF(x) − κ`. `M_D = N⁰` on `[D, 2D)`.
Window `(R, 2D+b]`, `D = R+a`: ends `E₁ = (R, D]`, `E₂ = (2D, 2D+b]`.

## Mathematical targets
- P1 middle prime-free: `x<y<2x ⇒ ⌊y/k⌋<x` for `k≥2`; `neutralWindow Q D D = neutralWindow 1 D D`.
- P2 flat-packet bound: `μ_D ≥ −N⁰(1,1) = κ + ½D(3) − 2 log 2 ≈ 1.199` (constant vector,
  `sum_neutralBlock_dyadic`).
- P3 potential floor: `M = V + 𝓔`, `𝓔 ⪰ 0` ⇒ `μ_D ≤ −min V_D`; closed form
  `V(x) = ΔF(x) − κ − ½[ΔF(x−A) + ΔF(B−1−x)] − ½[ΔF(x+B) − ΔF(x+A)]` on `(A, B]`.
- P4 loss law without derivative: if `M+C` invertible, `≥ 0` on `φ^⊥`, and Schur complement
  `S_C ⪰ −x`, then `N+C+x` is `≥ 0` on the hyperplane `⟨m + (M+C)⁻¹Pe, φ⟩ = 0`, so index `≤ 1`.
  With parts of index `≤ 1` at level `C < μ_D`: `S_C` has PSD diagonal blocks, `S_C ⪰ −‖X_C‖`.
- P5 inverse antitone at equal index: `A ⪯ B`, both invertible of the same index ⇒
  `B⁻¹ ⪯ A⁻¹` (Haynsworth on `[[B, 1],[1, A⁻¹]]` over both corners).
- P6 tower: `(range ι_m)^⊥` is charge-free, so `M_{mD}` is `⪰ 1/5000` there; hence
  `ι_mᵀ G_{mD} ι_m = (M_D − E)⁻¹`, `E ⪰ 0`, and `G_D ⪯ ι_mᵀ G_{mD} ι_m` by P5.
- P7 pencil: ratio `≤ 3`: `P_i = −𝒥_i − w𝒞_i`, `S(w) = S(0) − wΞ − w²Π`,
  `Π = 𝒞ᵀG𝒞` (sliver blocks), `Ξ = 𝒥ᵀG𝒞 + 𝒞ᵀG𝒥`; twin = `w ↦ −w`.
- P8 exact Green identities: `G_D φ = −φ/μ`, `G_D V_D = 𝟙`, `G_D v_S = χ_S` for sub-windows `S`.
- P9 magnitude reading (not a theorem): floors at aperture `≈0.36` are of prolate size
  (`10⁻³–10⁻²`), so `‖G₊‖` is large; crude norm bounds cannot give the first step.
- P10 pole plane: for `M` with one bound state, `x·(M + p⊗q + q⊗p)x = z·Mz +
  ⟨p,x⟩²((1+β)² − αγ)/α` with `z = x + ⟨p,x⟩(Gq − ((1+β)/α)Gp) ⊥ p`; `M ≥ 0` on `p^⊥` iff
  `α ≤ 0`. Woodbury with the `2×2` pole matrix gives the inverse.
- P11 dual elimination: for ends with `16a ≤ R`, `8b ≤ R + a` (the first two steps of the
  ladder) the ends `E` are narrow, `N_e` has row sums `≥ 3/4` (narrow potential `> 1`; jets
  between the ends `≤ 2/D` each; no contact since `2x + 2 ≤ y < 3x`), so `N_e ⪰ 3/4` and
  `N_e⁻¹ ≥ 0` entrywise (negative part of `N_e⁻¹w` has nonpositive energy). Haynsworth over
  `N_e`: `ind N_W = ind(M_D − P N_e⁻¹ Pᵀ)`. `P < 0` entrywise, so the dressed middle keeps
  negative entries off the diagonal; AGZ two wells and sink counts apply on the middle.
- P12 thin end: on `(R, R+J]` with `KJ ≤ R`, `K ≥ 16`, `V_j ≥ log K − 2` (density `log(R+j)`
  minus half the jets `log j + log(J−j) ≤ 2 log(J/2)`), so `N ⪰ log K − 2` (row sums, entries
  `≤ 0` off the diagonal). Coupling of adjacent windows: jets `≤ 4/((J−i)+(l+1))`, Hilbert
  gives norm `≤ 24`; contacts by Schur `≤ 2 Σ_{k≤Q}Λ(k)`. Block form with `A ⪰ c` on `ψ^⊥`,
  `E ⪰ s`, `‖P‖ ≤ B`: `≥ cx + sy − 2B√(xy) ≥ (c−ε)(x+y)` if `s ≥ c − ε + B²/ε`. So an end of
  relative width `δ` costs at most `≈ B²/log(1/δ)` of the floor; losses of a chain of thin
  ends of fixed total width are not summable (one step is the best use).
- P13 continuity method: gap `c` := form `≥ c` on a hyperplane. Gap decreases with the window
  (restriction), is lower semicontinuous (P12). At block size `KR`, `log K ≥ c/2 + 2B²/c + 2`,
  one block is a thin end: from the certified `(KR, 2KR]`, bound ⇒ gap `c` (hypothesis) ⇒
  next window has gap `c/2 > 0` ⇒ bound; up to `KJ`; refinement gives `(R, R+J]`.
  Gap = margin: for symmetric `G` with entries `≤ 0` off the diagonal and a positive
  eigenvector, `ind(G − c) ≤ 1` gives a gap `c` on the hyperplane orthogonal to the
  eigenvector (Poincaré inequality of the Doob chain); so a gap of `(mR, mR + mJ]` is a gap of
  `(R, R + J]` (refinement preserves the index at every level).
- P14 transfer from the aperture: a step packet of `(R, R+J]` is a test of Weil's form on an
  interval of length `log((R+J)/R)`; on charge-free packets the neutral form is Weil's form
  (`R + J < (Q+1)R`), hence `≥ E(A)·Σσ²` if `log((R+J)/R) < 2A`, `E(A)` the ground energy of
  the aperture. So `E(A)` is a gap of every window inside the aperture (hyperplane: charge
  zero), at every block size. Charge cancellation on the ground vector of the middle turns
  the floor on charge-free packets into `S ⪰ c` on the two ends: the excess of the step.
  Weil's form splits into even and odd tests (on smooth tests; parity is not a symmetry of
  step packets). `E` is strictly decreasing in the aperture, so `E(A) ≥ 0` gives `E > 0`
  inside: RH ⇒ common positive gap of the windows of every cutoff. With P13: RH ⟺ a priori
  gap of the bound windows.
- P15 levels from a floor: floor `c ∈ [0, 1/5000)` on charge-free packets ⇒ `N_W − c` has
  index `≤ 1`; the middle keeps one bound state at level `−c`; Haynsworth ⇒ `S_{−c} ⪰ 0`;
  unit speed in the level ⇒ `S_C ⪰ 0` for `C ∈ [−c, μ)`. A `ρ`-step window has ratio
  `≤ ρ²/2`: if `log(ρ²/2) < 2A`, `ρ²/2 < Q + 1`, `c ≤ E(A)`, the excess of the `ρ`-steps
  vanishes at every level `≥ −c`. First step: `ρ = 103/50`, `A = 1881/5000`
  (`log(10609/5000) < 0.7524`), odd floor `1/2000`, even floor `1/50000` (WindowTowerOfSpecZ).
- P16 the way back: a floor `c` on the step packets of `(R, R+J]` is, up to `η`, a floor on the
  block functions of the comb `(RB, (R+J)B]`, `B → ∞`; for `log R ≥ C_Q²/η + κ` the form of a
  divisor is `≥` the form of its block averages `− η·mass + κ·mass(rest)`, so the floor passes
  to every divisor; the samples of a `C²` packet at scale `rB` live on the comb of a window
  `(3r, 3r+J]` inside the aperture; comb form → sum over the zeros. Hence
  `c ≤ E(A) ⟺` floor on the step packets of all windows inside `A` at all block sizes
  (`Q ≥ e^{2A}`), and `E(A) ≥ 0 ⟺` Weil's overlap law (`weilSchur ⪰ 0`) on those windows.
- P17 pencil `𝔚_w = 𝔚 + (1 − w)C₂`: `C₂` on combs is `2 log 2 Σ c_m c_{2m}`, bounded by the mass
  (`|ΔC₂| ≤ pΣs² + (q+1)Σ(c−s)²`, `pq = 1`), exactly the floor graph of two on block functions
  of even block size, a Riemann sum of `∫f(u)f(u + log 2)` on samples. So P16 holds for every
  `w`. Below `log 3`: Liouville twist of Weil's functional = pencil at `w = −1`; on windows of
  ratio `≤ 3` every reweighting = pencil at `ω(2)`, independent of `Q ≥ 2`. The odd witness at
  `181/500` (Liouville `< −(1/1000)∫F²`) inside aperture `37/100` (`e^{0.74} ≤ 3`,
  `0.74 ≤ log(10609/5000)`) gives a first-step window with a step packet below `−1/1000`.

## Modules
Compile clean, wired into the umbrella. Mine (M) and a second agent's (P; paper card
`../3-formalized/gcw-sliver-bounds-ratio-excess-and-ratio-three.md`, source §2.21).
1. (M) `TheGreenMatrixOfTheDyadicMiddleHasABoundStateChannelAndAPositiveChannel` — `OneBoundState`,
   `positiveChannel`, `primeFreeMiddle` (P1), `bindingEnergy > 1` (P2), `greenMatrix`,
   `overlapSchur`, overlap law in Green form, `riemannHypothesis_iff_forall_greenForm`.
2. (M) `TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle` — levels, Dirichlet
   principle `positiveChannel_ge`, `S_C` grows at unit speed, P4, additive loss law, RH forms
   (`…_overlapSchur_bddBelow`, `…_forall_overlapSchur_nonneg`, `…_of_level_function`).
3. (P) `ChargeCancellationPreservesTheCertifiedFloor` — floor for `J < R`, charge-cancellation
   Schur floor, neutral-orthogonal overlap criterion.
4. (M) `TheCertifiedFloorsAreAPrioriBoundsForTheGreenMatrixAndTheConditionalEnergies` —
   `−1 ⪯ G_D ⪯ 5000`, floors of the conditional energies, first step from coupling `≤ 1/5000`.
5. (M) `TheGreenFormOfABoundWindowGrowsWithTheWindowAndAlongTheRefinementTower` — reversed C–S,
   compression monotonicity (P5 in compression form), domain monotonicity, `0 ⪯ G_D` on slivers
   (bulk of ratio `≥ 4/3`), tower law `G_D ⪯ ι_mᵀ G_{mD} ι_m`, `μ_D ≤ μ_{mD}` (P6).
6. (P) `TheSliverBlocksOfTheGreenMatrixHaveALogarithmicDiagonalAndBulkDipoleCoupling` —
   `μ_D < 3`, diagonal `Θ(1/log D)` for `D ≥ 2^256`, `endJet`, `endContact`, `pencilCoupling`,
   failure of weights in `[−4, 0]` on `(R, 3R]`, sign-twin obstruction.
7. (P) `TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree` — excess functions, Hilbert
   bounds, ladder `2.06 → 3.21`, rigidity `(∀k, level_k = 0) ↔ RH`.
8. (M) `TheContactPencilOfTheOnePrimeRangeIsConcaveInTheWeightOfThePrimeTwo` — duality of the
   Green form (`inv_form_nonneg_iff`), `pencilSchur`, normal form
   `S(t) = S(0) − 2tΞ − t²Π` (P7), `Π ⪰ 0` (`contactGreen_nonneg/_pos`), concavity, admissible
   weights form an interval, at ratio three all admissible weights have one sign and
   `not_hermNegIndex_eq_one_of_weight_nonpos`.
9. (M) `TheGreenMatrixOfTheMiddleIsNegativeOnlyAlongItsPotentialAndPositiveOnChargeFreePackets`
   — charge formula `⟨w,Gw⟩ = (Σw)²/(D·N(1,1)) + ⟨w₀,Gw₀⟩`, `G_D ≻ 0` on charge-free packets,
   `OneBoundState.inv` (class closed under inversion), Gershgorin `M_D ⪯ 2 log 2D + 3`,
   quantitative positivity off a negative vector, lower bounds `1/(8 log 2D + 21)` (charge-free),
   `1/(152 log 2D + 453)` (slivers, diagonal for `D ≥ 2`, contact form), overlap law and RH in
   charge form (P8).
10. (M) `ThePolePlaneAbsorbsTheBoundStateAndTheGreenMatrixOfWeilsFormOnTheMiddleIsPositive` —
   `withPoles M p q = M + p⊗q + q⊗p`; pole normal form and pole criterion (positive definite
   iff `[[α, 1+β],[1+β, γ]] ≺ 0`, `α = ⟨p,Gp⟩`, `β = ⟨p,Gq⟩`, `γ = ⟨q,Gq⟩`); inverse through
   the pole matrix (`poleSolution`), `G ⪯ (M + poles)⁻¹`; `weilMiddle D = M_D + d⊗𝟙 + 𝟙⊗d`;
   `⟨d,G_D d⟩ < 0`, `(1+⟨d,G_D𝟙⟩)² < ⟨d,G_D d⟩⟨𝟙,G_D𝟙⟩`, `⟨d,G_D𝟙⟩ < −1/2`; `weilGreen D`
   positive definite, `‖w‖²/(2 log 2D + 5) ≤ ⟨w,𝒢_D w⟩ ≤ 5000‖w‖²`; overlap law for Weil's
   form (`weilSchur`), `riemannHypothesis_iff_forall_weilSchur_nonneg` (P10).
11. (M) `TheFirstOverlapStepIsOneBoundStateOfTheMiddleDressedByTheAttractionOfItsTwoEnds` —
   ends with `16a ≤ R`, `8b ≤ R + a` are `⪰ 3/4` without a certificate (`endForm_form_ge`);
   inverse of a positive definite matrix with entries `≤ 0` off the diagonal preserves
   positivity; `endAttraction = P N_e⁻¹ Pᵀ` (PSD, entrywise `≥ 0`, `⪯ (4/3) P Pᵀ`);
   `dressedMiddle` (negative off the diagonal, `⪯ M_D`, least energy of the window over the end
   packets); dual overlap law `hermNegIndex_neutralWindow_eq_dressedMiddle`; step ⟺ Hodge index
   inequality of the dressed form on disjoint positive packets of the middle; certificate by a
   positive trial vector; each end alone leaves one bound state (P11).
12. (M) `AThinEndIsLogarithmicallyStiffAndAFloorExtendsTheBoundRange` — potential of a thin
   window `≥ log K − 2`, form `⪰ log K − 2`; `adjacentCoupling` of two adjacent windows, norm
   `≤ 24 + 2 Σ_{k≤Q}Λ(k)` at every block size (`≤ 26` up to ratio three); window = first part +
   adjacent part + coupling (`neutralWindow_submatrix_finSumFinEquiv`); dual law for a thin
   tail, attraction `⪯ 676/(log K − 2)`; stiff corner lemma; floor `c` ⇒ floor `c − ε` on
   `(R, R+J+j]`, `Kj ≤ R+J`, `log K ≥ c − ε + B²/ε + 2`; one bound state with floor `1/10000`
   beyond the certified range (`log K ≥ 6760003`) (P12).
13. (M) `TheBoundRangeEndsOnlyWhereTheGapOfTheBoundWindowsCloses` — `HasGap`; gap decreases
   with the window, lower semicontinuous; continuity method
   `hermNegIndex_neutralWindow_eq_one_of_gap` (cutoff `Q`, ratio `≤ a/b`: bound ⇒ gap `c` for
   one `c > 0` gives all bound); `exists_bound_window_without_gap` (unconditional: an unbound
   window is preceded, at smaller ratio, by bound windows without gap `c`, every `c > 0`);
   `riemannHypothesis_of_gap_of_bound_windows` (P13). Gap = margin
   (`hasGap_iff_hermNegIndex_add_diagonal_le_one`, `hasGap_neutralWindow_iff`); the gap
   decreases along the tower (`hasGap_neutralWindow_of_hasGap_refined`); loss of a thin step
   at every level; gap `1/10000` beyond the certified range at every block size
   (`hasGap_neutralWindow_beyond_certified`).
14. (M) `TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt` — `WeilFloor`,
   `EvenWeilFloor`, `OddWeilFloor`; floor ⇒ ground energy (`WeilFloor.le_groundEnergy`),
   parity (`WeilFloor.of_even_of_odd`); ground energy ⇒ floor on charge-free packets and gap
   of every window inside the aperture (`neutralWindow_floor_of_le_groundEnergy`,
   `hasGap_neutralWindow_of_le_groundEnergy`); floor ⇒ excess of the step
   (`overlapSchur_form_ge_of_floor`, `greenForm_add_excess_le_of_floor`); first step from the
   even sector at aperture `1881/5000` (odd floor `1/2000` of WindowTowerOfSpecZ); sign ⇒ gap
   (`groundEnergy_pos_of_lt_of_nonneg`); `riemannHypothesis_iff_exists_gap_neutralWindow`,
   `riemannHypothesis_iff_gap_of_bound_windows` (P14).
15. (M) `TheFirstOverlapStepHoldsAtEveryBlockSize` — floor `c ∈ [0, 1/5000)` on charge-free
   packets ⇒ `S_C ⪰ 0` for `C ∈ [−c, μ)` (`overlapSchurLevel_nonneg_of_floor`), excess zero
   (`windowExcess_eq_zero_of_floor`, `schurStepExcess_eq_zero_of_le_groundEnergy`); even floor
   `1/50000` at aperture `1881/5000` (WindowTowerOfSpecZ) ⇒ `E(1881/5000) ≥ 1/50000`; first
   step at every block size for `Q ≥ 2`: one negative square
   (`hermNegIndex_neutralWindow_firstStep`), gap `1/50000`, Green form with excess `1/50000`,
   dressed middle with one bound state, `schurStepExcess Q (103/50) C = 0` for
   `C ≥ −1/50000`, `levelAt Q 1 = 0` (P15).
16. (M) `TheGroundEnergyOfAnApertureIsTheFloorOfWeilsFormOnTheWindowsInsideIt` — `StepFloor`;
   comb transfer (`combForm_ge_blockMean_add_residual`,
   `eventually_combForm_ge_of_stepPacket_floor`, `mul_integral_sq_le_zeroSum_of_eventually`,
   `exists_window_inside_aperture`); `WeilFloor.of_stepFloor`, `stepFloor_iff_le_groundEnergy`,
   `le_groundEnergy_iff_forall_blockWindow_form_ge`, `exists_stepPacket_lt_of_groundEnergy_lt`,
   `groundEnergy_nonneg_iff_forall_weilSchur_nonneg` (P16).
17. (M) `TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin` — `doubleContact`,
   `abs_doubleContact_sub_le`, `two_log_two_mul_doubleContact_blockFunction`,
   `tendsto_doubleContact_sample`; `pencilStepForm`, `pencilCombForm`, `pencilWeilForm`,
   `PencilStepFloor`; `pencilWeilForm_ge_of_stepFloor`, `exists_stepPacket_pencil_lt`;
   `packetForm_stepPacket_eq_two`, `reweightedPacketForm_stepPacket_eq_pencilStepForm`,
   `re_weilFullFunctional_liouville_eq_pencilWeilForm`, `exists_window_signTwin_pencil_lt`,
   `exists_firstStep_window_signTwin_lt` (P17).
18. (M) `TheDipoleOfWeilsGreenMatrixCarriesTheFirstOverlapStep` — `weilPencilCoupling`
   `P_w = W₀ − wC`, `weilPencilSchur`, `weilDipole`, `weilContactForm`; reweighted window in the
   overlap blocks (`reweightedWindow_submatrix_overlapEquiv_weil`), overlap law of the pencil,
   normal form `S_w = S₀ + 2w·dip − w²Π`; `weilSchur_nonneg_firstStep`;
   `exists_firstStep_weilPencilSchur_neg` (twin packet refined ×5000 into `(5000R, 10609R]`);
   `exists_firstStep_weilDipole_pos` (dipole `≥ −S₋₁/4 > 0`, all `w ≤ −1` fail);
   `weilSignTwin_obstruction_firstStep` (P18).
19. (M) `TheContinuumGreenKernelIsTheLimitOfTheTowerAndIsNegativeOnlyAlongTheCharge` —
   `greenForm`, `towerGreen`, `continuumGreen` (sup along `k!·D`), `continuumGreenMatrix`
   (polarization); convergence, tower consistency `𝔊_{mD}(ι_m w) = 𝔊_D(w)`, `G_D ⪯ 𝔊_D ⪯ 5000`,
   `𝔊_D + 𝟙𝟙ᵀ/(Dδ) ⪰ 0`, positive definite on charge-free functions, at most one negative square;
   binding energies converge in `[δ, 3]` (P19).

## Status of the questions
- Q1 sliver blocks: answered. `G_D = −(Σw)²/(D|N(1,1)|) + positive`; on slivers and charge-free
  packets `‖w‖²/(C log 2D) ≤ ⟨w,G_D w⟩ ≤ 5000‖w‖²`; order `1/log D` attained (P, diagonal).
- Q2 `μ_D`: `−N(1,1) ≤ μ_D < 3`, nondecreasing along the tower.
- Q3 first step: answered at every block size, `Q ≥ 2`, ratio `≤ 10609/5000`: one negative
  square, gap and excess `1/50000` (M15). The proof is the floor of Weil's form at aperture
  `1881/5000` (odd `1/2000`, even `1/50000`, WindowTowerOfSpecZ) carried to the matrices
  (M14); it does not go through bounds for the Green matrix. Reductions inside the calculus
  (coupling `≤ 1/5000` M4, dipole M8, dressed middle M11, a priori gap M13) stay unproved by
  their own means. Perturbation from the certified range reaches ends of relative width
  `exp(−6760003)` only (M12). In Weil's form the first step fails for the sign twin: some
  first-step window carries a step packet below `−1/1000` for every `ω` with `ω(2) = −1` (M17);
  in Weil's normal form the dipole `⟨W₀e, 𝒢_D Ce⟩` is positive there and sign-blind bounds fail
  (M18).
- Q4 excess: excess functions and envelopes (P), additive loss law (M2); thin steps: loss of
  the floor `≤ B²/log(1/δ)` (M12), not summable along a chain; gap = margin (M13); excess of
  the `ρ`-steps is zero down to level `−c` while `ρ²/2` lies inside an aperture of ground
  energy `≥ c` (M15); RH ⟺ a priori gap of the bound windows (M14); in Weil's normal form a
  step at every block size ⟺ sign of the ground energy of its aperture (M16).
- Q5 closed form: the kernel exists as the tower limit with closed-form negative part `−1/δ` (M19); positive part open. The continuum form is `log|x| + log|p|` on an interval of ratio two, a
  truncated convolution in the multiplicative variable with the digamma symbol (infinitely many
  poles); in the multiplicative variable the kernel is the finite part of
  `½[1/|x−y| + 1/(x+y)]`, a regional logarithmic Laplacian; no closed form found. Normal
  forms: two channels, charge formula, pole matrix (M10).

## Open after M18
- A proof of a step through the Green matrix of the middle (coupling bound, dipole sign or a
  priori gap), not through the aperture.
- Neutral part of the sign twin on the first step: a second negative square? (M17 decides
  Weil's form; the odd witness has uncontrolled charge.)
- Later steps (`ρ = 2.25, 2.53, 3.21`): ground energies of the apertures `½ log(ρ²/2)`;
  certificates at larger apertures (A140), outside the calculus.
- Converse at one aperture for the neutral part: does one negative square of the neutral
  windows inside an aperture at every block size give `E(A) ≥ 0`? (Holds for Weil's form, M16;
  the pole plane separates the two.)
- A priori gap of a bound window; wide ends; continuum object and closed form.

## Ideas not yet done
- Tower limits: `μ_∞ = sup_D μ_D`, limit of the Green form along the tower (bounded, monotone).
- Composition: Krein formula, Green matrix of a window on its ends is the inverse of the Schur
  complement; one bound state iff positive there.
- Excess is quasi-convex in the contact weight (levels + pencil).
- Explicit charge of the coupling (column sums of `endCoupling` in closed form).

## Log
- 2026-11-14 — card created; README first draft; modules 1–9 above formalized.
- 2026-11-14 — modules 10, 11 formalized; README rewritten as the foundational document.
- 2026-11-14 — module 11 extended to ends `16a ≤ R`, `8b ≤ R + a`; modules 12, 13 formalized.
- 2026-11-14 — modules 14, 15 formalized: ground energy of an aperture as gap and excess; first step at every block size.
- 2026-11-14 — modules 16, 17 formalized: ground energy = floor of Weil's form on the windows inside an aperture; first step of Weil's form fails for the sign twin.
- 2026-11-14 — module 18 formalized: Weil pencil normal form; positive dipole and sign-blind obstruction at the first step.
- 2026-11-14 — module 19 formalized: continuum Green kernel as tower limit, negative part in closed form.
