# Exact Window Visibility Onset Law and Programme Corollaries

- **ID:** window-visibility-onset-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.9 (`A30`, `A34`, `B18`, `B21`, `B22`, `Γ36`, `Γ40`, `Π29`, `Σ28`, `Σ41`, `P1`, `AHD`)
- **Lean:** `formal/GaloisForLFunctions/WindowVisibilityLaw/` (umbrella `WindowVisibilityLaw.lean`, wired into `MainTheorems.lean`). All results unconditional; axioms `[propext, Classical.choice, Quot.sound]`.
- **Statement:** Every tempered zero configuration `Z` has a right-closed window-positivity interval `[0, onsetAperture Z]`; seeing `(V1)` and hiding `(V2)` are exact complements across it, `onsetAperture Z = ⊤ ↔` all zeros on `Re = 1/2`. On the model families the onset aperture obeys exact coherence, depth-mass, smoothness, split-density and perturbation laws stated below.

## Results (paper proof = Lean proof; statements as formalized)

### 1. Closed-interval law and `ζ` / `P1` / `AHD` dictionary — `OnsetApertureAndPositivityDictionary.lean`
Dilation `f_n(u) = f(r_n u)`, `r_n = 1 + 1/(n+1)`, plus dominated convergence over `TemperedConfig Z` gives left-continuity of positivity in `a`.
- `windowPositiveAt_iff_le_onsetAperture`: `0 ≤ a → (WindowPositiveAt Z a ↔ (a : EReal) ≤ onsetAperture Z)`.
- `exists_re_W_neg_iff_onsetAperture_lt`: visible at `a` iff `onsetAperture Z < a`.
- `hodgeDefectAt_eq_zero_iff_le_onsetAperture`; `onsetAperture_eq_top_iff_onLine`.
- `riemannHypothesis_iff_onsetAperture_zeta_eq_top`; `onsetAperture_zeta_eq_contact_of_not_rh`; `zetaWindowPositive_contact_of_not_rh` (positivity holds at the contact aperture itself); `enlargedWeilFloorAperture_le_onsetAperture_zeta`; `windowThreshold_eq_top_iff_le_onsetAperture` (`AHD.windowThreshold A = ⊤ ↔ A/2 ≤ onsetAperture ζ`); `zeta_abs_re_sub_half_lt_of_le_onsetAperture` (closed-endpoint `1/R` excluded depth).

### 2. Coherent clusters and tilt amplification (`A34`) — `CoherentClusterAndTiltAmplificationLaw.lean`
- `windowPositiveAt_multiplicityPairConfig_iff`: multiplicity-`k` pair `½ ± δ + iγ₀` in the doubled `2π/L` on-line lattice, `0 < a ≤ L/2`: `WindowPositiveAt ↔ k · pairEnergy δ a ≤ L`, `pairEnergy δ a = sinh(2δa)/(2δ) − a`.
- Deep regime: `windowPositiveAt_multiplicityPairConfig_of_le_log`, `onsetAperture_multiplicityPairConfig_lt_of_log_le` (`a* ≍ (1/2δ) log(4δL/k)`). Shallow regime: `windowPositiveAt_multiplicityPairConfig_of_cubic_le`, `onsetAperture_multiplicityPairConfig_lt_of_lt_cubic` (`a* ≍ (3L/(2kδ²))^{1/3}`).
- General RvM configurations (`N(t,t+1] ≤ A₀ log(|t|+3)`): test `e^{−iγ₀u} sinh(δu)(a²−u²)₊^{5/2}` achieves `P²/‖f‖² ≥ e^{2δa}/(60·2^{26}δ)`; `windowPositiveAt_coherent_cluster_bound`, `windowPositiveAt_global_sea_cluster_bound` (collar-unshielded clusters obey `M_S e^{2(δ−σ)a} ≲ A₀ δ a log(|γ₀|+…)`); `enlargedWeilFloor_excludes_zeta_coherent_cluster`.

### 3. Shallow dichotomy and crystal barrier (`B21`, `B22`, `Σ28`, `Σ41`, `A30`, `B18`) — `ShallowClusterExclusionAndTaperedCrystalBarrier.lean`
- `macroscopic_coherent_cluster_cancels_log_height`.
- `dci_admissible_coherent_cluster_visible_at_sub_depth`: for `L ≤ k ≤ 20L` the cluster obeys the DCI bound `2kδ² ≤ 40δ²L` yet `onsetAperture < a` once `δ²a³ > 3/2` — naive `(V2)` at `δ ≲ (log log T)/a` fails.
- `windowPositiveAt_of_onLineLattice_and_offLineDepthMass`: over an `m₀`-fold `2π/L` on-line lattice, off-line zeros of depth `≤ σ` and unit-window depth-squared mass `≤ W` hide at `a` whenever `a²(2a+2π)e^{2π}e^{2σa}W ≤ m₀L` — the true non-lattice `(V2)`.
- `windowPositiveAt_biquadraticCrystal_of_le` (`38aLδ²cosh(2δa) ≤ M`), `exists_hidden_inv_aperture_zero_above_single_exp`: for `a ≥ 2`, `L ≥ 4a`, a finite tapered packet hides an exact depth-`1/a` zero at ordinate `2πk₀/L` — single-exponential height is the shielded barrier.
- `doubly_exponential_height_nonlocality`; `contact_law_log_scale_cluster_bound` (`c log T ≤ onsetAperture ζ ⇒ M_S T^{2c(δ−σ)} ≲ …`).

### 4. Split columns and perturbed fragility (`Γ36`, `Γ40`, `Π29`) — `SplitColumnThresholdAndPerturbedFragility.lean`
- `exists_window_re_W_neg_of_one_side_isolation` (right-half-plane isolation of one zero suffices).
- `re_eq_half_of_re_W_nonneg_of_split_columns`: positivity at `a > π D_on + (π/2) D_off` forces the critical line; `onsetAperture_le_half_pi_density_of_all_offLine_columns`; `re_eq_half_of_re_W_nonneg_of_curve_columns_improved` (`(g − ½) log q`).
- `onsetAperture_mixedGenusColumnConfig_eq`: `g ≥ 2`, small `δ`: `onsetAperture = (g − ½)ℓ > (g/2)ℓ = πD/2` — `πD/2` is false for mixed columns; the split law is sharp.
- `onsetAperture_singleDefectOffLineLattice_lt`: shifting one off-line pair by `ε ∈ (0, π/L]` gives `onsetAperture < a` whenever `a ≤ L/2`, `2 ≤ δa`, `960·2^{26}δL < ε²a²e^{2δa}`.
- `windowPositiveAt_perturbedOffLineLatticeConfig`: `|ε_k| ≤ π/(2L)`, `8a²e^{2δa}∑|ε_k| ≤ L ⇒` positive at `a ≤ L/2`.

### 5. Synthesis — `CompleteWindowVisibilitySynthesis.lean`
`window_visibility_closed_interval_law`, `zeta_and_ahd_onset_dictionary`, `onsetAperture_multiplicityPairConfig_mem_deep_interval`, `onsetAperture_multiplicityPairConfig_mem_cubic_interval`, `onsetAperture_perturbedOffLineLatticeConfig_eq` (`2Le^{δL}∑|ε_k| ≤ 1 ⇒ onsetAperture = L/2`), `shallow_coherence_vs_nonlattice_hiding_dichotomy`, `aperture_height_duality_shielded_vs_unshielded`, `split_column_and_perturbed_lattice_dichotomy`, `zeta_programme_consequences_of_window_visibility`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized in `formal/GaloisForLFunctions/WindowVisibilityLaw/`
