import GaloisForLFunctions.ArchimedeanTateDomination.ShiftedPoleResiduePinchingAndNoGo
import GaloisForLFunctions.ArithmeticIncidencePositivity.AnExplicitLargerApertureRetainsAWeilFloor
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.SinglePrimeWindowJumpGraphAndObstructions

/-!
# Unconditional archimedean Tate domination past `log 2` and complete synthesis

This module establishes the unconditional positive-dimension archimedean Tate domination regime
past the first prime fold `log 2` and packages the complete resolution of the archimedean Tate
domination question:

* **Strict Weil floor past `log 2`** (`firstFoldSubstage_bounds`,
  `weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture`): centering `H ∈ W_A` into
  `[−A/2, A/2]` transports the enlarged aperture floor `1/8000` to every window
  `0 ≤ A ≤ 2 · enlargedWeilFloorAperture`, with
  `log 2 < 181/250 < 2 · enlargedWeilFloorAperture < 1 < log 3`.
* **Unconditional first-fold domination** (`firstFoldStage_linearDomination`,
  `firstFoldStage_backwardTateGammaDomination`, `firstFoldStage_symTateGammaDomination`,
  `firstFoldSubstage_explicit_primeTwo_domination`): across `[0, 2 · enlargedWeilFloorAperture]` —
  including the nonempty first-fold sub-stage `[log 2, 2 · enlargedWeilFloorAperture]` where the
  reduced point count is `√2 (2^k − 1) ∫ H(u) H(u + log 2) du` — all three canonical archimedean
  Tate families dominate `tatePointCount A H k` unconditionally on explicit uniform horizons.
* **Complete dichotomy synthesis** (`archimedean_tate_domination_complete_solution`): combines
  dimension-zero inheritance, `1`-jet compatibility of the unshifted and shifted Tate families,
  unconditional domination past `log 2`, unshifted global impossibility and doubly-exponential
  horizon collapse, and shifted-pole residue pinching to `1 / ζ(1 + k)` with global impossibility
  across all pole weights `φ ∈ ℝ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.ArchimedeanTateDomination

open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
open ArithmeticIncidencePositivity ArithmeticCastelnuovoSeveri ArithmeticCriticalityTheory
open ArithmeticDegenerationTheory LatticeSectionTheory.WindowJumpCounts
open _root_.RHTower _root_.RHTower.WeilMarkovPole

/-! ### `1`-jet compatibility of the full Gamma-plus-pole Tate families -/

theorem hasDerivAt_backwardTateGamma_add_windowPole_zero {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) :
    HasDerivAt (fun k => backwardTateGammaForm k H + k * windowPoleForm H)
      (archWindowForm H) 0 := by
  rw [archWindowForm]
  exact (hasDerivAt_backwardTateGammaForm_zero hH).add
    (((hasDerivAt_id (0 : ℝ)).mul_const (windowPoleForm H)).congr_deriv (one_mul _))

theorem hasDerivAt_symTateGamma_add_windowPole_zero {A : ℝ} {H : ℝ → ℝ}
    (hH : IsWindowTest A H) :
    HasDerivAt (fun k => symTateGammaForm k H + k * windowPoleForm H)
      (archWindowForm H) 0 := by
  rw [archWindowForm]
  exact (hasDerivAt_symTateGammaForm_zero hH).add
    (((hasDerivAt_id (0 : ℝ)).mul_const (windowPoleForm H)).congr_deriv (one_mul _))

theorem hasDerivAt_backwardTateGamma_add_shiftedPole_zero {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : IsWindowTest A H) :
    HasDerivAt (fun k => backwardTateGammaForm k H + k * shiftedPoleForm k H)
      (archWindowForm H) 0 := by
  rw [archWindowForm]
  exact (hasDerivAt_backwardTateGammaForm_zero hH).add
    (hasDerivAt_mul_shiftedPoleForm_zero hA hH)

theorem hasDerivAt_symTateGamma_add_shiftedPole_zero {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : IsWindowTest A H) :
    HasDerivAt (fun k => symTateGammaForm k H + k * shiftedPoleForm k H)
      (archWindowForm H) 0 := by
  rw [archWindowForm]
  exact (hasDerivAt_symTateGammaForm_zero hH).add
    (hasDerivAt_mul_shiftedPoleForm_zero hA hH)

/-! ### Strict Weil floor and unconditional domination past `log 2` -/

/-- The explicit enlarged window bound `2 · enlargedWeilFloorAperture` strictly exceeds `log 2`
(`> 181/250`) and lies strictly inside the first-fold stage `[log 2, log 3)`. -/
theorem firstFoldSubstage_bounds :
    Real.log 2 < 181 / 250 ∧
      181 / 250 < 2 * enlargedWeilFloorAperture ∧
      2 * enlargedWeilFloorAperture < 1 ∧
      1 < Real.log 3 := by
  obtain ⟨hl, hu⟩ := enlargedWeilFloorAperture_bounds
  have hlog2 := Real.log_two_lt_d9
  have hexp1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp1
  exact ⟨by linarith, by linarith, by linarith, hlog3⟩

/-- Every window `A ∈ [log 2, 2 · enlargedWeilFloorAperture]` has exact level `windowLevel A = 2`. -/
theorem windowLevel_eq_two_of_mem_firstFoldSubstage {A : ℝ}
    (h2 : Real.log 2 ≤ A) (hA : A ≤ 2 * enlargedWeilFloorAperture) :
    windowLevel A = 2 := by
  have hb := firstFoldSubstage_bounds
  have hlt3 : A < Real.log 3 := hA.trans_lt (hb.2.2.1.trans hb.2.2.2)
  have hexp2 : (2 : ℝ) ≤ Real.exp A := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ Real.exp A := Real.exp_le_exp.mpr h2
  have hexp3 : Real.exp A < (3 : ℝ) := by
    calc Real.exp A < Real.exp (Real.log 3) := Real.exp_lt_exp.mpr hlt3
      _ = 3 := Real.exp_log (by norm_num)
  rw [windowLevel]
  exact Nat.floor_eq_iff (Real.exp_pos A).le |>.mpr ⟨hexp2, by push_cast; linarith⟩

/-- Every window test on `[−A, 0]` with `0 ≤ A ≤ 2 · enlargedWeilFloorAperture` retains the
strict Weil floor `(1 / 8000) ‖H‖² ≤ weilQuad H`. -/
theorem weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture {A : ℝ}
    (hA : A ≤ 2 * enlargedWeilFloorAperture) {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    (1 / 8000 : ℝ) * ∫ u, H u ^ 2 ≤ weilQuad H := by
  set f : ℝ → ℝ := fun u => H (u - A / 2)
  have hfd : ContDiff ℝ 2 f := hH.contDiff.comp (contDiff_id.sub contDiff_const)
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) fun u hu =>
      hH.vanish (u - A / 2) fun hm => hu ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hfs : ∀ u, enlargedWeilFloorAperture < |u| → f u = 0 := fun u hu => by
    refine hH.vanish (u - A / 2) fun hm => ?_
    rcases lt_abs.mp hu with hpos | hneg
    · linarith [hm.2]
    · linarith [hm.1]
  have hfloor := fullZeroForm_ge_of_support_le_enlargedWeilFloorAperture hfd hfc hfs
  have hpair : weilPair f f = fullZeroForm f := weilPair_eq_fullZeroForm ⟨hfd, hfc⟩
  have hquad : weilPair f f = weilQuad H := weilQuad_comp_sub H (A / 2)
  have hmass : (∫ u, f u ^ 2) = ∫ u, H u ^ 2 :=
    integral_sub_right_eq_self (μ := volume) (fun u => H u ^ 2) (A / 2)
  linarith

private theorem coerciveWindowConst_le_one_of_le_two_mul_enlargedAperture {A : ℝ}
    (hA : A ≤ 2 * enlargedWeilFloorAperture) :
    coerciveWindowConst A ≤ 1 := by
  have hb := firstFoldSubstage_bounds
  have hexp3 : Real.exp A < 3 := by
    calc Real.exp A ≤ Real.exp (2 * enlargedWeilFloorAperture) := Real.exp_le_exp.mpr hA
      _ < Real.exp 1 := Real.exp_lt_exp.mpr hb.2.2.1
      _ < 3 := by linarith [Real.exp_one_lt_d9]
  have hlev : windowLevel A ≤ 2 := by
    rw [windowLevel]
    exact Nat.lt_succ_iff.mp ((Nat.floor_lt (Real.exp_pos A).le).mpr (by exact_mod_cast hexp3))
  unfold coerciveWindowConst
  have hsub : ∑ n ∈ Finset.Icc 2 (windowLevel A),
      (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n ≤
      ∑ n ∈ Finset.Icc 2 2,
        (jordanTotient 1 n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hlev) fun n hn _ =>
      div_nonneg (jordanTotient_one_sub_vonMangoldt_nonneg (Finset.mem_Icc.mp hn).1)
        (Real.sqrt_nonneg _)
  rw [Finset.Icc_self, Finset.sum_singleton] at hsub
  have hj2 : jordanTotient 1 2 = 1 := by rw [jordanTotient_two]; norm_num
  rw [hj2, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at hsub
  have hsq2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt zero_le_one zero_le_two]; norm_num
  have hval : (1 - Real.log 2) / Real.sqrt 2 ≤ 1 / 2 := by
    have h1 : 1 - Real.log 2 ≤ 1 / 2 := by linarith [Real.log_two_gt_d9]
    calc (1 - Real.log 2) / Real.sqrt 2 ≤ (1 - Real.log 2) / 1 :=
          div_le_div_of_nonneg_left (by linarith [Real.log_two_lt_d9]) zero_lt_one hsq2
      _ ≤ 1 / 2 := by linarith
  linarith

/-- **Unconditional linear archimedean domination past `log 2`**: on every window
`0 ≤ A ≤ 2 · enlargedWeilFloorAperture` and every `0 ≤ k ≤ 1 / 16000`,
`tatePointCount A H k ≤ k · archWindowForm H`. -/
theorem firstFoldStage_linearDomination {A : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ 2 * enlargedWeilFloorAperture) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 16000) :
    tatePointCount A H k ≤ k * archWindowForm H := by
  refine linearArchimedeanDomination_of_weilFloor hA0
    (fun _ hG => weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture hA hG) hH hk0 ?_
  refine le_min (by linarith) ?_
  have hc := coerciveWindowConst_le_one_of_le_two_mul_enlargedAperture hA
  have hden : 0 < coerciveWindowConst A + 1 := by linarith [coerciveWindowConst_nonneg A]
  have hdiv : (1 / 16000 : ℝ) ≤ (1 / 8000) / (coerciveWindowConst A + 1) := by
    rw [le_div_iff₀ hden]; linarith
  exact hk.trans hdiv

/-- **Unconditional Esscher-tilted Tate-Gamma domination past `log 2`**: on every window
`0 ≤ A ≤ 2 · enlargedWeilFloorAperture` and every `0 ≤ k ≤ 1 / 160000`,
`tatePointCount A H k ≤ backwardTateGammaForm k H + k · windowPoleForm H`. -/
theorem firstFoldStage_backwardTateGammaDomination {A : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ 2 * enlargedWeilFloorAperture) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 160000) :
    tatePointCount A H k ≤ backwardTateGammaForm k H + k * windowPoleForm H := by
  have hE : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hk1 : k ≤ 1 := by linarith
  have hk4 : |k| ≤ 1 / 4 := by rw [abs_of_nonneg hk0]; linarith
  have hcnt := (le_abs_self _).trans (abs_tatePointCount_sub_jet_le hA0 hH hk0 hk1)
  have hgam := (neg_abs_le _).trans'
    (neg_le_neg (abs_backwardTateGammaForm_sub_linear_le hH hk4))
  have hc := coerciveWindowConst_le_one_of_le_two_mul_enlargedAperture hA
  have hQ := mul_le_mul_of_nonneg_left
    (weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture hA hH) hk0
  have hrel : k * weilQuad H =
      k * archGammaForm H + k * windowPoleForm H -
        2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u := by
    rw [weilQuad_eq_archWindowForm_sub_vonMangoldt hH, archWindowForm]; ring
  have hsq : (coerciveWindowConst A + 18) * k ^ 2 * ∫ u, H u ^ 2 ≤
      k * ((1 / 8000 : ℝ) * ∫ u, H u ^ 2) := by
    have hcoeff : (coerciveWindowConst A + 18) * k ≤ 1 / 8000 := by
      nlinarith [coerciveWindowConst_nonneg A]
    have heq : (coerciveWindowConst A + 18) * k ^ 2 * ∫ u, H u ^ 2 =
        k * (((coerciveWindowConst A + 18) * k) * ∫ u, H u ^ 2) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hE) hk0
  linarith

/-- **Unconditional symmetrized Tate-Gamma domination past `log 2`**: on every window
`0 ≤ A ≤ 2 · enlargedWeilFloorAperture` and every `0 ≤ k ≤ 1 / 160000`,
`tatePointCount A H k ≤ symTateGammaForm k H + k · windowPoleForm H`. -/
theorem firstFoldStage_symTateGammaDomination {A : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ 2 * enlargedWeilFloorAperture) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 160000) :
    tatePointCount A H k ≤ symTateGammaForm k H + k * windowPoleForm H := by
  have hE : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hk1 : k ≤ 1 := by linarith
  have hk4 : |k| ≤ 1 / 4 := by rw [abs_of_nonneg hk0]; linarith
  have hcnt := (le_abs_self _).trans (abs_tatePointCount_sub_jet_le hA0 hH hk0 hk1)
  have hgam := (neg_abs_le _).trans'
    (neg_le_neg (abs_symTateGammaForm_sub_linear_le hH hk4))
  have hc := coerciveWindowConst_le_one_of_le_two_mul_enlargedAperture hA
  have hQ := mul_le_mul_of_nonneg_left
    (weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture hA hH) hk0
  have hrel : k * weilQuad H =
      k * archGammaForm H + k * windowPoleForm H -
        2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u := by
    rw [weilQuad_eq_archWindowForm_sub_vonMangoldt hH, archWindowForm]; ring
  have hsq : (coerciveWindowConst A + 18) * k ^ 2 * ∫ u, H u ^ 2 ≤
      k * ((1 / 8000 : ℝ) * ∫ u, H u ^ 2) := by
    have hcoeff : (coerciveWindowConst A + 18) * k ≤ 1 / 8000 := by
      nlinarith [coerciveWindowConst_nonneg A]
    have heq : (coerciveWindowConst A + 18) * k ^ 2 * ∫ u, H u ^ 2 =
        k * (((coerciveWindowConst A + 18) * k) * ∫ u, H u ^ 2) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hE) hk0
  linarith

/-- **Explicit `ℙ^{k−1}(𝔽₂)` autocorrelation domination on `[log 2, 2 · enlargedWeilFloorAperture]`**:
on the first-fold sub-stage `log 2 ≤ A ≤ 2 · enlargedWeilFloorAperture`, the reduced point count
equals `√2 (2^k − 1) ∫ H(u) H(u + log 2) du` and is dominated by both
`backwardTateGammaForm k H + k · windowPoleForm H` and `symTateGammaForm k H + k · windowPoleForm H`
for all `0 ≤ k ≤ 1 / 160000`. -/
theorem firstFoldSubstage_explicit_primeTwo_domination {A : ℝ}
    (h2 : Real.log 2 ≤ A) (hA : A ≤ 2 * enlargedWeilFloorAperture)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 160000) :
    tatePointCount A H k =
        Real.sqrt 2 * ((2 : ℝ) ^ k - 1) * ∫ u, H u * H (u + Real.log 2) ∧
      Real.sqrt 2 * ((2 : ℝ) ^ k - 1) * (∫ u, H u * H (u + Real.log 2)) ≤
        backwardTateGammaForm k H + k * windowPoleForm H ∧
      Real.sqrt 2 * ((2 : ℝ) ^ k - 1) * (∫ u, H u * H (u + Real.log 2)) ≤
        symTateGammaForm k H + k * windowPoleForm H := by
  have hA0 : 0 ≤ A := (Real.log_pos (by norm_num)).le.trans h2
  have hlev := windowLevel_eq_two_of_mem_firstFoldSubstage h2 hA
  have hcnt : tatePointCount A H k =
      Real.sqrt 2 * ((2 : ℝ) ^ k - 1) * ∫ u, H u * H (u + Real.log 2) := by
    rw [tatePointCount, tateFunction_firstPrime hH hlev k, add_sub_cancel_left]
    have h2eq : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
      rw [div_eq_iff (Real.sqrt_ne_zero'.mpr two_pos), Real.mul_self_sqrt zero_le_two]
    calc 2 * (((2 : ℝ) ^ k - 1) / Real.sqrt 2 * ∫ u, H u * H (u + Real.log 2))
        = (2 / Real.sqrt 2) * ((2 : ℝ) ^ k - 1) * ∫ u, H u * H (u + Real.log 2) := by ring
      _ = Real.sqrt 2 * ((2 : ℝ) ^ k - 1) * ∫ u, H u * H (u + Real.log 2) := by rw [h2eq]
  refine ⟨hcnt, ?_, ?_⟩
  · rw [← hcnt]
    exact firstFoldStage_backwardTateGammaDomination hA0 hA hH hk0 hk
  · rw [← hcnt]
    exact firstFoldStage_symTateGammaDomination hA0 hA hH hk0 hk

/-! ### Complete synthesis of the archimedean Tate domination dichotomy -/

/-- **Complete resolution of the archimedean Tate domination question**:
1. *Dimension-zero inheritance*: window-local positive-dimension domination on `(0, k₀(A, H)]` by
   any `1`-jet-compatible family (`a 0 = 0`, `HasDerivAt a (archWindowForm H) 0`) implies
   `RiemannHypothesis`.
2. *Unconditional first-fold survival past `log 2`*: `log 2 < 2 · enlargedWeilFloorAperture < log 3`,
   and on every window `0 ≤ A ≤ 2 · enlargedWeilFloorAperture` and every `0 ≤ k ≤ 1 / 160000`, both
   `backwardTateGammaForm k H + k · windowPoleForm H` and
   `symTateGammaForm k H + k · windowPoleForm H` unconditionally dominate `tatePointCount A H k`.
3. *Unshifted global impossibility and doubly-exponential horizon collapse*: for every `k > 0` and
   `α, β ∈ ℝ`, `α · archGammaForm H + β · windowPoleForm H` fails to dominate across all windows,
   and on `windowRiemannKernel A` any domination horizon collapses faster than
   `C_* exp(−exp(A − 2))` (ruling out any uniform horizon `k₀ > 0`).
4. *Shifted-pole residue pinching and global no-go across all `φ ∈ ℝ`*: for `0 < k < 1`, any
   dominating combination `α · archGammaForm H + β · windowPoleForm H + φ · shiftedPoleForm k H`
   has its shifted-pole weight uniquely pinched to the Euler-product inverse
   `eulerProductPoleWeight k = 1 / ζ(1 + k) < k`, and for `0 < k ≤ 1 / 4` NO scalar `φ ∈ ℝ`
   allows `k · archGammaForm H + φ · shiftedPoleForm k H`,
   `backwardTateGammaForm k H + φ · shiftedPoleForm k H`, or
   `symTateGammaForm k H + φ · shiftedPoleForm k H` to dominate across all windows. -/
theorem archimedean_tate_domination_complete_solution :
    ((∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        ∃ a : ℝ → ℝ, a 0 = 0 ∧ HasDerivAt a (archWindowForm H) 0 ∧
          ∃ k₀ > 0, ∀ k ∈ Ioc 0 k₀, tatePointCount A H k ≤ a k) →
      RiemannHypothesis) ∧
    (Real.log 2 < 2 * enlargedWeilFloorAperture ∧
      2 * enlargedWeilFloorAperture < Real.log 3 ∧
      ∀ A : ℝ, 0 ≤ A → A ≤ 2 * enlargedWeilFloorAperture →
        ∀ H : ℝ → ℝ, IsWindowTest A H →
          ∀ k : ℝ, 0 ≤ k → k ≤ 1 / 160000 →
            tatePointCount A H k ≤ backwardTateGammaForm k H + k * windowPoleForm H ∧
            tatePointCount A H k ≤ symTateGammaForm k H + k * windowPoleForm H) ∧
    ((∀ k : ℝ, 0 < k → ∀ α β : ℝ,
        ¬ ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
          tatePointCount A H k ≤ α * archGammaForm H + β * windowPoleForm H) ∧
      (∃ A₀ Cstar : ℝ, 0 ≤ A₀ ∧ 0 < Cstar ∧
        ∀ A : ℝ, A₀ ≤ A → ∀ k : ℝ, 0 < k →
          tatePointCount A (windowRiemannKernel A) k ≤
            k * archWindowForm (windowRiemannKernel A) →
          k ≤ Cstar * Real.exp (-Real.exp (A - 2))) ∧
      (¬ ∃ k₀ > 0, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
          ∀ k ∈ Ioc 0 k₀,
            tatePointCount A H k ≤ backwardTateGammaForm k H + k * windowPoleForm H) ∧
      (¬ ∃ k₀ > 0, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
          ∀ k ∈ Ioc 0 k₀,
            tatePointCount A H k ≤ symTateGammaForm k H + k * windowPoleForm H)) ∧
    ((∀ k : ℝ, 0 < k → k < 1 →
        eulerProductPoleWeight k * (riemannZeta ((1 + k : ℝ) : ℂ)).re = 1 ∧
        eulerProductPoleWeight k < k ∧
        ∀ α β φ : ℝ,
          (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
            tatePointCount A H k ≤
              α * archGammaForm H + β * windowPoleForm H + φ * shiftedPoleForm k H) →
          φ = eulerProductPoleWeight k) ∧
      (∀ k : ℝ, 0 < k → k ≤ 1 / 4 →
        (¬ ∃ φ : ℝ, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
            tatePointCount A H k ≤ k * archGammaForm H + φ * shiftedPoleForm k H) ∧
        (¬ ∃ φ : ℝ, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
            tatePointCount A H k ≤ backwardTateGammaForm k H + φ * shiftedPoleForm k H) ∧
        (¬ ∃ φ : ℝ, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
            tatePointCount A H k ≤ symTateGammaForm k H + φ * shiftedPoleForm k H))) := by
  have hb := firstFoldSubstage_bounds
  refine ⟨riemannHypothesis_of_local_archimedeanTateDomination,
    ⟨hb.1.trans hb.2.1, hb.2.2.1.trans hb.2.2.2, fun A hA0 hA H hH k hk0 hk =>
      ⟨firstFoldStage_backwardTateGammaDomination hA0 hA hH hk0 hk,
       firstFoldStage_symTateGammaDomination hA0 hA hH hk0 hk⟩⟩,
    ⟨fun k hk α β => not_forall_window_domination_archGamma_pole hk α β,
     exists_horizon_le_doubleExp,
     not_exists_uniform_horizon_backwardTateGamma,
     not_exists_uniform_horizon_symTateGamma⟩,
    ⟨fun k hk0 hk1 =>
      ⟨eulerProductPoleWeight_mul_zeta_eq_one hk0,
       eulerProductPoleWeight_lt_self hk0,
       fun α β φ hdom => shiftedPole_weight_pinched_eq_eulerProduct hk0 hk1 hdom⟩,
     fun k hk0 hk4 =>
      ⟨not_exists_shiftedPole_weight_domination_linear hk0 (by linarith),
       not_exists_shiftedPole_weight_domination_backwardTateGamma hk0 hk4,
       not_exists_shiftedPole_weight_domination_symTateGamma hk0 hk4⟩⟩⟩

end GaloisForLFunctions.ArchimedeanTateDomination

#print axioms GaloisForLFunctions.ArchimedeanTateDomination.firstFoldSubstage_bounds
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.firstFoldStage_backwardTateGammaDomination
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.firstFoldSubstage_explicit_primeTwo_domination
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.archimedean_tate_domination_complete_solution
