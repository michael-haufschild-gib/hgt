import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneProbeSeesEveryOuterEigenvalue
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeAgainstTwoAndWolffTowerObstruction
import GaloisForLFunctions.HTGeometry.CauchyPompeiu

/-!
# Wolff blindness needs a wall

`WolffBlindnessRequiresSeparation` extracts the class sums of a vector orthogonal to a tower from
the residues of the discrete Cauchy transform `G(z) = Σ_τ q_τ/(1 − c_τ z)` at isolated poles. Here
the residue is replaced by the `∂̄`-equation of the Cauchy kernel, which needs no isolation.

* **Cauchy–Pompeiu for tests** (`integral_dzbar_div_sub`): `∫ ∂̄φ(w)/(w − z) dA = −π φ(z)` for a
  compactly supported `C¹` function `φ`.
* **The `∂̄`-pairing** (`tsum_mul_eq_integral_dzbar_mul`): for summable masses `q_τ` at bounded
  points `p_τ`, `Σ_τ q_τ φ(p_τ) = −π⁻¹ ∫ ∂̄φ(w) Σ_τ q_τ/(w − p_τ) dA`. The Cauchy kernel is
  locally integrable in the plane, so the sum passes under the integral.
* **`∂̄`-uniqueness** (`tsum_ite_eq_zero_of_ae_cauchy`): if `Σ_τ q_τ/(w − p_τ)` vanishes for almost
  every `w` of a disc, the mass at its centre is zero; pair with bumps shrinking to the centre.
* **Null accessibility** (`NullAccessibleOff`, `classSum_eq_zero_of_nullAccessible`). The transform
  vanishes on the component of the origin off the closed pole set. If near `c₀⁻¹` that set is null
  and every other point off it lies in this component, the transform vanishes almost everywhere
  near `c₀⁻¹`, and the class sum at `c₀` vanishes — isolated or not.
* **Towers** (`card_le_towerDefect_of_nullAccessibleOff`, `not_nullAccessibleOff_of_towerGram_psd`).
  A fixed test's tower sees every visible outer eigenvalue `b` whose reciprocal is null-accessible
  off the closed active folded spectrum. A fixed test is blind to `b` only if every disc about `b⁻¹`
  meets the closed folded spectrum in positive area or contains points it walls off from the
  origin.
* **Countable folded spectra** (`card_le_towerDefect_of_countable_folded`,
  `tower_law_of_countable_folded`, `exists_test_tower_law_of_countable_folded`). If the closed
  folded spectrum meets the unit disc in a countable set, the tower of a fixed test carries every
  visible outer eigenvalue, isolated or not, and one probe carries the whole tower defect: finitely
  or infinitely many eigenvalues, with real parts of any order type.
-/

open Complex Filter Topology Set Metric MeasureTheory
open scoped ComplexConjugate Classical lp ENNReal Real
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. The `∂̄`-equation of the Cauchy kernel -/

/-- `∂̄φ` vanishes off the topological support of `φ`. -/
theorem dzbar_eq_zero_of_notMem_tsupport {φ : ℂ → ℂ} {w : ℂ} (hw : w ∉ tsupport φ) :
    _root_.HTGeometry.dzbar φ w = 0 := by
  have h : fderiv ℝ φ w = 0 := by
    by_contra hne
    exact hw (tsupport_fderiv_subset ℝ (subset_tsupport _ hne))
  simp [_root_.HTGeometry.dzbar, _root_.HTGeometry.wirtingerAntihol, h]

/-- **Cauchy–Pompeiu for tests.** For a compactly supported `C¹` function,
`∫ ∂̄φ(w)/(w − z) dA(w) = −π φ(z)`. -/
theorem integral_dzbar_div_sub {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (z : ℂ) : ∫ w, _root_.HTGeometry.dzbar φ w / (w - z) = -(π : ℂ) * φ z := by
  obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  set R : ℝ := |R₀| + ‖z‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  set h : ℂ → ℂ := fun w => φ (w + z) with hh
  have hC : ContDiff ℝ 1 h := hφ.comp (contDiff_id.add contDiff_const)
  have hout : ∀ u : ℂ, R - ‖z‖ ≤ ‖u‖ → u ∉ tsupport φ := by
    intro u hu hmem
    have h1 := mem_closedBall_zero_iff.mp (hR₀ hmem)
    have h2 : R₀ ≤ |R₀| := le_abs_self R₀
    linarith
  have hfar : ∀ w : ℂ, R ≤ ‖w‖ → R - ‖z‖ ≤ ‖w + z‖ := by
    intro w hw
    have := norm_sub_norm_le w (-z)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hmean : _root_.HTGeometry.circleMean h R = 0 := by
    rw [_root_.HTGeometry.circleMean]
    refine (intervalIntegral.integral_congr fun θ _ => ?_).trans intervalIntegral.integral_zero
    show φ (circleMap 0 R θ + z) = 0
    refine image_eq_zero_of_notMem_tsupport (hout _ (hfar _ ?_))
    simp [abs_of_pos hR]
  have hdz : ∀ w, _root_.HTGeometry.dzbar h w = _root_.HTGeometry.dzbar φ (w + z) := by
    intro w
    simp only [_root_.HTGeometry.dzbar, hh, fderiv_comp_add_right]
  have hset : ∫ w in ball (0 : ℂ) R, _root_.HTGeometry.dzbar h w / w =
      ∫ w, _root_.HTGeometry.dzbar φ (w + z) / w := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [hdz]
    · intro w hw
      rw [mem_ball_zero_iff, not_lt] at hw
      rw [hdz, dzbar_eq_zero_of_notMem_tsupport (hout _ (hfar _ hw)), zero_div]
  have htr : ∫ w, _root_.HTGeometry.dzbar φ (w + z) / w =
      ∫ u, _root_.HTGeometry.dzbar φ u / (u - z) := by
    have := integral_add_right_eq_self (μ := volume)
      (fun u => _root_.HTGeometry.dzbar φ u / (u - z)) z
    simpa only [add_sub_cancel_right] using this
  have hpomp := _root_.HTGeometry.cauchyPompeiu_center hC hR
  rw [hmean, hset, htr] at hpomp
  have h0 : h 0 = φ z := by simp [hh]
  rw [h0, Complex.real_smul] at hpomp
  push_cast at hpomp
  linear_combination (-1 / 2 : ℂ) * hpomp

/-- The Cauchy kernel about any point of `‖a‖ ≤ P` has integral at most `2π(R + P)` over the disc
`‖w‖ < R`. -/
theorem lintegral_ball_norm_inv_sub_le (R P : ℝ) (a : ℂ) (ha : ‖a‖ ≤ P) :
    ∫⁻ w, (ball (0 : ℂ) R).indicator (fun w => ENNReal.ofReal ‖w - a‖⁻¹) w ≤
      ENNReal.ofReal (R + P) * ENNReal.ofReal (2 * π) := by
  have hsub : ∀ w, (ball (0 : ℂ) R).indicator (fun w => ENNReal.ofReal ‖w - a‖⁻¹) w ≤
      (ball (0 : ℂ) (R + P)).indicator (fun u => ENNReal.ofReal ‖u‖⁻¹) (w - a) := by
    intro w
    by_cases hw : w ∈ ball (0 : ℂ) R
    · have hw' : w - a ∈ ball (0 : ℂ) (R + P) := by
        rw [mem_ball_zero_iff] at hw ⊢
        calc ‖w - a‖ ≤ ‖w‖ + ‖a‖ := norm_sub_le _ _
          _ < R + P := by linarith
      rw [indicator_of_mem hw, indicator_of_mem hw']
    · rw [indicator_of_notMem hw]
      exact zero_le
  calc ∫⁻ w, (ball (0 : ℂ) R).indicator (fun w => ENNReal.ofReal ‖w - a‖⁻¹) w
      ≤ ∫⁻ w, (ball (0 : ℂ) (R + P)).indicator (fun u => ENNReal.ofReal ‖u‖⁻¹) (w - a) :=
        lintegral_mono hsub
    _ = ∫⁻ u, (ball (0 : ℂ) (R + P)).indicator (fun u => ENNReal.ofReal ‖u‖⁻¹) u :=
        lintegral_sub_right_eq_self _ a
    _ ≤ _ := _root_.HTGeometry.lintegral_ball_norm_inv (R + P)

/-- **The `∂̄`-pairing of a discrete Cauchy transform.** For summable masses `q_τ` at points
`‖p_τ‖ ≤ P` and a compactly supported `C¹` function `φ`,
`Σ_τ q_τ φ(p_τ) = −π⁻¹ ∫ ∂̄φ(w) Σ_τ q_τ/(w − p_τ) dA(w)`. -/
theorem tsum_mul_eq_integral_dzbar_mul {T : Type*} [Countable T] {q p : T → ℂ}
    (hq : Summable fun τ => ‖q τ‖) {P : ℝ} (hp : ∀ τ, ‖p τ‖ ≤ P) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∑' τ, q τ * φ (p τ) =
      -(π : ℂ)⁻¹ * ∫ w, _root_.HTGeometry.dzbar φ w * ∑' τ, q τ / (w - p τ) := by
  set D : ℂ → ℂ := _root_.HTGeometry.dzbar φ with hDdef
  have hDc : Continuous D := _root_.HTGeometry.continuous_dzbar hφ
  have hDs : HasCompactSupport D :=
    HasCompactSupport.intro hφc.isCompact fun w hw => dzbar_eq_zero_of_notMem_tsupport hw
  obtain ⟨M, hM⟩ := hDc.bounded_above_of_compact_support hDs
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_ball 0
  have hDout : ∀ w, w ∉ ball (0 : ℂ) R → D w = 0 := fun w hw =>
    dzbar_eq_zero_of_notMem_tsupport fun h => hw (hR h)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- each value by Cauchy–Pompeiu
  have hval : ∀ τ, q τ * φ (p τ) = -(π : ℂ)⁻¹ * ∫ w, q τ * (D w / (w - p τ)) := by
    intro τ
    rw [integral_const_mul, integral_dzbar_div_sub hφ hφc]
    field_simp
  -- the sum passes under the integral
  have hmeas : ∀ τ, AEStronglyMeasurable (fun w => q τ * (D w / (w - p τ))) volume := fun τ =>
    (aestronglyMeasurable_const.mul
      ((hDc.measurable.div (measurable_id.sub_const _)).aestronglyMeasurable))
  set C : ℝ≥0∞ := ENNReal.ofReal M * (ENNReal.ofReal (R + P) * ENNReal.ofReal (2 * π)) with hC
  have hlint : ∀ τ, ∫⁻ w, ‖q τ * (D w / (w - p τ))‖ₑ ≤ ‖q τ‖ₑ * C := by
    intro τ
    have hpt : ∀ w, ‖q τ * (D w / (w - p τ))‖ₑ ≤
        ‖q τ‖ₑ * (ENNReal.ofReal M *
          (ball (0 : ℂ) R).indicator (fun w => ENNReal.ofReal ‖w - p τ‖⁻¹) w) := by
      intro w
      by_cases hw : w ∈ ball (0 : ℂ) R
      · rw [indicator_of_mem hw, enorm_mul]
        gcongr
        by_cases hwp : w = p τ
        · simp [hwp]
        · have hpos : 0 < ‖w - p τ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwp)
          rw [← ofReal_norm, ← ENNReal.ofReal_mul hMnn, norm_div]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hM w) (inv_nonneg.mpr hpos.le)
      · simp [hDout w hw]
    calc ∫⁻ w, ‖q τ * (D w / (w - p τ))‖ₑ
        ≤ ∫⁻ w, ‖q τ‖ₑ * (ENNReal.ofReal M *
            (ball (0 : ℂ) R).indicator (fun w => ENNReal.ofReal ‖w - p τ‖⁻¹) w) :=
          lintegral_mono hpt
      _ = ‖q τ‖ₑ * (ENNReal.ofReal M *
            ∫⁻ w, (ball (0 : ℂ) R).indicator (fun w => ENNReal.ofReal ‖w - p τ‖⁻¹) w) := by
          rw [lintegral_const_mul' _ _ enorm_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ‖q τ‖ₑ * C := by
          rw [hC]
          gcongr
          exact lintegral_ball_norm_inv_sub_le R P (p τ) (hp τ)
  have hqe : ∑' τ, ‖q τ‖ₑ ≠ ⊤ := by
    rw [show (fun τ => ‖q τ‖ₑ) = fun τ => ENNReal.ofReal ‖q τ‖ from
      funext fun τ => (ofReal_norm _).symm,
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hq]
    exact ENNReal.ofReal_ne_top
  have hsum : ∑' τ, ∫⁻ w, ‖q τ * (D w / (w - p τ))‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlint)
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hqe (by rw [hC]; finiteness)
  rw [tsum_congr hval, tsum_mul_left, ← integral_tsum hmeas hsum]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [← tsum_mul_left]
  exact tsum_congr fun τ => by ring

/-- **`∂̄`-uniqueness.** If `Σ_τ q_τ/(w − p_τ)` vanishes for almost every `w` in a disc about
`z₀`, the total mass at `z₀` is zero. -/
theorem tsum_ite_eq_zero_of_ae_cauchy {T : Type*} [Countable T] {q p : T → ℂ}
    (hq : Summable fun τ => ‖q τ‖) {P : ℝ} (hp : ∀ τ, ‖p τ‖ ≤ P) {z₀ : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hG : ∀ᵐ w ∂(volume.restrict (ball z₀ r₀)), ∑' τ, q τ / (w - p τ) = 0) :
    ∑' τ, (if p τ = z₀ then q τ else 0) = 0 := by
  -- bumps of radius `r₀/(n + 2)` about `z₀`
  set ρ : ℕ → ℝ := fun n => r₀ / ((n : ℝ) + 2) with hρ
  have hρ0 : ∀ n, 0 < ρ n := fun n => by positivity
  have hρr : ∀ n, ρ n < r₀ := fun n => by
    rw [hρ, div_lt_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    have := Filter.Tendsto.const_div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ) tendsto_natCast_atTop_atTop) r₀
    simpa [hρ] using this
  let f : ∀ n : ℕ, ContDiffBump z₀ := fun n =>
    ⟨ρ n / 2, ρ n, by linarith [hρ0 n], by linarith [hρ0 n]⟩
  set φ : ℕ → ℂ → ℂ := fun n w => ((f n w : ℝ) : ℂ) with hφ
  have hφC : ∀ n, ContDiff ℝ 1 (φ n) := fun n => ofRealCLM.contDiff.comp (f n).contDiff
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    (f n).hasCompactSupport.comp_left Complex.ofReal_zero
  have hφs : ∀ n, tsupport (φ n) ⊆ ball z₀ r₀ := fun n =>
    (tsupport_comp_subset Complex.ofReal_zero _).trans
      ((f n).tsupport_eq.trans_subset (closedBall_subset_ball (hρr n)))
  -- every pairing vanishes
  have hzero : ∀ n, ∑' τ, q τ * φ n (p τ) = 0 := by
    intro n
    rw [tsum_mul_eq_integral_dzbar_mul hq hp (hφC n) (hφc n)]
    have hball : ∀ᵐ w, w ∈ ball z₀ r₀ → ∑' τ, q τ / (w - p τ) = 0 :=
      (ae_restrict_iff' measurableSet_ball).mp hG
    have h0 : ∫ w, _root_.HTGeometry.dzbar (φ n) w * ∑' τ, q τ / (w - p τ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hball] with w hw
      by_cases hwb : w ∈ ball z₀ r₀
      · rw [Pi.zero_apply, hw hwb, mul_zero]
      · rw [Pi.zero_apply, dzbar_eq_zero_of_notMem_tsupport fun h => hwb (hφs n h), zero_mul]
    rw [h0, mul_zero]
  -- the bumps converge to the indicator of `z₀`
  have hlim : Tendsto (fun n => ∑' τ, q τ * φ n (p τ)) atTop
      (𝓝 (∑' τ, if p τ = z₀ then q τ else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hq (fun τ => ?_)
      (Eventually.of_forall fun n τ => ?_)
    · by_cases hpτ : p τ = z₀
      · simp only [if_pos hpτ]
        refine tendsto_const_nhds.congr fun n => ?_
        have h1 : f n z₀ = 1 :=
          (f n).one_of_mem_closedBall (mem_closedBall_self (f n).rIn_pos.le)
        simp [hφ, hpτ, h1]
      · simp only [if_neg hpτ]
        have hd : 0 < ‖p τ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpτ)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hρlim.eventually (gt_mem_nhds hd)] with n hn
        have hfz : f n (p τ) = 0 := by
          by_contra hne
          have hmem : p τ ∈ Function.support (f n) := hne
          rw [(f n).support_eq, mem_ball, dist_eq_norm] at hmem
          exact absurd hmem (not_lt.mpr hn.le)
        simp [hφ, hfz]
    · rw [norm_mul]
      have h1 : ‖φ n (p τ)‖ ≤ 1 := by
        simp only [hφ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (f n).nonneg]
        exact (f n).le_one
      calc ‖q τ‖ * ‖φ n (p τ)‖ ≤ ‖q τ‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖q τ‖ := mul_one _
  exact tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)

/-! ### 2. Null accessibility -/

section Cauchy

variable {T : Type*} [Countable T] {q c : T → ℂ}

omit [Countable T] in
/-- The discrete Cauchy transform in partial fractions: `q/(1 − cz) = −(q/c)/(z − c⁻¹)`. -/
theorem discreteCauchy_eq_tsum_div_sub (hc : ∀ τ, c τ ≠ 0) (z : ℂ) :
    discreteCauchy q c z = ∑' τ, -(q τ / c τ) / (z - (c τ)⁻¹) := by
  refine tsum_congr fun τ => ?_
  by_cases hz : z = (c τ)⁻¹
  · simp [hz, mul_inv_cancel₀ (hc τ)]
  · have hcτ := hc τ
    have h1 : z - (c τ)⁻¹ ≠ 0 := sub_ne_zero.mpr hz
    have h2 : 1 - c τ * z ≠ 0 := fun h0 =>
      hz (eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h0).symm)
    rw [div_eq_div_iff h2 h1]
    field_simp
    ring

/-- **Class extraction at a null-accessible pole.** Let the moments `Σ q_τ c_τ^k`, `k ≥ 0`,
vanish, and `F ⊇` the closed pole set. If a connected open set through the origin avoids `F`, and
on a disc about `c₀⁻¹` the set `F` is null and every point off `F` other than the centre lies in
that open set, the class sum at `c₀` vanishes. -/
theorem classSum_eq_zero_of_nullAccessible (hq : Summable fun τ => ‖q τ‖) {m M : ℝ} (hm : 0 < m)
    (hM : 0 < M) (hcm : ∀ τ, m ≤ ‖c τ‖) (hcM : ∀ τ, ‖c τ‖ ≤ M)
    (hmom : ∀ k : ℕ, ∑' τ, q τ * c τ ^ k = 0) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {U F : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (h0 : (0 : ℂ) ∈ U)
    (hFp : closure (cauchyPoles q c) ⊆ F) (hUF : ∀ z ∈ U, z ∉ F) {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ z, ‖z - c₀⁻¹‖ < ε → z ≠ c₀⁻¹ → z ∉ F → z ∈ U)
    (hnull : volume (F ∩ ball c₀⁻¹ ε) = 0) :
    ∑' τ, (if c τ = c₀ then q τ else 0) = 0 := by
  have hc0 : ∀ τ, c τ ≠ 0 := fun τ => norm_pos_iff.mp (hm.trans_le (hcm τ))
  have hG : EqOn (discreteCauchy q c) 0 U :=
    discreteCauchy_eqOn_zero hq hm hM hcm hcM hmom hUo hUc h0 fun z hz hzK => hUF z hz (hFp hzK)
  -- the transform vanishes almost everywhere near `c₀⁻¹`
  have hexc : volume (F ∩ ball c₀⁻¹ ε ∪ {c₀⁻¹}) = 0 :=
    measure_union_null hnull (measure_singleton _)
  have hae : ∀ᵐ w ∂(volume.restrict (ball c₀⁻¹ ε)), ∑' τ, -(q τ / c τ) / (w - (c τ)⁻¹) = 0 := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hexc] with w hw hwb
    rw [← discreteCauchy_eq_tsum_div_sub hc0]
    have hwF : w ∉ F := fun h => hw (Or.inl ⟨h, hwb⟩)
    have hwc : w ≠ c₀⁻¹ := fun h => hw (Or.inr h)
    exact hG (hball w (by rwa [mem_ball, dist_eq_norm] at hwb) hwc hwF)
  -- masses `−q_τ/c_τ` at the points `c_τ⁻¹`, all of modulus `≤ m⁻¹`
  have hq' : Summable fun τ => ‖-(q τ / c τ)‖ := by
    refine (hq.div_const m).of_nonneg_of_le (fun _ => norm_nonneg _) fun τ => ?_
    rw [norm_neg, norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hm (hcm τ)
  have hp : ∀ τ, ‖(c τ)⁻¹‖ ≤ m⁻¹ := fun τ => by
    rw [norm_inv]
    exact inv_anti₀ hm (hcm τ)
  have h := tsum_ite_eq_zero_of_ae_cauchy hq' hp hε hae
  have e : ∀ τ, (if (c τ)⁻¹ = c₀⁻¹ then -(q τ / c τ) else 0) =
      -c₀⁻¹ * (if c τ = c₀ then q τ else 0) := by
    intro τ
    by_cases h' : c τ = c₀
    · rw [if_pos (by rw [h']), if_pos h', h']
      ring
    · rw [if_neg fun h'' => h' (inv_injective h''), if_neg h', mul_zero]
  rw [tsum_congr e, tsum_mul_left] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (inv_ne_zero hc₀))

end Cauchy

/-- `w` is **null-accessible from the origin off** `F`: a connected open set through the origin
avoids `F`, and on a disc about `w` the set `F` is null and every point off `F`, except possibly
`w`, lies in that open set. -/
def NullAccessibleOff (F : Set ℂ) (w : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ IsPreconnected U ∧ (0 : ℂ) ∈ U ∧ (∀ z ∈ U, z ∉ F) ∧
    ∃ ε > 0, (∀ z, ‖z - w‖ < ε → z ≠ w → z ∉ F → z ∈ U) ∧ volume (F ∩ ball w ε) = 0

/-- An accessible point is null-accessible: off its centre the disc lies in the open set, so `F`
meets it at most in the centre. -/
theorem AccessibleOff.nullAccessibleOff {F : Set ℂ} {w : ℂ} (h : AccessibleOff F w) :
    NullAccessibleOff F w := by
  obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball⟩ := h
  refine ⟨U, hUo, hUc, h0, hUF, ε, hε, fun z hz hne _ => hball z hz hne, ?_⟩
  refine measure_mono_null (fun z hz => ?_) (measure_singleton w)
  by_contra hne
  exact hUF z (hball z (by rw [← dist_eq_norm]; exact hz.2) hne) hz.1

/-- Null accessibility is invariant under complex conjugation. -/
theorem NullAccessibleOff.conj {F : Set ℂ} {w : ℂ} (h : NullAccessibleOff F w) :
    NullAccessibleOff ((starRingEnd ℂ) ⁻¹' F) (conj w) := by
  obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball, hnull⟩ := h
  have himg : (starRingEnd ℂ) ⁻¹' U = (starRingEnd ℂ) '' U := by
    ext z
    constructor
    · intro hz
      exact ⟨conj z, hz, Complex.conj_conj z⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hnorm : ∀ z, ‖conj z - w‖ = ‖z - conj w‖ := fun z => by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
  refine ⟨(starRingEnd ℂ) ⁻¹' U, hUo.preimage Complex.continuous_conj, ?_, by simpa using h0,
    fun z hz hzF => hUF _ hz hzF, ε, hε, fun z hz hne hzF => hball _ ?_ ?_ hzF, ?_⟩
  · rw [himg]
    exact hUc.image _ Complex.continuous_conj.continuousOn
  · rw [hnorm]
    exact hz
  · intro h'
    apply hne
    rw [← h', Complex.conj_conj]
  · have hset : (starRingEnd ℂ) ⁻¹' F ∩ ball (conj w) ε =
        (starRingEnd ℂ) ⁻¹' (F ∩ ball w ε) := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_ball, dist_eq_norm, hnorm]
    have hmp : MeasurePreserving (starRingEnd ℂ) volume volume :=
      Complex.conjLIE.measurePreserving
    have hemb : MeasurableEmbedding (starRingEnd ℂ) :=
      Complex.conjLIE.toHomeomorph.measurableEmbedding
    rw [hset, hmp.measure_preimage_emb hemb]
    exact hnull

/-- The disc minus a closed set it meets countably is path-connected. -/
theorem isPreconnected_ball_diff_of_countable {F : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcount : (F ∩ ball (0 : ℂ) ρ).Countable) : IsPreconnected (ball (0 : ℂ) ρ \ F) := by
  set e : ℂ ≃ₜ ball (0 : ℂ) 1 := Homeomorph.unitBall
  set f : ℂ → ℂ := fun x => (ρ : ℂ) * (e x : ℂ)
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have hf : Continuous f := continuous_const.mul (continuous_subtype_val.comp e.continuous)
  have hfinj : Function.Injective f := fun x y h =>
    e.injective (Subtype.ext (mul_left_cancel₀ hρ0 h))
  have hfball : ∀ x, f x ∈ ball (0 : ℂ) ρ := fun x => by
    have h1 : ‖(e x : ℂ)‖ < 1 := mem_ball_zero_iff.mp (e x).2
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg (e x : ℂ)]
  have hsub : f ⁻¹' F ⊆ f ⁻¹' (F ∩ ball (0 : ℂ) ρ) := fun x hx =>
    show f x ∈ F ∩ ball (0 : ℂ) ρ from ⟨hx, hfball x⟩
  have hA : (f ⁻¹' F).Countable := (hcount.preimage hfinj).mono hsub
  have hpc : IsPathConnected (f '' (f ⁻¹' F)ᶜ) :=
    (hA.isPathConnected_compl_of_one_lt_rank
      (by simp only [rank_real_complex, Nat.one_lt_ofNat])).image hf
  have himg : f '' (f ⁻¹' F)ᶜ = ball (0 : ℂ) ρ \ F := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hfball x, hx⟩
    · rintro ⟨hz, hzF⟩
      have hz' : z / ρ ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le,
          div_lt_one hρ]
        exact mem_ball_zero_iff.mp hz
      have hfz : f (e.symm ⟨z / ρ, hz'⟩) = z := by
        simp only [f, Homeomorph.apply_symm_apply]
        field_simp
      refine ⟨e.symm ⟨z / ρ, hz'⟩, ?_, hfz⟩
      show f (e.symm ⟨z / ρ, hz'⟩) ∉ F
      rw [hfz]
      exact hzF
  rw [← himg]
  exact hpc.isConnected.isPreconnected

/-- **Countable obstacles.** If a closed set `F` missing the origin meets the disc `‖z‖ < ρ` in a
countable set, every point of the disc is null-accessible off `F`, isolated from `F` or not. -/
theorem nullAccessibleOff_of_countable {F : Set ℂ} (hFc : IsClosed F) {ρ : ℝ} (hρ : 0 < ρ)
    (hcount : (F ∩ ball (0 : ℂ) ρ).Countable) (h0 : (0 : ℂ) ∉ F) {w : ℂ} (hw : ‖w‖ < ρ) :
    NullAccessibleOff F w := by
  have hsub : ∀ z, ‖z - w‖ < ρ - ‖w‖ → z ∈ ball (0 : ℂ) ρ := fun z hz => by
    rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ < ρ := by linarith
  refine ⟨ball (0 : ℂ) ρ \ F, isOpen_ball.sdiff hFc, isPreconnected_ball_diff_of_countable hρ
    hcount, ⟨by simpa using hρ, h0⟩, fun z hz => hz.2, ρ - ‖w‖, by linarith,
    fun z hz _ hzF => ⟨hsub z hz, hzF⟩, ?_⟩
  have hsubset : F ∩ ball w (ρ - ‖w‖) ⊆ F ∩ ball (0 : ℂ) ρ := fun z hz =>
    ⟨hz.1, hsub z (by rw [← dist_eq_norm]; exact hz.2)⟩
  exact measure_mono_null hsubset (hcount.measure_zero volume)

/-! ### 3. Towers -/

/-- **Tower class extraction at null-accessible eigenvalues.** If `b⁻¹` is null-accessible from
the origin off the closed active folded spectrum, every vector orthogonal to the tower has zero
class sums at `b` and at `1/b̄`. -/
theorem classSum_eq_zero_of_nullAccessibleOff (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℂ}
    (hb : b ≠ 0) (hacc : NullAccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) b⁻¹)
    (a : ℓ²(Z.carrier, ℂ)) (ha : ∀ k : ℤ, inner ℂ (towerVec Z hZ hg hgc ℓ k) a = 0) :
    (∑' τ : Z.carrier, (if frobEig ℓ τ = b then conj (zeroCoord Z g τ) * a τ else 0)) = 0 ∧
      ∑' τ : Z.carrier, (if frobEig ℓ τ = reflEig b then
        conj (zeroCoord Z g τ) * a τ else 0) = 0 := by
  haveI : Countable Z.carrier := (SquareRootThreshold.countable_carrier Z).to_subtype
  set q : Z.carrier → ℂ := fun τ => conj (zeroCoord Z g τ) * a τ
  have hq : Summable fun τ => ‖q τ‖ := summable_conj_zeroCoord_mul Z hZ hg hgc a
  have hmom := tsum_mul_conj_frobEig_zpow_eq_zero Z hZ hg hgc ℓ a ha
  have hm : 0 < Real.exp (-(ℓ / 2)) := Real.exp_pos _
  have hM : 0 < Real.exp (ℓ / 2) := Real.exp_pos _
  have hseen : ∀ τ : Z.carrier, q τ ≠ 0 → paperFT g (gammaOf τ) ≠ 0 :=
    fun τ h hz => h (by simp [q, zeroCoord, hz])
  set F := activeFoldedSpectrum Z g ℓ
  constructor
  · -- the outer class: nodes `β̄_τ`, poles `conj β_τ⁻¹`
    have hpoles : closure (cauchyPoles q fun τ : Z.carrier => conj (frobEig ℓ τ)) ⊆
        (starRingEnd ℂ) ⁻¹' closure F := by
      refine (closure_mono ?_).trans (Complex.continuous_conj.closure_preimage_subset F)
      rintro z ⟨τ, hqτ, rfl⟩
      exact ⟨τ, τ.2, Or.inl (hseen τ hqτ), by rw [map_inv₀, Complex.conj_conj]⟩
    obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball, hnull⟩ := hacc.conj
    rw [map_inv₀] at hball hnull
    have h := classSum_eq_zero_of_nullAccessible hq hm hM
      (exp_neg_half_le_norm_conj_frobEig Z ℓ hℓ) (norm_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_natCast]).trans (hmom n))
      ((map_ne_zero (starRingEnd ℂ)).mpr hb) hUo hUc h0 hpoles hUF hε hball hnull
    simpa only [(starRingEnd ℂ).injective.eq_iff] using h
  · -- the reflected class: nodes `β̄_τ⁻¹`, poles `β̄_τ = (β_{1−τ̄})⁻¹`
    have e : ∀ β : ℂ, (conj β)⁻¹ = b ↔ β = reflEig b := fun β => by
      constructor
      · intro h; rw [reflEig, ← h, map_inv₀, Complex.conj_conj, inv_inv]
      · intro h; rw [h, reflEig, map_inv₀, Complex.conj_conj, inv_inv]
    have hpoles : closure (cauchyPoles q fun τ : Z.carrier => (conj (frobEig ℓ τ))⁻¹) ⊆
        closure F := by
      refine closure_mono ?_
      rintro z ⟨τ, hqτ, rfl⟩
      refine ⟨reflect (τ : ℂ), Z.reflect_mem _ τ.2, Or.inr ?_, ?_⟩
      · rw [gammaOf_reflect, Complex.conj_conj]
        exact hseen τ hqτ
      · rw [inv_inv, frobEig_reflect, inv_inv]
    obtain ⟨U, hUo, hUc, h0, hUF, ε, hε, hball, hnull⟩ := hacc
    have hlow : ∀ τ : Z.carrier, Real.exp (-(ℓ / 2)) ≤ ‖(conj (frobEig ℓ τ))⁻¹‖ := fun τ => by
      rw [norm_inv, Real.exp_neg]
      exact inv_anti₀ (norm_pos_iff.mpr ((map_ne_zero _).mpr (frobEig_ne_zero ℓ τ)))
        (norm_conj_frobEig_le Z hℓ τ)
    have h := classSum_eq_zero_of_nullAccessible hq hm hM hlow (norm_inv_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_neg, zpow_natCast, inv_pow]).trans
        (hmom (-(n : ℤ)))) hb hUo hUc h0 hpoles hUF hε hball hnull
    simpa only [e] using h

/-- **Null-accessible eigenvalues are seen together.** Finitely many visible outer eigenvalues
whose reciprocals are null-accessible from the origin off the closed active folded spectrum are
seen by one window of the tower of `g`. -/
theorem card_le_towerDefect_of_nullAccessibleOff (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ visibleSet Z g ℓ)
    (hacc : ∀ b ∈ O, NullAccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) b⁻¹) :
    ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) :=
  exists_towerGram_negIndex_ge_of_closure Z hZ hg hgc hℓ O hO fun b hb => by
    obtain ⟨⟨ρ, -, rfl⟩, -⟩ := hO b hb
    exact eigTarget_mem_closure_of_classSum Z hZ hg hgc _ fun a ha =>
      classSum_eq_zero_of_nullAccessibleOff Z hZ hg hgc hℓ (frobEig_ne_zero ℓ ρ) (hacc _ hb) a ha

/-- **Wolff blindness needs a wall.** If every window of the tower of `g` is positive, no visible
outer eigenvalue `b` has `b⁻¹` null-accessible: every disc about `b⁻¹` meets the closed active
folded spectrum in positive area, or contains points that it walls off from the origin. -/
theorem not_nullAccessibleOff_of_towerGram_psd (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hpsd : ∀ K : Finset ℤ, hermNegIndex (towerGram Z g ℓ K) = 0) {b : ℂ}
    (hb : b ∈ visibleSet Z g ℓ) :
    ¬ NullAccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) b⁻¹ := fun hacc => by
  obtain ⟨K, hK⟩ := card_le_towerDefect_of_nullAccessibleOff Z hZ hg hgc hℓ {b}
    (by simpa using hb) (by simpa using hacc)
  rw [hpsd K] at hK
  simp at hK

/-! ### 4. Countable folded spectra -/

/-- The **folded spectrum** at scale `ℓ`: the reciprocal eigenvalues `e^{−ℓ(τ−½)}` of all zeros. -/
def foldedSpectrum (Z : ZeroConfig) (ℓ : ℝ) : Set ℂ :=
  {w | ∃ τ ∈ Z.carrier, w = (frobEig ℓ τ)⁻¹}

theorem activeFoldedSpectrum_subset (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) :
    activeFoldedSpectrum Z g ℓ ⊆ foldedSpectrum Z ℓ := by
  rintro w ⟨τ, hτ, -, rfl⟩
  exact ⟨τ, hτ, rfl⟩

/-- **Countable folded spectra do not blind a fixed test.** If the closed active folded spectrum
meets the unit disc in a countable set, every finite set of visible outer eigenvalues is seen by
one window of the tower of `g`, whether or not their reciprocals are isolated. -/
theorem card_le_towerDefect_of_countable_folded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcount : (closure (activeFoldedSpectrum Z g ℓ) ∩ ball (0 : ℂ) 1).Countable)
    (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ visibleSet Z g ℓ) :
    ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) := by
  have hlow : closure (activeFoldedSpectrum Z g ℓ) ⊆ {z : ℂ | Real.exp (-(ℓ / 2)) ≤ ‖z‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    rintro z ⟨τ, hτ, -, rfl⟩
    show Real.exp (-(ℓ / 2)) ≤ ‖(frobEig ℓ τ)⁻¹‖
    rw [norm_inv, norm_frobEig, ← Real.exp_neg, Real.exp_le_exp]
    have := (Z.strip _ hτ).2
    nlinarith
  have h0 : (0 : ℂ) ∉ closure (activeFoldedSpectrum Z g ℓ) := fun h => by
    have := hlow h
    simp only [Set.mem_setOf_eq, norm_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  refine card_le_towerDefect_of_nullAccessibleOff Z hZ hg hgc hℓ O hO fun b hb => ?_
  obtain ⟨⟨ρ, hρ, rfl⟩, -⟩ := hO b hb
  refine nullAccessibleOff_of_countable isClosed_closure one_pos hcount h0 ?_
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ ((one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2)

/-- **A fixed test carries every visible eigenvalue of a countable folded spectrum.** If the
closed active folded spectrum meets the unit disc in a countable set, some window of the tower of
`g` has `n` negative squares iff at least `n` outer eigenvalues are visible to `g`. -/
theorem tower_law_of_countable_folded (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcount : (closure (activeFoldedSpectrum Z g ℓ) ∩ ball (0 : ℂ) 1).Countable) (n : ℕ) :
    (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
      (n : ℕ∞) ≤ (visibleSet Z g ℓ).encard := by
  constructor
  · rintro ⟨K, hK⟩
    exact (ENat.coe_le_coe.mpr hK).trans
      ((wfVisibleSet_sandwich_and_infinite_law Z hZ hg hgc hℓ).2.1 K).1
  · intro hn
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hn
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
    obtain ⟨K, hK⟩ := card_le_towerDefect_of_countable_folded Z hZ hg hgc hℓ hcount
      htfin.toFinset fun b hb => hts (htfin.mem_toFinset.mp hb)
    have hcard : htfin.toFinset.card = n := by
      have h := htfin.encard_eq_coe_toFinset_card
      rw [htc] at h
      exact_mod_cast h.symm
    exact ⟨K, hcard ▸ hK⟩

/-- **Countable folded spectra: one test carries the whole tower defect.** If at scale `ℓ` the
closed folded spectrum of all zeros meets the unit disc in a countable set, one probe has, on some
window of its tower, `n` negative squares iff there are at least `n` distinct outer eigenvalues —
finitely or infinitely many, with no condition on the order of the real parts. -/
theorem exists_test_tower_law_of_countable_folded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hcount : (closure (foldedSpectrum Z ℓ) ∩ ball (0 : ℂ) 1).Countable) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
        (n : ℕ∞) ≤ (outerEig Z ℓ).encard := by
  have hR : (rightZeros Z).Countable :=
    (SquareRootThreshold.countable_carrier Z).mono fun _ h => h.1
  set B : Set ℝ := ⋃ b ∈ outerEig Z ℓ, {s : ℝ | frobWeight Z (probe s 0) ℓ b = 0}
  have hB : B.Countable := (hR.image _).biUnion fun b hb => countable_badModulation Z hZ hℓ hb
  obtain ⟨s, hs⟩ : ∃ s, s ∉ B := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real (hB.mono fun s _ => h s)
  have hvis : visibleSet Z (probe s 0) ℓ = outerEig Z ℓ := by
    ext b
    exact ⟨fun h => h.1, fun hb => ⟨hb, fun h0 => hs (Set.mem_biUnion hb h0)⟩⟩
  have hcount' : (closure (activeFoldedSpectrum Z (probe s 0) ℓ) ∩ ball (0 : ℂ) 1).Countable :=
    hcount.mono (inter_subset_inter_left _
      (closure_mono (activeFoldedSpectrum_subset Z _ ℓ)))
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun n => ?_⟩
  rw [← hvis]
  exact tower_law_of_countable_folded Z hZ (probe_contDiff s 0) (probe_hasCompactSupport s 0) hℓ
    hcount' n

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
