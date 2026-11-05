import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.NearLineDensityBesselCertificateAndSeparation
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TwoSidedThetaMollifierTrap
import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.HalfPlaneMollifiedGreenReading
import GaloisForLFunctions.RHTower.SelbergNearLineCriticalGateDensity
import GaloisForLFunctions.RHTower.SteinhausEulerLocalMeanSq
import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValues
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Log

/-!
# Sharp `V / log V` Zero-Detection Phase Transition and Subcritical Mollifier Disc-Corridor Divergence

This module establishes the sharp zero-detection threshold for `LogFreeNearLineWindowOccupancy`
(`D_win`) together with the unconditional `V log V` disc-corridor divergence of all polynomial
subcritical Dirichlet mollifiers (`0 < θ < 1/2`) and the discrete `log N` sharpness of Gallagher's
separated large-values bound:

1. **Sharp `V / log V` Disc-Detection Sufficiency:** Any holomorphic zero-detector `F` on
   `[1/2, 2] ×ℂ [V - 5, 2V + 5]` vanishing on right-half `ξ`-zeros at depth `≥ A / log V` inside
   Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]` whose shifted `L²` defect on
   `σ ∈ [1/2 + A/(2 log V), 1 + A/(2 log V)]` is bounded by `C e^{-r(σ - 1/2) log V} · (V / log V)`
   forces at most `(32 C / (π r)) (e^{-r A / 2} / A²) V` occupied windows, hence implies
   `LogFreeNearLineWindowOccupancy`.
2. **Sharp `V / log V` Impossibility Across All `Lᵖ` (`1 ≤ p < ∞`) and `log⁺`:** The normalized
   Fejér–Dirichlet polynomial `F_V(s) = 1 - D_V(s)` (`b₁ = 1`, length `≤ ⌊V^θ⌋`) vanishes on
   `Re s = 1/2 + A / log V` inside `≥ V / 12` distinct Burnol unit windows while satisfying
   `∫_{V-5}^{2V+5} ‖F_V(σ + it) - 1‖^p dt ≪_{p,θ,A} V / log V` and
   `∫_{V-5}^{2V+5} max(0, log‖F_V(σ + it)‖) dt ≪_{θ,A} V / log V` uniformly for all `σ ≥ 1/2`.
3. **Log-Free Barban–Vehov Shifted `L²` Defect at Scale `V`:** Unconditionally for `ζ`, the
   two-length Barban–Vehov mollifier `M_{X,Y}` (`r/2 < θ_Y < θ_X < 1/2`) achieves
   `∫_{T₁}^{T₂} ‖ζ(σ₀ + it) M_{X,Y}(σ₀ + it) - 1‖² dt ≤ (T₂ - T₁) A₀ e^{-r(σ₀ - 1/2) log S} + 240 S^{θ_X + 1/2}`.
4. **Universal Subcritical Mollifier Defect Floor & `V log V` Disc-Corridor Divergence:** Every
   normalized polynomial mollifier `Ψ` (`1 ≤ y ≤ V^θ`, `0 < θ < 1/2`, `b₁ = 1`, `‖b_d‖ ≤ 1`) has
   shifted defect `∫_V^{2V} ‖ζΨ(1/2 + a/log V + it) - 1‖² dt ≥ (subcriticalShiftedDefectFloor θ a - ε) V`
   (`subcriticalShiftedDefectFloor θ a > 0`), so its 2D disc-corridor bound is eventually at least
   `(subcriticalShiftedDefectFloor θ A / (2 π A)) V log V`.
5. **Sharpness of Gallagher's Discrete Dirichlet Large-Values `log N` Factor:** For every `N ≥ 4`
   and `V ≥ 40`, a dyadic resonant Dirichlet polynomial achieves
   `∑_r ‖dirPoly N a (λ_r)‖² ≥ (1/40) V (log N) ∑_m ‖a_m‖²` over `> 9`-separated ordinates in `[V, 2V]`.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology Classical

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §0. Planar box integration and decimal calibration of `2π / log 2` -/

theorem two_pi_div_log_two_bounds :
    (9 : ℝ) < 2 * Real.pi / Real.log 2 ∧ 2 * Real.pi / Real.log 2 < 10 := by
  have hlog_lo : (6931 / 10000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_hi : Real.log 2 < 6932 / 10000 := by linarith [Real.log_two_lt_d9]
  have hlog_pos : 0 < Real.log 2 := by linarith
  have hpi_lo : (3141 / 1000 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d20; norm_num at h; linarith
  have hpi_hi : Real.pi < 3142 / 1000 := by
    have h := Real.pi_lt_d20; norm_num at h; linarith
  constructor
  · rw [lt_div_iff₀ hlog_pos]; linarith
  · rw [div_lt_iff₀ hlog_pos]; linarith

theorem isClosed_reProdIm_Icc (a b c d : ℝ) : IsClosed (Icc a b ×ℂ Icc c d) := by
  have heq : (Icc a b ×ℂ Icc c d) = (Complex.re ⁻¹' Icc a b) ∩ (Complex.im ⁻¹' Icc c d) := by
    ext z; simp [Complex.mem_reProdIm]
  rw [heq]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

theorem isCompact_reProdIm_Icc (a b c d : ℝ) : IsCompact (Icc a b ×ℂ Icc c d) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_closedBall (0 : ℂ) (max |a| |b| + max |c| |d|))
    (isClosed_reProdIm_Icc a b c d) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |z.re| ≤ max |a| |b| := abs_le_max_abs_abs hz.1.1 hz.1.2
  have him : |z.im| ≤ max |c| |d| := abs_le_max_abs_abs hz.2.1 hz.2.2
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hre him)

/-- Iterated vertical-then-horizontal evaluation of a 2D area integral on a closed rectangle
`[a, b] ×ℂ [c, d]` for any function continuous on the rectangle. -/
theorem setIntegral_reProdIm_eq_iterated_of_continuousOn {f : ℂ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hf : ContinuousOn f (Icc a b ×ℂ Icc c d)) :
    ∫ z in Icc a b ×ℂ Icc c d, f z =
      ∫ x in a..b, ∫ y in c..d, f ((x : ℂ) + (y : ℂ) * I) := by
  have hK_closed : IsClosed (Icc a b ×ℂ Icc c d) := isClosed_reProdIm_Icc a b c d
  let f₀ : C(Icc a b ×ℂ Icc c d, ℝ) := ⟨fun z => f z, hf.restrict⟩
  obtain ⟨F_ext, hF_ext⟩ := f₀.exists_restrict_eq hK_closed
  have heq : ∀ z ∈ Icc a b ×ℂ Icc c d, F_ext z = f z := fun z hz =>
    congrArg (fun H : C(Icc a b ×ℂ Icc c d, ℝ) => H ⟨z, hz⟩) hF_ext
  let G : ℝ × ℝ → ℝ := fun p => F_ext ((p.1 : ℂ) + (p.2 : ℂ) * I)
  have hGc : Continuous G := F_ext.continuous.comp (by fun_prop)
  have hpre : (Icc a b ×ℂ Icc c d) = measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d) := by
    ext z; simp [Complex.mem_reProdIm, Complex.measurableEquivRealProd]; tauto
  have hG : ∀ z : ℂ, G (measurableEquivRealProd z) = F_ext z := fun z => by
    simp [G, Complex.measurableEquivRealProd, Complex.re_add_im]
  have hp := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding G (Icc a b ×ˢ Icc c d)
  have hint : Integrable G ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hGc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc ∫ z in Icc a b ×ℂ Icc c d, f z
      = ∫ z in Icc a b ×ℂ Icc c d, F_ext z :=
        setIntegral_congr_fun hK_closed.measurableSet fun z hz => (heq z hz).symm
    _ = ∫ z in measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d), G (measurableEquivRealProd z) := by
        rw [hpre]; simp only [hG]
    _ = ∫ p in Icc a b ×ˢ Icc c d, G p := hp
    _ = ∫ x in Icc a b, ∫ y in Icc c d, G (x, y) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod G hint]
    _ = ∫ x in a..b, ∫ y in c..d, F_ext ((x : ℂ) + (y : ℂ) * I) := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
        rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
    _ = ∫ x in a..b, ∫ y in c..d, f ((x : ℂ) + (y : ℂ) * I) := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [Set.uIcc_of_le hab] at hx
        refine intervalIntegral.integral_congr fun y hy => ?_
        rw [Set.uIcc_of_le hcd] at hy
        apply heq
        simp [Complex.mem_reProdIm, hx.1, hx.2, hy.1, hy.2]

/-- Superadditivity of a nonnegative continuous area integrand over pairwise disjoint open balls
contained in a compact rectangle `K`. -/
theorem sum_ball_integral_le_setIntegral {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {c : ι → ℂ} {R : ℝ} {K : Set ℂ} {g : ℂ → ℝ}
    (hK_meas : MeasurableSet K) (hK_comp : IsCompact K) (hg_cont : ContinuousOn g K)
    (hg_nn : ∀ z ∈ K, 0 ≤ g z) (hsub : ∀ i ∈ S, Metric.ball (c i) R ⊆ K)
    (hdisj : (S : Set ι).PairwiseDisjoint (fun i => Metric.ball (c i) R)) :
    (∑ i ∈ S, ∫ z in Metric.ball (c i) R, g z) ≤ ∫ z in K, g z := by
  have hintK : IntegrableOn g K volume := hg_cont.integrableOn_compact hK_comp
  have hint_indK : Integrable (K.indicator g) volume := hintK.integrable_indicator hK_meas
  have hint_ball : ∀ i ∈ S, Integrable ((Metric.ball (c i) R).indicator g) volume := fun i hi =>
    (hintK.mono_set (hsub i hi)).integrable_indicator measurableSet_ball
  have hrew : (∑ i ∈ S, ∫ z in Metric.ball (c i) R, g z) =
      ∫ z, ∑ i ∈ S, (Metric.ball (c i) R).indicator g z := by
    calc (∑ i ∈ S, ∫ z in Metric.ball (c i) R, g z)
        = ∑ i ∈ S, ∫ z, (Metric.ball (c i) R).indicator g z :=
          Finset.sum_congr rfl fun i _ => (integral_indicator measurableSet_ball).symm
      _ = ∫ z, ∑ i ∈ S, (Metric.ball (c i) R).indicator g z :=
          (integral_finsetSum S fun i hi => hint_ball i hi).symm
  rw [hrew, ← integral_indicator hK_meas]
  refine integral_mono (integrable_finsetSum S fun i hi => hint_ball i hi) hint_indK fun z => ?_
  by_cases hex : ∃ i ∈ S, z ∈ Metric.ball (c i) R
  · obtain ⟨i₀, hi₀S, hzi₀⟩ := hex
    have hK_mem : z ∈ K := hsub i₀ hi₀S hzi₀
    rw [Finset.sum_eq_single i₀]
    · rw [Set.indicator_of_mem hzi₀, Set.indicator_of_mem hK_mem]
    · intro j hjS hji₀
      have hnot : z ∉ Metric.ball (c j) R :=
        Set.disjoint_left.mp (hdisj hi₀S hjS hji₀.symm) hzi₀
      exact Set.indicator_of_notMem hnot g
    · intro hi₀_not; exact absurd hi₀S hi₀_not
  · push Not at hex
    have hzero : (∑ i ∈ S, (Metric.ball (c i) R).indicator g z) = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hex i hi) g
    rw [hzero]
    exact Set.indicator_nonneg hg_nn z

/-! ## §1. Sharp `V / log V` disc-detection sufficiency (`D_win`) -/

theorem finset_exists_mod8_class_card_ge (B : Finset ℕ) :
    ∃ j : Fin 8, B.card ≤ 8 * (B.filter (fun m => m % 8 = j.val)).card := by
  have hpart : B.card = ∑ j : Fin 8, (B.filter (fun m => m % 8 = j.val)).card := by
    have h1 : ∀ m ∈ B, (1 : ℕ) = ∑ j : Fin 8, if m % 8 = j.val then 1 else 0 := by
      intro m _
      let j₀ : Fin 8 := ⟨m % 8, Nat.mod_lt m (by norm_num)⟩
      rw [Finset.sum_eq_single j₀]
      · simp [j₀]
      · intro j _ hj; rw [if_neg]; intro heq; apply hj; ext; exact heq.symm
      · intro h; exact absurd (Finset.mem_univ j₀) h
    calc B.card = ∑ m ∈ B, 1 := Finset.card_eq_sum_ones B
      _ = ∑ m ∈ B, ∑ j : Fin 8, if m % 8 = j.val then 1 else 0 :=
          Finset.sum_congr rfl fun m hm => h1 m hm
      _ = ∑ j : Fin 8, ∑ m ∈ B, if m % 8 = j.val then 1 else 0 := Finset.sum_comm
      _ = ∑ j : Fin 8, (B.filter (fun m => m % 8 = j.val)).card := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_filter]
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin 8 => (B.filter (fun m => m % 8 = j.val)).card) Finset.univ_nonempty
  refine ⟨j₀, ?_⟩
  calc B.card = ∑ j : Fin 8, (B.filter (fun m => m % 8 = j.val)).card := hpart
    _ ≤ ∑ _j : Fin 8, (B.filter (fun m => m % 8 = j₀.val)).card :=
        Finset.sum_le_sum fun j hj => hj₀ j hj
    _ = 8 * (B.filter (fun m => m % 8 = j₀.val)).card := by
        rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]

/-- **Sharp `V / log V` disc-detection sufficiency at finite height `V`.**
If a holomorphic detector `F` on `[1/2, 2] ×ℂ [V - 5, 2V + 5]` vanishes at every right-half
`ξ`-zero of depth `≥ A / log V` in Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]` and its shifted `L²`
defect on `[V - 5, 2V + 5]` is bounded by `C e^{-r(σ - 1/2) log V} · (V / log V)` across the
corridor `σ ∈ [1/2 + A/(2 log V), 1 + A/(2 log V)]`, then the number of `A / log V`-occupied
Burnol windows is at most `(32 C / (π r)) · (e^{-r A / 2} / A²) · V`. -/
theorem occupiedBurnolWindows_le_of_shiftedDefect_div_log
    {V A C r : ℝ} (hV : Real.exp 2 ≤ V) (hA0 : 0 < A) (hAL : A ≤ Real.log V)
    (hC0 : 0 ≤ C) (hr0 : 0 < r) {F : ℂ → ℂ}
    (hF_diff : DifferentiableOn ℂ F (Icc (1 / 2) 2 ×ℂ Icc (V - 5) (2 * V + 5)))
    (hF_zero : ∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
      ∀ ρ ∈ burnolUnitXiZeros m, 1 / 2 + A / Real.log V ≤ ρ.re → F ρ = 0)
    (hF_L2 : ∀ σ ∈ Icc (1 / 2 + A / (2 * Real.log V)) (1 + A / (2 * Real.log V)),
      (∫ t in (V - 5)..(2 * V + 5), ‖F ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) ≤
        C * Real.exp (-(r * (σ - 1 / 2) * Real.log V)) * (V / Real.log V)) :
    (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
      (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|)).card : ℝ) ≤
      (32 * C / (Real.pi * r)) * (Real.exp (-(r * A / 2)) / A ^ 2) * V := by
  classical
  have hV_pos : 0 < V := lt_of_lt_of_le (Real.exp_pos 2) hV
  have hV_ge7 : 7 ≤ V := by
    have he2 : (7 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  have hL_ge2 : 2 ≤ Real.log V := by
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log V := Real.log_le_log (Real.exp_pos 2) hV
  have hL_pos : 0 < Real.log V := by linarith
  have ⟨R, hR_def⟩ : ∃ x : ℝ, x = A / (2 * Real.log V) := ⟨_, rfl⟩
  have hR_pos : 0 < R := by rw [hR_def]; positivity
  have hR_le_half : R ≤ 1 / 2 := by
    rw [hR_def, div_le_iff₀ (by positivity)]
    linarith
  have ⟨B, hB_def⟩ : ∃ s : Finset ℕ, s = (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
    (fun m => ∃ ρ ∈ burnolUnitXiZeros m, A / Real.log V ≤ |ρ.re - 1 / 2|) := ⟨_, rfl⟩
  rw [← hB_def]
  have hex_right : ∀ m ∈ B, ∃ ρ ∈ burnolUnitXiZeros m, 1 / 2 + A / Real.log V ≤ ρ.re := by
    intro m hm
    rw [hB_def, Finset.mem_filter] at hm
    obtain ⟨_, ρ, hρ_mem, hρ_abs⟩ := hm
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
    · refine ⟨ρ, hρ_mem, ?_⟩
      rw [abs_of_nonneg (by linarith)] at hρ_abs
      linarith
    · refine ⟨1 - star ρ, one_sub_star_mem_burnolUnitXiZeros m ρ hρ_mem, ?_⟩
      rw [abs_of_neg (by linarith)] at hρ_abs
      have hre_star : (1 - star ρ).re = 1 - ρ.re := by simp
      linarith
  let ρ_sel : ℕ → ℂ := fun m =>
    if hm : m ∈ B then Classical.choose (hex_right m hm) else 0
  have hρ_prop : ∀ m (hm : m ∈ B),
      ρ_sel m ∈ burnolUnitXiZeros m ∧ 1 / 2 + A / Real.log V ≤ (ρ_sel m).re := by
    intro m hm
    dsimp [ρ_sel]
    rw [dif_pos hm]
    exact Classical.choose_spec (hex_right m hm)
  obtain ⟨j₀, hj₀_card⟩ := finset_exists_mod8_class_card_ge B
  have ⟨B₀, hB₀_def⟩ : ∃ s : Finset ℕ, s = B.filter (fun m => m % 8 = j₀.val) := ⟨_, rfl⟩
  rw [← hB₀_def] at hj₀_card
  have ⟨K_cor, hK_def⟩ : ∃ s : Set ℂ, s = Icc (1 / 2 + R) (1 + R) ×ℂ Icc (V - 5) (2 * V + 5) :=
    ⟨_, rfl⟩
  have hK_sub_big : K_cor ⊆ Icc (1 / 2) 2 ×ℂ Icc (V - 5) (2 * V + 5) := by
    intro z hz
    rw [hK_def] at hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hm_bounds : ∀ m ∈ B₀, m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)) ∧
      V - 3 < (ρ_sel m).im ∧ (ρ_sel m).im < 2 * V + 3 ∧ (ρ_sel m).re < 1 := by
    intro m hm₀
    have hmB : m ∈ B := by rw [hB₀_def, Finset.mem_filter] at hm₀; exact hm₀.1
    have hmIcc : m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)) := by
      rw [hB_def, Finset.mem_filter] at hmB; exact hmB.1
    obtain ⟨hρ_mem, _⟩ := hρ_prop m hmB
    have hρ_iff := (mem_burnolUnitXiZeros_iff m (ρ_sel m)).mp hρ_mem
    have hcoords := burnolUnit_coords m
    have hm_lo : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hmIcc).1)
    have hm_hi : (m : ℝ) ≤ 2 * V :=
      (by exact_mod_cast (Finset.mem_Icc.mp hmIcc).2 : (m : ℝ) ≤ (Nat.floor (2 * V) : ℝ)).trans
        (Nat.floor_le (by positivity))
    refine ⟨hmIcc, ?_, ?_, hρ_iff.1.2.1⟩
    · linarith [hcoords.2.2.1, hcoords.2.2.2.2, hρ_iff.1.2.2.1]
    · linarith [hcoords.2.2.2.1, hρ_iff.1.2.2.2]
  have hball_sub_K : ∀ m ∈ B₀, Metric.closedBall (ρ_sel m) R ⊆ K_cor := by
    intro m hm₀ z hz
    have hmB : m ∈ B := by rw [hB₀_def, Finset.mem_filter] at hm₀; exact hm₀.1
    obtain ⟨_, hρ_re_lo⟩ := hρ_prop m hmB
    obtain ⟨_, him_lo, him_hi, hρ_re_hi⟩ := hm_bounds m hm₀
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff : |z.re - (ρ_sel m).re| ≤ R :=
      (Complex.abs_re_le_norm (z - ρ_sel m)).trans hz
    have him_diff : |z.im - (ρ_sel m).im| ≤ R :=
      (Complex.abs_im_le_norm (z - ρ_sel m)).trans hz
    have h2R : A / Real.log V = 2 * R := by rw [hR_def]; ring
    rw [hK_def]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith [(abs_le.mp hre_diff).1, h2R]
    · linarith [(abs_le.mp hre_diff).2]
    · linarith [(abs_le.mp him_diff).1]
    · linarith [(abs_le.mp him_diff).2]
  have hdisj : (B₀ : Set ℕ).PairwiseDisjoint (fun m => Metric.ball (ρ_sel m) R) := by
    intro m₁ hm₁ m₂ hm₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz₁ hz₂
    rw [Finset.mem_coe, hB₀_def, Finset.mem_filter] at hm₁ hm₂
    have hmod : m₁ % 8 = m₂ % 8 := hm₁.2.trans hm₂.2.symm
    have hgap : (8 : ℝ) ≤ |(m₁ : ℝ) - (m₂ : ℝ)| := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h8 : m₁ + 8 ≤ m₂ := by omega
        have hcast : (m₁ : ℝ) + 8 ≤ (m₂ : ℝ) := by exact_mod_cast h8
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have h8 : m₂ + 8 ≤ m₁ := by omega
        have hcast : (m₂ : ℝ) + 8 ≤ (m₁ : ℝ) := by exact_mod_cast h8
        rw [abs_of_nonneg (by linarith)]; linarith
    have hc₁ := burnolUnit_coords m₁
    have hc₂ := burnolUnit_coords m₂
    have him₁ := ((mem_burnolUnitXiZeros_iff m₁ (ρ_sel m₁)).mp (hρ_prop m₁ hm₁.1).1).1.2.2
    have him₂ := ((mem_burnolUnitXiZeros_iff m₂ (ρ_sel m₂)).mp (hρ_prop m₂ hm₂.1).1).1.2.2
    have him_gap : 2 < |(ρ_sel m₁).im - (ρ_sel m₂).im| := by
      rcases le_or_gt (m₁ : ℝ) (m₂ : ℝ) with hle | hgt
      · rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hgap
        rw [abs_sub_comm, abs_of_pos (by linarith [hc₁.2.2.2.1, hc₂.2.2.1, hc₂.2.2.2.2, him₁.2, him₂.1])]
        linarith [hc₁.2.2.2.1, hc₂.2.2.1, hc₂.2.2.2.2, him₁.2, him₂.1]
      · rw [abs_of_pos (by linarith)] at hgap
        rw [abs_of_pos (by linarith [hc₂.2.2.2.1, hc₁.2.2.1, hc₁.2.2.2.2, him₂.2, him₁.1])]
        linarith [hc₂.2.2.2.1, hc₁.2.2.1, hc₁.2.2.2.2, him₂.2, him₁.1]
    rw [Metric.mem_ball, dist_eq_norm] at hz₁ hz₂
    have hd₁ : |z.im - (ρ_sel m₁).im| < R := by
      simpa [Complex.sub_im] using lt_of_le_of_lt (Complex.abs_im_le_norm (z - ρ_sel m₁)) hz₁
    have hd₂ : |z.im - (ρ_sel m₂).im| < R := by
      simpa [Complex.sub_im] using lt_of_le_of_lt (Complex.abs_im_le_norm (z - ρ_sel m₂)) hz₂
    have htri : |(ρ_sel m₁).im - (ρ_sel m₂).im| ≤
        |z.im - (ρ_sel m₂).im| + |z.im - (ρ_sel m₁).im| := by
      have : (ρ_sel m₁).im - (ρ_sel m₂).im = (z.im - (ρ_sel m₂).im) - (z.im - (ρ_sel m₁).im) := by ring
      rw [this]; exact abs_sub _ _
    linarith
  have hball_lb : ∀ m ∈ B₀, Real.pi * R ^ 2 ≤ ∫ z in Metric.ball (ρ_sel m) R, ‖F z - 1‖ ^ 2 := by
    intro m hm₀
    have hmB : m ∈ B := by rw [hB₀_def, Finset.mem_filter] at hm₀; exact hm₀.1
    obtain ⟨hρ_mem, hρ_re⟩ := hρ_prop m hmB
    obtain ⟨hmIcc, _, _, _⟩ := hm_bounds m hm₀
    have hF0 : F (ρ_sel m) = 0 := hF_zero m hmIcc (ρ_sel m) hρ_mem hρ_re
    have hsub_big : Metric.closedBall (ρ_sel m) R ⊆
        Icc (1 / 2) 2 ×ℂ Icc (V - 5) (2 * V + 5) :=
      (hball_sub_K m hm₀).trans hK_sub_big
    have hdiff_sub : DifferentiableOn ℂ (fun z => F z - 1) (Metric.ball (ρ_sel m) R) :=
      (hF_diff.mono (Metric.ball_subset_closedBall.trans hsub_big)).sub_const 1
    have hcont_sub : ContinuousOn (fun z => F z - 1) (Metric.closedBall (ρ_sel m) R) :=
      (hF_diff.continuousOn.mono hsub_big).sub continuousOn_const
    have hmv := RHTower.norm_sq_value_mul_area_le_integral_ball_local
      (fun z => F z - 1) (ρ_sel m) hR_pos hdiff_sub hcont_sub
    rw [hF0, zero_sub, norm_neg, norm_one, one_pow, mul_one] at hmv
    exact hmv
  have hg_cont : ContinuousOn (fun z => ‖F z - 1‖ ^ 2) K_cor := by
    have hsub_cont : ContinuousOn (fun z => F z - 1) K_cor :=
      (hF_diff.continuousOn.mono hK_sub_big).sub continuousOn_const
    exact (continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hsub_cont)
  have hsum_le_K : (B₀.card : ℝ) * (Real.pi * R ^ 2) ≤ ∫ z in K_cor, ‖F z - 1‖ ^ 2 := by
    calc (B₀.card : ℝ) * (Real.pi * R ^ 2)
        = ∑ _m ∈ B₀, Real.pi * R ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ B₀, ∫ z in Metric.ball (ρ_sel m) R, ‖F z - 1‖ ^ 2 :=
          Finset.sum_le_sum fun m hm => hball_lb m hm
      _ ≤ ∫ z in K_cor, ‖F z - 1‖ ^ 2 := by
          rw [hK_def]
          exact sum_ball_integral_le_setIntegral
            (isClosed_reProdIm_Icc _ _ _ _).measurableSet
            (isCompact_reProdIm_Icc _ _ _ _)
            (by rwa [← hK_def])
            (fun _ _ => sq_nonneg _)
            (fun m hm => Metric.ball_subset_closedBall.trans
              (by rw [← hK_def]; exact hball_sub_K m hm))
            hdisj
  have hab : 1 / 2 + R ≤ 1 + R := by linarith
  have hcd : V - 5 ≤ 2 * V + 5 := by linarith
  have hiter : ∫ z in K_cor, ‖F z - 1‖ ^ 2 =
      ∫ σ in (1 / 2 + R)..(1 + R),
        ∫ t in (V - 5)..(2 * V + 5), ‖F ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 := by
    rw [hK_def]
    exact setIntegral_reProdIm_eq_iterated_of_continuousOn hab hcd (by rwa [← hK_def])
  have hslice_int : IntervalIntegrable
      (fun σ : ℝ => ∫ t in (V - 5)..(2 * V + 5), ‖F ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      volume (1 / 2 + R) (1 + R) := by
    let f₀ : C(K_cor, ℝ) := ⟨fun z => ‖F z - 1‖ ^ 2, hg_cont.restrict⟩
    have hK_closed : IsClosed K_cor := by rw [hK_def]; exact isClosed_reProdIm_Icc _ _ _ _
    obtain ⟨F_ext, hF_ext⟩ := f₀.exists_restrict_eq hK_closed
    have heq : ∀ z ∈ K_cor, F_ext z = ‖F z - 1‖ ^ 2 := fun z hz =>
      congrArg (fun H : C(K_cor, ℝ) => H ⟨z, hz⟩) hF_ext
    have hcont_param : Continuous (fun σ : ℝ =>
        ∫ t in (V - 5)..(2 * V + 5), F_ext ((σ : ℂ) + (t : ℂ) * I)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (by fun_prop : Continuous fun p : ℝ × ℝ => F_ext ((p.1 : ℂ) + (p.2 : ℂ) * I))
        (V - 5) (2 * V + 5)
    refine (hcont_param.intervalIntegrable _ _).congr fun σ hσ => ?_
    rw [Set.uIoc_of_le hab] at hσ
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hcd] at ht
    refine heq _ ?_
    rw [hK_def]
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add]
    exact ⟨⟨le_of_lt hσ.1, hσ.2⟩, ht⟩
  have hexp_int : ∫ σ in (1 / 2 + R)..(1 + R),
      C * Real.exp (-(r * (σ - 1 / 2) * Real.log V)) * (V / Real.log V) ≤
      (C * Real.exp (-(r * A / 2)) / (r * (Real.log V) ^ 2)) * V := by
    have hrL : 0 < r * Real.log V := mul_pos hr0 hL_pos
    have hderiv : ∀ σ : ℝ, HasDerivAt
        (fun x : ℝ => -(1 / (r * Real.log V)) * Real.exp (-(r * (x - 1 / 2) * Real.log V)))
        (Real.exp (-(r * (σ - 1 / 2) * Real.log V))) σ := by
      intro σ
      have hfn_eq : (fun x : ℝ => -(r * (x - 1 / 2) * Real.log V)) =
          (fun x : ℝ => -(r * Real.log V) * (x - 1 / 2)) := by
        ext x; ring
      have hd1 : HasDerivAt (fun x : ℝ => -(r * (x - 1 / 2) * Real.log V))
          (-(r * Real.log V)) σ := by
        rw [hfn_eq]
        exact (((hasDerivAt_id σ).sub_const (1 / 2 : ℝ)).const_mul
          (-(r * Real.log V))).congr_deriv (mul_one _)
      have hd2 := (Real.hasDerivAt_exp _).comp σ hd1
      refine (hd2.const_mul (-(1 / (r * Real.log V)))).congr_deriv ?_
      have hrL_ne : r * Real.log V ≠ 0 := hrL.ne'
      field_simp
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 1 / 2 + R) (b := 1 + R)
      (fun σ _ => hderiv σ) ((Continuous.intervalIntegrable (by fun_prop) _ _))
    have hrew_int : (∫ σ in (1 / 2 + R)..(1 + R),
        C * Real.exp (-(r * (σ - 1 / 2) * Real.log V)) * (V / Real.log V)) =
        (C * (V / Real.log V)) *
          ∫ σ in (1 / 2 + R)..(1 + R), Real.exp (-(r * (σ - 1 / 2) * Real.log V)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun σ _ => by ring
    rw [hrew_int, hftc]
    have hexp_lo : 1 / 2 + R - 1 / 2 = A / (2 * Real.log V) := by rw [hR_def]; ring
    have hexp_arg : -(r * (1 / 2 + R - 1 / 2) * Real.log V) = -(r * A / 2) := by
      rw [hexp_lo]; field_simp
    rw [hexp_arg]
    have hdrop : -(1 / (r * Real.log V)) * Real.exp (-(r * (1 + R - 1 / 2) * Real.log V)) -
        -(1 / (r * Real.log V)) * Real.exp (-(r * A / 2)) ≤
        (1 / (r * Real.log V)) * Real.exp (-(r * A / 2)) := by
      have hpos_term : 0 ≤ (1 / (r * Real.log V)) *
          Real.exp (-(r * (1 + R - 1 / 2) * Real.log V)) := by positivity
      linarith
    calc (C * (V / Real.log V)) *
          (-(1 / (r * Real.log V)) * Real.exp (-(r * (1 + R - 1 / 2) * Real.log V)) -
            -(1 / (r * Real.log V)) * Real.exp (-(r * A / 2)))
        ≤ (C * (V / Real.log V)) * ((1 / (r * Real.log V)) * Real.exp (-(r * A / 2))) :=
          mul_le_mul_of_nonneg_left hdrop (by positivity)
      _ = (C * Real.exp (-(r * A / 2)) / (r * (Real.log V) ^ 2)) * V := by field_simp
  have hK_ub : ∫ z in K_cor, ‖F z - 1‖ ^ 2 ≤
      (C * Real.exp (-(r * A / 2)) / (r * (Real.log V) ^ 2)) * V := by
    rw [hiter]
    refine (intervalIntegral.integral_mono_on hab hslice_int
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun σ hσ => ?_).trans hexp_int
    rw [← hR_def] at hF_L2
    exact hF_L2 σ hσ
  have hB₀_real : (B₀.card : ℝ) * (Real.pi * R ^ 2) ≤
      (C * Real.exp (-(r * A / 2)) / (r * (Real.log V) ^ 2)) * V :=
    hsum_le_K.trans hK_ub
  have hpiR2_pos : 0 < Real.pi * R ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hR_pos)
  have hB₀_bound : (B₀.card : ℝ) ≤
      (4 * C / (Real.pi * r)) * (Real.exp (-(r * A / 2)) / A ^ 2) * V := by
    rw [← le_div_iff₀ hpiR2_pos] at hB₀_real
    refine hB₀_real.trans (le_of_eq ?_)
    rw [hR_def]
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hr_ne : r ≠ 0 := hr0.ne'
    have hA_ne : A ≠ 0 := hA0.ne'
    have hL_ne : Real.log V ≠ 0 := hL_pos.ne'
    field_simp
    ring
  have hB_le_8 : (B.card : ℝ) ≤ 8 * (B₀.card : ℝ) := by exact_mod_cast hj₀_card
  calc (B.card : ℝ) ≤ 8 * (B₀.card : ℝ) := hB_le_8
    _ ≤ 8 * ((4 * C / (Real.pi * r)) * (Real.exp (-(r * A / 2)) / A ^ 2) * V) :=
        mul_le_mul_of_nonneg_left hB₀_bound (by norm_num)
    _ = (32 * C / (Real.pi * r)) * (Real.exp (-(r * A / 2)) / A ^ 2) * V := by ring

/-- **Global `D_win` corollary of `V / log V` shifted-defect zero detection.** -/
theorem logFreeNearLineWindowOccupancy_of_shiftedDefect_div_log
    {C r : ℝ} (hC0 : 0 ≤ C) (hr0 : 0 < r)
    (hdet : ∀ A : ℝ, 0 < A → ∀ᶠ V : ℝ in atTop, ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F (Icc (1 / 2) 2 ×ℂ Icc (V - 5) (2 * V + 5)) ∧
      (∀ m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)),
        ∀ ρ ∈ burnolUnitXiZeros m, 1 / 2 + A / Real.log V ≤ ρ.re → F ρ = 0) ∧
      (∀ σ ∈ Icc (1 / 2 + A / (2 * Real.log V)) (1 + A / (2 * Real.log V)),
        (∫ t in (V - 5)..(2 * V + 5), ‖F ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) ≤
          C * Real.exp (-(r * (σ - 1 / 2) * Real.log V)) * (V / Real.log V))) :
    LogFreeNearLineWindowOccupancy := by
  let δ : ℝ → ℝ := fun A =>
    if 0 < A then (32 * C / (Real.pi * r)) * (Real.exp (-(r * A / 2)) / A ^ 2) else 0
  refine ⟨δ, ?_, ?_⟩
  · have hexp0 : Tendsto (fun A : ℝ => Real.exp (-(r * A / 2))) atTop (𝓝 0) := by
      have hlin : Tendsto (fun A : ℝ => (r / 2) * A) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
      have hneg : Tendsto (fun A : ℝ => -(r * A / 2)) atTop atBot := by
        refine tendsto_neg_atTop_atBot.comp (hlin.congr fun A => ?_); ring
      exact Real.tendsto_exp_atBot.comp hneg
    have hinv0 : Tendsto (fun A : ℝ => (A ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    have hprod0 : Tendsto
        (fun A : ℝ => (32 * C / (Real.pi * r)) * (Real.exp (-(r * A / 2)) / A ^ 2))
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (hexp0.mul hinv0).const_mul (32 * C / (Real.pi * r))
    refine hprod0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    simp [δ, hA]
  · intro A hA0
    have hV_exp : ∀ᶠ V : ℝ in atTop, Real.exp 2 ≤ V := eventually_ge_atTop (Real.exp 2)
    have hV_log : ∀ᶠ V : ℝ in atTop, A ≤ Real.log V :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop A)
    filter_upwards [hV_exp, hV_log, hdet A hA0] with V hV hAL ⟨F, hFd, hFz, hFL2⟩
    have hbound := occupiedBurnolWindows_le_of_shiftedDefect_div_log
      hV hA0 hAL hC0 hr0 hFd hFz hFL2
    simpa [δ, hA0] using hbound

/-! ## §2. Sharp `V / log V` impossibility across all `Lᵖ` (`1 ≤ p < ∞`) and `log⁺` -/

/-- Dyadic half-length `M = ⌊θ log V / (2 log 2)⌋₊` of the Fejér–Dirichlet detector. -/
def fejerHalfLen (θ V : ℝ) : ℕ :=
  ⌊θ * Real.log V / (2 * Real.log 2)⌋₊

/-- Dirichlet coefficients of `F_V(s) = 1 - 2^{-(s - σ_*)} (M⁻¹ ∑_{j < M} 2^{-j(s - σ_*)})²`
at `σ_* = 1/2 + A / log V`, supported on dyadic powers `2^{1 + j₁ + j₂} ≤ ⌊V^θ⌋₊` with `b₁ = 1`. -/
def fejerDetectorCoeff (θ A V : ℝ) (n : ℕ) : ℂ :=
  (if n = 1 then (1 : ℂ) else 0) -
    ∑ p ∈ Finset.range (fejerHalfLen θ V) ×ˢ Finset.range (fejerHalfLen θ V),
      if 2 ^ (1 + p.1 + p.2) = n then
        (((1 / (fejerHalfLen θ V : ℝ) ^ 2) *
          (n : ℝ) ^ (1 / 2 + A / Real.log V) : ℝ) : ℂ)
      else 0

/-- The normalized Fejér–Dirichlet detector `F_V = edPoly (fejerDetectorCoeff θ A V) (Icc 1 ⌊V^θ⌋₊)`. -/
def fejerDirichletDetector (θ A V : ℝ) : ℂ → ℂ :=
  RHTower.edPoly (fejerDetectorCoeff θ A V) (Finset.Icc 1 ⌊V ^ θ⌋₊)

theorem fejerDetectorCoeff_one (θ A V : ℝ) : fejerDetectorCoeff θ A V 1 = 1 := by
  unfold fejerDetectorCoeff
  rw [if_pos rfl]
  have hzero : (∑ p ∈ Finset.range (fejerHalfLen θ V) ×ˢ Finset.range (fejerHalfLen θ V),
      if 2 ^ (1 + p.1 + p.2) = 1 then
        (((1 / (fejerHalfLen θ V : ℝ) ^ 2) *
          ((1 : ℕ) : ℝ) ^ (1 / 2 + A / Real.log V) : ℝ) : ℂ)
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    have hgt : 1 < 2 ^ (1 + p.1 + p.2) :=
      Nat.one_lt_two_pow (by omega)
    rw [if_neg (ne_of_gt hgt)]
  rw [hzero, sub_zero]

theorem fejerDirichletDetector_eq_edPoly (θ A V : ℝ) :
    fejerDirichletDetector θ A V =
      RHTower.edPoly (fejerDetectorCoeff θ A V) (Finset.Icc 1 ⌊V ^ θ⌋₊) := rfl

theorem two_pow_fejer_mem_Icc {θ V : ℝ} (hθ0 : 0 < θ) (hV1 : 1 ≤ V)
    {j₁ j₂ : ℕ} (hj₁ : j₁ < fejerHalfLen θ V) (hj₂ : j₂ < fejerHalfLen θ V) :
    2 ^ (1 + j₁ + j₂) ∈ Finset.Icc 1 ⌊V ^ θ⌋₊ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogV_nn : 0 ≤ Real.log V := Real.log_nonneg hV1
  have hM_pos : 1 ≤ fejerHalfLen θ V := by omega
  have hM_le : (fejerHalfLen θ V : ℝ) ≤ θ * Real.log V / (2 * Real.log 2) :=
    Nat.floor_le (by positivity)
  have hexp_le : 1 + j₁ + j₂ ≤ 2 * fejerHalfLen θ V := by omega
  have hpow_le_nat : 2 ^ (1 + j₁ + j₂) ≤ 2 ^ (2 * fejerHalfLen θ V) :=
    Nat.pow_le_pow_right (by norm_num) hexp_le
  have hpow_le_Vθ : ((2 ^ (2 * fejerHalfLen θ V) : ℕ) : ℝ) ≤ V ^ θ := by
    have h1 : (2 * (fejerHalfLen θ V : ℝ)) * Real.log 2 ≤ θ * Real.log V := by
      have := mul_le_mul_of_nonneg_right hM_le (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hlog2))
      have hne : (2 * Real.log 2) ≠ 0 := (mul_pos (by norm_num) hlog2).ne'
      have h2 : (fejerHalfLen θ V : ℝ) * (2 * Real.log 2) ≤ θ * Real.log V := by
        rwa [div_mul_cancel₀ _ hne] at this
      linarith
    calc ((2 ^ (2 * fejerHalfLen θ V) : ℕ) : ℝ)
        = (2 : ℝ) ^ (2 * fejerHalfLen θ V) := by push_cast; rfl
      _ = Real.exp (((2 * fejerHalfLen θ V : ℕ) : ℝ) * Real.log 2) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      _ ≤ Real.exp (θ * Real.log V) := Real.exp_le_exp.mpr (by push_cast; linarith)
      _ = V ^ θ := by rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hV1), mul_comm]
  refine Finset.mem_Icc.mpr ⟨Nat.one_le_two_pow, Nat.le_floor ?_⟩
  exact (by exact_mod_cast hpow_le_nat : ((2 ^ (1 + j₁ + j₂) : ℕ) : ℝ) ≤ _).trans hpow_le_Vθ

/-- Exact complex-square factorization of `fejerDirichletDetector θ A V z - 1` whenever
`1 ≤ fejerHalfLen θ V`. -/
theorem fejerDirichletDetector_sub_one_eq_neg_sq {θ A V : ℝ} (hθ0 : 0 < θ) (hV1 : 1 ≤ V)
    (hM1 : 1 ≤ fejerHalfLen θ V) (σ t : ℝ) :
    fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1 =
      -(Complex.exp ((((1 / 2 + A / Real.log V - σ) * Real.log 2 : ℝ) : ℂ) -
          (((Real.log 2 * t : ℝ) : ℂ) * I)) *
        (∑ j ∈ Finset.range (fejerHalfLen θ V),
          (((1 / (fejerHalfLen θ V : ℝ)) *
            Real.exp ((j : ℝ) * Real.log 2 * (1 / 2 + A / Real.log V - σ)) : ℝ) : ℂ) *
            Complex.exp (-(((j : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I)) ^ 2) := by
  have ⟨M, hM_def⟩ : ∃ m : ℕ, m = fejerHalfLen θ V := ⟨_, rfl⟩
  have ⟨σs, hσs_def⟩ : ∃ x : ℝ, x = 1 / 2 + A / Real.log V := ⟨_, rfl⟩
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 ⌊V ^ θ⌋₊ := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp
      (two_pow_fejer_mem_Icc hθ0 hV1 (by omega : 0 < fejerHalfLen θ V)
        (by omega : 0 < fejerHalfLen θ V))
    exact Finset.mem_Icc.mpr ⟨le_rfl, h1.trans h2⟩
  unfold fejerDirichletDetector RHTower.edPoly fejerDetectorCoeff
  rw [← hM_def, ← hσs_def]
  simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_mul]
  have hhead : (∑ n ∈ Finset.Icc 1 ⌊V ^ θ⌋₊,
      if n = 1 then (1 : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) else 0) = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro n _ hn1; rw [if_neg hn1]
    · intro hnot; exact absurd h1_mem hnot
  rw [hhead]
  have hswap : (∑ n ∈ Finset.Icc 1 ⌊V ^ θ⌋₊, ∑ p ∈ Finset.range M ×ˢ Finset.range M,
      (if 2 ^ (1 + p.1 + p.2) = n then
        (((1 / (M : ℝ) ^ 2) * (n : ℝ) ^ σs : ℝ) : ℂ) else 0) *
        ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) =
      ∑ p ∈ Finset.range M ×ˢ Finset.range M,
        (((1 / (M : ℝ) ^ 2) * ((2 ^ (1 + p.1 + p.2) : ℕ) : ℝ) ^ σs : ℝ) : ℂ) *
          (((2 ^ (1 + p.1 + p.2) : ℕ) : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have hmem : 2 ^ (1 + p.1 + p.2) ∈ Finset.Icc 1 ⌊V ^ θ⌋₊ := by
      rw [hM_def] at hp
      exact two_pow_fejer_mem_Icc hθ0 hV1 hp.1 hp.2
    rw [Finset.sum_eq_single (2 ^ (1 + p.1 + p.2))]
    · simp
    · intro n _ hne; rw [if_neg hne.symm, zero_mul]
    · intro hnot; exact absurd hmem hnot
  rw [hswap, sub_sub_cancel_left]
  congr 1
  have hterm_pow : ∀ k : ℕ,
      ((((2 ^ k : ℕ) : ℝ) ^ σs : ℝ) : ℂ) * (((2 ^ k : ℕ) : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
        Complex.exp ((((k : ℝ) * Real.log 2 * (σs - σ) : ℝ) : ℂ) -
          (((k : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I) := by
    intro k
    have hk_pos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hlog_pow : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hk_pos.ne'),
      Real.rpow_def_of_pos hk_pos, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.ofReal_log hk_pos.le, hlog_pow]
    congr 1; push_cast; ring
  rw [Finset.sum_product]
  conv_rhs => rw [sq, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
  have h12 := hterm_pow (1 + j₁ + j₂)
  have hsplit_c : ((((1 / (M : ℝ) ^ 2) * ((2 ^ (1 + j₁ + j₂) : ℕ) : ℝ) ^ σs : ℝ) : ℂ) *
      (((2 ^ (1 + j₁ + j₂) : ℕ) : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) =
      (((1 / (M : ℝ) ^ 2 : ℝ) : ℂ)) *
        (((((2 ^ (1 + j₁ + j₂) : ℕ) : ℝ) ^ σs : ℝ) : ℂ) *
          (((2 ^ (1 + j₁ + j₂) : ℕ) : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) := by
    push_cast; ring
  rw [hsplit_c, h12]
  simp_rw [Complex.ofReal_mul, Complex.ofReal_exp]
  have hpull : ∀ u e₀ a₁ b₁ a₂ b₂ : ℂ,
      e₀ * ((u * a₁ * b₁) * (u * a₂ * b₂)) = (u * u) * (e₀ * (a₁ * b₁ * (a₂ * b₂))) :=
    fun _ _ _ _ _ _ => by ring
  rw [hpull]
  have hcoeff_eq : (((1 / (M : ℝ) ^ 2 : ℝ) : ℂ)) =
      (((1 / (M : ℝ) : ℝ) : ℂ)) * (((1 / (M : ℝ) : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hcoeff_eq]
  congr 1
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fejér–Dirichlet detector vanishes on `Re s = 1/2 + A / log V` inside at least `(1/12) V`
distinct Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]` eventually in `V`. -/
theorem fejerDirichletDetector_occupiedWindows_ge {θ A : ℝ} (hθ0 : 0 < θ) :
    ∀ᶠ V : ℝ in atTop,
      (1 / 12 : ℝ) * V ≤
        (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter (fun m =>
          ∃ s : ℂ, s.re = 1 / 2 + A / Real.log V ∧
            burnolUnitLower m < s.im ∧ s.im < burnolUnitUpper m ∧
            fejerDirichletDetector θ A V s = 0)).card : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hV_M : ∀ᶠ V : ℝ in atTop, 2 * Real.log 2 / θ ≤ Real.log V :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (144 : ℝ), hV_M] with V hV144 hVM
  have hV1 : 1 ≤ V := by linarith
  have hM1 : 1 ≤ fejerHalfLen θ V := by
    unfold fejerHalfLen
    refine Nat.le_floor ?_
    push_cast
    rw [le_div_iff₀ (by positivity), one_mul]
    have := mul_le_mul_of_nonneg_left hVM hθ0.le
    rwa [mul_div_cancel₀ _ hθ0.ne'] at this
  have ⟨P₀, hP₀_def⟩ : ∃ x : ℝ, x = 2 * Real.pi / Real.log 2 := ⟨_, rfl⟩
  have hP₀_9 : 9 < P₀ := by rw [hP₀_def]; exact two_pi_div_log_two_bounds.1
  have hP₀_10 : P₀ < 10 := by rw [hP₀_def]; exact two_pi_div_log_two_bounds.2
  have hP₀_pos : 0 < P₀ := by linarith
  let k₀ : ℕ := ⌈(V + 1) / P₀⌉₊
  let K_cnt : ℕ := ⌊(V - 2) / P₀⌋₊
  have hK_ge1 : 1 ≤ K_cnt := by
    dsimp [K_cnt]; refine Nat.le_floor ?_
    push_cast; rw [le_div_iff₀ hP₀_pos]; linarith
  let t_pt : ℕ → ℝ := fun r => ((k₀ + r : ℕ) : ℝ) * P₀
  let m_pt : ℕ → ℕ := fun r => ⌊t_pt r⌋₊
  have ht_bounds : ∀ r ∈ Finset.range K_cnt, V + 1 ≤ t_pt r ∧ t_pt r < 2 * V - 1 := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hk₀_lo : (V + 1) / P₀ ≤ (k₀ : ℝ) := Nat.le_ceil _
    have hk₀_hi : (k₀ : ℝ) < (V + 1) / P₀ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hr_hi : (r : ℝ) + 1 ≤ (V - 2) / P₀ := by
      have hrK : (r : ℝ) + 1 ≤ (K_cnt : ℝ) := by exact_mod_cast hr
      exact hrK.trans (Nat.floor_le (div_nonneg (by linarith) hP₀_pos.le))
    constructor
    · calc V + 1 = ((V + 1) / P₀) * P₀ := (div_mul_cancel₀ _ hP₀_pos.ne').symm
        _ ≤ ((k₀ : ℝ) + (r : ℝ)) * P₀ :=
            mul_le_mul_of_nonneg_right (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) hP₀_pos.le
        _ = t_pt r := by dsimp [t_pt]; push_cast; rfl
    · calc t_pt r = ((k₀ : ℝ) + (r : ℝ)) * P₀ := by dsimp [t_pt]; push_cast; rfl
        _ < (((V + 1) / P₀ + 1) + ((V - 2) / P₀ - 1)) * P₀ :=
            mul_lt_mul_of_pos_right (by linarith) hP₀_pos
        _ = 2 * V - 1 := by field_simp; ring
  have hzero_at : ∀ r : ℕ,
      fejerDirichletDetector θ A V (((1 / 2 + A / Real.log V : ℝ) : ℂ) + (t_pt r : ℂ) * I) = 0 := by
    intro r
    have hfac := fejerDirichletDetector_sub_one_eq_neg_sq hθ0 hV1 hM1
      (1 / 2 + A / Real.log V) (t_pt r)
    rw [sub_self, zero_mul] at hfac
    have hexp_1 : Complex.exp ((0 : ℂ) - ((Real.log 2 * t_pt r : ℝ) : ℂ) * I) = 1 := by
      have harg : (0 : ℂ) - ((Real.log 2 * t_pt r : ℝ) : ℂ) * I =
          (-((k₀ + r : ℕ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        dsimp [t_pt]; rw [hP₀_def]
        have hne : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
        push_cast; field_simp; ring
      rw [harg, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    have hsum_1 : (∑ j ∈ Finset.range (fejerHalfLen θ V),
        (((1 / (fejerHalfLen θ V : ℝ)) * Real.exp ((j : ℝ) * Real.log 2 * 0) : ℝ) : ℂ) *
          Complex.exp (-(((j : ℝ) * Real.log 2 * t_pt r : ℝ) : ℂ) * I)) = 1 := by
      have hterm : ∀ j : ℕ,
          Complex.exp (-(((j : ℝ) * Real.log 2 * t_pt r : ℝ) : ℂ) * I) = 1 := by
        intro j
        have harg : -(((j : ℝ) * Real.log 2 * t_pt r : ℝ) : ℂ) * I =
            (-((j * (k₀ + r) : ℕ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
          dsimp [t_pt]; rw [hP₀_def]
          have hne : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
          push_cast; field_simp; ring
        rw [harg, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
      simp_rw [mul_zero, Real.exp_zero, mul_one, hterm, mul_one, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      have hM_ne : (fejerHalfLen θ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast; field_simp
    have hcast0 : (((0 : ℝ) : ℂ)) = (0 : ℂ) := Complex.ofReal_zero
    rw [hcast0, hexp_1, hsum_1, one_pow, mul_one] at hfac
    exact sub_eq_zero.mp (by linear_combination hfac)
  have himg_sub : (Finset.range K_cnt).image m_pt ⊆
      (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter (fun m =>
        ∃ s : ℂ, s.re = 1 / 2 + A / Real.log V ∧
          burnolUnitLower m < s.im ∧ s.im < burnolUnitUpper m ∧
          fejerDirichletDetector θ A V s = 0) := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨ht_lo, ht_hi⟩ := ht_bounds r hr
    have ht_nn : 0 ≤ t_pt r := by linarith
    have hm_le_t : (m_pt r : ℝ) ≤ t_pt r := Nat.floor_le ht_nn
    have ht_lt_m1 : t_pt r < (m_pt r : ℝ) + 1 := Nat.lt_floor_add_one (t_pt r)
    have hceil_le : Nat.ceil V ≤ m_pt r := by
      refine Nat.le_floor ?_
      have hc : (Nat.ceil V : ℝ) < V + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    have hfloor_ge : m_pt r ≤ Nat.floor (2 * V) :=
      Nat.le_floor (hm_le_t.trans (by linarith))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨hceil_le, hfloor_ge⟩,
      ((1 / 2 + A / Real.log V : ℝ) : ℂ) + (t_pt r : ℂ) * I, ?_, ?_, ?_, hzero_at r⟩
    · simp
    · have hc := burnolUnit_coords (m_pt r)
      have him : (((1 / 2 + A / Real.log V : ℝ) : ℂ) + (t_pt r : ℂ) * I).im = t_pt r := by simp
      rw [him]; linarith [hc.2.1]
    · have hc := burnolUnit_coords (m_pt r)
      have him : (((1 / 2 + A / Real.log V : ℝ) : ℂ) + (t_pt r : ℂ) * I).im = t_pt r := by simp
      rw [him]; linarith [hc.2.2.1]
  have hinj : Set.InjOn m_pt (Finset.range K_cnt) := by
    intro r₁ hr₁ r₂ hr₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgap : P₀ ≤ t_pt r₂ - t_pt r₁ := by
        have hr12 : (r₁ : ℝ) + 1 ≤ (r₂ : ℝ) := by exact_mod_cast hlt
        dsimp [t_pt]
        have : (((k₀ + r₂ : ℕ) : ℝ) - ((k₀ + r₁ : ℕ) : ℝ)) * P₀ ≥ 1 * P₀ :=
          mul_le_mul_of_nonneg_right (by push_cast; linarith) hP₀_pos.le
        linarith
      have h1 : (m_pt r₁ : ℝ) ≤ t_pt r₁ := Nat.floor_le (by linarith [(ht_bounds r₁ hr₁).1])
      have h2 : t_pt r₂ < (m_pt r₂ : ℝ) + 1 := Nat.lt_floor_add_one _
      have heqR : (m_pt r₁ : ℝ) = (m_pt r₂ : ℝ) := by exact_mod_cast heq
      linarith
    · have hgap : P₀ ≤ t_pt r₁ - t_pt r₂ := by
        have hr21 : (r₂ : ℝ) + 1 ≤ (r₁ : ℝ) := by exact_mod_cast hgt
        dsimp [t_pt]
        have : (((k₀ + r₁ : ℕ) : ℝ) - ((k₀ + r₂ : ℕ) : ℝ)) * P₀ ≥ 1 * P₀ :=
          mul_le_mul_of_nonneg_right (by push_cast; linarith) hP₀_pos.le
        linarith
      have h1 : (m_pt r₂ : ℝ) ≤ t_pt r₂ := Nat.floor_le (by linarith [(ht_bounds r₂ hr₂).1])
      have h2 : t_pt r₁ < (m_pt r₁ : ℝ) + 1 := Nat.lt_floor_add_one _
      have heqR : (m_pt r₁ : ℝ) = (m_pt r₂ : ℝ) := by exact_mod_cast heq
      linarith
  have hcard_ge : K_cnt ≤ ((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter (fun m =>
      ∃ s : ℂ, s.re = 1 / 2 + A / Real.log V ∧
        burnolUnitLower m < s.im ∧ s.im < burnolUnitUpper m ∧
        fejerDirichletDetector θ A V s = 0)).card := by
    calc K_cnt = ((Finset.range K_cnt).image m_pt).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card himg_sub
  have hK_real : (1 / 12 : ℝ) * V ≤ (K_cnt : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((V - 2) / P₀)
    have hdiv : (V - 2) / 10 ≤ (V - 2) / P₀ :=
      div_le_div_of_nonneg_left (by linarith) hP₀_pos hP₀_10.le
    dsimp [K_cnt]
    linarith
  exact hK_real.trans (by exact_mod_cast hcard_ge)

/-- One-period `L¹` bound for `fejerDirichletDetector θ A V - 1` on `[t₀, t₀ + 2π / log 2]` and
pointwise `L^∞` bound `≤ exp((1 + θ) A)` uniformly for all `σ ≥ 1/2`. -/
theorem fejerDirichletDetector_period_and_sup_le {θ A V : ℝ}
    (hθ0 : 0 < θ) (hA0 : 0 < A) (hVe : Real.exp 1 ≤ V) (hM1 : 1 ≤ fejerHalfLen θ V)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t₀ : ℝ) :
    (∀ t : ℝ, ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1‖ ≤
        Real.exp ((1 + θ) * A)) ∧
      (∫ t in t₀..(t₀ + 2 * Real.pi / Real.log 2),
        ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1‖) ≤
        ((2 * Real.pi / Real.log 2) / (fejerHalfLen θ V : ℝ)) * Real.exp ((1 + θ) * A) := by
  have hV1 : 1 ≤ V := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hVe
  have hL1 : 1 ≤ Real.log V := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log V := Real.log_le_log (Real.exp_pos 1) hVe
  have hL_pos : 0 < Real.log V := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have ⟨M, hM_def⟩ : ∃ m : ℕ, m = fejerHalfLen θ V := ⟨_, rfl⟩
  rw [← hM_def] at hM1 ⊢
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hM_le : (M : ℝ) ≤ θ * Real.log V / (2 * Real.log 2) := by
    rw [hM_def]; exact Nat.floor_le (by positivity)
  have hshift_le : 1 / 2 + A / Real.log V - σ ≤ A / Real.log V := by linarith
  let w : ℕ → ℝ := fun j =>
    (1 / (M : ℝ)) * Real.exp ((j : ℝ) * Real.log 2 * (1 / 2 + A / Real.log V - σ))
  have hw_nn : ∀ j : ℕ, 0 ≤ w j := fun j => by dsimp [w]; positivity
  have hw_le : ∀ j ∈ Finset.range M, w j ≤ (1 / (M : ℝ)) * Real.exp (θ * A / 2) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjM : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast hj.le
    have h1 : (j : ℝ) * Real.log 2 * (1 / 2 + A / Real.log V - σ) ≤
        (j : ℝ) * Real.log 2 * (A / Real.log V) :=
      mul_le_mul_of_nonneg_left hshift_le (by positivity)
    have h2 : (j : ℝ) * Real.log 2 ≤ θ * Real.log V / 2 := by
      have := mul_le_mul_of_nonneg_right (hjM.trans hM_le) hlog2.le
      have hne : Real.log 2 ≠ 0 := hlog2.ne'
      have hsimp : (θ * Real.log V / (2 * Real.log 2)) * Real.log 2 = θ * Real.log V / 2 := by
        field_simp
      rwa [hsimp] at this
    have h3 : (j : ℝ) * Real.log 2 * (A / Real.log V) ≤ θ * A / 2 := by
      calc (j : ℝ) * Real.log 2 * (A / Real.log V)
          ≤ (θ * Real.log V / 2) * (A / Real.log V) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = θ * A / 2 := by field_simp
    dsimp [w]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h1.trans h3)) (by positivity)
  have hpref_le : Real.exp ((1 / 2 + A / Real.log V - σ) * Real.log 2) ≤ Real.exp A := by
    apply Real.exp_le_exp.mpr
    have h1 : (1 / 2 + A / Real.log V - σ) * Real.log 2 ≤ (A / Real.log V) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hshift_le hlog2.le
    have h2 : A / Real.log V ≤ A := div_le_self hA0.le hL1
    nlinarith
  let S_poly : ℝ → ℂ := fun t =>
    ∑ j ∈ Finset.range M, (w j : ℂ) * Complex.exp (-(((j : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I)
  have hnorm_eq : ∀ t : ℝ,
      ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1‖ =
        Real.exp ((1 / 2 + A / Real.log V - σ) * Real.log 2) * ‖S_poly t‖ ^ 2 := by
    intro t
    have hfac := fejerDirichletDetector_sub_one_eq_neg_sq (A := A) hθ0 hV1 (by rwa [← hM_def]) σ t
    rw [← hM_def] at hfac
    rw [hfac, norm_neg, norm_mul, norm_pow]
    congr 1
    rw [sub_eq_add_neg, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal,
      show -(((Real.log 2 * t : ℝ) : ℂ) * I) = ((- (Real.log 2 * t) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  refine ⟨?_, ?_⟩
  · intro t
    rw [hnorm_eq t]
    have hS_le : ‖S_poly t‖ ≤ Real.exp (θ * A / 2) := by
      calc ‖S_poly t‖
          ≤ ∑ j ∈ Finset.range M,
              ‖(w j : ℂ) * Complex.exp (-(((j : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I)‖ :=
            norm_sum_le _ _
        _ = ∑ j ∈ Finset.range M, w j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_mul,
              show -(((j : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I =
                ((- ((j : ℝ) * Real.log 2 * t) : ℝ) : ℂ) * I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
              Real.norm_of_nonneg (hw_nn j)]
        _ ≤ ∑ _j ∈ Finset.range M, (1 / (M : ℝ)) * Real.exp (θ * A / 2) :=
            Finset.sum_le_sum fun j hj => hw_le j hj
        _ = Real.exp (θ * A / 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp
    calc Real.exp ((1 / 2 + A / Real.log V - σ) * Real.log 2) * ‖S_poly t‖ ^ 2
        ≤ Real.exp A * (Real.exp (θ * A / 2)) ^ 2 :=
          mul_le_mul hpref_le (pow_le_pow_left₀ (norm_nonneg _) hS_le 2) (sq_nonneg _)
            (Real.exp_pos _).le
      _ = Real.exp ((1 + θ) * A) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · have ⟨P₀, hP₀_def⟩ : ∃ x : ℝ, x = 2 * Real.pi / Real.log 2 := ⟨_, rfl⟩
    rw [← hP₀_def]
    have hP₀_pos : 0 < P₀ := by rw [hP₀_def]; positivity
    have hnormSq_re : ∀ t : ℝ, ‖S_poly t‖ ^ 2 = (S_poly t * star (S_poly t)).re := fun t => by
      simp [Complex.sq_norm, Complex.normSq_apply]
    have hexpand : ∀ t : ℝ, S_poly t * star (S_poly t) =
        ∑ j₁ ∈ Finset.range M, ∑ j₂ ∈ Finset.range M,
          ((w j₁ * w j₂ : ℝ) : ℂ) *
            Complex.exp (((t * (((j₂ : ℝ) - (j₁ : ℝ)) * Real.log 2) : ℝ) : ℂ) * I) := by
      intro t
      dsimp [S_poly]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₂ _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      have hconj_arg : (starRingEnd ℂ) (-(((j₂ : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I) =
          (((j₂ : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I := by
        rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, neg_mul_neg]
      rw [hconj_arg]
      have hmul : (w j₁ : ℂ) * Complex.exp (-(((j₁ : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I) *
          ((w j₂ : ℂ) * Complex.exp ((((j₂ : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I)) =
          ((w j₁ * w j₂ : ℝ) : ℂ) *
            (Complex.exp (-(((j₁ : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I) *
              Complex.exp ((((j₂ : ℝ) * Real.log 2 * t : ℝ) : ℂ) * I)) := by push_cast; ring
      rw [hmul, ← Complex.exp_add]
      congr 2; push_cast; ring
    have hphase_int : ∀ j₁ j₂ : ℕ,
        (∫ t in (0 : ℝ)..P₀,
          Complex.exp ((((t + t₀) * (((j₂ : ℝ) - (j₁ : ℝ)) * Real.log 2) : ℝ) : ℂ) * I)) =
          if j₁ = j₂ then (P₀ : ℂ) else 0 := by
      intro j₁ j₂
      let L : ℝ := ((j₂ : ℝ) - (j₁ : ℝ)) * Real.log 2
      have hsplit_t : ∀ t : ℝ,
          Complex.exp ((((t + t₀) * L : ℝ) : ℂ) * I) =
            Complex.exp (((t₀ * L : ℝ) : ℂ) * I) * Complex.exp (((t * L : ℝ) : ℂ) * I) := by
        intro t; rw [← Complex.exp_add]; congr 1; push_cast; ring
      simp_rw [show (((j₂ : ℝ) - (j₁ : ℝ)) * Real.log 2) = L from rfl, hsplit_t,
        intervalIntegral.integral_const_mul]
      by_cases h12 : j₁ = j₂
      · subst h12
        have hL0 : L = 0 := by dsimp [L]; ring
        rw [if_pos rfl, hL0, RHTower.Sieve.integral_exp_phase_zero]
        simp
      · rw [if_neg h12]
        have hne_real : (j₂ : ℝ) - (j₁ : ℝ) ≠ 0 :=
          sub_ne_zero.mpr (by exact_mod_cast Ne.symm h12)
        have hL_ne : L ≠ 0 := mul_ne_zero hne_real hlog2.ne'
        rw [RHTower.Sieve.integral_exp_phase L hL_ne P₀]
        have hexp_P : Complex.exp (((P₀ * L : ℝ) : ℂ) * I) = 1 := by
          let m_int : ℤ := (j₂ : ℤ) - (j₁ : ℤ)
          have harg : ((P₀ * L : ℝ) : ℂ) * I = (m_int : ℂ) * (2 * (Real.pi : ℂ) * I) := by
            dsimp [L, m_int]; rw [hP₀_def]
            have hne2 : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
            push_cast; field_simp
          rw [harg, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
        rw [hexp_P, sub_self, zero_div, mul_zero]
    have hS_int_c : (∫ t in t₀..(t₀ + P₀), S_poly t * star (S_poly t)) =
        ((P₀ * ∑ j ∈ Finset.range M, (w j) ^ 2 : ℝ) : ℂ) := by
      have hshift := intervalIntegral.integral_comp_add_right
        (fun t => S_poly t * star (S_poly t)) t₀ (a := 0) (b := P₀)
      rw [zero_add, add_comm P₀ t₀] at hshift
      rw [← hshift]
      simp_rw [hexpand]
      rw [intervalIntegral.integral_finsetSum]
      · trans (∑ j₁ ∈ Finset.range M, ((w j₁ * w j₁ : ℝ) : ℂ) * (P₀ : ℂ))
        · refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
          rw [intervalIntegral.integral_finsetSum]
          · simp_rw [intervalIntegral.integral_const_mul, hphase_int]
            rw [Finset.sum_eq_single j₁]
            · simp
            · intro j₂ _ hj₂₁; rw [if_neg hj₂₁.symm, mul_zero]
            · intro hnot; exact absurd hj₁ hnot
          · intro j₂ _; exact Continuous.intervalIntegrable (by fun_prop) _ _
        · push_cast
          rw [← Finset.sum_mul, mul_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => (sq _).symm
      · intro j₁ _
        exact Continuous.intervalIntegrable (continuous_finsetSum _ fun j₂ _ => by fun_prop) _ _
    have hS_cont : Continuous S_poly := continuous_finsetSum _ fun j _ => by fun_prop
    have hS_int_re : (∫ t in t₀..(t₀ + P₀), ‖S_poly t‖ ^ 2) =
        P₀ * ∑ j ∈ Finset.range M, (w j) ^ 2 := by
      simp_rw [hnormSq_re]
      have hcomm := (Complex.reCLM.intervalIntegral_comp_comm
        (Continuous.intervalIntegrable (hS_cont.mul hS_cont.star) t₀ (t₀ + P₀))).symm
      change (∫ x in t₀..(t₀ + P₀), Complex.reCLM (S_poly x * star (S_poly x))) = _
      rw [hcomm, hS_int_c]
      simp
    have hsum_w2 : ∑ j ∈ Finset.range M, (w j) ^ 2 ≤ (1 / (M : ℝ)) * Real.exp (θ * A) := by
      calc ∑ j ∈ Finset.range M, (w j) ^ 2
          ≤ ∑ _j ∈ Finset.range M, ((1 / (M : ℝ)) * Real.exp (θ * A / 2)) ^ 2 :=
            Finset.sum_le_sum fun j hj => pow_le_pow_left₀ (hw_nn j) (hw_le j hj) 2
        _ = (M : ℝ) * (((1 / (M : ℝ)) * Real.exp (θ * A / 2)) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = (1 / (M : ℝ)) * (Real.exp (θ * A / 2) * Real.exp (θ * A / 2)) := by field_simp
        _ = (1 / (M : ℝ)) * Real.exp (θ * A) := by rw [← Real.exp_add]; ring_nf
    simp_rw [hnorm_eq, intervalIntegral.integral_const_mul, hS_int_re]
    calc Real.exp ((1 / 2 + A / Real.log V - σ) * Real.log 2) *
          (P₀ * ∑ j ∈ Finset.range M, (w j) ^ 2)
        ≤ Real.exp A * (P₀ * ((1 / (M : ℝ)) * Real.exp (θ * A))) :=
          mul_le_mul hpref_le (mul_le_mul_of_nonneg_left hsum_w2 hP₀_pos.le)
            (mul_nonneg hP₀_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
            (Real.exp_pos _).le
      _ = (P₀ / (M : ℝ)) * (Real.exp A * Real.exp (θ * A)) := by ring
      _ = (P₀ / (M : ℝ)) * Real.exp ((1 + θ) * A) := by rw [← Real.exp_add]; ring_nf

/-- Full-window `[V - 5, 2V + 5]` `L¹` defect bound `≤ (8 e^{(1 + θ) A} / θ) · (V / log V)`
uniformly for all `σ ≥ 1/2`. -/
theorem fejerDirichletDetector_L1_defect_le_div_log {θ A : ℝ} (hθ0 : 0 < θ) (hA0 : 0 < A) :
    ∀ᶠ V : ℝ in atTop, ∀ σ : ℝ, 1 / 2 ≤ σ →
      (∫ t in (V - 5)..(2 * V + 5),
        ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1‖) ≤
        (8 * Real.exp ((1 + θ) * A) / θ) * (V / Real.log V) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hV_M2 : ∀ᶠ V : ℝ in atTop, 4 * Real.log 2 / θ ≤ Real.log V :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (max 20 (Real.exp 1)), hV_M2] with V hVmax hVM2 σ hσ
  have hV20 : 20 ≤ V := le_trans (le_max_left _ _) hVmax
  have hVe : Real.exp 1 ≤ V := le_trans (le_max_right _ _) hVmax
  have hL_pos : 0 < Real.log V := lt_of_lt_of_le (by positivity) hVM2
  have h2_le_x : 2 ≤ θ * Real.log V / (2 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hVM2 hθ0.le
    rw [mul_div_cancel₀ _ hθ0.ne'] at this
    linarith
  have hM1 : 1 ≤ fejerHalfLen θ V := by
    unfold fejerHalfLen; exact Nat.le_floor (by linarith)
  have hM_half : θ * Real.log V / (4 * Real.log 2) ≤ (fejerHalfLen θ V : ℝ) := by
    unfold fejerHalfLen
    have hlt := Nat.lt_floor_add_one (θ * Real.log V / (2 * Real.log 2))
    have hdiv2 : θ * Real.log V / (4 * Real.log 2) =
        (θ * Real.log V / (2 * Real.log 2)) / 2 := by ring
    linarith
  have ⟨P₀, hP₀_def⟩ : ∃ x : ℝ, x = 2 * Real.pi / Real.log 2 := ⟨_, rfl⟩
  have hP₀_9 : 9 < P₀ := by rw [hP₀_def]; exact two_pi_div_log_two_bounds.1
  have hP₀_10 : P₀ < 10 := by rw [hP₀_def]; exact two_pi_div_log_two_bounds.2
  have hP₀_pos : 0 < P₀ := by linarith
  let N_per : ℕ := ⌊(V + 10) / P₀⌋₊ + 1
  have hcover : 2 * V + 5 ≤ (V - 5) + (N_per : ℝ) * P₀ := by
    dsimp [N_per]; push_cast
    have hlt := (Nat.lt_floor_add_one ((V + 10) / P₀)).le
    have := mul_le_mul_of_nonneg_right hlt hP₀_pos.le
    rw [div_mul_cancel₀ _ hP₀_pos.ne'] at this
    linarith
  have hNP_le : (N_per : ℝ) * P₀ ≤ 2 * V := by
    dsimp [N_per]; push_cast
    have hfl : (⌊(V + 10) / P₀⌋₊ : ℝ) ≤ (V + 10) / P₀ := Nat.floor_le (by positivity)
    calc ((⌊(V + 10) / P₀⌋₊ : ℝ) + 1) * P₀
        ≤ ((V + 10) / P₀ + 1) * P₀ := mul_le_mul_of_nonneg_right (by linarith) hP₀_pos.le
      _ = V + 10 + P₀ := by rw [add_mul, div_mul_cancel₀ _ hP₀_pos.ne', one_mul]
      _ ≤ 2 * V := by linarith
  let g : ℝ → ℝ := fun t => ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1‖
  have hg_cont : Continuous g := by
    have hdiff := RHTower.differentiable_edPoly (fejerDetectorCoeff θ A V)
      (s := Finset.Icc 1 ⌊V ^ θ⌋₊) (fun n hn => (Finset.mem_Icc.mp hn).1)
    exact continuous_norm.comp ((hdiff.continuous.comp (by fun_prop)).sub continuous_const)
  have hg_nn : ∀ t : ℝ, 0 ≤ g t := fun _ => norm_nonneg _
  have hsub_int : ∫ t in (V - 5)..(2 * V + 5), g t ≤
      ∫ t in (V - 5)..((V - 5) + (N_per : ℝ) * P₀), g t :=
    integral_subinterval_le_of_cont_nonneg hg_cont hg_nn le_rfl (by linarith) hcover
  have hsum_periods : ∀ K : ℕ,
      (∫ t in (V - 5)..((V - 5) + (K : ℝ) * P₀), g t) =
        ∑ k ∈ Finset.range K, ∫ t in ((V - 5) + (k : ℝ) * P₀)..((V - 5) + (k : ℝ) * P₀ + P₀), g t := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hsplit : (V - 5) + ((K + 1 : ℕ) : ℝ) * P₀ = (V - 5) + (K : ℝ) * P₀ + P₀ := by
        push_cast; ring
      rw [hsplit, ← intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable _ _) (hg_cont.intervalIntegrable _ _),
        ih, Finset.sum_range_succ]
  rw [hsum_periods N_per] at hsub_int
  have hper_ub : ∀ k ∈ Finset.range N_per,
      (∫ t in ((V - 5) + (k : ℝ) * P₀)..((V - 5) + (k : ℝ) * P₀ + P₀), g t) ≤
        (P₀ / (fejerHalfLen θ V : ℝ)) * Real.exp ((1 + θ) * A) := by
    intro k _
    rw [hP₀_def]
    exact (fejerDirichletDetector_period_and_sup_le hθ0 hA0 hVe hM1 hσ _).2
  have htot_ub : ∫ t in (V - 5)..(2 * V + 5), g t ≤
      ((N_per : ℝ) * P₀ / (fejerHalfLen θ V : ℝ)) * Real.exp ((1 + θ) * A) := by
    calc ∫ t in (V - 5)..(2 * V + 5), g t
        ≤ ∑ _k ∈ Finset.range N_per, (P₀ / (fejerHalfLen θ V : ℝ)) * Real.exp ((1 + θ) * A) :=
          hsub_int.trans (Finset.sum_le_sum hper_ub)
      _ = ((N_per : ℝ) * P₀ / (fejerHalfLen θ V : ℝ)) * Real.exp ((1 + θ) * A) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hM_pos : 0 < (fejerHalfLen θ V : ℝ) := by exact_mod_cast hM1
  have hrat_le : (N_per : ℝ) * P₀ / (fejerHalfLen θ V : ℝ) ≤ (8 / θ) * (V / Real.log V) := by
    calc (N_per : ℝ) * P₀ / (fejerHalfLen θ V : ℝ)
        ≤ (2 * V) / (θ * Real.log V / (4 * Real.log 2)) :=
          div_le_div₀ (by positivity) hNP_le (by positivity) hM_half
      _ = (8 * Real.log 2 / θ) * (V / Real.log V) := by field_simp; ring
      _ ≤ (8 * 1 / θ) * (V / Real.log V) := by gcongr
      _ = (8 / θ) * (V / Real.log V) := by ring
  calc ∫ t in (V - 5)..(2 * V + 5), g t
      ≤ ((N_per : ℝ) * P₀ / (fejerHalfLen θ V : ℝ)) * Real.exp ((1 + θ) * A) := htot_ub
    _ ≤ ((8 / θ) * (V / Real.log V)) * Real.exp ((1 + θ) * A) :=
        mul_le_mul_of_nonneg_right hrat_le (Real.exp_pos _).le
    _ = (8 * Real.exp ((1 + θ) * A) / θ) * (V / Real.log V) := by ring

/-- **Sharp `V / log V` impossibility across all `Lᵖ` (`1 ≤ p < ∞`):**
For every `p ≥ 1`, `0 < θ < 1`, and `A > 0`, `fejerDirichletDetector θ A V` has `Lᵖ` defect at
most `C(p, θ, A) · (V / log V)` uniformly across ALL `σ ≥ 1/2`. -/
theorem fejerDirichletDetector_Lp_defect_le_div_log
    {p θ A : ℝ} (hp1 : 1 ≤ p) (hθ0 : 0 < θ) (hA0 : 0 < A) :
    ∀ᶠ V : ℝ in atTop, ∀ σ : ℝ, 1 / 2 ≤ σ →
      (∫ t in (V - 5)..(2 * V + 5),
        ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ p) ≤
        (8 * Real.exp (p * (1 + θ) * A) / θ) * (V / Real.log V) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hV_M1 : ∀ᶠ V : ℝ in atTop, 2 * Real.log 2 / θ ≤ Real.log V :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (max 20 (Real.exp 1)), hV_M1,
    fejerDirichletDetector_L1_defect_le_div_log hθ0 hA0] with V hVmax hVM1 hL1 σ hσ
  have hV20 : 20 ≤ V := le_trans (le_max_left _ _) hVmax
  have hVe : Real.exp 1 ≤ V := le_trans (le_max_right _ _) hVmax
  have hM1 : 1 ≤ fejerHalfLen θ V := by
    unfold fejerHalfLen; refine Nat.le_floor ?_
    push_cast; rw [le_div_iff₀ (by positivity), one_mul]
    have := mul_le_mul_of_nonneg_left hVM1 hθ0.le
    rwa [mul_div_cancel₀ _ hθ0.ne'] at this
  have hsup := (fejerDirichletDetector_period_and_sup_le hθ0 hA0 hVe hM1 hσ 0).1
  let g : ℝ → ℝ := fun t => ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I) - 1‖
  have hg_cont : Continuous g := by
    have hdiff := RHTower.differentiable_edPoly (fejerDetectorCoeff θ A V)
      (s := Finset.Icc 1 ⌊V ^ θ⌋₊) (fun n hn => (Finset.mem_Icc.mp hn).1)
    exact continuous_norm.comp ((hdiff.continuous.comp (by fun_prop)).sub continuous_const)
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hpt : ∀ t : ℝ, g t ^ p ≤ Real.exp ((p - 1) * (1 + θ) * A) * g t := by
    intro t
    rcases eq_or_lt_of_le (show 0 ≤ g t from norm_nonneg _) with h0 | hpos
    · rw [← h0, Real.zero_rpow hp_pos.ne', mul_zero]
    · have hp_split : g t ^ p = g t ^ (p - 1) * g t := by
        rw [← Real.rpow_add_one (ne_of_gt hpos), sub_add_cancel]
      rw [hp_split]
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hpos)
      calc g t ^ (p - 1)
          ≤ (Real.exp ((1 + θ) * A)) ^ (p - 1) :=
            Real.rpow_le_rpow (le_of_lt hpos) (hsup t) (by linarith)
        _ = Real.exp ((p - 1) * (1 + θ) * A) := by
            rw [← Real.exp_mul]; congr 1; ring
  have hg_p_cont : Continuous (fun t => g t ^ p) :=
    hg_cont.rpow_const fun _ => Or.inr hp_pos.le
  have hmono : (∫ t in (V - 5)..(2 * V + 5), g t ^ p) ≤
      ∫ t in (V - 5)..(2 * V + 5), Real.exp ((p - 1) * (1 + θ) * A) * g t :=
    intervalIntegral.integral_mono_on (by linarith)
      (hg_p_cont.intervalIntegrable _ _)
      ((continuous_const.mul hg_cont).intervalIntegrable _ _)
      (fun t _ => hpt t)
  rw [intervalIntegral.integral_const_mul] at hmono
  calc (∫ t in (V - 5)..(2 * V + 5), g t ^ p)
      ≤ Real.exp ((p - 1) * (1 + θ) * A) * (∫ t in (V - 5)..(2 * V + 5), g t) := hmono
    _ ≤ Real.exp ((p - 1) * (1 + θ) * A) * ((8 * Real.exp ((1 + θ) * A) / θ) * (V / Real.log V)) :=
        mul_le_mul_of_nonneg_left (hL1 σ hσ) (Real.exp_pos _).le
    _ = (8 * (Real.exp ((p - 1) * (1 + θ) * A) * Real.exp ((1 + θ) * A)) / θ) * (V / Real.log V) := by
        ring
    _ = (8 * Real.exp (p * (1 + θ) * A) / θ) * (V / Real.log V) := by
        rw [← Real.exp_add]
        have hexp_eq : (p - 1) * (1 + θ) * A + (1 + θ) * A = p * (1 + θ) * A := by ring
        rw [hexp_eq]

/-- **Sharp `V / log V` impossibility for the positive logarithmic mean `log⁺‖F_V‖`:**
Uniformly for all `σ ≥ 1/2`, `∫_{V-5}^{2V+5} max(0, log‖F_V(σ + it)‖) dt ≪_{θ,A} V / log V`. -/
theorem fejerDirichletDetector_posLogMean_le_div_log
    {θ A : ℝ} (hθ0 : 0 < θ) (hA0 : 0 < A) :
    ∀ᶠ V : ℝ in atTop, ∀ σ : ℝ, 1 / 2 ≤ σ →
      (∫ t in (V - 5)..(2 * V + 5),
        max 0 (Real.log ‖fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I)‖)) ≤
        (8 * Real.exp ((1 + θ) * A) / θ) * (V / Real.log V) := by
  filter_upwards [eventually_ge_atTop (20 : ℝ),
    fejerDirichletDetector_L1_defect_le_div_log hθ0 hA0] with V hV20 hL1 σ hσ
  let F_line : ℝ → ℂ := fun t => fejerDirichletDetector θ A V ((σ : ℂ) + (t : ℂ) * I)
  have hF_cont : Continuous F_line :=
    (RHTower.differentiable_edPoly (fejerDetectorCoeff θ A V)
      (s := Finset.Icc 1 ⌊V ^ θ⌋₊) (fun n hn => (Finset.mem_Icc.mp hn).1)).continuous.comp
      (by fun_prop)
  have hlog_cont : Continuous (fun t => max 0 (Real.log ‖F_line t‖)) := by
    refine Continuous.congr (f := fun t => Real.log (max 1 ‖F_line t‖))
      (Real.continuous_log'.comp
        ((continuous_const.max (continuous_norm.comp hF_cont)).subtype_mk
          fun t => lt_of_lt_of_le zero_lt_one (le_max_left 1 _))) fun t => ?_
    rcases le_or_gt ‖F_line t‖ 1 with hle | hgt
    · rw [max_eq_left hle, Real.log_one]
      rcases eq_or_lt_of_le (norm_nonneg (F_line t)) with h0 | hpos
      · rw [← h0, Real.log_zero, max_self]
      · rw [max_eq_left (Real.log_nonpos hpos.le hle)]
    · rw [max_eq_right hgt.le, max_eq_right (Real.log_pos hgt).le]
  have hpt : ∀ t : ℝ, max 0 (Real.log ‖F_line t‖) ≤ ‖F_line t - 1‖ := by
    intro t
    refine max_le (norm_nonneg _) ?_
    rcases le_or_gt ‖F_line t‖ 1 with hle | hgt
    · rcases eq_or_lt_of_le (norm_nonneg (F_line t)) with h0 | hpos
      · rw [← h0, Real.log_zero]; exact norm_nonneg _
      · exact (Real.log_nonpos hpos.le hle).trans (norm_nonneg _)
    · have htri : ‖F_line t‖ ≤ 1 + ‖F_line t - 1‖ := by
        calc ‖F_line t‖ = ‖(1 : ℂ) + (F_line t - 1)‖ := by ring_nf
          _ ≤ ‖(1 : ℂ)‖ + ‖F_line t - 1‖ := norm_add_le _ _
          _ = 1 + ‖F_line t - 1‖ := by simp
      calc Real.log ‖F_line t‖
          ≤ Real.log (1 + ‖F_line t - 1‖) :=
            Real.log_le_log (lt_trans zero_lt_one hgt) htri
        _ ≤ (1 + ‖F_line t - 1‖) - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = ‖F_line t - 1‖ := by ring
  refine (intervalIntegral.integral_mono_on (by linarith : V - 5 ≤ 2 * V + 5)
    (hlog_cont.intervalIntegrable _ _)
    ((continuous_norm.comp (hF_cont.sub continuous_const)).intervalIntegrable _ _)
    fun t _ => hpt t).trans (hL1 σ hσ)

/-! ## §3. Log-free Barban–Vehov shifted `L²` defect at scale `V` -/

theorem norm_sub_one_sq (z : ℂ) : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 1 - 2 * (z - 1).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  ring

theorem integral_norm_zetaMollified_sub_one_sq_eq (c : ℕ → ℂ) (X : ℕ)
    {σ T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT12 : T₁ ≤ T₂) :
    (∫ t in T₁..T₂, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) =
      (∫ t in T₁..T₂, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
        (T₂ - T₁) -
        2 * (∫ t in T₁..T₂, (riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I) - 1)).re := by
  let Z : ℝ → ℂ := fun t => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
    RHTower.edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I)
  have hZ_cont : ContinuousOn Z (Icc T₁ T₂) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_iff_continuous_restrict.mpr ?_
      refine continuous_iff_continuousAt.mpr fun x => ?_
      have hne1 : ((σ : ℂ) + ((x : ℝ) : ℂ) * I) ≠ 1 := by
        intro h; have := congrArg Complex.im h; simp at this
        linarith [x.2.1]
      have hc_arg : Continuous (fun y : Icc T₁ T₂ => (σ : ℂ) + ((y : ℝ) : ℂ) * I) := by fun_prop
      exact ContinuousAt.comp (x := x) (differentiableAt_riemannZeta hne1).continuousAt hc_arg.continuousAt
    · exact (RHTower.differentiable_edPoly c (s := Finset.Icc 1 X)
        (fun n hn => (Finset.mem_Icc.mp hn).1)).continuous.comp_continuousOn (by fun_prop)
  have hZ2_int : IntervalIntegrable (fun t => ‖Z t‖ ^ 2) volume T₁ T₂ :=
    ((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hZ_cont)).intervalIntegrable_of_Icc hT12
  have hZsub_int : IntervalIntegrable (fun t => Z t - 1) volume T₁ T₂ :=
    (hZ_cont.sub continuousOn_const).intervalIntegrable_of_Icc hT12
  have hre_int : IntervalIntegrable (fun t => 2 * (Z t - 1).re) volume T₁ T₂ :=
    (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (hZ_cont.sub continuousOn_const))).intervalIntegrable_of_Icc hT12
  have h1_int : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume T₁ T₂ :=
    intervalIntegrable_const
  simp_rw [norm_sub_one_sq]
  change (∫ t in T₁..T₂, (‖Z t‖ ^ 2 - 1 - 2 * (Z t - 1).re)) = _
  rw [intervalIntegral.integral_sub (hZ2_int.sub h1_int) hre_int,
    intervalIntegral.integral_sub hZ2_int h1_int,
    intervalIntegral.integral_const, smul_eq_mul, mul_one,
    intervalIntegral.integral_const_mul]
  congr 2
  exact Complex.reCLM.intervalIntegral_comp_comm hZsub_int

/-- **Unconditional log-free Barban–Vehov shifted `L²` defect at scale `S` (`0 < r < 2 θ_Y < 2 θ_X < 1`).** -/
theorem exists_twoLength_defect_normSq_arbitrary_rate
    {θ_Y θ_X r : ℝ} (hθY : 0 < θ_Y) (hYX_exp : θ_Y < θ_X) (hθX : θ_X < 1 / 2)
    (hr0 : 0 < r) (hr : r < 2 * θ_Y) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1), ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        3 ≤ RHTower.VerticalAP.molLen θ_Y S ∧
        RHTower.VerticalAP.molLen θ_Y S < RHTower.VerticalAP.molLen θ_X S ∧
        (RHTower.VerticalAP.molLen θ_X S : ℝ) ≤ S ^ θ_X ∧
        ∀ σ₀ ∈ Set.Icc (1 / 2 : ℝ) 1,
          (∫ t in T₁..T₂,
            ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly
                (RHTower.twoLengthCoeff (RHTower.VerticalAP.molLen θ_X S)
                  (RHTower.VerticalAP.molLen θ_Y S))
                (Finset.Icc 1 (RHTower.VerticalAP.molLen θ_X S)) ((σ₀ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2) ≤
            (T₂ - T₁) * A₀ * Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S)) +
              240 * S ^ (θ_X + 1 / 2) := by
  obtain ⟨A₀, hA₀_pos, hev⟩ :=
    GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_twoLength_mollified_meanSquare_arbitrary_exponents
      hθY hYX_exp hθX hr0 hr
  have hθX_pos : 0 < θ_X := hθY.trans hYX_exp
  refine ⟨A₀, hA₀_pos, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (16 : ℝ)] with S hS hS16
  obtain ⟨T₁, hT₁, T₂, hT₂, hY3, hYX, hX_le, _, _, hmean⟩ := hS
  refine ⟨T₁, hT₁, T₂, hT₂, hY3, hYX, hX_le, fun σ₀ hσ₀ => ?_⟩
  let Y := RHTower.VerticalAP.molLen θ_Y S
  let X := RHTower.VerticalAP.molLen θ_X S
  have hY1 : 1 ≤ Y := by omega
  have hX1 : 1 ≤ X := by omega
  have hT_ge4 : 4 ≤ 2 * S / 3 := by linarith
  have hT₁_pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hid := integral_norm_zetaMollified_sub_one_sq_eq (RHTower.twoLengthCoeff X Y) X
    (σ := σ₀) hT₁_pos hT12
  have h1st := RHTower.norm_integral_zeta_mul_edPoly_sub_one_block_le hX1
    (RHTower.twoLengthCoeff_one hY1 hYX)
    (fun n hn => RHTower.norm_twoLengthCoeff_le hY1 hYX hn)
    hσ₀.1 (hσ₀.2.trans (by norm_num)) hT_ge4
    (le_of_lt hT₁.1) (le_of_lt hT₁.2) (by linarith [hT₂.1]) (by linarith [hT₂.2]) hT12
  have hre_ge : -(2 * (∫ t in T₁..T₂, (riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly (RHTower.twoLengthCoeff X Y) (Finset.Icc 1 X)
          ((σ₀ : ℂ) + (t : ℂ) * I) - 1)).re) ≤
      120 * S ^ (θ_X + 1 / 2) := by
    have habs : |(∫ t in T₁..T₂, (riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly (RHTower.twoLengthCoeff X Y) (Finset.Icc 1 X)
          ((σ₀ : ℂ) + (t : ℂ) * I) - 1)).re| ≤
        2 + (X : ℝ) * (45 * Real.sqrt (2 * S / 3) + 8) :=
      (Complex.abs_re_le_norm _).trans h1st
    have hsqrt_le : Real.sqrt (2 * S / 3) ≤ Real.sqrt S :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt_ge4 : 4 ≤ Real.sqrt S := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
      exact Real.sqrt_le_sqrt hS16
    have hS_pos : 0 < S := by linarith
    have hpow_split : S ^ θ_X * Real.sqrt S = S ^ (θ_X + 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hS_pos]
    have hpow_ge1 : 1 ≤ S ^ (θ_X + 1 / 2) :=
      Real.one_le_rpow (by linarith) (by linarith)
    have hX_prod : (X : ℝ) * (45 * Real.sqrt (2 * S / 3) + 8) ≤ 47 * S ^ (θ_X + 1 / 2) := by
      calc (X : ℝ) * (45 * Real.sqrt (2 * S / 3) + 8)
          ≤ S ^ θ_X * (45 * Real.sqrt S + 2 * Real.sqrt S) :=
            mul_le_mul hX_le (by linarith) (by positivity) (by positivity)
        _ = 47 * (S ^ θ_X * Real.sqrt S) := by ring
        _ = 47 * S ^ (θ_X + 1 / 2) := by rw [hpow_split]
    linarith [(abs_le.mp habs).1]
  have hm2 := hmean σ₀ hσ₀
  rw [hid]
  linarith

/-! ## §4. Universal subcritical mollifier defect floor and `V log V` disc-corridor divergence -/

/-- Universal asymptotic floor coefficient for `(1 / V) ∫_V^{2V} ‖ζΨ(1/2 + a / log V + it) - 1‖² dt`
across all normalized polynomial Dirichlet mollifiers of length `y ≤ V^θ` (`0 < θ < 1/2`):
strictly positive for every `θ ∈ (0, 1)` via `e^{-2a} log(1/θ)` and diverging as
`roughMollifierConst · e^{-2a} / θ - 1` when `θ → 0⁺`. -/
def subcriticalShiftedDefectFloor (θ a : ℝ) : ℝ :=
  max (Real.exp (-(2 * a)) * Real.log (1 / θ))
    (roughMollifierConst * Real.exp (-(2 * a)) / θ - 1)

theorem subcriticalShiftedDefectFloor_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (a : ℝ) :
    0 < subcriticalShiftedDefectFloor θ a := by
  unfold subcriticalShiftedDefectFloor
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  have h1lt : 1 < 1 / θ := (one_lt_div hθ0).mpr hθ1
  exact mul_pos (Real.exp_pos _) (Real.log_pos h1lt)

theorem sum_mollifiedZetaCoeff_rpow_mono_shift (b : ℕ → ℂ) (y M : ℕ)
    {a A L : ℝ} (haA : a ≤ A) (hL0 : 0 < L) :
    (∑ n ∈ Finset.Icc 1 M,
        ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + A / L))) ≤
      ∑ n ∈ Finset.Icc 1 M,
        ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hexp : -2 * (1 / 2 + A / L) ≤ -2 * (1 / 2 + a / L) := by
    have := div_le_div_of_nonneg_right haA hL0.le
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hexp) (sq_nonneg _)

/-- Uniform prime-log second-moment floor across the entire strip slice `a ∈ [0, A]`. -/
theorem eventually_uniform_primeLog_normSq_ge {A θ ε : ℝ}
    (hA0 : 0 ≤ A) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ a ∈ Icc 0 A, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ V ^ θ →
      ∀ b : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        (1 + Real.exp (-(2 * A)) * Real.log (1 / θ) - ε) * V ≤
          ∫ t in V..(2 * V),
            ‖riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly b (Finset.Icc 1 y)
                (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have ⟨δ, hδ_def⟩ : ∃ x : ℝ, x = min (1 / 2) (ε / 2) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; exact lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := by rw [hδ_def]; exact (min_le_left _ _).trans (by norm_num)
  have hδ_le_ε : δ ≤ ε / 2 := by rw [hδ_def]; exact min_le_right _ _
  have ⟨η, hη_def⟩ : ∃ x : ℝ, x = min ((1 - θ) / 2) (1 - Real.exp (-(δ / 4))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη_def]
    refine lt_min (by linarith) ?_
    have : Real.exp (-(δ / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hη_le1 : η ≤ (1 - θ) / 2 := by rw [hη_def]; exact min_le_left _ _
  have hη_le2 : η ≤ 1 - Real.exp (-(δ / 4)) := by rw [hη_def]; exact min_le_right _ _
  have ⟨θ₁, hθ₁_def⟩ : ∃ x : ℝ, x = 1 - η := ⟨_, rfl⟩
  have hθθ₁ : θ < θ₁ := by linarith
  have hθ₁0 : 0 < θ₁ := lt_trans hθ0 hθθ₁
  have hθ₁1 : θ₁ < 1 := by linarith
  have ⟨θ', hθ'_def⟩ : ∃ x : ℝ, x = θ₁ + (1 - θ₁) / 4 := ⟨_, rfl⟩
  have hθ'1 : θ' < 1 := by linarith
  have hθ'ge : Real.exp (-(δ / 4)) ≤ θ' := by linarith
  have hθ'pos : 0 < θ' := lt_of_lt_of_le (Real.exp_pos _) hθ'ge
  have hlog_θ' : Real.log (1 / θ) - δ / 4 ≤ Real.log (θ' / θ) := by
    have h1 : Real.exp (-(δ / 4)) / θ ≤ θ' / θ := div_le_div_of_nonneg_right hθ'ge hθ0.le
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (Real.exp_pos _).ne' hθ0.ne', Real.log_exp] at h2
    rw [one_div, Real.log_inv]
    linarith
  have ⟨D₀, hD₀_def⟩ : ∃ x : ℝ, x = 1 + Real.exp (-(2 * A)) * max 0 (Real.log (1 / θ) - δ / 2) :=
    ⟨_, rfl⟩
  have hD₀1 : 1 ≤ D₀ := by
    have : 0 ≤ Real.exp (-(2 * A)) * max 0 (Real.log (1 / θ) - δ / 2) := by positivity
    linarith
  have ⟨Cm, hCm_def⟩ : ∃ x : ℝ, x = 2 * RHTower.Sieve.mertensFirstConst + 1 / 2 := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm_def]; have := RHTower.Sieve.mertensFirstConst_nonneg; linarith
  have ⟨yStar, hyStar_def⟩ : ∃ n : ℕ, n = max 2 ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊ := ⟨_, rfl⟩
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - θ₁) / 2) (ε := δ / 600) (by norm_num) (by linarith) (by positivity)
  have ⟨S_yStar, hSy_def⟩ : ∃ x : ℝ, x = RHTower.Sieve.mertensS yStar +
      |RHTower.Sieve.meisselMertensConst| + Cm / Real.log 2 + Real.log (1 / θ) + 2 := ⟨_, rfl⟩
  have ⟨L₁, hL₁_def⟩ : ∃ x : ℝ, x = max (max (2 * A + 3) (32 / (1 - θ₁)))
      (max (128 / ((δ / D₀) * (1 - θ₁)))
        (max ((2 * Real.log 2 + Real.exp S_yStar) / θ') (32 * (Cm + 1) / (δ * θ')))) := ⟨_, rfl⟩
  filter_upwards [Real.tendsto_log_atTop.eventually ((eventually_ge_atTop L₁).and hsup),
    eventually_gt_atTop 1] with V hVL hV1
  obtain ⟨hLL₁, hsupL⟩ := hVL
  have hV0 : 0 < V := lt_trans zero_lt_one hV1
  have ⟨L, hL_def⟩ : ∃ x : ℝ, x = Real.log V := ⟨_, rfl⟩
  rw [← hL_def] at hLL₁ hsupL ⊢
  have hL₁_val : max (max (2 * A + 3) (32 / (1 - θ₁)))
      (max (128 / ((δ / D₀) * (1 - θ₁)))
        (max ((2 * Real.log 2 + Real.exp S_yStar) / θ') (32 * (Cm + 1) / (δ * θ')))) ≤ L := by
    rwa [← hL₁_def]
  have hLA : 2 * A + 3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL₁_val
  have hL32 : 32 / (1 - θ₁) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL₁_val
  have hLc : 128 / ((δ / D₀) * (1 - θ₁)) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₁_val
  have hLyS : (2 * Real.log 2 + Real.exp S_yStar) / θ' ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hL₁_val
  have hLCm : 32 * (Cm + 1) / (δ * θ') ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hL₁_val
  have hL0 : 0 < L := by linarith only [hA0, hLA]
  have hδ₁0 : 0 < 1 - θ₁ := by linarith only [hθ₁1]
  have hδL8 : 8 ≤ (1 - θ₁) / 4 * L := by
    have h1 := (div_le_iff₀ hδ₁0).mp hL32; linarith only [h1]
  have hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L := by
    have hcpos : 0 < δ / D₀ := div_pos hδ (by linarith only [hD₀1])
    have h1 := (div_le_iff₀ (mul_pos hcpos hδ₁0)).mp hLc
    rw [div_le_iff₀ hcpos]; nlinarith only [h1]
  have hsup' : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤
      δ / 6 := by linarith only [hsupL, hδ]
  intro a ha_mem y hy hyle b hb1 hb
  have ha0 : 0 ≤ a := ha_mem.1
  have haA : a ≤ A := ha_mem.2
  have hLa : 2 * a + 3 ≤ L := by linarith only [haA, hLA]
  have hyle_θ : (y : ℝ) ≤ Real.exp (θ * L) := by
    rw [mul_comm, Real.exp_mul, hL_def, Real.exp_log hV0]; exact hyle
  have hyle_θ₁ : (y : ℝ) ≤ Real.exp (θ₁ * L) :=
    hyle_θ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθθ₁.le hL0.le))
  have ⟨M, hM_def⟩ : ∃ n : ℕ, n = ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊ := ⟨_, rfl⟩
  have hM_def' : M = ⌊Real.exp (θ' * L)⌋₊ := by rw [hM_def, hθ'_def]
  have hMle : (M : ℝ) ≤ Real.exp (θ' * L) := by rw [hM_def']; exact Nat.floor_le (Real.exp_pos _).le
  have hMgt : Real.exp (θ' * L) - 1 < M := by
    rw [hM_def']; have h1 := Nat.lt_floor_add_one (Real.exp (θ' * L)); linarith only [h1]
  have hMle1 : (M : ℝ) ≤ Real.exp ((θ₁ + (1 - θ₁) / 4) * L) := by rwa [← hθ'_def]
  have hMgt1 : Real.exp ((θ₁ + (1 - θ₁) / 4) * L) - 1 < M := by rwa [← hθ'_def]
  obtain ⟨hM2, hyM, hMge, _, _⟩ :=
    RHTower.gaussFloor_scale hθ₁0 (div_pos hδ (by linarith only [hD₀1])) hL0 hδL8 hδLc hyle_θ₁
      hMle1 hMgt1
  have hMge' : Real.exp (θ' * L) / 2 ≤ (M : ℝ) := by rwa [hθ'_def]
  have hD_ge_A : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + A / L)) := by
    have ⟨fterm, hfterm_def⟩ : ∃ f : ℕ → ℝ, f = fun n =>
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + A / L)) := ⟨_, rfl⟩
    have hfterm_app : ∀ n, fterm n =
        ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + A / L)) := fun n => by
      rw [hfterm_def]
    simp_rw [← hfterm_app]
    have hfterm0 : ∀ n ∈ Finset.Icc 1 M, 0 ≤ fterm n := fun n _ => by
      rw [hfterm_app]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have h1val : fterm 1 = 1 := by
      rw [hfterm_app, RHTower.mollifiedZetaCoeff_one hy, hb1, norm_one]; simp
    by_cases hpos_target : Real.log (1 / θ) - δ / 2 ≤ 0
    · have hD₀_eq : D₀ = 1 := by rw [hD₀_def, max_eq_left hpos_target, mul_zero, add_zero]
      rw [hD₀_eq, ← h1val]
      exact Finset.single_le_sum hfterm0 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    · have hpos_t : 0 < Real.log (1 / θ) - δ / 2 := lt_of_not_ge hpos_target
      have hD₀_eq : D₀ = 1 + Real.exp (-(2 * A)) * (Real.log (1 / θ) - δ / 2) := by
        rw [hD₀_def, max_eq_right hpos_t.le]
      have ⟨Pset, hPset_def⟩ : ∃ s : Finset ℕ, s = (Finset.Ioc y M).filter Nat.Prime := ⟨_, rfl⟩
      have hsub_union : insert 1 Pset ⊆ Finset.Icc 1 M := by
        intro n hn
        rcases Finset.mem_insert.mp hn with rfl | hp
        · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
        · rw [hPset_def] at hp
          obtain ⟨hny, hnM⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
          exact Finset.mem_Icc.mpr ⟨by omega, hnM⟩
      have h1not : 1 ∉ Pset := by
        rw [hPset_def]; exact fun h => Nat.not_prime_one (Finset.mem_filter.mp h).2
      have hsum_ge : 1 + Real.exp (-(2 * A)) * (∑ p ∈ Pset, (1 / (p : ℝ))) ≤
          ∑ n ∈ Finset.Icc 1 M, fterm n := by
        have hp_le : ∀ p ∈ Pset, Real.exp (-(2 * A)) * (1 / (p : ℝ)) ≤ fterm p := by
          intro p hp
          rw [hfterm_app]; rw [hPset_def] at hp
          obtain ⟨hpIoc, hpp⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpy, hpM⟩ := Finset.mem_Ioc.mp hpIoc
          rw [RHTower.mollifiedZetaCoeff_prime hy hpp hpy, hb1, norm_one, one_pow, one_mul]
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hp_le_expL : (p : ℝ) ≤ Real.exp L :=
            (by exact_mod_cast hpM : (p : ℝ) ≤ M).trans
              (hMle.trans (Real.exp_le_exp.mpr (mul_le_of_le_one_left hL0.le hθ'1.le)))
          have hlogp : Real.log (p : ℝ) ≤ L := by
            have := Real.log_le_log hp0 hp_le_expL; rwa [Real.log_exp] at this
          rw [Real.rpow_def_of_pos hp0, one_div, ← Real.rpow_neg_one,
            Real.rpow_def_of_pos hp0, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hq : Real.log (p : ℝ) / L ≤ 1 := (div_le_one hL0).mpr hlogp
          have hexp_eq : Real.log (p : ℝ) * (-2 * (1 / 2 + A / L)) =
              -(2 * A * (Real.log (p : ℝ) / L)) + Real.log (p : ℝ) * (-1) := by
            have hLne : L ≠ 0 := hL0.ne'; field_simp [hLne]; ring
          nlinarith only [hA0, hq, hexp_eq]
        have hsum_le := Finset.sum_le_sum hp_le
        calc 1 + Real.exp (-(2 * A)) * (∑ p ∈ Pset, (1 / (p : ℝ)))
            = fterm 1 + ∑ p ∈ Pset, (Real.exp (-(2 * A)) * (1 / (p : ℝ))) := by
              rw [h1val, Finset.mul_sum]
          _ ≤ fterm 1 + ∑ p ∈ Pset, fterm p := by linarith only [hsum_le]
          _ = ∑ n ∈ insert 1 Pset, fterm n := (Finset.sum_insert h1not).symm
          _ ≤ ∑ n ∈ Finset.Icc 1 M, fterm n :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_union fun n hn _ => hfterm0 n hn
      have hlogM_ge : θ' * L - Real.log 2 ≤ Real.log (M : ℝ) := by
        have := Real.log_le_log (div_pos (Real.exp_pos _) zero_lt_two) hMge'
        rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
      have hθ'L_ge : 2 * Real.log 2 + Real.exp S_yStar ≤ θ' * L := by
        have h1 := (div_le_iff₀ hθ'pos).mp hLyS; linarith only [h1]
      have hlogM_half : θ' * L / 2 ≤ Real.log (M : ℝ) := by
        have hS0 : 1 ≤ Real.exp S_yStar := by
          have hs1 : 0 ≤ RHTower.Sieve.mertensS yStar :=
            Finset.sum_nonneg fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
          have hs2 : 0 ≤ |RHTower.Sieve.meisselMertensConst| := abs_nonneg _
          have hs3 : 0 ≤ Cm / Real.log 2 :=
            div_nonneg hCm0 (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
          have hlogθ : 0 < Real.log (1 / θ) := by
            rw [one_div, Real.log_inv]; exact neg_pos.mpr (Real.log_neg hθ0 hθ1)
          exact Real.one_le_exp (by linarith only [hs1, hs2, hs3, hlogθ, hSy_def])
        linarith only [hlogM_ge, hθ'L_ge, hS0]
      have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
      have hLCm_mul : 32 * (Cm + 1) ≤ δ * θ' * L := by
        have h1 := (div_le_iff₀ (mul_pos hδ hθ'pos)).mp hLCm; linarith only [h1]
      have hP_ge : Real.log (1 / θ) - δ / 2 ≤ ∑ p ∈ Pset, (1 / (p : ℝ)) := by
        rw [hPset_def, sum_Ioc_prime_inv_eq_mertensS_sub' hyM]
        have hM_mert := (abs_le.mp (RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le hM2)).1
        unfold RHTower.Sieve.logLog at hM_mert
        rw [← hCm_def] at hM_mert
        by_cases hyS : y ≤ yStar
        · have hmert_mono : RHTower.Sieve.mertensS y ≤ RHTower.Sieve.mertensS yStar := by
            unfold RHTower.Sieve.mertensS
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
            obtain ⟨hpy, hpp⟩ := Nat.mem_primesLE.mp hp
            exact Nat.mem_primesLE.mpr ⟨hpy.trans hyS, hpp⟩
          have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          have hlogM_exp : Real.exp S_yStar ≤ Real.log (M : ℝ) := by
            linarith only [hlogM_ge, hθ'L_ge, hlog2_pos]
          have hlogLogM : S_yStar ≤ Real.log (Real.log (M : ℝ)) := by
            have := Real.log_le_log (Real.exp_pos _) hlogM_exp; rwa [Real.log_exp] at this
          have hlog2_le : Real.log 2 ≤ Real.log (M : ℝ) :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hM2)
          have herrM : Cm / Real.log (M : ℝ) ≤ Cm / Real.log 2 :=
            div_le_div_of_nonneg_left hCm0 hlog2_pos hlog2_le
          have hMM := neg_abs_le RHTower.Sieve.meisselMertensConst
          linarith only [hM_mert, hmert_mono, hlogLogM, herrM, hMM, hSy_def, hδ]
        · have hyS' : yStar < y := lt_of_not_ge hyS
          have hy2 : 2 ≤ y := by
            have : 2 ≤ yStar := by rw [hyStar_def]; exact le_max_left _ _
            omega
          have hy_mert := (abs_le.mp (RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le hy2)).2
          unfold RHTower.Sieve.logLog at hy_mert
          rw [← hCm_def] at hy_mert
          have hy_ceil : ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊ < y := by
            have : ⌈Real.exp (16 * (Cm + 1) / δ)⌉₊ ≤ yStar := by
              rw [hyStar_def]; exact le_max_right _ _
            omega
          have hy_exp : Real.exp (16 * (Cm + 1) / δ) < (y : ℝ) :=
            lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hy_ceil)
          have hlogy_big : 16 * (Cm + 1) / δ ≤ Real.log (y : ℝ) := by
            have := Real.log_le_log (Real.exp_pos _) hy_exp.le; rwa [Real.log_exp] at this
          have hlogy_pos : 0 < Real.log (y : ℝ) := lt_of_lt_of_le (by positivity) hlogy_big
          have herry : Cm / Real.log (y : ℝ) ≤ δ / 16 := by
            rw [div_le_iff₀ hlogy_pos]
            have h1 := (div_le_iff₀ hδ).mp hlogy_big; linarith only [h1]
          have herrM : Cm / Real.log (M : ℝ) ≤ δ / 16 := by
            rw [div_le_iff₀ hlogM_pos]
            have h1 : δ * (θ' * L / 2) ≤ δ * Real.log (M : ℝ) :=
              mul_le_mul_of_nonneg_left hlogM_half hδ.le
            linarith only [hLCm_mul, h1, hδ]
          have hlogy_le : Real.log (y : ℝ) ≤ θ * L := by
            have := Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) hyle_θ
            rwa [Real.log_exp] at this
          have hlogM_ge_mul : (1 - δ / 16) * (θ' * L) ≤ Real.log (M : ℝ) := by
            have hlog2_le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
            nlinarith only [hlogM_ge, hlog2_le, hLCm_mul, hCm0]
          have h1sub_pos : 0 < 1 - δ / 16 := by linarith only [hδ1]
          have hquot : (1 - δ / 16) * (θ' / θ) ≤ Real.log (M : ℝ) / Real.log (y : ℝ) := by
            calc (1 - δ / 16) * (θ' / θ)
                = ((1 - δ / 16) * (θ' * L)) / (θ * L) := by field_simp
              _ ≤ Real.log (M : ℝ) / Real.log (y : ℝ) :=
                  div_le_div₀ (by positivity) hlogM_ge_mul hlogy_pos hlogy_le
          have hlog_quot : Real.log (1 - δ / 16) + Real.log (θ' / θ) ≤
              Real.log (Real.log (M : ℝ)) - Real.log (Real.log (y : ℝ)) := by
            rw [← Real.log_mul h1sub_pos.ne' (by positivity),
              ← Real.log_div hlogM_pos.ne' hlogy_pos.ne']
            exact Real.log_le_log (by positivity) hquot
          have hlog_1sub : -(δ / 8) ≤ Real.log (1 - δ / 16) := by
            have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (1 - δ / 16)⁻¹)
            rw [Real.log_inv] at h
            have hinv : (1 - δ / 16)⁻¹ - 1 ≤ δ / 8 := by
              rw [sub_le_iff_le_add, inv_eq_one_div, div_le_iff₀ h1sub_pos]
              nlinarith only [hδ, hδ1]
            linarith only [h, hinv]
          linarith only [hM_mert, hy_mert, herry, herrM, hlog_quot, hlog_1sub, hlog_θ', hδ]
      rw [hD₀_eq]
      have hmul_P := mul_le_mul_of_nonneg_left hP_ge (Real.exp_pos (-(2 * A))).le
      linarith only [hmul_P, hsum_ge]
  have hD_ge_a : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) :=
    hD_ge_A.trans (sum_mollifiedZetaCoeff_rpow_mono_shift b y M haA hL0)
  rw [hM_def] at hD_ge_a
  have hmain := gaussFloor_general_at_scale ha0 hθ₁0 hθ₁1 hD₀1 hδ hδ1 hLa hδL8 hδLc hsup' hy
    hyle_θ₁ hb hD_ge_a
  rw [hL_def, Real.exp_log hV0, ← hL_def] at hmain
  refine le_trans ?_ hmain
  refine mul_le_mul_of_nonneg_right ?_ hV0.le
  have hmax : Real.log (1 / θ) - δ / 2 ≤ max 0 (Real.log (1 / θ) - δ / 2) := le_max_right _ _
  have hexp_le1 : Real.exp (-(2 * A)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hA0])
  have h1 : Real.exp (-(2 * A)) * (Real.log (1 / θ) - δ / 2) ≤
      Real.exp (-(2 * A)) * max 0 (Real.log (1 / θ) - δ / 2) :=
    mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
  have h2 : Real.exp (-(2 * A)) * (δ / 2) ≤ δ / 2 := by
    have := mul_le_mul_of_nonneg_right hexp_le1 (by positivity : 0 ≤ δ / 2)
    linarith only [this]
  rw [mul_sub] at h1
  linarith only [hD₀_def, h1, h2, hδ, hδ_le_ε]

/-- Uniform `y`-rough `1/θ` second-moment floor across `a ∈ [0, A]`. -/
theorem eventually_uniform_rough_normSq_ge {A θ ε : ℝ}
    (hA0 : 0 ≤ A) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ a ∈ Icc 0 A, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ V ^ θ →
      ∀ b : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        (roughMollifierConst * Real.exp (-(2 * A)) / θ - ε) * V ≤
          ∫ t in V..(2 * V),
            ‖riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly b (Finset.Icc 1 y)
                (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have ⟨cr, hcr_def⟩ : ∃ x : ℝ, x = roughMollifierConst := ⟨_, rfl⟩
  rw [← hcr_def]
  have hcr0 : 0 < cr := by rw [hcr_def]; exact roughMollifierConst_pos
  have ⟨δ, hδ_def⟩ : ∃ x : ℝ, x = min (1 / 2) (ε / 2) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; exact lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := by rw [hδ_def]; exact (min_le_left _ _).trans (by norm_num)
  have hδ_le_ε : δ ≤ ε / 2 := by rw [hδ_def]; exact min_le_right _ _
  have ⟨η, hη_def⟩ : ∃ x : ℝ, x = min ((1 - θ) / 2) (δ * θ / (2 * cr + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη_def]; exact lt_min (by linarith) (by positivity)
  have hη_le1 : η ≤ (1 - θ) / 2 := by rw [hη_def]; exact min_le_left _ _
  have hη_le2 : η ≤ δ * θ / (2 * cr + 1) := by rw [hη_def]; exact min_le_right _ _
  have ⟨θ₁, hθ₁_def⟩ : ∃ x : ℝ, x = 1 - η := ⟨_, rfl⟩
  have hθθ₁ : θ < θ₁ := by linarith
  have hθ₁0 : 0 < θ₁ := lt_trans hθ0 hθθ₁
  have hθ₁1 : θ₁ < 1 := by linarith
  have ⟨θ', hθ'_def⟩ : ∃ x : ℝ, x = θ₁ + (1 - θ₁) / 4 := ⟨_, rfl⟩
  have hθ'1 : θ' < 1 := by linarith
  have hθ'pos : 0 < θ' := by linarith
  have ⟨D₀, hD₀_def⟩ : ∃ x : ℝ, x = max 1 (cr * Real.exp (-(2 * A)) * θ' / θ) := ⟨_, rfl⟩
  have hD₀1 : 1 ≤ D₀ := by rw [hD₀_def]; exact le_max_left _ _
  have hsup := RHTower.eventually_exp_mul_exp_neg_exp_le (k := 5) (C := 1 / 128)
    (δ := (1 - θ₁) / 2) (ε := δ / 600) (by norm_num) (by linarith) (by positivity)
  have ⟨L₁, hL₁_def⟩ : ∃ x : ℝ, x = max (max (2 * A + 3) (1 / θ))
      (max (32 / (1 - θ₁)) (128 / ((δ / D₀) * (1 - θ₁)))) := ⟨_, rfl⟩
  filter_upwards [Real.tendsto_log_atTop.eventually ((eventually_ge_atTop L₁).and hsup),
    eventually_gt_atTop 1] with V hVL hV1
  obtain ⟨hLL₁, hsupL⟩ := hVL
  have hV0 : 0 < V := lt_trans zero_lt_one hV1
  have ⟨L, hL_def⟩ : ∃ x : ℝ, x = Real.log V := ⟨_, rfl⟩
  rw [← hL_def] at hLL₁ hsupL ⊢
  have hL₁_val : max (max (2 * A + 3) (1 / θ))
      (max (32 / (1 - θ₁)) (128 / ((δ / D₀) * (1 - θ₁)))) ≤ L := by rwa [← hL₁_def]
  have hLA : 2 * A + 3 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL₁_val
  have hLθ : 1 / θ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL₁_val
  have hL32 : 32 / (1 - θ₁) ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₁_val
  have hLc : 128 / ((δ / D₀) * (1 - θ₁)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL₁_val
  have hL0 : 0 < L := by linarith
  have hδ₁0 : 0 < 1 - θ₁ := by linarith
  have hδL8 : 8 ≤ (1 - θ₁) / 4 * L := by
    have := (div_le_iff₀ hδ₁0).mp hL32; linarith
  have hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L := by
    have hcpos : 0 < δ / D₀ := by positivity
    have h1 := (div_le_iff₀ (mul_pos hcpos hδ₁0)).mp hLc
    rw [div_le_iff₀ hcpos]; nlinarith
  have hsup' : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤
      δ / 6 := by linarith
  intro a ha_mem y hy hyle b hb1 hb
  have ha0 : 0 ≤ a := ha_mem.1
  have haA : a ≤ A := ha_mem.2
  have hLa : 2 * a + 3 ≤ L := by linarith only [haA, hLA]
  have hyle_θ : (y : ℝ) ≤ Real.exp (θ * L) := by
    rw [mul_comm, Real.exp_mul, hL_def, Real.exp_log hV0]; exact hyle
  have hyle_θ₁ : (y : ℝ) ≤ Real.exp (θ₁ * L) :=
    hyle_θ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθθ₁.le hL0.le))
  have ⟨M, hM_def⟩ : ∃ n : ℕ, n = ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊ := ⟨_, rfl⟩
  have hM_def' : M = ⌊Real.exp (θ' * L)⌋₊ := by rw [hM_def, hθ'_def]
  have hMle : (M : ℝ) ≤ Real.exp (θ' * L) := by rw [hM_def']; exact Nat.floor_le (by positivity)
  have hMgt : Real.exp (θ' * L) - 1 < M := by
    rw [hM_def']; have := Nat.lt_floor_add_one (Real.exp (θ' * L)); linarith
  have hMle1 : (M : ℝ) ≤ Real.exp ((θ₁ + (1 - θ₁) / 4) * L) := by rwa [← hθ'_def]
  have hMgt1 : Real.exp ((θ₁ + (1 - θ₁) / 4) * L) - 1 < M := by rwa [← hθ'_def]
  obtain ⟨hM2, _, _, _, _⟩ :=
    RHTower.gaussFloor_scale hθ₁0 (by positivity : 0 < δ / D₀) hL0 hδL8 hδLc hyle_θ₁ hMle1 hMgt1
  have hD_ge_A : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + A / L)) := by
    have ⟨fterm, hfterm_def⟩ : ∃ f : ℕ → ℝ, f = fun n =>
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + A / L)) := ⟨_, rfl⟩
    have hfterm_app : ∀ n, fterm n =
        ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + A / L)) := fun n => by
      rw [hfterm_def]
    simp_rw [← hfterm_app]
    have hfterm0 : ∀ n ∈ Finset.Icc 1 M, 0 ≤ fterm n := fun n _ => by
      rw [hfterm_app]; positivity
    rw [hD₀_def]
    refine max_le ?_ ?_
    · have h1val : fterm 1 = 1 := by
        rw [hfterm_app, RHTower.mollifiedZetaCoeff_one hy, hb1, norm_one]; simp
      rw [← h1val]
      exact Finset.single_le_sum hfterm0 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    · have ⟨Rset, hRset_def⟩ : ∃ s : Finset ℕ, s = (Finset.Icc 1 M).image (roughPart y) := ⟨_, rfl⟩
      have hRsub : Rset ⊆ Finset.Icc 1 M := by
        intro v hv
        rw [hRset_def] at hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
        exact Finset.mem_Icc.mpr ⟨roughPart_pos y hm1, (roughPart_le y hm1).trans hmM⟩
      have hR_term : ∀ v ∈ Rset, Real.exp (-(2 * A)) * (1 / (v : ℝ)) ≤ fterm v := by
        intro v hv
        rw [hfterm_app]; rw [hRset_def] at hv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
        rw [mollifiedZetaCoeff_roughPart hy hb1 m, norm_one, one_pow, one_mul]
        have hv1 : 1 ≤ roughPart y m := roughPart_pos y hm1
        have hv0 : (0 : ℝ) < roughPart y m := by exact_mod_cast hv1
        have hv_expL : (roughPart y m : ℝ) ≤ Real.exp L :=
          (by exact_mod_cast (roughPart_le y hm1).trans hmM : (roughPart y m : ℝ) ≤ M).trans
            (hMle.trans (Real.exp_le_exp.mpr (by nlinarith only [hθ'1, hL0])))
        have hlogv : Real.log (roughPart y m : ℝ) ≤ L := by
          have := Real.log_le_log hv0 hv_expL; rwa [Real.log_exp] at this
        rw [Real.rpow_def_of_pos hv0, one_div, ← Real.rpow_neg_one,
          Real.rpow_def_of_pos hv0, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hq : Real.log (roughPart y m : ℝ) / L ≤ 1 := (div_le_one hL0).mpr hlogv
        have hexp_eq : Real.log (roughPart y m : ℝ) * (-2 * (1 / 2 + A / L)) =
            -(2 * A * (Real.log (roughPart y m : ℝ) / L)) + Real.log (roughPart y m : ℝ) * (-1) := by
          field_simp; ring
        have h2A : -(2 * A) ≤ -(2 * A * (Real.log (roughPart y m : ℝ) / L)) := by
          nlinarith only [hA0, hq]
        linarith only [hexp_eq, h2A]
      have hθL1 : 1 ≤ θ * L := by
        have := (div_le_iff₀ hθ0).mp hLθ; linarith
      have hlogy : Real.log (y : ℝ) ≤ θ * L := by
        have := Real.log_le_log (by exact_mod_cast hy) hyle_θ; rwa [Real.log_exp] at this
      have hmert_ub := exp_one_add_mertensS_le_inv_roughMollifierConst hy hθL1 hlogy
      rw [← hcr_def] at hmert_ub
      have hlogM1 : θ' * L ≤ Real.log ((M : ℝ) + 1) := by
        have h1 : Real.exp (θ' * L) ≤ (M : ℝ) + 1 := by linarith
        have := Real.log_le_log (Real.exp_pos _) h1; rwa [Real.log_exp] at this
      have hlogM1_nn : 0 ≤ Real.log ((M : ℝ) + 1) := by
        have : 0 ≤ θ' * L := by positivity
        linarith
      have hrough_ge : cr * θ' / θ ≤ ∑ v ∈ Rset, (1 / (v : ℝ)) := by
        rw [hRset_def]
        have hbase := sum_inv_image_roughPart_ge y M
        have hdiv : cr * θ' / θ ≤
            Real.log ((M : ℝ) + 1) / Real.exp (1 + RHTower.Sieve.mertensS y) := by
          have h1 : cr * θ' / θ = (θ' * L) / (θ * L / cr) := by field_simp
          rw [h1]
          exact div_le_div₀ hlogM1_nn hlogM1 (Real.exp_pos _) hmert_ub
        exact hdiv.trans hbase
      calc cr * Real.exp (-(2 * A)) * θ' / θ
          = Real.exp (-(2 * A)) * (cr * θ' / θ) := by ring
        _ ≤ Real.exp (-(2 * A)) * ∑ v ∈ Rset, (1 / (v : ℝ)) :=
            mul_le_mul_of_nonneg_left hrough_ge (Real.exp_pos _).le
        _ = ∑ v ∈ Rset, (Real.exp (-(2 * A)) * (1 / (v : ℝ))) := Finset.mul_sum _ _ _
        _ ≤ ∑ v ∈ Rset, fterm v := Finset.sum_le_sum hR_term
        _ ≤ ∑ n ∈ Finset.Icc 1 M, fterm n :=
            Finset.sum_le_sum_of_subset_of_nonneg hRsub fun n hn _ => hfterm0 n hn
  have hD_ge_a : D₀ ≤ ∑ n ∈ Finset.Icc 1 M,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) :=
    hD_ge_A.trans (sum_mollifiedZetaCoeff_rpow_mono_shift b y M haA hL0)
  rw [hM_def] at hD_ge_a
  have hmain := gaussFloor_general_at_scale ha0 hθ₁0 hθ₁1 hD₀1 hδ hδ1 hLa hδL8 hδLc hsup' hy
    hyle_θ₁ hb hD_ge_a
  rw [hL_def, Real.exp_log hV0, ← hL_def] at hmain
  refine le_trans ?_ hmain
  refine mul_le_mul_of_nonneg_right ?_ hV0.le
  have hexp_le1 : Real.exp (-(2 * A)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hloss : cr * Real.exp (-(2 * A)) * (1 - θ') / θ ≤ δ / 2 := by
    have h1θ' : 1 - θ' = 3 * η / 4 := by linarith
    rw [h1θ']
    have hexp_34 : Real.exp (-(2 * A)) * (3 * η / 4) ≤ η := by
      have := mul_le_mul_of_nonneg_right hexp_le1 (by positivity : 0 ≤ 3 * η / 4)
      linarith
    have h1 : cr * Real.exp (-(2 * A)) * (3 * η / 4) ≤ cr * η := by
      have := mul_le_mul_of_nonneg_left hexp_34 hcr0.le; linarith
    calc cr * Real.exp (-(2 * A)) * (3 * η / 4) / θ
        ≤ cr * η / θ := div_le_div_of_nonneg_right h1 hθ0.le
      _ ≤ cr * (δ * θ / (2 * cr + 1)) / θ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hη_le2 hcr0.le) hθ0.le
      _ = cr * δ / (2 * cr + 1) := by field_simp
      _ ≤ δ / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [hcr0, hδ]
  have hD₀_ge_main : cr * Real.exp (-(2 * A)) * θ' / θ ≤ D₀ := by
    rw [hD₀_def]; exact le_max_right _ _
  have hdecomp : cr * Real.exp (-(2 * A)) / θ - cr * Real.exp (-(2 * A)) * θ' / θ =
      cr * Real.exp (-(2 * A)) * (1 - θ') / θ := by ring
  linarith

/-- Uniform shifted `L²` defect floor across `a ∈ [0, A]` for all subcritical polynomial mollifiers
(`0 < θ < 1/2`). -/
theorem eventually_uniform_integral_normSq_zetaMollified_sub_one_ge
    {A θ ε : ℝ} (hA0 : 0 ≤ A) (hθ0 : 0 < θ) (hθ_half : θ < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ a ∈ Icc 0 A, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ V ^ θ →
      ∀ b : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        (subcriticalShiftedDefectFloor θ A - ε) * V ≤
          ∫ t in V..(2 * V),
            ‖riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly b (Finset.Icc 1 y)
                (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 := by
  have hθ1 : θ < 1 := by linarith
  have hexp_neg : θ + 1 / 2 - 1 < 0 := by linarith
  have hrpow0 : Tendsto (fun V : ℝ => V ^ (θ + 1 / 2 - 1)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith : 0 < -(θ + 1 / 2 - 1)) |>.congr fun V => by ring_nf
  have h1st_small : ∀ᶠ V : ℝ in atTop, 100 * V ^ (θ + 1 / 2 - 1) ≤ ε / 2 :=
    ((hrpow0.const_mul 100).eventually (eventually_le_nhds (by simpa using half_pos hε)))
  have hlogA : ∀ᶠ V : ℝ in atTop, 2 * A + 3 ≤ Real.log V :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * A + 3))
  filter_upwards [eventually_ge_atTop (16 : ℝ), hlogA, h1st_small,
    eventually_uniform_primeLog_normSq_ge hA0 hθ0 hθ1 (half_pos hε),
    eventually_uniform_rough_normSq_ge hA0 hθ0 hθ1 (half_pos hε)] with
    V hV16 hLA hsmall hprime hrough a ha_mem y hy hyle b hb1 hb
  have hV_pos : 0 < V := by linarith
  have hL_pos : 0 < Real.log V := by linarith
  have hσ_lo : 1 / 2 ≤ 1 / 2 + a / Real.log V := by
    have : 0 ≤ a / Real.log V := div_nonneg ha_mem.1 hL_pos.le; linarith
  have hσ_hi : 1 / 2 + a / Real.log V ≤ 2 := by
    have : a / Real.log V ≤ 1 := (div_le_one hL_pos).mpr (by linarith [ha_mem.2])
    linarith
  have hid := integral_norm_zetaMollified_sub_one_sq_eq b y
    (σ := 1 / 2 + a / Real.log V) hV_pos (by linarith : V ≤ 2 * V)
  have h1st := RHTower.norm_integral_zeta_mul_edPoly_sub_one_block_le hy hb1 hb
    hσ_lo hσ_hi (by linarith : 4 ≤ V) le_rfl (by linarith) (by linarith) le_rfl
    (by linarith : V ≤ 2 * V)
  have h1st_bound : 2 * |(∫ t in V..(2 * V),
      (riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly b (Finset.Icc 1 y)
          (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1)).re| ≤
      (ε / 2) * V := by
    have habs := (Complex.abs_re_le_norm _).trans h1st
    have hsqrt4 : 4 ≤ Real.sqrt V := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]; exact Real.sqrt_le_sqrt hV16
    have hy_prod : (y : ℝ) * (45 * Real.sqrt V + 8) ≤ 47 * V ^ (θ + 1 / 2) := by
      calc (y : ℝ) * (45 * Real.sqrt V + 8)
          ≤ V ^ θ * (45 * Real.sqrt V + 2 * Real.sqrt V) :=
            mul_le_mul hyle (by linarith) (by positivity) (by positivity)
        _ = 47 * (V ^ θ * V ^ (1 / 2 : ℝ)) := by rw [Real.sqrt_eq_rpow]; ring
        _ = 47 * V ^ (θ + 1 / 2) := by rw [← Real.rpow_add hV_pos]
    have hpow1 : 1 ≤ V ^ (θ + 1 / 2) := Real.one_le_rpow (by linarith) (by linarith)
    have h100 : 4 + 2 * ((y : ℝ) * (45 * Real.sqrt V + 8)) ≤ 100 * V ^ (θ + 1 / 2) := by
      linarith
    have hmul_V : 100 * V ^ (θ + 1 / 2) ≤ (ε / 2) * V := by
      have := mul_le_mul_of_nonneg_right hsmall hV_pos.le
      have hrew : V ^ (θ + 1 / 2 - 1) * V = V ^ (θ + 1 / 2) := by
        rw [← Real.rpow_add_one hV_pos.ne', sub_add_cancel]
      linarith
    linarith
  have hre_le := le_abs_self (∫ t in V..(2 * V),
    (riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
      RHTower.edPoly b (Finset.Icc 1 y)
        (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1)).re
  have hp := hprime a ha_mem y hy hyle b hb1 hb
  have hr := hrough a ha_mem y hy hyle b hb1 hb
  rw [hid]
  unfold subcriticalShiftedDefectFloor
  rcases max_cases (Real.exp (-(2 * A)) * Real.log (1 / θ))
      (roughMollifierConst * Real.exp (-(2 * A)) / θ - 1) with ⟨hmax, _⟩ | ⟨hmax, _⟩
  · rw [hmax]; linarith
  · rw [hmax]; linarith

/-- **Universal subcritical mollifier shifted `L²` defect floor (`0 < θ < 1/2`, all `a ≥ 0`).** -/
theorem eventually_integral_normSq_zetaMollified_sub_one_ge
    {a θ ε : ℝ} (ha : 0 ≤ a) (hθ0 : 0 < θ) (hθ_half : θ < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ V ^ θ →
      ∀ b : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        (subcriticalShiftedDefectFloor θ a - ε) * V ≤
          ∫ t in V..(2 * V),
            ‖riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
              RHTower.edPoly b (Finset.Icc 1 y)
                (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 := by
  filter_upwards [eventually_uniform_integral_normSq_zetaMollified_sub_one_ge
    ha hθ0 hθ_half hε] with V hV y hy hyle b hb1 hb
  exact hV a ⟨ha, le_rfl⟩ y hy hyle b hb1 hb

/-- **`V log V` disc-corridor divergence for every subcritical polynomial mollifier (`0 < θ < 1/2`).**
Integrating `‖ζ(z) Ψ(z) - 1‖²` over the corridor `[1/2 + A / (2 log V), 1/2 + A / log V] ×ℂ [V, 2V]`
and dividing by the disc area `π (A / (2 log V))²` yields a lower bound of order `V log V`. -/
theorem eventually_discCorridorBound_zetaMollified_ge_mul_log
    {A θ : ℝ} (hA0 : 0 < A) (hθ0 : 0 < θ) (hθ_half : θ < 1 / 2) :
    ∀ᶠ V : ℝ in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ V ^ θ →
      ∀ b : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        (subcriticalShiftedDefectFloor θ A / (2 * Real.pi * A)) * V * Real.log V ≤
          (∫ z in Icc (1 / 2 + A / (2 * Real.log V)) (1 / 2 + A / Real.log V) ×ℂ Icc V (2 * V),
            ‖riemannZeta z * RHTower.edPoly b (Finset.Icc 1 y) z - 1‖ ^ 2) /
            (Real.pi * (A / (2 * Real.log V)) ^ 2) := by
  have hθ1 : θ < 1 := by linarith
  have hfloor_pos : 0 < subcriticalShiftedDefectFloor θ A :=
    subcriticalShiftedDefectFloor_pos hθ0 hθ1 A
  have hε_pos : 0 < (3 / 4 : ℝ) * subcriticalShiftedDefectFloor θ A := by positivity
  filter_upwards [eventually_ge_atTop (Real.exp 2),
    eventually_uniform_integral_normSq_zetaMollified_sub_one_ge hA0.le hθ0 hθ_half hε_pos] with
    V hVe2 hV_unif y hy hyle b hb1 hb
  have hV_pos : 0 < V := lt_of_lt_of_le (Real.exp_pos 2) hVe2
  have hL_ge2 : 2 ≤ Real.log V := by
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log V := Real.log_le_log (Real.exp_pos 2) hVe2
  have hL_pos : 0 < Real.log V := by linarith
  let σ₁ : ℝ := 1 / 2 + A / (2 * Real.log V)
  let σ₂ : ℝ := 1 / 2 + A / Real.log V
  have hσ12 : σ₁ ≤ σ₂ := by
    dsimp [σ₁, σ₂]
    have : A / (2 * Real.log V) ≤ A / Real.log V := by
      rw [div_le_div_iff₀ (by positivity) hL_pos]; nlinarith
    linarith
  let g : ℂ → ℝ := fun z => ‖riemannZeta z * RHTower.edPoly b (Finset.Icc 1 y) z - 1‖ ^ 2
  have hg_cont : ContinuousOn g (Icc σ₁ σ₂ ×ℂ Icc V (2 * V)) := by
    have hZ_cont : ContinuousOn (fun z : ℂ => riemannZeta z * RHTower.edPoly b (Finset.Icc 1 y) z)
        (Icc σ₁ σ₂ ×ℂ Icc V (2 * V)) := by
      refine ContinuousOn.mul ?_ ?_
      · refine continuousOn_iff_continuous_restrict.mpr (continuous_iff_continuousAt.mpr fun z => ?_)
        have hne1 : (z : ℂ) ≠ 1 := by
          intro h; have := congrArg Complex.im h; simp at this
          linarith [z.2.2.1]
        exact (differentiableAt_riemannZeta hne1).continuousAt.comp continuousAt_subtype_val
      · exact (RHTower.differentiable_edPoly b (s := Finset.Icc 1 y)
          (fun n hn => (Finset.mem_Icc.mp hn).1)).continuous.continuousOn
    exact (continuous_pow 2).comp_continuousOn
      (continuous_norm.comp_continuousOn (hZ_cont.sub continuousOn_const))
  have hiter := setIntegral_reProdIm_eq_iterated_of_continuousOn hσ12 (by linarith : V ≤ 2 * V) hg_cont
  have hslice_int : IntervalIntegrable
      (fun σ : ℝ => ∫ t in V..(2 * V), g ((σ : ℂ) + (t : ℂ) * I)) volume σ₁ σ₂ := by
    let f₀ : C(Icc σ₁ σ₂ ×ℂ Icc V (2 * V), ℝ) := ⟨fun z => g z, hg_cont.restrict⟩
    have hK_closed := isClosed_reProdIm_Icc σ₁ σ₂ V (2 * V)
    obtain ⟨F_ext, hF_ext⟩ := f₀.exists_restrict_eq hK_closed
    have heq : ∀ z ∈ Icc σ₁ σ₂ ×ℂ Icc V (2 * V), F_ext z = g z := fun z hz =>
      congrArg (fun H : C(Icc σ₁ σ₂ ×ℂ Icc V (2 * V), ℝ) => H ⟨z, hz⟩) hF_ext
    have hcont_p : Continuous (fun σ : ℝ =>
        ∫ t in V..(2 * V), F_ext ((σ : ℂ) + (t : ℂ) * I)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (by fun_prop : Continuous fun p : ℝ × ℝ => F_ext ((p.1 : ℂ) + (p.2 : ℂ) * I)) V (2 * V)
    refine (hcont_p.intervalIntegrable _ _).congr fun σ hσ => ?_
    rw [Set.uIoc_of_le hσ12] at hσ
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith : V ≤ 2 * V)] at ht
    apply heq
    simp [Complex.mem_reProdIm, le_of_lt hσ.1, hσ.2, ht.1, ht.2]
  have hslice_lb : ∀ σ ∈ Icc σ₁ σ₂,
      ((1 / 4 : ℝ) * subcriticalShiftedDefectFloor θ A * V) ≤
        ∫ t in V..(2 * V), g ((σ : ℂ) + (t : ℂ) * I) := by
    intro σ hσ
    let a : ℝ := (σ - 1 / 2) * Real.log V
    have ha_mem : a ∈ Icc 0 A := by
      dsimp [a, σ₁, σ₂] at hσ ⊢
      constructor
      · have h1 : A / (2 * Real.log V) ≤ σ - 1 / 2 := by linarith [hσ.1]
        have : 0 ≤ A / (2 * Real.log V) := by positivity
        exact mul_nonneg (by linarith) hL_pos.le
      · have h2 : σ - 1 / 2 ≤ A / Real.log V := by linarith [hσ.2]
        have := mul_le_mul_of_nonneg_right h2 hL_pos.le
        rwa [div_mul_cancel₀ _ hL_pos.ne'] at this
    have hσ_eq : 1 / 2 + a / Real.log V = σ := by
      dsimp [a]; rw [mul_div_cancel_right₀ _ hL_pos.ne']; ring
    have hlb := hV_unif a ha_mem y hy hyle b hb1 hb
    rw [hσ_eq] at hlb
    linarith
  have h2D_lb : (A / (2 * Real.log V)) * ((1 / 4 : ℝ) * subcriticalShiftedDefectFloor θ A * V) ≤
      ∫ z in Icc σ₁ σ₂ ×ℂ Icc V (2 * V), g z := by
    rw [hiter]
    have hmono := intervalIntegral.integral_mono_on hσ12
      intervalIntegrable_const hslice_int hslice_lb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hwidth : σ₂ - σ₁ = A / (2 * Real.log V) := by dsimp [σ₁, σ₂]; ring
    rw [hwidth] at hmono
    exact hmono
  have harea_pos : 0 < Real.pi * (A / (2 * Real.log V)) ^ 2 := by positivity
  rw [le_div_iff₀ harea_pos]
  refine le_trans (le_of_eq ?_) h2D_lb
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hA_ne : A ≠ 0 := hA0.ne'
  have hL_ne : Real.log V ≠ 0 := hL_pos.ne'
  field_simp
  ring

/-! ## §5. Sharpness of Gallagher's discrete Dirichlet large-values `log N` factor -/

/-- **Sharpness of the `log N` factor in Gallagher's discrete separated mean-value theorem:**
For every `N ≥ 4` and `V ≥ 40`, there exist `> 9`-separated ordinates `λ_0 < ⋯ < λ_R` in `[V, 2V]`
and nonzero coefficients `a : Fin N → ℂ` achieving
`∑_r ‖dirPoly N a (λ_r)‖² ≥ (1/40) V (log N) ∑_m ‖a_m‖²`. -/
theorem exists_separated_dirPoly_sum_normSq_ge_mul_log
    {N : ℕ} (hN4 : 4 ≤ N) {V : ℝ} (hV40 : 40 ≤ V) :
    ∃ (R : ℕ) (lam : Fin (R + 1) → ℝ) (a : Fin N → ℂ),
      (∀ r : Fin (R + 1), V ≤ lam r ∧ lam r ≤ 2 * V) ∧
      (∀ r₁ r₂ : Fin (R + 1), r₁ < r₂ → 9 < lam r₂ - lam r₁) ∧
      (0 < ∑ m : Fin N, ‖a m‖ ^ 2) ∧
      (1 / 40 : ℝ) * V * Real.log (N : ℝ) * (∑ m : Fin N, ‖a m‖ ^ 2) ≤
        ∑ r : Fin (R + 1), ‖RHTower.Sieve.dirPoly N a (lam r)‖ ^ 2 := by
  classical
  have ⟨P₀, hP₀_def⟩ : ∃ x : ℝ, x = 2 * Real.pi / Real.log 2 := ⟨_, rfl⟩
  have hP₀_9 : 9 < P₀ := by rw [hP₀_def]; exact two_pi_div_log_two_bounds.1
  have hP₀_10 : P₀ < 10 := by rw [hP₀_def]; exact two_pi_div_log_two_bounds.2
  have hP₀_pos : 0 < P₀ := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  let K : ℕ := Nat.log 2 N + 1
  have hK_ge1 : 1 ≤ K := by dsimp [K]; omega
  have hj_lt_N : ∀ j : Fin K, 2 ^ j.val - 1 < N := by
    intro j
    have hj_le : j.val ≤ Nat.log 2 N := by dsimp [K] at j; omega
    have hpow_le : 2 ^ j.val ≤ N :=
      (Nat.pow_le_pow_right (by norm_num) hj_le).trans (Nat.pow_log_le_self 2 (by omega))
    have hpow_pos : 1 ≤ 2 ^ j.val := Nat.one_le_two_pow
    omega
  let idx : Fin K → Fin N := fun j => ⟨2 ^ j.val - 1, hj_lt_N j⟩
  have hidx_inj : Function.Injective idx := by
    intro j₁ j₂ heq
    have hval : 2 ^ j₁.val - 1 = 2 ^ j₂.val - 1 := congrArg Fin.val heq
    have hpow1 : 1 ≤ 2 ^ j₁.val := Nat.one_le_two_pow
    have hpow2 : 1 ≤ 2 ^ j₂.val := Nat.one_le_two_pow
    have hpow_eq : 2 ^ j₁.val = 2 ^ j₂.val := by omega
    exact Fin.ext (Nat.pow_right_injective (by norm_num) hpow_eq)
  let S_idx : Finset (Fin N) := Finset.univ.image idx
  let a : Fin N → ℂ := fun m => if m ∈ S_idx then 1 else 0
  have ha_l2 : (∑ m : Fin N, ‖a m‖ ^ 2) = (K : ℝ) := by
    have hterm : ∀ m : Fin N, ‖a m‖ ^ 2 = if m ∈ S_idx then (1 : ℝ) else 0 := by
      intro m; dsimp [a]; split_ifs <;> simp
    simp_rw [hterm]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_image_of_injective _ hidx_inj, Finset.card_fin]
  have ha_pos : 0 < ∑ m : Fin N, ‖a m‖ ^ 2 := by
    rw [ha_l2]; exact_mod_cast hK_ge1
  let Q : ℕ := ⌊V / P₀⌋₊
  have hQ_ge4 : 4 ≤ Q := by
    dsimp [Q]; refine Nat.le_floor ?_
    push_cast; rw [le_div_iff₀ hP₀_pos]; linarith
  let R : ℕ := Q - 1
  have hR1_eq_Q : R + 1 = Q := by dsimp [R]; omega
  let k₀ : ℕ := ⌈V / P₀⌉₊
  let lam : Fin (R + 1) → ℝ := fun r => ((k₀ + r.val : ℕ) : ℝ) * P₀
  refine ⟨R, lam, a, ?_, ?_, ha_pos, ?_⟩
  · intro r
    have hk₀_lo : V / P₀ ≤ (k₀ : ℝ) := Nat.le_ceil _
    have hk₀_hi : (k₀ : ℝ) < V / P₀ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hr_hi : (r.val : ℝ) + 1 ≤ V / P₀ := by
      have hrQ : (r.val : ℝ) + 1 ≤ (Q : ℝ) := by exact_mod_cast (by omega : r.val + 1 ≤ Q)
      exact hrQ.trans (Nat.floor_le (by positivity))
    constructor
    · calc V = (V / P₀) * P₀ := (div_mul_cancel₀ _ hP₀_pos.ne').symm
        _ ≤ ((k₀ : ℝ) + (r.val : ℝ)) * P₀ :=
            mul_le_mul_of_nonneg_right
              (by linarith [(Nat.cast_nonneg r.val : (0 : ℝ) ≤ r.val)]) hP₀_pos.le
        _ = lam r := by dsimp [lam]; push_cast; rfl
    · have hlt : lam r < 2 * V := by
        calc lam r = ((k₀ : ℝ) + (r.val : ℝ)) * P₀ := by dsimp [lam]; push_cast; rfl
          _ < ((V / P₀ + 1) + (V / P₀ - 1)) * P₀ :=
              mul_lt_mul_of_pos_right (by linarith) hP₀_pos
          _ = 2 * V := by field_simp; ring
      exact hlt.le
  · intro r₁ r₂ hlt
    have hr12 : (r₁.val : ℝ) + 1 ≤ (r₂.val : ℝ) := by exact_mod_cast hlt
    have hdiff : P₀ ≤ lam r₂ - lam r₁ := by
      dsimp [lam]; push_cast
      have : 1 * P₀ ≤ (((k₀ : ℝ) + (r₂.val : ℝ)) - ((k₀ : ℝ) + (r₁.val : ℝ))) * P₀ :=
        mul_le_mul_of_nonneg_right (by linarith) hP₀_pos.le
      linarith
    linarith
  · have hval_at : ∀ r : Fin (R + 1), RHTower.Sieve.dirPoly N a (lam r) = (K : ℂ) := by
      intro r
      unfold RHTower.Sieve.dirPoly
      have hite : ∀ m : Fin N,
          a m * Complex.exp (((lam r * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * I) =
            if m ∈ S_idx then Complex.exp (((lam r * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * I) else 0 := by
        intro m; dsimp [a]; split_ifs <;> simp
      simp_rw [hite, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      dsimp [S_idx]
      rw [Finset.sum_image fun j₁ _ j₂ _ h => hidx_inj h]
      have hterm1 : ∀ j : Fin K,
          Complex.exp (((lam r * Real.log (((idx j : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I) = 1 := by
        intro j
        have hpow_pos : 1 ≤ 2 ^ j.val := Nat.one_le_two_pow
        have hcast_idx : ((idx j : ℕ) : ℝ) + 1 = (2 : ℝ) ^ j.val := by
          dsimp [idx]
          have : (2 ^ j.val - 1) + 1 = 2 ^ j.val := by omega
          exact_mod_cast this
        rw [hcast_idx, Real.log_pow]
        have harg : ((lam r * ((j.val : ℝ) * Real.log 2) : ℝ) : ℂ) * I =
            (((k₀ + r.val) * j.val : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
          dsimp [lam]; rw [hP₀_def]
          have hne : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2_pos.ne'
          push_cast; field_simp
        rw [harg, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
      simp_rw [hterm1, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    have hsum_lam : (∑ r : Fin (R + 1), ‖RHTower.Sieve.dirPoly N a (lam r)‖ ^ 2) =
        (Q : ℝ) * (K : ℝ) ^ 2 := by
      simp_rw [hval_at, Complex.norm_natCast, Finset.sum_const, Finset.card_fin,
        hR1_eq_Q, nsmul_eq_mul]
    rw [hsum_lam, ha_l2]
    have hQ_lb : (3 / 40 : ℝ) * V ≤ (Q : ℝ) := by
      have hlt := Nat.lt_floor_add_one (V / P₀)
      have hdiv : V / 10 ≤ V / P₀ := div_le_div_of_nonneg_left (by linarith) hP₀_pos hP₀_10.le
      dsimp [Q]; linarith
    have hK_lb : Real.log (N : ℝ) ≤ (K : ℝ) := by
      have hN_lt : N < 2 ^ K := by
        dsimp [K]; exact Nat.lt_pow_succ_log_self (by norm_num) N
      have hN_lt_real : (N : ℝ) < (2 : ℝ) ^ K := by exact_mod_cast hN_lt
      have hlog_lt := Real.log_lt_log (by exact_mod_cast (by omega : 0 < N)) hN_lt_real
      rw [Real.log_pow] at hlog_lt
      have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_ge1
      nlinarith
    have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hprod_lb : (1 / 40 : ℝ) * V * Real.log (N : ℝ) ≤ (Q : ℝ) * (K : ℝ) := by
      calc (1 / 40 : ℝ) * V * Real.log (N : ℝ)
          ≤ (3 / 40 : ℝ) * V * Real.log (N : ℝ) := by nlinarith
        _ ≤ (Q : ℝ) * (K : ℝ) := mul_le_mul hQ_lb hK_lb hlogN_nn (Nat.cast_nonneg Q)
    calc (1 / 40 : ℝ) * V * Real.log (N : ℝ) * (K : ℝ)
        ≤ ((Q : ℝ) * (K : ℝ)) * (K : ℝ) :=
          mul_le_mul_of_nonneg_right hprod_lb (Nat.cast_nonneg K)
      _ = (Q : ℝ) * (K : ℝ) ^ 2 := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_le_of_shiftedDefect_div_log
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logFreeNearLineWindowOccupancy_of_shiftedDefect_div_log
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.fejerDirichletDetector_occupiedWindows_ge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.fejerDirichletDetector_Lp_defect_le_div_log
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.fejerDirichletDetector_posLogMean_le_div_log
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_twoLength_defect_normSq_arbitrary_rate
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_integral_normSq_zetaMollified_sub_one_ge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_discCorridorBound_zetaMollified_ge_mul_log
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_separated_dirPoly_sum_normSq_ge_mul_log
