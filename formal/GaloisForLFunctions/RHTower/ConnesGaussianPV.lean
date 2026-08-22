import GaloisForLFunctions.RHTower.ConnesGaussianIdLogMoment
import GaloisForLFunctions.RHTower.ConnesArchPrincipalValue
import GaloisForLFunctions.RHTower.ConnesSchwartzLogDecay
import GaloisForLFunctions.HTGeometry.GaussianSchwartz

/-!
# The regularized principal value of the Gaussian

The constant of the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

is fixed by evaluating Connes' logarithmically regularized principal value on the self-dual
Gaussian.  One integration by parts against the primitive `e^{-πx²} log x` turns the divergent
`∫_ε^∞ e^{-πx²} dx/x` into `−e^{-πε²} log ε + 2π ∫_ε^∞ x e^{-πx²} log x dx`, and the log
divergences cancel exactly, leaving `−γ/2 − (log π)/2`.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_gauss_log_atTop :
    Tendsto (fun x : ℝ => GaloisForLFunctions.gaussReal x * Real.log x) atTop (𝓝 0) := by
  have h := connes_schwartz_mul_log_atTop GaloisForLFunctions.gaussianSchwartz
  have h2 := (Complex.continuous_re.tendsto (0 : ℂ)).comp h
  rw [Complex.zero_re] at h2
  refine h2.congr fun x => ?_
  show ((GaloisForLFunctions.gaussianSchwartz : ℝ → ℂ) x * ((Real.log x : ℝ) : ℂ)).re
      = GaloisForLFunctions.gaussReal x * Real.log x
  rw [GaloisForLFunctions.gaussianSchwartz_apply, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem connes_gauss_log_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => GaloisForLFunctions.gaussReal y * Real.log y)
      (-(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x
        + GaloisForLFunctions.gaussReal x / x) x := by
  have h1 := GaloisForLFunctions.hasDerivAt_gaussReal x
  have h2 := Real.hasDerivAt_log (ne_of_gt hx)
  have h := h1.mul h2
  refine h.congr_deriv ?_
  field_simp

theorem connes_gauss_deriv_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x
      + GaloisForLFunctions.gaussReal x / x) (Ioi ε) volume := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 : IntegrableOn (fun x : ℝ =>
      -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x) (Ioi ε) volume := by
    have h0 := connes_integrableOn_pow_log_mul_gaussian hπ 1
    have h0' : IntegrableOn (fun x : ℝ =>
        -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x) (Ioi (0:ℝ)) volume := by
      have := h0.const_mul (-(2 * π))
      refine this.congr ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
      show -(2 * π) * (x ^ 1 * (Real.log x * Real.exp (-π * x ^ 2)))
          = -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x
      show -(2 * π) * (x ^ 1 * (Real.log x * Real.exp (-π * x ^ 2)))
          = -(2 * π * x) * Real.exp (-(π * x ^ 2)) * Real.log x
      have : Real.exp (-π * x ^ 2) = Real.exp (-(π * x ^ 2)) := by ring_nf
      rw [this]
      ring
    exact h0'.mono_set (Ioi_subset_Ioi hε.le)
  have h2 : IntegrableOn (fun x : ℝ => GaloisForLFunctions.gaussReal x / x) (Ioi ε) volume := by
    have hg : IntegrableOn (fun x : ℝ => ε⁻¹ * GaloisForLFunctions.gaussReal x) (Ioi ε) volume :=
      (GaloisForLFunctions.gaussianSchwartzReal.integrable (μ := volume)).integrableOn.const_mul ε⁻¹
    refine Integrable.mono' hg ?_ ?_
    · have hmeas : Measurable (fun x : ℝ => GaloisForLFunctions.gaussReal x / x) := by
        unfold GaloisForLFunctions.gaussReal
        fun_prop
      exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := ε))] with x hx
      have hx0 : ε < x := hx
      have hxpos : (0:ℝ) < x := lt_trans hε hx0
      rw [Real.norm_of_nonneg
        (div_nonneg (GaloisForLFunctions.gaussReal_pos x).le hxpos.le)]
      calc GaloisForLFunctions.gaussReal x / x
          ≤ GaloisForLFunctions.gaussReal x / ε :=
            div_le_div_of_nonneg_left (GaloisForLFunctions.gaussReal_pos x).le hε hx0.le
        _ = ε⁻¹ * GaloisForLFunctions.gaussReal x := by rw [div_eq_inv_mul]
  exact h1.add h2

/-- **The integration by parts.** -/
theorem connes_gauss_tail_ibp {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ioi ε, GaloisForLFunctions.gaussReal x / x)
      = -(GaloisForLFunctions.gaussReal ε * Real.log ε)
        + 2 * π * ∫ x in Ioi ε, x * (Real.log x * GaloisForLFunctions.gaussReal x) := by
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y : ℝ => GaloisForLFunctions.gaussReal y * Real.log y)
    (f' := fun x : ℝ => -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x
      + GaloisForLFunctions.gaussReal x / x)
    (a := ε) (m := (0:ℝ))
    (((GaloisForLFunctions.contDiff_gaussReal (n := 0)).continuous.continuousAt.mul
      (Real.continuousAt_log (ne_of_gt hε))).continuousWithinAt)
    (fun x hx => connes_gauss_log_hasDerivAt (lt_trans hε hx))
    (connes_gauss_deriv_integrable hε) connes_gauss_log_atTop
  have hsplit : (∫ x in Ioi ε, (-(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x
        + GaloisForLFunctions.gaussReal x / x))
      = (∫ x in Ioi ε, -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x)
        + ∫ x in Ioi ε, GaloisForLFunctions.gaussReal x / x := by
    have hπ : (0 : ℝ) < π := Real.pi_pos
    have h1 : IntegrableOn (fun x : ℝ =>
        -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x) (Ioi ε) volume := by
      have h0 := connes_integrableOn_pow_log_mul_gaussian hπ 1
      have h0' : IntegrableOn (fun x : ℝ =>
          -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x) (Ioi (0:ℝ)) volume := by
        have := h0.const_mul (-(2 * π))
        refine this.congr ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
        show -(2 * π) * (x ^ 1 * (Real.log x * Real.exp (-π * x ^ 2)))
            = -(2 * π * x) * Real.exp (-(π * x ^ 2)) * Real.log x
        have : Real.exp (-π * x ^ 2) = Real.exp (-(π * x ^ 2)) := by ring_nf
        rw [this]
        ring
      exact h0'.mono_set (Ioi_subset_Ioi hε.le)
    have h2 : IntegrableOn (fun x : ℝ => GaloisForLFunctions.gaussReal x / x) (Ioi ε) volume := by
      have hg : IntegrableOn (fun x : ℝ => ε⁻¹ * GaloisForLFunctions.gaussReal x) (Ioi ε) volume :=
        (GaloisForLFunctions.gaussianSchwartzReal.integrable (μ := volume)).integrableOn.const_mul ε⁻¹
      refine Integrable.mono' hg ?_ ?_
      · have hmeas : Measurable (fun x : ℝ => GaloisForLFunctions.gaussReal x / x) := by
          unfold GaloisForLFunctions.gaussReal
          fun_prop
        exact hmeas.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := ε))] with x hx
        have hx0 : ε < x := hx
        have hxpos : (0:ℝ) < x := lt_trans hε hx0
        rw [Real.norm_of_nonneg
          (div_nonneg (GaloisForLFunctions.gaussReal_pos x).le hxpos.le)]
        calc GaloisForLFunctions.gaussReal x / x
            ≤ GaloisForLFunctions.gaussReal x / ε :=
              div_le_div_of_nonneg_left (GaloisForLFunctions.gaussReal_pos x).le hε hx0.le
          _ = ε⁻¹ * GaloisForLFunctions.gaussReal x := by rw [div_eq_inv_mul]
    exact MeasureTheory.integral_add h1 h2
  have hconst : (∫ x in Ioi ε, -(2 * π * x) * GaloisForLFunctions.gaussReal x * Real.log x)
      = -(2 * π) * ∫ x in Ioi ε, x * (Real.log x * GaloisForLFunctions.gaussReal x) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  rw [hsplit, hconst] at hmain
  linarith [hmain]

theorem connes_gauss_abs (x : ℝ) :
    GaloisForLFunctions.gaussReal |x| = GaloisForLFunctions.gaussReal x := by
  unfold GaloisForLFunctions.gaussReal
  rw [sq_abs]

/-- Folding the two-sided tail onto the positive half line. -/
theorem connes_gauss_fold {ε : ℝ} (hε : 0 < ε) :
    (∫ x in {x : ℝ | ε ≤ |x|}, GaloisForLFunctions.gaussReal x * (2 * |x|)⁻¹)
      = ∫ x in Ioi ε, GaloisForLFunctions.gaussReal x / x := by
  have hSm : MeasurableSet {x : ℝ | ε ≤ |x|} := measurableSet_le measurable_const measurable_norm
  have hpt : ∀ x : ℝ,
      Set.indicator {x : ℝ | ε ≤ |x|}
        (fun y : ℝ => GaloisForLFunctions.gaussReal y * (2 * |y|)⁻¹) x
        = Set.indicator (Ici ε)
            (fun y : ℝ => GaloisForLFunctions.gaussReal y * (2 * y)⁻¹) |x| := by
    intro x
    by_cases hx : ε ≤ |x|
    · have h1 : x ∈ {x : ℝ | ε ≤ |x|} := hx
      have h2 : |x| ∈ Ici ε := hx
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, connes_gauss_abs x]
    · have h1 : x ∉ {x : ℝ | ε ≤ |x|} := hx
      have h2 : |x| ∉ Ici ε := hx
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  rw [← MeasureTheory.integral_indicator hSm,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt), integral_comp_abs,
    MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hinter : Ioi (0:ℝ) ∩ Ici ε = Ici ε := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hε h, h⟩⟩
  have hIci : (Ici ε) =ᵐ[volume] (Ioi ε) := by
    refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
    · have hdiff : Ici ε \ Ioi ε = {ε} := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff, not_lt]
        exact ⟨fun h => le_antisymm h.2 h.1, fun h => by rw [h]; exact ⟨le_refl _, le_refl _⟩⟩
      rw [hdiff]
      exact Real.volume_singleton
    · have hdiff : Ioi ε \ Ici ε = (∅ : Set ℝ) := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ici, Set.mem_empty_iff_false, not_le,
          iff_false, not_and, not_lt]
        exact fun h => h.le
      rw [hdiff]
      simp
  rw [hinter, MeasureTheory.setIntegral_congr_set hIci, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hxpos : (0:ℝ) < x := lt_trans hε hx
  field_simp

theorem connes_gauss_zero : (GaloisForLFunctions.gaussianSchwartz : ℝ → ℂ) 0 = 1 := by
  rw [GaloisForLFunctions.gaussianSchwartz_apply]
  unfold GaloisForLFunctions.gaussReal
  norm_num

/-- The regularized principal value of the Gaussian at cut-off `ε`, in closed form. -/
theorem connes_gauss_logPV_eq {ε : ℝ} (hε : 0 < ε) :
    connesRealLogPV ((GaloisForLFunctions.gaussianSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε
      = (((1 - GaloisForLFunctions.gaussReal ε) * Real.log ε
          + 2 * π * ∫ x in Ioi ε, x * (Real.log x * GaloisForLFunctions.gaussReal x) : ℝ) : ℂ) := by
  have hSm : MeasurableSet {x : ℝ | ε ≤ |x|} := measurableSet_le measurable_const measurable_norm
  rw [connesRealLogPV, connes_gauss_zero]
  have hcast : (∫ x in {x : ℝ | ε ≤ |x|},
        (GaloisForLFunctions.gaussianSchwartz : ℝ → ℂ) x
          * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      = (((∫ x in {x : ℝ | ε ≤ |x|},
          GaloisForLFunctions.gaussReal x * (2 * |x|)⁻¹ : ℝ)) : ℂ) := by
    rw [← _root_.integral_complex_ofReal]
    refine setIntegral_congr_fun hSm fun x _ => ?_
    rw [GaloisForLFunctions.gaussianSchwartz_apply, connesRealMultHaarDensity,
      ← Complex.ofReal_mul]
  rw [hcast, connes_gauss_fold hε, connes_gauss_tail_ibp hε]
  push_cast
  ring

theorem connes_gauss_boundary_tendsto :
    Tendsto (fun ε : ℝ => (1 - GaloisForLFunctions.gaussReal ε) * Real.log ε)
      (𝓝[>] 0) (𝓝 0) := by
  have hbase0 := _root_.tendsto_log_mul_rpow_nhdsGT_zero (r := (2:ℝ)) (by norm_num)
  have hbase : Tendsto (fun ε : ℝ => π * (Real.log ε * ε ^ (2:ℕ))) (𝓝[>] 0) (𝓝 0) := by
    have h2 := hbase0.const_mul π
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0:ℝ) < ε := hε
    have hcast : ε ^ (2:ℝ) = ε ^ (2:ℕ) := by
      rw [← Real.rpow_natCast ε 2]
      norm_num
    rw [hcast]
  have habs : Tendsto (fun ε : ℝ => |π * (Real.log ε * ε ^ (2:ℕ))|) (𝓝[>] 0) (𝓝 0) := by
    have h3 := hbase.abs
    rwa [abs_zero] at h3
  refine squeeze_zero_norm' ?_ habs
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0:ℝ) < ε := hε
  have hnn : 0 ≤ 1 - GaloisForLFunctions.gaussReal ε := by
    have : GaloisForLFunctions.gaussReal ε ≤ 1 := by
      unfold GaloisForLFunctions.gaussReal
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, sq_nonneg ε]
    linarith
  have hle : 1 - GaloisForLFunctions.gaussReal ε ≤ π * ε ^ 2 := by
    have h := Real.add_one_le_exp (-(π * ε ^ 2))
    unfold GaloisForLFunctions.gaussReal
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  have hrhs : |π * (Real.log ε * ε ^ (2:ℕ))| = π * ε ^ 2 * |Real.log ε| := by
    rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos), abs_mul,
      abs_of_nonneg (sq_nonneg ε)]
    ring
  rw [hrhs]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

theorem connes_gauss_idlog_integrable :
    IntegrableOn (fun x : ℝ => x * (Real.log x * GaloisForLFunctions.gaussReal x))
      (Ioi (0:ℝ)) volume := by
  have h0 := connes_integrableOn_pow_log_mul_gaussian Real.pi_pos 1
  refine h0.congr ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
  show x ^ 1 * (Real.log x * Real.exp (-π * x ^ 2))
      = x * (Real.log x * GaloisForLFunctions.gaussReal x)
  unfold GaloisForLFunctions.gaussReal
  ring_nf

theorem connes_gauss_tail_tendsto :
    Tendsto (fun ε : ℝ => ∫ x in Ioi ε, x * (Real.log x * GaloisForLFunctions.gaussReal x))
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (0:ℝ), x * (Real.log x * GaloisForLFunctions.gaussReal x))) := by
  set f : ℝ → ℝ := fun x => x * (Real.log x * GaloisForLFunctions.gaussReal x) with hf
  have hfint : IntegrableOn f (Ioi (0:ℝ)) volume := connes_gauss_idlog_integrable
  have hrepr : ∀ ε : ℝ, 0 < ε →
      (∫ x in Ioi ε, f x) = ∫ x in Ioi (0:ℝ), Set.indicator (Ioi ε) f x := by
    intro ε hε
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
    have hset : Ioi (0:ℝ) ∩ Ioi ε = Ioi ε := by
      ext y
      constructor
      · rintro ⟨_, h⟩
        exact h
      · intro h
        exact ⟨lt_trans hε h, h⟩
    rw [hset]
  have hmain : Tendsto (fun ε : ℝ => ∫ x in Ioi (0:ℝ), Set.indicator (Ioi ε) f x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (0:ℝ), f x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖f x‖) ?_ ?_ hfint.norm ?_
    · filter_upwards with ε
      exact (hfint.aestronglyMeasurable.indicator measurableSet_Ioi)
    · filter_upwards with ε
      filter_upwards with x
      by_cases hx : x ∈ Ioi ε
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x hx
      have hx0 : (0:ℝ) < x := hx
      have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), Set.indicator (Ioi ε) f x = f x := by
        have hmem : {y : ℝ | y < x} ∈ 𝓝 (0:ℝ) := gt_mem_nhds hx0
        have hmem' : {y : ℝ | y < x} ∈ 𝓝[>] (0:ℝ) := nhdsWithin_le_nhds hmem
        filter_upwards [hmem'] with ε hε
        exact Set.indicator_of_mem (show x ∈ Ioi ε from hε) f
      exact tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hrepr ε hε).symm

theorem connes_gauss_idlog_value :
    (∫ x in Ioi (0:ℝ), x * (Real.log x * GaloisForLFunctions.gaussReal x))
      = (-Real.eulerMascheroniConstant - Real.log π) / (4 * π) := by
  rw [← connes_integral_id_log_mul_gaussian Real.pi_pos]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  unfold GaloisForLFunctions.gaussReal
  ring_nf

/-- **The §V constant.**  Connes' logarithmically regularized principal value of the self-dual
Gaussian is `−γ/2 − (log π)/2`. -/
theorem connes_gaussian_logPV_tendsto :
    Tendsto (fun ε : ℝ =>
        connesRealLogPV ((GaloisForLFunctions.gaussianSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε)
      (𝓝[>] 0)
      (𝓝 (((-Real.eulerMascheroniConstant / 2 - Real.log π / 2 : ℝ)) : ℂ)) := by
  have hval : (0:ℝ) + 2 * π * ((-Real.eulerMascheroniConstant - Real.log π) / (4 * π))
      = -Real.eulerMascheroniConstant / 2 - Real.log π / 2 := by
    have hπ : (π:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring
  have hreal : Tendsto (fun ε : ℝ => (1 - GaloisForLFunctions.gaussReal ε) * Real.log ε
        + 2 * π * ∫ x in Ioi ε, x * (Real.log x * GaloisForLFunctions.gaussReal x))
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant / 2 - Real.log π / 2)) := by
    have h := connes_gauss_boundary_tendsto.add (connes_gauss_tail_tendsto.const_mul (2 * π))
    rw [connes_gauss_idlog_value, hval] at h
    exact h
  have hcast := (Complex.continuous_ofReal.tendsto
    (-Real.eulerMascheroniConstant / 2 - Real.log π / 2)).comp hreal
  refine hcast.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (connes_gauss_logPV_eq hε).symm

end

end GaloisForLFunctions.RHTower
