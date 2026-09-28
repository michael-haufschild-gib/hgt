import GaloisForLFunctions.RHTower.ChronologicalTailObservation
import GaloisForLFunctions.RHTower.ChronologicalWeightedSourceFloor

/-!
# The Möbius weight observed by a sampling functional

For `ψ ∈ L²([1, 2])` put `H_ψ(x) = ⟪ψ, h(x ·)⟫ = ∫₁² conj ψ(u) h(xu) du` and let
`w = 1_{(0, θ]} H_ψ`.

* `H_ψ` is bounded by `‖ψ‖` and Lipschitz on `(0, 1]` (the Bose defect is Lipschitz on `(0, 2]`).
* Pairing the rescaled Möbius head with `ψ` gives the actual weighted source at the integer
  scale: `⟪ψ, head_N⟫ = Σ_n μ(n) w(n/N)`.
* Absolute Fubini on `(0, θ) × [1, 2]` gives `mellin w ρ = ⟪ψ, K_ρ⟫` for `Re ρ = 1/2`: the
  integrand is dominated by `x^{-1/2} |ψ(u)|`.
-/

open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology ComplexConjugate Moebius
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-- The profile `H_ψ(x) = ⟪ψ, h(x ·)⟫` of a sampling functional. -/
def sampleProfile (ψ : SampleSpace) (x : ℝ) : ℂ :=
  inner ℂ ψ (toSample fun u : ℝ => ((fusionBoseDefect (x * u) : ℝ) : ℂ))

/-- The sharply cut weight `1_{(0, θ]} H_ψ`. -/
def sampleWeight (θ : ℝ) (ψ : SampleSpace) : ℝ → ℂ := (Ioc 0 θ).indicator (sampleProfile ψ)

theorem norm_toSample_bose_le (c : ℝ) :
    ‖toSample fun u : ℝ => ((fusionBoseDefect (c * u) : ℝ) : ℂ)‖ ≤ 1 :=
  norm_toSample_le zero_le_one fun u _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fusionBoseDefect_bounds _).1]
    exact (fusionBoseDefect_bounds _).2.1

theorem norm_sampleProfile_le (ψ : SampleSpace) (x : ℝ) : ‖sampleProfile ψ x‖ ≤ ‖ψ‖ :=
  (norm_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left (norm_toSample_bose_le x) (norm_nonneg ψ)).trans_eq (mul_one _))

/-- **The profile is Lipschitz on `(0, 1]`.** -/
theorem exists_sampleProfile_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ : SampleSpace, ∀ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖sampleProfile ψ x - sampleProfile ψ y‖ ≤ ‖ψ‖ * L * |x - y| := by
  obtain ⟨Lh, hLh0, hLh⟩ := exists_fusionBoseDefect_lipschitz
  refine ⟨2 * Lh, by positivity, fun ψ x hx y hy => ?_⟩
  rw [sampleProfile, sampleProfile, ← inner_sub_right,
    ← toSample_sub (memLp_sample_bose x) (memLp_sample_bose y), mul_assoc]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg ψ))
  refine norm_toSample_le (by positivity) fun u hu => ?_
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu.1
  have hmem : ∀ z ∈ Ioc (0 : ℝ) 1, z * u ∈ Ioc (0 : ℝ) 2 := fun z hz =>
    ⟨mul_pos hz.1 hu0, by nlinarith [hz.1, hz.2, hu.2]⟩
  simp only [Pi.sub_apply]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine (hLh _ (hmem x hx) _ (hmem y hy)).trans ?_
  rw [← sub_mul, abs_mul, abs_of_pos hu0]
  nlinarith [mul_nonneg (mul_nonneg hLh0 (abs_nonneg (x - y))) (by linarith [hu.2] : 0 ≤ 2 - u)]

theorem measurable_sampleWeight {θ : ℝ} (hθ1 : θ ≤ 1) (ψ : SampleSpace) :
    Measurable (sampleWeight θ ψ) := by
  classical
  obtain ⟨L, hL0, hL⟩ := exists_sampleProfile_lipschitz
  have hcont : ContinuousOn (sampleProfile ψ) (Ioc 0 θ) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := ⟨‖ψ‖ * L, by positivity⟩) fun x hx y hy => ?_)
      |>.continuousOn
    rw [dist_eq_norm, Real.dist_eq]
    exact hL ψ x ⟨hx.1, hx.2.trans hθ1⟩ y ⟨hy.1, hy.2.trans hθ1⟩
  rw [sampleWeight, ← Set.piecewise_eq_indicator]
  exact hcont.measurable_piecewise continuousOn_const measurableSet_Ioc

/-- **Pairing the head with `ψ` is the weighted Möbius source at the integer scale.** -/
theorem inner_headFun_eq_source {θ : ℝ} (hθ1 : θ < 1) (ψ : SampleSpace) {N : ℕ} (hN : 0 < N) :
    (inner ℂ ψ (toSample (headFun θ N)) : ℂ) =
      chronologicalMobiusWeightedSource (sampleWeight θ ψ) (1 / N) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ k : ℕ, MemLp (fun u : ℝ => if (k : ℝ) ≤ θ * N then (μ k : ℂ) *
      ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) else 0) 2 sampleMeasure := by
    intro k
    by_cases hk : (k : ℝ) ≤ θ * N
    · simp only [hk, if_true]
      exact (memLp_sample_bose _).const_mul _
    · simp only [hk, if_false]
      exact MemLp.zero'
  have hhead : headFun θ N = ∑ k ∈ Finset.Ioc 0 N, fun u : ℝ => if (k : ℝ) ≤ θ * N then
      (μ k : ℂ) * ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) else 0 := by
    funext u; rw [headFun, Finset.sum_apply]
  have hw : ∀ x, θ < x → sampleWeight θ ψ x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hx)) _
  rw [hhead, toSample_sum _ fun k _ => hterm k, inner_sum,
    chronologicalMobiusWeightedSource_eq_sum _ N (by positivity) hw
      (by rw [← div_eq_mul_one_div, lt_div_iff₀ hNpos]; nlinarith)]
  symm
  rw [← Finset.sum_subset (Finset.Ioc_subset_Iic_self.trans (by
      intro k hk; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Iic.mp hk))))
    fun k _ hk => ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    rw [mul_one_div]
    by_cases hkθ : (k : ℝ) ≤ θ * N
    · have hmem : (k : ℝ) / N ∈ Ioc 0 θ := ⟨div_pos hk0 hNpos, (div_le_iff₀ hNpos).mpr
        (by linarith)⟩
      simp only [hkθ, if_true]
      rw [sampleWeight, Set.indicator_of_mem hmem, sampleProfile,
        show (fun u : ℝ => (μ k : ℂ) * ((fusionBoseDefect (k / N * u) : ℝ) : ℂ)) =
          (μ k : ℂ) • fun u : ℝ => ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) from rfl,
        toSample_smul _ (memLp_sample_bose _), inner_smul_right]
    · have hnot : (k : ℝ) / N ∉ Ioc 0 θ := fun h =>
        hkθ (by have := (div_le_iff₀ hNpos).mp h.2; linarith)
      simp only [hkθ, if_false]
      rw [sampleWeight, Set.indicator_of_notMem hnot, mul_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl, toSample_zero, inner_zero_right]
  · have hk0 : k = 0 := by
      by_contra h
      exact hk (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h,
        Nat.lt_succ_iff.mp (Finset.mem_range.mp ‹k ∈ Finset.range (N + 1)›)⟩)
    subst hk0
    simp

/-- **The Mellin moment of the observed weight is the pairing with the critical vector.** -/
theorem mellin_sampleWeight {θ : ℝ} (hθ1 : θ < 1) (ψ : SampleSpace) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) : mellin (sampleWeight θ ψ) ρ = inner ℂ ψ (critVec θ ρ) := by
  -- the critical transform as an integral over `(0, θ)`
  have hK : ∀ u : ℝ, 0 < u → boseTransform (criticalProfile θ ρ) (u : ℂ) =
      ∫ x in Ioo 0 θ, (x : ℂ) ^ (ρ - 1) * ((fusionBoseDefect (x * u) : ℝ) : ℂ) := by
    intro u hu
    rw [boseTransform_ofReal _ hu]
    have hfun : (fun x : ℝ => criticalProfile θ ρ x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) =
        (Ioo 0 θ).indicator fun x : ℝ => (x : ℂ) ^ (ρ - 1) * ((fusionBoseDefect (x * u) : ℝ) : ℂ) := by
      funext x
      by_cases hx : x ∈ Ioo 0 θ
      · rw [Set.indicator_of_mem hx, criticalProfile_eq_cpow hx.1 hx.2]
      · rw [Set.indicator_of_notMem hx, criticalProfile_of_not hx, zero_mul]
    rw [hfun, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr (Ioo_subset_Ioo_right hθ1.le)]
  -- the Mellin transform as an integral over `(0, θ)`
  have hM : mellin (sampleWeight θ ψ) ρ =
      ∫ x in Ioo 0 θ, (x : ℂ) ^ (ρ - 1) * sampleProfile ψ x := by
    rw [mellin]
    have hfun : (fun t : ℝ => (t : ℂ) ^ (ρ - 1) • sampleWeight θ ψ t) =
        (Ioc 0 θ).indicator fun t : ℝ => (t : ℂ) ^ (ρ - 1) * sampleProfile ψ t := by
      funext t
      by_cases ht : t ∈ Ioc 0 θ
      · rw [sampleWeight, Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul]
      · rw [sampleWeight, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
    rw [hfun, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Ioc_subset_Ioi_self, integral_Ioc_eq_integral_Ioo]
  -- Fubini on `(0, θ) × [1, 2]`
  set F : ℝ → ℝ → ℂ := fun x u =>
    (x : ℂ) ^ (ρ - 1) * (conj ((ψ : ℝ → ℂ) u) * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) with hF
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioo (0 : ℝ) θ)).prod sampleMeasure) := by
    have hg1 : Integrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (volume.restrict (Ioo (0 : ℝ) θ)) :=
      integrableOn_rpow_Ioo (by norm_num) 0 θ
    have hg2 : Integrable (fun u => ‖(ψ : ℝ → ℂ) u‖) sampleMeasure :=
      ((Lp.memLp ψ).integrable one_le_two).norm
    refine (hg1.mul_prod hg2).mono' ?_ ?_
    · exact (((Complex.measurable_ofReal.comp measurable_fst).pow_const _).aestronglyMeasurable).mul
        ((Complex.continuous_conj.comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable ψ).comp_snd).mul
          (Complex.measurable_ofReal.comp (measurable_fusionBoseDefect.comp
            (measurable_fst.mul measurable_snd))).aestronglyMeasurable)
    · have hmem : ∀ᵐ z ∂((volume.restrict (Ioo (0 : ℝ) θ)).prod sampleMeasure),
          z ∈ Ioo (0 : ℝ) θ ×ˢ Icc (1 : ℝ) 2 := by
        rw [show sampleMeasure = volume.restrict (Icc (1 : ℝ) 2) from rfl, Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Icc)
      filter_upwards [hmem] with z hz
      obtain ⟨hx, -⟩ := hz
      have hb := fusionBoseDefect_bounds (z.1 * z.2)
      simp only [Function.uncurry, hF]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.norm_real,
        RCLike.norm_conj, Real.norm_eq_abs, abs_of_nonneg hb.1]
      have hre : (ρ - 1).re = -(1 / 2) := by rw [Complex.sub_re, hρ, Complex.one_re]; norm_num
      rw [hre]
      exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right (norm_nonneg _) hb.2.1))
        (Real.rpow_nonneg hx.1.le _)
  rw [hM, critVec, inner_toSample_right ψ (memLp_sample_of_continuousOn (continuousOn_critFun hρ))]
  calc ∫ x in Ioo 0 θ, (x : ℂ) ^ (ρ - 1) * sampleProfile ψ x
      = ∫ x in Ioo 0 θ, ∫ u in Icc (1 : ℝ) 2, F x u := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hF, sampleProfile, inner_toSample_right ψ (memLp_sample_bose x),
          integral_const_mul]
    _ = ∫ u in Icc (1 : ℝ) 2, ∫ x in Ioo 0 θ, F x u := integral_integral_swap hint
    _ = ∫ u in Icc (1 : ℝ) 2, conj ((ψ : ℝ → ℂ) u) * boseTransform (criticalProfile θ ρ) (u : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
        rw [hK u (lt_of_lt_of_le one_pos hu.1), ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hF]
        ring

end RHTower
