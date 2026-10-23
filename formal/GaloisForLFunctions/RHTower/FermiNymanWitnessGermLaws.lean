import GaloisForLFunctions.RHTower.FermiNymanWitnessGermRigidity
import GaloisForLFunctions.RHTower.FermiNymanBoundedSpuriousClassification

/-!
# Germ laws for Fermi witnesses: mass growth at the origin and the top-octave log-mean

A witness of the alternating Nyman–Beurling system is determined by its germ at `t = 0`.  This
module describes the germ by a single number, the mass function `m_w(x) = ∫_0^x |w|²`, and proves:

* **Mass dichotomy (unconditional).**  A measurable square-integrable witness is a.e. dyadically
  self-similar if and only if its mass is at most linear at the origin, `m_w(x) ≤ C x`.
  Self-similarity halves the mass with the scale, `m_w(x/2) = m_w(x)/2`, which gives linear mass.
  Conversely, under `m_w(x) ≤ C x` every dilation average
  `w_η(t) = η⁻¹ t ∫_{t/(1+η)}^{t} w(u) u⁻² du` is bounded by `η⁻¹(1+η)²√C`, hence a bounded
  continuous witness, hence self-similar; comparing `w_η(t/2)` with `w_η(t)` and substituting
  `u ↦ u/2` gives `∫_s^t (w(u/2) − w(u)) u⁻² du = 0` for all `0 < s < t ≤ 1`, and Lebesgue
  differentiation finishes.  A zero witness `t^{ρ̄−1}` has `m(x) = x^{2 Re ρ − 1}/(2 Re ρ − 1)`,
  superlinear; a spurious witness has exactly linear mass.
* **The Riemann hypothesis is linear mass growth of every witness at the origin.**
  Under RH every dilation average is self-similar, so every square-integrable witness is a.e.
  self-similar and has linear mass; without RH a zero witness has superlinear mass.
* **The Riemann hypothesis is a single linear functional on the witness class**: every continuous
  witness has vanishing logarithmic mean on the top octave, `∫_{1/2}^1 w(t) dt/t = 0`.  Under RH
  witnesses are bounded and self-similar, and bounded witnesses have zero logarithmic mean; a zero
  witness has logarithmic mean `(1 − 2^{1−ρ̄})/(ρ̄ − 1) ≠ 0`.

In the language of the Haar approximation problem: the only obstruction is the energy of
approximants near `t = 0`, and that energy is controlled exactly when no witness carries
superlinear mass at the origin.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry

/-! ## Lebesgue differentiation on `(0,1]` from interval integrals -/

/-- A function integrable on every `(η, 1]` whose integrals over all intervals `(s, t] ⊆ (0, 1]`
vanish is zero a.e. on `(0, 1]`. -/
theorem ae_eq_zero_Ioc_of_forall_setIntegral_Ioc_eq_zero {g : ℝ → ℂ}
    (hg : ∀ η : ℝ, 0 < η → IntegrableOn g (Ioc η 1))
    (hint : ∀ s t : ℝ, 0 < s → s < t → t ≤ 1 → ∫ u in Ioc s t, g u = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), g t = 0 := by
  have hslice : ∀ n : ℕ, ∀ᵐ x ∂volume, x ∈ Ioo (1 / ((n : ℝ) + 2)) 1 → g x = 0 := by
    intro n
    set η : ℝ := 1 / ((n : ℝ) + 2) with hηdef
    have hη : 0 < η := by positivity
    set G : ℝ → ℂ := (Ioc η 1).indicator g with hGdef
    have hGint : Integrable G := by
      rw [hGdef, integrable_indicator_iff measurableSet_Ioc]
      exact hg η hη
    have hint' : ∀ s t : ℝ, η < s → s < t → t ≤ 1 → ∫ u in Ioc s t, G u = 0 := by
      intro s t hs hst ht1
      rw [hGdef, setIntegral_indicator measurableSet_Ioc,
        inter_eq_left.mpr (Ioc_subset_Ioc hs.le ht1)]
      exact hint s t (lt_trans hη hs) hst ht1
    filter_upwards [ae_eq_zero_on_Ioo_of_forall_setIntegral_Ioc_eq_zero hGint hint']
      with x hx hxmem
    have := hx hxmem
    rwa [hGdef, indicator_of_mem (show x ∈ Ioc η 1 from ⟨hxmem.1, hxmem.2.le⟩)] at this
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hall := ae_all_iff.2 hslice
  have hne1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [hall, hne1] with x hx hx1 hxmem
  have hxlt : x < 1 := lt_of_le_of_ne hxmem.2 hx1
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
  refine hx n ⟨?_, hxlt⟩
  rw [div_lt_iff₀ (by positivity)]
  have := (div_lt_iff₀ hxmem.1).1 hn
  nlinarith [hxmem.1]

/-! ## The mass function -/

/-- The mass of `w` on `(0, x]`: `m_w(x) = ∫_0^x |w|²`. -/
def witnessMass (w : ℝ → ℂ) (x : ℝ) : ℝ := ∫ t in Ioc (0 : ℝ) x, ‖w t‖ ^ 2

theorem witnessMass_nonneg (w : ℝ → ℂ) (x : ℝ) : 0 ≤ witnessMass w x :=
  integral_nonneg fun _ => sq_nonneg _

/-- Cauchy–Schwarz: `∫_0^x ‖w‖ ≤ √(m_w(x) · x)`. -/
theorem integral_norm_le_sqrt_witnessMass {w : ℝ → ℂ} (hw : Measurable w)
    (hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1)) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    (∫ t in Ioc (0 : ℝ) x, ‖w t‖) ≤ Real.sqrt (witnessMass w x * x) := by
  have h2 : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 x) := hsq.mono_set (Ioc_subset_Ioc_right hx.2)
  have hcs := sq_integral_mul_le (μ := volume.restrict (Ioc (0 : ℝ) x)) (f := fun t => ‖w t‖)
    (g := fun _ => (1 : ℝ)) hw.norm.aestronglyMeasurable aestronglyMeasurable_const h2
    (by simp)
  simp only [mul_one, one_pow] at hcs
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hx.1.le] at hcs
  exact (Real.le_sqrt (integral_nonneg fun _ => norm_nonneg _)
    (mul_nonneg (witnessMass_nonneg w x) hx.1.le)).2 hcs

/-! ## Linear mass bounds every dilation average -/

/-- Under `m_w(x) ≤ C x`, the dilation average is bounded by `η⁻¹ (1 + η)² √C` on `(0, 1]`. -/
theorem IsL2FermiWitness.norm_dilationAverage_le_of_linearMass {w : ℝ → ℂ}
    (hw : IsL2FermiWitness w) {C : ℝ} (hC : ∀ x ∈ Ioc (0 : ℝ) 1, witnessMass w x ≤ C * x)
    {η : ℝ} (hη : 0 < η) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖haarDilationAverage η w t‖ ≤ η⁻¹ * (1 + η) ^ 2 * Real.sqrt C := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm hw.measurable.aestronglyMeasurable).mpr hw.sq).integrable
      (by norm_num)
  have ht0 : 0 < t := ht.1
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 ⟨one_pos, le_rfl⟩
    have h2 := witnessMass_nonneg w 1
    linarith
  have hη1 : 0 < 1 + η := by linarith
  have hlow : 0 < t / (1 + η) := div_pos ht0 hη1
  have hsubI : Ioc (t / (1 + η)) t ⊆ Ioc (0 : ℝ) t := Ioc_subset_Ioc_left hlow.le
  have hsub1 : Ioc (0 : ℝ) t ⊆ Ioc 0 1 := Ioc_subset_Ioc_right ht.2
  unfold haarDilationAverage
  rw [integral_Icc_comp_div_eq_primitive hη ht0, norm_mul, norm_mul, norm_inv, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hη.le, Real.norm_of_nonneg ht0.le]
  have hpt : ∀ u ∈ Ioc (t / (1 + η)) t, ‖w u / (u : ℂ) ^ 2‖ ≤ ((1 + η) / t) ^ 2 * ‖w u‖ := by
    intro u hu
    have hu0 : 0 < u := lt_trans hlow hu.1
    have h1 : (u ^ 2)⁻¹ ≤ ((1 + η) / t) ^ 2 := by
      rw [← inv_div, inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hlow.le hu.1.le 2)
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le, div_eq_mul_inv,
      mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hint1 : IntegrableOn (fun u => w u / (u : ℂ) ^ 2) (Ioc (t / (1 + η)) t) := by
    have h := intervalIntegrable_div_sq hw.measurable hwi hlow
      (by rw [div_le_one hη1]; linarith [ht.2])
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by rw [div_le_one hη1]; linarith [ht.2])]
      at h
    exact h.mono_set (Ioc_subset_Ioc_right ht.2)
  have hsqrt : Real.sqrt (witnessMass w t * t) ≤ Real.sqrt C * t := by
    rw [show Real.sqrt C * t = Real.sqrt (C * (t * t)) by
      rw [Real.sqrt_mul hC0, Real.sqrt_mul_self ht0.le]]
    exact Real.sqrt_le_sqrt (by nlinarith [hC t ht])
  calc η⁻¹ * (t * ‖∫ u in Ioc (t / (1 + η)) t, w u / (u : ℂ) ^ 2‖)
      ≤ η⁻¹ * (t * ∫ u in Ioc (t / (1 + η)) t, ((1 + η) / t) ^ 2 * ‖w u‖) := by
        gcongr
        refine (norm_integral_le_integral_norm _).trans ?_
        exact setIntegral_mono_on hint1.norm
          ((hwi.mono_set (hsubI.trans hsub1)).norm.const_mul _) measurableSet_Ioc hpt
    _ = η⁻¹ * (1 + η) ^ 2 * (t⁻¹ * ∫ u in Ioc (t / (1 + η)) t, ‖w u‖) := by
        rw [integral_const_mul]
        field_simp
    _ ≤ η⁻¹ * (1 + η) ^ 2 * (t⁻¹ * ∫ u in Ioc (0 : ℝ) t, ‖w u‖) := by
        have hmono : (∫ u in Ioc (t / (1 + η)) t, ‖w u‖) ≤ ∫ u in Ioc (0 : ℝ) t, ‖w u‖ :=
          setIntegral_mono_set (hwi.mono_set hsub1).norm
            (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall hsubI)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 ht0.le))
          (by positivity)
    _ ≤ η⁻¹ * (1 + η) ^ 2 * (t⁻¹ * Real.sqrt (witnessMass w t * t)) := by
        gcongr
        exact integral_norm_le_sqrt_witnessMass hw.measurable hw.sq ht
    _ ≤ η⁻¹ * (1 + η) ^ 2 * (t⁻¹ * (Real.sqrt C * t)) := by gcongr
    _ = η⁻¹ * (1 + η) ^ 2 * Real.sqrt C := by
        field_simp

/-! ## From self-similar dilation averages to a.e. self-similarity -/

/-- If all dilation averages are self-similar, then `∫_s^t (w(u/2) − w(u)) u⁻² du = 0` for all
`0 < s < t ≤ 1`. -/
theorem IsL2FermiWitness.setIntegral_sub_comp_half_div_sq_eq_zero {w : ℝ → ℂ}
    (hw : IsL2FermiWitness w)
    (hss : ∀ η : ℝ, 0 < η → ∀ t ∈ Ioc (0 : ℝ) 1,
      haarDilationAverage η w (t / 2) = haarDilationAverage η w t)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht1 : t ≤ 1) :
    ∫ u in Ioc s t, (w (u / 2) - w u) / (u : ℂ) ^ 2 = 0 := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm hw.measurable.aestronglyMeasurable).mpr hw.sq).integrable
      (by norm_num)
  have hw2 : IntegrableOn (fun u => w (u / 2)) (Ioc 0 1) := by
    have hn := integrableOn_comp_div_of_integrableOn (μ := 2) (f := fun t => ‖w t‖) hwi.norm
      (by norm_num)
    exact (integrable_norm_iff
      ((hw.measurable.comp (measurable_id.div_const 2)).aestronglyMeasurable)).1 hn
  have ht0 : 0 < t := lt_trans hs hst
  have ht0' : t ≠ 0 := ht0.ne'
  set η : ℝ := t / s - 1 with hηdef
  have hη : 0 < η := by
    rw [hηdef, sub_pos, lt_div_iff₀ hs, one_mul]; exact hst
  have hts : t / (1 + η) = s := by
    rw [hηdef, add_sub_cancel, div_div_eq_mul_div, mul_div_cancel_left₀ s ht0']
  have hts2 : t / 2 / (1 + η) = s / 2 := by
    rw [div_right_comm, hts]
  have h := hss η hη t ⟨ht0, ht1⟩
  unfold haarDilationAverage at h
  rw [integral_Icc_comp_div_eq_primitive hη ht0,
    integral_Icc_comp_div_eq_primitive hη (by positivity : (0 : ℝ) < t / 2), hts, hts2] at h
  have hηc : ((η : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hη.ne')
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0'
  have hkey : ∫ u in Ioc s t, w u / (u : ℂ) ^ 2 =
      (1 / 2 : ℂ) * ∫ u in Ioc (s / 2) (t / 2), w u / (u : ℂ) ^ 2 := by
    have h' := mul_left_cancel₀ hηc h
    push_cast at h'
    apply mul_left_cancel₀ htc
    linear_combination (-1 : ℂ) * h'
  -- substitution `u ↦ u/2` in the lower-octave integral
  have hsub2 : ∫ u in Ioc s t, w (u / 2) / (u : ℂ) ^ 2 =
      (1 / 2 : ℂ) * ∫ u in Ioc (s / 2) (t / 2), w u / (u : ℂ) ^ 2 := by
    rw [← intervalIntegral.integral_of_le hst.le,
      ← intervalIntegral.integral_of_le (by linarith : s / 2 ≤ t / 2)]
    have hcv := intervalIntegral.integral_comp_div (a := s) (b := t)
      (fun u : ℝ => w u / (u : ℂ) ^ 2) (two_ne_zero)
    rw [Complex.real_smul] at hcv
    have hcongr : ∀ x : ℝ, w (x / 2) / (x : ℂ) ^ 2 =
        (1 / 4 : ℂ) * (w (x / 2) / (((x / 2 : ℝ) : ℂ)) ^ 2) := by
      intro x
      push_cast
      by_cases hx : (x : ℂ) = 0
      · simp [hx]
      · field_simp
        ring
    simp_rw [hcongr]
    rw [intervalIntegral.integral_const_mul, hcv]
    push_cast
    ring
  have hA : IntegrableOn (fun u => w (u / 2) / (u : ℂ) ^ 2) (Ioc s t) := by
    have hmeas : Measurable (fun u : ℝ => w (u / 2) / (u : ℂ) ^ 2) :=
      (hw.measurable.comp (measurable_id.div_const 2)).div (Complex.measurable_ofReal.pow_const 2)
    refine ((hw2.mono_set (Ioc_subset_Ioc hs.le ht1)).norm.const_mul (s ^ 2)⁻¹).mono'
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have hu : s < u := hu.1
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith), div_eq_mul_inv,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by nlinarith)) (norm_nonneg _)
  have hB : IntegrableOn (fun u => w u / (u : ℂ) ^ 2) (Ioc s t) := by
    have h := intervalIntegrable_div_sq hw.measurable hwi hs (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h
    exact h.mono_set (Ioc_subset_Ioc_right ht1)
  have hdiff : ∫ u in Ioc s t, (w (u / 2) - w u) / (u : ℂ) ^ 2 =
      (∫ u in Ioc s t, w (u / 2) / (u : ℂ) ^ 2) - ∫ u in Ioc s t, w u / (u : ℂ) ^ 2 := by
    rw [← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [sub_div]
  rw [hdiff, hsub2, hkey]
  ring

/-- **A square-integrable witness all of whose dilation averages are self-similar is a.e.
self-similar.** -/
theorem IsL2FermiWitness.ae_selfSimilar_of_forall_dilationAverage_selfSimilar {w : ℝ → ℂ}
    (hw : IsL2FermiWitness w)
    (hss : ∀ η : ℝ, 0 < η → ∀ t ∈ Ioc (0 : ℝ) 1,
      haarDilationAverage η w (t / 2) = haarDilationAverage η w t) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm hw.measurable.aestronglyMeasurable).mpr hw.sq).integrable
      (by norm_num)
  have hw2 : IntegrableOn (fun u => w (u / 2)) (Ioc 0 1) := by
    have hn := integrableOn_comp_div_of_integrableOn (μ := 2) (f := fun t => ‖w t‖) hwi.norm
      (by norm_num)
    exact (integrable_norm_iff
      ((hw.measurable.comp (measurable_id.div_const 2)).aestronglyMeasurable)).1 hn
  have hloc : ∀ η : ℝ, 0 < η →
      IntegrableOn (fun u => (w (u / 2) - w u) / (u : ℂ) ^ 2) (Ioc η 1) := by
    intro η hη
    have hmeas : Measurable (fun u : ℝ => (w (u / 2) - w u) / (u : ℂ) ^ 2) :=
      ((hw.measurable.comp (measurable_id.div_const 2)).sub hw.measurable).div
        (Complex.measurable_ofReal.pow_const 2)
    refine (((hw2.sub hwi).mono_set (Ioc_subset_Ioc_left hη.le)).norm.const_mul (η ^ 2)⁻¹).mono'
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have hu : η < u := hu.1
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith), div_eq_mul_inv,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by nlinarith)) (norm_nonneg _)
  have h0 := ae_eq_zero_Ioc_of_forall_setIntegral_Ioc_eq_zero hloc
    (fun s t hs hst ht1 => hw.setIntegral_sub_comp_half_div_sq_eq_zero hss hs hst ht1)
  filter_upwards [h0, ae_restrict_mem measurableSet_Ioc] with t ht htmem
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast htmem.1.ne'
  rcases div_eq_zero_iff.1 ht with h | h
  · exact sub_eq_zero.1 h
  · exact absurd ((pow_eq_zero_iff (by norm_num)).1 h) ht0

/-- **Linear mass forces a.e. self-similarity.** -/
theorem IsL2FermiWitness.ae_selfSimilar_of_linearMass {w : ℝ → ℂ} (hw : IsL2FermiWitness w)
    {C : ℝ} (hC : ∀ x ∈ Ioc (0 : ℝ) 1, witnessMass w x ≤ C * x) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t :=
  hw.ae_selfSimilar_of_forall_dilationAverage_selfSimilar fun η hη _ ht =>
    (hw.dilationAverage_isFermiNymanWitness hη).selfSimilar_of_bounded
      (M := η⁻¹ * (1 + η) ^ 2 * Real.sqrt C)
      (fun _ hu => hw.norm_dilationAverage_le_of_linearMass hC hη hu) ht

/-! ## Self-similarity halves the mass with the scale -/

/-- For an a.e. self-similar function, `m(x/2) = m(x)/2` on `(0, 1]`. -/
theorem witnessMass_half_of_ae_selfSimilar {w : ℝ → ℂ}
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    witnessMass w (x / 2) = (1 / 2) * witnessMass w x := by
  unfold witnessMass
  rw [← intervalIntegral.integral_of_le (by linarith [hx.1] : (0 : ℝ) ≤ x / 2),
    ← intervalIntegral.integral_of_le hx.1.le]
  have h := intervalIntegral.integral_comp_div (a := 0) (b := x) (fun t : ℝ => ‖w t‖ ^ 2)
    two_ne_zero
  simp only [zero_div] at h
  have hcongr : ∫ t in (0 : ℝ)..x, ‖w (t / 2)‖ ^ 2 = ∫ t in (0 : ℝ)..x, ‖w t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hx.1.le, intervalIntegral.integral_of_le hx.1.le]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have := (ae_restrict_iff' measurableSet_Ioc).1 hs
    filter_upwards [this] with t ht htmem
    rw [ht ⟨htmem.1, htmem.2.trans hx.2⟩]
  rw [hcongr, smul_eq_mul] at h
  linarith [h]

theorem witnessMass_pow_half_of_ae_selfSimilar {w : ℝ → ℂ}
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) (n : ℕ) :
    witnessMass w ((1 / 2 : ℝ) ^ n) = (1 / 2 : ℝ) ^ n * witnessMass w 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmem : (1 / 2 : ℝ) ^ n ∈ Ioc (0 : ℝ) 1 :=
      ⟨pow_pos (by norm_num) n, pow_le_one₀ (by norm_num) (by norm_num)⟩
    rw [pow_succ, show (1 / 2 : ℝ) ^ n * (1 / 2) = (1 / 2 : ℝ) ^ n / 2 by ring,
      witnessMass_half_of_ae_selfSimilar hs hmem, ih]
    ring

/-- **A.e. self-similar square-integrable functions have linear mass at the origin:**
`m_w(x) ≤ 2 m_w(1) x`. -/
theorem witnessMass_le_of_ae_selfSimilar {w : ℝ → ℂ}
    (hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1))
    (hs : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    witnessMass w x ≤ (2 * witnessMass w 1) * x := by
  obtain ⟨n, hn0, hn1⟩ := exists_nat_pow_near_of_lt_one hx.1 hx.2
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hle1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmono : witnessMass w x ≤ witnessMass w ((1 / 2 : ℝ) ^ n) := by
    unfold witnessMass
    exact setIntegral_mono_set (hsq.mono_set (Ioc_subset_Ioc_right hle1))
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall (Ioc_subset_Ioc_right hn1))
  rw [witnessMass_pow_half_of_ae_selfSimilar hs n] at hmono
  have h2x : (1 / 2 : ℝ) ^ n ≤ 2 * x := by
    rw [pow_succ] at hn0
    linarith
  nlinarith [witnessMass_nonneg w 1]

/-- **Mass dichotomy.**  A square-integrable witness is a.e. dyadically self-similar iff its
mass at the origin is at most linear. -/
theorem IsL2FermiWitness.ae_selfSimilar_iff_linearMass {w : ℝ → ℂ} (hw : IsL2FermiWitness w) :
    (∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t) ↔
      ∃ C : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1, witnessMass w x ≤ C * x :=
  ⟨fun hs => ⟨2 * witnessMass w 1, fun _ hx => witnessMass_le_of_ae_selfSimilar hw.sq hs hx⟩,
    fun ⟨_, hC⟩ => hw.ae_selfSimilar_of_linearMass hC⟩

/-! ## The Riemann hypothesis as linear mass growth at the origin -/

/-- Under RH every square-integrable witness is a.e. self-similar. -/
theorem IsL2FermiWitness.ae_selfSimilar_of_riemannHypothesis (hRH : RiemannHypothesis)
    {w : ℝ → ℂ} (hw : IsL2FermiWitness w) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w (t / 2) = w t :=
  hw.ae_selfSimilar_of_forall_dilationAverage_selfSimilar fun _ hη t ht =>
    (riemannHypothesis_iff_fermiNymanWitness_selfSimilar.1 hRH) _
      (hw.dilationAverage_isFermiNymanWitness hη) t ht

/-- The power function `t ↦ t^{z−1}` is measurable. -/
theorem measurable_powerWitness (z : ℂ) : Measurable (powerWitness z) := by
  unfold powerWitness
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  intro t ht
  have h := Complex.continuousAt_ofReal_cpow t (z - 1) (Or.inr ht)
  have hpair : ContinuousAt (fun u : ℝ => (u, z - 1)) t :=
    (continuous_id.prodMk continuous_const).continuousAt
  exact (ContinuousAt.comp (f := fun u : ℝ => (u, z - 1)) h hpair).continuousWithinAt

/-- A zero witness has superlinear mass: `m(x) = x^{2σ−1}/(2σ−1)` is not `O(x)`. -/
theorem not_linearMass_powerWitness {z : ℂ} (hz : 1 / 2 < z.re) (hz1 : z.re < 1) (C : ℝ) :
    ¬ ∀ x ∈ Ioc (0 : ℝ) 1, witnessMass (powerWitness z) x ≤ C * x := by
  intro hC
  set σ : ℝ := z.re with hσ
  have hpos : 0 < 2 * σ - 1 := by linarith
  have hneg : 0 < 2 - 2 * σ := by linarith
  -- `x^{2σ−2} = (x⁻¹)^{2−2σ} → ∞` as `x → 0⁺`
  have hlim : Tendsto (fun x : ℝ => x⁻¹ ^ (2 - 2 * σ)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_atTop hneg).comp tendsto_inv_nhdsGT_zero
  have hev1 : ∀ᶠ x : ℝ in 𝓝[>] 0, C * (2 * σ - 1) + 1 ≤ x⁻¹ ^ (2 - 2 * σ) :=
    hlim.eventually (eventually_ge_atTop _)
  have hev2 : ∀ᶠ x : ℝ in 𝓝[>] 0, x ≤ 1 :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds one_pos)
  obtain ⟨x, hx1, hx2, hx0⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
  have hx0' : 0 < x := hx0
  have hm := hC x ⟨hx0', hx2⟩
  unfold witnessMass at hm
  rw [integral_Ioc_normSq_powerWitness hz hx0'] at hm
  -- `x^{2σ−1} = x^{2σ−2} · x`
  have hsplit : x ^ (2 * σ - 1) = x ^ (2 * σ - 2) * x := by
    rw [show 2 * σ - 1 = (2 * σ - 2) + 1 by ring, Real.rpow_add hx0', Real.rpow_one]
  have hinv : x⁻¹ ^ (2 - 2 * σ) = x ^ (2 * σ - 2) := by
    rw [Real.inv_rpow hx0'.le, show 2 - 2 * σ = -(2 * σ - 2) by ring, Real.rpow_neg hx0'.le,
      inv_inv]
  rw [hinv] at hx1
  rw [hsplit, div_le_iff₀ hpos] at hm
  -- hm : x^{2σ−2} · x ≤ C x (2σ−1)
  have : x ^ (2 * σ - 2) ≤ C * (2 * σ - 1) := by
    have h := hm
    rw [show C * x * (2 * σ - 1) = (C * (2 * σ - 1)) * x by ring] at h
    exact le_of_mul_le_mul_right h hx0'
  linarith

/-- **RH ⟺ every square-integrable witness has at most linear mass at the origin.** -/
theorem riemannHypothesis_iff_forall_l2FermiWitness_linearMass :
    RiemannHypothesis ↔ ∀ w : ℝ → ℂ, IsL2FermiWitness w →
      ∃ C : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1, witnessMass w x ≤ C * x := by
  constructor
  · intro hRH w hw
    exact hw.ae_selfSimilar_iff_linearMass.1 (hw.ae_selfSimilar_of_riemannHypothesis hRH)
  · intro h
    by_contra hRH
    obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    have hwit := isFermiNymanWitness_powerWitness_of_zeta_eq_zero hζ h1 h2
    obtain ⟨C, hC⟩ := h _ (hwit.isL2_of_measurable (measurable_powerWitness _))
    exact not_linearMass_powerWitness (z := (starRingEnd ℂ) ρ)
      (by rw [Complex.conj_re]; exact h1) (by rw [Complex.conj_re]; exact h2) C hC

/-- **RH ⟺ the dyadic dilation is power-bounded on the witness class** (`‖w(·/2^k)‖² = 2^k m_w(2^{−k})`). -/
theorem riemannHypothesis_iff_forall_l2FermiWitness_dyadicMass_bounded :
    RiemannHypothesis ↔ ∀ w : ℝ → ℂ, IsL2FermiWitness w →
      ∃ C : ℝ, ∀ k : ℕ, (2 : ℝ) ^ k * witnessMass w ((1 / 2 : ℝ) ^ k) ≤ C := by
  rw [riemannHypothesis_iff_forall_l2FermiWitness_linearMass]
  constructor
  · intro h w hw
    obtain ⟨C, hC⟩ := h w hw
    refine ⟨C, fun k => ?_⟩
    have hmem : (1 / 2 : ℝ) ^ k ∈ Ioc (0 : ℝ) 1 :=
      ⟨pow_pos (by norm_num) k, pow_le_one₀ (by norm_num) (by norm_num)⟩
    have hk := hC _ hmem
    have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ k * witnessMass w ((1 / 2 : ℝ) ^ k)
        ≤ (2 : ℝ) ^ k * (C * (1 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left hk (pow_pos (by norm_num) k).le
      _ = C * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by ring
      _ = C := by rw [h2, mul_one]
  · intro h w hw
    obtain ⟨C, hC⟩ := h w hw
    refine ⟨2 * C, fun x hx => ?_⟩
    obtain ⟨n, hn0, hn1⟩ := exists_nat_pow_near_of_lt_one hx.1 hx.2
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hle1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hmono : witnessMass w x ≤ witnessMass w ((1 / 2 : ℝ) ^ n) := by
      unfold witnessMass
      exact setIntegral_mono_set (hw.sq.mono_set (Ioc_subset_Ioc_right hle1))
        (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioc_right hn1))
    have hk := hC n
    have h2 : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    have h2x : (1 / 2 : ℝ) ^ n ≤ 2 * x := by
      rw [pow_succ] at hn0
      linarith
    have hpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    -- `m(2^{-n}) ≤ C 2^{-n} ≤ 2 C x`
    have hm : witnessMass w ((1 / 2 : ℝ) ^ n) ≤ C * (1 / 2 : ℝ) ^ n := by
      have := (le_div_iff₀' hpos).2 hk
      rwa [show C / 2 ^ n = C * (1 / 2 : ℝ) ^ n by rw [one_div_pow, mul_one_div]] at this
    have hC0 : 0 ≤ C :=
      le_trans (mul_nonneg (by positivity) (witnessMass_nonneg _ _)) (hC 0)
    nlinarith

/-! ## The top-octave logarithmic mean: a linear RH criterion -/

/-- The logarithmic mean of a power function on the top octave. -/
theorem dyadicLogMean_powerWitness {z : ℂ} (hz : z ≠ 1) :
    dyadicLogMean (powerWitness z) = (1 - (2 : ℂ) ^ (1 - z)) / (z - 1) := by
  unfold dyadicLogMean powerWitness
  have hcongr : ∀ t ∈ Ioc (1 / 2 : ℝ) 1, (t : ℂ)⁻¹ * (t : ℂ) ^ (z - 1) = (t : ℂ) ^ (z - 2) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (lt_trans (by norm_num) ht.1).ne'
    rw [show z - 2 = (z - 1) + (-1) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_neg_one,
      mul_comm]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    integral_cpow (Or.inr ⟨by intro h; apply hz; linear_combination h,
      by rw [Set.mem_uIcc]; norm_num⟩),
    show z - 2 + 1 = z - 1 by ring, half_cpow_eq_two_cpow, Complex.ofReal_one, Complex.one_cpow]

theorem dyadicLogMean_powerWitness_ne_zero {z : ℂ} (hz1 : z.re < 1) :
    dyadicLogMean (powerWitness z) ≠ 0 := by
  have hz : z ≠ 1 := fun h => by rw [h] at hz1; simp at hz1
  rw [dyadicLogMean_powerWitness hz]
  exact div_ne_zero (one_sub_two_cpow_ne_zero hz1) (sub_ne_zero.2 hz)

/-- **RH ⟺ every continuous witness has zero logarithmic mean on the top octave**
`∫_{1/2}^1 w(t) dt/t = 0`: the Riemann hypothesis is a single linear functional on the
witness class. -/
theorem riemannHypothesis_iff_fermiNymanWitness_dyadicLogMean_eq_zero :
    RiemannHypothesis ↔ ∀ w : ℝ → ℂ, IsFermiNymanWitness w → dyadicLogMean w = 0 := by
  constructor
  · intro hRH w hw
    have hs := (riemannHypothesis_iff_fermiNymanWitness_selfSimilar.1 hRH) w hw
    obtain ⟨M, hM⟩ := bounded_of_continuous_dyadicSelfSimilar hw.1 hs
    have hmem : w ∈ boundedFermiWitnessSet := ⟨hw, M, hM⟩
    rw [boundedFermiWitnessSet_eq_dyadicLogMeanZeroSet] at hmem
    exact hmem.2.2
  · intro h
    by_contra hRH
    obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    have hwit := isFermiNymanWitness_powerWitness_of_zeta_eq_zero hζ h1 h2
    exact dyadicLogMean_powerWitness_ne_zero (by rw [Complex.conj_re]; exact h2) (h _ hwit)

end RHTower
