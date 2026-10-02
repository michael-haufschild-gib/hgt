import GaloisForLFunctions.RHTower.CCMFiniteExponentialRemainderTail
import GaloisForLFunctions.RHTower.CCMArchimedeanLogWeightEquivalence

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RHTower


private theorem log_tail_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => -(Real.log t + 2) / t)
      ((1 + Real.log x) / x ^ 2) x := by
  convert (((Real.hasDerivAt_log hx.ne').add_const 2).neg.div (hasDerivAt_id x) hx.ne') using 1 <;> try rfl
  all_goals dsimp
  all_goals field_simp [hx.ne']
  all_goals ring

private theorem log_tail_limit :
    Tendsto (fun x : ℝ => -(Real.log x + 2) / x) atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hi : Tendsto (fun x : ℝ => 2 / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul (2 : ℝ))
  simpa only [← add_div, neg_div, zero_add, neg_zero] using (hl.add hi).neg

private theorem integrable_log_tail {R : ℝ} (hR : 1 ≤ R) :
    IntegrableOn (fun x : ℝ => (1 + Real.log x) / x ^ 2) (Ioi R) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun x : ℝ => -(Real.log x + 2) / x)
    (fun x hx => log_tail_derivative (lt_of_lt_of_le (by linarith : 0 < R) hx))
    _ log_tail_limit
  intro x hx
  have hlog := Real.log_nonneg (hR.trans hx.le)
  positivity

private theorem integral_log_tail {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in Ioi R, (1 + Real.log x) / x ^ 2) = (Real.log R + 2) / R := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun x : ℝ => -(Real.log x + 2) / x)
    (fun x hx => log_tail_derivative (lt_of_lt_of_le (by linarith : 0 < R) hx))
    (integrable_log_tail hR) log_tail_limit
  simpa only [zero_sub, neg_div, neg_neg] using h

private theorem half_logarithmic_tail (g : ℝ → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) {V R : ℝ} (hR : 1 ≤ R)
    (hb : ∀ᵐ ξ : ℝ, ξ ≠ 0 → ‖g ξ‖ ≤ V / (Real.pi * |ξ|)) :
    IntegrableOn (fun ξ => suzukiLogWeight ξ * ‖g ξ‖ ^ 2) (Ioi R) ∧
      (∫ ξ in Ioi R, suzukiLogWeight ξ * ‖g ξ‖ ^ 2) ≤
        V ^ 2 * (Real.log R + 2) / (Real.pi ^ 2 * R) := by
  have hi : IntegrableOn (fun ξ : ℝ => (V / Real.pi) ^ 2 *
      ((1 + Real.log ξ) / ξ ^ 2)) (Ioi R) := (integrable_log_tail hR).const_mul _
  have hcmp : ∀ᵐ ξ : ℝ ∂volume.restrict (Ioi R),
      suzukiLogWeight ξ * ‖g ξ‖ ^ 2 ≤ (V / Real.pi) ^ 2 * ((1 + Real.log ξ) / ξ ^ 2) := by
    filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioi] with ξ hξ hx
    have hξpos : 0 < ξ := (zero_lt_one.trans_le hR).trans hx
    have hlog : 0 ≤ Real.log ξ := Real.log_nonneg (hR.trans hx.le)
    have h := hξ hξpos.ne'
    rw [abs_of_pos hξpos] at h
    have hs : ‖g ξ‖ ^ 2 ≤ (V / (Real.pi * ξ)) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) h
    rw [suzukiLogWeight, abs_of_pos hξpos, max_eq_left hlog]
    calc
      _ ≤ (1 + Real.log ξ) * (V / (Real.pi * ξ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hgi : IntegrableOn (fun ξ => suzukiLogWeight ξ * ‖g ξ‖ ^ 2) (Ioi R) := by
    apply hi.mono' (measurable_suzukiLogWeight.aestronglyMeasurable.mul (hg.norm.pow 2)).restrict
    filter_upwards [hcmp] with ξ hξ
    change ‖suzukiLogWeight ξ * ‖g ξ‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (suzukiLogWeight_nonneg ξ) (sq_nonneg _))]
    exact hξ
  refine ⟨hgi, (integral_mono_ae hgi hi hcmp).trans_eq ?_⟩
  rw [integral_const_mul, integral_log_tail hR]
  ring

private theorem log_weight_band {R ξ : ℝ} (hR : 1 ≤ R) (hξ : ξ ∈ centralInterval R) :
    suzukiLogWeight ξ ≤ 1 + Real.log R := by
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have habs : |ξ| ≤ R := abs_le.mpr hξ
  have hlog : Real.log |ξ| ≤ Real.log R := by
    by_cases hzero : ξ = 0
    · simpa [hzero] using hlogR
    · exact Real.log_le_log (abs_pos.mpr hzero) habs
  exact add_le_add (le_refl 1) (max_le hlog hlogR)

/-- The certified inverse-frequency envelope gives an exact logarithmic
Fourier energy bound and proves its integrability simultaneously. -/
theorem CCMFiniteExponentialBudget.logarithmic_energy
    {f : SoninL2} {V R : ℝ} (hf : CCMFiniteExponentialBudget f V) (hR : 1 ≤ R) :
    Integrable (suzukiHlogDensity f) ∧
      suzukiHlogMoment f ≤ (1 + Real.log R) * ‖f‖ ^ 2 +
        2 * V ^ 2 * (Real.log R + 2) / (Real.pi ^ 2 * R) := by
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F := fun ξ : ℝ => suzukiLogWeight ξ * ‖g ξ‖ ^ 2
  have hg : AEStronglyMeasurable g (volume : Measure ℝ) := (Lp.memLp (fourierUnitary f)).1
  have hF : AEStronglyMeasurable F (volume : Measure ℝ) :=
    measurable_suzukiLogWeight.aestronglyMeasurable.mul (hg.norm.pow 2)
  have hnonneg (ξ : ℝ) : 0 ≤ F ξ := mul_nonneg (suzukiLogWeight_nonneg ξ) (sq_nonneg _)
  have hb : ∀ᵐ ξ : ℝ, ξ ≠ 0 → ‖g ξ‖ ≤ V / (Real.pi * |ξ|) := hf.ae_norm_fourier_le
  have hn : ∀ᵐ ξ : ℝ, ξ ≠ 0 → ‖g (-ξ)‖ ≤ V / (Real.pi * |ξ|) := by
    have ht := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hb
    filter_upwards [ht] with ξ hξ
    intro hξ0
    simpa only [abs_neg] using hξ (neg_ne_zero.mpr hξ0)
  obtain ⟨hpi, hp⟩ := half_logarithmic_tail g hg hR hb
  obtain ⟨hmni, hmn⟩ := half_logarithmic_tail (fun ξ => g (-ξ))
    (hg.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))) hR hn
  have hmi : IntegrableOn F (Iio (-R)) := by
    have hneg : IntegrableOn (fun ξ : ℝ => suzukiLogWeight (-ξ) * ‖g (- -ξ)‖ ^ 2)
        (Iio (-R)) := IntegrableOn.comp_neg_Iio (c := -R)
          (show IntegrableOn (fun ξ => suzukiLogWeight ξ * ‖g (-ξ)‖ ^ 2)
            (Ioi (- -R)) from by simpa only [neg_neg] using hmni)
    simpa only [F, suzukiLogWeight, abs_neg, neg_neg] using hneg
  have hm : (∫ ξ in Iio (-R), F ξ) ≤ V ^ 2 * (Real.log R + 2) / (Real.pi ^ 2 * R) := by
    have heq : (fun ξ => suzukiLogWeight ξ * ‖g (-ξ)‖ ^ 2) = fun ξ => F (-ξ) := by
      funext ξ
      simp only [F, suzukiLogWeight, abs_neg]
    rw [heq, integral_comp_neg_Ioi, integral_Iic_eq_integral_Iio] at hmn
    exact hmn
  have hi : Integrable (fun ξ => ‖g ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hlowcmp : ∀ᵐ ξ : ℝ ∂volume.restrict (centralInterval R),
      F ξ ≤ (1 + Real.log R) * ‖g ξ‖ ^ 2 := by
    filter_upwards [ae_restrict_mem (measurableSet_centralInterval R)] with ξ hξ
    exact mul_le_mul_of_nonneg_right (log_weight_band hR hξ) (sq_nonneg _)
  have hli : IntegrableOn F (centralInterval R) := by
    apply ((hi.const_mul (1 + Real.log R)).integrableOn).mono' hF.restrict
    filter_upwards [hlowcmp] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ξ)]
    exact hξ
  have hlow : (∫ ξ in centralInterval R, F ξ) ≤ (1 + Real.log R) * ‖f‖ ^ 2 := by
    calc
      _ ≤ ∫ ξ in centralInterval R, (1 + Real.log R) * ‖g ξ‖ ^ 2 :=
        integral_mono_ae hli (hi.const_mul _).integrableOn hlowcmp
      _ = (1 + Real.log R) * ∫ ξ in centralInterval R, ‖g ξ‖ ^ 2 := integral_const_mul _ _
      _ ≤ (1 + Real.log R) * ∫ ξ : ℝ, ‖g ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hi (Eventually.of_forall fun ξ => sq_nonneg _))
          (by have hlog := Real.log_nonneg hR; positivity)
      _ = _ := by rw [← norm_sq_eq_integral, fourierUnitary.norm_map]
  have hset : (centralInterval R)ᶜ = Iio (-R) ∪ Ioi R := by
    ext ξ
    simp only [centralInterval, mem_compl_iff, mem_Icc, not_and_or,
      not_le, mem_union, mem_Iio, mem_Ioi]
  have hci : IntegrableOn F (centralInterval R)ᶜ := by
    rw [hset]
    exact hmi.union hpi
  have hfi : Integrable F := by
    have h := hli.union hci
    simpa only [union_compl_self, integrableOn_univ] using h
  have hd : Disjoint (Iio (-R)) (Ioi R) := by
    apply disjoint_left.mpr
    intro ξ hξ hξ'
    have h1 : ξ < -R := hξ
    have h2 : R < ξ := hξ'
    linarith
  refine ⟨hfi, ?_⟩
  change (∫ ξ, F ξ) ≤ _
  rw [← integral_add_compl (measurableSet_centralInterval R) hfi, hset,
    setIntegral_union hd measurableSet_Ioi hmi hpi]
  exact (add_le_add hlow (add_le_add hm hp)).trans_eq (by ring)

/-- Every literal odd remainder iterate has finite logarithmic energy,
with its actual certified budget retained in the quantitative tail. -/
theorem ccmNormalizedWeilRemainder_odd_iterate_logarithmic_energy
    (a : SuzukiPositiveAperture) (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    let f : SoninL2 := (((ccmNormalizedWeilRemainder a)^[n])
      ((1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) -
        ccmPolarApertureVector a (-1 / 2))) : SoninL2)
    Integrable (suzukiHlogDensity f) ∧
      suzukiHlogMoment f ≤ (1 + Real.log R) * ‖f‖ ^ 2 +
        2 * ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * Real.exp (a.1 / 2)) ^ 2 *
          (Real.log R + 2) / (Real.pi ^ 2 * R) :=
  (ccmNormalizedWeilRemainder_odd_iterate_budget a n).logarithmic_energy hR

end RHTower
end
