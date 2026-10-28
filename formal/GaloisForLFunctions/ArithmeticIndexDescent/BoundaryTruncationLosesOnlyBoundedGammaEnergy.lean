import GaloisForLFunctions.ArithmeticIndexDescent.TruncatedGammaWeightsHaveLogarithmicMass
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Bounded boundary leakage of the exact Gamma weight

The square reserve of a truncated Schur weight is supported where exactly one
argument lies in the truncation interval. Four integrable power rectangles
bound this leakage uniformly. The logarithmically growing mass then shows that
the original Gamma operator has sharp norm pi/2.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProduct
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

/-- The reciprocal square bound gives a pointwise inverse-square-root majorant. -/
theorem gammaBoundarySchurWeight_le_rpow {t : ℝ} (ht : 0 < t) :
    gammaBoundarySchurWeight t ≤ t ^ (-1 / 2 : ℝ) := by
  have hsq : (t ^ (-1 / 2 : ℝ)) ^ 2 = t⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num [Real.rpow_neg_one]
  have hw := gammaBoundarySchurWeight_sq_le_inv ht
  have hp := Real.rpow_nonneg ht.le (-1 / 2 : ℝ)
  nlinarith only [hsq, hw, hp]

private theorem half_weighted_kernel_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    archLevyDensity (s + t) * gammaBoundarySchurWeight s *
      gammaBoundarySchurWeight t / 2 ≤ s ^ (-3 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) := by
  have hk : archLevyDensity (s + t) ≤ 2 / (s + t) := by
    simpa only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul] using
      ccmGammaTranslationDensity_le_carleman (add_pos hs ht)
  have hhalf : archLevyDensity (s + t) / 2 ≤ s⁻¹ := by
    have hsum : (s + t)⁻¹ ≤ s⁻¹ := inv_anti₀ hs (by linarith only [ht])
    have hmid : archLevyDensity (s + t) / 2 ≤ (s + t)⁻¹ := by
      calc
        _ ≤ (2 / (s + t)) / 2 := div_le_div_of_nonneg_right hk (by norm_num)
        _ = _ := by ring
    exact hmid.trans hsum
  have hweight := mul_le_mul (gammaBoundarySchurWeight_le_rpow hs)
    (gammaBoundarySchurWeight_le_rpow ht) (gammaBoundarySchurWeight_pos ht).le
    (Real.rpow_nonneg hs.le _)
  calc
    _ = (archLevyDensity (s + t) / 2) *
        (gammaBoundarySchurWeight s * gammaBoundarySchurWeight t) := by ring
    _ ≤ s⁻¹ * (s ^ (-1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ)) :=
      mul_le_mul hhalf hweight
        (mul_nonneg (gammaBoundarySchurWeight_pos hs).le (gammaBoundarySchurWeight_pos ht).le)
        (inv_nonneg.mpr hs.le)
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hs]
      congr 2
      ring

private def leakageHead (a t : ℝ) : ℝ :=
  (Ioc 0 a).indicator (fun u : ℝ => u ^ (-1 / 2 : ℝ)) t

private def leakageTail (a t : ℝ) : ℝ :=
  (Ioi a).indicator (fun u : ℝ => u ^ (-3 / 2 : ℝ)) t

private theorem leakageHead_nonneg (a t : ℝ) : 0 ≤ leakageHead a t := by
  by_cases ht : t ∈ Ioc 0 a
  · rw [leakageHead, indicator_of_mem ht]
    exact Real.rpow_nonneg ht.1.le _
  · simp only [leakageHead, indicator_of_notMem ht, le_refl]

private theorem leakageTail_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) :
    0 ≤ leakageTail a t := by
  by_cases ht : t ∈ Ioi a
  · rw [leakageTail, indicator_of_mem ht]
    exact Real.rpow_nonneg (ha.trans ht).le _
  · simp only [leakageTail, indicator_of_notMem ht, le_refl]

private theorem integrable_leakageHead {a : ℝ} (ha : 0 < a) :
    Integrable (leakageHead a) μ₊ := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2))
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr hi).mono_measure Measure.restrict_le_self

private theorem integrable_leakageTail {a : ℝ} (ha : 0 < a) :
    Integrable (leakageTail a) μ₊ := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) ha
  exact ((integrable_indicator_iff measurableSet_Ioi).mpr hi).mono_measure Measure.restrict_le_self

private theorem integral_leakageHead {a : ℝ} (ha : 0 < a) :
    (∫ t, leakageHead a t ∂μ₊) = 2 * a ^ (1 / 2 : ℝ) := by
  rw [leakageHead, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    show Ioc (0 : ℝ) a ∩ Ioi 0 = Ioc 0 a from inter_eq_left.mpr (fun _ ht => ht.1),
    ← intervalIntegral.integral_of_le ha.le,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num
  ring

private theorem integral_leakageTail {a : ℝ} (ha : 0 < a) :
    (∫ t, leakageTail a t ∂μ₊) = 2 * a ^ (-1 / 2 : ℝ) := by
  rw [leakageTail, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    show Ioi a ∩ Ioi (0 : ℝ) = Ioi a from inter_eq_left.mpr (fun _ ht => ha.trans ht),
    integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) ha]
  norm_num
  ring

private def leakageRectangle (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  leakageTail a p.1 * leakageHead a p.2

private theorem leakageRectangle_nonneg {a : ℝ} (ha : 0 < a) (p : ℝ × ℝ) :
    0 ≤ leakageRectangle a p :=
  mul_nonneg (leakageTail_nonneg ha _) (leakageHead_nonneg _ _)

private theorem integrable_leakageRectangle {a : ℝ} (ha : 0 < a) :
    Integrable (leakageRectangle a) (μ₊.prod μ₊) :=
  (integrable_leakageTail ha).mul_prod (integrable_leakageHead ha)

private theorem integral_leakageRectangle {a : ℝ} (ha : 0 < a) :
    (∫ p, leakageRectangle a p ∂(μ₊.prod μ₊)) = 4 := by
  rw [leakageRectangle, integral_prod_mul, integral_leakageTail ha, integral_leakageHead ha,
    show (2 * a ^ (-1 / 2 : ℝ)) * (2 * a ^ (1 / 2 : ℝ)) =
      4 * (a ^ (-1 / 2 : ℝ) * a ^ (1 / 2 : ℝ)) by ring, ← Real.rpow_add ha]
  norm_num

private def leakageMajorant (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  leakageRectangle a p + leakageRectangle a p.swap +
    leakageRectangle 1 p + leakageRectangle 1 p.swap

private theorem integrable_leakageMajorant {a : ℝ} (ha : 0 < a) :
    Integrable (leakageMajorant a) (μ₊.prod μ₊) :=
  (((integrable_leakageRectangle ha).add (integrable_leakageRectangle ha).swap).add
    (integrable_leakageRectangle zero_lt_one)).add (integrable_leakageRectangle zero_lt_one).swap

private theorem integral_leakageMajorant {a : ℝ} (ha : 0 < a) :
    (∫ p, leakageMajorant a p ∂(μ₊.prod μ₊)) = 16 := by
  have haI := integrable_leakageRectangle ha
  have h1I := integrable_leakageRectangle zero_lt_one
  have haS : Integrable (fun p : ℝ × ℝ => leakageRectangle a p.swap) (μ₊.prod μ₊) := haI.swap
  have h1S : Integrable (fun p : ℝ × ℝ => leakageRectangle 1 p.swap) (μ₊.prod μ₊) := h1I.swap
  have hA : Integrable (fun p : ℝ × ℝ => leakageRectangle a p + leakageRectangle a p.swap)
      (μ₊.prod μ₊) := haI.add haS
  have hB : Integrable (fun p : ℝ × ℝ => leakageRectangle a p + leakageRectangle a p.swap +
      leakageRectangle 1 p) (μ₊.prod μ₊) := hA.add h1I
  have haswap : (∫ p, leakageRectangle a p.swap ∂(μ₊.prod μ₊)) = 4 := by
    rw [integral_prod_swap, integral_leakageRectangle ha]
  have h1swap : (∫ p, leakageRectangle 1 p.swap ∂(μ₊.prod μ₊)) = 4 := by
    rw [integral_prod_swap, integral_leakageRectangle zero_lt_one]
  rw [leakageMajorant, integral_add hB h1S, integral_add hA h1I, integral_add haI haS,
    integral_leakageRectangle ha, integral_leakageRectangle zero_lt_one, haswap, h1swap]
  norm_num

private theorem leakageMajorant_nonneg {a : ℝ} (ha : 0 < a) (p : ℝ × ℝ) :
    0 ≤ leakageMajorant a p :=
  add_nonneg (add_nonneg (add_nonneg (leakageRectangle_nonneg ha p)
    (leakageRectangle_nonneg ha p.swap)) (leakageRectangle_nonneg zero_lt_one p))
    (leakageRectangle_nonneg zero_lt_one p.swap)

private theorem leakageMajorant_swap (a : ℝ) (p : ℝ × ℝ) :
    leakageMajorant a p.swap = leakageMajorant a p := by
  simp only [leakageMajorant, Prod.swap_swap]
  ring

private theorem half_kernel_le_majorant_of_mismatch {a s t : ℝ} (ha : 0 < a)
    (hs : 0 < s) (ht : 0 < t) (hsi : s ∈ Ioc a 1) (hto : t ∉ Ioc a 1) :
    archLevyDensity (s + t) * gammaBoundarySchurWeight s *
      gammaBoundarySchurWeight t / 2 ≤ leakageMajorant a (s, t) := by
  have hRa := leakageRectangle_nonneg ha (s, t)
  have hRas := leakageRectangle_nonneg ha (t, s)
  have hR1 := leakageRectangle_nonneg zero_lt_one (s, t)
  have hR1s := leakageRectangle_nonneg zero_lt_one (t, s)
  by_cases hta : t ≤ a
  · have he : leakageRectangle a (s, t) = s ^ (-3 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) := by
      simp only [leakageRectangle, leakageTail, leakageHead, indicator_of_mem hsi.1,
        indicator_of_mem (show t ∈ Ioc 0 a from ⟨ht, hta⟩)]
    have hle : archLevyDensity (s + t) * gammaBoundarySchurWeight s *
        gammaBoundarySchurWeight t / 2 ≤ leakageRectangle a (s, t) := by
      rw [he]
      exact half_weighted_kernel_le hs ht
    unfold leakageMajorant
    dsimp only [Prod.swap]
    linarith only [hle, hRas, hR1, hR1s]
  · have ht1 : 1 < t := by
      by_contra h
      exact hto ⟨lt_of_not_ge hta, le_of_not_gt h⟩
    have he : leakageRectangle 1 (t, s) = t ^ (-3 / 2 : ℝ) * s ^ (-1 / 2 : ℝ) := by
      simp only [leakageRectangle, leakageTail, leakageHead, indicator_of_mem ht1,
        indicator_of_mem (show s ∈ Ioc 0 1 from ⟨hs, hsi.2⟩)]
    have hle : archLevyDensity (s + t) * gammaBoundarySchurWeight s *
        gammaBoundarySchurWeight t / 2 ≤ leakageRectangle 1 (t, s) := by
      rw [he]
      calc
        _ = archLevyDensity (t + s) * gammaBoundarySchurWeight t *
            gammaBoundarySchurWeight s / 2 := by rw [add_comm t s]; ring
        _ ≤ _ := half_weighted_kernel_le ht hs
    unfold leakageMajorant
    dsimp only [Prod.swap]
    linarith only [hle, hRa, hRas, hR1]

private theorem literal_truncation_reserve_le {a s t : ℝ} (ha : 0 < a)
    (hs : 0 < s) (ht : 0 < t) :
    archLevyDensity (s + t) * gammaBoundarySchurWeight s * gammaBoundarySchurWeight t *
      ‖truncatedGammaWeightFun a s / (gammaBoundarySchurWeight s : ℂ) -
        truncatedGammaWeightFun a t / (gammaBoundarySchurWeight t : ℂ)‖ ^ 2 / 2 ≤
      leakageMajorant a (s, t) := by
  have hws : (gammaBoundarySchurWeight s : ℂ) ≠ 0 := by
    exact_mod_cast (gammaBoundarySchurWeight_pos hs).ne'
  have hwt : (gammaBoundarySchurWeight t : ℂ) ≠ 0 := by
    exact_mod_cast (gammaBoundarySchurWeight_pos ht).ne'
  by_cases hsi : s ∈ Ioc a 1 <;> by_cases hti : t ∈ Ioc a 1
  · simpa only [truncatedGammaWeightFun, indicator_of_mem hsi, indicator_of_mem hti,
      div_self hws, div_self hwt, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, zero_div] using leakageMajorant_nonneg ha (s, t)
  · simpa only [truncatedGammaWeightFun, indicator_of_mem hsi, indicator_of_notMem hti,
      div_self hws, zero_div, sub_zero, norm_one, one_pow, mul_one] using
      half_kernel_le_majorant_of_mismatch ha hs ht hsi hti
  · have hle := half_kernel_le_majorant_of_mismatch ha ht hs hti hsi
    rw [← leakageMajorant_swap a (s, t)]
    simpa only [truncatedGammaWeightFun, indicator_of_notMem hsi, indicator_of_mem hti,
      zero_div, div_self hwt, zero_sub, norm_neg, norm_one, one_pow, mul_one,
      add_comm t s, mul_right_comm _ (gammaBoundarySchurWeight t)
        (gammaBoundarySchurWeight s)] using hle
  · simpa only [truncatedGammaWeightFun, indicator_of_notMem hsi, indicator_of_notMem hti,
      zero_div, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero] using leakageMajorant_nonneg ha (s, t)

/-- The discarded boundary interaction is bounded independently of the inner cutoff. -/
theorem truncatedGammaWeight_reserve_le {a : ℝ} (ha : 0 < a) :
    (∫ p, gammaBoundaryPairReserveDensity (truncatedGammaWeight a ha)
      (truncatedGammaWeight a ha) p ∂(μ₊.prod μ₊)) ≤ 16 := by
  have hpos : ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊), 0 < p.1 ∧ 0 < p.2 := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hfirst : ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊),
      truncatedGammaWeight a ha p.1 = truncatedGammaWeightFun a p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (truncatedGammaWeight_coeFn ha)
  have hsecond : ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊),
      truncatedGammaWeight a ha p.2 = truncatedGammaWeightFun a p.2 :=
    Measure.quasiMeasurePreserving_snd.ae (truncatedGammaWeight_coeFn ha)
  rw [← integral_leakageMajorant ha]
  apply integral_mono_ae (integrable_gammaBoundaryPairReserveDensity _ _)
    (integrable_leakageMajorant ha)
  filter_upwards [hpos, hfirst, hsecond] with p hp hf hg
  unfold gammaBoundaryPairReserveDensity
  rw [hf, hg]
  exact literal_truncation_reserve_le ha hp.1 hp.2

/-- Truncated weights lose only a bounded amount from the critical Rayleigh value. -/
theorem truncatedGammaWeight_rayleigh_lower {a : ℝ} (ha : 0 < a) :
    (Real.pi / 2) * ‖truncatedGammaWeight a ha‖ ^ 2 - 16 ≤
      (inner ℂ (truncatedGammaWeight a ha)
        (ccmGammaBoundaryCLM (truncatedGammaWeight a ha))).re := by
  have h := truncatedGammaWeight_reserve_le ha
  rw [← gammaBoundary_quadratic_deficit] at h
  linarith only [h]

/-- The existing Gamma boundary operator has the sharp norm pi/2. -/
theorem norm_ccmGammaBoundaryCLM_eq_pi_half : ‖ccmGammaBoundaryCLM‖ = Real.pi / 2 := by
  apply le_antisymm norm_ccmGammaBoundaryCLM_le_pi_half
  by_contra hnot
  have hd : 0 < Real.pi / 2 - ‖ccmGammaBoundaryCLM‖ := sub_pos.mpr (lt_of_not_ge hnot)
  let c : ℝ := Real.exp (-1) / 2
  have hc : 0 < c := div_pos (Real.exp_pos _) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (16 / ((Real.pi / 2 - ‖ccmGammaBoundaryCLM‖) * c))
  let a : ℝ := Real.exp (-((n : ℝ) + 1))
  have ha : 0 < a := Real.exp_pos _
  let f : SuzukiPositiveL2 := truncatedGammaWeight a ha
  have hmass : c * ((n : ℝ) + 1) ≤ ‖f‖ ^ 2 := norm_truncatedGammaWeight_exp_sq_ge n
  have hupper : (inner ℂ f (ccmGammaBoundaryCLM f)).re ≤
      ‖ccmGammaBoundaryCLM‖ * ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ f (ccmGammaBoundaryCLM f)‖ := Complex.re_le_norm _
      _ ≤ ‖f‖ * ‖ccmGammaBoundaryCLM f‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖ccmGammaBoundaryCLM‖ * ‖f‖) :=
        mul_le_mul_of_nonneg_left (ccmGammaBoundaryCLM.le_opNorm f) (norm_nonneg _)
      _ = _ := by ring
  have hlower : (Real.pi / 2) * ‖f‖ ^ 2 - 16 ≤
      (inner ℂ f (ccmGammaBoundaryCLM f)).re := truncatedGammaWeight_rayleigh_lower ha
  have hbudget : (Real.pi / 2 - ‖ccmGammaBoundaryCLM‖) * ‖f‖ ^ 2 ≤ 16 := by
    nlinarith only [hlower, hupper]
  have hlarge : 16 < (n : ℝ) * ((Real.pi / 2 - ‖ccmGammaBoundaryCLM‖) * c) :=
    (div_lt_iff₀ (mul_pos hd hc)).mp hn
  have hcharge := mul_le_mul_of_nonneg_left hmass hd.le
  nlinarith only [hbudget, hlarge, hcharge, mul_pos hd hc]

/-- Explicit boundary truncations approach the critical quadratic value from below. -/
theorem exists_truncatedGammaWeight_near_critical {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, let f := truncatedGammaWeight (Real.exp (-((n : ℝ) + 1))) (Real.exp_pos _)
      f ≠ 0 ∧ (Real.pi / 2 - δ) * ‖f‖ ^ 2 < (inner ℂ f (ccmGammaBoundaryCLM f)).re := by
  let c : ℝ := Real.exp (-1) / 2
  have hc : 0 < c := div_pos (Real.exp_pos _) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (16 / (δ * c))
  refine ⟨n, ?_⟩
  dsimp only
  let f := truncatedGammaWeight (Real.exp (-((n : ℝ) + 1))) (Real.exp_pos _)
  have hmass : c * ((n : ℝ) + 1) ≤ ‖f‖ ^ 2 := norm_truncatedGammaWeight_exp_sq_ge n
  have hf : f ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hmass
    exact (not_le_of_gt (mul_pos hc (by positivity))) hmass
  refine ⟨hf, ?_⟩
  have hlarge : 16 < (n : ℝ) * (δ * c) := (div_lt_iff₀ (mul_pos hδ hc)).mp hn
  have hcharge := mul_le_mul_of_nonneg_left hmass hδ.le
  have hlower : (Real.pi / 2) * ‖f‖ ^ 2 - 16 ≤
      (inner ℂ f (ccmGammaBoundaryCLM f)).re := truncatedGammaWeight_rayleigh_lower (Real.exp_pos _)
  nlinarith only [hlarge, hcharge, hlower, mul_pos hδ hc]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.truncatedGammaWeight_reserve_le
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.truncatedGammaWeight_rayleigh_lower
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_ccmGammaBoundaryCLM_eq_pi_half
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_truncatedGammaWeight_near_critical
