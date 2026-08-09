import GaloisForLFunctions.RHTower.MellinVanishingCriterion

/-!
# Balance is exactly what the detector sees: the Báez-Duarte family is maximal among dilates

The Mellin-vanishing template of `MellinVanishingCriterion` applies to any family in the carrier whose
transforms vanish at the detector points.  The natural pool of candidates is the *fractional-part dilates*

`fractDilate θ : u ↦ {θu}/u`,

all of which lie in the carrier — the bound `‖{θu}/u‖ ≤ 1/u` needs no cancellation.  This file computes
their transforms and draws the consequence.

The single dilate is *not* annihilated.  Splitting the ray at `1` and using the corpus's full-ray identity
`∫_0^∞ {θu} u^{-(ρ+1)} du = θ^ρ·(−ζ(ρ)/ρ)` together with the elementary head
`∫_0^1 {θu} u^{-(ρ+1)} du = θ/(1−ρ)` gives

`⟪bdDetector (1−ρ), fractDilate θ⟫ = θ^ρ·(−ζ(ρ)/ρ) − θ/(1−ρ)`,

which at a zero of `ζ` is `−θ/(1−ρ) ≠ 0`.  Hence a finite combination `∑ cₖ · fractDilate θₖ` is killed by
the detector **iff** `∑ cₖ θₖ = 0` — the *balance* condition — and that holds regardless of which zero one
looks at, so one hypothetical off-line zero already forces it.

Two conclusions.

* `bdGen_eq_fractDilate_sub` — Báez-Duarte's generator is the balanced two-term combination
  `fractDilate θ − θ · fractDilate 1`.  So the Báez-Duarte span sits inside the dilate span as exactly the
  balanced part.
* `not_mellinAnnihilated_of_sum_ne_zero` — an *unbalanced* combination is never annihilated, so it cannot be
  added to a Mellin-annihilated family.  **Within the fractional-part dilates, the Báez-Duarte family is
  maximal:** enlarging the span this way is impossible, and a genuinely different family has to come from
  outside the class (arithmetic coefficients, say).
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The fractional-part dilate `u ↦ {θu}/u`, in the carrier coordinate. -/
def fractDilateFun (θ : ℝ) : ℝ → ℂ := fun u => ((Int.fract (θ * u) : ℝ) : ℂ) * ((u : ℂ))⁻¹

theorem memLp_fractDilateFun (θ : ℝ) : MemLp (fractDilateFun θ) 2 bdMeasure := by
  refine memLp_two_bdMeasure_of_sq_le ?_ (C := 1) (b := -2) (by norm_num) ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact (measurable_fract_complex.comp (measurable_const_mul θ)).mul
      (Complex.measurable_ofReal).inv
  · intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hb : ‖fractDilateFun θ u‖ ≤ u⁻¹ := by
      rw [fractDilateFun, norm_mul, norm_inv, Complex.norm_real u, Real.norm_eq_abs,
        abs_of_pos hu0]
      calc ‖((Int.fract (θ * u) : ℝ) : ℂ)‖ * u⁻¹ ≤ 1 * u⁻¹ :=
            mul_le_mul_of_nonneg_right (norm_fract_le _) (by positivity)
        _ = u⁻¹ := one_mul _
    calc ‖fractDilateFun θ u‖ ^ 2 ≤ (u⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = 1 * u ^ (-2 : ℝ) := by rw [inv_sq_eq_rpow hu0, one_mul]

/-- The dilate as an element of the carrier. -/
def fractDilate (θ : ℝ) : BDCarrier := (memLp_fractDilateFun θ).toLp _

/-- **Báez-Duarte's generator is the balanced two-term dilate combination.** -/
theorem bdGen_eq_fractDilate_sub (θ : ℝ) :
    bdGen θ = fractDilate θ - (θ : ℂ) • fractDilate 1 := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [(memLp_bdGenFun θ).coeFn_toLp, (memLp_fractDilateFun θ).coeFn_toLp,
    (memLp_fractDilateFun 1).coeFn_toLp,
    MeasureTheory.Lp.coeFn_sub (fractDilate θ) ((θ : ℂ) • fractDilate 1),
    MeasureTheory.Lp.coeFn_smul (θ : ℂ) (fractDilate 1)] with u hu hu1 hu2 hsub hsmul
  rw [bdGen, hu, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, fractDilate, fractDilate, hu1, hu2,
    bdGenFun, fractDilateFun, fractDilateFun, one_mul, smul_eq_mul]
  ring

/-- The head of the ray integral for a dilate: on `(0,1]` the fractional part is linear. -/
theorem integral_Ioc_zero_one_fract_dilate_cpow {w : ℂ} (hw : w.re < 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    (∫ u in Ioc (0 : ℝ) 1, ((Int.fract (θ * u) : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1)))
      = (θ : ℂ) * (1 / (1 - w)) := by
  have hbase : (∫ u in Ioc (0 : ℝ) 1, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1)))
      = 1 / (1 - w) := integral_Ioc_zero_one_fract_cpow hw
  have hcongr : ∀ u ∈ Ioo (0 : ℝ) 1,
      ((Int.fract (θ * u) : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1))
        = (θ : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1))) := by
    intro u hu
    have hfr1 : Int.fract (θ * u) = θ * u := by
      refine Int.fract_eq_self.mpr ⟨(mul_pos hθ0 hu.1).le, ?_⟩
      calc θ * u < θ * 1 := mul_lt_mul_of_pos_left hu.2 hθ0
        _ = θ := mul_one θ
        _ ≤ 1 := hθ1
    have hfr2 : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
    rw [hfr1, hfr2]
    push_cast
    ring
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr, integral_const_mul,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, hbase]

/-- **The transform of a single dilate.**  Not annihilated: the head term survives. -/
theorem inner_bdDetector_fractDilate {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    inner ℂ (bdDetector (one_sub_re_lt hρ)) (fractDilate θ)
      = ((θ : ℝ) : ℂ) ^ ρ * (-(riemannZeta ρ / ρ)) - (θ : ℂ) * (1 / (1 - ρ)) := by
  have hρ0 : 0 < ρ.re := by linarith
  set F : ℝ → ℂ := fun u => ((Int.fract (θ * u) : ℝ) : ℂ) * (u : ℂ) ^ (-(ρ + 1)) with hF
  have hI : IntegrableOn F (Ioi 0) := integrableOn_Ioi_zero_fract_dilate_cpow hρ0 hρ1 hθ0
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hsplit : (∫ u in Ioi (0:ℝ), F u)
      = (∫ u in Ioc (0:ℝ) 1, F u) + ∫ u in Ioi (1:ℝ), F u := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hI.mono_set (by rw [← hunion]; exact Set.subset_union_left))
      (hI.mono_set (by rw [← hunion]; exact Set.subset_union_right))
  have htail : (∫ u in Ioi (1:ℝ), F u)
      = ((θ : ℝ) : ℂ) ^ ρ * (-(riemannZeta ρ / ρ)) - (θ : ℂ) * (1 / (1 - ρ)) := by
    have hfull := integral_Ioi_zero_fract_dilate_cpow hρ0 hρ1 hθ0
    rw [hF] at hsplit
    rw [hsplit, integral_Ioc_zero_one_fract_dilate_cpow hρ1 hθ0 hθ1] at hfull
    linear_combination hfull
  rw [inner_bdDetector]
  have hcongr : ∀ᵐ u ∂bdMeasure,
      (fractDilate θ : ℝ → ℂ) u * (u : ℂ) ^ ((1 - ρ) - 1) = F u := by
    filter_upwards [(memLp_fractDilateFun θ).coeFn_toLp, ae_restrict_mem measurableSet_Ioi]
      with u hu hu1
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu1)
    have hune : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu0)
    rw [fractDilate, hu, fractDilateFun, hF, mul_assoc, ← Complex.cpow_neg_one,
      ← Complex.cpow_add _ _ hune]
    congr 2
    ring
  rw [show (∫ u in Ioi (1:ℝ), (fractDilate θ : ℝ → ℂ) u * (u : ℂ) ^ ((1 - ρ) - 1))
      = ∫ u in Ioi (1:ℝ), F u from integral_congr_ae hcongr]
  exact htail

/-- At a zero of `ζ` only the head term survives. -/
theorem inner_bdDetector_fractDilate_of_zero {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    inner ℂ (bdDetector (one_sub_re_lt hρ)) (fractDilate θ) = -((θ : ℂ) * (1 / (1 - ρ))) := by
  rw [inner_bdDetector_fractDilate hρ hρ1 hθ0 hθ1, hzero]
  simp

/-- **Balance is exactly the annihilation condition.**  A finite combination of dilates is killed by the
detector at a zero precisely when its weighted mass `∑ cₖ θₖ` vanishes. -/
theorem inner_bdDetector_sum_fractDilate {n : ℕ} {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) (θ : Fin n → ℝ) (hθ : ∀ k, 0 < θ k ∧ θ k ≤ 1) (c : Fin n → ℂ) :
    inner ℂ (bdDetector (one_sub_re_lt hρ)) (∑ k, c k • fractDilate (θ k))
      = -((∑ k, c k * ((θ k : ℝ) : ℂ)) * (1 / (1 - ρ))) := by
  rw [inner_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_bdDetector_fractDilate_of_zero hρ hρ1 hzero (hθ k).1 (hθ k).2]
  ring

/-- **The Báez-Duarte family is maximal among the dilates.**  An unbalanced combination is not annihilated
at any zero, so it can never be adjoined to a Mellin-annihilated family. -/
theorem not_inner_bdDetector_sum_fractDilate_eq_zero {n : ℕ} {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (hρ1 : ρ.re < 1) (hzero : riemannZeta ρ = 0) (θ : Fin n → ℝ)
    (hθ : ∀ k, 0 < θ k ∧ θ k ≤ 1) (c : Fin n → ℂ)
    (hbal : ∑ k, c k * ((θ k : ℝ) : ℂ) ≠ 0) :
    inner ℂ (bdDetector (one_sub_re_lt hρ)) (∑ k, c k • fractDilate (θ k)) ≠ 0 := by
  rw [inner_bdDetector_sum_fractDilate hρ hρ1 hzero θ hθ c]
  have hne : (1 : ℂ) - ρ ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) - ρ).re = 0 := by rw [h, Complex.zero_re]
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith
  simp only [ne_eq, neg_eq_zero, mul_eq_zero, one_div, inv_eq_zero]
  push Not
  exact ⟨hbal, hne⟩

end RHTower

end
