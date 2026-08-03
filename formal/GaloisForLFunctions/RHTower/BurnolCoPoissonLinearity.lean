import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource

/-!
# Linearity of the co-Poisson sum in the seed

The co-Poisson sum is linear in its seed: scaling is unconditional, and additivity holds whenever
the two summability and correction-integrability conditions are available.  For the sub-window
reciprocal seeds the correction integrand is literally the indicator of the inverted window, so both
conditions are explicit.

Consequently the Mellin transform of any finite combination of sub-window co-Poisson values is the
corresponding combination of `(d^(-w) - c^(-w)) zeta(w)/w`, and in particular vanishes at every zeta
zero.  The annihilation at a zero is therefore a property of the whole span, not of one seed.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- **Scaling the seed scales the co-Poisson sum.** -/
theorem burnolCoPoissonRightSum_const_smul (l : ℂ) (g : ℝ → ℂ) (t : ℝ) :
    burnolCoPoissonRightSum (fun v => l * g v) t = l * burnolCoPoissonRightSum g t := by
  rw [burnolCoPoissonRightSum, burnolCoPoissonRightSum]
  have hsum : (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * (l * g (|t| / ((n + 1 : ℕ) : ℝ)))) =
      l * ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have hint : (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * (l * g y⁻¹))) =
      l * ∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => by ring
  rw [hsum, hint]
  ring

/-- **Adding seeds adds the co-Poisson sums.** -/
theorem burnolCoPoissonRightSum_add {b : ℝ} (hb : 0 < b) {g h : ℝ → ℂ}
    (hgs : Function.support g ⊆ Icc b b⁻¹) (hhs : Function.support h ⊆ Icc b b⁻¹)
    (hgi : IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ)⁻¹ * g y⁻¹) (Ioi 0))
    (hhi : IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ)⁻¹ * h y⁻¹) (Ioi 0)) (t : ℝ) :
    burnolCoPoissonRightSum (fun v => g v + h v) t =
      burnolCoPoissonRightSum g t + burnolCoPoissonRightSum h t := by
  rw [burnolCoPoissonRightSum, burnolCoPoissonRightSum, burnolCoPoissonRightSum]
  have hsum : (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        (g (|t| / ((n + 1 : ℕ) : ℝ)) + h (|t| / ((n + 1 : ℕ) : ℝ)))) =
      (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|t| / ((n + 1 : ℕ) : ℝ))) +
        ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * h (|t| / ((n + 1 : ℕ) : ℝ)) := by
    rw [← Summable.tsum_add (burnolCoPoissonRightSum_summable hb hgs t)
      (burnolCoPoissonRightSum_summable hb hhs t)]
    exact tsum_congr fun n => by ring
  have hint : (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * (g y⁻¹ + h y⁻¹))) =
      (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹)) +
        ∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * h y⁻¹) := by
    rw [← integral_add hgi hhi]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => by ring
  rw [hsum, hint]
  ring

/-! ## The correction integrand of a sub-window seed -/

theorem correction_integrand_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {y : ℝ} (hy : 0 < y) :
    ((y : ℝ) : ℂ)⁻¹ * coPoissonSubWindowSeed c d y⁻¹ =
      Set.indicator (Icc d⁻¹ c⁻¹) (fun _ : ℝ => (1 : ℂ)) y := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
  have hiff : y⁻¹ ∈ Icc c d ↔ y ∈ Icc d⁻¹ c⁻¹ := by
    rw [mem_Icc, mem_Icc, le_inv_comm₀ hc hy, inv_le_comm₀ hy hd, and_comm]
  by_cases h : y ∈ Icc d⁻¹ c⁻¹
  · rw [Set.indicator_of_mem h, coPoissonSubWindowSeed_of_mem (hiff.mpr h),
      Complex.ofReal_inv, inv_inv, inv_mul_cancel₀ hyne]
  · rw [Set.indicator_of_notMem h,
      coPoissonSubWindowSeed_of_notMem (fun hcon => h (hiff.mp hcon)), mul_zero]

/-- **The correction integrand of a sub-window seed is integrable.**  On the positive ray it is the
indicator of the inverted window. -/
theorem integrableOn_correction_coPoissonSubWindowSeed {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ)⁻¹ * coPoissonSubWindowSeed c d y⁻¹) (Ioi 0) := by
  have hbase : IntegrableOn
      (Set.indicator (Icc d⁻¹ c⁻¹) (fun _ : ℝ => (1 : ℂ))) (Ioi 0) :=
    ((integrableOn_const (C := (1 : ℂ)) (by simp)).integrable_indicator
      measurableSet_Icc).integrableOn
  refine hbase.congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (correction_integrand_coPoissonSubWindowSeed hc hcd (mem_Ioi.mp hy)).symm

theorem ae_burnolCoPoisson_subWindow_cpow {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (w : ℂ) :
    (fun t : ℝ => burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t * (t : ℂ) ^ (-w))
        =ᵐ[volume.restrict (Set.Ioi 0)]
      fun t : ℝ => ((Int.fract (d⁻¹ * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) -
        ((Int.fract (c⁻¹ * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
  filter_upwards [burnolCoPoissonRightSum_coPoissonSubWindowSeed_ae_fract hc hcd,
    ae_restrict_mem measurableSet_Ioi] with t ht htpos
  have htp : (0 : ℝ) < t := mem_Ioi.mp htpos
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htp)
  have hpow : ((t : ℝ) : ℂ)⁻¹ * (t : ℂ) ^ (-w) = (t : ℂ) ^ (-(w + 1)) := by
    rw [show (-(w + 1) : ℂ) = -1 + -w by ring, Complex.cpow_add _ _ htne,
      show ((t : ℝ) : ℂ) ^ (-1 : ℂ) = ((t : ℝ) : ℂ)⁻¹ by
        rw [Complex.cpow_neg, Complex.cpow_one]]
  rw [ht]
  have harg1 : t / d = d⁻¹ * t := by rw [div_eq_mul_inv, mul_comm]
  have harg2 : t / c = c⁻¹ * t := by rw [div_eq_mul_inv, mul_comm]
  rw [harg1, harg2]
  push_cast
  rw [← hpow]
  ring

theorem integrableOn_burnolCoPoisson_subWindow_cpow {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (fun t : ℝ =>
      burnolCoPoissonRightSum (coPoissonSubWindowSeed c d) t * (t : ℂ) ^ (-w)) (Set.Ioi 0) := by
  have hd : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have h := (integrableOn_Ioi_zero_fract_dilate_cpow hw0 hw1 (inv_pos.mpr hd)).sub
    (integrableOn_Ioi_zero_fract_dilate_cpow hw0 hw1 (inv_pos.mpr hc))
  exact h.congr (ae_burnolCoPoisson_subWindow_cpow hc hcd w).symm

/-- **A two-term combination of sub-window seeds is annihilated at a zeta zero.**  The co-Poisson
sum is linear in the seed, so the whole span of the explicit family carries the factor `zeta(w)`. -/
theorem integral_Ioi_burnolCoPoisson_subWindow_pair_cpow_eq_zero
    {c₁ d₁ c₂ d₂ : ℝ} (hc₁ : 0 < c₁) (hcd₁ : c₁ ≤ d₁) (hc₂ : 0 < c₂) (hcd₂ : c₂ ≤ d₂)
    {b : ℝ} (hb : 0 < b)
    (hs₁ : Function.support (coPoissonSubWindowSeed c₁ d₁) ⊆ Icc b b⁻¹)
    (hs₂ : Function.support (coPoissonSubWindowSeed c₂ d₂) ⊆ Icc b b⁻¹)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) (hz : riemannZeta w = 0) :
    (∫ t in Set.Ioi (0 : ℝ),
        burnolCoPoissonRightSum
          (fun v => coPoissonSubWindowSeed c₁ d₁ v + coPoissonSubWindowSeed c₂ d₂ v) t *
            (t : ℂ) ^ (-w)) = 0 := by
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      burnolCoPoissonRightSum
          (fun v => coPoissonSubWindowSeed c₁ d₁ v + coPoissonSubWindowSeed c₂ d₂ v) t *
            (t : ℂ) ^ (-w) =
        burnolCoPoissonRightSum (coPoissonSubWindowSeed c₁ d₁) t * (t : ℂ) ^ (-w) +
          burnolCoPoissonRightSum (coPoissonSubWindowSeed c₂ d₂) t * (t : ℂ) ^ (-w) := by
    intro t _
    rw [burnolCoPoissonRightSum_add hb hs₁ hs₂
      (integrableOn_correction_coPoissonSubWindowSeed hc₁ hcd₁)
      (integrableOn_correction_coPoissonSubWindowSeed hc₂ hcd₂)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add (integrableOn_burnolCoPoisson_subWindow_cpow hc₁ hcd₁ hw0 hw1)
      (integrableOn_burnolCoPoisson_subWindow_cpow hc₂ hcd₂ hw0 hw1),
    integral_Ioi_burnolCoPoisson_subWindow_cpow hc₁ hcd₁ hw0 hw1,
    integral_Ioi_burnolCoPoisson_subWindow_cpow hc₂ hcd₂ hw0 hw1, hz]
  simp


/-! ## The correction integrand of a general window seed -/

/-- The logarithmic integrand of a window seed is integrable: the seed lives above the aperture, so
the reciprocal weight is bounded there. -/
theorem integrableOn_logMass_of_window_seed {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    IntegrableOn (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u) (Set.Ioi 0) := by
  refine Integrable.mono' (g := fun u : ℝ => b⁻¹ * ‖g u‖)
    (((hg.norm).restrict (s := Set.Ioi 0)).const_mul _)
    ((Complex.measurable_ofReal.inv.aestronglyMeasurable).mul hg.aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hupos : (0 : ℝ) < u := mem_Ioi.mp hu
  by_cases hz : g u = 0
  · simp [hz]
  · have hmem : u ∈ Icc b b⁻¹ := hsupp (Function.mem_support.mpr hz)
    have hinv : u⁻¹ ≤ b⁻¹ := by
      rw [inv_le_inv₀ hupos hb]
      exact hmem.1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hupos]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)

/-- **The correction integrand of a window seed is integrable.**  Inverting the positive ray with
the `rpow` substitution of exponent `-1` turns it into the logarithmic integrand. -/
theorem integrableOn_correction_of_window_seed {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ)⁻¹ * g y⁻¹) (Set.Ioi 0) := by
  have hbase := integrableOn_logMass_of_window_seed hb hg hsupp
  have hiff := (integrableOn_Ioi_comp_rpow_iff
    (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u) (p := (-1 : ℝ)) (by norm_num)).mpr hbase
  refine hiff.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hxpos : (0 : ℝ) < x := mem_Ioi.mp hx
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hxpos)
  have hrpow1 : (x : ℝ) ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
  have hrpow2 : (x : ℝ) ^ ((-1 : ℝ) - 1) = (x ^ (2 : ℕ))⁻¹ := by
    rw [show ((-1 : ℝ) - 1) = -(2 : ℝ) by ring, Real.rpow_neg hxpos.le,
      ← Real.rpow_natCast x 2]
    norm_num
  dsimp only
  rw [hrpow1, hrpow2]
  rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_inv, inv_inv]
  rw [sq, mul_inv]
  field_simp

/-- **Additivity of the co-Poisson sum for arbitrary window seeds.** -/
theorem burnolCoPoissonRightSum_add_of_window {b : ℝ} (hb : 0 < b) {g h : ℝ → ℂ}
    (hgi : Integrable g) (hhi : Integrable h)
    (hgs : Function.support g ⊆ Icc b b⁻¹) (hhs : Function.support h ⊆ Icc b b⁻¹) (t : ℝ) :
    burnolCoPoissonRightSum (fun v => g v + h v) t =
      burnolCoPoissonRightSum g t + burnolCoPoissonRightSum h t :=
  burnolCoPoissonRightSum_add hb hgs hhs
    (integrableOn_correction_of_window_seed hb hgi hgs)
    (integrableOn_correction_of_window_seed hb hhi hhs) t

end RHTower
