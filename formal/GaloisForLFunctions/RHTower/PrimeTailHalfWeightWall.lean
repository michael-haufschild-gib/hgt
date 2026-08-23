import GaloisForLFunctions.RHTower.PrimeTailBoundaryAsymptotic

/-!
# The half-weight wall of the prime-tail co-Poisson current

The boundary law `G_z(x) ∼ 1/((z-1) x log(1/x))` pins the exact weight at which the current
becomes square integrable at the origin.  The square of the principal profile is
`x^{2α-2} log(1/x)^{-2}`, and the inverse-square logarithm is exactly strong enough to rescue the
endpoint: the weighted current is square integrable on the unit interval precisely when
`α ≥ 1/2`, with the critical weight included.

The positive half rests on the single integrability statement `1/(x log^2 x)` on `(0, δ]`, proved
from the primitive `-1/log x`, which is continuous at the origin.  The negative half compares the
profile with a pure power after absorbing the logarithm into an arbitrarily small power.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## A crude uniform bound for the tail -/

/-- The absolute Dirichlet bound of the divided-log coefficients. -/
def primeTailBound (σ : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-σ)

theorem norm_primeTailSum_le {z : ℂ} (hz : 1 < z.re) (y : ℝ) :
    ‖primeTailSum z y‖ ≤ primeTailBound z.re := by
  refine tsum_of_norm_bounded (summable_rpow_neg hz).hasSum (fun n => ?_)
  by_cases h : y < (n : ℝ)
  · rw [if_pos h]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, eulerLogDirichletCoeff_zero, zero_mul, norm_zero]
      positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    have h1 : ‖eulerLogDirichletCoeff n‖ ≤ 1 := norm_eulerLogDirichletCoeff_le_one n
    have h2 : (0 : ℝ) < (n : ℝ) ^ (-z).re := Real.rpow_pos_of_pos hn0 _
    calc ‖eulerLogDirichletCoeff n‖ * (n : ℝ) ^ (-z).re
        ≤ 1 * (n : ℝ) ^ (-z).re := mul_le_mul_of_nonneg_right h1 h2.le
      _ = (n : ℝ) ^ (-z.re) := by simp
  · rw [if_neg h, norm_zero]
    positivity

theorem primeTailBound_nonneg (σ : ℝ) : 0 ≤ primeTailBound σ := by
  refine tsum_nonneg (fun n => ?_)
  positivity

theorem norm_primeTailCurrent_le {z : ℂ} (hz : 1 < z.re) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖primeTailCurrent z x‖ ≤ x ^ (-z.re) * primeTailBound z.re := by
  rw [primeTailCurrent_eq_primeTailSum hx hx1, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hpow : x ^ (-z).re = x ^ (-z.re) := by simp
  rw [hpow]
  exact mul_le_mul_of_nonneg_left (norm_primeTailSum_le hz _)
    (Real.rpow_pos_of_pos hx _).le

/-! ## Measurability -/

theorem measurable_primeTailStep (z : ℂ) :
    Measurable (fun x : ℝ => (x : ℂ) ^ (-z) * primeTailSum z ((⌈x⁻¹⌉₊ : ℝ) - 1 / 2)) := by
  refine (measurable_ofReal_cpow (-z)).mul ?_
  have hcomp : (fun x : ℝ => primeTailSum z ((⌈x⁻¹⌉₊ : ℝ) - 1 / 2))
      = (fun N : ℕ => primeTailSum z ((N : ℝ) - 1 / 2)) ∘ (fun x : ℝ => ⌈x⁻¹⌉₊) := rfl
  rw [hcomp]
  exact measurable_from_top.comp (Nat.measurable_ceil.comp measurable_inv)

theorem aestronglyMeasurable_primeTailCurrent (z : ℂ) :
    AEStronglyMeasurable (primeTailCurrent z) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine ((measurable_primeTailStep z).aestronglyMeasurable.restrict).congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact (primeTailCurrent_eq_primeTailSum hx.1 hx.2.le).symm

/-! ## The critical profile is integrable -/

theorem hasDerivAt_neg_inv_log {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t : ℝ => -(Real.log t)⁻¹) ((x * (Real.log x) ^ 2)⁻¹) x := by
  have hlogne : Real.log x ≠ 0 := ne_of_lt (Real.log_neg hx hx1)
  have h := ((Real.hasDerivAt_log (ne_of_gt hx)).inv hlogne).neg
  refine h.congr_deriv ?_
  field_simp

/-- **The critical profile.**  `1/(x log^2 x)` is integrable at the origin: the primitive
`-1/log x` extends continuously by `0`. -/
theorem integrableOn_inv_mul_log_sq {d : ℝ} (hd1 : d < 1) :
    IntegrableOn (fun x : ℝ => (x * (Real.log x) ^ 2)⁻¹) (Ioc 0 d) volume := by
  have hcont : ContinuousOn (fun x : ℝ => -(Real.log x)⁻¹) (Icc 0 d) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · subst h0
      have hzero : -(Real.log (0 : ℝ))⁻¹ = 0 := by simp
      rw [ContinuousWithinAt, hzero]
      have hsub : Icc (0 : ℝ) d ⊆ {0} ∪ Ioc 0 d := by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr ⟨h, ht.2⟩
      refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
      rw [nhdsWithin_union]
      refine Filter.Tendsto.sup ?_ ?_
      · rw [nhdsWithin_singleton]
        simpa using tendsto_pure_nhds (fun x : ℝ => -(Real.log x)⁻¹) 0
      · refine Tendsto.mono_left ?_ (nhdsWithin_mono _ Ioc_subset_Ioi_self)
        have hlog : Tendsto (fun x : ℝ => (Real.log x)⁻¹) (𝓝[>] 0) (𝓝 0) :=
          Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot
        simpa using hlog.neg
    · refine ContinuousAt.continuousWithinAt ?_
      have hlx : Real.log x ≠ 0 := ne_of_lt (Real.log_neg h0 (lt_of_le_of_lt hx.2 hd1))
      exact ((Real.continuousAt_log (ne_of_gt h0)).inv₀ hlx).neg
  refine intervalIntegral.integrableOn_deriv_of_nonneg hcont ?_ ?_
  · intro x hx
    exact hasDerivAt_neg_inv_log hx.1 (lt_trans hx.2 hd1)
  · intro x hx
    refine inv_nonneg.mpr ?_
    exact mul_nonneg hx.1.le (sq_nonneg _)

/-! ## Two-sided control of the current near the origin -/

theorem exists_two_sided_primeTailCurrent {z : ℂ} (hz : 1 < z.re) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∀ x ∈ Ioo (0 : ℝ) δ,
      1 / (2 * ‖z - 1‖) * (x * Real.log x⁻¹)⁻¹ ≤ ‖primeTailCurrent z x‖
      ∧ ‖primeTailCurrent z x‖ ≤ 2 / ‖z - 1‖ * (x * Real.log x⁻¹)⁻¹ := by
  have hzne1 : z - (1 : ℂ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro h; rw [h] at hz; simp at hz
  have hnz1 : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr hzne1
  have hnorm : Tendsto
      (fun x : ℝ => ‖primeTailCurrent z x * ((z - 1) * (x : ℂ) * (Real.log x⁻¹ : ℂ))‖)
      (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_primeTailCurrent_boundary hz).norm
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 0,
      ‖primeTailCurrent z x * ((z - 1) * (x : ℂ) * (Real.log x⁻¹ : ℂ))‖ ∈ Ioo (1 / 2 : ℝ) 2 :=
    hnorm.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨min u (1 / 8), lt_min hu (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num),
    fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := hx.1
  have hxu : x < u := lt_of_lt_of_le hx.2 (min_le_left _ _)
  have hx8 : x < 1 / 8 := lt_of_lt_of_le hx.2 (min_le_right _ _)
  have hlogpos : (0 : ℝ) < Real.log x⁻¹ := by
    refine Real.log_pos ?_
    rw [one_lt_inv_iff₀]
    exact ⟨hx0, by linarith⟩
  have hmem := hsub ⟨hx0, hxu⟩
  simp only [Set.mem_setOf_eq] at hmem
  have hfact : ‖primeTailCurrent z x * ((z - 1) * (x : ℂ) * (Real.log x⁻¹ : ℂ))‖
      = ‖primeTailCurrent z x‖ * (‖z - 1‖ * x * Real.log x⁻¹) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hx0.le, Real.norm_of_nonneg hlogpos.le]
  rw [hfact] at hmem
  have hlogne : Real.log x⁻¹ ≠ 0 := ne_of_gt hlogpos
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hzn : ‖z - 1‖ ≠ 0 := ne_of_gt hnz1
  set w : ℝ := ‖z - 1‖ * x * Real.log x⁻¹ with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  constructor
  · have hEq : 1 / (2 * ‖z - 1‖) * (x * Real.log x⁻¹)⁻¹ = 1 / (2 * w) := by
      rw [hw]; field_simp
    rw [hEq, div_le_iff₀ (by positivity)]
    have := hmem.1
    nlinarith [hw0]
  · have hEq2 : 2 / ‖z - 1‖ * (x * Real.log x⁻¹)⁻¹ = 2 / w := by
      rw [hw]; field_simp
    rw [hEq2, le_div_iff₀ (by positivity)]
    exact le_of_lt hmem.2

/-! ## The wall -/

/-- The weighted square of the current. -/
def wallIntegrand (z : ℂ) (α : ℝ) (x : ℝ) : ℝ := (x ^ α * ‖primeTailCurrent z x‖) ^ 2

theorem aestronglyMeasurable_wallIntegrand (z : ℂ) (α : ℝ) {s : Set ℝ} (hs : s ⊆ Ioo (0 : ℝ) 1) :
    AEStronglyMeasurable (wallIntegrand z α) (volume.restrict s) := by
  have hbase : AEStronglyMeasurable (wallIntegrand z α) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine (AEStronglyMeasurable.mul ?_ (aestronglyMeasurable_primeTailCurrent z).norm).pow 2
    exact ((measurable_id.pow_const α).aestronglyMeasurable).restrict
  exact hbase.mono_measure (Measure.restrict_mono hs le_rfl)

theorem integrableOn_wallIntegrand_upper {z : ℂ} (hz : 1 < z.re) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) (α : ℝ) : IntegrableOn (wallIntegrand z α) (Ico δ 1) volume := by
  set M : ℝ := (max (δ ^ α) 1 * (δ ^ (-z.re) * primeTailBound z.re)) ^ 2 with hM
  refine Integrable.mono' (g := fun _ : ℝ => M) ?_
    (aestronglyMeasurable_wallIntegrand z α (fun x hx => ⟨lt_of_lt_of_le hδ hx.1, hx.2⟩)) ?_
  · refine integrableOn_const ?_ ?_
    · exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.Ico_subset_Icc_self)
        (by simp [Real.volume_Icc]))
    · simp [enorm_eq_nnnorm]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ico] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hδ hx.1
    have hx1 : x ≤ 1 := le_of_lt hx.2
    have hpow : x ^ α ≤ max (δ ^ α) 1 := by
      rcases le_or_gt 0 α with hα | hα
      · exact le_trans (Real.rpow_le_one hx0.le hx1 hα) (le_max_right _ _)
      · exact le_trans (Real.rpow_le_rpow_of_nonpos hδ hx.1 hα.le) (le_max_left _ _)
    have hnorm : ‖primeTailCurrent z x‖ ≤ δ ^ (-z.re) * primeTailBound z.re := by
      refine le_trans (norm_primeTailCurrent_le hz hx0 hx1) ?_
      refine mul_le_mul_of_nonneg_right ?_ (primeTailBound_nonneg z.re)
      exact Real.rpow_le_rpow_of_nonpos hδ hx.1 (by linarith)
    have hprod : x ^ α * ‖primeTailCurrent z x‖
        ≤ max (δ ^ α) 1 * (δ ^ (-z.re) * primeTailBound z.re) := by
      refine mul_le_mul hpow hnorm (norm_nonneg _) ?_
      exact le_trans zero_le_one (le_max_right _ _)
    have hnn : 0 ≤ x ^ α * ‖primeTailCurrent z x‖ :=
      mul_nonneg (Real.rpow_pos_of_pos hx0 α).le (norm_nonneg _)
    rw [Real.norm_of_nonneg (by rw [wallIntegrand]; positivity), wallIntegrand, hM]
    exact pow_le_pow_left₀ hnn hprod 2

theorem integrableOn_wallIntegrand_lower {z : ℂ} (hz : 1 < z.re) {α : ℝ} (hα : 1 / 2 ≤ α)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 4)
    (hbd : ∀ x ∈ Ioo (0 : ℝ) δ,
      ‖primeTailCurrent z x‖ ≤ 2 / ‖z - 1‖ * (x * Real.log x⁻¹)⁻¹) :
    IntegrableOn (wallIntegrand z α) (Ioo 0 δ) volume := by
  set C : ℝ := (2 / ‖z - 1‖) ^ 2 with hC
  have hmaj : IntegrableOn (fun x : ℝ => C * (x * (Real.log x) ^ 2)⁻¹) (Ioo 0 δ) volume :=
    ((integrableOn_inv_mul_log_sq (by linarith : δ < 1)).mono_set
      Ioo_subset_Ioc_self).const_mul C
  refine Integrable.mono' hmaj
    (aestronglyMeasurable_wallIntegrand z α (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hx1 : x < 1 := by linarith [hx.2]
  have hlogpos : (0 : ℝ) < Real.log x⁻¹ := by
    refine Real.log_pos ?_
    rw [one_lt_inv_iff₀]
    exact ⟨hx0, hx1⟩
  have hloginv : Real.log x⁻¹ = -Real.log x := Real.log_inv x
  have hnn : 0 ≤ x ^ α * ‖primeTailCurrent z x‖ :=
    mul_nonneg (Real.rpow_pos_of_pos hx0 α).le (norm_nonneg _)
  have hstep : (x ^ α * ‖primeTailCurrent z x‖) ^ 2
      ≤ (x ^ α * (2 / ‖z - 1‖ * (x * Real.log x⁻¹)⁻¹)) ^ 2 := by
    refine pow_le_pow_left₀ hnn ?_ 2
    exact mul_le_mul_of_nonneg_left (hbd x hx) (Real.rpow_pos_of_pos hx0 α).le
  have hexp : (x ^ α * (2 / ‖z - 1‖ * (x * Real.log x⁻¹)⁻¹)) ^ 2
      = C * (x ^ (2 * α) * (x ^ (2 : ℝ) * (Real.log x) ^ 2)⁻¹) := by
    rw [hC, hloginv]
    have hx2 : x ^ (2 * α) = (x ^ α) ^ 2 := by
      rw [← Real.rpow_natCast (x ^ α) 2, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    have hxx : x ^ (2 : ℝ) = x * x := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hx2, hxx]
    field_simp
  have hcmp : x ^ (2 * α) * (x ^ (2 : ℝ) * (Real.log x) ^ 2)⁻¹
      ≤ (x * (Real.log x) ^ 2)⁻¹ := by
    have hxle : x ^ (2 * α) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith)
    have hlogsq : (0 : ℝ) < (Real.log x) ^ 2 := by
      have : Real.log x ≠ 0 := ne_of_lt (Real.log_neg hx0 hx1)
      positivity
    have hxx : x ^ (2 : ℝ) = x * x := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hxx, Real.rpow_one] at *
    rw [mul_inv, mul_inv, mul_inv]
    have hxpos : (0 : ℝ) < x⁻¹ := by positivity
    have hlpos : (0 : ℝ) < ((Real.log x) ^ 2)⁻¹ := by positivity
    calc x ^ (2 * α) * (x⁻¹ * x⁻¹ * ((Real.log x) ^ 2)⁻¹)
        ≤ x * (x⁻¹ * x⁻¹ * ((Real.log x) ^ 2)⁻¹) := by
          refine mul_le_mul_of_nonneg_right hxle ?_
          positivity
      _ = x⁻¹ * ((Real.log x) ^ 2)⁻¹ := by field_simp
  rw [Real.norm_of_nonneg (by rw [wallIntegrand]; positivity), wallIntegrand]
  refine hstep.trans ?_
  rw [hexp]
  exact mul_le_mul_of_nonneg_left hcmp (by positivity)

end

end RHTower
