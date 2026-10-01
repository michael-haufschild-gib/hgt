import GaloisForLFunctions.RHTower.FermiNymanWeightedCorrelation
import GaloisForLFunctions.RHTower.FermiNymanCorrelationKernel

/-!
# The exact zero-weight boundary of the Fermi witness domain

A source witness with nonpositive weight vanishes on `(0,1]`. At every positive
weight the fixed spurious mode `k=1` is admitted and nonzero. Its exact energy is
`1/(2a)`, so source membership at all positive weights supplies no uniform energy
bound as the parameter tends to zero. No statement about the canonical index
vanishing follows from this domain boundary alone.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem IsWeightedFermiWitness.mono_weight {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) : IsWeightedFermiWitness b w := by
  refine ⟨hw.1, ?_, hw.2.2⟩
  have hc : ContinuousOn (fun t : ℝ => t ^ (2 * b - 1) * ‖w t‖ ^ 2) (Ioc 0 1) := by
    apply ContinuousOn.mul ?_ (hw.1.norm.pow 2)
    exact fun t ht => (Real.continuousAt_rpow_const t (2 * b - 1) (Or.inl ht.1.ne')).continuousWithinAt
  apply hw.2.1.mono' (hc.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)) (sq_nonneg _)

theorem IsWeightedFermiWitness.selfSimilar_zero {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness 0 w) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    w (t / 2) = w t := by
  apply hw.selfSimilar_of_correlation_order (by norm_num) (by norm_num) ?_ ht
  intro ρ
  exfalso
  have h1 : 1 < (ρ : ℂ).re := by simpa using ρ.2.2.1
  linarith [ρ.2.2.2]

/-- At the zero weight, finite energy leaves no nonzero dyadic-periodic profile. -/
theorem zero_of_integrable_inv_normSq_dyadicSelfSimilar {w : ℝ → ℂ}
    (hc : ContinuousOn w (Ioc (0 : ℝ) 1))
    (hI : IntegrableOn (fun t => t⁻¹ * ‖w t‖ ^ 2) (Ioc (0 : ℝ) 1))
    (hs : ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w t = 0 := by
  let f : ℝ → ℝ := fun t => t⁻¹ * ‖w t‖ ^ 2
  have hscale : ∀ t ∈ Ioc (0 : ℝ) 1, f (t / 2) = 2 * f t := by
    intro t ht
    dsimp [f]
    rw [hs t ht]
    field_simp
  have hhalf : (∫ t in Ioc (0 : ℝ) (1 / 2), f t) = ∫ t in Ioc (0 : ℝ) 1, f t := by
    have h := integral_Ioc_comp_half f
    have heq : (∫ t in Ioc (0 : ℝ) 1, f (t / 2)) = 2 * ∫ t in Ioc (0 : ℝ) 1, f t := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioc hscale
    rw [heq, smul_eq_mul] at h
    linarith
  have hleft : IntegrableOn f (Ioc (0 : ℝ) (1 / 2)) :=
    hI.mono_set (Ioc_subset_Ioc_right (by norm_num))
  have hright : IntegrableOn f (Ioc (1 / 2 : ℝ) 1) :=
    hI.mono_set (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have hsplit : (∫ t in Ioc (0 : ℝ) 1, f t) =
      (∫ t in Ioc (0 : ℝ) (1 / 2), f t) + ∫ t in Ioc (1 / 2 : ℝ) 1, f t := by
    rw [← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact setIntegral_union (by
      apply Set.disjoint_left.mpr
      intro x hx hy
      linarith [hx.2, hy.1]) measurableSet_Ioc hleft hright
  have hzero : (∫ t in Ioc (1 / 2 : ℝ) 1, f t) = 0 := by linarith
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (1 / 2 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (inv_nonneg.mpr (by linarith [hx.1])) (sq_nonneg _)
  have hae : f =ᵐ[volume.restrict (Ioc (1 / 2 : ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hright).mp hzero
  have hfc : ContinuousOn f (Ioc (1 / 2 : ℝ) 1) := by
    apply ContinuousOn.mul ?_ ((hc.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)).norm.pow 2)
    exact continuousOn_id.inv₀ (fun x hx => by change x ≠ 0; linarith [hx.1])
  have hfund : ∀ x ∈ Ioc (1 / 2 : ℝ) 1, w x = 0 := by
    intro x hx
    have hfx := (Measure.eqOn_Ioc_of_ae_eq volume hae hfc continuousOn_const) hx
    change x⁻¹ * ‖w x‖ ^ 2 = 0 at hfx
    have hn := (mul_eq_zero.mp hfx).resolve_left (inv_ne_zero (ne_of_gt (by linarith [hx.1])))
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  obtain ⟨n, hn0, hn1⟩ := exists_nat_pow_near_of_lt_one ht.1 ht.2
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  let x := t / (1 / 2 : ℝ) ^ n
  have hx0 : 1 / 2 < x := by
    apply (lt_div_iff₀ hp).mpr
    rw [pow_succ] at hn0
    nlinarith
  have hx1 : x ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using hn1)
  have heq : x * (1 / 2 : ℝ) ^ n = t := div_mul_cancel₀ t hp.ne'
  rw [← heq, dyadicSelfSimilar_mul_pow_half hs n ⟨by linarith, hx1⟩, hfund x ⟨hx0, hx1⟩]

theorem IsWeightedFermiWitness.eq_zero_of_nonpos {a : ℝ} (ha : a ≤ 0) {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w t = 0 := by
  have hw0 := hw.mono_weight ha
  apply zero_of_integrable_inv_normSq_dyadicSelfSimilar hw0.1 ?_
    (fun t ht => hw0.selfSimilar_zero ht) ht
  simpa only [mul_zero, zero_sub, Real.rpow_neg_one] using hw0.2.1


/-- The fixed source has a nonzero weighted witness precisely at positive weights. -/
theorem weightedFermiWitness_nontrivial_iff (a : ℝ) :
    (∃ w : ℝ → ℂ, IsWeightedFermiWitness a w ∧
      ∃ t ∈ Ioc (0 : ℝ) 1, w t ≠ 0) ↔ 0 < a := by
  constructor
  · rintro ⟨w, hw, t, ht, hn⟩
    by_contra ha
    exact hn (hw.eq_zero_of_nonpos (le_of_not_gt ha) ht)
  · intro ha
    refine ⟨spuriousWitness 1, isWeightedFermiWitness_spurious ha (by norm_num), 1,
      ⟨by norm_num, le_rfl⟩, ?_⟩
    simp [spuriousWitness, powerWitness]

theorem integral_weighted_normSq_spurious {a : ℝ} (ha : 0 < a) (k : ℤ) :
    (∫ t in Ioc (0 : ℝ) 1, t ^ (2 * a - 1) * ‖spuriousWitness k t‖ ^ 2) =
      1 / (2 * a) := by
  have hz : 1 - a < ((starRingEnd ℂ) (dyadicSpuriousMode k)).re := by
    rw [Complex.conj_re, dyadicSpuriousMode_re]
    linarith
  simpa [spuriousWitness, dyadicSpuriousMode_re] using
    (integral_weighted_normSq_powerWitness hz (by norm_num : (0 : ℝ) < 1))

/-- A single literal source witness already rules out a uniform energy bound near zero. -/
theorem spurious_weighted_energy_unbounded_near_zero (k : ℤ) (M : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ Ioo (0 : ℝ) ε,
      M < ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * a - 1) * ‖spuriousWitness k t‖ ^ 2 := by
  let a : ℝ := min (ε / 2) (1 / (4 * (|M| + 1)))
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hae : a < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hab : a ≤ 1 / (4 * (|M| + 1)) := min_le_right _ _
  have hm : M * (2 * a) ≤ |M| * (2 * a) :=
    mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
  refine ⟨a, ⟨ha, hae⟩, ?_⟩
  rw [integral_weighted_normSq_spurious ha k]
  apply (lt_div_iff₀ (by positivity : 0 < 2 * a)).mpr
  have hb := (le_div_iff₀ (by positivity : 0 < 4 * (|M| + 1))).mp hab
  nlinarith [abs_nonneg M]

/-- Hypothesis-free source-domain boundary and its energy obstruction. -/
theorem weightedFermiWitness_domain_boundary :
    (∀ a : ℝ, (∃ w : ℝ → ℂ, IsWeightedFermiWitness a w ∧
      ∃ t ∈ Ioc (0 : ℝ) 1, w t ≠ 0) ↔ 0 < a) ∧
    ∀ ε : ℝ, 0 < ε → ∀ M : ℝ, ∃ a ∈ Ioo (0 : ℝ) ε,
      M < ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * a - 1) * ‖spuriousWitness 1 t‖ ^ 2 :=
  ⟨weightedFermiWitness_nontrivial_iff, fun _ hε M =>
    spurious_weighted_energy_unbounded_near_zero 1 M hε⟩

end RHTower
