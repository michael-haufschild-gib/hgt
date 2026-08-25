import GaloisForLFunctions.RHTower.Sieve.InghamCriticalMoment

open MeasureTheory

namespace RHTower

noncomputable section

/-- Jensen--Hölder inequality for a bounded nonnegative density of mass at most one. -/
theorem rpow_integral_mul_le_integral_rpow_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {q Cw Cg : ℝ} (hq : 1 < q) (hCw : 0 ≤ Cw)
    {W g : Ω → ℝ}
    (hWmeas : Measurable W) (hgmeas : Measurable g)
    (hW0 : ∀ x, 0 ≤ W x) (hg0 : ∀ x, 0 ≤ g x)
    (hWle : ∀ x, W x ≤ Cw)
    (hgle : ∀ᶠ x in MeasureTheory.ae μ, g x ≤ Cg)
    (hgmass : ∫ x, g x ∂μ ≤ 1) :
    (∫ x, W x * g x ∂μ) ^ q ≤ ∫ x, W x ^ q * g x ∂μ := by
  let q' : ℝ := q / (q - 1)
  let α : ℝ := 1 / q
  let β : ℝ := 1 - 1 / q
  let F : Ω → ℝ := fun x => W x * g x ^ α
  let G : Ω → ℝ := fun x => g x ^ β
  have hq0 : 0 < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hqm1 : 0 < q - 1 := sub_pos.mpr hq
  have hq'0 : 0 < q' := by dsimp [q']; positivity
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hβ0 : 0 ≤ β := by
    dsimp [β]
    rw [sub_nonneg, div_le_one hq0]
    linarith
  have hβpos : 0 < β := by
    dsimp [β]
    rw [sub_pos, div_lt_one hq0]
    linarith
  have hFmeas : Measurable F := by
    dsimp [F]
    exact hWmeas.mul ((Real.continuous_rpow_const hα0).measurable.comp hgmeas)
  have hGmeas : Measurable G := by
    dsimp [G]
    exact (Real.continuous_rpow_const hβ0).measurable.comp hgmeas
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    dsimp [F]
    exact mul_nonneg (hW0 x) (Real.rpow_nonneg (hg0 x) _)
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    dsimp [G]
    exact Real.rpow_nonneg (hg0 x) _
  have hFmem : MemLp F (ENNReal.ofReal q) μ := by
    apply MemLp.of_bound hFmeas.aestronglyMeasurable
      (Cw * Cg ^ α)
    filter_upwards [hgle] with x hgx
    rw [Real.norm_of_nonneg (hF0 x)]
    dsimp [F]
    exact mul_le_mul (hWle x)
      (Real.rpow_le_rpow (hg0 x) hgx hα0)
      (Real.rpow_nonneg (hg0 x) α) hCw
  have hGmem : MemLp G (ENNReal.ofReal q') μ := by
    apply MemLp.of_bound hGmeas.aestronglyMeasurable (Cg ^ β)
    filter_upwards [hgle] with x hgx
    rw [Real.norm_of_nonneg (hG0 x)]
    exact Real.rpow_le_rpow (hg0 x) hgx hβ0
  have hpq : q.HolderConjugate q' := by
    rw [Real.holderConjugate_iff]
    refine ⟨hq, ?_⟩
    dsimp [q']
    field_simp [hqne, sub_ne_zero.mpr hq.ne]
    ring
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (f := F) (g := G)
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hG0)
    hFmem hGmem
  have hFG : ∀ x, F x * G x = W x * g x := by
    intro x
    dsimp [F, G]
    by_cases hzero : g x = 0
    · simp [hzero, hαpos.ne', hβpos.ne']
    rw [mul_assoc, ← Real.rpow_add (lt_of_le_of_ne (hg0 x) (Ne.symm hzero))]
    have : α + β = 1 := by dsimp [α, β]; ring
    rw [this, Real.rpow_one]
  have hFq : ∀ x, F x ^ q = W x ^ q * g x := by
    intro x
    dsimp [F]
    rw [Real.mul_rpow (hW0 x) (Real.rpow_nonneg (hg0 x) α),
      ← Real.rpow_mul (hg0 x)]
    have : α * q = 1 := by dsimp [α]; field_simp
    rw [this, Real.rpow_one]
  have hGq : ∀ x, G x ^ q' = g x := by
    intro x
    dsimp [G]
    rw [← Real.rpow_mul (hg0 x)]
    have : β * q' = 1 := by
      dsimp [β, q']
      field_simp [hqne, sub_ne_zero.mpr hq.ne]
    rw [this, Real.rpow_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall hFG),
    integral_congr_ae (Filter.Eventually.of_forall hFq),
    integral_congr_ae (Filter.Eventually.of_forall hGq)] at hholder
  have hI0 : 0 ≤ ∫ x, W x * g x ∂μ :=
    integral_nonneg fun x => mul_nonneg (hW0 x) (hg0 x)
  have hA0 : 0 ≤ ∫ x, W x ^ q * g x ∂μ :=
    integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (hW0 x) q) (hg0 x)
  have hJ0 : 0 ≤ ∫ x, g x ∂μ := integral_nonneg hg0
  have hJpow : (∫ x, g x ∂μ) ^ (1 / q') ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow hJ0 hgmass (by positivity : 0 ≤ 1 / q')
  have hIA : (∫ x, W x * g x ∂μ) ≤
      (∫ x, W x ^ q * g x ∂μ) ^ (1 / q) := by
    calc
      (∫ x, W x * g x ∂μ) ≤
          (∫ x, W x ^ q * g x ∂μ) ^ (1 / q) *
            (∫ x, g x ∂μ) ^ (1 / q') := hholder
      _ ≤ (∫ x, W x ^ q * g x ∂μ) ^ (1 / q) * 1 := by
        exact mul_le_mul_of_nonneg_left hJpow (Real.rpow_nonneg hA0 _)
      _ = _ := mul_one _
  have hpow := Real.rpow_le_rpow hI0 hIA hq0.le
  calc
    (∫ x, W x * g x ∂μ) ^ q ≤
        ((∫ x, W x ^ q * g x ∂μ) ^ (1 / q)) ^ q := hpow
    _ = ∫ x, W x ^ q * g x ∂μ := by
      rw [← Real.rpow_mul hA0]
      have : (1 / q) * q = 1 := by field_simp
      rw [this, Real.rpow_one]

end

end RHTower
