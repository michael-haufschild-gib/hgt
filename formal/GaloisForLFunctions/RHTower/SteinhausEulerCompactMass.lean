import GaloisForLFunctions.RHTower.SteinhausEulerTranslatedMass

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- Literal normalized critical energy on a symmetric compact interval. -/
def steinhausEulerCompactMass (N m : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t in Icc (-(m : ℝ)) m, steinhausEulerSpatialDensity N t ω

theorem measurable_steinhausEulerCompactMass (N m : ℕ) :
    Measurable (steinhausEulerCompactMass N m) :=
  (measurable_steinhausEulerSpatialDensity_joint N).lintegral_prod_right'

/-- A finite deterministic cover gives a pointwise mass bound without spatial independence. -/
theorem steinhausEulerCompactMass_le_sum_translated (N m : ℕ) (ω : Omega) :
    steinhausEulerCompactMass N m ω ≤
      ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), steinhausEulerTranslatedMass N k ω := by
  let S := Finset.Icc (-(m : ℤ)) (m : ℤ)
  have hcover : Icc (-(m : ℝ)) (m : ℝ) ⊆
      ⋃ k : S, Icc (k.val : ℝ) ((k.val : ℝ) + 1) := by
    intro t ht
    have hlo : -(m : ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by simpa using ht.1)
    have hhi : ⌊t⌋ ≤ (m : ℤ) := by
      exact_mod_cast (Int.floor_le t).trans ht.2
    refine Set.mem_iUnion.mpr ⟨⟨⌊t⌋, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩, ?_⟩
    exact ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩
  calc
    _ ≤ ∫⁻ t in ⋃ k : S, Icc (k.val : ℝ) ((k.val : ℝ) + 1),
        steinhausEulerSpatialDensity N t ω := lintegral_mono_set hcover
    _ ≤ ∑' k : S, steinhausEulerTranslatedMass N k.val ω :=
      lintegral_iUnion_le _ _
    _ = _ := by
      rw [tsum_fintype]
      exact Finset.sum_coe_sort (s := S) (f := fun k : ℤ => steinhausEulerTranslatedMass N k ω)

private theorem subunit_rpow_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ S, f i) ^ q ≤ ∑ i ∈ S, f i ^ q := by
  classical
  induction S using Finset.induction with
  | empty => simp [ENNReal.zero_rpow_of_pos hq]
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hq.le hq1).trans (add_le_add le_rfl ih)

/-- A fixed compact window costs only the cardinality of its deterministic unit cover. -/
theorem lintegral_steinhausEulerCompactMass_rpow_le (N m : ℕ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    (∫⁻ ω, steinhausEulerCompactMass N m ω ^ q ∂steinhausMeasure) ≤
      ((Finset.Icc (-(m : ℤ)) (m : ℤ)).card : ℝ≥0∞) *
        ∫⁻ ω, steinhausEulerCriticalMass N ω ^ q ∂steinhausMeasure := by
  calc
    _ ≤ ∫⁻ ω, ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
        steinhausEulerTranslatedMass N k ω ^ q ∂steinhausMeasure := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.rpow_le_rpow (steinhausEulerCompactMass_le_sum_translated N m ω) hq.le).trans
        (subunit_rpow_sum_le _ _ hq hq1.le)
    _ = _ := by
      rw [lintegral_finsetSum _
        (f := fun k : ℤ => fun ω => steinhausEulerTranslatedMass N (k : ℝ) ω ^ q)
        (fun k _ => ENNReal.continuous_rpow_const.measurable.comp
          (measurable_steinhausEulerTranslatedMass N k))]
      simp_rw [lintegral_steinhausEulerTranslatedMass_rpow]
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Every fixed compact critical window has vanishing subunit moments along all cutoffs. -/
theorem tendsto_lintegral_steinhausEulerCompactMass_rpow (m : ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun N => ∫⁻ ω, steinhausEulerCompactMass N m ω ^ q ∂steinhausMeasure)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => ((Finset.Icc (-(m : ℤ)) (m : ℤ)).card : ℝ≥0∞) *
      ∫⁻ ω, steinhausEulerCriticalMass N ω ^ q ∂steinhausMeasure) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ((Finset.Icc (-(m : ℤ)) (m : ℤ)).card : ℝ≥0∞))
      (tendsto_lintegral_steinhausEulerCriticalMass_rpow hq hq1) (Or.inr (by simp))
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := ENNReal.tendsto_atTop_zero.mp hlim ε hε
  exact ⟨N₀, fun N hN => (lintegral_steinhausEulerCompactMass_rpow_le N m hq hq1).trans (hN₀ N hN)⟩

end RHTower
