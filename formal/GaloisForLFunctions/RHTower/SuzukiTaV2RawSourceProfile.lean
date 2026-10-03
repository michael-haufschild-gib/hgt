import GaloisForLFunctions.RHTower.SuzukiFiniteSourceProfile

open Filter MeasureTheory Set
open scoped Topology InnerProduct
noncomputable section
namespace RHTower

/-- Actual V2 source admission at parameter1, obtained from its literal
pointwise comparison with the already audited half-pole source. -/
theorem norm_ccmPolarApertureVector_one_le (a : SuzukiPositiveAperture) :
    ‖ccmPolarApertureVector a 1‖ ≤ Real.exp a.1 := by
  have hpoint : ∀ᵐ x : ℝ, ‖(ccmPolarL2Vector a 1 : ℝ → ℂ) x‖ ≤
      Real.exp (a.1 / 2) * ‖(ccmPolarL2Vector a (1 / 2) : ℝ → ℂ) x‖ := by
    filter_upwards [ccmPolarL2Vector_coeFn a 1, ccmPolarL2Vector_coeFn a (1 / 2)] with x hx hy
    rw [hx, hy]
    by_cases hmem : x ∈ centralInterval a.1
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      simp only [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hmem.2])
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  have h := Lp.norm_le_mul_norm_of_ae_le_mul hpoint
  have he : (Real.exp (a.1 / 2)) ^ 2 = Real.exp a.1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hhalf : ‖ccmPolarApertureVector a (1 / 2)‖ ≤ Real.exp (a.1 / 2) := by
    have hsq := norm_sq_ccmPolarApertureVector_half a
    rw [Real.sinh_eq] at hsq
    nlinarith [Real.exp_pos (-a.1), Real.exp_pos (a.1 / 2)]
  change ‖ccmPolarApertureVector a 1‖ ≤
    Real.exp (a.1 / 2) * ‖ccmPolarApertureVector a (1 / 2)‖ at h
  calc
    _ ≤ Real.exp (a.1 / 2) * ‖ccmPolarApertureVector a (1 / 2)‖ := h
    _ ≤ Real.exp (a.1 / 2) * Real.exp (a.1 / 2) :=
      mul_le_mul_of_nonneg_left hhalf (Real.exp_pos _).le
    _ = Real.exp a.1 := by nlinarith only [he]

/-- Every literal exponential source produces the existing actual raw deficiency. -/
theorem suzukiTaSourceResponse_polar (a : SuzukiPositiveAperture) (s : ℝ) :
    suzukiTaSourceResponse a (ccmPolarApertureVector a s) = suzukiTaRawDeficiency a s := by
  apply ext_inner_right ℂ
  intro z
  rw [suzukiTaSourceResponse_inner, suzukiTaRawDeficiency_inner]
  let e := suzukiApertureL2Equiv a
  have hp : e (suzukiTaExponentialL2 a s) = ccmPolarApertureVector a s := by
    apply Subtype.ext
    exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a s
  have hf : ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z) =
      e (suzukiTaPhysicalEmbedding a z) := by
    change _ = e (e.symm _)
    rw [e.apply_symm_apply]
    rfl
  change inner ℂ (ccmPolarApertureVector a s)
    (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)) =
      inner ℂ (suzukiTaExponentialL2 a s) (suzukiTaPhysicalEmbedding a z)
  rw [← hp, hf, e.inner_map_map]

/-- Actual V2 parameter1 physical profile, with all source norm and budget
obligations discharged. -/
theorem eventually_suzukiTaV2_rawSource_profile (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      ‖ccmArchimedeanFormToAperture ⟨a, ha⟩
        (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaRawDeficiency ⟨a, ha⟩ 1)) -
        ccmSourceShiftProfile ⟨a, ha⟩ (ccmPolarApertureVector ⟨a, ha⟩ 1)‖ ^ 2 < ε := by
  filter_upwards [eventually_suzukiTaSourceResponse_source_profile (ε / 2) (by positivity)]
    with a haProfile
  intro ha
  have hb : CCMFiniteExponentialBudget (ccmPolarL2Vector ⟨a, ha⟩ 1) (Real.exp a) := by
    simpa only [abs_one, one_mul] using CCMFiniteExponentialBudget.polar ⟨a, ha⟩ 1
  have h := haProfile ha (ccmPolarApertureVector ⟨a, ha⟩ 1) (Real.exp a)
    (norm_ccmPolarApertureVector_one_le ⟨a, ha⟩) hb
  rw [suzukiTaSourceResponse_polar] at h
  have he : (Real.exp a) ^ 2 = Real.exp (2 * a) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at h
  refine lt_of_le_of_lt ?_ (show ε / 2 < ε by linarith)
  apply le_of_mul_le_mul_left (a := Real.exp (2 * a)) ?_ (Real.exp_pos _)
  simpa only [mul_comm (ε / 2)] using h

theorem tendsto_suzukiTaV2_rawSource_profile :
    Tendsto (fun a : SuzukiPositiveAperture =>
      ‖ccmArchimedeanFormToAperture a
        (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖ ^ 2)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le (sq_nonneg _)
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_suzukiTaV2_rawSource_profile ε hε)] with a ha
    exact ha a.2

end RHTower
end
