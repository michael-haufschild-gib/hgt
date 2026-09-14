import GaloisForLFunctions.HTGeometry.ModularDirichletFormSmoothApprox

/-!
# Density of the form domain and the Friedrichs Laplacian of the modular surface

The `L²(𝒟)` classes of `C¹` functions with compact support in `𝒟°` are dense in `L²(𝒟)`: a
square-integrable function is approximated by a continuous compactly supported one, which is cut
off to a compact subset of `𝒟°` carrying almost all the measure and then replaced by a smooth
uniform approximation.  Since every such class lies in the range of the form embedding `J`, the
range of `J` is dense.  Together with closability this makes the covariance `J J†` injective with
dense range, so its closed inverse — the Friedrichs operator of the modular Dirichlet form — is the
self-adjoint operator `1 − Δ` of the modular surface, and `J J†` is its bounded inverse.
-/

open UpperHalfPlane MeasureTheory ModularGroup Set Topology
open scoped InnerProductSpace ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The chart inverse and pull-backs of compactly supported functions -/

theorem continuousOn_ofComplex : ContinuousOn ofComplex upperSet := by
  have h := UpperHalfPlane.ofComplex.continuousOn
  show ContinuousOn ofComplex {z : ℂ | 0 < z.im}
  simpa [UpperHalfPlane.ofComplex] using h

theorem preimage_coe_fdoImage : UpperHalfPlane.coe ⁻¹' fdoImage = fdo :=
  Set.preimage_image_eq _ UpperHalfPlane.coe_injective

theorem isCompact_preimage_coe {C : Set ℂ} (hC : IsCompact C) (hCU : C ⊆ upperSet) :
    IsCompact (UpperHalfPlane.coe ⁻¹' C) :=
  (hC.image_of_continuousOn (continuousOn_ofComplex.mono hCU)).of_isClosed_subset
    (hC.isClosed.preimage continuous_coe) (fun z hz => ⟨z, hz, ofComplex_apply z⟩)

theorem isChartC1_mul_cutoff {P : ℂ → ℂ} (hP : ContDiff ℝ 1 P) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    IsChartC1 fun z : ℍ => P z * (χ z : ℂ) := by
  unfold IsChartC1
  have h : ContDiff ℝ 1 fun w : ℂ => P w * (χ w : ℂ) :=
    hP.mul (Complex.ofRealCLM.contDiff.comp hχ)
  refine h.contDiffOn.congr fun w hw => ?_
  show P (ofComplex w : ℂ) * (χ (ofComplex w : ℂ) : ℂ) = P w * (χ w : ℂ)
  rw [ofComplex_apply_of_im_pos hw]

/-! ## Approximation by interior functions -/

/-- **Interior approximation.**  Every `F ∈ L²(𝒟)` is within `ε` of the class of a `C¹` function
with compact support in `𝒟°`. -/
theorem exists_interior_approx (F : ModularL2) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : ℍ → ℂ) (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ) (_ : tsupport ψ ⊆ fdo),
      ‖F - toModularL2 ψ (memLp_of_isChartC1_of_hasCompactSupport hψ hs)‖ < ε := by
  set f : ℍ → ℂ := ⇑(modularToLp F) with hf
  have hfL2 : MemLp f 2 modularCellMeasure := Lp.memLp (modularToLp F)
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  -- a continuous compactly supported approximant
  obtain ⟨g, hgs, hgF, hgc, -⟩ := hfL2.exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 4))
    (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hε4)
  obtain ⟨M₀, hM₀⟩ := hgc.bounded_above_of_compact_support hgs
  set M : ℝ := max M₀ 0 + 1 with hMdef
  have hMpos : 0 < M := by
    have : (0 : ℝ) ≤ max M₀ 0 := le_max_right _ _
    linarith
  have hM : ∀ z, ‖g z‖ ≤ M := fun z => (hM₀ z).trans (by
    have : M₀ ≤ max M₀ 0 := le_max_left _ _
    linarith)
  -- a compact subset of `𝒟°` carrying almost all the measure
  set r : ℝ := ε / (4 * M) with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨K, hKfdo, hKc, hKμ⟩ := isOpen_fdo.measurableSet.exists_isCompact_sdiff_lt
    (μ := modularCellMeasure) (measure_ne_top _ _) (ε := ENNReal.ofReal (r ^ 2))
    (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
  -- the cutoff
  have hCU : UpperHalfPlane.coe '' K ⊆ fdoImage := Set.image_mono hKfdo
  obtain ⟨χ, hχ, hχs, hχU, hχ1, hχ01⟩ := exists_smooth_cutoff (hKc.image continuous_coe) hCU
  -- the smooth uniform approximation of `g` on the support of the cutoff
  set V : ℝ := (modularCellMeasure Set.univ).toReal ^ (2⁻¹ : ℝ) with hVdef
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  set η : ℝ := ε / (4 * (V + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hGc : ContinuousOn (fun w => g (ofComplex w)) (tsupport χ) :=
    (hgc.comp_continuousOn continuousOn_ofComplex).mono (hχU.trans fdoImage_subset_upperSet)
  obtain ⟨P, hP, hPG⟩ := exists_contDiff_uniform_approx hχs hGc hη
  -- the interior function
  set ψ : ℍ → ℂ := fun z => P z * (χ z : ℂ) with hψdef
  have hψ : IsChartC1 ψ := isChartC1_mul_cutoff hP hχ
  have hψsupp : tsupport ψ ⊆ UpperHalfPlane.coe ⁻¹' tsupport χ := by
    refine closure_minimal ?_ ((isClosed_tsupport χ).preimage continuous_coe)
    intro z hz
    have h0 : χ z ≠ 0 := fun h => hz (by simp [ψ, h])
    exact subset_tsupport χ h0
  have hψK : tsupport ψ ⊆ fdo :=
    hψsupp.trans (by rw [← preimage_coe_fdoImage]; exact Set.preimage_mono hχU)
  have hψs : HasCompactSupport ψ :=
    (isCompact_preimage_coe hχs (hχU.trans fdoImage_subset_upperSet)).of_isClosed_subset
      (isClosed_tsupport ψ) hψsupp
  refine ⟨ψ, hψ, hψs, hψK, ?_⟩
  -- measurability of the pieces
  have hχc : Continuous fun z : ℍ => (χ z : ℂ) :=
    Complex.continuous_ofReal.comp (hχ.continuous.comp continuous_coe)
  have hmf : AEStronglyMeasurable f modularCellMeasure := Lp.aestronglyMeasurable _
  have hm2 : AEStronglyMeasurable (fun z => g z - g z * (χ z : ℂ)) modularCellMeasure :=
    (hgc.sub (hgc.mul hχc)).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun z => g z * (χ z : ℂ) - ψ z) modularCellMeasure :=
    ((hgc.mul hχc).sub hψ.continuous).aestronglyMeasurable
  -- the norm as an `eLpNorm`
  have hnorm : ‖F - toModularL2 ψ (memLp_of_isChartC1_of_hasCompactSupport hψ hψs)‖ =
      (eLpNorm (f - ψ) 2 modularCellMeasure).toReal := by
    have h1 : ‖F - toModularL2 ψ (memLp_of_isChartC1_of_hasCompactSupport hψ hψs)‖ =
        ‖modularToLp F - MemLp.toLp ψ (memLp_of_isChartC1_of_hasCompactSupport hψ hψs)‖ := rfl
    rw [h1, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (modularToLp F)
      (MemLp.toLp ψ (memLp_of_isChartC1_of_hasCompactSupport hψ hψs)),
      MemLp.coeFn_toLp (memLp_of_isChartC1_of_hasCompactSupport hψ hψs)] with z h1 h2
    rw [h1, Pi.sub_apply, h2]
    rfl
  -- the cutoff error
  have hb : eLpNorm (fun z => g z - g z * (χ z : ℂ)) 2 modularCellMeasure ≤
      ENNReal.ofReal (ε / 4) := by
    have hpt : ∀ᵐ z ∂modularCellMeasure,
        ‖g z - g z * (χ z : ℂ)‖ ≤ ‖(fdo \ K).indicator (fun _ => M) z‖ := by
      filter_upwards [ae_mem_fdo] with z hz
      by_cases hzK : z ∈ K
      · have h1 : χ z = 1 := by
          have := hχ1 (Set.mem_image_of_mem UpperHalfPlane.coe hzK)
          simpa using this
        simp [h1]
      · rw [Set.indicator_of_mem (show z ∈ fdo \ K from ⟨hz, hzK⟩), Real.norm_eq_abs,
          abs_of_pos hMpos]
        have h01 := hχ01 z
        have hcast : g z - g z * (χ z : ℂ) = g z * ((1 - χ z : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [h01.2])]
        calc ‖g z‖ * (1 - χ z) ≤ M * 1 :=
              mul_le_mul (hM z) (by linarith [h01.1]) (by linarith [h01.2]) hMpos.le
          _ = M := mul_one M
    refine (eLpNorm_mono_ae hpt).trans ((eLpNorm_indicator_const_le (M : ℝ) 2).trans ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos hMpos, ENNReal.toReal_ofNat]
    calc ENNReal.ofReal M * modularCellMeasure (fdo \ K) ^ (1 / (2 : ℝ)) ≤
          ENNReal.ofReal M * ENNReal.ofReal (r ^ 2) ^ (1 / (2 : ℝ)) :=
          mul_le_mul_right (ENNReal.rpow_le_rpow hKμ.le (by norm_num)) _
      _ = ENNReal.ofReal (ε / 4) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← ENNReal.ofReal_mul hMpos.le]
          congr 1
          rw [show ((r ^ 2 : ℝ) ^ (1 / (2 : ℝ))) = r by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]]
          rw [hrdef]
          field_simp
  -- the smoothing error
  have hc : eLpNorm (fun z => g z * (χ z : ℂ) - ψ z) 2 modularCellMeasure ≤
      ENNReal.ofReal (ε / 4) := by
    have hpt : ∀ᵐ z ∂modularCellMeasure, ‖g z * (χ z : ℂ) - ψ z‖ ≤ η := by
      refine ae_of_all _ fun z => ?_
      by_cases hz : (z : ℂ) ∈ tsupport χ
      · have h1 := hPG z hz
        rw [ofComplex_apply] at h1
        have h01 := hχ01 z
        have hcast : g z * (χ z : ℂ) - ψ z = (g z - P z) * (χ z : ℂ) := by
          simp only [ψ]; ring
        rw [hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h01.1]
        calc ‖g z - P z‖ * χ z ≤ η * 1 := mul_le_mul h1.le h01.2 h01.1 hη.le
          _ = η := mul_one η
      · have h0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [ψ, h0, hη.le]
    refine (eLpNorm_le_of_ae_bound hpt).trans ?_
    rw [ENNReal.toReal_ofNat, ← ENNReal.ofReal_toReal (measure_ne_top modularCellMeasure Set.univ),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ← ENNReal.ofReal_mul hV]
    apply ENNReal.ofReal_le_ofReal
    show V * η ≤ ε / 4
    have hVη : V * η = ε / 4 * (V / (V + 1)) := by
      rw [hηdef]; field_simp
    have hle : V / (V + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    rw [hVη]
    calc ε / 4 * (V / (V + 1)) ≤ ε / 4 * 1 := mul_le_mul_of_nonneg_left hle hε4.le
      _ = ε / 4 := mul_one _
  -- assembly
  have hsplit : f - ψ = (f - g) + ((fun z => g z - g z * (χ z : ℂ)) +
      fun z => g z * (χ z : ℂ) - ψ z) := by
    funext z; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have htri : eLpNorm (f - ψ) 2 modularCellMeasure ≤
      ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) := by
    rw [hsplit]
    refine (eLpNorm_add_le (hmf.sub hgc.aestronglyMeasurable) (hm2.add hm3) one_le_two).trans
      (add_le_add hgF ?_)
    exact (eLpNorm_add_le hm2 hm3 one_le_two).trans (add_le_add hb hc)
  have hsum : ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) =
      ENNReal.ofReal (3 * ε / 4) := by
    rw [← ENNReal.ofReal_add hε4.le hε4.le, ← ENNReal.ofReal_add hε4.le (by positivity)]
    congr 1; ring
  rw [hnorm]
  calc (eLpNorm (f - ψ) 2 modularCellMeasure).toReal ≤ 3 * ε / 4 :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) (htri.trans hsum.le)
    _ < ε := by linarith

/-! ## Density of the range of the form embedding -/

/-- **The form embedding has dense range.** -/
theorem dense_range_formInclusion : Dense (Set.range formInclusion) := by
  rw [Metric.dense_iff]
  intro F r hr
  obtain ⟨ψ, hψ, hs, hK, hlt⟩ := exists_interior_approx F hr
  refine ⟨toModularL2 ψ (memLp_of_isChartC1_of_hasCompactSupport hψ hs), ?_,
    toModularL2_mem_range_formInclusion hψ hs hK⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
  exact hlt

theorem dense_range_formInclusion' :
    Dense ((LinearMap.range (formInclusion : FormDomain →ₗ[ℂ] ModularL2) : Submodule ℂ ModularL2) :
      Set ModularL2) := by
  rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  exact dense_range_formInclusion

/-! ## The Friedrichs Laplacian of the modular surface -/

/-- The covariance `J J†` is injective. -/
theorem modularCovariance_injective : Function.Injective modularCovariance :=
  formEmbeddingCovariance_injective formInclusion formInclusion_injective dense_range_formInclusion'

/-- The covariance `J J†` has dense range. -/
theorem modularCovariance_dense_range :
    Dense ((LinearMap.range (modularCovariance : ModularL2 →ₗ[ℂ] ModularL2) :
      Submodule ℂ ModularL2) : Set ModularL2) :=
  formEmbeddingCovariance_dense_range formInclusion formInclusion_injective
    dense_range_formInclusion'

/-- **The Friedrichs operator `1 − Δ` of the modular surface**: the closed inverse of the covariance
of the modular Dirichlet form. -/
def modularFriedrichsOperator : ModularL2 →ₗ.[ℂ] ModularL2 := friedrichsFormOperator formInclusion

theorem modularFriedrichsOperator_isSelfAdjoint : IsSelfAdjoint modularFriedrichsOperator :=
  friedrichsFormOperator_isSelfAdjoint formInclusion formInclusion_injective
    dense_range_formInclusion'

theorem modularFriedrichsOperator_dense_domain : Dense (modularFriedrichsOperator.domain : Set ModularL2) :=
  friedrichsFormOperator_dense_domain formInclusion formInclusion_injective
    dense_range_formInclusion'

end

end GaloisForLFunctions.HTGeometry
