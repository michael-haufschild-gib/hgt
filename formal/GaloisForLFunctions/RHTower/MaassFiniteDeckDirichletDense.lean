import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichletPeriodization
import GaloisForLFunctions.HTGeometry.ModularDirichletFormDense

/-!
# Density of the central finite-deck Maass Dirichlet form

The finite-deck coefficient space is finite-dimensional.  The scalar compact-interior density
argument therefore extends to vector fields: approximate an `L²` field by a continuous compactly
supported vector field, cut it off in the interior of the modular cell, then smooth all deck
coordinates uniformly.  Central averaging and periodization from
`MaassFiniteDeckDirichletPeriodization` transfer the resulting approximation to the completed
finite-deck form.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff Classical
namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace MaassCongruenceL2
noncomputable section

private theorem isChartC1_continuous_vec {N : ℕ} {F : ℍ → DeckSpace N}
    (hF : IsChartC1 F) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (hF.continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [IsChartC1, chartFun, Function.comp_def, ofComplex_apply] using h

private theorem isChartC1_smul_cutoff_vec {N : ℕ} {P : ℂ → DeckSpace N}
    (hP : ContDiff ℝ 1 P) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) :
    IsChartC1 fun z : ℍ => (χ z : ℂ) • P z := by
  unfold IsChartC1
  have h : ContDiff ℝ 1 fun w : ℂ => (χ w : ℂ) • P w :=
    (Complex.ofRealCLM.contDiff.comp hχ).smul hP
  refine h.contDiffOn.congr fun w hw => ?_
  show (χ (ofComplex w : ℂ) : ℂ) • P (ofComplex w : ℂ) = (χ w : ℂ) • P w
  rw [ofComplex_apply_of_im_pos hw]

/-- Every finite-deck `L²` vector is approximated by a compactly supported `C¹` vector field in
`fdo`. -/
theorem exists_interior_approx_vector (N : ℕ) (F : DeckL2 N) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : ℍ → DeckSpace N) (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ)
      (_ : tsupport ψ ⊆ fdo),
      ‖F - toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs)‖ < ε := by
  set f : ℍ → DeckSpace N := ⇑F with hf
  have hfL2 : MemLp f 2 cellMeasure := Lp.memLp F
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
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
  set r : ℝ := ε / (4 * M) with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨K, hKfdo, hKc, hKμ⟩ := isOpen_fdo.measurableSet.exists_isCompact_sdiff_lt
    (μ := cellMeasure) (measure_ne_top _ _) (ε := ENNReal.ofReal (r ^ 2))
    (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
  have hCU : UpperHalfPlane.coe '' K ⊆ fdoImage := Set.image_mono hKfdo
  obtain ⟨χ, hχ, hχs, hχU, hχ1, hχ01⟩ := exists_smooth_cutoff (hKc.image continuous_coe) hCU
  set V : ℝ := (cellMeasure Set.univ).toReal ^ (2⁻¹ : ℝ) with hVdef
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  set η : ℝ := ε / (4 * (V + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hGc : ContinuousOn (fun w => g (ofComplex w)) (tsupport χ) :=
    (hgc.comp_continuousOn continuousOn_ofComplex).mono (hχU.trans fdoImage_subset_upperSet)
  obtain ⟨P, hP, hPG⟩ := exists_contDiff_uniform_approx_vector hχs hGc hη
  set ψ : ℍ → DeckSpace N := fun z => (χ z : ℂ) • P z with hψdef
  have hψ : IsChartC1 ψ := isChartC1_smul_cutoff_vec hP hχ
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
  have hχc : Continuous fun z : ℍ => (χ z : ℂ) :=
    Complex.continuous_ofReal.comp (hχ.continuous.comp continuous_coe)
  have hmf : AEStronglyMeasurable f cellMeasure := Lp.aestronglyMeasurable _
  have hm2 : AEStronglyMeasurable (fun z => g z - (χ z : ℂ) • g z) cellMeasure :=
    (hgc.sub (hχc.smul hgc)).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun z : ℍ => (χ z : ℂ) • g z - ψ z) cellMeasure :=
    ((hχc.smul hgc).sub (isChartC1_continuous_vec hψ)).aestronglyMeasurable
  have hnorm : ‖F - toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hψs)‖ =
      (eLpNorm (f - ψ) 2 cellMeasure).toReal := by
    have h1 : ‖F - toDeckL2 ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hψs)‖ =
        ‖F - MemLp.toLp ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hψs)‖ := rfl
    rw [h1, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub F
      (MemLp.toLp ψ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hψs)),
      MemLp.coeFn_toLp (memLp_of_isChartC1_of_hasCompactSupport_vec hψ hψs)] with z h1 h2
    rw [h1, Pi.sub_apply, h2]
    rfl
  have hb : eLpNorm (fun z => g z - (χ z : ℂ) • g z) 2 cellMeasure ≤
      ENNReal.ofReal (ε / 4) := by
    have hpt : ∀ᵐ z ∂cellMeasure,
        ‖g z - (χ z : ℂ) • g z‖ ≤ ‖(fdo \ K).indicator (fun _ => M) z‖ := by
      filter_upwards [ae_mem_fdo] with z hz
      by_cases hzK : z ∈ K
      · have h1 : χ z = 1 := by
          have := hχ1 (Set.mem_image_of_mem UpperHalfPlane.coe hzK)
          simpa using this
        simp [h1]
      · rw [Set.indicator_of_mem (show z ∈ fdo \ K from ⟨hz, hzK⟩), Real.norm_eq_abs,
          abs_of_pos hMpos]
        have h01 := hχ01 z
        have hcast : g z - (χ z : ℂ) • g z = ((1 - χ z : ℝ) : ℂ) • g z := by
          push_cast
          module
        rw [hcast, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [h01.2])]
        calc (1 - χ z) * ‖g z‖ ≤ 1 * M :=
              mul_le_mul (by linarith [h01.1]) (hM z) (norm_nonneg _) zero_le_one
          _ = M := one_mul M
    refine (eLpNorm_mono_ae hpt).trans ((eLpNorm_indicator_const_le (M : ℝ) 2).trans ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos hMpos, ENNReal.toReal_ofNat]
    calc ENNReal.ofReal M * cellMeasure (fdo \ K) ^ (1 / (2 : ℝ)) ≤
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
  have hc : eLpNorm (fun z : ℍ => (χ z : ℂ) • g z - ψ z) 2 cellMeasure ≤
      ENNReal.ofReal (ε / 4) := by
    have hpt : ∀ᵐ z : ℍ ∂cellMeasure, ‖(χ z : ℂ) • g z - ψ z‖ ≤ η := by
      refine ae_of_all _ fun z => ?_
      by_cases hz : (z : ℂ) ∈ tsupport χ
      · have h1 := hPG z hz
        rw [ofComplex_apply] at h1
        have h01 := hχ01 z
        have hcast : (χ z : ℂ) • g z - ψ z = (χ z : ℂ) • (g z - P z) := by
          simp only [ψ]
          rw [smul_sub]
        rw [hcast, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h01.1]
        calc χ z * ‖g z - P z‖ ≤ 1 * η :=
              mul_le_mul h01.2 h1.le (norm_nonneg _) zero_le_one
          _ = η := one_mul η
      · have h0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [ψ, h0, hη.le]
    refine (eLpNorm_le_of_ae_bound hpt).trans ?_
    rw [ENNReal.toReal_ofNat, ← ENNReal.ofReal_toReal (measure_ne_top cellMeasure Set.univ),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ← ENNReal.ofReal_mul hV]
    apply ENNReal.ofReal_le_ofReal
    show V * η ≤ ε / 4
    have hVη : V * η = ε / 4 * (V / (V + 1)) := by
      rw [hηdef]
      field_simp
    have hle : V / (V + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    rw [hVη]
    calc ε / 4 * (V / (V + 1)) ≤ ε / 4 * 1 := mul_le_mul_of_nonneg_left hle hε4.le
      _ = ε / 4 := mul_one _
  have hsplit : f - ψ = (f - g) + ((fun z : ℍ => g z - (χ z : ℂ) • g z) +
      fun z : ℍ => (χ z : ℂ) • g z - ψ z) := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply]
    module
  have htri : eLpNorm (f - ψ) 2 cellMeasure ≤
      ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) := by
    rw [hsplit]
    refine (eLpNorm_add_le (hmf.sub hgc.aestronglyMeasurable) (hm2.add hm3) one_le_two).trans
      (add_le_add hgF ?_)
    exact (eLpNorm_add_le hm2 hm3 one_le_two).trans (add_le_add hb hc)
  have hsum : ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) =
      ENNReal.ofReal (3 * ε / 4) := by
    rw [← ENNReal.ofReal_add hε4.le hε4.le, ← ENNReal.ofReal_add hε4.le (by positivity)]
    congr 1
    ring
  rw [hnorm]
  calc (eLpNorm (f - ψ) 2 cellMeasure).toReal ≤ 3 * ε / 4 :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) (htri.trans hsum.le)
    _ < ε := by linarith

/-- The central finite-deck Dirichlet form has dense `L²` range. -/
theorem dense_range_formInclusionCentral (N : ℕ) :
    Dense (Set.range (formInclusionCentral N)) := by
  rw [Metric.dense_iff]
  intro w r hr
  obtain ⟨ψ, hψ, hs, hK, hlt⟩ := exists_interior_approx_vector N (w : DeckL2 N) hr
  obtain ⟨u, hu⟩ := exists_formInclusion_approx_of_interior w hψ hs hK
    (by simpa only [norm_sub_rev] using hlt)
  refine ⟨formInclusionCentral N u, ?_, ⟨u, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hu

theorem dense_range_formInclusionCentral' (N : ℕ) :
    Dense ((LinearMap.range (formInclusionCentral N).toLinearMap : Submodule ℂ (deckCentralFixedL2 N)) :
      Set (deckCentralFixedL2 N)) := by
  rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  exact dense_range_formInclusionCentral N

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
