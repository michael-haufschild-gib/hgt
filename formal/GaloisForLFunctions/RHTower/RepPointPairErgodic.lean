import GaloisForLFunctions.RHTower.RepPointPairDirichletForm

/-!
# Ergodicity: the top of the spectrum is attained only by invariant constants

Let `φ ≥ 0` with `φ(0) > 0`, and let `U` be a continuous `ρ`-equivariant field, square-integrable on
the modular cell, with `L_φ U = m U` for the kernel mass `m`.  The Dirichlet form identity gives
`∫_𝒟 ∫_ℍ φ(u(z, w)) ‖U(z) − U(w)‖² = 0`, so for almost every `z ∈ 𝒟`, `U(w) = U(z)` whenever
`φ(u(z, w)) > 0`.  This set of good centres is `SL(2, ℤ)`-invariant, hence of full measure in `ℍ`,
so every small ball contains a good centre and `U` is constant on it.  A locally constant function
on the connected `ℍ` is constant, and equivariance makes its value `ρ`-invariant
(`eq_const_of_ppApply_eq_mass`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology RCLike
open scoped MatrixGroups ENNReal InnerProductSpace Pointwise

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-- **The set of null-energy centres is full in `ℍ`.**  If a property of points of `ℍ` is
`SL(2, ℤ)`-invariant and holds almost everywhere on the modular cell, it holds almost everywhere. -/
theorem ae_of_ae_fd_of_invariant {P : ℍ → Prop} (hinv : ∀ (B : SL(2, ℤ)) z, P z → P (B • z))
    (hfd : ∀ᵐ z ∂cellMeasure, P z) : ∀ᵐ z, P z := by
  rw [ae_iff] at hfd ⊢
  have hfd' : volume ({z | ¬ P z} ∩ fd) = 0 := by
    rwa [Measure.restrict_apply' isClosed_fd.measurableSet] at hfd
  have hsub : {z | ¬ P z} ⊆ ⋃ B : SL(2, ℤ), B • ({z | ¬ P z} ∩ fd) := by
    intro z hz
    obtain ⟨g, hg⟩ := exists_smul_mem_fd z
    refine mem_iUnion.2 ⟨g⁻¹, ?_⟩
    refine ⟨g • z, ⟨fun h => hz ?_, hg⟩, inv_smul_smul g z⟩
    simpa using hinv g⁻¹ _ h
  refine measure_mono_null hsub (measure_iUnion_null fun B => ?_)
  rw [measure_smul]
  exact hfd'

section Ergodic

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφ0 : ∀ u, 0 ≤ φ u) (hφR : KernelSupport φ R)
  {U : ℍ → EuclideanSpace ℂ ι} (hUc : Continuous U) (hUe : IsEquivariant ρ U)

include hφc hφM hR hφ0 hφR hUc hUe in
/-- **Ergodicity.**  If `φ ≥ 0`, `φ(0) > 0` and `L_φ U = m U` for the kernel mass `m`, then the
continuous equivariant field `U` is a constant with `ρ`-invariant value. -/
theorem eq_const_of_ppApply_eq_mass (hφpos : 0 < φ 0) (hU2 : MemLp U 2 cellMeasure)
    (heig : ∀ z, ppApply ρ φ U z = ((kernelMassR φ : ℝ) : ℂ) • U z) :
    ∃ c : EuclideanSpace ℂ ι, (∀ B, ρ B c = c) ∧ ∀ z, U z = c := by
  -- the Dirichlet energy vanishes
  have hD := integral_dirichlet hφc hφM hR hφ0 hφR hUc hUe hU2
  have hre : ∀ z, re ⟪U z, ppApply ρ φ U z⟫_ℂ = kernelMassR φ * ‖U z‖ ^ 2 := by
    intro z
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (U z)
    rw [heig, inner_smul_right]
    simp only [RCLike.re_to_complex] at h ⊢
    rw [Complex.re_ofReal_mul, h]
  simp_rw [hre] at hD
  rw [integral_const_mul] at hD
  have hD0 : ∫ z in fd, ∫ w, φ (pairU z w) * ‖U z - U w‖ ^ 2 = 0 := by rw [hD]; ring
  have hF0 : ∀ z, 0 ≤ ∫ w, φ (pairU z w) * ‖U z - U w‖ ^ 2 := fun z =>
    integral_nonneg fun w => mul_nonneg (hφ0 _) (sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg hF0
    (integrable_dirichlet_inner hφc hφM hR hφ0 hφR hUc hUe hU2)).1 hD0
  -- good centres
  set P : ℍ → Prop := fun z => ∀ w, 0 < φ (pairU z w) → U w = U z
  have hgood : ∀ᵐ z ∂cellMeasure, P z := by
    filter_upwards [hae] with z hz w hw
    by_contra hne
    have hcont : Continuous (fun w => φ (pairU z w) * ‖U z - U w‖ ^ 2) :=
      (hφc.comp (continuous_pairU_right z)).mul ((continuous_const.sub hUc).norm.pow 2)
    have hsupp : HasCompactSupport (fun w => φ (pairU z w) * ‖U z - U w‖ ^ 2) := by
      refine HasCompactSupport.intro (isCompact_pairU_le z R) fun w hw => ?_
      simp only [Set.mem_setOf_eq, not_le] at hw
      simp [hφR _ hw]
    have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hsupp
      (fun w => mul_nonneg (hφ0 _) (sq_nonneg _)) (x := w)
      (mul_ne_zero hw.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hne)))))
    have : (∫ w, φ (pairU z w) * ‖U z - U w‖ ^ 2) = 0 := hz
    linarith
  have hinv : ∀ (B : SL(2, ℤ)) z, P z → P (B • z) := by
    intro B z hz w hw
    have hw' : 0 < φ (pairU z (B⁻¹ • w)) := by
      rwa [← pairU_smul_int B, smul_inv_smul]
    have h1 := hz _ hw'
    calc U w = U (B • (B⁻¹ • w)) := by rw [smul_inv_smul]
      _ = ρ B (U (B⁻¹ • w)) := hUe _ _
      _ = ρ B (U z) := by rw [h1]
      _ = U (B • z) := (hUe _ _).symm
  have hall := ae_of_ae_fd_of_invariant hinv hgood
  -- local constancy
  obtain ⟨ε, hε, hφε⟩ : ∃ ε > 0, ∀ u, u < ε → 0 ≤ u → 0 < φ u := by
    have := hφc.continuousAt (x := 0) |>.eventually (lt_mem_nhds hφpos)
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 this
    exact ⟨ε, hε, fun u hu hu0 => h (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hu0]; exact hu)⟩
  have hloc : IsLocallyConstant U := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    have hnhd : {q : ℍ × ℍ | pairU q.1 q.2 < ε} ∈ 𝓝 (z, z) :=
      continuous_pairU.continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (by
          show pairU z z < ε
          rw [pairU_eq_cosh, dist_self, Real.cosh_zero, sub_self, zero_div]
          exact hε))
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hnhd
    obtain ⟨N, hNsub, hNo, hzN⟩ := mem_nhds_iff.1 (inter_mem hu hv)
    have hpos : 0 < volume N := hNo.measure_pos volume ⟨z, hzN⟩
    obtain ⟨z', hz'N, hz'P⟩ : ∃ z' ∈ N, P z' := by
      by_contra h
      push Not at h
      have : volume N = 0 := measure_mono_null (fun x hx => h x hx) (ae_iff.1 hall)
      exact hpos.ne' this
    have hconst : ∀ w ∈ N, U w = U z' := by
      intro w hw
      have hmem : (z', w) ∈ u ×ˢ v := ⟨(hNsub hz'N).1, (hNsub hw).2⟩
      have hlt : pairU z' w < ε := huv hmem
      exact hz'P w (hφε _ hlt (pairU_nonneg _ _))
    filter_upwards [hNo.mem_nhds hzN] with w hw
    rw [hconst w hw, hconst z hzN]
  refine ⟨U UpperHalfPlane.I, fun B => ?_, fun z =>
    hloc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _)⟩
  rw [← hUe, hloc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ (B • UpperHalfPlane.I))
    (mem_univ UpperHalfPlane.I)]

end Ergodic

end

end GaloisForLFunctions.RHTower.RepPointPair
