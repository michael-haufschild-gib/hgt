import GaloisForLFunctions.HTGeometry.ModularDirichletFormClosable

/-!
# Periodisation of interior functions into the modular form pre-domain

A `C¹` function `ψ` on `ℍ` with compact support inside the interior `𝒟°` of the fundamental domain
extends to an `SL(2, ℤ)`-invariant function `periodize ψ` on `ℍ`: at `z` it is `ψ(γ z)` for the
(unique up to sign) `γ` with `γ z ∈ 𝒟°`, and `0` if there is none.  Because the action is properly
discontinuous, every point has a neighbourhood on which `periodize ψ` is either `ψ ∘ γ` for one
fixed `γ` or identically zero, so `periodize ψ` is `C¹`; it is bounded, and on `𝒟°` it coincides
with `ψ` together with its hyperbolic gradient.  Hence `periodize ψ` lies in the form pre-domain
and the `L²` class of `ψ` on `𝒟` lies in the range of the form embedding `J`.
-/

open UpperHalfPlane MeasureTheory ModularGroup Set Topology
open scoped InnerProductSpace MatrixGroups

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Proper discontinuity of `SL(2, ℤ)` on `ℍ` -/

theorem continuous_modular_smul (γ : SL(2, ℤ)) : Continuous fun z : ℍ => γ • z := by
  show Continuous fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z
  exact continuous_const_smul _

/-- Only finitely many elements of `SL(2, ℤ)` move a compact set to meet a compact set. -/
theorem finite_modular_smul_inter {K L : Set ℍ} (hK : IsCompact K) (hL : IsCompact L) :
    {γ : SL(2, ℤ) | ((γ • ·) '' K ∩ L).Nonempty}.Finite := by
  let e : SL(2, ℤ) → 𝒮ℒ := fun γ =>
    ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩
  have he : Function.Injective e := fun γ γ' h =>
    Matrix.SpecialLinearGroup.mapGL_injective (congrArg Subtype.val h)
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) hK hL
  refine (hfin.preimage he.injOn).subset ?_
  intro γ hγ
  exact hγ

/-! ## Periodisation -/

open scoped Classical in
/-- The `SL(2, ℤ)`-periodisation of a function on `ℍ` supported in `𝒟°`. -/
def periodize (ψ : ℍ → ℂ) (z : ℍ) : ℂ :=
  if h : ∃ γ : SL(2, ℤ), γ • z ∈ fdo then ψ (h.choose • z) else 0

theorem periodize_eq_of_mem (ψ : ℍ → ℂ) {z : ℍ} {γ : SL(2, ℤ)} (hγ : γ • z ∈ fdo) :
    periodize ψ z = ψ (γ • z) := by
  have h : ∃ γ : SL(2, ℤ), γ • z ∈ fdo := ⟨γ, hγ⟩
  unfold periodize
  rw [dif_pos h]
  congr 1
  have h1 : (h.choose * γ⁻¹) • (γ • z) ∈ fdo := by
    rw [smul_smul, inv_mul_cancel_right]; exact h.choose_spec
  have h2 := eq_smul_self_of_mem_fdo_mem_fdo hγ h1
  rw [smul_smul, inv_mul_cancel_right] at h2
  exact h2.symm

theorem periodize_eq_zero_of_forall (ψ : ℍ → ℂ) {z : ℍ}
    (h : ∀ γ : SL(2, ℤ), γ • z ∉ tsupport ψ) : periodize ψ z = 0 := by
  unfold periodize
  split_ifs with hz
  · exact image_eq_zero_of_notMem_tsupport (h _)
  · rfl

theorem periodize_smul (ψ : ℍ → ℂ) (δ : SL(2, ℤ)) (z : ℍ) :
    periodize ψ (δ • z) = periodize ψ z := by
  by_cases h : ∃ γ : SL(2, ℤ), γ • z ∈ fdo
  · obtain ⟨γ, hγ⟩ := h
    have h' : (γ * δ⁻¹) • (δ • z) ∈ fdo := by
      rw [smul_smul, inv_mul_cancel_right]; exact hγ
    rw [periodize_eq_of_mem ψ h', periodize_eq_of_mem ψ hγ, smul_smul, inv_mul_cancel_right]
  · have h' : ¬ ∃ γ : SL(2, ℤ), γ • (δ • z) ∈ fdo := by
      rintro ⟨γ, hγ⟩
      exact h ⟨γ * δ, by rw [mul_smul]; exact hγ⟩
    unfold periodize
    rw [dif_neg h, dif_neg h']

theorem periodize_eq_of_mem_fdo (ψ : ℍ → ℂ) {z : ℍ} (hz : z ∈ fdo) : periodize ψ z = ψ z := by
  have h := periodize_eq_of_mem ψ (γ := 1) (by simpa using hz)
  simpa using h

theorem norm_periodize_le {ψ : ℍ → ℂ} {C : ℝ} (hC : ∀ z, ‖ψ z‖ ≤ C) (hC0 : 0 ≤ C) (z : ℍ) :
    ‖periodize ψ z‖ ≤ C := by
  unfold periodize
  split_ifs
  · exact hC _
  · simpa using hC0

/-! ## The Möbius maps in the chart -/

/-- The Möbius transformation of `γ ∈ SL(2, ℤ)` as a function on `ℂ`. -/
def moebiusChart (γ : SL(2, ℤ)) (w : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))

theorem moebiusChart_coe (γ : SL(2, ℤ)) (z : ℍ) : moebiusChart γ (z : ℂ) = ((γ • z : ℍ) : ℂ) := by
  rw [coe_specialLinearGroup_apply]
  simp [moebiusChart]

theorem moebiusChart_denom_ne_zero (γ : SL(2, ℤ)) {w : ℂ} (hw : w ∈ upperSet) :
    (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ) ≠ 0 := by
  intro h
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  have hw' : (0 : ℝ) < w.im := hw
  rcases him with h0 | h0
  · have hc : (γ 1 0 : ℤ) = 0 := by exact_mod_cast h0
    have hd : (γ 1 1 : ℤ) = 0 := by
      rw [hc] at hre
      simp at hre
      exact_mod_cast hre
    rw [hc, hd] at hdet
    simp at hdet
  · exact absurd h0 hw'.ne'

theorem contDiffOn_moebiusChart (γ : SL(2, ℤ)) : ContDiffOn ℝ 1 (moebiusChart γ) upperSet := by
  unfold moebiusChart
  have h : ContDiffOn ℂ 1 (fun w : ℂ => ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) /
      ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))) upperSet := by
    refine ContDiffOn.div ?_ ?_ (fun w hw => moebiusChart_denom_ne_zero γ hw)
    · fun_prop
    · fun_prop
  exact h.restrict_scalars ℝ

theorem moebiusChart_mem_upperSet (γ : SL(2, ℤ)) {w : ℂ} (hw : w ∈ upperSet) :
    moebiusChart γ w ∈ upperSet := by
  have h := moebiusChart_coe γ ⟨w, hw⟩
  show 0 < (moebiusChart γ w).im
  rw [show (⟨w, hw⟩ : ℍ) = ⟨w, hw⟩ from rfl] at h
  have : moebiusChart γ w = ((γ • (⟨w, hw⟩ : ℍ) : ℍ) : ℂ) := h
  rw [this]
  exact (γ • (⟨w, hw⟩ : ℍ)).im_pos

/-- The composite `ψ ∘ γ` of a chart-`C¹` function with a Möbius map is chart-`C¹`. -/
theorem isChartC1_comp_smul {ψ : ℍ → ℂ} (hψ : IsChartC1 ψ) (γ : SL(2, ℤ)) :
    IsChartC1 fun z => ψ (γ • z) := by
  unfold IsChartC1
  have hcomp : ContDiffOn ℝ 1 (chartFun ψ ∘ moebiusChart γ) upperSet :=
    hψ.comp (contDiffOn_moebiusChart γ) (fun w hw => moebiusChart_mem_upperSet γ hw)
  refine hcomp.congr fun w hw => ?_
  show ψ (γ • ofComplex w) = ψ (ofComplex (moebiusChart γ w))
  rw [ofComplex_apply_of_im_pos hw]
  have h := moebiusChart_coe γ ⟨w, hw⟩
  rw [show moebiusChart γ w = ((γ • (⟨w, hw⟩ : ℍ) : ℍ) : ℂ) from h, ofComplex_apply]

/-! ## Smoothness of the periodisation -/

/-- **The periodisation is `C¹`.**  Near a point some translate of which lies in `𝒟°` it is
`ψ ∘ γ`; near any other point it vanishes identically, by proper discontinuity. -/
theorem isChartC1_periodize {ψ : ℍ → ℂ} (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ fdo) : IsChartC1 (periodize ψ) := by
  unfold IsChartC1
  apply contDiffOn_of_locally_contDiffOn
  intro w hw
  set z₀ : ℍ := ⟨w, hw⟩ with hz₀
  by_cases hcase : ∃ γ : SL(2, ℤ), γ • z₀ ∈ fdo
  · obtain ⟨γ, hγ⟩ := hcase
    refine ⟨UpperHalfPlane.coe '' ((fun z : ℍ => γ • z) ⁻¹' fdo),
      isOpenEmbedding_coe.isOpenMap _ (isOpen_fdo.preimage (continuous_modular_smul γ)),
      ⟨z₀, hγ, rfl⟩, ?_⟩
    have hc := isChartC1_comp_smul hψ γ
    refine (ContDiffOn.mono hc inter_subset_left).congr ?_
    rintro w' ⟨_, z, hz, rfl⟩
    show periodize ψ (ofComplex (z : ℂ)) = ψ (γ • ofComplex (z : ℂ))
    rw [ofComplex_apply, periodize_eq_of_mem ψ hz]
  · push Not at hcase
    have hKc : IsCompact (tsupport ψ) := hs
    obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds z₀
    set S := {γ : SL(2, ℤ) | ((γ • ·) '' L ∩ tsupport ψ).Nonempty} with hS
    have hSf : S.Finite := finite_modular_smul_inter hLc hKc
    set N : Set ℍ := interior L ∩ ⋂ γ ∈ S, (fun z : ℍ => γ • z) ⁻¹' (tsupport ψ)ᶜ with hN
    have hNopen : IsOpen N :=
      isOpen_interior.inter (hSf.isOpen_biInter fun γ _ =>
        (isClosed_tsupport ψ).isOpen_compl.preimage (continuous_modular_smul γ))
    have hz₀N : z₀ ∈ N := by
      refine ⟨mem_interior_iff_mem_nhds.mpr hLn, mem_iInter₂.mpr fun γ _ => ?_⟩
      intro h
      exact hcase γ (hK h)
    have hzero : ∀ z ∈ N, periodize ψ z = 0 := by
      intro z hz
      apply periodize_eq_zero_of_forall
      intro γ hγK
      by_cases hγS : γ ∈ S
      · exact (mem_iInter₂.mp hz.2 γ hγS) hγK
      · exact hγS ⟨γ • z, ⟨z, interior_subset hz.1, rfl⟩, hγK⟩
    refine ⟨UpperHalfPlane.coe '' N, isOpenEmbedding_coe.isOpenMap _ hNopen, ⟨z₀, hz₀N, rfl⟩, ?_⟩
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    rintro w' ⟨_, z, hzN, rfl⟩
    show periodize ψ (ofComplex (z : ℂ)) = 0
    rw [ofComplex_apply]
    exact hzero z hzN

/-! ## Continuity and the hyperbolic gradient -/

theorem IsChartC1.continuous {ψ : ℍ → ℂ} (hψ : IsChartC1 ψ) : Continuous ψ := by
  have h : ψ = chartFun ψ ∘ UpperHalfPlane.coe := by
    funext z; simp [chartFun, ofComplex_apply]
  rw [h]
  exact ((ContDiffOn.continuousOn hψ).comp_continuous continuous_coe fun z => z.im_pos)

theorem continuous_hypGradX {ψ : ℍ → ℂ} (hψ : IsChartC1 ψ) : Continuous (hypGradX ψ) := by
  have h1 : Continuous fun z : ℍ => fderiv ℝ (chartFun ψ) (z : ℂ) 1 :=
    (hψ.continuousOn_fderiv 1).comp_continuous continuous_coe fun z => z.im_pos
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul h1

theorem continuous_hypGradY {ψ : ℍ → ℂ} (hψ : IsChartC1 ψ) : Continuous (hypGradY ψ) := by
  have h1 : Continuous fun z : ℍ => fderiv ℝ (chartFun ψ) (z : ℂ) Complex.I :=
    (hψ.continuousOn_fderiv Complex.I).comp_continuous continuous_coe fun z => z.im_pos
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul h1

/-- Two functions that agree on an open subset of `ℍ` have the same chart derivative there. -/
theorem chartDeriv_congr_of_eqOn {u₁ u₂ : ℍ → ℂ} {O : Set ℍ} (hO : IsOpen O) (h : EqOn u₁ u₂ O)
    (v : ℂ) {z : ℍ} (hz : z ∈ O) : chartDeriv u₁ v z = chartDeriv u₂ v z := by
  unfold chartDeriv
  have hev : chartFun u₁ =ᶠ[nhds (z : ℂ)] chartFun u₂ := by
    have hmem : UpperHalfPlane.coe '' O ∈ nhds (z : ℂ) :=
      (isOpenEmbedding_coe.isOpenMap _ hO).mem_nhds ⟨z, hz, rfl⟩
    filter_upwards [hmem] with w hw
    obtain ⟨z', hz', rfl⟩ := hw
    show u₁ (ofComplex (z' : ℂ)) = u₂ (ofComplex (z' : ℂ))
    rw [ofComplex_apply]
    exact h hz'
  rw [hev.fderiv_eq]

theorem hypGradX_congr_of_eqOn {u₁ u₂ : ℍ → ℂ} {O : Set ℍ} (hO : IsOpen O) (h : EqOn u₁ u₂ O)
    {z : ℍ} (hz : z ∈ O) : hypGradX u₁ z = hypGradX u₂ z := by
  unfold hypGradX; rw [chartDeriv_congr_of_eqOn hO h 1 hz]

theorem hypGradY_congr_of_eqOn {u₁ u₂ : ℍ → ℂ} {O : Set ℍ} (hO : IsOpen O) (h : EqOn u₁ u₂ O)
    {z : ℍ} (hz : z ∈ O) : hypGradY u₁ z = hypGradY u₂ z := by
  unfold hypGradY; rw [chartDeriv_congr_of_eqOn hO h Complex.I hz]

/-- The hyperbolic gradient of a function vanishes outside its support. -/
theorem hypGradX_eq_zero_of_notMem_tsupport {ψ : ℍ → ℂ} {z : ℍ} (hz : z ∉ tsupport ψ) :
    hypGradX ψ z = 0 := by
  have h := hypGradX_congr_of_eqOn (u₂ := fun _ => 0) (isClosed_tsupport ψ).isOpen_compl
    (fun z' hz' => image_eq_zero_of_notMem_tsupport hz') hz
  rw [h, hypGradX_const]

theorem hypGradY_eq_zero_of_notMem_tsupport {ψ : ℍ → ℂ} {z : ℍ} (hz : z ∉ tsupport ψ) :
    hypGradY ψ z = 0 := by
  have h := hypGradY_congr_of_eqOn (u₂ := fun _ => 0) (isClosed_tsupport ψ).isOpen_compl
    (fun z' hz' => image_eq_zero_of_notMem_tsupport hz') hz
  rw [h, hypGradY_const]

theorem hasCompactSupport_hypGradX {ψ : ℍ → ℂ} (hs : HasCompactSupport ψ) :
    HasCompactSupport (hypGradX ψ) :=
  hs.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (fun _ hz => by_contra fun h => hz (hypGradX_eq_zero_of_notMem_tsupport h))
    (isClosed_tsupport ψ))

theorem hasCompactSupport_hypGradY {ψ : ℍ → ℂ} (hs : HasCompactSupport ψ) :
    HasCompactSupport (hypGradY ψ) :=
  hs.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (fun _ hz => by_contra fun h => hz (hypGradY_eq_zero_of_notMem_tsupport h))
    (isClosed_tsupport ψ))

/-! ## Membership in the pre-domain -/

/-- Almost every point of the fundamental domain is interior. -/
theorem ae_mem_fdo : ∀ᵐ z ∂modularCellMeasure, z ∈ fdo := by
  rw [ae_restrict_iff' isClosed_fd.measurableSet]
  have h0 : ∀ᵐ z ∂(volume : Measure ℍ), z ∉ fd \ fdo :=
    ae_iff.mpr (by simp only [not_not, Set.setOf_mem_eq]; exact volume_fd_diff_fdo)
  filter_upwards [h0] with z hz hzfd
  by_contra hcon
  exact hz ⟨hzfd, hcon⟩

theorem memLp_of_continuous_of_bound {u : ℍ → ℂ} (hu : Continuous u) {C : ℝ}
    (hC : ∀ᵐ z ∂modularCellMeasure, ‖u z‖ ≤ C) : MemLp u 2 modularCellMeasure :=
  MemLp.of_bound hu.aestronglyMeasurable C hC

/-- The periodisation of a `C¹` function with compact support in `𝒟°` is in the pre-domain. -/
def periodizePre (ψ : ℍ → ℂ) (hψ : IsChartC1 ψ) (hs : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ fdo) : formPreDomain :=
  ⟨periodize ψ, isChartC1_periodize hψ hs hK, periodize_smul ψ, by
      obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hs
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC ⟨Complex.I, by simp⟩)
      exact memLp_of_continuous_of_bound (isChartC1_periodize hψ hs hK).continuous
        (ae_of_all _ (norm_periodize_le hC hC0)), by
      obtain ⟨C, hC⟩ := (continuous_hypGradX hψ).bounded_above_of_compact_support
        (hasCompactSupport_hypGradX hs)
      refine memLp_of_continuous_of_bound (C := C)
        (continuous_hypGradX (isChartC1_periodize hψ hs hK)) ?_
      filter_upwards [ae_mem_fdo] with z hz
      rw [hypGradX_congr_of_eqOn isOpen_fdo (fun z' hz' => periodize_eq_of_mem_fdo ψ hz') hz]
      exact hC z, by
      obtain ⟨C, hC⟩ := (continuous_hypGradY hψ).bounded_above_of_compact_support
        (hasCompactSupport_hypGradY hs)
      refine memLp_of_continuous_of_bound (C := C)
        (continuous_hypGradY (isChartC1_periodize hψ hs hK)) ?_
      filter_upwards [ae_mem_fdo] with z hz
      rw [hypGradY_congr_of_eqOn isOpen_fdo (fun z' hz' => periodize_eq_of_mem_fdo ψ hz') hz]
      exact hC z⟩

theorem memLp_of_isChartC1_of_hasCompactSupport {ψ : ℍ → ℂ} (hψ : IsChartC1 ψ)
    (hs : HasCompactSupport ψ) : MemLp ψ 2 modularCellMeasure := by
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hs
  exact memLp_of_continuous_of_bound hψ.continuous (ae_of_all _ hC)

/-- **Interior functions lie in the range of the form embedding.**  The `L²(𝒟)` class of a `C¹`
function with compact support in `𝒟°` is the image of its periodisation. -/
theorem toModularL2_mem_range_formInclusion {ψ : ℍ → ℂ} (hψ : IsChartC1 ψ)
    (hs : HasCompactSupport ψ) (hK : tsupport ψ ⊆ fdo) :
    toModularL2 ψ (memLp_of_isChartC1_of_hasCompactSupport hψ hs) ∈ Set.range formInclusion := by
  refine ⟨⟨formEmbeddingMap (periodizePre ψ hψ hs hK),
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)⟩, ?_⟩
  rw [formInclusion_apply]
  show (formEmbeddingMap (periodizePre ψ hψ hs hK)).ofLp 0 = _
  rw [formEmbeddingMap_apply]
  show toModularL2 (periodize ψ) (formPreDomain.memLp (periodizePre ψ hψ hs hK)) = _
  refine toModularL2_congr _ _ ?_
  filter_upwards [ae_mem_fdo] with z hz
  exact periodize_eq_of_mem_fdo ψ hz

end

end GaloisForLFunctions.HTGeometry
