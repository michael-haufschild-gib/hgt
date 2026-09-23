import GaloisForLFunctions.HTGeometry.ModularDirichletFormIntegrationByParts

/-!
# Closability of the modular Dirichlet form

The form embedding `J : V → L²(𝒟)` of the modular Dirichlet form is injective.  An element of the
form domain `V ⊆ L²(𝒟)³` is a limit `(u_n, y∂_x u_n, y∂_y u_n)` of embedded pre-domain elements;
if its first coordinate vanishes, the other two coordinates pair to zero with every interior test
weight `y φ` (`φ ∈ C¹_c(𝒟°)`), because integration by parts turns the pairing of `y∂_v u_n` with
`y φ` into the pairing of `u_n` with `y · (y ∂_v φ)`, which tends to zero.  A square-integrable
function on `𝒟` that pairs to zero with every smooth interior test function vanishes almost
everywhere, by the fundamental lemma of the calculus of variations transported through the chart.

Consequently the covariance `J J†` is injective with dense range, and its closed inverse is the
Friedrichs Laplacian `1 − Δ` of the modular surface.
-/

open UpperHalfPlane MeasureTheory ModularGroup Set Topology
open scoped InnerProductSpace ContDiff

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Interior test functions and their weights -/

/-- A `C¹` test function on `ℂ` with compact support inside `𝒟°`. -/
structure InteriorTest where
  φ : ℂ → ℂ
  contDiff : ContDiff ℝ 1 φ
  compact : HasCompactSupport φ
  support_subset : tsupport φ ⊆ fdoImage

/-- The weight `y φ` on `ℍ`. -/
def InteriorTest.weight (T : InteriorTest) (z : ℍ) : ℂ := (z.im : ℂ) * T.φ z

/-- The derived weight `y · (y ∂_v φ)` on `ℍ`. -/
def InteriorTest.weightD (T : InteriorTest) (v : ℂ) (z : ℍ) : ℂ :=
  (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ T.φ z v)

/-- A continuous function on `ℂ` with compact support, multiplied by a power of `y`, is bounded on
`ℍ`. -/
theorem exists_bound_im_pow_mul {g : ℂ → ℂ} (hg : Continuous g) (hs : HasCompactSupport g)
    (k : ℕ) : ∃ C : ℝ, ∀ z : ℍ, ‖(z.im : ℂ) ^ k * g z‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := hg.bounded_above_of_compact_support hs
  obtain ⟨Y, hY⟩ := hs.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  refine ⟨(|Y| ^ k) * C₁, fun z => ?_⟩
  by_cases hz : (z : ℂ) ∈ tsupport g
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |z.im| ≤ |Y| := by
      have := hY _ hz
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self Y)
    have h2 : ‖g z‖ ≤ C₁ := hC₁ z
    have h3 : 0 ≤ ‖g z‖ := norm_nonneg _
    calc |z.im| ^ k * ‖g z‖ ≤ |Y| ^ k * ‖g z‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h1 k) h3
      _ ≤ |Y| ^ k * C₁ := mul_le_mul_of_nonneg_left h2 (by positivity)
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, norm_zero]
    have h0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0)
    positivity

theorem continuous_im_pow_mul {g : ℂ → ℂ} (hg : Continuous g) (k : ℕ) :
    Continuous fun z : ℍ => (z.im : ℂ) ^ k * g z :=
  ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow k).mul (hg.comp continuous_coe)

theorem memLp_im_pow_mul {g : ℂ → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) (k : ℕ) :
    MemLp (fun z : ℍ => (z.im : ℂ) ^ k * g z) 2 modularCellMeasure := by
  obtain ⟨C, hC⟩ := exists_bound_im_pow_mul hg hs k
  exact MemLp.of_bound (continuous_im_pow_mul hg k).aestronglyMeasurable C (ae_of_all _ hC)

theorem InteriorTest.continuous_fderiv (T : InteriorTest) (v : ℂ) :
    Continuous fun w => fderiv ℝ T.φ w v :=
  (T.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem InteriorTest.tsupport_fderiv_subset (T : InteriorTest) (v : ℂ) :
    tsupport (fun w => fderiv ℝ T.φ w v) ⊆ tsupport T.φ := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro w hw
  by_contra hcon
  apply hw
  have h0 : T.φ =ᶠ[nhds w] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport T.φ).isOpen_compl.mem_nhds hcon] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  show fderiv ℝ T.φ w v = 0
  rw [h0.fderiv_eq, fderiv_const_apply]
  rfl

theorem InteriorTest.hasCompactSupport_fderiv (T : InteriorTest) (v : ℂ) :
    HasCompactSupport fun w => fderiv ℝ T.φ w v :=
  T.compact.of_isClosed_subset (isClosed_tsupport _) (T.tsupport_fderiv_subset v)

theorem InteriorTest.weight_eq (T : InteriorTest) :
    T.weight = fun z : ℍ => (z.im : ℂ) ^ (1 : ℕ) * T.φ z := by
  funext z; simp [InteriorTest.weight]

theorem InteriorTest.weightD_eq (T : InteriorTest) (v : ℂ) :
    T.weightD v = fun z : ℍ => (z.im : ℂ) ^ (2 : ℕ) * fderiv ℝ T.φ z v := by
  funext z; simp [InteriorTest.weightD, pow_two, mul_assoc]

/-- The conjugate weight `conj (y φ)`. -/
def InteriorTest.conjWeight (T : InteriorTest) (z : ℍ) : ℂ := starRingEnd ℂ (T.weight z)

/-- The conjugate derived weight `conj (y · (y ∂_v φ))`. -/
def InteriorTest.conjWeightD (T : InteriorTest) (v : ℂ) (z : ℍ) : ℂ :=
  starRingEnd ℂ (T.weightD v z)

theorem InteriorTest.memLp_conjWeight (T : InteriorTest) :
    MemLp T.conjWeight 2 modularCellMeasure := by
  have h := memLp_im_pow_mul (Complex.continuous_conj.comp T.contDiff.continuous)
    (T.compact.comp_left (map_zero _)) 1
  have heq : T.conjWeight = fun z : ℍ => (z.im : ℂ) ^ (1 : ℕ) * starRingEnd ℂ (T.φ z) := by
    funext z; simp [InteriorTest.conjWeight, InteriorTest.weight]
  rw [heq]; exact h

theorem InteriorTest.memLp_conjWeightD (T : InteriorTest) (v : ℂ) :
    MemLp (T.conjWeightD v) 2 modularCellMeasure := by
  have h := memLp_im_pow_mul (Complex.continuous_conj.comp (T.continuous_fderiv v))
    ((T.hasCompactSupport_fderiv v).comp_left (map_zero _)) 2
  have heq : T.conjWeightD v =
      fun z : ℍ => (z.im : ℂ) ^ (2 : ℕ) * starRingEnd ℂ (fderiv ℝ T.φ z v) := by
    funext z; simp [InteriorTest.conjWeightD, InteriorTest.weightD, pow_two, mul_assoc]
  rw [heq]; exact h

/-! ## Pairings and test functionals -/

/-- The pairing `F ↦ ⟪w, F⟫ = ∫_𝒟 conj(w) · F dμ` with a square-integrable weight. -/
def pairing (w : ℍ → ℂ) (hw : MemLp w 2 modularCellMeasure) : ModularL2 →L[ℂ] ℂ :=
  innerSL ℂ (toModularL2 w hw)

theorem pairing_apply (w : ℍ → ℂ) (hw : MemLp w 2 modularCellMeasure) (F : ModularL2) :
    pairing w hw F = ∫ z in fd, starRingEnd ℂ (w z) * modularToLp F z ∂volume := by
  show ⟪toModularL2 w hw, F⟫_ℂ = _
  have h := L2.inner_def (𝕜 := ℂ) (MemLp.toLp w hw) (modularToLp F)
  refine h.trans (integral_congr_ae ?_)
  filter_upwards [MemLp.coeFn_toLp hw] with z hz
  rw [hz, RCLike.inner_apply, mul_comm]

theorem pairing_toModularL2 (w : ℍ → ℂ) (hw : MemLp w 2 modularCellMeasure) (f : ℍ → ℂ)
    (hf : MemLp f 2 modularCellMeasure) :
    pairing w hw (toModularL2 f hf) = ∫ z in fd, starRingEnd ℂ (w z) * f z ∂volume := by
  rw [pairing_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf] with z hz
  rw [show modularToLp (toModularL2 f hf) z = f z from hz]

/-- The functional `x ↦ ⟪y φ, x_i⟫ + ⟪y (y ∂_v φ), x_0⟫` on `L²(𝒟)³`. -/
def testFunctional (T : InteriorTest) (i : Fin 3) (v : ℂ) : FormTriple →L[ℂ] ℂ :=
  (pairing T.conjWeight T.memLp_conjWeight).comp (PiLp.proj 2 (fun _ : Fin 3 => ModularL2) i) +
    (pairing (T.conjWeightD v) (T.memLp_conjWeightD v)).comp
      (PiLp.proj 2 (fun _ : Fin 3 => ModularL2) 0)

theorem testFunctional_apply (T : InteriorTest) (i : Fin 3) (v : ℂ) (x : FormTriple) :
    testFunctional T i v x = pairing T.conjWeight T.memLp_conjWeight (x.ofLp i) +
      pairing (T.conjWeightD v) (T.memLp_conjWeightD v) (x.ofLp 0) := rfl

/-- Integration by parts: the `∂_x` test functional vanishes on the embedded pre-domain. -/
theorem testFunctional_formEmbeddingMap_X (T : InteriorTest) (u : formPreDomain) :
    testFunctional T 1 1 (formEmbeddingMap u) = 0 := by
  rw [testFunctional_apply, formEmbeddingMap_apply, formEmbeddingMap_apply]
  show pairing _ _ (toModularL2 (hypGradX u) (formPreDomain.memLp_gradX u)) +
    pairing _ _ (toModularL2 u (formPreDomain.memLp u)) = 0
  rw [pairing_toModularL2, pairing_toModularL2]
  have h := setIntegral_fd_testWeight_hypGradX (formPreDomain.c1 u) T.contDiff T.compact
    T.support_subset
  simp only [InteriorTest.conjWeight, InteriorTest.conjWeightD, Complex.conj_conj,
    InteriorTest.weight, InteriorTest.weightD]
  rw [h, neg_add_cancel]

/-- Integration by parts: the `∂_y` test functional vanishes on the embedded pre-domain. -/
theorem testFunctional_formEmbeddingMap_Y (T : InteriorTest) (u : formPreDomain) :
    testFunctional T 2 Complex.I (formEmbeddingMap u) = 0 := by
  rw [testFunctional_apply, formEmbeddingMap_apply, formEmbeddingMap_apply]
  show pairing _ _ (toModularL2 (hypGradY u) (formPreDomain.memLp_gradY u)) +
    pairing _ _ (toModularL2 u (formPreDomain.memLp u)) = 0
  rw [pairing_toModularL2, pairing_toModularL2]
  have h := setIntegral_fd_testWeight_hypGradY (formPreDomain.c1 u) T.contDiff T.compact
    T.support_subset
  simp only [InteriorTest.conjWeight, InteriorTest.conjWeightD, Complex.conj_conj,
    InteriorTest.weight, InteriorTest.weightD]
  rw [h, neg_add_cancel]

/-- The `∂_x` test functional vanishes on the form domain. -/
theorem formDomainClosure_le_ker_X (T : InteriorTest) :
    formDomainClosure ≤ LinearMap.ker (testFunctional T 1 1 : FormTriple →ₗ[ℂ] ℂ) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (testFunctional T 1 1).isClosed_ker
  rintro _ ⟨u, rfl⟩
  exact testFunctional_formEmbeddingMap_X T u

/-- The `∂_y` test functional vanishes on the form domain. -/
theorem formDomainClosure_le_ker_Y (T : InteriorTest) :
    formDomainClosure ≤ LinearMap.ker (testFunctional T 2 Complex.I : FormTriple →ₗ[ℂ] ℂ) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (testFunctional T 2 Complex.I).isClosed_ker
  rintro _ ⟨u, rfl⟩
  exact testFunctional_formEmbeddingMap_Y T u

/-! ## The fundamental lemma on the fundamental domain -/

/-- A square-integrable function on `𝒟` that pairs to zero with every interior test weight `y φ`
vanishes. -/
theorem eq_zero_of_forall_interiorTest (F : ModularL2)
    (h : ∀ T : InteriorTest, ∫ z in fd, T.weight z * modularToLp F z ∂volume = 0) : F = 0 := by
  set f : ℍ → ℂ := ⇑(modularToLp F) with hf
  set ν : Measure ℂ := modularCellMeasure.map UpperHalfPlane.coe with hν
  let G : ℂ → ℂ := fun w => (w.im : ℂ) * f (ofComplex w)
  have hGcoe : ∀ z : ℍ, G z = (z.im : ℂ) * f z := fun z => by simp [G, ofComplex_apply]
  have hGcoe' : G ∘ UpperHalfPlane.coe = fun z => (z.im : ℂ) * f z := funext hGcoe
  have hfm : AEStronglyMeasurable f modularCellMeasure := Lp.aestronglyMeasurable _
  have himc : Continuous fun z : ℍ => (z.im : ℂ) :=
    Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
  have hGm : AEStronglyMeasurable G ν := by
    rw [hν, measurableEmbedding_coe.aestronglyMeasurable_map_iff, hGcoe']
    exact himc.aestronglyMeasurable.mul hfm
  have hfint : Integrable f modularCellMeasure := MemLp.integrable one_le_two (Lp.memLp F)
  have hfoc : Integrable (fun w => f (ofComplex w)) ν := by
    rw [hν, measurableEmbedding_coe.integrable_map_iff]
    exact hfint.congr (ae_of_all _ fun z => by simp [ofComplex_apply])
  have hGloc : LocallyIntegrableOn G fdoImage ν := by
    rw [locallyIntegrableOn_iff isOpen_fdoImage.isLocallyClosed]
    intro K _ hKc
    obtain ⟨Y, hY⟩ := hKc.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
    refine Integrable.mono' ((hfoc.norm.const_mul |Y|).integrableOn) hGm.restrict ?_
    rw [ae_restrict_iff' hKc.measurableSet]
    refine ae_of_all _ fun w hw => ?_
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right ((hY w hw).trans (le_abs_self Y)) (norm_nonneg _)
  -- the test integrals vanish
  have hvan : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ fdoImage →
      ∫ w, g w • G w ∂ν = 0 := by
    intro g hg hgs hgU
    let T : InteriorTest :=
      { φ := fun w => (g w : ℂ)
        contDiff := Complex.ofRealCLM.contDiff.comp (hg.of_le (WithTop.coe_le_coe.mpr le_top))
        compact := hgs.comp_left Complex.ofReal_zero
        support_subset := (closure_mono (Function.support_comp_subset Complex.ofReal_zero g)).trans hgU }
    have hT := h T
    have hmeas : AEStronglyMeasurable (fun w => g w • G w) ν :=
      hg.continuous.aestronglyMeasurable.smul hGm
    rw [hν, integral_map measurable_coe.aemeasurable hmeas]
    rw [← hT]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show g z • G z = T.weight z * f z
    rw [hGcoe, Complex.real_smul]
    simp only [T, InteriorTest.weight]
    ring
  have hae := isOpen_fdoImage.ae_eq_zero_of_integral_contDiff_smul_eq_zero hGloc hvan
  rw [hν, measurableEmbedding_coe.ae_map_iff] at hae
  have hfdo : ∀ᵐ z ∂modularCellMeasure, z ∈ fdo := by
    rw [ae_restrict_iff' isClosed_fd.measurableSet]
    have h0 : ∀ᵐ z ∂(volume : Measure ℍ), z ∉ fd \ fdo :=
      ae_iff.mpr (by simp only [not_not, Set.setOf_mem_eq]; exact volume_fd_diff_fdo)
    filter_upwards [h0] with z hz hzfd
    by_contra hcon
    exact hz ⟨hzfd, hcon⟩
  have hzero : f =ᵐ[modularCellMeasure] 0 := by
    filter_upwards [hae, hfdo] with z hz hzfdo
    have h1 : G z = 0 := hz (mem_image_of_mem _ hzfdo)
    rw [hGcoe] at h1
    have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
    exact (mul_eq_zero.mp h1).resolve_left hy
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hzero

/-! ## Injectivity of the form embedding -/

theorem formInclusion_eq_zero_imp {v : FormDomain} (h0 : formInclusion v = 0) : v = 0 := by
  rw [formInclusion_apply] at h0
  have h1 : (v : FormTriple).ofLp 1 = 0 := by
    apply eq_zero_of_forall_interiorTest
    intro T
    have hker := formDomainClosure_le_ker_X T v.2
    rw [LinearMap.mem_ker] at hker
    change testFunctional T 1 1 v = 0 at hker
    rw [testFunctional_apply, h0, map_zero, add_zero, pairing_apply] at hker
    simpa [InteriorTest.conjWeight, Complex.conj_conj] using hker
  have h2 : (v : FormTriple).ofLp 2 = 0 := by
    apply eq_zero_of_forall_interiorTest
    intro T
    have hker := formDomainClosure_le_ker_Y T v.2
    rw [LinearMap.mem_ker] at hker
    change testFunctional T 2 Complex.I v = 0 at hker
    rw [testFunctional_apply, h0, map_zero, add_zero, pairing_apply] at hker
    simpa [InteriorTest.conjWeight, Complex.conj_conj] using hker
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **Closability of the modular Dirichlet form.**  The form embedding `J : V → L²(𝒟)` is
injective. -/
theorem formInclusion_injective : Function.Injective formInclusion := by
  intro v w hvw
  have := formInclusion_eq_zero_imp (v := v - w) (by rw [map_sub, hvw, sub_self])
  exact sub_eq_zero.mp this

end

end GaloisForLFunctions.HTGeometry
