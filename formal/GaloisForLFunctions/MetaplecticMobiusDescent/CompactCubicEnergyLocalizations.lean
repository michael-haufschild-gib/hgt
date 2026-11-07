/-
Compact localization adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.LocalizingTheCompletedCubicEnergy
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.EuclideanRellich

/-!
# Each cutoff gives a compact mass localization

Apply real Euclidean Rellich to the real and imaginary parts of localized
smooth tests, using their common compact support and the actual quotient
energy bound. Reassemble the complex functions, then pass to the completed
energy graph by density. Explicit Borel transport identifies the two
presentations of Euclidean Lebesgue measure used by the Sobolev spaces.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota EuclideanSobolev

lemma euclideanIntegral_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     ∫p,g p) =
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanIntegrable_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Integrable g volume) ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeIntegral_eq_borel (g : EuclideanSpatial→ℝ) :
    (∫p,g p)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) :=
  euclideanIntegral_borel_transport inferInstance inferInstance g

lemma euclideanNativeIntegrable_iff_borel (g : EuclideanSpatial→ℝ) :
    Integrable g volume ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) :=
  euclideanIntegrable_borel_transport inferInstance inferInstance g

def euclideanLp_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) := by
  have he := hm.measurable_eq
  subst m
  exact LinearIsometryEquiv.refl ℂ _

def euclideanNativeLpBorelEquiv : EuclideanL2 ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) :=
  euclideanLp_borel_transport inferInstance inferInstance

lemma euclideanLp_borel_transport_schwartz (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanLp_borel_transport m hm
      (letI : MeasurableSpace EuclideanSpatial := m
       letI : BorelSpace EuclideanSpatial := hm
       f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeLpBorelEquiv_schwartz (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanNativeLpBorelEquiv (f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) :=
  euclideanLp_borel_transport_schwartz inferInstance inferInstance f

lemma euclideanOriginalMeasurable_eq_borel :
    (inferInstance : MeasurableSpace EuclideanSpatial)=borel EuclideanSpatial :=
  BorelSpace.measurable_eq

local instance localizedRellichMeasurableSpace : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance localizedRellichBorelSpace : BorelSpace EuclideanSpatial := ⟨rfl⟩

def kernelLocalizedRealTest (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) : C1c (E := EuclideanSpatial) :=
  ⟨fun p => projection (kernelLocalizedField χ f p),
    (projection.contDiff.comp (kernelLocalizedField_smooth χ f)).of_le (by simp),
    (kernelLocalizedField_compact χ f).comp_left (map_zero projection)⟩

lemma sourceC1c_toL2_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2 («μ» := volume) g‖^2=∫p,‖g.1 p‖^2 := by
  calc
    ‖toL2 («μ» := volume) g‖^2=inner ℝ (toL2 («μ» := volume) g) (toL2 («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2 («μ» := volume) g p) (toL2 («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)
        (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma sourceC1c_toL2Grad_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2Grad («μ» := volume) g‖^2=∫p,‖grad g.1 p‖^2 := by
  calc
    ‖toL2Grad («μ» := volume) g‖^2=inner ℝ (toL2Grad («μ» := volume) g) (toL2Grad («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2Grad («μ» := volume) g p) (toL2Grad («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_grad_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)
        (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma kernelLocalizedRealTest_grad_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) (p : EuclideanSpatial) :
    ‖grad (kernelLocalizedRealTest χ f projection).1 p‖^2≤
      ∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
  have hdiff : DifferentiableAt ℝ (kernelLocalizedField χ f) p :=
    ((kernelLocalizedField_smooth χ f).differentiable (by simp)).differentiableAt
  have hd := (projection.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (kernelLocalizedRealTest χ f projection).1 p=_ at hd
  unfold grad
  rw [LinearIsometryEquiv.norm_map,hd,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual]
  apply Finset.sum_le_sum
  intro j hj
  have hh := hprojection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
  change (projection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)))^2≤_
  simp only [Real.norm_eq_abs] at hh
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2

lemma kernelLocalizedRealTest_energy_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) :
    ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
      ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤
        ‖kernelLocalizedH1 χ f‖^2 := by
  let g := kernelLocalizedRealTest χ f projection
  rw [sourceC1c_toL2_norm_sq,sourceC1c_toL2Grad_norm_sq,kernelLocalizedH1_norm_sq,
    ←integral_add (memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq]
  rw [euclideanNativeIntegral_eq_borel]
  have hden := (euclideanNativeIntegrable_iff_borel (kernelLocalizedDensity χ f)).mp
    (kernelLocalizedDensity_integrable χ f)
  apply integral_mono
    ((memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq.add
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq)
    hden
  intro p
  have hm := hprojection (kernelLocalizedField χ f p)
  have hg := kernelLocalizedRealTest_grad_le χ f projection hprojection p
  change ‖projection (kernelLocalizedField χ f p)‖^2+_≤_
  unfold kernelLocalizedDensity
  nlinarith [norm_nonneg (projection (kernelLocalizedField χ f p)),norm_nonneg (kernelLocalizedField χ f p)]

lemma kernelLocalizedRealTest_support (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) :
    Function.support (kernelLocalizedRealTest χ f projection).1⊆tsupport χ.func := by
  intro p hp
  apply kernelLocalizedField_tsupport χ f
  apply subset_tsupport
  intro hz
  apply hp
  change projection (kernelLocalizedField χ f p)=0
  rw [hz,map_zero]

theorem kernelLocalizedReal_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖)
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)) '' family)) := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  have hCB : 0≤C*B := mul_nonneg hC hB
  have henergy : ∀f∈family,
      ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
        ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤C*B := by
    intro f hf
    exact (kernelLocalizedRealTest_energy_le χ f projection hprojection).trans
      ((hbound f).trans (mul_le_mul_of_nonneg_left (hfamily f hf) hC))
  have hh := c1c_family_precompact (tsupport χ.func) χ.compact
    ((fun f => kernelLocalizedRealTest χ f projection) '' family) (Real.sqrt (C*B))
    (by
      rintro _ ⟨f,hf,rfl⟩
      exact kernelLocalizedRealTest_support χ f projection)
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection))])
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection))])
  simpa only [Set.image_image,Function.comp_def] using hh

abbrev RellichRealL2 := Lp ℝ 2 (volume : Measure EuclideanSpatial)
abbrev RellichComplexL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)

def kernelComplexL2Assemble : (RellichRealL2 × RellichRealL2) →L[ℝ] RellichComplexL2 :=
  (Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.fst ℝ RellichRealL2 RellichRealL2)+
  (Complex.I • Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.snd ℝ RellichRealL2 RellichRealL2)

lemma kernelComplexL2Assemble_localized (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelComplexL2Assemble
      (toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
        toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM))=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := by
  let r := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM)
  let i := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)
  let R := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) r
  let I := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) i
  have hr : (r : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).re :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM).2).coeFn_toLp
  have hi : (i : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).im :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM).2).coeFn_toLp
  change R+Complex.I•I=(kernelLocalizedSchwartz χ f).toLp 2 volume
  apply Lp.ext
  filter_upwards [hr,hi,Complex.ofRealCLM.coeFn_compLpL r,Complex.ofRealCLM.coeFn_compLpL i,
    Lp.coeFn_add R (Complex.I•I),Lp.coeFn_smul Complex.I I,
    (kernelLocalizedSchwartz χ f).coeFn_toLp 2 volume] with p hrp hip hR hI ha hs hf
  rw [ha,Pi.add_apply,hs,Pi.smul_apply,hR,hI,hrp,hip,hf]
  change ((kernelLocalizedField χ f p).re:ℂ)+Complex.I*((kernelLocalizedField χ f p).im:ℂ)=kernelLocalizedField χ f p
  simpa only [mul_comm] using Complex.re_add_im (kernelLocalizedField χ f p)

theorem kernelLocalizedComplex_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => (kernelLocalizedSchwartz χ f).toLp 2 volume) '' family)) := by
  have hr := kernelLocalizedReal_family_precompact χ hinj Complex.reCLM
    (fun z => by change ‖z.re‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z) family B hB hfamily
  have hi := kernelLocalizedReal_family_precompact χ hinj Complex.imCLM
    (fun z => by change ‖z.im‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm z) family B hB hfamily
  have hc := (hr.prod hi).image kernelComplexL2Assemble.continuous
  apply hc.closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
    toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)),?_,?_⟩
  · exact ⟨subset_closure ⟨f,hf,rfl⟩,subset_closure ⟨f,hf,rfl⟩⟩
  · exact kernelComplexL2Assemble_localized χ f

theorem kernelLocalizedNative_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)) := by
  have hc := kernelLocalizedComplex_family_precompact χ hinj family B hB hfamily
  apply (hc.image euclideanNativeLpBorelEquiv.symm.continuous).closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(kernelLocalizedSchwartz χ f).toLp 2 volume,subset_closure ⟨f,hf,rfl⟩,?_⟩
  apply euclideanNativeLpBorelEquiv.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [kernelL2Localize_core χ hinj]
  exact (euclideanNativeLpBorelEquiv_schwartz _).symm

def kernelEnergyLocalizeL2 (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanL2 :=
  (kernelL2Localize χ).comp kernelEnergyMass

theorem kernelEnergyLocalizeL2_isCompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    IsCompactOperator (kernelEnergyLocalizeL2 χ) := by
  let family : Set kernelSmoothTests := {f | ‖kernelEnergyGraphCore f‖≤2}
  let C := closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)
  have hc : IsCompact C := kernelLocalizedNative_family_precompact χ hinj family 4 (by norm_num) (by
    intro f hf
    rw [←kernelEnergyGraphCore_norm_sq]
    change ‖kernelEnergyGraphCore f‖≤2 at hf
    nlinarith [norm_nonneg (kernelEnergyGraphCore f)])
  let T := kernelEnergyLocalizeL2 χ
  have hclosed : IsClosed (T ⁻¹' C) := hc.isClosed.preimage T.continuous
  have hsub : closure (kernelEnergyGraphCore ''
      (kernelEnergyGraphCore ⁻¹' Metric.ball (0 : KernelEnergyGraph) 2))⊆T ⁻¹' C := by
    apply hclosed.closure_subset_iff.mpr
    rintro _ ⟨f,hf,rfl⟩
    change kernelL2Localize χ (kernelEnergyMass (kernelEnergyGraphCore f))∈C
    rw [kernelEnergyMass_core]
    apply subset_closure
    refine ⟨f,?_,rfl⟩
    change ‖kernelEnergyGraphCore f‖≤2
    exact le_of_lt (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right (kernelEnergyGraphCore f)] using hf)
  have hball : Metric.ball (0 : KernelEnergyGraph) 2⊆T ⁻¹' C := by
    intro u hu
    exact hsub (kernelEnergyGraphCore_dense.subset_closure_image_preimage_of_isOpen
      Metric.isOpen_ball hu)
  refine ⟨C,hc,?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : KernelEnergyGraph) (by norm_num : (0 : ℝ)<2)) hball

#print axioms kernelLocalizedReal_family_precompact
#print axioms kernelLocalizedComplex_family_precompact
#print axioms kernelEnergyLocalizeL2_isCompact
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
