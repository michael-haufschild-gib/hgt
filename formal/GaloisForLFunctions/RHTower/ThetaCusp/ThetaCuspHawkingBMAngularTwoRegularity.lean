import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularTwoResponse

/-!
# Smooth reconstruction of the complete shift-two angular inverse

The actual native response is localized with every cutoff commutator retained. Smooth original
forcing and planar Sobolev gain give all local orders, then a smooth representative across all
modular seams. Compact test separation proves its classical equation. Restoring the entire cusp
principal field yields a smooth modular solution of `(2-Delta)U=S²` in the original coordinates,
with the previously constructed distributional field and finite-energy correction preserved.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate ENNReal SchwartzMap LineDeriv Laplacian
namespace RHTower.D4BMAngularTwo
open D4BMGlobalAngularResponse D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The native shift-two equation holds for unconjugated tests on the full half-plane. -/
theorem response_lifted_test_equation (q : XiZeroCopy) (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, g.laplaceTest.field z*globalLift (embedding (weakResponse q)) z) -
      2*(∫ z : UpperHalfPlane, g.field z*globalLift (embedding (weakResponse q)) z) =
      -(∫ z : UpperHalfPlane, g.field z*globalLift (forcingVector q) z) := by
  have he := weakResponse_distribution_equation q g.conjugate
  rw [PlanarChartTest.laplaceVector,g.conjugate.laplaceTest.lift_pairing,
    g.conjugate.lift_pairing,g.conjugate.lift_pairing] at he
  simp_rw [g.laplace_conjugate] at he
  simpa only [PlanarChartTest.conjugate,map_star,starRingEnd_apply,star_star] using he

/-- The actual lifted full-forcing response obeys its literal planar distributional
equation on all positive-height charts, including charts crossing modular seams. -/
theorem full_response_global_planar_equation (q : XiZeroCopy)
    (g : PlanarChartTest) :
    (∫ z : ℂ, g.laplacianTest.localValue (embedding (weakResponse q)) z) -
      (2:ℂ)*(∫ z : ℂ, (g.divHeight 2).localValue
        (embedding (weakResponse q)) z) =
      -(∫ z : ℂ, (g.divHeight 2).localValue (forcingVector q) z) := by
  have he := response_lifted_test_equation q g
  rw [g.scalar_planar,g.scalar_planar] at he
  rw [← g.laplacianTest.height_sq_planar]
  convert he using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [g.laplaceTest_field]
  rfl

private theorem lift_local_pair_integrable (g : PlanarChartTest) (u : Space) (ψ : 𝓢(ℂ,ℂ)) :
    Integrable (fun z : ℂ => ψ z*g.localValue u z) :=
  (ψ.memLp 2).integrable_mul (g.localValue_memLp u)

private theorem lifted_product_derivative (g : PlanarChartTest) (ψ : 𝓢(ℂ,ℂ)) (v z : ℂ) :
    ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).field z =
      (g.derivative v).field z*ψ z+g.field z*(∂_{v} ψ) z := by
  change fderiv ℝ (fun w => ψ w*g.field w) z v = _
  rw [fderiv_fun_mul ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt
    (g.smooth.differentiable (by simp)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,PlanarChartTest.derivative]
  ring

private theorem lifted_product_second (g : PlanarChartTest) (ψ : 𝓢(ℂ,ℂ)) (v z : ℂ) :
    (((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).derivative v).field z =
      ((g.derivative v).derivative v).field z*ψ z +
      2*(g.derivative v).field z*(∂_{v} ψ) z + g.field z*(∂_{v} (∂_{v} ψ)) z := by
  have he : ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).field =
      (fun w => (g.derivative v).field w*ψ w+g.field w*(∂_{v} ψ) w) :=
    funext (lifted_product_derivative g ψ v)
  change fderiv ℝ ((g.mulSmooth ψ (ψ.smooth ⊤)).derivative v).field z v = _
  rw [he]
  have hg := (g.smooth.differentiable (by simp)).differentiableAt (x := z)
  have hgd := ((g.derivative v).smooth.differentiable (by simp)).differentiableAt (x := z)
  have hp := ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt (x := z)
  have hpd := (((∂_{v} ψ).smooth ⊤).differentiable (by simp)).differentiableAt (x := z)
  rw [fderiv_fun_add (hgd.fun_mul hp) (hg.fun_mul hpd),
    fderiv_fun_mul hgd hp,fderiv_fun_mul hg hpd]
  simp only [add_apply,smul_apply,smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,PlanarChartTest.derivative]
  ring

private theorem lifted_product_laplacian (g : PlanarChartTest) (ψ : 𝓢(ℂ,ℂ)) (z : ℂ) :
    (g.mulSmooth ψ (ψ.smooth ⊤)).laplacianTest.field z =
      ψ z*g.laplacianTest.field z +
      2*(∑ i : Fin 2, (∂_{direction i} ψ) z*(g.derivative (direction i)).field z) +
      (Δ ψ) z*g.field z := by
  have hb (i : Fin 2) : Complex.orthonormalBasisOneI i = direction i := by
    rw [Complex.coe_orthonormalBasisOneI]
    rfl
  have hΔ : (Δ ψ) z = ∑ i : Fin 2, (∂_{direction i} (∂_{direction i} ψ)) z := by
    rw [SchwartzMap.laplacian_eq_sum Complex.orthonormalBasisOneI]
    simp only [sum_apply,hb]
  change (∑ i : Fin 2,
    (((g.mulSmooth ψ (ψ.smooth ⊤)).derivative (direction i)).derivative (direction i)).field z) = _
  simp_rw [lifted_product_second]
  simp only [hΔ,PlanarChartTest.laplacianTest,PlanarChartTest.planarLaplacian,
    PlanarChartTest.derivative,Fin.sum_univ_two]
  ring

private theorem lifted_product_laplacian_integral (g : PlanarChartTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) :
    (∫ z : ℂ, (g.mulSmooth ψ (ψ.smooth ⊤)).laplacianTest.localValue u z) =
      g.laplacianTest.localDistribution u ψ +
      2*(∑ i : Fin 2, (g.derivative (direction i)).localDistribution u (∂_{direction i} ψ)) +
      g.localDistribution u (Δ ψ) := by
  simp only [PlanarChartTest.localDistribution_apply]
  rw [← integral_finsetSum _ (fun i _ => lift_local_pair_integrable _ _ _),← integral_const_mul]
  have h0 := lift_local_pair_integrable g.laplacianTest u ψ
  have h1 : Integrable (fun z : ℂ => 2*(∑ i : Fin 2,
      (∂_{direction i} ψ) z*(g.derivative (direction i)).localValue u z)) :=
    (integrable_finsetSum Finset.univ (fun (i : Fin 2) _ =>
      lift_local_pair_integrable (g.derivative (direction i)) u (∂_{direction i} ψ))).const_mul 2
  have h2 := lift_local_pair_integrable g u (Δ ψ)
  rw [← integral_add h0 h1,← integral_add (h0.fun_add h1) h2]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.localValue,lifted_product_laplacian,Fin.sum_univ_two]
  ring

private theorem lifted_product_divHeight_integral (g : PlanarChartTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) (n : ℕ) :
    (∫ z : ℂ, ((g.mulSmooth ψ (ψ.smooth ⊤)).divHeight n).localValue u z) =
      (g.divHeight n).localDistribution u ψ := by
  rw [PlanarChartTest.localDistribution_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.localValue,PlanarChartTest.divHeight,PlanarChartTest.mulSmooth]
  ring

/-- The complete cutoff Laplacian is derived from the actual scalar equation.
Derivatives of localized scalars retain all cutoff terms, without asserting that
individual hyperbolic frame components are modular scalar functions. -/
theorem full_response_global_cutoff_laplacian (q : XiZeroCopy)
    (g : PlanarChartTest) :
    Δ (g.localDistribution (embedding (weakResponse q))) =
      (2:ℂ) • (∑ i : Fin 2, ∂_{direction i}
        ((g.derivative (direction i)).localDistribution (embedding (weakResponse q)))) -
      g.laplacianTest.localDistribution (embedding (weakResponse q)) +
      (2:ℂ) • (g.divHeight 2).localDistribution
        (embedding (weakResponse q)) -
      (g.divHeight 2).localDistribution (forcingVector q) := by
  ext ψ
  have he := full_response_global_planar_equation q (g.mulSmooth ψ (ψ.smooth ⊤))
  rw [lifted_product_laplacian_integral,lifted_product_divHeight_integral,
    lifted_product_divHeight_integral] at he
  rw [TemperedDistribution.laplacian_apply_apply]
  simp only [Fin.sum_univ_two] at he ⊢
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul,
    TemperedDistribution.lineDerivOp_apply_apply,map_neg]
  linear_combination he


/-- The actual globally smooth forcing localized by an arbitrary compact positive-height test. -/
def forcingTest (g : PlanarChartTest) (q : XiZeroCopy) :
    PlanarChartTest where
  field z := g.field z*globalForcing q (ofComplex z)
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport g.field
    · have hy := g.support hz
      have hf := globalForcing_smooth q (ofComplex z)
      rw [ofComplex_apply_of_im_pos hy] at hf
      exact g.smooth.contDiffAt.mul hf
    · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hz] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  compact := g.compact.mul_right
  support := (closure_mono (Function.support_mul_subset_left _ _)).trans g.support

private theorem global_ae_to_planar {P : ℂ → Prop}
    (hP : ∀ᵐ z : UpperHalfPlane ∂volume, P (z:ℂ)) :
    ∀ᵐ z ∂((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}), P z := by
  have hm : ∀ᵐ z ∂Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane), P z :=
    UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mpr hP
  rw [map_volume_chart_eq] at hm
  have hd : Measurable (fun z : ℂ => (chartDensity z : ℝ≥0∞)) := by
    unfold chartDensity
    fun_prop
  have hh := (ae_withDensity_iff hd).mp hm
  filter_upwards [hh,ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz hy
  apply hz
  simp [chartDensity,ne_of_gt hy]

/-- Every compact planar localization identifies the smooth glued source with the actual lifted L² forcing. -/
theorem forcing_localValue_ae (g : PlanarChartTest)
    (q : XiZeroCopy) :
    g.localValue (forcingVector q) =ᵐ[(volume : Measure ℂ)]
      (forcingTest g q).field := by
  have hp := global_ae_to_planar (P := fun z : ℂ =>
    globalLift (forcingVector q) (ofComplex z) = globalForcing q (ofComplex z)) (by
      filter_upwards [globalForcing_ae_lift q] with z hz
      simpa only [ofComplex_apply] using hz.symm)
  have hh := (ae_restrict_iff' isOpen_upperHalfPlaneSet.measurableSet).mp hp
  filter_upwards [hh] with z hz
  by_cases hy : 0 < z.im
  · simp only [PlanarChartTest.localValue,forcingTest,hz hy]
  · have hg : g.field z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (g.support h))
    simp [PlanarChartTest.localValue,forcingTest,hg]

/-- The actual global forcing distribution has a Schwartz representative on every compact chart. -/
theorem forcing_localDistribution_eq (g : PlanarChartTest)
    (q : XiZeroCopy) :
    g.localDistribution (forcingVector q) =
      ((forcingTest g q).compact.toSchwartzMap
        (forcingTest g q).smooth : 𝓢'(ℂ,ℂ)) := by
  ext ψ
  rw [g.localDistribution_apply]
  change _ = ∫ z : ℂ, ψ z • (forcingTest g q).field z
  apply integral_congr_ae
  filter_upwards [forcing_localValue_ae g q] with z hz
  rw [hz]
  rfl

/-- The original full forcing has every local Sobolev order across all modular seams and elliptic points. -/
theorem full_forcing_global_local_sobolev (q : XiZeroCopy)
    (g : PlanarChartTest) (s : ℝ) : MemSobolev s 2 (g.localDistribution (forcingVector q)) := by
  rw [forcing_localDistribution_eq]
  exact SchwartzMap.memSobolev _


private theorem all_orders_sum_sobolev {s : ℝ} {f : Fin 2 → 𝓢'(ℂ,ℂ)}
    (hf : ∀ i, MemSobolev s 2 (f i)) : MemSobolev s 2 (∑ i, f i) := by
  simpa only [Fin.sum_univ_two] using (hf 0).add (hf 1)

private theorem global_response_all_orders_step (q : XiZeroCopy)
    (s : ℝ)
    (hh : ∀ g : PlanarChartTest, MemSobolev s 2
      (g.localDistribution (embedding (weakResponse q)))) (g : PlanarChartTest) :
    MemSobolev (s+1) 2 (g.localDistribution (embedding (weakResponse q))) := by
  have hscalar (a : PlanarChartTest) := (hh a).mono (show s-1 ≤ s by linarith)
  have hsource (a : PlanarChartTest) :=
    full_forcing_global_local_sobolev q a (s-1)
  have hl : MemSobolev (s-1) 2
      (Δ (g.localDistribution (embedding (weakResponse q)))) := by
    rw [full_response_global_cutoff_laplacian]
    have hD := all_orders_sum_sobolev (fun i =>
      (hh (g.derivative (direction i))).lineDerivOp (m := direction i))
    exact (((hD.smul (2:ℂ)).sub (hscalar g.laplacianTest)).add
      ((hscalar (g.divHeight 2)).smul ((2:ℂ)))).sub (hsource (g.divHeight 2))
  have hout := planar_sobolev_gain_two (hscalar g) hl
  convert hout using 1
  ring

/-- The actual globally lifted response has every local Sobolev order, with no seam exclusion. -/
theorem full_response_global_local_all_orders (q : XiZeroCopy)
    (n : ℕ) (g : PlanarChartTest) :
    MemSobolev (n : ℝ) 2 (g.localDistribution (embedding (weakResponse q))) := by
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero]
    exact memSobolev_zero_iff.mpr ⟨g.localVector _,rfl⟩
  | succ n ih =>
    simpa only [Nat.cast_add,Nat.cast_one] using global_response_all_orders_step q n ih g

/-- Every compact chart localization of the actual global response has a constructed smooth representative. -/
theorem full_response_global_local_smooth (q : XiZeroCopy) (g : PlanarChartTest) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      f =ᵐ[volume] g.localValue (embedding (weakResponse q)) := by
  obtain ⟨f,hf,he⟩ := planar_all_sobolev_smooth_representative
    (g.localVector (embedding (weakResponse q)))
    (fun n => full_response_global_local_all_orders q n g)
  exact ⟨f,hf,he.trans (g.localValue_memLp _).coeFn_toLp⟩


private theorem exists_planarChartTest_ne_zero {z : ℂ} (hz : z ∈ {z : ℂ | 0 < z.im}) :
    ∃ g : PlanarChartTest, g.field z ≠ 0 := by
  obtain ⟨b,hb,hc,hd,_,he⟩ := exists_contDiff_tsupport_subset (n := ⊤) (isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hcc : HasCompactSupport (Complex.ofRealCLM ∘ b) := hc.comp_left rfl
  have hdd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ b) := Complex.ofRealCLM.contDiff.comp hd
  have hss : tsupport (Complex.ofRealCLM ∘ b) ⊆ {z : ℂ | 0 < z.im} := by
    apply Subset.trans _ hb
    exact closure_mono (by intro x hx; simpa using hx)
  refine ⟨⟨Complex.ofRealCLM ∘ b,hdd,hcc,hss⟩,?_⟩
  change (b z : ℂ) ≠ 0
  simp [he]

/-- Smooth representatives of all compact chart localizations glue across all modular seams.
The glued field represents the actual globally lifted scalar in planar measure. -/
private theorem global_smooth_representative_of_localizations (u : Space)
    (hu : ∀ g : PlanarChartTest, ∃ r : ℂ → ℂ, ContDiff ℝ ∞ r ∧ r =ᵐ[volume] g.localValue u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
      f =ᵐ[volume.restrict {z : ℂ | 0 < z.im}] (fun z : ℂ => globalLift u (ofComplex z)) := by
  classical
  choose R hR hRa using hu
  have hcross (g h : PlanarChartTest) (z : ℂ) : g.field z * R h z = h.field z * R g z := by
    have hae : (fun w : ℂ => g.field w * R h w) =ᵐ[volume]
        (fun w : ℂ => h.field w * R g w) := by
      filter_upwards [hRa g,hRa h] with w hgw hhw
      rw [hgw,hhw]
      simp only [PlanarChartTest.localValue]
      ring
    exact congrFun (Measure.eq_of_ae_eq hae (g.smooth.continuous.mul (hR h).continuous)
      (h.smooth.continuous.mul (hR g).continuous)) z
  let chosen (z : ℂ) (hz : z ∈ {z : ℂ | 0 < z.im}) : PlanarChartTest :=
    Classical.choose (exists_planarChartTest_ne_zero hz)
  have chosen_ne (z : ℂ) (hz : z ∈ {z : ℂ | 0 < z.im}) : (chosen z hz).field z ≠ 0 :=
    Classical.choose_spec (exists_planarChartTest_ne_zero hz)
  let f (z : ℂ) : ℂ := if hz : z ∈ {z : ℂ | 0 < z.im} then
    R (chosen z hz) z / (chosen z hz).field z else 0
  have hquot (z : ℂ) (g : PlanarChartTest) (hg : g.field z ≠ 0) : f z = R g z / g.field z := by
    have hz : z ∈ {z : ℂ | 0 < z.im} := g.support (subset_tsupport g.field hg)
    dsimp only [f]
    rw [dif_pos hz]
    apply (div_eq_div_iff (chosen_ne z hz) hg).mpr
    have he := hcross (chosen z hz) g z
    linear_combination -he
  have hs : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} := by
    intro z hz
    let g := chosen z hz
    have hg : g.field z ≠ 0 := chosen_ne z hz
    have hq : ContDiffAt ℝ ∞ (fun w : ℂ => R g w / g.field w) z := by
      simpa only [div_eq_mul_inv] using (hR g).contDiffAt.mul
        (g.smooth.contDiffAt.fun_inv hg)
    apply (hq.congr_of_eventuallyEq _).contDiffWithinAt
    filter_upwards [(isOpen_ne_fun g.smooth.continuous continuous_const).mem_nhds hg] with w hw
    exact hquot w g hw
  let U (g : PlanarChartTest) : Set ℂ := {z | g.field z ≠ 0}
  have hU (g : PlanarChartTest) : IsOpen (U g) := isOpen_ne_fun g.smooth.continuous continuous_const
  have hcover : {z : ℂ | 0 < z.im} ⊆ ⋃ g : PlanarChartTest, U g := by
    intro z hz
    obtain ⟨g,hg⟩ := exists_planarChartTest_ne_zero hz
    exact mem_iUnion.mpr ⟨g,hg⟩
  have hpatch (g : PlanarChartTest) : f =ᵐ[volume.restrict (U g)] (fun z : ℂ => globalLift u (ofComplex z)) := by
    apply (ae_restrict_iff' (hU g).measurableSet).mpr
    filter_upwards [hRa g] with z hz hg
    rw [hquot z g hg,hz]
    simp only [PlanarChartTest.localValue]
    exact mul_div_cancel_left₀ _ hg
  obtain ⟨C,hC,hcov⟩ := (HereditarilyLindelofSpace.isLindelof {z : ℂ | 0 < z.im}).elim_countable_subcover
    U hU hcover
  have he : f =ᵐ[volume.restrict (⋃ g ∈ C, U g)] (fun z : ℂ => globalLift u (ofComplex z)) :=
    (ae_restrict_biUnion_iff U hC _).mpr (fun g _ => hpatch g)
  exact ⟨f,hs,ae_restrict_of_ae_restrict_of_subset hcov he⟩

/-- The actual response has a smooth planar representative on the entire upper half-plane. -/
theorem full_response_global_planar_smooth (q : XiZeroCopy) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
      f =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
        (fun z => globalLift (embedding (weakResponse q)) (ofComplex z)) :=
  global_smooth_representative_of_localizations _ (full_response_global_local_smooth q)

/-- The constructed globally smooth representative of the original full-forcing response. -/
def globalResponse (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  (full_response_global_planar_smooth q).choose (z:ℂ)

/-- The actual full-forcing response is smooth across every seam and elliptic fixed point. -/
theorem globalResponse_smooth (q : XiZeroCopy) :
    ChartSmooth (globalResponse q) := by
  intro z
  have hs := (full_response_global_planar_smooth q).choose_spec.1.contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  apply hs.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,globalResponse,ofComplex_apply_of_im_pos hw]

/-- The smooth global response is the original lifted L² solution in full invariant volume. -/
theorem globalResponse_ae_lift (q : XiZeroCopy) :
    globalResponse q =ᵐ[(volume : Measure UpperHalfPlane)]
      globalLift (embedding (weakResponse q)) := by
  have he := (full_response_global_planar_smooth q).choose_spec.2
  have hd := (withDensity_absolutelyContinuous
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im})
    (fun z => (chartDensity z : ℝ≥0∞))).ae_le he
  rw [← map_volume_chart_eq] at hd
  have hn := UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mp hd
  filter_upwards [hn] with z hz
  simpa only [ofComplex_apply,globalResponse] using hz

private theorem chartSmooth_eq_of_ae_eq {f g : UpperHalfPlane → ℂ}
    (hf : ChartSmooth f) (hg : ChartSmooth g) (he : f =ᵐ[(volume : Measure UpperHalfPlane)] g) : f = g := by
  have hm : ∀ᵐ z ∂Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane),
      f (ofComplex z) = g (ofComplex z) :=
    UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mpr (by
      filter_upwards [he] with z hz
      simpa only [ofComplex_apply] using hz)
  rw [map_volume_chart_eq] at hm
  have hd : Measurable (fun z : ℂ => (chartDensity z : ℝ≥0∞)) := by
    unfold chartDensity
    fun_prop
  have hh := (ae_withDensity_iff hd).mp hm
  have hae : (fun z : ℂ => f (ofComplex z)) =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
      (fun z : ℂ => g (ofComplex z)) := by
    filter_upwards [hh,ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz hy
    exact hz (by simp [chartDensity,ne_of_gt hy])
  have hc (a : UpperHalfPlane → ℂ) (ha : ChartSmooth a) :
      ContinuousOn (fun z : ℂ => a (ofComplex z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hh := ha (ofComplex z)
    rw [ofComplex_apply_of_im_pos hz] at hh
    exact hh.continuousAt.continuousWithinAt
  have hp := Measure.eqOn_open_of_ae_eq hae isOpen_upperHalfPlaneSet (hc f hf) (hc g hg)
  funext z
  simpa only [ofComplex_apply] using hp z.im_pos

/-- The globally smooth response obeys the original modular identifications pointwise. -/
theorem globalResponse_invariant (q : XiZeroCopy) (γ : PSL2Z)
    (z : UpperHalfPlane) : globalResponse q (γ • z) = globalResponse q z := by
  apply congrFun (chartSmooth_eq_of_ae_eq ((globalResponse_smooth q).modular_pullback γ)
    (globalResponse_smooth q) ?_) z
  have ht := (measurePreserving_smul γ (volume : Measure UpperHalfPlane)).quasiMeasurePreserving.ae
    (globalResponse_ae_lift q)
  filter_upwards [ht,globalResponse_ae_lift q] with w hw he
  rw [hw,he,globalLift_invariant]

/-- The smooth, globally modular response represents the original solution in its native Hilbert space. -/
theorem globalResponse_native_ae (q : XiZeroCopy) :
    globalResponse q =ᵐ[measure] embedding (weakResponse q) := by
  have ht : globalResponse q =ᵐ[measure] globalLift (embedding (weakResponse q)) :=
    ae_restrict_of_ae (globalResponse_ae_lift q)
  exact ht.trans (globalLift_ae_eq (embedding (weakResponse q)))


/-- Every actual scalar localization equals the localization of the constructed smooth response. -/
theorem response_localValue_ae (g : PlanarChartTest)
    (q : XiZeroCopy) :
    g.localValue (embedding (weakResponse q)) =ᵐ[(volume : Measure ℂ)]
      (fun z => g.field z*globalResponse q (ofComplex z)) := by
  have he := (ae_restrict_iff' isOpen_upperHalfPlaneSet.measurableSet).mp
    (full_response_global_planar_smooth q).choose_spec.2
  filter_upwards [he] with z hz
  by_cases hy : 0 < z.im
  · have hh := hz hy
    change g.field z*globalLift (embedding (weakResponse q)) (ofComplex z) = _
    rw [← hh]
    simp only [globalResponse,ofComplex_apply_of_im_pos hy]
  · have hg : g.field z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (g.support h))
    simp [PlanarChartTest.localValue,hg]

/-- The exact full planar test equation holds for the actual smooth representatives. -/
theorem full_response_smooth_planar_test (q : XiZeroCopy) (g : PlanarChartTest) :
    (∫ z : ℂ, g.laplacianTest.field z*globalResponse q (ofComplex z)) -
      (2:ℂ)*(∫ z : ℂ, (g.divHeight 2).field z*globalResponse q (ofComplex z)) =
      -(∫ z : ℂ, (g.divHeight 2).field z*globalForcing q (ofComplex z)) := by
  have hR (a : PlanarChartTest) := integral_congr_ae (response_localValue_ae a q)
  have hF := integral_congr_ae (forcing_localValue_ae (g.divHeight 2) q)
  have h := full_response_global_planar_equation q g
  rw [hR,hR,hF] at h
  exact h

private def responseResidual (q : XiZeroCopy) (z : ℂ) : ℂ :=
  planarLaplacian (globalResponse q ∘ ofComplex) z -
    ((2:ℂ)*globalResponse q (ofComplex z)-globalForcing q (ofComplex z)) /
      (z.im : ℂ)^(2 : ℕ)

private theorem responseResidual_continuousOn (q : XiZeroCopy) :
    ContinuousOn (responseResidual q) {z : ℂ | 0 < z.im} := by
  have hR := (globalResponse_smooth q).planar_contDiffOn
  have hF := (globalForcing_smooth q).planar_contDiffOn
  apply (planarLaplacian_contDiffOn hR).continuousOn.sub
  exact ((continuousOn_const.mul hR.continuousOn).sub hF.continuousOn).div
    ((Complex.ofRealCLM.continuous.comp Complex.continuous_im).pow 2).continuousOn
    (fun z hz => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))

private theorem responseResidual_test_zero (q : XiZeroCopy) (g : PlanarChartTest) :
    (∫ z : ℂ, g.field z*responseResidual q z) = 0 := by
  let R := globalResponse q ∘ ofComplex
  let F := globalForcing q ∘ ofComplex
  have hR := (globalResponse_smooth q).planar_contDiffOn
  have hF := (globalForcing_smooth q).planar_contDiffOn
  have h0 := g.integrable_mul_planar (planarLaplacian R) (planarLaplacian_contDiffOn hR).continuousOn
  have h1 := (g.divHeight 2).integrable_mul_planar R hR.continuousOn
  have h2 := (g.divHeight 2).integrable_mul_planar F hF.continuousOn
  have h01 : Integrable (fun z : ℂ => planarLaplacian R z*g.field z -
      (2:ℂ)*(R z*(g.divHeight 2).field z)) volume :=
    h0.sub (h1.const_mul ((2:ℂ)))
  have he := full_response_smooth_planar_test q g
  change (∫ z : ℂ, g.laplacianTest.field z*R z) -
    (2:ℂ)*(∫ z : ℂ, (g.divHeight 2).field z*R z) =
    -(∫ z : ℂ, (g.divHeight 2).field z*F z) at he
  rw [g.laplacian_green R hR] at he
  have he' : (∫ z : ℂ, planarLaplacian R z*g.field z) -
      (2:ℂ)*(∫ z : ℂ, R z*(g.divHeight 2).field z) +
      (∫ z : ℂ, F z*(g.divHeight 2).field z) = 0 := by
    have heq := congrArg (fun c : ℂ => c + ∫ z : ℂ, (g.divHeight 2).field z*F z) he
    simpa only [neg_add_cancel,mul_comm,R,F,Function.comp_apply] using heq
  calc
    _ = ∫ z : ℂ, (planarLaplacian R z*g.field z -
        (2:ℂ)*(R z*(g.divHeight 2).field z)) + F z*(g.divHeight 2).field z := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [responseResidual,PlanarChartTest.divHeight,R,F,Function.comp_apply]
      ring
    _ = _ := by
      rw [integral_add h01 h2,integral_sub h0 (h1.const_mul ((2:ℂ))),
        integral_const_mul]
      exact he'

/-- The reconstructed response satisfies the classical equation at every positive-height point. -/
theorem globalResponse_classical_planar (q : XiZeroCopy) (z : ℂ) (hz : 0 < z.im) :
    planarLaplacian (globalResponse q ∘ ofComplex) z =
      ((2:ℂ)*globalResponse q (ofComplex z)-globalForcing q (ofComplex z)) /
        (z.im : ℂ)^(2 : ℕ) := by
  have hc := responseResidual_continuousOn q
  have ha := isOpen_upperHalfPlaneSet.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hc.locallyIntegrableOn isOpen_upperHalfPlaneSet.measurableSet) (fun b hb hk hs => by
      let g : PlanarChartTest := ⟨Complex.ofRealCLM ∘ b,Complex.ofRealCLM.contDiff.comp hb,
        hk.comp_left rfl,(closure_mono (by intro w hw; simpa using hw)).trans hs⟩
      simpa only [g,Function.comp_apply,Complex.ofRealCLM_apply,Complex.real_smul] using
        responseResidual_test_zero q g)
  have har : responseResidual q =ᵐ[volume.restrict {z : ℂ | 0 < z.im}] (fun _ => 0) :=
    (ae_restrict_iff' isOpen_upperHalfPlaneSet.measurableSet).mpr ha
  have hp := Measure.eqOn_open_of_ae_eq har isOpen_upperHalfPlaneSet hc continuousOn_const
  exact sub_eq_zero.mp (hp hz)

/-- The original complete forcing drives the actual smooth response pointwise on the entire half-plane. -/
theorem globalResponse_classical_equation (q : XiZeroCopy) (z : UpperHalfPlane) :
    chartLaplacian (globalResponse q) z - (2:ℂ)*globalResponse q z =
      -globalForcing q z := by
  have h := globalResponse_classical_planar q (z:ℂ) z.im_pos
  simp only [ofComplex_apply,coe_im] at h
  rw [chartLaplacian,h]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]
  ring

private theorem chartLaplacian_sub (f g : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (hg : ChartSmooth g) (z : UpperHalfPlane) :
    chartLaplacian (fun w => f w-g w) z = chartLaplacian f z-chartLaplacian g z := by
  let F := f ∘ ofComplex
  let G := g ∘ ofComplex
  have hd (i : Fin 2) :
      fderiv ℝ (fun w => fderiv ℝ (fun w => F w-G w) w (direction i)) (z:ℂ) (direction i) =
        fderiv ℝ (fun w => fderiv ℝ F w (direction i)) (z:ℂ) (direction i) -
        fderiv ℝ (fun w => fderiv ℝ G w (direction i)) (z:ℂ) (direction i) := by
    have he : (fun w => fderiv ℝ (fun w => F w-G w) w (direction i)) =ᶠ[𝓝 (z:ℂ)]
        (fun w => fderiv ℝ F w (direction i)-fderiv ℝ G w (direction i)) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
      rw [fderiv_fun_sub ((hf ⟨w,hw⟩).differentiableAt (by simp))
        ((hg ⟨w,hw⟩).differentiableAt (by simp)),sub_apply]
    have hF : DifferentiableAt ℝ (fun w => fderiv ℝ F w (direction i)) (z:ℂ) := (((hf z).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
    have hG : DifferentiableAt ℝ (fun w => fderiv ℝ G w (direction i)) (z:ℂ) := (((hg z).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
    rw [he.fderiv_eq,fderiv_fun_sub hF hG,sub_apply]
  change (z.im : ℂ)^(2 : ℕ)*(∑ i : Fin 2,
    fderiv ℝ (fun w => fderiv ℝ (fun w => F w-G w) w (direction i)) (z:ℂ) (direction i)) = _
  rw [Finset.sum_congr rfl (fun i _ => hd i),Finset.sum_sub_distrib,mul_sub]
  rfl

/-- The smooth, globally modular inverse of the entire original squared source. -/
def smoothFullResponse (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  globalResponse q z-globalCuspCutoff q z

/-- The complete response is smooth, including at modular seams and elliptic points. -/
theorem smoothFullResponse_smooth (q : XiZeroCopy) : ChartSmooth (smoothFullResponse q) := by
  intro z
  exact (globalResponse_smooth q z).sub (globalCuspCutoff_smooth q z)

/-- The complete smooth response satisfies the original modular identifications pointwise. -/
theorem smoothFullResponse_invariant (q : XiZeroCopy) (γ : PSL2Z) (z : UpperHalfPlane) :
    smoothFullResponse q (γ • z) = smoothFullResponse q z := by
  simp only [smoothFullResponse,globalResponse_invariant,globalCuspCutoff_invariant]

/-- Smooth reconstruction preserves the full previously constructed distributional field. -/
theorem smoothFullResponse_ae_fullResponse (q : XiZeroCopy) :
    smoothFullResponse q =ᵐ[(volume : Measure UpperHalfPlane)] fullResponse q := by
  filter_upwards [globalResponse_ae_lift q] with z hz
  simp only [smoothFullResponse,fullResponse,hz]

/-- The exact cusp subtraction recovers the chosen finite-energy correction. -/
theorem smoothFullResponse_renormalized_native (q : XiZeroCopy) :
    (fun z => smoothFullResponse q z+globalCuspCutoff q z) =ᵐ[measure]
      embedding (weakResponse q) := by
  filter_upwards [globalResponse_native_ae q] with z hz
  simpa only [smoothFullResponse,sub_add_cancel] using hz

/-- The actual shift-two inverse solves the complete original source equation pointwise. -/
theorem smoothFullResponse_classical_equation (q : XiZeroCopy) (z : UpperHalfPlane) :
    2*smoothFullResponse q z-chartLaplacian (smoothFullResponse q) z =
      scalar (D4BMGlobalAngularResponse.center q) (coordinates z)^(2 : ℕ) := by
  change 2*(globalResponse q z-globalCuspCutoff q z)-
    chartLaplacian (fun w => globalResponse q w-globalCuspCutoff q w) z = _
  rw [chartLaplacian_sub _ _ (globalResponse_smooth q) (globalCuspCutoff_smooth q)]
  have he := globalResponse_classical_equation q z
  unfold globalForcing at he
  linear_combination -he

/-- The complete inverse in the literal angular metric coordinates. -/
def coordinateResponse (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  smoothFullResponse q (ofComplex (angularCoordinates.symm z))

/-- Coordinate conversion preserves the complete response pointwise. -/
theorem coordinateResponse_coordinates (q : XiZeroCopy) (z : UpperHalfPlane) :
    coordinateResponse q (coordinates z) = smoothFullResponse q z := by
  change smoothFullResponse q (ofComplex (angularCoordinates.symm (angularCoordinates (z:ℂ)))) = _
  rw [angularCoordinates.symm_apply_apply,ofComplex_apply]

/-- All original angular coordinate derivatives of the complete inverse exist. -/
theorem coordinateResponse_smooth (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (coordinateResponse q) z := by
  have hi : 0 < (angularCoordinates.symm z).im := by
    change 0 < ((z 0 : ℂ)+(z 1 : ℂ)*Complex.I).im
    simpa using hz
  have h := smoothFullResponse_smooth q (ofComplex (angularCoordinates.symm z))
  change ContDiffAt ℝ ∞ (smoothFullResponse q ∘ ofComplex) _ at h
  rw [ofComplex_apply_of_im_pos hi] at h
  change ContDiffAt ℝ ∞ ((smoothFullResponse q ∘ ofComplex) ∘ angularCoordinates.symm) z
  exact h.comp z angularCoordinates.symm.contDiff.contDiffAt

/-- The original coordinate Laplacian retains the entire literal scalar-square source. -/
theorem coordinateResponse_equation (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    2*coordinateResponse q z-D4BMAngularSeries.hyperbolicLaplacian (coordinateResponse q) z =
      scalar (D4BMGlobalAngularResponse.center q) z^(2 : ℕ) := by
  let w : UpperHalfPlane := ⟨angularCoordinates.symm z,by
    change 0 < ((z 0 : ℂ)+(z 1 : ℂ)*Complex.I).im
    simpa using hz⟩
  have hw : coordinates w = z := by
    change angularCoordinates (angularCoordinates.symm z) = z
    exact angularCoordinates.apply_symm_apply z
  have hf : (fun v => coordinateResponse q (coordinates v)) = smoothFullResponse q :=
    funext (coordinateResponse_coordinates q)
  have he := smoothFullResponse_classical_equation q w
  rw [← hf,chartLaplacian_coordinates,hw] at he
  dsimp only at he
  rw [hw] at he
  exact he

end
end RHTower.D4BMAngularTwo
