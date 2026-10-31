import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalSmoothResponse

/-!
# Global smoothness of modular weak responses

Let `h` be a finite-energy weak solution of `(Δ - L) h = F` in the modular energy domain, for
an arbitrary complex parameter `L` and an arbitrary `L²` forcing `F` whose global modular lift
has a smooth representative. Then the lift of `h` has a smooth representative on the whole
upper half-plane. The proof is the elliptic bootstrap of the zero-indexed theta response,
stated for arbitrary data: global Green integration against seam-crossing chart tests, the
exact localization commutator, a gain of one Sobolev order per step, and gluing of the smooth
local representatives.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup TemperedDistribution
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate ENNReal SchwartzMap LineDeriv Laplacian

namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- The variational form of `(Δ - L) h = F` on the modular energy domain. -/
def ModularWeakSolution (L : ℂ) (F : Space) (h : energyDomain) : Prop :=
  ∀ v : energyDomain, inner ℂ v h - (1-L)*inner ℂ (embedding v) (embedding h) =
    -inner ℂ (embedding v) F

/-- A weak solution satisfies the scalar distribution equation against every seam-crossing
planar chart test. -/
theorem modularWeak_distribution_equation {L : ℂ} {F : Space} {h : energyDomain}
    (hw : ModularWeakSolution L F h) (g : PlanarChartTest) :
    inner ℂ g.laplaceVector (embedding h) -
      L*inner ℂ (embedding g.toChartTest.energyTest) (embedding h) =
      inner ℂ (embedding g.toChartTest.energyTest) F := by
  have he := hw g.toChartTest.energyTest
  rw [energy_inner_decomposition, g.completed_green] at he
  linear_combination -he

/-- The same equation for unconjugated tests, unfolded to the global modular lifts. -/
theorem modularWeak_lifted_test_equation {L : ℂ} {F : Space} {h : energyDomain}
    (hw : ModularWeakSolution L F h) (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, g.laplaceTest.field z*globalLift (embedding h) z) -
      L*(∫ z : UpperHalfPlane, g.field z*globalLift (embedding h) z) =
      ∫ z : UpperHalfPlane, g.field z*globalLift F z := by
  have he := modularWeak_distribution_equation hw g.conjugate
  rw [PlanarChartTest.laplaceVector, g.conjugate.laplaceTest.lift_pairing,
    g.conjugate.lift_pairing, g.conjugate.lift_pairing] at he
  simp_rw [g.laplace_conjugate] at he
  simpa only [PlanarChartTest.conjugate, map_star, starRingEnd_apply, star_star] using he

/-- The planar distributional equation on every positive-height chart. -/
theorem modularWeak_planar_equation {L : ℂ} {F : Space} {h : energyDomain}
    (hw : ModularWeakSolution L F h) (g : PlanarChartTest) :
    (∫ z : ℂ, g.laplacianTest.localValue (embedding h) z) -
      L*(∫ z : ℂ, (g.divHeight 2).localValue (embedding h) z) =
      ∫ z : ℂ, (g.divHeight 2).localValue F z := by
  have he := modularWeak_lifted_test_equation hw g
  rw [g.scalar_planar, g.scalar_planar] at he
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
  simp only [add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, PlanarChartTest.derivative]
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
    fderiv_fun_mul hgd hp, fderiv_fun_mul hg hpd]
  simp only [add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, PlanarChartTest.derivative]
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
    simp only [sum_apply, hb]
  change (∑ i : Fin 2,
    (((g.mulSmooth ψ (ψ.smooth ⊤)).derivative (direction i)).derivative (direction i)).field z) = _
  simp_rw [lifted_product_second]
  simp only [hΔ, PlanarChartTest.laplacianTest, PlanarChartTest.planarLaplacian,
    PlanarChartTest.derivative, Fin.sum_univ_two]
  ring

private theorem lifted_product_laplacian_integral (g : PlanarChartTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) :
    (∫ z : ℂ, (g.mulSmooth ψ (ψ.smooth ⊤)).laplacianTest.localValue u z) =
      g.laplacianTest.localDistribution u ψ +
      2*(∑ i : Fin 2, (g.derivative (direction i)).localDistribution u (∂_{direction i} ψ)) +
      g.localDistribution u (Δ ψ) := by
  simp only [PlanarChartTest.localDistribution_apply]
  rw [← integral_finsetSum _ (fun i _ => lift_local_pair_integrable _ _ _),
    ← integral_const_mul]
  have h0 := lift_local_pair_integrable g.laplacianTest u ψ
  have h1 : Integrable (fun z : ℂ => 2*(∑ i : Fin 2,
      (∂_{direction i} ψ) z*(g.derivative (direction i)).localValue u z)) :=
    (integrable_finsetSum Finset.univ (fun (i : Fin 2) _ =>
      lift_local_pair_integrable (g.derivative (direction i)) u (∂_{direction i} ψ))).const_mul 2
  have h2 := lift_local_pair_integrable g u (Δ ψ)
  rw [← integral_add h0 h1, ← integral_add (h0.fun_add h1) h2]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.localValue, lifted_product_laplacian, Fin.sum_univ_two]
  ring

private theorem lifted_product_divHeight_integral (g : PlanarChartTest) (u : Space)
    (ψ : 𝓢(ℂ,ℂ)) (n : ℕ) :
    (∫ z : ℂ, ((g.mulSmooth ψ (ψ.smooth ⊤)).divHeight n).localValue u z) =
      (g.divHeight n).localDistribution u ψ := by
  rw [PlanarChartTest.localDistribution_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.localValue, PlanarChartTest.divHeight, PlanarChartTest.mulSmooth]
  ring

/-- The exact localization commutator: the Euclidean Laplacian of a localized weak solution,
with every cutoff term retained. -/
theorem modularWeak_cutoff_laplacian {L : ℂ} {F : Space} {h : energyDomain}
    (hw : ModularWeakSolution L F h) (g : PlanarChartTest) :
    Δ (g.localDistribution (embedding h)) =
      (2:ℂ) • (∑ i : Fin 2, ∂_{direction i}
        ((g.derivative (direction i)).localDistribution (embedding h))) -
      g.laplacianTest.localDistribution (embedding h) +
      L • (g.divHeight 2).localDistribution (embedding h) +
      (g.divHeight 2).localDistribution F := by
  ext ψ
  have he := modularWeak_planar_equation hw (g.mulSmooth ψ (ψ.smooth ⊤))
  rw [lifted_product_laplacian_integral, lifted_product_divHeight_integral,
    lifted_product_divHeight_integral] at he
  rw [TemperedDistribution.laplacian_apply_apply]
  simp only [Fin.sum_univ_two] at he ⊢
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul,
    TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  linear_combination he

/-- Localization of a smooth global representative by a compact chart test. -/
def PlanarChartTest.smoothLocalTest (g : PlanarChartTest) (G : UpperHalfPlane → ℂ)
    (hG : ChartSmooth G) : PlanarChartTest where
  field z := g.field z*G (ofComplex z)
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport g.field
    · have hy := g.support hz
      have hf := hG (ofComplex z)
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
  filter_upwards [hh, ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz hy
  apply hz
  simp [chartDensity, ne_of_gt hy]

/-- A forcing whose global lift has a smooth representative has every local Sobolev order. -/
theorem smooth_lift_local_sobolev {F : Space} {G : UpperHalfPlane → ℂ} (hG : ChartSmooth G)
    (hGF : G =ᵐ[(volume : Measure UpperHalfPlane)] globalLift F)
    (g : PlanarChartTest) (r : ℝ) : MemSobolev r 2 (g.localDistribution F) := by
  have hloc : g.localValue F =ᵐ[(volume : Measure ℂ)] (g.smoothLocalTest G hG).field := by
    have hp := global_ae_to_planar (P := fun z : ℂ =>
      globalLift F (ofComplex z) = G (ofComplex z)) (by
        filter_upwards [hGF] with z hz
        simpa only [ofComplex_apply] using hz.symm)
    have hh := (ae_restrict_iff' isOpen_upperHalfPlaneSet.measurableSet).mp hp
    filter_upwards [hh] with z hz
    by_cases hy : 0 < z.im
    · simp only [PlanarChartTest.localValue, PlanarChartTest.smoothLocalTest, hz hy]
    · have hg : g.field z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hy (g.support h))
      simp [PlanarChartTest.localValue, PlanarChartTest.smoothLocalTest, hg]
  have he : g.localDistribution F =
      ((g.smoothLocalTest G hG).compact.toSchwartzMap
        (g.smoothLocalTest G hG).smooth : 𝓢'(ℂ,ℂ)) := by
    ext ψ
    rw [g.localDistribution_apply]
    change _ = ∫ z : ℂ, ψ z • (g.smoothLocalTest G hG).field z
    apply integral_congr_ae
    filter_upwards [hloc] with z hz
    rw [hz]
    rfl
  rw [he]
  exact SchwartzMap.memSobolev _

private theorem local_sobolev_zero (g : PlanarChartTest) (u : Space) :
    MemSobolev 0 2 (g.localDistribution u) :=
  memSobolev_zero_iff.mpr ⟨g.localVector u, rfl⟩

private theorem sum_sobolev {r : ℝ} {f : Fin 2 → 𝓢'(ℂ,ℂ)}
    (hf : ∀ i, MemSobolev r 2 (f i)) : MemSobolev r 2 (∑ i, f i) := by
  simpa only [Fin.sum_univ_two] using (hf 0).add (hf 1)

private theorem modularWeak_sobolev_step {L : ℂ} {F : Space} {h : energyDomain}
    (hw : ModularWeakSolution L F h) (r : ℝ)
    (hsource : ∀ g : PlanarChartTest, MemSobolev (r-1) 2 (g.localDistribution F))
    (hh : ∀ g : PlanarChartTest, MemSobolev r 2 (g.localDistribution (embedding h)))
    (g : PlanarChartTest) :
    MemSobolev (r+1) 2 (g.localDistribution (embedding h)) := by
  have hscalar (a : PlanarChartTest) := (hh a).mono (show r-1 ≤ r by linarith)
  have hl : MemSobolev (r-1) 2 (Δ (g.localDistribution (embedding h))) := by
    rw [modularWeak_cutoff_laplacian hw]
    have hD := sum_sobolev (fun i =>
      (hh (g.derivative (direction i))).lineDerivOp (m := direction i))
    exact (((hD.smul (2:ℂ)).sub (hscalar g.laplacianTest)).add
      ((hscalar (g.divHeight 2)).smul L)).add (hsource (g.divHeight 2))
  have hout := planar_sobolev_gain_two (hscalar g) hl
  convert hout using 1
  ring

/-- With a smooth forcing lift, a weak solution has every local Sobolev order. -/
theorem modularWeak_local_all_orders {L : ℂ} {F : Space} {h : energyDomain}
    (hw : ModularWeakSolution L F h) {G : UpperHalfPlane → ℂ} (hG : ChartSmooth G)
    (hGF : G =ᵐ[(volume : Measure UpperHalfPlane)] globalLift F)
    (n : ℕ) (g : PlanarChartTest) :
    MemSobolev (n : ℝ) 2 (g.localDistribution (embedding h)) := by
  induction n generalizing g with
  | zero => simpa only [Nat.cast_zero] using local_sobolev_zero g (embedding h)
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one] using
      modularWeak_sobolev_step hw n (fun a => smooth_lift_local_sobolev hG hGF a _) ih g

private theorem exists_planarChartTest_ne_zero {z : ℂ} (hz : z ∈ {z : ℂ | 0 < z.im}) :
    ∃ g : PlanarChartTest, g.field z ≠ 0 := by
  obtain ⟨b, hb, hc, hd, _, he⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hcc : HasCompactSupport (Complex.ofRealCLM ∘ b) := hc.comp_left rfl
  have hdd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ b) := Complex.ofRealCLM.contDiff.comp hd
  have hss : tsupport (Complex.ofRealCLM ∘ b) ⊆ {z : ℂ | 0 < z.im} := by
    apply Subset.trans _ hb
    exact closure_mono (by intro x hx; simpa using hx)
  refine ⟨⟨Complex.ofRealCLM ∘ b, hdd, hcc, hss⟩, ?_⟩
  change (b z : ℂ) ≠ 0
  simp [he]

private theorem smooth_representative_of_localizations (u : Space)
    (hu : ∀ g : PlanarChartTest, ∃ r : ℂ → ℂ, ContDiff ℝ ∞ r ∧ r =ᵐ[volume] g.localValue u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
      f =ᵐ[volume.restrict {z : ℂ | 0 < z.im}] (fun z : ℂ => globalLift u (ofComplex z)) := by
  classical
  choose R hR hRa using hu
  have hcross (g h : PlanarChartTest) (z : ℂ) : g.field z * R h z = h.field z * R g z := by
    have hae : (fun w : ℂ => g.field w * R h w) =ᵐ[volume]
        (fun w : ℂ => h.field w * R g w) := by
      filter_upwards [hRa g, hRa h] with w hgw hhw
      rw [hgw, hhw]
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
  have hU (g : PlanarChartTest) : IsOpen (U g) :=
    isOpen_ne_fun g.smooth.continuous continuous_const
  have hcover : {z : ℂ | 0 < z.im} ⊆ ⋃ g : PlanarChartTest, U g := by
    intro z hz
    obtain ⟨g, hg⟩ := exists_planarChartTest_ne_zero hz
    exact mem_iUnion.mpr ⟨g, hg⟩
  have hpatch (g : PlanarChartTest) :
      f =ᵐ[volume.restrict (U g)] (fun z : ℂ => globalLift u (ofComplex z)) := by
    apply (ae_restrict_iff' (hU g).measurableSet).mpr
    filter_upwards [hRa g] with z hz hg
    rw [hquot z g hg, hz]
    simp only [PlanarChartTest.localValue]
    exact mul_div_cancel_left₀ _ hg
  obtain ⟨C, hC, hcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof {z : ℂ | 0 < z.im}).elim_countable_subcover
      U hU hcover
  have he : f =ᵐ[volume.restrict (⋃ g ∈ C, U g)] (fun z : ℂ => globalLift u (ofComplex z)) :=
    (ae_restrict_biUnion_iff U hC _).mpr (fun g _ => hpatch g)
  exact ⟨f, hs, ae_restrict_of_ae_restrict_of_subset hcov he⟩

/-- **Global regularity.** A modular weak solution whose forcing lift has a smooth
representative has a smooth representative on the whole upper half-plane. -/
theorem modularWeak_global_planar_smooth {L : ℂ} {F : Space} {h : energyDomain}
    (hw : ModularWeakSolution L F h) {G : UpperHalfPlane → ℂ} (hG : ChartSmooth G)
    (hGF : G =ᵐ[(volume : Measure UpperHalfPlane)] globalLift F) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
      f =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
        (fun z => globalLift (embedding h) (ofComplex z)) := by
  apply smooth_representative_of_localizations
  intro g
  obtain ⟨f, hf, he⟩ := planar_all_sobolev_smooth_representative
    (g.localVector (embedding h)) (fun n => modularWeak_local_all_orders hw hG hGF n g)
  exact ⟨f, hf, he.trans (g.localValue_memLp _).coeFn_toLp⟩

end
end RHTower.D4BMModularCore
