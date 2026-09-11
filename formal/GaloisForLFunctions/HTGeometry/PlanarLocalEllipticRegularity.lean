import GaloisForLFunctions.HTGeometry.PlanarSobolevLaplacianGain
import GaloisForLFunctions.HTGeometry.PlanarSobolevSmoothRepresentative
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Local elliptic regularity for planar scalar equations

Compactly supported test functions turn a classical C2 equation into a distributional
cutoff identity. The two-derivative Sobolev gain bootstraps all local orders, and continuity
identifies the smooth representative with the original solution pointwise.
-/

open MeasureTheory Set Filter Topology TemperedDistribution
open scoped ContDiff Distributions SchwartzMap LineDeriv Laplacian
namespace GaloisForLFunctions.HTGeometry.PlanarElliptic
noncomputable section
variable {Ω : TopologicalSpace.Opens ℂ}


def dir (v : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ f z v

def dtest (g : 𝓓(Ω,ℂ)) (v : ℂ) : 𝓓(Ω,ℂ) where
  toFun := dir v g
  contDiff' := (g.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  hasCompactSupport' := g.hasCompactSupport.fderiv_apply ℝ v
  tsupport_subset' := (tsupport_fderiv_apply_subset ℝ v).trans g.tsupport_subset

@[simp] theorem dtest_apply (g : 𝓓(Ω,ℂ)) (v z : ℂ) : dtest g v z = dir v g z := rfl

theorem localized_contDiff {n : ℕ∞ω} (g : 𝓓(Ω,ℂ)) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ n u Ω) (hn : n ≤ ∞) :
    ContDiff ℝ n (fun z => g z*u z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ tsupport g
  · exact (g.contDiff.of_le hn).contDiffAt.mul
      ((hu z (g.tsupport_subset hz)).contDiffAt (Ω.isOpen.mem_nhds (g.tsupport_subset hz)))
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    filter_upwards [he] with w hw
    simp [hw]

def mulTest (g : 𝓓(Ω,ℂ)) (a : ℂ → ℂ) (ha : ContDiffOn ℝ ∞ a Ω) : 𝓓(Ω,ℂ) where
  toFun z := g z*a z
  contDiff' := localized_contDiff g ha le_rfl
  hasCompactSupport' := g.hasCompactSupport.mul_right
  tsupport_subset' := tsupport_mul_subset_left.trans g.tsupport_subset

def lapTest (g : 𝓓(Ω,ℂ)) : 𝓓(Ω,ℂ) := dtest (dtest g 1) 1 + dtest (dtest g Complex.I) Complex.I

theorem localized_memLp (g : 𝓓(Ω,ℂ)) {u : ℂ → ℂ} (hu : ContinuousOn u Ω) :
    MemLp (fun z => g z*u z) 2 (volume : Measure ℂ) := by
  have hd := localized_contDiff g (contDiffOn_zero.mpr hu) (by simp)
  exact hd.continuous.memLp_of_hasCompactSupport g.hasCompactSupport.mul_right

def localVector (g : 𝓓(Ω,ℂ)) (u : ℂ → ℂ) (hu : ContinuousOn u Ω) : Lp ℂ 2 (volume : Measure ℂ) :=
  (localized_memLp g hu).toLp (fun z => g z*u z)

def localDistribution (g : 𝓓(Ω,ℂ)) (u : ℂ → ℂ) (hu : ContinuousOn u Ω) : 𝓢'(ℂ,ℂ) :=
  localVector g u hu

theorem localDistribution_apply (g : 𝓓(Ω,ℂ)) (u : ℂ → ℂ) (hu : ContinuousOn u Ω)
    (ψ : 𝓢(ℂ,ℂ)) : localDistribution g u hu ψ = ∫ z : ℂ, ψ z*(g z*u z) := by
  rw [localDistribution,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(localized_memLp g hu).coeFn_toLp] with z hz
  change localVector g u hu z = g z*u z at hz
  rw [hz]
  rfl

theorem dir_contDiffOn {u : ℂ → ℂ} {n m : ℕ∞ω} (hu : ContDiffOn ℝ n u Ω)
    (hm : m+1 ≤ n) (v : ℂ) : ContDiffOn ℝ m (dir v u) Ω :=
  (hu.fderiv_of_isOpen Ω.isOpen hm).clm_apply contDiffOn_const

theorem localized_integrable (g : 𝓓(Ω,ℂ)) {u : ℂ → ℂ} (hu : ContinuousOn u Ω) :
    Integrable (fun z => g z*u z) (volume : Measure ℂ) :=
  (localized_contDiff g (contDiffOn_zero.mpr hu) (by simp)).continuous.integrable_of_hasCompactSupport
    g.hasCompactSupport.mul_right

theorem integral_test_dir (g : 𝓓(Ω,ℂ)) {u : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω) (v : ℂ) :
    (∫ z : ℂ, g z*dir v u z) = -(∫ z : ℂ, dtest g v z*u z) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (localized_integrable (dtest g v) hu.continuousOn)
    (localized_integrable g (dir_contDiffOn hu (m := 0) (by norm_num) v).continuousOn)
    (localized_integrable g hu.continuousOn)
  · intro z _
    exact g.contDiff.differentiable (by simp) z
  · intro z hz
    exact ((hu z (g.tsupport_subset hz)).contDiffAt
      (Ω.isOpen.mem_nhds (g.tsupport_subset hz))).differentiableAt (by norm_num)

theorem integral_test_second (g : 𝓓(Ω,ℂ)) {u : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u Ω) (v : ℂ) :
    (∫ z : ℂ, g z*dir v (dir v u) z) = ∫ z : ℂ, dtest (dtest g v) v z*u z := by
  rw [integral_test_dir g (dir_contDiffOn hu (m := 1) (by norm_num) v) v,
    integral_test_dir (dtest g v) (hu.of_le (by norm_num)) v, neg_neg]

/-- The planar eigenfunction equation tested against every compact smooth function. -/
theorem weak_equation {u V : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u Ω)
    (hV : ContDiffOn ℝ ∞ V Ω)
    (heq : ∀ z ∈ Ω, dir 1 (dir 1 u) z + dir Complex.I (dir Complex.I u) z = V z*u z)
    (g : 𝓓(Ω,ℂ)) :
    (∫ z : ℂ, lapTest g z*u z) = ∫ z : ℂ, mulTest g V hV z*u z := by
  have hi (v : ℂ) := localized_integrable g
    (dir_contDiffOn (dir_contDiffOn hu (m := 1) (by norm_num) v)
      (m := 0) (by norm_num) v).continuousOn
  have hleft : (∫ z : ℂ, lapTest g z*u z) =
      (∫ z : ℂ, g z*(dir 1 (dir 1 u) z + dir Complex.I (dir Complex.I u) z)) := by
    simp only [lapTest, FunLike.coe_add, Pi.add_apply, add_mul, mul_add]
    rw [integral_add (localized_integrable _ hu.continuousOn) (localized_integrable _ hu.continuousOn),
      integral_add (hi 1) (hi Complex.I), integral_test_second g hu 1,
      integral_test_second g hu Complex.I]
  rw [hleft]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ Ω
  · change g z * _ = (g z*V z)*u z
    rw [heq z hz, mul_assoc]
  · have hg : g z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (g.tsupport_subset h))
    simp [mulTest,hg]

private theorem product_derivative (g : 𝓓(Ω,ℂ)) (ψ : 𝓢(ℂ,ℂ)) (v z : ℂ) :
    dtest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) v z =
      dtest g v z * ψ z + g z * (∂_{v} ψ) z := by
  change fderiv ℝ (fun w => g w*ψ w) z v = _
  rw [fderiv_fun_mul (g.contDiff.differentiable (by simp) z)
    ((ψ.smooth ⊤).differentiable (by simp) z)]
  simp only [add_apply,smul_apply,smul_eq_mul,SchwartzMap.lineDerivOp_apply_eq_fderiv,dtest_apply,dir]
  ring

private theorem product_second (g : 𝓓(Ω,ℂ)) (ψ : 𝓢(ℂ,ℂ)) (v z : ℂ) :
    dtest (dtest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) v) v z =
      dtest (dtest g v) v z*ψ z + 2*dtest g v z*(∂_{v} ψ) z +
        g z*(∂_{v} (∂_{v} ψ)) z := by
  have he : (dtest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) v : ℂ → ℂ) =
      fun w => dtest g v w*ψ w + g w*(∂_{v} ψ) w := funext (product_derivative g ψ v)
  change fderiv ℝ (dtest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) v) z v = _
  rw [he]
  have hg := g.contDiff.differentiable (by simp) z
  have hd := (dtest g v).contDiff.differentiable (by simp) z
  have hp := (ψ.smooth ⊤).differentiable (by simp) z
  have hpd := ((∂_{v} ψ).smooth ⊤).differentiable (by simp) z
  rw [fderiv_fun_add (hd.fun_mul hp) (hg.fun_mul hpd), fderiv_fun_mul hd hp,
    fderiv_fun_mul hg hpd]
  simp only [add_apply,smul_apply,smul_eq_mul,SchwartzMap.lineDerivOp_apply_eq_fderiv,dtest_apply,dir]
  ring

private theorem schwartz_laplacian (ψ : 𝓢(ℂ,ℂ)) (z : ℂ) :
    (Δ ψ) z = (∂_{(1:ℂ)} (∂_{(1:ℂ)} ψ)) z + (∂_{Complex.I} (∂_{Complex.I} ψ)) z := by
  rw [SchwartzMap.laplacian_eq_sum Complex.orthonormalBasisOneI]
  simp [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI]

private theorem product_laplacian (g : 𝓓(Ω,ℂ)) (ψ : 𝓢(ℂ,ℂ)) (z : ℂ) :
    lapTest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) z =
      ψ z*lapTest g z + 2*((∂_{(1:ℂ)} ψ) z*dtest g 1 z +
        (∂_{Complex.I} ψ) z*dtest g Complex.I z) + (Δ ψ) z*g z := by
  change dtest (dtest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) 1) 1 z +
    dtest (dtest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) Complex.I) Complex.I z = _
  rw [product_second,product_second,schwartz_laplacian]
  simp only [lapTest,FunLike.coe_add,Pi.add_apply]
  ring

private theorem pair_integrable (g : 𝓓(Ω,ℂ)) {u : ℂ → ℂ} (hu : ContinuousOn u Ω)
    (ψ : 𝓢(ℂ,ℂ)) : Integrable (fun z : ℂ => ψ z*(g z*u z)) :=
  (ψ.memLp 2).integrable_mul (localized_memLp g hu)

private theorem product_laplacian_integral (g : 𝓓(Ω,ℂ)) {u : ℂ → ℂ}
    (hu : ContinuousOn u Ω) (ψ : 𝓢(ℂ,ℂ)) :
    (∫ z : ℂ, lapTest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) z*u z) =
      localDistribution (lapTest g) u hu ψ +
      2*(localDistribution (dtest g 1) u hu (∂_{(1:ℂ)} ψ) +
        localDistribution (dtest g Complex.I) u hu (∂_{Complex.I} ψ)) +
      localDistribution g u hu (Δ ψ) := by
  simp only [localDistribution_apply]
  have h1 := pair_integrable (dtest g 1) hu (∂_{(1:ℂ)} ψ)
  have hI := pair_integrable (dtest g Complex.I) hu (∂_{Complex.I} ψ)
  have h0 := pair_integrable (lapTest g) hu ψ
  have h2 := pair_integrable g hu (Δ ψ)
  rw [← integral_add h1 hI,← integral_const_mul,← integral_add h0 ((h1.fun_add hI).const_mul 2),
    ← integral_add (h0.fun_add ((h1.fun_add hI).const_mul 2)) h2]
  apply integral_congr_ae
  filter_upwards with z
  rw [product_laplacian]
  ring

/-- The full cutoff commutator, derived from the original classical PDE. -/
theorem cutoff_laplacian {u V : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u Ω)
    (hV : ContDiffOn ℝ ∞ V Ω)
    (heq : ∀ z ∈ Ω, dir 1 (dir 1 u) z + dir Complex.I (dir Complex.I u) z = V z*u z)
    (g : 𝓓(Ω,ℂ)) :
    Δ (localDistribution g u hu.continuousOn) =
      (2:ℂ) • (∂_{(1:ℂ)} (localDistribution (dtest g 1) u hu.continuousOn) +
        ∂_{Complex.I} (localDistribution (dtest g Complex.I) u hu.continuousOn)) -
      localDistribution (lapTest g) u hu.continuousOn +
      localDistribution (mulTest g V hV) u hu.continuousOn := by
  ext ψ
  have he := weak_equation hu hV heq (mulTest g ψ (ψ.smooth ⊤).contDiffOn)
  rw [product_laplacian_integral _ hu.continuousOn] at he
  have hr : (∫ z : ℂ, mulTest (mulTest g ψ (ψ.smooth ⊤).contDiffOn) V hV z*u z) =
      localDistribution (mulTest g V hV) u hu.continuousOn ψ := by
    rw [localDistribution_apply]
    apply integral_congr_ae
    filter_upwards with z
    change ((g z*ψ z)*V z)*u z = ψ z*((g z*V z)*u z)
    ring
  rw [hr] at he
  rw [TemperedDistribution.laplacian_apply_apply]
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul,
    TemperedDistribution.lineDerivOp_apply_apply,map_neg]
  linear_combination he

/-- Every compact localization of a classical solution has all Sobolev orders. -/
theorem local_all_orders {u V : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u Ω)
    (hV : ContDiffOn ℝ ∞ V Ω)
    (heq : ∀ z ∈ Ω, dir 1 (dir 1 u) z + dir Complex.I (dir Complex.I u) z = V z*u z)
    (n : ℕ) (g : 𝓓(Ω,ℂ)) :
    MemSobolev (n:ℝ) 2 (localDistribution g u hu.continuousOn) := by
  induction n generalizing g with
  | zero =>
      rw [Nat.cast_zero,memSobolev_zero_iff]
      exact ⟨localVector g u hu.continuousOn,rfl⟩
  | succ n ih =>
      have hlow (a : 𝓓(Ω,ℂ)) := (ih a).mono (show (n:ℝ)-1 ≤ n by linarith)
      have hd : MemSobolev ((n:ℝ)-1) 2 (Δ (localDistribution g u hu.continuousOn)) := by
        rw [cutoff_laplacian hu hV heq]
        have hd1 := (ih (dtest g 1)).lineDerivOp (m := (1:ℂ))
        have hdI := (ih (dtest g Complex.I)).lineDerivOp (m := Complex.I)
        exact (((hd1.add hdI).smul (2:ℂ)).sub (hlow (lapTest g))).add
          (hlow (mulTest g V hV))
      have hout := planar_sobolev_gain_two (hlow g) hd
      convert hout using 1
      push_cast
      ring

/-- Smoothness of the original localized function, with pointwise identification. -/
theorem localized_smooth {u V : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u Ω)
    (hV : ContDiffOn ℝ ∞ V Ω)
    (heq : ∀ z ∈ Ω, dir 1 (dir 1 u) z + dir Complex.I (dir Complex.I u) z = V z*u z)
    (g : 𝓓(Ω,ℂ)) : ContDiff ℝ ∞ (fun z => g z*u z) := by
  obtain ⟨f,hf,he⟩ := planar_all_sobolev_smooth_representative
    (localVector g u hu.continuousOn) (fun n => local_all_orders hu hV heq n g)
  have hae : f =ᵐ[volume] (fun z => g z*u z) :=
    he.trans (localized_memLp g hu.continuousOn).coeFn_toLp
  have hc := (localized_contDiff g (contDiffOn_zero.mpr hu.continuousOn) (by simp)).continuous
  rwa [Measure.eq_of_ae_eq hae hf.continuous hc] at hf

private theorem exists_test_ne_zero {z : ℂ} (hz : z ∈ Ω) :
    ∃ g : 𝓓(Ω,ℂ), g z ≠ 0 := by
  obtain ⟨a,hsupp,hcompact,hsmooth,_,ha⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Ω.isOpen.mem_nhds hz)
  have hsupport : tsupport (fun w => (a w : ℂ)) ⊆ Ω := by
    apply Subset.trans (b := tsupport a) _ hsupp
    apply closure_mono
    intro w hw
    change (a w : ℂ) ≠ 0 at hw
    change a w ≠ 0
    exact fun h => hw (by rw [h]; rfl)
  let g : 𝓓(Ω,ℂ) :=
    { toFun := fun w => (a w : ℂ)
      contDiff' := Complex.ofRealCLM.contDiff.comp hsmooth
      hasCompactSupport' := hcompact.comp_left (g := Complex.ofReal) rfl
      tsupport_subset' := hsupport }
  refine ⟨g,?_⟩
  change (a z : ℂ) ≠ 0
  rw [ha]
  exact one_ne_zero

/-- A C2 planar solution of a scalar elliptic equation with smooth potential is smooth. -/
theorem smooth_of_equation {u V : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u Ω)
    (hV : ContDiffOn ℝ ∞ V Ω)
    (heq : ∀ z ∈ Ω, dir 1 (dir 1 u) z + dir Complex.I (dir Complex.I u) z = V z*u z) :
    ContDiffOn ℝ ∞ u Ω := by
  intro z hz
  obtain ⟨g,hg⟩ := exists_test_ne_zero hz
  have hquot := (localized_smooth hu hV heq g).contDiffAt.mul (g.contDiff.contDiffAt.fun_inv hg)
  apply (hquot.congr_of_eventuallyEq _).contDiffWithinAt
  filter_upwards [(isOpen_ne_fun g.continuous continuous_const).mem_nhds hg] with w hw
  change u w = (g w*u w)*(g w)⁻¹
  field_simp

end
end GaloisForLFunctions.HTGeometry.PlanarElliptic
