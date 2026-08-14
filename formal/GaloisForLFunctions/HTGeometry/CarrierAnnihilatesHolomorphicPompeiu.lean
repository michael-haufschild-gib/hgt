import GaloisForLFunctions.HTGeometry.ContinuousMapCauchyTransform
import GaloisForLFunctions.HTGeometry.CompactSmoothCutoff
import GaloisForLFunctions.HTGeometry.DbarSolve

/-!
# A vanishing Cauchy transform annihilates every holomorphic function near the carrier

Cut a function holomorphic on an open set off by a smooth function equal to `1` near a compact
subset.  The cut-off function is globally `C¹` with compact support and its `∂̄` is supported away
from the compact set, so Cauchy–Pompeiu writes the original function on the compact set as a
superposition of Cauchy kernels with poles off it.  A functional whose Cauchy transform vanishes off
the compact set therefore kills the whole superposition.

Unlike the rectangle-contour form, this needs no rectangle inside the domain of holomorphy: the
carrier may be any plane compact and the domain any open set containing it.

* `GaloisForLFunctions.HTGeometry.apply_eq_zero_of_cauchyTransform_eq_zero_of_isOpen`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

variable {K : Set ℂ} [CompactSpace K]

/-- **A functional whose Cauchy transform vanishes off a plane compact annihilates the restriction
of every function holomorphic on an open set containing it.** -/
theorem apply_eq_zero_of_cauchyTransform_eq_zero_of_isOpen
    (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G U)
    (L : C(K, ℂ) →L[ℂ] ℂ)
    (hzero : ∀ v, v ∉ K → functionalCauchyTransform L v = 0)
    (gK : C(K, ℂ)) (hgK : ∀ z : K, gK z = G (z : ℂ)) :
    L gK = 0 := by
  classical
  obtain ⟨chi, W, hWopen, hKW, hchiC, hchics, hchiU, hchi1⟩ := exists_smooth_cutoff hK hU hKU
  set V : Set ℂ := W ∩ U with hV
  have hVopen : IsOpen V := hWopen.inter hU
  have hKV : K ⊆ V := fun z hz => ⟨hKW hz, hKU hz⟩
  set g : ℂ → ℂ := fun w => (chi w : ℂ) * U.indicator G w with hg
  -- smoothness of the cut-off function
  have hGsmooth : ∀ w ∈ U, ContDiffAt ℝ 1 G w := by
    intro w hw
    exact ((hG.analyticOnNhd hU w hw).contDiffAt).restrict_scalars ℝ
  have hgU : ∀ w ∈ U, g =ᶠ[nhds w] fun u => (chi u : ℂ) * G u := by
    intro w hw
    filter_upwards [hU.mem_nhds hw] with u hu
    simp only [hg, Set.indicator_of_mem hu]
  have hgzero : ∀ w ∉ tsupport chi, g =ᶠ[nhds w] fun _ => (0 : ℂ) := by
    intro w hw
    filter_upwards [(isClosed_tsupport chi).isOpen_compl.mem_nhds hw] with u hu
    have : chi u = 0 := by
      by_contra hcon
      exact hu (subset_tsupport chi hcon)
    simp only [hg, this]
    simp
  have hgC : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ U
    · refine ContDiffAt.congr_of_eventuallyEq ?_ (hgU w hw)
      have hchi1' : ContDiff ℝ 1 chi := hchiC.of_le (by exact_mod_cast le_top)
      exact (Complex.ofRealCLM.contDiff.comp hchi1').contDiffAt.mul (hGsmooth w hw)
    · have hwts : w ∉ tsupport chi := fun hc => hw (hchiU hc)
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const (hgzero w hwts)
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro hchics fun w hw => ?_
    have : chi w = 0 := by
      by_contra hcon
      exact hw (subset_tsupport chi hcon)
    simp only [hg, this]
    simp
  -- on a neighbourhood of the carrier the cut-off function is the original one
  have hgV : ∀ w ∈ V, g =ᶠ[nhds w] G := by
    intro w hw
    filter_upwards [hVopen.mem_nhds hw] with u hu
    simp only [hg, Set.indicator_of_mem hu.2, hchi1 u hu.1]
    simp
  have hdzV : ∀ w ∈ V, dzbar g w = 0 := by
    intro w hw
    have hfd : fderiv ℝ g w = fderiv ℝ G w := (hgV w hw).fderiv_eq
    have hGd : DifferentiableAt ℂ G w := (hG.analyticOnNhd hU w hw.2).differentiableAt
    rw [dzbar, hfd]
    exact (dzbar_eq_zero_of_differentiableAt hGd).1
  have hdzcont : Continuous (dzbar g) := by
    have : dzbar g = fun w => wirtingerAntiholL (fderiv ℝ g w) := by
      funext w
      rw [dzbar, wirtingerAntiholL_apply]
    rw [this]
    exact wirtingerAntiholL.continuous.comp (hgC.continuous_fderiv (by norm_num))
  -- the Cauchy family of the source
  set Phi : ℂ → C(K, ℂ) := fun u => dzbar g u • resolventInv K u with hPhi
  have hPhiV : ∀ u ∈ V, Phi u = 0 := by
    intro u hu
    simp only [hPhi, hdzV u hu, zero_smul]
  have hPhicont : Continuous Phi := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u ∈ K
    · have hev : Phi =ᶠ[nhds u] fun _ => (0 : C(K, ℂ)) := by
        filter_upwards [hVopen.mem_nhds (hKV hu)] with w hw using hPhiV w hw
      exact ContinuousAt.congr continuousAt_const hev.symm
    · have hcont : ContinuousAt (fun u : ℂ => resolventInv K u) u :=
        (differentiableAt_resolventInv hu).continuousAt
      exact (hdzcont.continuousAt).smul hcont
  have hPhics : HasCompactSupport Phi := by
    refine HasCompactSupport.intro (hgcs) fun u hu => ?_
    have hzero' : dzbar g u = 0 := by
      have hev : g =ᶠ[nhds u] fun _ => (0 : ℂ) := by
        filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hu] with w hw
        by_contra hcon
        exact hw (subset_tsupport g hcon)
      have hfd : fderiv ℝ g u = fderiv ℝ (fun _ : ℂ => (0 : ℂ)) u := hev.fderiv_eq
      rw [dzbar, hfd]
      simp [wirtingerAntihol]
    simp only [hPhi, hzero', zero_smul]
  have hPhiint : Integrable Phi volume := hPhicont.integrable_of_hasCompactSupport hPhics
  -- the integral of the Cauchy family reproduces the function on the carrier
  have hkernel : ∀ (u : ℂ) (z : K), (Phi u) z = dzbar g u * (u - (z : ℂ))⁻¹ := by
    intro u z
    by_cases hu : u ∈ K
    · simp only [hPhi, hdzV u (hKV hu), zero_smul, ContinuousMap.zero_apply, zero_mul]
    · simp only [hPhi, ContinuousMap.smul_apply, smul_eq_mul, resolventInv_eq hu,
        kernelFun_apply]
  have heval : ∀ z : K, (∫ u : ℂ, Phi u) z = -((Real.pi : ℂ) * G (z : ℂ)) := by
    intro z
    have hcomm := (ContinuousMap.evalCLM ℂ z).integral_comp_comm hPhiint
    have hpt : (∫ u : ℂ, (ContinuousMap.evalCLM ℂ z) (Phi u))
        = ∫ u : ℂ, dzbar g u * (u - (z : ℂ))⁻¹ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      exact hkernel u z
    have hsub : (∫ u : ℂ, dzbar g u / ((z : ℂ) - u)) = (Real.pi : ℝ) • g (z : ℂ) := by
      have hshift := integral_sub_left_eq_self
        (fun u : ℂ => dzbar g u / ((z : ℂ) - u)) volume ((z : ℂ))
      rw [← hshift]
      have hcongr : ∀ w : ℂ, dzbar g ((z : ℂ) - w) / ((z : ℂ) - ((z : ℂ) - w))
          = dzbar g ((z : ℂ) - w) / w := by
        intro w
        congr 1
        ring
      simp only [hcongr]
      exact integral_dzbar_kernel hgC hgcs (z : ℂ)
    have hneg : ∀ u : ℂ, dzbar g u * (u - (z : ℂ))⁻¹ = -(dzbar g u / ((z : ℂ) - u)) := by
      intro u
      have h1 : (u - (z : ℂ))⁻¹ = -(((z : ℂ) - u)⁻¹) := by
        rw [neg_inv, neg_sub]
      rw [h1, mul_neg, div_eq_mul_inv]
    have hgz : g (z : ℂ) = G (z : ℂ) := (hgV (z : ℂ) (hKV z.2)).self_of_nhds
    calc (∫ u : ℂ, Phi u) z
        = (ContinuousMap.evalCLM ℂ z) (∫ u : ℂ, Phi u) := rfl
      _ = ∫ u : ℂ, (ContinuousMap.evalCLM ℂ z) (Phi u) := hcomm.symm
      _ = ∫ u : ℂ, dzbar g u * (u - (z : ℂ))⁻¹ := hpt
      _ = ∫ u : ℂ, -(dzbar g u / ((z : ℂ) - u)) := by simp only [hneg]
      _ = -∫ u : ℂ, dzbar g u / ((z : ℂ) - u) := integral_neg _
      _ = -((Real.pi : ℝ) • g (z : ℂ)) := by rw [hsub]
      _ = -((Real.pi : ℂ) * G (z : ℂ)) := by rw [hgz, Complex.real_smul]
  have hintEq : (∫ u : ℂ, Phi u) = (-(Real.pi : ℂ)) • gK := by
    ext z
    rw [heval z, ContinuousMap.smul_apply, smul_eq_mul, hgK z]
    ring
  -- the functional kills the integral term by term
  have hLzero : L (∫ u : ℂ, Phi u) = 0 := by
    rw [← L.integral_comp_comm hPhiint]
    have hterm : ∀ u : ℂ, L (Phi u) = 0 := by
      intro u
      by_cases hu : u ∈ K
      · simp only [hPhi, hdzV u (hKV hu), zero_smul, map_zero]
      · simp only [hPhi, map_smul, smul_eq_mul, ← cauchyTransform_eq_apply_resolventInv,
          hzero u hu, mul_zero]
    simp only [hterm, integral_zero]
  rw [hintEq, map_smul, smul_eq_mul] at hLzero
  have hpi : (-(Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  exact (mul_eq_zero.mp hLzero).resolve_left hpi

end GaloisForLFunctions.HTGeometry
