import GaloisForLFunctions.RHTower.RepPointPairRegularity
import GaloisForLFunctions.RHTower.HyperbolicRadialGreen
import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport
import GaloisForLFunctions.RHTower.DeckPointPairLaplacian

/-!
# Unfolding and the Laplacian for the twisted point-pair operators

For a continuous `ρ`-equivariant field `F`, the translates of the modular cell unfold the point-pair
operator to one integral over the upper half-plane, `L_φ F(z) = ∫_ℍ φ(u(z,w)) F(w) dμ(w)`
(`ppApply_eq_integral`; the fibres of `SL(2,ℤ) → PSL(2,ℤ)` have two elements).  Hence for a `C²`
profile `φ` the chart function of `L_φ F` is the radial kernel integral, `L_φ F` is `C²` and
`y²Δ(L_φ F) = L_{Dφ} F` with `Dφ(u) = u(u+1)φ''(u) + (2u+1)φ'(u)` (`hypLap_ppApply`).  Conversely
for a `C²` equivariant `V` the Green identity on `ℍ` gives `L_φ(y²ΔV) = L_{Dφ} V` (`ppApply_hypLap`),
and `y²Δ` preserves equivariance (`hypLap_equivariant`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped ContDiff MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry SelbergMaassTraceEnergy
open GaloisForLFunctions.RHTower.DeckPointPair (kerInt radialK radialLap hypLap chartLap
  dir_dir_congr continuous_radialLap radial_kernelC1 radial_kernelC1_deriv laplacian_kerInt_radial
  integral_radial_smul_chartLap continuous_chartLap dir_dir_comp_clm natCard_fiber_PSL2Z
  dist_le_of_pairU_le)

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

variable (ρ) in
/-- `ρ`-equivariance of a field: `F(Az) = ρ(A) F(z)`. -/
def IsEquivariant (F : ℍ → EuclideanSpace ℂ ι) : Prop := ∀ (A : SL(2, ℤ)) (z : ℍ), F (A • z) = ρ A (F z)

theorem kernelSupport_deck {φ : ℝ → ℝ} {R : ℝ} (hφR : KernelSupport φ R) :
    DeckPointPair.KernelSupport φ R := hφR

section Unfold

variable {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
include hφc hφR

/-- The unfolded integrand is integrable on `ℍ`: continuous, supported in a compact ball. -/
theorem integrable_pairKernel_smul {F : ℍ → EuclideanSpace ℂ ι} (hFc : Continuous F) (z : ℍ) :
    Integrable (fun w : ℍ => ((φ (pairU z w) : ℝ) : ℂ) • F w) := by
  have hcont : Continuous (fun w : ℍ => ((φ (pairU z w) : ℝ) : ℂ) • F w) :=
    (Complex.continuous_ofReal.comp (hφc.comp (continuous_pairU_right z))).smul hFc
  refine (integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall z (1 + 2 * R))
    ?_).1 (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
  intro w hw
  by_contra hwK
  apply hw
  have : R < pairU z w := by
    by_contra h
    push Not at h
    exact hwK (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le h))
  simp [hφR _ this]

/-- **Unfolding.** For a continuous `ρ`-equivariant `F`,
`L_φ F(z) = ∫_ℍ φ(u(z, w)) F(w) dμ(w)`. -/
theorem ppApply_eq_integral {F : ℍ → EuclideanSpace ℂ ι} (hFc : Continuous F)
    (hFe : IsEquivariant ρ F) (z : ℍ) :
    ppApply ρ φ F z = ∫ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) • F w := by
  rw [isFundamentalDomain_fd.integral_eq_tsum'' _ (integrable_pairKernel_smul hφc hφR hFc z)]
  have hterm : ∀ B : SL(2, ℤ), ppTerm ρ φ F z B =
      ∫ x in fd, ((φ (pairU z ((QuotientGroup.mk B : PSL2Z) • x)) : ℝ) : ℂ) •
        F ((QuotientGroup.mk B : PSL2Z) • x) := by
    intro B
    unfold ppTerm
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [PSL2Z_mk_smul]
    rw [hFe B x]
  have hsum : HasSum (fun B => ppTerm ρ φ F z B) (∑ B ∈ ppNearSet z R, ppTerm ρ φ F z B) :=
    hasSum_sum_of_ne_finset_zero fun B hB => ppTerm_eq_zero hφR F z (by simpa [ppNearSet] using hB)
  have hfib := hsum.tsum_fiberwise (QuotientGroup.mk : SL(2, ℤ) → PSL2Z)
  have hfibre : ∀ b : PSL2Z,
      ∑' B : ((QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}), ppTerm ρ φ F z B =
        (2 : ℂ) • ∫ x in fd, ((φ (pairU z (b • x)) : ℝ) : ℂ) • F (b • x) := by
    intro b
    have hc : ∀ B : ((QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}), ppTerm ρ φ F z B =
        ∫ x in fd, ((φ (pairU z (b • x)) : ℝ) : ℂ) • F (b • x) := fun B => by
      rw [hterm, show (QuotientGroup.mk (B : SL(2, ℤ)) : PSL2Z) = b from B.2]
    rw [tsum_congr hc, tsum_const, natCard_fiber_PSL2Z b, two_smul, two_smul]
  simp_rw [hfibre] at hfib
  have h1 := hfib.const_smul (1 / 2 : ℂ)
  simp only [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at h1
  unfold ppApply
  rw [hsum.tsum_eq, h1.tsum_eq]

end Unfold

section Laplace

variable {φ : ℝ → ℝ} {R : ℝ}

theorem ppApply_ofComplex_eq_kerInt (hφc : Continuous φ) (hφR : KernelSupport φ R)
    {F : ℍ → EuclideanSpace ℂ ι} (hFc : Continuous F) (hFe : IsEquivariant ρ F) {ζ : ℂ}
    (hζ : 0 < ζ.im) : ppApply ρ φ F (ofComplex ζ) = kerInt (radialK φ) F ζ := by
  rw [ppApply_eq_integral hφc hφR hFc hFe]
  unfold kerInt radialK
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [DeckPointPair.pairUc_ofComplex hζ, Complex.coe_smul]

/-- **`L_φ F` is `C²`** for a `C²` profile and a continuous equivariant `F`. -/
theorem contDiffOn_two_ppApply (hφ : ContDiff ℝ 2 φ) (hφR : KernelSupport φ R)
    {F : ℍ → EuclideanSpace ℂ ι} (hFc : Continuous F) (hFe : IsEquivariant ρ F) :
    ContDiffOn ℝ 2 (fun ζ => ppApply ρ φ F (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im} :=
  ((radial_kernelC1 hφ (kernelSupport_deck hφR)).contDiffOn_two_kerInt
    (radial_kernelC1_deriv hφ (kernelSupport_deck hφR)) hFc).congr
    fun _ hζ => ppApply_ofComplex_eq_kerInt hφ.continuous hφR hFc hFe hζ

theorem kernelSupport_radialLap (hφR : KernelSupport φ R) : KernelSupport (radialLap φ) R :=
  DeckPointPair.kernelSupport_radialLap (kernelSupport_deck hφR)

/-- **`y²Δ L_φ F = L_{Dφ} F`.** -/
theorem hypLap_ppApply (hφ : ContDiff ℝ 2 φ) (hφR : KernelSupport φ R)
    {F : ℍ → EuclideanSpace ℂ ι} (hFc : Continuous F) (hFe : IsEquivariant ρ F) (w : ℍ) :
    hypLap (ppApply ρ φ F) w = ppApply ρ (radialLap φ) F w := by
  have hw := w.im_pos
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have heq : (fun ζ => ppApply ρ φ F (ofComplex ζ)) =ᶠ[𝓝 (w : ℂ)] kerInt (radialK φ) F := by
    filter_upwards [hopen.mem_nhds (show 0 < (w : ℂ).im from hw)] with ζ hζ
    exact ppApply_ofComplex_eq_kerInt hφ.continuous hφR hFc hFe hζ
  unfold hypLap chartLap
  rw [dir_dir_congr heq, dir_dir_congr heq,
    laplacian_kerInt_radial hφ (kernelSupport_deck hφR) hFc (show 0 < (w : ℂ).im from hw),
    smul_smul, UpperHalfPlane.coe_im, mul_inv_cancel₀ (pow_ne_zero 2 hw.ne'), one_smul,
    ← ppApply_ofComplex_eq_kerInt (continuous_radialLap hφ) (kernelSupport_radialLap hφR) hFc hFe
      (show 0 < (w : ℂ).im from hw), ofComplex_apply]

end Laplace

/-- A real-linear functional of `y²ΔV` is minus the positive hyperbolic Laplacian of that functional
of `V`. -/
theorem clm_hypLap {V : ℍ → EuclideanSpace ℂ ι}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) (w : ℍ)
    (ℓ : EuclideanSpace ℂ ι →L[ℝ] ℂ) :
    ℓ (hypLap V w) = -positiveHyperbolicLaplacian (fun w => ℓ (V w)) w := by
  have h1 := dir_dir_comp_clm hV ℓ w.im_pos 1
  have hI := dir_dir_comp_clm hV ℓ w.im_pos Complex.I
  unfold hypLap chartLap positiveHyperbolicLaplacian
  rw [map_smul, map_add]
  change _ = -(-((w.im : ℂ) ^ 2) * (dir 1 (dir 1 (fun ζ => ℓ (V (ofComplex ζ)))) w +
    dir Complex.I (dir Complex.I (fun ζ => ℓ (V (ofComplex ζ)))) w))
  rw [h1, hI, Complex.real_smul]
  push_cast
  ring

/-- A coordinate of `y²ΔV` is minus the positive hyperbolic Laplacian of that coordinate. -/
theorem hypLap_apply {V : ℍ → EuclideanSpace ℂ ι}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) (w : ℍ) (q : ι) :
    hypLap V w q = -positiveHyperbolicLaplacian (fun w => V w q) w :=
  clm_hypLap hV w ((EuclideanSpace.proj q : EuclideanSpace ℂ ι →L[ℂ] ℂ).restrictScalars ℝ)

/-- **The Laplace–Beltrami operator preserves equivariance.** -/
theorem hypLap_equivariant {V : ℍ → EuclideanSpace ℂ ι}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im})
    (hVe : IsEquivariant ρ V) : IsEquivariant ρ (hypLap V) := by
  intro A z
  ext q
  let ℓ : EuclideanSpace ℂ ι →L[ℝ] ℂ :=
    ((EuclideanSpace.proj q : EuclideanSpace ℂ ι →L[ℂ] ℂ).comp
      (ρ A).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hℓ : ∀ v, ℓ v = (ρ A v) q := fun v => rfl
  rw [hypLap_apply hV, ← hℓ, clm_hypLap hV z ℓ]
  congr 1
  have hsmooth : IsRealSmoothUpperHalfPlane (fun w => V w q) :=
    ((EuclideanSpace.proj q : EuclideanSpace ℂ ι →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hV
  rw [← SelbergMaassCuspTransport.positive_laplacian_pullback A _ hsmooth z]
  congr 1
  funext w
  rw [hVe A w, hℓ]

/-- **Green identity**: `L_φ (y²ΔV) = L_{Dφ} V`. -/
theorem ppApply_hypLap {φ : ℝ → ℝ} {R : ℝ} (hφ : ContDiff ℝ 2 φ) (hR : 0 ≤ R)
    (hφR : KernelSupport φ R) {V : ℍ → EuclideanSpace ℂ ι}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im})
    (hVe : IsEquivariant ρ V) (z : ℍ) :
    ppApply ρ φ (hypLap V) z = ppApply ρ (radialLap φ) V z := by
  have hVc : Continuous V := by
    have h := hV.continuousOn.comp_continuous continuous_coe fun w => w.im_pos
    simpa [Function.comp_def, ofComplex_apply] using h
  have hLc : Continuous (hypLap V) :=
    (UpperHalfPlane.continuous_im.pow 2).smul (continuous_chartLap hV)
  rw [ppApply_eq_integral hφ.continuous hφR hLc (hypLap_equivariant hV hVe),
    ppApply_eq_integral (continuous_radialLap hφ) (kernelSupport_radialLap hφR) hVc hVe]
  simp_rw [Complex.coe_smul]
  exact integral_radial_smul_chartLap hφ hR (kernelSupport_deck hφR) hV z

end

end GaloisForLFunctions.RHTower.RepPointPair
