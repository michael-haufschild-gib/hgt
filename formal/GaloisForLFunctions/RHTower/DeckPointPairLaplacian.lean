import GaloisForLFunctions.RHTower.HyperbolicRadialGreen
import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport

/-!
# The Laplacian and the finite-deck point-pair operators

For a `C²` profile `φ` and a continuous deck-equivariant `F`, the chart function of `L_φ F` is the
radial kernel integral `ζ ↦ ∫ φ(U(ζ, w)) F(w) dμ(w)`; hence `L_φ F` is `C²` and
`y²Δ(L_φ F) = L_{Dφ} F` with `Dφ(u) = u(u+1)φ''(u) + (2u+1)φ'(u)`.  Conversely, for a `C²`
deck-equivariant `V` the Green identity on the upper half-plane gives `L_φ(y²ΔV) = L_{Dφ} V`.
The Laplace–Beltrami operator `y²Δ` commutes with integral Möbius transformations, so it preserves
deck equivariance.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
open scoped ContDiff MatrixGroups

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergMaassTraceEnergy

noncomputable section

variable {N : ℕ}

/-- The Laplace–Beltrami operator `y²(∂ₓ² + ∂ᵧ²)` in the chart. -/
def hypLap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : ℍ → E) (w : ℍ) : E :=
  (w.im ^ 2) • chartLap V w

/-- Second directional derivatives only depend on the germ. -/
theorem dir_dir_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℂ → E}
    {ζ : ℂ} (h : f =ᶠ[𝓝 ζ] g) (v : ℂ) : dir v (dir v f) ζ = dir v (dir v g) ζ := by
  have h1 : dir v f =ᶠ[𝓝 ζ] dir v g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with ζ' hζ'
    unfold dir
    rw [hζ']
  change fderiv ℝ (dir v f) ζ v = fderiv ℝ (dir v g) ζ v
  rw [h1.fderiv_eq]

theorem continuous_radialLap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (radialLap φ) := by
  unfold radialLap
  have h1 := (contDiff_one_deriv hφ).continuous
  have h2 := continuous_deriv_deriv hφ
  fun_prop

theorem kernelSupport_radialLap {φ : ℝ → ℝ} {R : ℝ} (hφR : KernelSupport φ R) :
    KernelSupport (radialLap φ) R := fun u hu => by
  simp [radialLap, deriv_eq_zero_of_kernelSupport hφR hu,
    deriv_eq_zero_of_kernelSupport (kernelSupport_deriv hφR) hu]

section Deck

variable {φ : ℝ → ℝ} {R : ℝ}

theorem ppApply_ofComplex_eq_kerInt (hφc : Continuous φ) (hφR : KernelSupport φ R)
    {F : ℍ → DeckSpace N} (hFc : Continuous F) (hFe : deckEquivariant N F) {ζ : ℂ}
    (hζ : 0 < ζ.im) : ppApply φ F (ofComplex ζ) = kerInt (radialK φ) F ζ := by
  rw [ppApply_eq_integral hφc hφR hFc hFe]
  unfold kerInt radialK
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [pairUc_ofComplex hζ, Complex.coe_smul]

/-- **`L_φ F` is `C²`** for a `C²` profile and a continuous equivariant `F`. -/
theorem contDiffOn_two_ppApply (hφ : ContDiff ℝ 2 φ) (hφR : KernelSupport φ R)
    {F : ℍ → DeckSpace N} (hFc : Continuous F) (hFe : deckEquivariant N F) :
    ContDiffOn ℝ 2 (fun ζ => ppApply φ F (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im} :=
  ((radial_kernelC1 hφ hφR).contDiffOn_two_kerInt (radial_kernelC1_deriv hφ hφR) hFc).congr
    fun _ hζ => ppApply_ofComplex_eq_kerInt hφ.continuous hφR hFc hFe hζ

/-- **`y²Δ L_φ F = L_{Dφ} F`.** -/
theorem hypLap_ppApply (hφ : ContDiff ℝ 2 φ) (hφR : KernelSupport φ R)
    {F : ℍ → DeckSpace N} (hFc : Continuous F) (hFe : deckEquivariant N F) (w : ℍ) :
    hypLap (ppApply φ F) w = ppApply (radialLap φ) F w := by
  have hw := w.im_pos
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have heq : (fun ζ => ppApply φ F (ofComplex ζ)) =ᶠ[𝓝 (w : ℂ)] kerInt (radialK φ) F := by
    filter_upwards [hopen.mem_nhds (show 0 < (w : ℂ).im from hw)] with ζ hζ
    exact ppApply_ofComplex_eq_kerInt hφ.continuous hφR hFc hFe hζ
  unfold hypLap chartLap
  rw [dir_dir_congr heq, dir_dir_congr heq,
    laplacian_kerInt_radial hφ hφR hFc (show 0 < (w : ℂ).im from hw), smul_smul,
    UpperHalfPlane.coe_im, mul_inv_cancel₀ (pow_ne_zero 2 hw.ne'), one_smul,
    ← ppApply_ofComplex_eq_kerInt (continuous_radialLap hφ) (kernelSupport_radialLap hφR) hFc hFe
      (show 0 < (w : ℂ).im from hw), ofComplex_apply]

end Deck

/-- A coordinate of `y²ΔV` is minus the positive hyperbolic Laplacian of that coordinate. -/
theorem hypLap_apply {V : ℍ → DeckSpace N}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) (w : ℍ) (q : Deck N) :
    hypLap V w q = -positiveHyperbolicLaplacian (fun w => V w q) w := by
  let g : DeckSpace N →L[ℝ] ℂ := (EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).restrictScalars ℝ
  have h1 := dir_dir_comp_clm hV g w.im_pos 1
  have hI := dir_dir_comp_clm hV g w.im_pos Complex.I
  unfold hypLap chartLap positiveHyperbolicLaplacian
  change ((w.im ^ 2 : ℝ) • (dir 1 (dir 1 (fun ζ => V (ofComplex ζ))) w +
      dir Complex.I (dir Complex.I (fun ζ => V (ofComplex ζ))) w)) q = _
  rw [PiLp.smul_apply, PiLp.add_apply]
  change _ = -(-((w.im : ℂ) ^ 2) * (dir 1 (dir 1 (fun ζ => g (V (ofComplex ζ)))) w +
    dir Complex.I (dir Complex.I (fun ζ => g (V (ofComplex ζ)))) w))
  rw [h1, hI]
  change (w.im ^ 2 : ℝ) • ((dir 1 (dir 1 (fun ζ => V (ofComplex ζ))) w) q +
    (dir Complex.I (dir Complex.I (fun ζ => V (ofComplex ζ))) w) q) = _
  rw [Complex.real_smul]
  push_cast
  rw [neg_mul, neg_neg, mul_add, mul_add]
  rfl

/-- **The Laplace–Beltrami operator preserves deck equivariance.** -/
theorem hypLap_equivariant {V : ℍ → DeckSpace N}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im})
    (hVe : deckEquivariant N V) : deckEquivariant N (hypLap V) := by
  intro A z
  ext q
  rw [finiteRegularUnitary_apply, hypLap_apply hV, hypLap_apply hV]
  congr 1
  have hsmooth : IsRealSmoothUpperHalfPlane (fun w => V w q) :=
    ((EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn hV
  rw [← SelbergMaassCuspTransport.positive_laplacian_pullback A _ hsmooth z]
  congr 1
  funext w
  rw [hVe A w, finiteRegularUnitary_apply]

/-- **Green identity for the deck operator**: `L_φ (y²ΔV) = L_{Dφ} V`. -/
theorem ppApply_hypLap {φ : ℝ → ℝ} {R : ℝ} (hφ : ContDiff ℝ 2 φ) (hR : 0 ≤ R)
    (hφR : KernelSupport φ R) {V : ℍ → DeckSpace N}
    (hV : ContDiffOn ℝ 2 (fun ζ => V (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im})
    (hVe : deckEquivariant N V) (z : ℍ) :
    ppApply φ (hypLap V) z = ppApply (radialLap φ) V z := by
  have hVc : Continuous V := by
    have h := hV.continuousOn.comp_continuous continuous_coe fun w => w.im_pos
    simpa [Function.comp_def, ofComplex_apply] using h
  have hLc : Continuous (hypLap V) :=
    (UpperHalfPlane.continuous_im.pow 2).smul (continuous_chartLap hV)
  rw [ppApply_eq_integral hφ.continuous hφR hLc (hypLap_equivariant hV hVe),
    ppApply_eq_integral (continuous_radialLap hφ) (kernelSupport_radialLap hφR) hVc hVe]
  simp_rw [Complex.coe_smul]
  exact integral_radial_smul_chartLap hφ hR hφR hV z

end

end GaloisForLFunctions.RHTower.DeckPointPair
