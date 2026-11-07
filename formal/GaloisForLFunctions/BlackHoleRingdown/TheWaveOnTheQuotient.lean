import GaloisForLFunctions.BlackHoleRingdown.TheScalarWaveOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinChannel
import GaloisForLFunctions.BlackHoleRingdown.TheCuspChannel

/-!
# The gravitational wave lives on the quotient

The perturbations of the metric are `SL₂(ℤ)`-covariant tensors, so they descend to the black hole with horizon `PSL₂(ℤ)\ℍ`.

The rotated gradient `V = (∂_y F, -∂_x F)` of an invariant function `F` is an invariant covector: a Möbius map `g` is conformal,
`dg = [[A, -B], [B, A]]` with `A + iB = g'`, so differentiating `F ∘ g = F` gives `V(z) = (dg)ᵀ V(g z)`. This applies to the image
field of a pulse and to the numerator at any `u`, which is invariant by the identity theorem from the line `Re u = 0`.

In the scalar sector `h_tt, h_tr, h_rr` are invariant functions and `h_xx = h_yy = a/y²` with `a` invariant, which is the invariant
form `a (dx² + dy²)/y²`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower (mem_window_self)
open _root_.RHTower.D4BMHorizon (Point)
open EisensteinSeries
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)

/-! ### The Möbius map -/

/-- The Möbius map in the chart. -/
def moebius (γ : SL(2, ℤ)) (ζ : ℂ) : ℂ :=
  ((γ 0 0 : ℤ) * ζ + (γ 0 1 : ℤ)) / ((γ 1 0 : ℤ) * ζ + (γ 1 1 : ℤ))

/-- Its derivative `(cζ + d)⁻²`. -/
def moebiusD (γ : SL(2, ℤ)) (ζ : ℂ) : ℂ := (((γ 1 0 : ℤ) * ζ + (γ 1 1 : ℤ))⁻¹) ^ 2

theorem denom_ne (γ : SL(2, ℤ)) {ζ : ℂ} (hζ : 0 < ζ.im) : ((γ 1 0 : ℤ) : ℂ) * ζ + (γ 1 1 : ℤ) ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  have hc' : γ 1 0 = 0 := by simpa [hζ.ne'] using him
  have hd' : γ 1 1 = 0 := by simpa [hc'] using hre
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  rw [hc', hd'] at hdet
  simp at hdet

theorem hasDerivAt_moebius (γ : SL(2, ℤ)) {ζ : ℂ} (hζ : 0 < ζ.im) :
    HasDerivAt (moebius γ) (moebiusD γ ζ) ζ := by
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    have h : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    exact_mod_cast h
  have hne := denom_ne γ hζ
  have hn : HasDerivAt (fun w : ℂ => ((γ 0 0 : ℤ) : ℂ) * w + (γ 0 1 : ℤ)) (γ 0 0 : ℂ) ζ := by
    simpa using ((hasDerivAt_id ζ).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)
  have hd : HasDerivAt (fun w : ℂ => ((γ 1 0 : ℤ) : ℂ) * w + (γ 1 1 : ℤ)) (γ 1 0 : ℂ) ζ := by
    simpa using ((hasDerivAt_id ζ).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  refine (hn.div hd hne).congr_deriv ?_
  rw [moebiusD]
  field_simp
  linear_combination hdet

theorem coe_smul_eq (γ : SL(2, ℤ)) (z : UpperHalfPlane) : ((γ • z : UpperHalfPlane) : ℂ) = moebius γ z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [moebius]

/-! ### Invariant functions -/

/-- **The rotated gradient of an invariant function is an invariant covector.** -/
theorem covariant_of_invariant {F : ℂ → ℂ} (γ : SL(2, ℤ)) (z : UpperHalfPlane)
    (hd : DifferentiableAt ℝ F (γ • z : UpperHalfPlane))
    (hinv : ∀ ζ : ℂ, 0 < ζ.im → F (moebius γ ζ) = F ζ) {Fx Fy Fx' Fy' : ℂ}
    (h1 : HasDerivAt (fun q : ℝ => F ⟨q, z.im⟩) Fx z.re)
    (h2 : HasDerivAt (fun q : ℝ => F ⟨z.re, q⟩) Fy z.im)
    (h3 : HasDerivAt (fun q : ℝ => F ⟨q, (γ • z : UpperHalfPlane).im⟩) Fx' (γ • z : UpperHalfPlane).re)
    (h4 : HasDerivAt (fun q : ℝ => F ⟨(γ • z : UpperHalfPlane).re, q⟩) Fy' (γ • z : UpperHalfPlane).im) :
    Fy = (moebiusD γ z).re * Fy' + (moebiusD γ z).im * (-Fx') ∧
      -Fx = -(moebiusD γ z).im * Fy' + (moebiusD γ z).re * (-Fx') := by
  set w := (γ • z : UpperHalfPlane) with hw
  have hzim : 0 < (z : ℂ).im := z.im_pos
  have hzeta : ((⟨z.re, z.im⟩ : ℂ)) = (z : ℂ) := Complex.eta _
  have hwc : ((⟨w.re, w.im⟩ : ℂ)) = (w : ℂ) := Complex.eta _
  have hL : HasFDerivAt F (fderiv ℝ F (w : ℂ)) (w : ℂ) := hd.hasFDerivAt
  set L := fderiv ℝ F (w : ℂ) with hLdef
  have hL1 : L 1 = Fx' := by
    have hc := (show HasFDerivAt F L ((⟨w.re, w.im⟩ : ℂ)) by rw [hwc]; exact hL).comp_hasDerivAt w.re
      (hasDerivAt_mk_re w.re w.im)
    exact hc.unique h3
  have hLI : L I = Fy' := by
    have hc := (show HasFDerivAt F L ((⟨w.re, w.im⟩ : ℂ)) by rw [hwc]; exact hL).comp_hasDerivAt w.im
      (hasDerivAt_mk_im w.re w.im)
    exact hc.unique h4
  have hg : HasFDerivAt (moebius γ) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (moebiusD γ z)).restrictScalars ℝ)
      (z : ℂ) := (hasDerivAt_moebius γ hzim).hasFDerivAt.restrictScalars ℝ
  have hcomp := (show HasFDerivAt F L (moebius γ (z : ℂ)) by rw [← coe_smul_eq]; exact hL).comp (z : ℂ) hg
  have hev : F ∘ moebius γ =ᶠ[𝓝 (z : ℂ)] F := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim] with ζ hζ
    exact hinv ζ hζ
  set G : ℂ →L[ℝ] ℂ := L.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (moebiusD γ z)).restrictScalars ℝ)
    with hG
  have hF : HasFDerivAt F G (z : ℂ) := hcomp.congr_of_eventuallyEq hev.symm
  have hFz : HasFDerivAt F G ((⟨z.re, z.im⟩ : ℂ)) := by
    rw [hzeta]
    exact hF
  have hx := (hFz.comp_hasDerivAt z.re (hasDerivAt_mk_re z.re z.im)).unique h1
  have hy := (hFz.comp_hasDerivAt z.im (hasDerivAt_mk_im z.re z.im)).unique h2
  set g' := moebiusD γ z with hg'
  have hsplit1 : L g' = (g'.re : ℝ) • Fx' + (g'.im : ℝ) • Fy' := by
    have : g' = (g'.re : ℝ) • (1 : ℂ) + (g'.im : ℝ) • I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, hL1, hLI]
  have hsplit2 : L (g' * I) = (-g'.im : ℝ) • Fx' + (g'.re : ℝ) • Fy' := by
    have : g' * I = (-g'.im : ℝ) • (1 : ℂ) + (g'.re : ℝ) • I := by
      apply Complex.ext <;> simp
    rw [this, map_add, map_smul, map_smul, hL1, hLI]
  have hX : Fx = L g' := by
    rw [← hx]
    change L ((1 : ℂ) • g') = _
    rw [one_smul]
  have hY : Fy = L (g' * I) := by
    rw [← hy]
    change L (I • g') = _
    rw [smul_eq_mul, mul_comm]
  rw [hX, hY, hsplit1, hsplit2]
  simp only [Complex.real_smul]
  push_cast
  constructor <;> ring

/-! ### The image field -/

/-- The image field as a function on the chart. -/
def imageChart (h : CompactPulse) (τ : ℝ) (ζ : ℂ) : ℂ := imageField h τ ζ.re ζ.im

theorem imageChart_moebius (h : CompactPulse) (τ : ℝ) (γ : SL(2, ℤ)) {ζ : ℂ} (hζ : 0 < ζ.im) :
    imageChart h τ (moebius γ ζ) = imageChart h τ ζ := by
  have hsm := imageField_smul h τ γ (⟨ζ, hζ⟩ : UpperHalfPlane)
  have hc : ((γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = moebius γ ζ := coe_smul_eq γ _
  have hre : (γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane).re = (moebius γ ζ).re := by
    rw [← hc]
    rfl
  have him : (γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane).im = (moebius γ ζ).im := by
    rw [← hc]
    rfl
  rw [hre, him] at hsm
  exact hsm

theorem differentiableAt_imageChart (h : CompactPulse) (τ : ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    DifferentiableAt ℝ (imageChart h τ) ζ := by
  obtain ⟨S, hS⟩ := exists_finset_box h τ ζ.re hζ
  have hev : imageChart h τ =ᶠ[𝓝 ζ] fun w => (1 / 2 : ℂ) * ∑ p ∈ S,
      pulseF h τ (rowHgt (rowC p) (rowD p) w.re w.im) := by
    have h1 : ∀ᶠ w : ℂ in 𝓝 ζ, |w.re - ζ.re| < 1 := by
      have := Complex.continuous_re.continuousAt.tendsto.eventually
        (Metric.ball_mem_nhds ζ.re one_pos)
      filter_upwards [this] with w hw
      simpa [Real.dist_eq] using hw
    have h2 : ∀ᶠ w : ℂ in 𝓝 ζ, w.im ∈ Ioo (ζ.im / 2) (2 * ζ.im) :=
      Complex.continuous_im.continuousAt.tendsto.eventually
        (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [h1, h2] with w a1 a2
    exact imageField_eq_sum hS (by simp) a1.le (Ioo_subset_Icc_self a2)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum fun p _ => ?_
  have hD := rowDen_pos p ζ.re hζ
  have hden : DifferentiableAt ℝ (fun w : ℂ => rowDen (rowC p) (rowD p) w.re w.im) ζ := by
    unfold rowDen
    have hre : DifferentiableAt ℝ (fun w : ℂ => w.re) ζ := Complex.reCLM.differentiableAt
    have him : DifferentiableAt ℝ (fun w : ℂ => w.im) ζ := Complex.imCLM.differentiableAt
    exact (((hre.const_mul _).add_const _).pow 2).add ((him.const_mul _).pow 2)
  have him' : DifferentiableAt ℝ (fun w : ℂ => w.im) ζ := Complex.imCLM.differentiableAt
  have hS' : DifferentiableAt ℝ (fun w : ℂ => rowHgt (rowC p) (rowD p) w.re w.im) ζ := by
    have h5 : DifferentiableAt ℝ (fun w : ℂ => w.im * (rowDen (rowC p) (rowD p) w.re w.im)⁻¹) ζ :=
      him'.mul (hden.inv hD.ne')
    simpa only [rowHgt, div_eq_mul_inv] using h5
  have hP : DifferentiableAt ℝ (pulseF h τ) (rowHgt (rowC p) (rowD p) ζ.re ζ.im) :=
    ((h.contDiff_pulseF τ).differentiable (by simp)) _
  exact hP.comp ζ hS'

/-- **The covector of the image field is `SL₂(ℤ)`-invariant.** -/
theorem imageCov_covariant (h : CompactPulse) (τ t r : ℝ) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    imageCov h 0 τ (chart4 t r z.re z.im) =
        (moebiusD γ z).re * imageCov h 0 τ (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) +
        (moebiusD γ z).im * imageCov h 1 τ (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) ∧
    imageCov h 1 τ (chart4 t r z.re z.im) =
        -(moebiusD γ z).im * imageCov h 0 τ (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) +
        (moebiusD γ z).re * imageCov h 1 τ (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) := by
  set w := (γ • z : UpperHalfPlane) with hw
  have hz : 0 < chart4 t r z.re z.im 3 := z.im_pos
  have hw0 : 0 < chart4 t r w.re w.im 3 := w.im_pos
  have h1 := imageCov_one h τ hz
  have h2 := imageCov_zero h τ hz
  have h3 := imageCov_one h τ hw0
  have h4 := imageCov_zero h τ hw0
  have key := covariant_of_invariant (F := imageChart h τ) γ z
    (differentiableAt_imageChart h τ w.im_pos) (fun ζ hζ => imageChart_moebius h τ γ hζ)
    (Fx := -imageCov h 1 τ (chart4 t r z.re z.im)) (Fy := imageCov h 0 τ (chart4 t r z.re z.im))
    (Fx' := -imageCov h 1 τ (chart4 t r w.re w.im)) (Fy' := imageCov h 0 τ (chart4 t r w.re w.im))
    h1 h2 h3 h4
  obtain ⟨a, b⟩ := key
  refine ⟨?_, ?_⟩
  · rw [a]
    ring
  · linear_combination b

/-- **The vector wave is a tensor on the quotient: temporal block.** -/
theorem imageT_covariant (h : CompactPulse) (t r : ℝ) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    imageT h.profile 0 (chart4 t r z.re z.im) =
        (moebiusD γ z).re * imageT h.profile 0 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) +
        (moebiusD γ z).im * imageT h.profile 1 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) ∧
    imageT h.profile 1 (chart4 t r z.re z.im) =
        -(moebiusD γ z).im * imageT h.profile 0 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) +
        (moebiusD γ z).re * imageT h.profile 1 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) := by
  set w := (γ • z : UpperHalfPlane) with hw
  have hz : 0 < chart4 t r z.re z.im 3 := z.im_pos
  have hw0 : 0 < chart4 t r w.re w.im 3 := w.im_pos
  have hτ : hyperTime (chart4 t r w.re w.im) = hyperTime (chart4 t r z.re z.im) := rfl
  have hF : rowF (chart4 t r w.re w.im) = rowF (chart4 t r z.re z.im) := rfl
  obtain ⟨a0, a1⟩ := imageCov_covariant h (hyperTime (chart4 t r z.re z.im)) t r γ z
  obtain ⟨b0, b1⟩ := imageCov_covariant h.D (hyperTime (chart4 t r z.re z.im)) t r γ z
  rw [imageT_profile h 0 hz, imageT_profile h 1 hz, imageT_profile h 0 hw0, imageT_profile h 1 hw0, hτ, hF,
    a0, a1, b0, b1]
  constructor <;> ring

/-- **The vector wave is a tensor on the quotient: radial block.** -/
theorem imageR_covariant (h : CompactPulse) (t r : ℝ) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    imageR h.profile 0 (chart4 t r z.re z.im) =
        (moebiusD γ z).re * imageR h.profile 0 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) +
        (moebiusD γ z).im * imageR h.profile 1 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) ∧
    imageR h.profile 1 (chart4 t r z.re z.im) =
        -(moebiusD γ z).im * imageR h.profile 0 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) +
        (moebiusD γ z).re * imageR h.profile 1 (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) := by
  set w := (γ • z : UpperHalfPlane) with hw
  have hz : 0 < chart4 t r z.re z.im 3 := z.im_pos
  have hw0 : 0 < chart4 t r w.re w.im 3 := w.im_pos
  have hτ : hyperTime (chart4 t r w.re w.im) = hyperTime (chart4 t r z.re z.im) := rfl
  have hF : rowF (chart4 t r w.re w.im) = rowF (chart4 t r z.re z.im) := rfl
  have hr : ((chart4 t r w.re w.im 1 : ℝ) : ℂ) = (chart4 t r z.re z.im 1 : ℝ) := rfl
  obtain ⟨a0, a1⟩ := imageCov_covariant h (hyperTime (chart4 t r z.re z.im)) t r γ z
  obtain ⟨b0, b1⟩ := imageCov_covariant h.D (hyperTime (chart4 t r z.re z.im)) t r γ z
  rw [imageR_profile h 0 hz, imageR_profile h 1 hz, imageR_profile h 0 hw0, imageR_profile h 1 hw0, hτ, hF, hr,
    a0, a1, b0, b1]
  constructor <;> ring

/-! ### The scalar wave -/

/-- The coefficients depend only on `r`. -/
def Coeff.RadialOnly (K : Coeff) : Prop :=
  ∀ t r x y x' y', K.A (chart4 t r x y) = K.A (chart4 t r x' y') ∧
    K.B (chart4 t r x y) = K.B (chart4 t r x' y') ∧ K.C (chart4 t r x y) = K.C (chart4 t r x' y')

theorem radialOnly_TT : coeffTT.RadialOnly := fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩
theorem radialOnly_TR : coeffTR.RadialOnly := fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩
theorem radialOnly_RR : coeffRR.RadialOnly := fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- **`h_tt, h_tr, h_rr` are invariant functions.** -/
theorem scalarEntry_smul {K : Coeff} (hK : K.RadialOnly) (h : CompactPulse) (t r : ℝ) (γ : SL(2, ℤ))
    (z : UpperHalfPlane) :
    scalarEntry K h (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) =
      scalarEntry K h (chart4 t r z.re z.im) := by
  obtain ⟨a, b, c⟩ := hK t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im z.re z.im
  have hP : entryPulse K h (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) =
      entryPulse K h (chart4 t r z.re z.im) := by
    simp only [entryPulse, Coeff.alpha, Coeff.beta, Coeff.gamma, a, b, c]
  rw [scalarEntry, hP]
  exact congrArg _ (imageField_smul _ _ γ z)

/-- The angular entry without the factor `y⁻²`. -/
def angularPulse (h : CompactPulse) (r : ℝ) : CompactPulse :=
  CompactPulse.pulseComb (-((r : ℂ) ^ 2) - (3 / 2 : ℂ) * (-(1 / 2)) + (9 / 4 : ℂ) * (-(1 / 2)))
    (-(1 / 2) - 3 * (-(1 / 2))) (-(1 / 2)) h

theorem scalarEntry_AA (h : CompactPulse) (t r x y : ℝ) :
    scalarEntry coeffAA h (chart4 t r x y) = ((y : ℂ) ^ 2)⁻¹ *
      (Complex.exp (-(3 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
        imageField (angularPulse h r) (t + radialPhase r) x y) := by
  rw [scalarEntry]
  change Complex.exp (-(3 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
    imageField (entryPulse coeffAA h (chart4 t r x y)) (t + radialPhase r) x y = _
  have hv : ∀ S : ℝ, (entryPulse coeffAA h (chart4 t r x y)) S =
      ((y : ℂ) ^ 2)⁻¹ * (angularPulse h r) S := fun S => by
    change coeffAA.alpha (chart4 t r x y) * h S + coeffAA.beta (chart4 t r x y) * h.D S +
      coeffAA.gamma (chart4 t r x y) * h.D.D S = ((y : ℂ) ^ 2)⁻¹ *
        ((-((r : ℂ) ^ 2) - (3 / 2 : ℂ) * (-(1 / 2)) + (9 / 4 : ℂ) * (-(1 / 2))) * h S +
          (-(1 / 2) - 3 * (-(1 / 2))) * h.D S + (-(1 / 2)) * h.D.D S)
    have hr1 : rC (chart4 t r x y) = (r : ℂ) := rfl
    have hy1 : yC (chart4 t r x y) = (y : ℂ) := rfl
    simp only [Coeff.alpha, Coeff.beta, Coeff.gamma, coeffAA, hr1, hy1]
    ring
  have hF : ∀ τ x' Y', imageField (entryPulse coeffAA h (chart4 t r x y)) τ x' Y' =
      ((y : ℂ) ^ 2)⁻¹ * imageField (angularPulse h r) τ x' Y' := fun τ x' Y' => by
    have hterm : ∀ p : gammaSet 1 1 0, imageTerm (entryPulse coeffAA h (chart4 t r x y)) (rowC p) (rowD p) τ x' Y' =
        ((y : ℂ) ^ 2)⁻¹ * imageTerm (angularPulse h r) (rowC p) (rowD p) τ x' Y' := fun p => by
      simp only [imageTerm, pulseF]
      rw [hv]
      ring
    simp only [imageField, hterm]
    rw [tsum_mul_left]
    ring
  rw [hF]
  ring

/-- **`h_xx = h_yy` is the invariant form `a (dx² + dy²)/y²`.** -/
theorem scalarEntry_AA_smul (h : CompactPulse) (t r : ℝ) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    (((γ • z : UpperHalfPlane).im : ℝ) : ℂ) ^ 2 *
        scalarEntry coeffAA h (chart4 t r (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im) =
      ((z.im : ℝ) : ℂ) ^ 2 * scalarEntry coeffAA h (chart4 t r z.re z.im) := by
  rw [scalarEntry_AA, scalarEntry_AA, imageField_smul]
  have h1 : (((γ • z : UpperHalfPlane).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (γ • z : UpperHalfPlane).im_pos.ne'
  have h2 : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  field_simp

/-! ### The modes of the zeros -/

theorem differentiableAt_numeratorChart (u : ℂ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    DifferentiableAt ℝ (fun w : ℂ => eisensteinNumerator u w.re w.im) ζ := by
  have h1 : DifferentiableAt ℝ (fun w : ℂ => (![w.re, w.im] : Point)) ζ := by
    rw [differentiableAt_pi]
    intro i
    fin_cases i
    · exact Complex.reCLM.differentiableAt
    · exact Complex.imCLM.differentiableAt
  have h2 : DifferentiableAt ℝ (numeratorField u) (![ζ.re, ζ.im] : Point) :=
    (contDiffAt_numeratorField u (z := ![ζ.re, ζ.im]) hζ (n := 1) (by simp)).differentiableAt (by norm_num)
  exact h2.comp ζ h1

/-- **The numerator is invariant.**  It is analytic in `u`, and invariant on the line `Re u = 0`. -/
theorem eisensteinNumerator_smul {u : ℂ} (hu : u.re < 1 / 2) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    eisensteinNumerator u (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im =
      eisensteinNumerator u z.re z.im := by
  have hopen : IsOpen {v : ℂ | v.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  have han : ∀ w : UpperHalfPlane, AnalyticOnNhd ℂ (fun v => eisensteinNumerator v w.re w.im) {v : ℂ | v.re < 1 / 2} :=
    fun w => DifferentiableOn.analyticOnNhd
      (fun v hv => (differentiableAt_eisensteinNumerator w.re w.im_pos hv).differentiableWithinAt) hopen
  have hconn : IsPreconnected {v : ℂ | v.re < 1 / 2} := (convex_halfSpace_re_lt (1 / 2)).isPreconnected
  have hI : Complex.I ∈ {v : ℂ | v.re < 1 / 2} := by
    simp only [mem_setOf_eq, Complex.I_re]
    norm_num
  have hline : ∀ ξ : ℝ, ξ ≠ 0 → eisensteinNumerator ((ξ : ℂ) * I) (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im =
      eisensteinNumerator ((ξ : ℂ) * I) z.re z.im := fun ξ hξ => by
    have h := normalizedEisenstein_smul hξ γ z
    rw [normalizedEisenstein_eq_numerator_div (xi_line_ne_zero ξ),
      normalizedEisenstein_eq_numerator_div (xi_line_ne_zero ξ)] at h
    exact (div_left_inj' (xi_line_ne_zero ξ)).mp h
  have hfreq : ∃ᶠ v in 𝓝[≠] Complex.I, eisensteinNumerator v (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im =
      eisensteinNumerator v z.re z.im := by
    have hseq : Tendsto (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) * I) atTop (𝓝[≠] Complex.I) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
          simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
        have h2 := ((Complex.continuous_ofReal.tendsto 1).comp h1).mul_const I
        simpa using h2
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h0
        have h1 : ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 1 :=
          mul_right_cancel₀ Complex.I_ne_zero (h0.trans (one_mul _).symm)
        have h2 : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h1
        have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine (hseq.frequently (Eventually.of_forall fun n => ?_).frequently)
    refine hline _ ?_
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact (han (γ • z)).eqOn_of_preconnected_of_frequently_eq (han z) hconn hI hfreq hu

/-- **The covector of a mode of a zero is invariant.** -/
theorem covNum_covariant (u : ℂ) (hu : u.re < 1 / 2) (γ : SL(2, ℤ)) (z : UpperHalfPlane) :
    covNum 0 u z.re z.im =
        (moebiusD γ z).re * covNum 0 u (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im +
        (moebiusD γ z).im * covNum 1 u (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im ∧
    covNum 1 u z.re z.im =
        -(moebiusD γ z).im * covNum 0 u (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im +
        (moebiusD γ z).re * covNum 1 u (γ • z : UpperHalfPlane).re (γ • z : UpperHalfPlane).im := by
  set w := (γ • z : UpperHalfPlane) with hw
  have hinv : ∀ ζ : ℂ, 0 < ζ.im → eisensteinNumerator u (moebius γ ζ).re (moebius γ ζ).im =
      eisensteinNumerator u ζ.re ζ.im := fun ζ hζ => by
    have hc : ((γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = moebius γ ζ := coe_smul_eq γ _
    have hre : (γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane).re = (moebius γ ζ).re := by
      rw [← hc]
      rfl
    have him : (γ • (⟨ζ, hζ⟩ : UpperHalfPlane) : UpperHalfPlane).im = (moebius γ ζ).im := by
      rw [← hc]
      rfl
    have := eisensteinNumerator_smul hu γ (⟨ζ, hζ⟩ : UpperHalfPlane)
    rw [hre, him] at this
    exact this
  have key := covariant_of_invariant (F := fun w : ℂ => eisensteinNumerator u w.re w.im) γ z
    (differentiableAt_numeratorChart u w.im_pos) hinv
    (Fx := numX u z.re z.im) (Fy := numY u z.re z.im) (Fx' := numX u w.re w.im) (Fy' := numY u w.re w.im)
    (hasDerivAt_num_x u z.re z.im_pos) (hasDerivAt_num_y u z.re z.im_pos)
    (hasDerivAt_num_x u w.re w.im_pos) (hasDerivAt_num_y u w.re w.im_pos)
  obtain ⟨a, b⟩ := key
  simp only [covNum, Fin.isValue, if_true, one_ne_zero, if_false]
  exact ⟨a, b⟩

/-! ### The time of the wave -/

/-- The time `t + γ(r)` of the metric is the hyperboloidal time of the scalar field. -/
theorem add_radialPhase_eq (t : ℝ) {r : ℝ} (hr : 1 < r) :
    t + radialPhase r = hyperboloidalTime t (tortoise r) := by
  have h1 : 0 < r - 1 := by linarith
  have h2 : 0 < r + 1 := by linarith
  have h0 : 0 < 2 * r := by linarith
  have hE := exp_two_mul_tortoise hr
  have hL : 2 * tortoise r = Real.log ((r - 1) / (r + 1)) := by
    rw [← hE, Real.log_exp]
  rw [Real.log_div h1.ne' h2.ne'] at hL
  have hh := hyperboloidalTime_tortoise t hr
  rw [hh, radialPhase, show r ^ 2 - 1 = (r - 1) * (r + 1) by ring,
    Real.log_mul h1.ne' h2.ne', Real.log_div h0.ne' h2.ne']
  linarith

end GaloisForLFunctions.BlackHoleRingdown

end
