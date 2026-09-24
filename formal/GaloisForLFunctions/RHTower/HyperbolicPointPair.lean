import GaloisForLFunctions.RHTower.HyperbolicRotationMean

/-!
# Selberg's point-pair principle

Every point of `ℍ` lies on a rotation orbit `k_θ·(iy)` (intermediate value theorem on
`Re(k_θ·w)`). Hence the rotation average `K̄F(w) = ∫₀^{2π} F(k_θ·w) dθ` is constant on orbits and
equals the axis average of `HyperbolicRotationMean`. For a rotation-invariant kernel `φ`, the
`GL(2,ℝ)`-invariance of the hyperbolic measure plus Fubini gives `2π ∫ φF = ∫ φ·K̄F`.
Combined with the mean-value theorem this proves `∫ φ G = (G(i)/E(i)) ∫ φ E` for any two
real-`C²` eigenfunctions with the same eigenvalue (`integral_kernel_eigen`). No growth or
decay condition on `G` beyond integrability of `φG` is used.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.HyperbolicPointPair
open HyperbolicRotationMean
noncomputable section

/-- The point `iy` of the upper half-plane. -/
def axisPoint {y : ℝ} (hy : 0 < y) : ℍ := ⟨Complex.I * y, by simpa using hy⟩

theorem rot_smul_axisPoint (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    ((rot θ • axisPoint hy : ℍ) : ℂ) = orbit θ y := by
  rw [coe_rot_smul, orbit, orbitNum, orbitDen]
  simp only [axisPoint, UpperHalfPlane.coe_mk]
  congr 1; ring

/-- Joint continuity of the rotation action along continuous parameters. -/
theorem continuous_rot_smul_of {X : Type*} [TopologicalSpace X] {a : X → ℝ} {b : X → ℍ}
    (ha : Continuous a) (hb : Continuous b) : Continuous fun x => rot (a x) • b x := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  have h : (fun x => ((rot (a x) • b x : ℍ) : ℂ)) = fun x =>
      ((b x : ℂ) * Real.cos (a x) + Real.sin (a x)) /
        (-(b x : ℂ) * Real.sin (a x) + Real.cos (a x)) := by
    funext x
    exact coe_rot_smul (a x) (b x)
  change Continuous (fun x => ((rot (a x) • b x : ℍ) : ℂ))
  rw [h]
  have hb' : Continuous fun x => (b x : ℂ) := UpperHalfPlane.continuous_coe.comp hb
  have hc : Continuous fun x => (Real.cos (a x) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp ha)
  have hs : Continuous fun x => (Real.sin (a x) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp ha)
  exact ((hb'.mul hc).add hs).div ((hb'.neg.mul hs).add hc)
    (fun x => rot_denom_ne_zero (a x) (b x))

/-- Continuity of a single rotation orbit. -/
theorem continuous_rot_orbit (w : ℍ) : Continuous fun θ : ℝ => rot θ • w :=
  continuous_rot_smul_of continuous_id continuous_const

theorem rot_neg_smul (θ : ℝ) (w : ℍ) : rot (-θ) • rot θ • w = w := by
  rw [← rot_add_smul, neg_add_cancel, rot_zero_smul]

/-- Every point lies on a rotation orbit through the imaginary axis. -/
theorem exists_rot_axis (w : ℍ) : ∃ θ : ℝ, ∃ y : ℝ, ∃ hy : 0 < y, w = rot θ • axisPoint hy := by
  let g : ℝ → ℝ := fun θ => ((rot θ • w : ℍ) : ℂ).re
  have h1 := continuous_rot_orbit w
  have hg : Continuous g := by
    show Continuous fun θ => ((rot θ • w : ℍ) : ℂ).re
    exact Complex.continuous_re.comp (UpperHalfPlane.continuous_coe.comp h1)
  have hg0 : g 0 = (w : ℂ).re := by simp [g, rot_zero_smul]
  have hgπ : g (Real.pi / 2) = -(w : ℂ).re / Complex.normSq (w : ℂ) := by
    simp only [g]
    rw [coe_rot_smul, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_zero, zero_add, mul_one, add_zero]
    rw [div_re]
    simp [Complex.normSq_neg]
  have hn : 0 < Complex.normSq (w : ℂ) := Complex.normSq_pos.mpr (UpperHalfPlane.ne_zero w)
  obtain ⟨θ0, -, hθ0⟩ : ∃ θ0 ∈ Icc 0 (Real.pi / 2), g θ0 = 0 := by
    rcases le_total 0 (w : ℂ).re with h | h
    · have hmem : (0 : ℝ) ∈ Icc (g (Real.pi / 2)) (g 0) := by
        rw [hg0, hgπ]
        exact ⟨div_nonpos_of_nonpos_of_nonneg (by linarith) hn.le, h⟩
      exact intermediate_value_Icc' (by positivity) hg.continuousOn hmem
    · have hmem : (0 : ℝ) ∈ Icc (g 0) (g (Real.pi / 2)) := by
        rw [hg0, hgπ]
        exact ⟨h, div_nonneg (by linarith) hn.le⟩
      exact intermediate_value_Icc (by positivity) hg.continuousOn hmem
  set u := rot θ0 • w
  have hre : (u : ℂ).re = 0 := hθ0
  have hu : (u : ℂ) = Complex.I * u.im := by
    apply Complex.ext
    · simpa using hre
    · simp
  refine ⟨-θ0, u.im, u.im_pos, ?_⟩
  have hax : axisPoint u.im_pos = u := by
    apply UpperHalfPlane.ext
    simp only [axisPoint, UpperHalfPlane.coe_mk]
    exact hu.symm
  rw [hax]
  exact (rot_neg_smul θ0 w).symm

/-- Unnormalized rotation average of a function on `ℍ` at a point. -/
def kAverage (F : ℍ → ℂ) (w : ℍ) : ℂ := ∫ θ in (0 : ℝ)..2 * Real.pi, F (rot θ • w)

theorem rot_periodic (θ : ℝ) (z : ℍ) : rot (θ + 2 * Real.pi) • z = rot θ • z := by
  apply UpperHalfPlane.ext
  rw [coe_rot_smul, coe_rot_smul, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The rotation average is constant along rotation orbits. -/
theorem kAverage_rot (F : ℍ → ℂ) (φ : ℝ) (w : ℍ) : kAverage F (rot φ • w) = kAverage F w := by
  unfold kAverage
  have hshift := intervalIntegral.integral_comp_add_right (fun θ => F (rot θ • w)) φ
    (a := 0) (b := 2 * Real.pi)
  simp only [rot_add_smul] at hshift
  have hper : Function.Periodic (fun θ => F (rot θ • w)) (2 * Real.pi) := fun θ => by
    simp only [rot_periodic]
  have h := hper.intervalIntegral_add_eq φ 0
  rw [zero_add] at h
  simp only [← mul_smul, ← rot_add]
  calc (∫ θ in (0 : ℝ)..2 * Real.pi, F (rot (θ + φ) • w))
      = ∫ θ in (0 + φ)..(2 * Real.pi + φ), F (rot θ • w) :=
        intervalIntegral.integral_comp_add_right (fun θ => F (rot θ • w)) φ
    _ = _ := by rw [zero_add, add_comm (2 * Real.pi) φ, h]

theorem kAverage_axis (F : ℍ → ℂ) {y : ℝ} (hy : 0 < y) :
    kAverage F (axisPoint hy) = rotAverage F y := by
  unfold kAverage rotAverage
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Function.comp_apply]
  congr 1
  apply UpperHalfPlane.ext
  rw [rot_smul_axisPoint, ofComplex_apply_of_im_pos (orbit_im_pos θ hy)]


/-- Rotation invariance of a kernel lets its pairing with `F` be computed from the rotation
average of `F`: `2π ∫ φ F = ∫ φ · K̄F`. -/
theorem two_pi_integral_eq_kAverage {φ F : ℍ → ℂ}
    (hφ : ∀ θ w, φ (rot θ • w) = φ w) (hφm : AEStronglyMeasurable φ volume)
    (hF : Continuous F) (hint : Integrable (fun w => φ w * F w)) :
    (2 * Real.pi : ℂ) * ∫ w, φ w * F w = ∫ w, φ w * kAverage F w := by
  set ν : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  set g : ℍ → ℂ := fun v => φ v * F v
  let f : ℍ × ℝ → ℂ := fun p => φ p.1 * F (rot p.2 • p.1)
  have hcont : Continuous fun p : ℍ × ℝ => F (rot p.2 • p.1) :=
    hF.comp (continuous_rot_smul_of continuous_snd continuous_fst)
  have hmeas : AEStronglyMeasurable f (volume.prod ν) :=
    (hφm.comp_fst).mul hcont.aestronglyMeasurable
  have hslice : ∀ θ, (fun w => f (w, θ)) = g ∘ fun x : ℍ => rot θ • x := by
    intro θ; funext w; simp only [f, g, Function.comp_apply, hφ]
  have hsliceI : ∀ θ, Integrable (g ∘ fun x : ℍ => rot θ • x) := fun θ =>
    (measurePreserving_smul (rot θ) volume).integrable_comp_of_integrable hint
  have hinvI : ∀ θ, (∫ w, (g ∘ fun x : ℍ => rot θ • x) w) = ∫ w, g w := fun θ =>
    integral_smul_eq_self (μ := (volume : Measure ℍ)) g
  have hnormI : ∀ θ, (∫ w, ‖(g ∘ fun x : ℍ => rot θ • x) w‖) = ∫ w, ‖g w‖ := fun θ =>
    integral_smul_eq_self (μ := (volume : Measure ℍ)) (fun v => ‖g v‖)
  have hint_prod : Integrable f (volume.prod ν) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall fun θ => ?_, ?_⟩
    · rw [hslice θ]; exact hsliceI θ
    · have hc : (fun θ => ∫ w, ‖f (w, θ)‖) = fun _ => ∫ w, ‖g w‖ := by
        funext θ
        rw [← hnormI θ]
        apply integral_congr_ae
        filter_upwards with w
        simp only [f, g, Function.comp_apply, hφ]
      rw [hc]
      haveI : IsFiniteMeasure ν :=
        ⟨by simpa [ν] using ENNReal.mul_lt_top ENNReal.ofNat_lt_top ENNReal.ofReal_lt_top⟩
      exact integrable_const _
  have hswap := integral_integral_swap (f := fun w θ => f (w, θ)) hint_prod
  have hleft : (∫ w, ∫ θ, f (w, θ) ∂ν) = ∫ w, φ w * kAverage F w := by
    apply integral_congr_ae
    filter_upwards with w
    simp only [f, kAverage, intervalIntegral.integral_of_le hpi]
    exact integral_const_mul (φ w) _
  have hright : (∫ θ, ∫ w, f (w, θ) ∂volume ∂ν) = (2 * Real.pi : ℂ) * ∫ w, g w := by
    have hc : (fun θ => ∫ w, f (w, θ)) = fun _ => ∫ w, g w := by
      funext θ; rw [hslice θ]; exact hinvI θ
    rw [hc, integral_const, Complex.real_smul]
    congr 1
    simp [ν, Real.volume_real_Ioc_of_le hpi]
  rw [← hleft, hswap, hright]

theorem continuous_of_smooth {G : ℍ → ℂ} (hG : IsRealSmoothUpperHalfPlane G) : Continuous G := by
  have h := hG.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  simpa [Function.comp_def, ofComplex_apply] using h

/-- Rotation averages of two eigenfunctions with the same eigenvalue are proportional at every
point of `ℍ`. -/
theorem kAverage_eq_smul {G E : ℍ → ℂ} {lam : ℂ}
    (hG : IsRealSmoothUpperHalfPlane G) (hGe : ∀ z, positiveHyperbolicLaplacian G z = lam * G z)
    (hE : IsRealSmoothUpperHalfPlane E) (hEe : ∀ z, positiveHyperbolicLaplacian E z = lam * E z)
    (hEI : E UpperHalfPlane.I ≠ 0) (w : ℍ) :
    kAverage G w = G UpperHalfPlane.I / E UpperHalfPlane.I * kAverage E w := by
  obtain ⟨θ, y, hy, rfl⟩ := exists_rot_axis w
  rw [kAverage_rot, kAverage_rot, kAverage_axis, kAverage_axis]
  exact rotAverage_eq_smul hG hGe hE hEe hEI hy

/-- **Selberg's point-pair principle at `i`.** For a rotation-invariant kernel `φ` and two
real-`C²` eigenfunctions `G, E` of the positive hyperbolic Laplacian with the same eigenvalue,
`∫ φ G = (G(i)/E(i)) ∫ φ E`. -/
theorem integral_kernel_eigen {φ G E : ℍ → ℂ} {lam : ℂ}
    (hφ : ∀ θ w, φ (rot θ • w) = φ w) (hφm : AEStronglyMeasurable φ volume)
    (hG : IsRealSmoothUpperHalfPlane G) (hGe : ∀ z, positiveHyperbolicLaplacian G z = lam * G z)
    (hE : IsRealSmoothUpperHalfPlane E) (hEe : ∀ z, positiveHyperbolicLaplacian E z = lam * E z)
    (hEI : E UpperHalfPlane.I ≠ 0)
    (hiG : Integrable (fun w => φ w * G w)) (hiE : Integrable (fun w => φ w * E w)) :
    (∫ w, φ w * G w) = G UpperHalfPlane.I / E UpperHalfPlane.I * ∫ w, φ w * E w := by
  have h1 := two_pi_integral_eq_kAverage hφ hφm (continuous_of_smooth hG) hiG
  have h2 := two_pi_integral_eq_kAverage hφ hφm (continuous_of_smooth hE) hiE
  have hk : (fun w => φ w * kAverage G w) =
      fun w => G UpperHalfPlane.I / E UpperHalfPlane.I * (φ w * kAverage E w) := by
    funext w
    rw [kAverage_eq_smul hG hGe hE hEe hEI w]
    ring
  rw [hk, integral_const_mul, ← h2] at h1
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  apply mul_left_cancel₀ hpi
  rw [h1]
  ring

end
end GaloisForLFunctions.RHTower.HyperbolicPointPair
