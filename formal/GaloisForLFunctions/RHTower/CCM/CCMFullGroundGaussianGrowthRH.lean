import GaloisForLFunctions.RHTower.CCM.CCMFullGroundZeroSideEigen
import GaloisForLFunctions.RHTower.XiRealRootedEigenGaussianGrowthRH

/-!
# Real-rooted ground states of Gaussian growth force RH

Let `u_j` be eigenvectors of the unconstrained restricted Weil forms at apertures `a_j → ∞` (for
example their ground states), with
real-rooted Fourier–Laplace transforms and nonzero mass `∫ f_j`, where `f_j` is the physical
function. Suppose that

* `∫ |f_j| ≤ M e^{a_j} |∫ f_j|`, and
* `|∫ conj(f_j(t)) e^{izt} dt| ≤ M e^{A (Re z)²} |∫ f_j|` on the strip `|Im z| < 1/2 + η`.

Then the Riemann hypothesis holds.

Compared with `riemannHypothesis_of_stripBoundedFullGrounds`, the normalized transforms may grow
like a fixed Gaussian along the strip. The mass ratio may grow exponentially in the aperture. The
first bound gives the Paley–Wiener growth `e^{(3/2 + η) a_j}` on the strip, and the receiver
`riemannHypothesis_of_realRootedEigen_gaussianGrowth` applies.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.CCMFullGroundEigen

open GaloisForLFunctions.HTGeometry
open RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

noncomputable section

/-- **Zero-side form of the eigen-equation.** If `Q_a(x, s) = μ ⟨x, s⟩` for every smooth
interior source `s`, then `∑_q F(γ_q) ŝ(-γ_q) = (μ/2π) ∫ F(σ) ŝ(-σ) dσ`, where
`F(z) = ∫ conj(x(t)) e^{izt} dt`. -/
theorem zeroSide_eigen_of_formEigen (a : SuzukiPositiveAperture) {x : CCMArchimedeanFormDomain a}
    {μ : ℝ}
    (heig : ∀ s : CCMComplexSmoothInteriorSource a, ccmRestrictedWeilForm a x s.toCCMFormVector =
      (μ : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * s t)
    (s : CCMComplexSmoothInteriorSource a) :
    ∑' q : XiZeroCopy, conjTransform (timeRep a x) (xiSpectralPoint q) *
        suzukiSmoothFourier s.toSuzukiSmoothCompactTest (-xiSpectralPoint q) =
      ((μ : ℂ) * (1 / (2 * Real.pi) : ℂ)) *
        ∫ σ : ℝ, conjTransform (timeRep a x) (σ : ℂ) *
          suzukiSmoothFourier s.toSuzukiSmoothCompactTest (-(σ : ℂ)) := by
  have hsupp := bound_support_of_supportedIn (supportedIn_timeRep a x)
  have h1 := tsum_mul_integral_eq_integral_zeroKernel s.toSuzukiSmoothCompactTest
    (integrable_timeRep a x) hsupp
  have h2 := integral_timeRep_formRepresenter_eq a x s
  have h3 := ccmRestrictedWeilForm_eq_integral_representer a x s
  have h6 := integral_conj_mul_eq_parseval a.2.le (integrable_timeRep a x)
    s.toSuzukiSmoothCompactTest
  have hs : ∀ t, s.toSuzukiSmoothCompactTest t = s t := fun t => rfl
  simp only [hs] at h6
  calc ∑' q : XiZeroCopy, conjTransform (timeRep a x) (xiSpectralPoint q) *
        suzukiSmoothFourier s.toSuzukiSmoothCompactTest (-xiSpectralPoint q)
      = ∑' q : XiZeroCopy, suzukiSmoothFourier s.toSuzukiSmoothCompactTest
          (-xiSpectralPoint q) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) *
            cexp (I * xiSpectralPoint q * (t : ℂ)) :=
        tsum_congr fun q => by rw [conjTransform, mul_comm]
    _ = ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) *
          zeroKernel s.toSuzukiSmoothCompactTest t := h1
    _ = ccmRestrictedWeilForm a x s.toCCMFormVector := by rw [h3, h2]
    _ = (μ : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * s t := heig s
    _ = _ := by rw [h6]; ring

/-- A full ground state satisfies the eigen-equation with the ground energy. -/
theorem formEigen_of_isFullGround (a : SuzukiPositiveAperture) {x : CCMArchimedeanFormDomain a}
    (hx : IsFullGround a x) (s : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a x s.toCCMFormVector =
      (ccmRestrictedWeilGroundEnergy a : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * s t := by
  have h4 := shiftedForm_eq_zero_of_isFullGround a hx s.toCCMFormVector
  rw [shiftedForm, sub_eq_zero, inner_aperture_eq_integral] at h4
  exact h4

/-- **Real-rooted eigenvectors of Gaussian growth force RH.** The vectors `u_j` satisfy the
eigen-equation `Q_{a_j}(u_j, s) = μ_j ⟨u_j, s⟩` against every smooth interior source. -/
theorem riemannHypothesis_of_gaussianGrowthEigenvectors {η A M : ℝ} (hη : 0 < η) (hA : 0 ≤ A)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (μ : ℕ → ℝ)
    (heig : ∀ j (s : CCMComplexSmoothInteriorSource (a j)),
      ccmRestrictedWeilForm (a j) (u j) s.toCCMFormVector =
        (μ j : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep (a j) (u j) t) * s t)
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hgauss : ∀ j (z : ℂ), |z.im| < 1 / 2 + η →
      ‖conjTransform (timeRep (a j) (u j)) z‖ ≤
        M * Real.exp (A * z.re ^ 2) * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) :
    RiemannHypothesis := by
  set f : ℕ → ℝ → ℂ := fun j => timeRep (a j) (u j) with hf
  set CT0 : ℕ → ℂ := fun j => conjTransform (f j) 0 with hCT0
  have hCT0eq : ∀ j, CT0 j = (starRingEnd ℂ) (∫ t : ℝ, f j t) := by
    intro j
    simp only [hCT0, conjTransform, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact integral_conj
  have hCT0ne : ∀ j, CT0 j ≠ 0 := by
    intro j
    rw [hCT0eq, map_ne_zero]
    exact hmass j
  have hnorm : ∀ j, ‖CT0 j‖ = ‖∫ t : ℝ, f j t‖ := fun j => by rw [hCT0eq, Complex.norm_conj]
  set G : ℕ → ℂ → ℂ := fun j z => conjTransform (f j) z / CT0 j with hG
  have hsupp : ∀ j, FourierZeroFlip.SupportedIn (a j).1 (f j) :=
    fun j => supportedIn_timeRep (a j) (u j)
  have hdivle : ∀ j (z : ℂ) (B : ℝ), ‖conjTransform (f j) z‖ ≤ B * ‖∫ t : ℝ, f j t‖ →
      ‖G j z‖ ≤ B := by
    intro j z B h
    have hpos : 0 < ‖CT0 j‖ := norm_pos_iff.mpr (hCT0ne j)
    rw [hG, norm_div, div_le_iff₀ hpos, hnorm]
    exact h
  refine RHTower.riemannHypothesis_of_realRootedEigen_gaussianGrowth (η := η) (A := A)
    (K := 3 / 2 + η) (M := M) hη hA (by linarith) ha (G := G)
    (κ := fun j => (μ j : ℂ) * (1 / (2 * Real.pi) : ℂ))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact ((differentiable_conjTransform (a j).2.le (integrable_timeRep (a j) (u j))
      (hsupp j)).div_const _).differentiableOn
  · intro j z hz
    exact hdivle j z _ (hgauss j z hz)
  · intro j z hz
    refine hdivle j z _ ?_
    set Y : ℝ := 1 / 2 + η with hY
    have hY0 : 0 ≤ Y := by rw [hY]; linarith
    have hsuppb := bound_support_of_supportedIn (hsupp j)
    have hfi := integrable_timeRep (a j) (u j)
    have hmom : ∀ t : ℝ, ‖f j t‖ * Real.exp (Y * |t|) ≤ ‖f j t‖ * Real.exp (Y * (a j).1) := by
      intro t
      by_cases hx : f j t = 0
      · rw [hx, norm_zero, zero_mul, zero_mul]
      · gcongr
        exact hsuppb t hx
    have hmomint : Integrable fun t : ℝ => ‖f j t‖ * Real.exp (Y * |t|) :=
      (hfi.norm.mul_const (Real.exp (Y * (a j).1))).mono'
        (hfi.norm.aestronglyMeasurable.mul
          (by fun_prop : Continuous fun t : ℝ => Real.exp (Y * |t|)).aestronglyMeasurable)
        (ae_of_all _ fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact hmom t)
    have hM : 0 ≤ M := by
      have h1 := le_trans (integral_nonneg fun t => norm_nonneg (f j t)) (hl1 j)
      have h2 : 0 < Real.exp (a j).1 * ‖∫ t : ℝ, f j t‖ :=
        mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (hmass j))
      rw [mul_assoc] at h1
      exact nonneg_of_mul_nonneg_left h1 h2
    calc ‖conjTransform (f j) z‖ ≤ ∫ t : ℝ, ‖f j t‖ * Real.exp (Y * |t|) :=
          norm_conjTransform_le hz.le hmomint
      _ ≤ ∫ t : ℝ, ‖f j t‖ * Real.exp (Y * (a j).1) :=
          integral_mono hmomint (hfi.norm.mul_const _) hmom
      _ = (∫ t : ℝ, ‖f j t‖) * Real.exp (Y * (a j).1) := integral_mul_const _ _
      _ ≤ (M * Real.exp (a j).1 * ‖∫ t : ℝ, f j t‖) * Real.exp (Y * (a j).1) := by
          gcongr
          exact hl1 j
      _ = M * Real.exp ((3 / 2 + η) * (a j).1) * ‖∫ t : ℝ, f j t‖ := by
          rw [show (3 / 2 + η) * (a j).1 = (a j).1 + Y * (a j).1 by rw [hY]; ring, Real.exp_add]
          ring
  · intro j z _ hz
    have hc : conjTransform (f j) z = 0 := by
      have := hz
      simp only [hG, div_eq_zero_iff] at this
      exact this.resolve_right (hCT0ne j)
    rw [conjTransform_eq_conj_unitaryLaplace, map_eq_zero] at hc
    have him := hreal j _ hc
    have : ((starRingEnd ℂ) z / (2 * Real.pi : ℂ)).im = -z.im / (2 * Real.pi) := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.div_ofReal_im, Complex.conj_im]
    rw [this] at him
    rcases div_eq_zero_iff.mp him with h | h
    · linarith
    · have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      linarith
  · intro j
    simp only [hG]
    exact div_self (hCT0ne j)
  · intro j R hR0 hRa w
    have hid := zeroSide_eigen_of_formEigen (a j) (heig j) (testSource (a j) w hRa)
    have hw : ∀ z, suzukiSmoothFourier (testSource (a j) w hRa).toSuzukiSmoothCompactTest z =
        suzukiSmoothFourier w z := fun z => rfl
    simp only [hw] at hid
    simp only [hG, div_mul_eq_mul_div]
    rw [tsum_div_const, integral_div, hid]
    ring

/-- **Real-rooted full ground states of Gaussian growth force RH.** -/
theorem riemannHypothesis_of_gaussianGrowthFullGrounds {η A M : ℝ} (hη : 0 < η) (hA : 0 ≤ A)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hgauss : ∀ j (z : ℂ), |z.im| < 1 / 2 + η →
      ‖conjTransform (timeRep (a j) (u j)) z‖ ≤
        M * Real.exp (A * z.re ^ 2) * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) :
    RiemannHypothesis :=
  riemannHypothesis_of_gaussianGrowthEigenvectors hη hA a ha u
    (fun j => ccmRestrictedWeilGroundEnergy (a j))
    (fun j => formEigen_of_isFullGround (a j) (hground j)) hreal hmass hl1 hgauss

end

end RHTower.CCMFullGroundEigen
