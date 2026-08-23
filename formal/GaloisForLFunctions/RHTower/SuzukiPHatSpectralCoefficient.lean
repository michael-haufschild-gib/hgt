import GaloisForLFunctions.RHTower.SuzukiPHatModelSpace
import GaloisForLFunctions.RHTower.SuzukiWeilDifferentialPairing
import GaloisForLFunctions.RHTower.SuzukiWeilTestSpace

noncomputable section

/-!
# The transform's coefficients are the spectral values

One integration by parts identifies the ray coefficient of `𝒫̂_{Dψ}` at a spectral point with the
Fourier value of `ψ` there: the derivative moves off the test function and onto the exponential
slope, producing the factor `iw` that cancels the `w` in the denominator, and on the real axis the
remaining integral is the conjugate of `ψ̂(γ)`.

This is the arithmetic half of the source's equation (3.8); what remains for `K_0 = K(Θ)` is the
Hilbert-space bookkeeping that turns it into the coefficient of `F_γ`.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

theorem deriv_conj_suzukiTest (ψ : SuzukiTest) (t : ℝ) :
    deriv (fun s : ℝ => (starRingEnd ℂ) ((ψ : ℝ → ℂ) s)) t
      = (starRingEnd ℂ) (deriv (ψ : ℝ → ℂ) t) := by
  have hψ : HasDerivAt (ψ : ℝ → ℂ) (deriv (ψ : ℝ → ℂ) t) t :=
    ((ψ.smooth.differentiable (by simp)).differentiableAt).hasDerivAt
  exact (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hψ).deriv

theorem suzukiTest_supp {a : ℝ} {ψ : SuzukiTest}
    (hsupp : Function.support (ψ : ℝ → ℂ) ⊆ Icc (-a) a) :
    ∀ t : ℝ, a < |t| → (ψ : ℝ → ℂ) t = 0 := by
  intro t ht
  by_contra h0
  have hmem : t ∈ Icc (-a) a := hsupp (by simpa [Function.mem_support] using h0)
  have : |t| ≤ a := abs_le.mpr ⟨hmem.1, hmem.2⟩
  linarith

/-- **Integration by parts on the coefficient.**  The transform's ray coefficient at `Dψ` is the
conjugate Fourier integral of `ψ`. -/
theorem suzukiPHatCoefFn_toDerivativeZeroMean {a : ℝ} (ha : 0 ≤ a) (ψ : SuzukiTest)
    (hsupp : Function.support (ψ : ℝ → ℂ) ⊆ Icc (-a) a) {w : ℂ} (hw : w ≠ 0) :
    suzukiPHatCoefFn ((ψ.toCompactTest hsupp).toDerivativeZeroMean) w
      = I * ∫ t : ℝ, Complex.exp (-(I * w * (t : ℂ))) * (starRingEnd ℂ) ((ψ : ℝ → ℂ) t) := by
  have hψ1 : ContDiff ℝ 1 (ψ : ℝ → ℂ) := ψ.smooth.of_le (by simp)
  have hcd : ContDiff ℝ 1 (fun s : ℝ => (starRingEnd ℂ) ((ψ : ℝ → ℂ) s)) :=
    Complex.conjCLE.contDiff.comp hψ1
  have hsupp' : ∀ t : ℝ, a < |t| → (starRingEnd ℂ) ((ψ : ℝ → ℂ) t) = 0 := by
    intro t ht
    rw [suzukiTest_supp hsupp t ht, map_zero]
  have hcongr : ∀ t : ℝ,
      (Complex.exp (-(I * w * (t : ℂ))) - 1)
        * (starRingEnd ℂ) ((((ψ.toCompactTest hsupp).toDerivativeZeroMean) : ℝ → ℂ) t)
      = (Complex.exp (-(I * w * (t : ℂ))) - 1)
        * deriv (fun s : ℝ => (starRingEnd ℂ) ((ψ : ℝ → ℂ) s)) t := by
    intro t
    rw [deriv_conj_suzukiTest, SuzukiSmoothCompactTest.coe_toDerivativeZeroMean]
    rfl
  rw [suzukiPHatCoefFn,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_expSlope_mul_deriv ha hcd hsupp' w]
  field_simp

theorem suzukiPHatCoefFn_ofReal {a : ℝ} (ha : 0 ≤ a) (ψ : SuzukiTest)
    (hsupp : Function.support (ψ : ℝ → ℂ) ⊆ Icc (-a) a) {γ : ℝ} (hγ : (γ : ℝ) ≠ 0) :
    suzukiPHatCoefFn ((ψ.toCompactTest hsupp).toDerivativeZeroMean) ((γ : ℝ) : ℂ)
      = I * (starRingEnd ℂ) (suzukiEntireFourier (ψ : ℝ → ℂ) ((γ : ℝ) : ℂ)) := by
  have hw : ((γ : ℝ) : ℂ) ≠ 0 := by simpa using hγ
  rw [suzukiPHatCoefFn_toDerivativeZeroMean ha ψ hsupp hw]
  congr 1
  rw [suzukiEntireFourier, ← integral_conj]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  rw [map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (I * ((γ : ℝ) : ℂ) * (t : ℂ)) = -(I * ((γ : ℝ) : ℂ) * (t : ℂ)) := by
    simp
  rw [hc]
  ring

end RHTower
