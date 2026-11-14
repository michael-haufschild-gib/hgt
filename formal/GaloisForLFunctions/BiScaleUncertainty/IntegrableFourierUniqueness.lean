import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# Fourier uniqueness in finite-dimensional spaces

The one-dimensional mollifier argument extends to every finite-dimensional
real inner product space. A vanishing Fourier transform annihilates each
smooth convolution; Fourier inversion and convergence of mollifiers
then recover the original integrable function almost everywhere.
-/

open MeasureTheory Filter Convolution ContinuousLinearMap
open scoped FourierTransform Topology

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteDimensionalFourier
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Radial mollifiers with the same radii as the one-dimensional uniqueness argument. -/
private def bump (n : ℕ) : ContDiffBump (0 : V) where
  rIn := (HTGeometry.uniqBump n).rIn
  rOut := (HTGeometry.uniqBump n).rOut
  rIn_pos := (HTGeometry.uniqBump n).rIn_pos
  rIn_lt_rOut := (HTGeometry.uniqBump n).rIn_lt_rOut

/-- An integrable function is determined almost everywhere by its Fourier transform. -/
theorem ae_eq_zero_of_fourier_eq_zero {f : V → ℂ} (hf : Integrable f)
    (hF : 𝓕 f = 0) : f =ᵐ[volume] 0 := by
  have hloc := hf.locallyIntegrable
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure V)) (φ := bump) (l := atTop) (K := 2)
    HTGeometry.tendsto_uniqBump_rOut
    (Eventually.of_forall HTGeometry.uniqBump_ratio) hloc
  have hzero (n : ℕ) :
      ((bump n).normed (volume : Measure V) ⋆[lsmul ℝ ℝ] f) = 0 := by
    let ψ : V → ℝ := (bump n).normed (volume : Measure V)
    let ψc : V → ℂ := fun x => (ψ x : ℂ)
    have hψ : Integrable ψ := (bump n).integrable_normed
    have hψc : Integrable ψc := hψ.ofReal
    have hc : Continuous ψc :=
      Complex.continuous_ofReal.comp ((bump n).continuous_normed (μ := volume))
    have hcs : HasCompactSupport ψc :=
      ((bump n).hasCompactSupport_normed (μ := (volume : Measure V))).comp_left
        (g := fun r : ℝ => (r : ℂ)) (by simp)
    let u := ψc ⋆[ContinuousLinearMap.mul ℂ ℂ] f
    have hu : Continuous u := hcs.continuous_convolution_left _ hc hloc
    have hui : Integrable u := hψc.integrable_convolution _ hf
    have huF : 𝓕 u = 0 := by
      funext ξ
      rw [Real.fourier_mul_convolution_eq hψc hf, hF]
      simp
    have huFi : Integrable (𝓕 u) := by rw [huF]; exact integrable_zero _ _ _
    have hinv := hu.fourierInv_fourier_eq hui huFi
    have hu0 : u = 0 := by
      rw [huF] at hinv
      have hz : (𝓕⁻ (0 : V → ℂ)) = 0 := by
        funext x
        rw [Real.fourierInv_eq]
        simp
      exact hinv.symm.trans hz
    funext x
    change (ψ ⋆[lsmul ℝ ℝ] f) x = 0
    calc
      _ = u x := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [lsmul_apply, ContinuousLinearMap.mul_apply', ψc, Complex.real_smul]
      _ = 0 := congrFun hu0 x
  filter_upwards [hae] with x hx
  have hz : (fun n : ℕ =>
      ((bump n).normed (volume : Measure V) ⋆[lsmul ℝ ℝ] f) x) = fun _ => 0 := by
    funext n
    exact congrFun (hzero n) x
  rw [hz] at hx
  exact (tendsto_nhds_unique tendsto_const_nhds hx).symm

/-- Fourier uniqueness stated intrinsically on `L¹`. -/
theorem l1_fourier_eq_zero_iff (f : Lp ℂ 1 (volume : Measure V)) :
    𝓕 (f : V → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro hF
    apply Lp.ext
    exact (ae_eq_zero_of_fourier_eq_zero
      (memLp_one_iff_integrable.mp (Lp.memLp f)) hF).trans
        (Lp.coeFn_zero ℂ 1 volume).symm
  · rintro rfl
    funext ξ
    rw [Real.fourier_congr_ae (Lp.coeFn_zero ℂ 1 volume), Real.fourier_eq]
    simp

#print axioms ae_eq_zero_of_fourier_eq_zero
#print axioms l1_fourier_eq_zero_iff

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteDimensionalFourier
