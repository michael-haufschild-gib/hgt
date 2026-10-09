import GaloisForLFunctions.HTGeometry.PaperCayleyRationalReconstruction
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiCarrierCayleyMomentBound

/-! # Recovering the actual Suzuki carrier from its Cayley moments

The normalized native moments are exactly Fourier coefficients. The paper endpoint
therefore recovers the literal arithmetic carrier density, and its Nevanlinna
weight, along every symmetric cutoff outside one Lebesgue-null set.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
local instance paperSuzukiCircleMeasurable : MeasurableSpace Circle :=
  GaloisForLFunctions.HTGeometry.instMeasurableSpaceCircle_galoisForLFunctions

/-- The exact angular coordinate already used by the native Cayley moment identity. -/
def paperSuzukiCayleyChart (t : ℝ) : AddCircle Real.pi :=
  ((Real.arctan t + Real.pi / 2 : ℝ) : AddCircle Real.pi)

/-- The Suzuki angular chart is the same Cayley chart after exact period rescaling. -/
theorem paperSuzukiCayleyChart_rescale (t : ℝ) :
    paperCircleRescale Real.pi 1 (paperSuzukiCayleyChart t) =
      addCircleCircleEquiv.symm (circleCayley t) := by
  apply addCircleCircleEquiv.injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Subtype.ext
  change ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
    (paperCircleRescale Real.pi 1 (paperSuzukiCayleyChart t)) : Circle) : ℂ) = _
  rw [AddCircle.homeomorphCircle_apply, ← fourier_one,
    fourier_paperCircleRescale, circleCayley_coe]
  exact (suzukiXiCarrierCayleyBoundaryCoordinate_eq_shifted_fourier t).symm

/-- Circle-null sets pull back to Lebesgue-null sets in the actual spectral coordinate. -/
theorem paperSuzukiCayleyChart_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving paperSuzukiCayleyChart volume
      (AddCircle.haarAddCircle (T := Real.pi)) := by
  have h0 := circleCayley_weighted_measurePreserving.quasiMeasurePreserving.mono_left
    (withDensity_absolutelyContinuous'
      (measurable_realDensity measurable_standardCauchyWeight).aemeasurable
      (Eventually.of_forall (fun t => by
        simpa only [realDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le] using
          standardCauchyWeight_pos t)))
  have h1 := (addCircleCircleMeasurePreserving.symm addCircleCircleEquiv).quasiMeasurePreserving.comp h0
  let e := paperCircleRescale Real.pi 1
  have h2 := ((paperCircleRescale_measurePreserving Real.pi 1).symm
    e.toMeasurableEquiv).quasiMeasurePreserving.comp h1
  convert h2 using 1
  funext t
  have h := congrArg e.symm (paperSuzukiCayleyChart_rescale t)
  simpa [e] using h

/-- The native angular density equals the literal arithmetic density at every real point. -/
theorem paperSuzukiCayleyChart_density (t : ℝ) :
    suzukiXiCarrierShiftedAngularCircleDensity (paperSuzukiCayleyChart t) =
      (suzukiXiRealAxisArithmeticCarrierDensity t : ℂ) := by
  have ht : Real.arctan t + Real.pi / 2 ∈ Ioc (0 : ℝ) (0 + Real.pi) := by
    constructor <;> linarith [Real.neg_pi_div_two_lt_arctan t, Real.arctan_lt_pi_div_two t]
  unfold paperSuzukiCayleyChart suzukiXiCarrierShiftedAngularCircleDensity
  rw [AddCircle.liftIoc_coe_apply ht]
  simp only [suzukiXiCarrierShiftedAngularDensity, add_sub_cancel_right, Real.tan_arctan]

/-- Literal symmetric reconstruction using only the existing arithmetic Cayley moments. -/
def paperSuzukiMomentPartialSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (suzukiXiCarrierCayleyMoment (-n) / (Real.pi : ℂ)) *
      suzukiXiCarrierCayleyBoundaryZPower n t

theorem paperSuzukiMomentPartialSum_eq (N : ℕ) (t : ℝ) :
    paperSuzukiMomentPartialSum N t =
      paperCircleFourierPartialSum Real.pi suzukiXiCarrierShiftedAngularCircleDensity N
        (paperSuzukiCayleyChart t) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold paperSuzukiMomentPartialSum paperCircleFourierPartialSum
  apply Finset.sum_congr rfl
  intro n _
  rw [suzukiXiCarrierCayleyMoment_eq_pi_mul_fourierCoeff,
    suzukiXiCarrierCayleyBoundaryZPower_eq_shifted_fourier]
  simp [hpi, paperSuzukiCayleyChart]

/-- All symmetric moment cutoffs converge to the actual arithmetic carrier density. -/
theorem paperSuzukiMoment_density_reconstruction :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, Tendsto (fun N => paperSuzukiMomentPartialSum N t) atTop
        (𝓝 (suzukiXiRealAxisArithmeticCarrierDensity t : ℂ)) := by
  obtain ⟨D, _, hz, hc⟩ := paperCircleLp_fourier_convergence Real.pi
    suzukiXiCarrierShiftedAngularDensityLp
  have ha : ∀ᵐ x ∂AddCircle.haarAddCircle,
      Tendsto (fun N => paperCircleFourierPartialSum Real.pi
        suzukiXiCarrierShiftedAngularCircleDensity N x) atTop
        (𝓝 (suzukiXiCarrierShiftedAngularCircleDensity x)) := by
    filter_upwards [compl_mem_ae_iff.mpr hz, suzukiXiCarrierShiftedAngularDensityLp_ae]
      with x hx he
    simpa only [paperCircleFourierPartialSum,
      fourierCoeff_congr_ae suzukiXiCarrierShiftedAngularDensityLp_ae, he] using hc x hx
  have hb : ∀ᵐ t ∂volume, Tendsto (fun N => paperSuzukiMomentPartialSum N t) atTop
      (𝓝 (suzukiXiRealAxisArithmeticCarrierDensity t : ℂ)) := by
    filter_upwards [paperSuzukiCayleyChart_quasiMeasurePreserving.ae ha] with t ht
    simpa only [← paperSuzukiMomentPartialSum_eq, paperSuzukiCayleyChart_density] using ht
  obtain ⟨E, hsub, hm, hz⟩ := exists_measurable_superset_of_null (ae_iff.mp hb)
  refine ⟨E, hm, hz, ?_⟩
  intro t ht
  by_contra h
  exact ht (hsub h)

/-- The same moments reconstruct the actual Lebesgue density of the native carrier measure. -/
theorem paperSuzukiMoment_nevanlinnaWeight_reconstruction :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, Tendsto (fun N => paperSuzukiMomentPartialSum N t / ((1 + t ^ 2 : ℝ) : ℂ))
        atTop (𝓝 (suzukiXiCarrierNevanlinnaWeight t : ℂ)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperSuzukiMoment_density_reconstruction
  refine ⟨E, hm, hz, fun t ht => ?_⟩
  simpa only [suzukiXiCarrierNevanlinnaWeight, Complex.ofReal_div, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv] using
    (hc t ht).mul_const (((1 + t ^ 2 : ℝ) : ℂ)⁻¹)

end
end RiemannGaussian
