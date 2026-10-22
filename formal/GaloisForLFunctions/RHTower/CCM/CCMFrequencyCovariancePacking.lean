import GaloisForLFunctions.RHTower.CCM.CCMSmoothNearRadical
import GaloisForLFunctions.RHTower.CCM.CCMPositiveFrequencyGramSaving
import GaloisForLFunctions.HTGeometry.L2CovarianceBessel

/-!
# Actual near-radical obstruction to a scalar covariance certificate

Many independent near-null directions impose a lower bound on the signed
covariance norm, even after retaining the complete positive-frequency window.
All parameters and every coefficient cross term remain present. The result
limits this sufficient certificate; it does not decide the Weil form's sign.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- Signed physical analysis energy, after the actual positive-window retention. -/
def ccmRetainedFrequencyDebt (a : SuzukiPositiveAperture) (α R : ℝ) (f : SoninL2) : ℝ :=
  (∫ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ) f‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α) -
    ccmPositiveFrequencyRetention a α R *
      (∫ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ) f‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R)

/-- The signed analysis energy must pay the full mass minus the actual source energy. -/
theorem ccmRetainedFrequencyDebt_ge_mass_sub_source
    (a : SuzukiPositiveAperture) (α R : ℝ) (u : ccmPolarConstraintSubmodule a) :
    α * ‖ccmArchimedeanFormEmbedding a u.1‖ ^ 2 - ccmRestrictedWeilSourceQuadratic a u.1 ≤
      ccmRetainedFrequencyDebt a α R (ccmArchimedeanFormEmbedding a u.1) := by
  have hsame : ∀ᵐ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ)
      (ccmArchimedeanFormEmbedding a u.1)‖ ^ 2 = ‖(u.1.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    filter_upwards [ccmFormDomain_ae_eq_fourier a u.1] with ξ hξ
    change ‖inner ℂ (ccmPolarPlaneWave a ξ)
      (ccmArchimedeanFormToAperture a u.1).1‖ ^ 2 = _
    rw [inner_ccmPolarPlaneWave_eq_fourier a u, hξ]
  have hN : (∫ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ)
      (ccmArchimedeanFormEmbedding a u.1)‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α) =
      ∫ ξ, ‖(u.1.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α := by
    rw [ccmNegativeFrequency_integral, ccmNegativeFrequency_integral]
    apply integral_congr_ae
    filter_upwards [hsame] with ξ hξ
    rw [hξ]
  have hP : (∫ ξ, ‖inner ℂ (ccmPolarPlaneWaveFrame a ξ)
      (ccmArchimedeanFormEmbedding a u.1)‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R) =
      ∫ ξ, ‖(u.1.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R := by
    rw [ccmPositiveFrequency_integral, ccmPositiveFrequency_integral]
    apply integral_congr_ae
    filter_upwards [hsame] with ξ hξ
    rw [hξ]
  have h := ccmRestrictedWeilSource_ge_retainedPositiveWindow a α R
    ⟨ccmPositiveFrequencyRetention a α R, ccmPositiveFrequencyRetention_bounds a α R⟩ u.1
  change α * ‖ccmArchimedeanFormEmbedding a u.1‖ ^ 2 - _ ≤ _ at h
  rw [ccmRetainedFrequencyDebt, hN, hP]
  linarith only [h]

/-- Bessel packing applies to the actual signed source coordinates. -/
theorem ccmRetainedFrequencyDebt_sum_sq_le {ι : Type*} (s : Finset ι)
    (a : SuzukiPositiveAperture) (α R : ℝ) (f : ι → SoninL2) (hf : Orthonormal ℂ f) :
    ∑ i ∈ s, ccmRetainedFrequencyDebt a α R (f i) ^ 2 ≤
      ccmPositiveFrequencyGramCeiling a α R ^ 2 :=
  l2Frame_difference_sum_sq_le s (ccmActualSourceNegativeMeasure a α)
    (ccmPositiveFrequencyMeasure a α R) (ccmPolarPlaneWaveFrame a)
    (ccmPositiveFrequencyRetention a α R) f hf

private theorem covariance_packing_of_subspace
    (a : SuzukiPositiveAperture) (α R ε : ℝ) (hα : ε ≤ α)
    (V : Submodule ℂ SoninL2) [FiniteDimensional ℂ V]
    (hV : ∀ f ∈ V, ∃ u : ccmPolarConstraintSubmodule a,
      ccmArchimedeanFormEmbedding a u.1 = f ∧
      |ccmRestrictedWeilSourceQuadratic a u.1| ≤ ε * ‖f‖ ^ 2) :
    (Module.finrank ℂ V : ℝ) * (α - ε) ^ 2 ≤ ccmPositiveFrequencyGramCeiling a α R ^ 2 := by
  let e := stdOrthonormalBasis ℂ V
  let f : Fin (Module.finrank ℂ V) → SoninL2 := fun i => (e i).1
  have hf : Orthonormal ℂ f := e.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hpoint : ∀ i, (α - ε) ^ 2 ≤ ccmRetainedFrequencyDebt a α R (f i) ^ 2 := by
    intro i
    obtain ⟨u, hu, hQ⟩ := hV (f i) (e i).2
    have hD := ccmRetainedFrequencyDebt_ge_mass_sub_source a α R u
    rw [hu, hf.norm_eq_one i, one_pow, mul_one] at hD
    rw [hf.norm_eq_one i, one_pow, mul_one] at hQ
    have hb : α - ε ≤ ccmRetainedFrequencyDebt a α R (f i) := by
      linarith [le_abs_self (ccmRestrictedWeilSourceQuadratic a u.1)]
    exact pow_le_pow_left₀ (sub_nonneg.mpr hα) hb 2
  calc
    _ = ∑ i : Fin (Module.finrank ℂ V), (α - ε) ^ 2 := by simp
    _ ≤ ∑ i : Fin (Module.finrank ℂ V), ccmRetainedFrequencyDebt a α R (f i) ^ 2 :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ ≤ _ := ccmRetainedFrequencyDebt_sum_sq_le Finset.univ a α R f hf

/-- Every retained window inherits the actual near-radical dimension cost.
There is no assumed zero location, positivity, spectral gap, or numerical input. -/
theorem ccmPositiveFrequencyGramCeiling_nearRadical_lower :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 → ∀ α R : ℝ,
      Real.exp (-Real.exp (2 * a.1 - 4)) ≤ α →
        (Real.exp (2 * a.1 - 4) / 20) *
          (α - Real.exp (-Real.exp (2 * a.1 - 4))) ^ 2 ≤
            ccmPositiveFrequencyGramCeiling a α R ^ 2 := by
  obtain ⟨A, hA⟩ := ccm_actual_near_radical_dimension
  refine ⟨A, fun a ha α R hα => ?_⟩
  obtain ⟨V, hfin, hdim, hV⟩ := hA a ha
  letI := hfin
  exact (mul_le_mul_of_nonneg_right hdim (sq_nonneg _)).trans
    (covariance_packing_of_subspace a α R _ hα V hV)

/-- At large aperture a scalar covariance certificate cannot close above twice the
superexponentially small near-radical scale, regardless of the retained window. -/
theorem ccmPositiveFrequencyGramCeiling_exceeds_twice_nearRadical_scale :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 → ∀ α R : ℝ,
      2 * Real.exp (-Real.exp (2 * a.1 - 4)) ≤ α →
        α < ccmPositiveFrequencyGramCeiling a α R := by
  obtain ⟨A, hA⟩ := ccmPositiveFrequencyGramCeiling_nearRadical_lower
  refine ⟨max A 100, fun a ha α R hα => ?_⟩
  have haA := (le_max_left A 100).trans ha
  have ha100 := (le_max_right A 100).trans ha
  let ε := Real.exp (-Real.exp (2 * a.1 - 4))
  have hε : 0 < ε := Real.exp_pos _
  have hεα : ε ≤ α := by change 2 * ε ≤ α at hα; linarith
  have hb := hA a haA α R hεα
  have hdim : 5 ≤ Real.exp (2 * a.1 - 4) / 20 := by
    have he := Real.add_one_le_exp (2 * a.1 - 4)
    linarith
  have hc := (mul_le_mul_of_nonneg_right hdim (sq_nonneg (α - ε))).trans hb
  have hα0 : 0 < α := hε.trans_le hεα
  have hαsq : α ^ 2 ≤ 4 * (α - ε) ^ 2 := by
    change 2 * ε ≤ α at hα
    have hlin : α ≤ 2 * (α - ε) := by linarith
    have hsquare := pow_le_pow_left₀ hα0.le hlin 2
    nlinarith only [hsquare]
  have hgap : 0 < (α - ε) ^ 2 := by
    apply sq_pos_of_pos
    change 2 * ε ≤ α at hα
    linarith
  have hsq : α ^ 2 < ccmPositiveFrequencyGramCeiling a α R ^ 2 := by
    linarith only [hc, hαsq, hgap]
  exact (sq_lt_sq₀ hα0.le (norm_nonneg _)).mp hsq

end RHTower
