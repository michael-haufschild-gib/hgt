import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Aliasing
import GaloisForLFunctions.HTGeometry.Quantum.IntegerClockPhaseEquidistribution

/-! # Haar distribution of the surviving phases on affine time lattices -/
open Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling
noncomputable section

private theorem mean_powers {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    Tendsto (fun n : ℕ => (n:ℂ)⁻¹ * ∑ j ∈ Finset.range n, z^j) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_const_div_atTop_nhds_zero_nat (2/‖z-1‖))
  intro n
  rw [geom_sum_eq hne, norm_mul, norm_inv, norm_div,Complex.norm_natCast]
  have hb : ‖z^n-1‖ ≤ 2 := (norm_sub_le _ _).trans_eq (by rw [norm_pow,hz,one_pow,norm_one]; norm_num)
  rw [show (2/‖z-1‖)/(n:ℝ) = (n:ℝ)⁻¹*(2/‖z-1‖) by ring]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (norm_nonneg _)) (by positivity)

/-- The empirical Fourier coefficient vanishes whenever this character
has nonintegral winding. Other characters may be resonant. -/
theorem off_resonance_character {I : Type*} [Fintype I] (ω : I → ℝ) (τ a : ℝ) (m : I → ℤ)
    (hn : ∀ k : ℤ, τ*finiteTorusCharacterDetuning m ω≠(k:ℝ)*(2*Real.pi)) :
    Tendsto (fun N => ∫ x, UnitAddTorus.mFourier m x
      ∂(integerClockPrefixLaw (fun n => finiteClockPhasePoint ω (a+(n:ℝ)*τ)) N : Measure _))
      atTop (𝓝 0) := by
  simp_rw [integral_integerClockPrefixLaw _ _ _ (UnitAddTorus.mFourier m).continuous.measurable,
    mFourier_finiteClockPhasePoint]
  let d := finiteTorusCharacterDetuning m ω
  let z := Complex.exp (((τ*d:ℝ):ℂ)*Complex.I)
  let u := Complex.exp (((a*d:ℝ):ℂ)*Complex.I)
  have hz : z ≠ 1 := by
    intro h
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp h
    apply hn k
    apply Complex.ofReal_injective
    apply mul_right_cancel₀ Complex.I_ne_zero
    push_cast
    simpa only [Complex.ofReal_mul, mul_assoc] using hk
  have he (n : ℕ) : Complex.exp ((((a+(n:ℝ)*τ)*d:ℝ):ℂ)*Complex.I) = u*z^n := by
    dsimp only [z,u]
    rw [←Complex.exp_nat_mul,←Complex.exp_add]
    congr 1
    push_cast
    ring
  change Tendsto (fun N : ℕ => _ * ∑ j ∈ Finset.range (N+1),
    Complex.exp ((((a+(j:ℝ)*τ)*d:ℝ):ℂ)*Complex.I)) atTop (𝓝 0)
  simp_rw [he,←Finset.mul_sum,mul_left_comm _ u]
  have hav := ((mean_powers (z := z) (Complex.norm_exp_ofReal_mul_I _) hz).comp
    (tendsto_add_atTop_nat 1)).const_mul u
  rw [mul_zero] at hav
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using hav

/-- At every nonresonant step the empirical phase laws converge to Haar,
including after an arbitrary translation of the time origin. -/
theorem affine_phaseLaw {I : Type*} [Fintype I] (ω : I → ℝ) (τ a : ℝ) (hf : FreeAtStep ω τ) :
    Tendsto (integerClockPrefixLaw (fun n => finiteClockPhasePoint ω (a+(n:ℝ)*τ))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure I)) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hm : m=0
  · subst m
    simp_rw [integral_integerClockPrefixLaw _ _ _ (UnitAddTorus.mFourier _).continuous.measurable,
      mFourier_finiteClockPhasePoint]
    have hd : finiteTorusCharacterDetuning (0 : I → ℤ) ω = 0 := by simp [finiteTorusCharacterDetuning]
    simp [hd,Nat.cast_add_one_ne_zero]
  rw [if_neg hm]
  exact off_resonance_character ω τ a m (fun k he => hm (hf m k he))

/-- Every nonzero period preserves the Haar law after deleting at most one
frequency. Both the step and the origin can be chosen after seeing ω. -/
theorem all_periods_projected_haar {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (ω : I → ℝ) (hi : RationallyIndependentFrequency ω) :
    ∀ τ : ℝ, τ ≠ 0 → ∃ b : I, ∀ a : ℝ,
      Tendsto (integerClockPrefixLaw (fun n => finiteClockPhasePoint
        (fun j : {j : I // j ≠ b} => ω j) (a+(n:ℝ)*τ))) atTop
        (𝓝 (finiteTorusHaarProbabilityMeasure {j : I // j ≠ b})) := by
  intro τ hτ
  obtain ⟨b,hb⟩ := exists_free_deletion ω hi τ hτ
  exact ⟨b,fun a => affine_phaseLaw _ τ a hb⟩

#print axioms all_periods_projected_haar
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling
