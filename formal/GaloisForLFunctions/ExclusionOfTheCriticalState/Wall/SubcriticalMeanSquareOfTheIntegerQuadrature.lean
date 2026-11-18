import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheZetaZerosOfTheIntegerPrimitive
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.FractionalFourierEnergyOfTheTiltedState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.ZetaOnSubcriticalFourierLines
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.SquareIntegrableDerivativesFromFourierMoments

/-!
# Subcritical exponential tilts of the integer quadrature error
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Integer wave minus its continuous density, on the real Mellin line of tilt β. -/
def tiltedIntegerError (Φ : ℝ → ℝ) (β t : ℝ) : ℝ :=
  Real.exp (β*t)*(integerReferenceWave Φ t - Real.exp (t/2)*(∫ u, Real.exp (-u/2)*Φ u))

open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- Every subcritical exponential tilt gives a square integrable quadrature
error for the continuous critical state. -/
theorem criticalState_subcritical_integer_error {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hΦ : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ u, |Φ u| ≤ K*Real.exp (2*u))
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2) :
    MemLp (tiltedIntegerError Φ β) 2 := by
  let σ := 1/2-β
  let B := weightedIntegerPrimitive Φ β
  let ψ := fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)
  let f := fun u : ℝ => (B u:ℂ)
  let r := 1-σ/2
  have hσ : 0 < σ := sub_pos.2 hβ'
  have hhalf : σ ≤ 1/2 := sub_le_self _ hβ
  obtain ⟨hi,h2,hFourier⟩ := state_representative_integerPrimitive_fourier
    (criticalHalfLineEnergyDomain_of_groundState hF) hΦ he hK hb hβ hβ'
  have hf0 : Integrable (fun ξ : ℝ => ‖𝓕 ψ ξ‖^2) := by
    simpa only [Real.rpow_zero,one_mul,ψ] using
      criticalState_tilted_fractional_fourier_energy hW ht hF he hβ (show (0:ℝ)≤0 from le_rfl) zero_lt_one
  have hfr : Integrable (fun ξ : ℝ => |ξ|^r*‖𝓕 ψ ξ‖^2) :=
    criticalState_tilted_fractional_fourier_energy hW ht hF he hβ
      (by dsimp only [r]; linarith only [hhalf]) (by dsimp only [r]; linarith only [hσ])
  obtain ⟨C,_,hC⟩ := squared_zeta_on_positive_line hσ hhalf
  have hmoment : Integrable fun ξ : ℝ => (2*Real.pi*ξ)^2*‖𝓕 f ξ‖^2 := by
    have hcont := RHTower.continuous_fourier_of_integrable (show Integrable f from hi)
    apply ((hf0.add hfr).const_mul C).mono' (by fun_prop)
    refine Eventually.of_forall fun ξ => ?_
    let z := (σ:ℂ)+((2*Real.pi*ξ:ℝ):ℂ)*Complex.I
    have him : z.im = 2*Real.pi*ξ := by simp [z]
    have hz : z ≠ 0 := fun h => by
      have e := congrArg Complex.re h
      simp [z] at e
      exact hσ.ne' e
    have hz' := Complex.abs_im_le_norm z
    rw [him] at hz'
    have ham : (2*Real.pi*ξ)^2 ≤ ‖z‖^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hz' 2
    have heq : 𝓕 f ξ = 𝓕 ψ ξ*(riemannZeta z/z) := hFourier ξ
    change ‖(2*Real.pi*ξ)^2*‖𝓕 f ξ‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),heq,norm_mul,norm_div,mul_pow,div_pow]
    change _ ≤ C*(‖𝓕 ψ ξ‖^2+|ξ|^r*‖𝓕 ψ ξ‖^2)
    calc _ ≤ ‖z‖^2*(‖𝓕 ψ ξ‖^2*(‖riemannZeta z‖^2/‖z‖^2)) :=
           mul_le_mul_of_nonneg_right ham (by positivity)
      _ = ‖riemannZeta z‖^2*‖𝓕 ψ ξ‖^2 := by field_simp [(norm_ne_zero_iff.mpr hz)] <;> ring
      _ ≤ (C*(1+|ξ|^r))*‖𝓕 ψ ξ‖^2 := mul_le_mul_of_nonneg_right (hC ξ) (sq_nonneg _)
      _ = _ := by ring
  let b := fun t : ℝ => -σ*B t+tiltedIntegerError Φ β t
  have hderiv (t : ℝ) : HasDerivAt B (b t) t := hasDerivAt_weightedIntegerPrimitive hΦ hK hb β t
  have hbm := integrable_square_derivative_of_fourier_moment hderiv hi h2 hmoment
  have hB : Continuous B := continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt
  have hN := continuous_integerReferenceWave hΦ hK hb
  have hbc : Continuous b := by dsimp only [b,tiltedIntegerError]; fun_prop
  have hb2 : MemLp b 2 := (memLp_two_iff_integrable_sq_norm hbc.aestronglyMeasurable).2
    (by simpa only [Real.norm_eq_abs,sq_abs] using hbm)
  have hBr : MemLp B 2 := (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).2
    (by simpa only [f,Complex.norm_real] using (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).1 h2)
  exact (hb2.add (hBr.const_mul σ)).congr (Eventually.of_forall fun t => by
    change -σ*B t+tiltedIntegerError Φ β t+σ*B t = _; ring)

/-- Failure of RH supplies a single actual state with square integrable integer
quadrature on every subcritical exponential line. -/
theorem riemannHypothesis_or_subcritical_integer_quadrature : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ β : ℝ, 0 ≤ β → β < 1/2 → MemLp (tiltedIntegerError Φ β) 2 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,_,⟨K,hK,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun _ => criticalState_subcritical_integer_error hW ht hF hΦ he hK hb⟩

#print axioms riemannHypothesis_or_subcritical_integer_quadrature
end GaloisForLFunctions.ExclusionOfTheCriticalState
