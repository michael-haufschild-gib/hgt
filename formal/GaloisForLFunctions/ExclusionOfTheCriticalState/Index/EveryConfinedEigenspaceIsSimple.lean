import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerOuterAndCyclic
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesDecideTheCriticalRatio

/-!
# The integral determines a confined eigenfunction

At an imaginary-axis Laplace zero the undamped resolvent is a half-line test.
The bare Weil pairing and the ordinary inner product with this test vanish.
The confined eigenvalue equation therefore forces its weighted resolvent norm
to vanish. In particular integration is injective on each real eigenspace.
Critical ratios of an orthogonal ladder are strictly increasing.
-/

noncomputable section
open MeasureTheory Filter Set Topology FourierTransform Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations CriticalArithmeticCorrelationTheory
  ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ _root_.RHTower

/-- The weak eigenvalue equation of the confined Weil form at energy λ. -/
def SatisfiesConfinedEigenEquation (R E : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
    criticalHalfLineMixedEnergy R F G = E * ∫ u, F u * G u

/-- A boundary Laplace zero of a confined eigenfunction forces the entire
profile to vanish, at every positive ratio and every real eigenvalue. -/
theorem ae_zero_of_confined_boundary_zero {R E : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (heig : SatisfiesConfinedEigenEquation R E F) {b : ℝ}
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) = 0) :
    F =ᵐ[volume] 0 := by
  have htest := hF.realUndampedCausalConvolution b hz
  have he := heig _ htest
  have horth := integral_mul_eq_zero_of_fourier_pair_zero hF htest
    (gammaFourierPair_realUndampedCausalConvolution b hF hz)
  obtain ⟨hg, hp⟩ := arithmetic_mixed_realUndampedCausalConvolution_eq_zero b hF hz
  unfold criticalHalfLineMixedEnergy at he
  rw [horth, hg, hp, pole_mixed_realUndampedCausalConvolution_eq_zero b hF hz,
    integral_weighted_realUndampedCausalConvolution_mixed b hF] at he
  simp only [zero_div, sub_zero, zero_add, mul_zero, ← mul_assoc] at he
  have hcoeff : criticalAliasCoefficient R * (4 / Real.pi) ≠ 0 :=
    (mul_pos (criticalAliasCoefficient_positive hR) (by positivity)).ne'
  have hnorm := (mul_eq_zero.mp he).resolve_left hcoeff
  have hK := memLp_weighted_modulatedCausalConvolution
    (a := 0) (x := 4 / Real.pi) (by positivity) b hF.memLp_weightedComplex
  have hzero := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun u =>
    sq_nonneg ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution 0 b (cx F)) u‖)
    ((memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mp hK)).mp hnorm
  have hres : modulatedCausalConvolution 0 b (cx F) =ᵐ[volume] 0 := by
    filter_upwards [hzero] with u hu
    have h := norm_eq_zero.mp (sq_eq_zero_iff.mp hu)
    exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  -- Fourier multiplication by the resolvent denominator recovers the input.
  have hfi : Integrable (cx F) := hF.integrable.ofReal (𝕜 := ℂ)
  have hs (u : ℝ) (hu : 0 ≤ u) : cx F u = 0 := by
    change (F u : ℂ) = 0
    rw [hF.support u hu, Complex.ofReal_zero]
  have hfzero : cx F =ᵐ[volume] 0 := by
    apply _root_.HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hfi
    intro ξ
    have hh := fourier_undampedCausalConvolution_mul (f := cx F) b
      (Complex.continuous_ofReal.measurable.comp hF.meas) hfi hF.memLp_weightedComplex hs hz ξ
    have hk : 𝓕 (modulatedCausalConvolution 0 b (cx F)) ξ = 0 := by
      rw [Real.fourier_congr_ae hres, Real.fourier_real_eq_integral_exp_smul]
      simp
    rw [hk, mul_zero] at hh
    exact hh.symm
  filter_upwards [hfzero] with u hu
  exact Complex.ofReal_eq_zero.mp hu

private theorem ae_zero_of_confined_integral_zero {R E : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (heig : SatisfiesConfinedEigenEquation R E F) (hz : (∫ u, F u) = 0) :
    F =ᵐ[volume] 0 := by
  apply ae_zero_of_confined_boundary_zero hR hF heig (b := 0)
  have hw : modulatedLaplaceRate 0 0 = ((0 : ℝ) : ℂ) := by simp [modulatedLaplaceRate]
  rw [hw, negativeHalfLineLaplace_ofReal]
  simp [hz]

private theorem integral_sq_zero_of_ae_zero {F : ℝ → ℝ} (h : F =ᵐ[volume] 0) :
    (∫ u, F u ^ 2) = 0 := by
  calc
    _ = ∫ _u : ℝ, (0 : ℝ) := integral_congr_ae (h.mono fun u hu => by
      change F u = 0 at hu
      rw [hu, zero_pow two_ne_zero])
    _ = 0 := by simp

private theorem SatisfiesConfinedEigenEquation.add_const_mul {R E : ℝ}
    {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (eF : SatisfiesConfinedEigenEquation R E F) (eG : SatisfiesConfinedEigenEquation R E G)
    (c : ℝ) : SatisfiesConfinedEigenEquation R E (fun u => F u + c * G u) := by
  intro X hX
  have hprod {Y : ℝ → ℝ} (hY : CriticalHalfLineEnergyDomain Y) : Integrable fun u => Y u * X u :=
    integrable_mul_of_sq_integrable hY.meas.aestronglyMeasurable hX.meas.aestronglyMeasurable hY.sq hX.sq
  rw [criticalHalfLineMixedEnergy_add_const_mul_left R hF hG hX c, eF X hX, eG X hX]
  simp only [add_mul, mul_assoc, integral_add (hprod hF) ((hprod hG).const_mul c), integral_const_mul]
  ring

/-- Every real confined eigenspace is simple. The proportionality constant
is the ratio of the integrals of the two profiles. -/
theorem confined_eigenfunction_eq_integral_ratio {R E : ℝ} (hR : 0 < R)
    {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (eF : SatisfiesConfinedEigenEquation R E F) (eG : SatisfiesConfinedEigenEquation R E G)
    (hFn : (∫ u, F u ^ 2) ≠ 0) :
    (∫ u, F u) ≠ 0 ∧ G =ᵐ[volume] fun u => ((∫ v, G v) / (∫ v, F v)) * F u := by
  have hm : (∫ u, F u) ≠ 0 := fun hz =>
    hFn (integral_sq_zero_of_ae_zero (ae_zero_of_confined_integral_zero hR hF eF hz))
  let c := (∫ u, G u) / (∫ u, F u)
  have hcharge : (∫ u, G u + (-c) * F u) = 0 := by
    rw [integral_add hG.integrable (hF.integrable.const_mul _), integral_const_mul, neg_mul]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hm, add_neg_cancel]
  have hz := ae_zero_of_confined_integral_zero hR (hG.add_const_mul hF (-c))
    (eG.add_const_mul hG hF eF (-c)) hcharge
  refine ⟨hm, ?_⟩
  filter_upwards [hz] with u hu
  change G u + (-c) * F u = 0 at hu
  change G u = c * F u
  linarith only [hu]

private theorem IsConfinedNullVector.eigen_zero {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) :
    SatisfiesConfinedEigenEquation R 0 F := fun G hG => by
  rw [hF.2.2 G hG, zero_mul]

/-- No nonzero confined null vector has an imaginary-axis Laplace zero,
even when the confined form already has negative directions. -/
theorem IsConfinedNullVector.boundary_laplace_ne_zero {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) (b : ℝ) :
    negativeHalfLineLaplace (cx F) (modulatedLaplaceRate 0 b) ≠ 0 :=
  fun hz => hF.2.1 (integral_sq_zero_of_ae_zero (ae_zero_of_confined_boundary_zero hR hF.1 hF.eigen_zero hz))

/-- Every pair of distinct rungs crosses at distinct ratios, for any zero divisor. -/
theorem IsCriticalLadder.strictMono_ratio {m : ℕ} {R : Fin (m+1) → ℝ} {Φ : Fin (m+1) → ℝ → ℝ}
    (hL : IsCriticalLadder m R Φ) : StrictMono R := by
  intro i j hij
  refine lt_of_le_of_ne (hL.mono hij.le) ?_
  intro heq
  have hi := hL.null i
  have hj : IsConfinedNullVector (R i) (Φ j) := by rw [heq]; exact hL.null j
  obtain ⟨-, hprop⟩ := confined_eigenfunction_eq_integral_ratio (hL.pos i) hi.1 hj.1
    hi.eigen_zero hj.eigen_zero hi.2.1
  let c := (∫ v, Φ j v) / (∫ v, Φ i v)
  have hpair : criticalHalfLineExponentialPair (Φ i) (Φ j) =
      c * criticalHalfLineExponentialPair (Φ i) (Φ i) := by
    rw [← exponentialPair_const_mul]
    exact integral_congr_ae (hprop.mono fun u hu => by
      change Φ j u = c * Φ i u at hu
      change Φ i u * Φ j u * _ = Φ i u * (c * Φ i u) * _
      rw [hu])
  rw [hL.orth i j hij.ne] at hpair
  have hc : c = 0 := (mul_eq_zero.mp hpair.symm).resolve_right
    (exponentialPair_self_pos hi.1 hi.2.1).ne'
  have hz : Φ j =ᵐ[volume] 0 := hprop.mono fun u hu => by
    change Φ j u = c * Φ i u at hu
    change Φ j u = 0
    simpa only [hc, zero_mul] using hu
  exact hj.2.1 (integral_sq_zero_of_ae_zero hz)

#print axioms ae_zero_of_confined_boundary_zero
#print axioms confined_eigenfunction_eq_integral_ratio
#print axioms IsConfinedNullVector.boundary_laplace_ne_zero
#print axioms IsCriticalLadder.strictMono_ratio

end GaloisForLFunctions.ExclusionOfTheCriticalState
