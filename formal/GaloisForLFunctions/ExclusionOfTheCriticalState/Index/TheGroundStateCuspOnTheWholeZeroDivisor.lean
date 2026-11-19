import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalLineCuspOfTheGroundState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.ThePoissonSpectrumOfAConfinedState
import GaloisForLFunctions.HTGeometry.TheCosineLossInAVerticalStrip

/-!
# The cosine cusp on the whole ζ divisor

At every threshold ground state the cosine loss of the reflected zero products
has right derivative four times the confinement energy. The sum runs over all
zero copies, including infinite off-line layers.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private abbrev diff (F : ℝ → ℝ) (h u : ℝ) := F u + (-1)*F (u+h)

/-- The unit tilt commutes with an inward difference up to a scalar
on the translated term. Thus the increment admits the unheated zero formula. -/
private theorem hasSum_reflected_increment {W : ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) {h : ℝ} (hh : 0 ≤ h) :
    HasSum (fun q : XiZeroCopy => exponentialLoss (centredZero q) h * reflectedLaplaceProduct F q)
      (bareMixedEnergy (diff F h) (diff F h) : ℂ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hG := criticalHalfLineEnergyDomain_increment hd hh
  have hT := criticalState_unitTilt_domain hW ht hF
  have hTG : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1*u)) * diff F h u) := by
    have he : (fun u => Real.exp (-(1*u))*diff F h u) = fun u =>
        Real.exp (-(1*u))*F u + (-Real.exp h)*(Real.exp (-(1*(u+h)))*F (u+h)) := by
      funext u
      have hx : Real.exp h * Real.exp (-(1*(u+h))) = Real.exp (-(1*u)) := by
        rw [← Real.exp_add]; congr 1; ring
      dsimp only [diff]
      linear_combination hx * F (u+h)
    rw [he]
    exact hT.add_const_mul (hT.causalTranslate hh) _
  have hs := hasSum_mul_of_tendsto_gaussian (summable_norm_sq_laplace_centredZero hTG)
    (summable_norm_sq_laplace_neg_centredZero hTG) (tendsto_heatedZeroPairing hG hG)
  refine hs.congr_fun fun q => ?_
  have hz : -4 < (centredZero q).re := by linarith only [(abs_lt.mp (abs_re_centredZero_lt q)).1]
  rw [laplace_translation_difference hd hh hz,
    laplace_translation_difference hd hh (neg_centredZero_re_gt_neg_four q)]
  simp only [exponentialLoss,reflectedLaplaceProduct,neg_mul,neg_neg]
  ring

private abbrev cosineTerm (F : ℝ → ℝ) (h : ℝ) (q : XiZeroCopy) : ℂ :=
  ((1-Real.cos (h*(centredZero q).im) : ℝ):ℂ) * reflectedLaplaceProduct F q

private theorem summable_cosineTerm {F : ℝ → ℝ}
    (hA : Summable fun q => ‖reflectedLaplaceProduct F q‖) (h : ℝ) :
    Summable (cosineTerm F h) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hA.mul_left 2)
  rw [cosineTerm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (one_sub_cos_mul_nonneg _ _)]
  exact mul_le_mul_of_nonneg_right (by linarith only [Real.neg_one_le_cos (h*(centredZero q).im)])
    (norm_nonneg _)

/-- The reflected samples on the full ζ divisor have cosine cusp `4aM`.
Off-line copies keep their signed complex coefficients. -/
theorem criticalState_wholeDivisor_cosine_cusp {W : ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) :
    Tendsto (fun h : ℝ => (∑' q : XiZeroCopy,
      ((1-Real.cos (h*(centredZero q).im) : ℝ):ℂ) * reflectedLaplaceProduct F q)/(h:ℂ))
      (𝓝[>] 0) (𝓝 ((4 * criticalAliasCoefficient W * ∫ u : ℝ, F u^2 * Real.exp (-(8*u)) : ℝ):ℂ)) := by
  let A := reflectedLaplaceProduct F
  have hn := isConfinedNullVector_of_groundState hW ht hF
  have hA : Summable fun q => ‖A q‖ := (hn.hasSum_bare_pair hW hW hn).summable.norm
  have herr := tendsto_strip_cosine_projection_error centredZero
    (fun q => by linarith only [abs_re_centredZero_lt q]) hA
  have hbare := Complex.continuous_ofReal.tendsto _ |>.comp
    (criticalState_tendsto_bare_increment_div hW ht hF)
  have hlim := (hbare.sub herr).div_const (2:ℂ)
  rw [sub_zero,show ∀ a M : ℝ, ((8*a*M : ℝ):ℂ)/2 = ((4*a*M : ℝ):ℂ) by intros; push_cast; ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0:ℝ) < h := hh
  have hK := hasSum_reflected_increment hW ht hF hh'.le
  have hP := (summable_cosineTerm hA h).hasSum.mul_left (2:ℂ)
  have he := ((hK.sub hP).const_smul (h⁻¹:ℝ)).tsum_eq
  have hsame (q : XiZeroCopy) :
      (exponentialLoss (centredZero q) h - ((2*(1-Real.cos (h*(centredZero q).im)) : ℝ):ℂ))*A q =
        exponentialLoss (centredZero q) h*reflectedLaplaceProduct F q - 2*cosineTerm F h q := by
    dsimp only [A,cosineTerm]; push_cast; ring
  change (((bareMixedEnergy (diff F h) (diff F h)/h : ℝ):ℂ) -
    ∑' q : XiZeroCopy, h⁻¹ • ((exponentialLoss (centredZero q) h -
      ((2*(1-Real.cos (h*(centredZero q).im)) : ℝ):ℂ))*A q))/2 = _
  simp_rw [hsame]
  rw [he,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_div]
  change _ = (∑' q : XiZeroCopy, cosineTerm F h q)/(h:ℂ)
  ring

#print axioms criticalState_wholeDivisor_cosine_cusp

end GaloisForLFunctions.ExclusionOfTheCriticalState
