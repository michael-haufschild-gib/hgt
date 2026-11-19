import GaloisForLFunctions.ExclusionOfTheCriticalState.TheConfinementEnergyOfAGroundStateIncrement
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheOnLineResolventOfAFiniteLayer
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheExplicitFormulaHoldsForTwoSidedTests
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The critical-line cusp of the ground state

For a finite off-line divisor the critical-line samples of the ground state have
cosine loss `4 a M h + o(h)`, where `a M` is its confinement energy. Apply the
diagonal zero formula to a translation difference. Each off-line pair of Laplace
factors has a double zero in the translation parameter, and the weighted
translation difference has squared norm `o(h)`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private abbrev diff (F : ℝ → ℝ) (h u : ℝ) := F u + (-1) * F (u+h)
private abbrev offCopy := (↑onLineCopiesᶜ : Type)
private abbrev L (F : ℝ → ℝ) := negativeHalfLineLaplace (cx F)
private def offTerm (F : ℝ → ℝ) (q : offCopy) (t : ℂ) : ℂ :=
  let z := centredZero q
  (1 - cexp (-z*t)) * (1 - cexp (z*t)) * (L F z * L F (-z))

/-- The Laplace transform of an inward translation difference factors at every point of the half-plane of convergence. -/
theorem laplace_translation_difference {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    {h : ℝ} (hh : 0 ≤ h) {z : ℂ} (hz : -4 < z.re) :
    negativeHalfLineLaplace (cx fun u => F u + (-1)*F (u+h)) z =
      (1 - cexp (-(z*h))) * negativeHalfLineLaplace (cx F) z := by
  change negativeHalfLineLaplace (cx fun u => F u + (-1) * shiftProfile F h u) z = _
  rw [laplace_cx_add hd ((criticalHalfLineEnergyDomain_shiftProfile hd hh).const_mul (-1)) hz,
    laplace_cx_const_mul, laplace_shiftProfile]
  simp only [Complex.ofReal_neg,Complex.ofReal_one]
  ring

private theorem centre_re_bound (q : XiZeroCopy) : -4 < (centredZero q).re := by
  linarith only [(abs_lt.mp (abs_re_centredZero_lt q)).1]

private theorem line_difference_mass {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    {h : ℝ} (hh : 0 ≤ h) (q : onLineCopies) :
    zeroValueMass (diff F h) q = 2 * ((1-Real.cos (h*(centredZero q).im)) * zeroValueMass F q) := by
  change ‖L (diff F h) (centredZero q)‖^2 = _
  change ‖negativeHalfLineLaplace (cx fun u => F u + (-1)*F (u+h)) (centredZero q)‖^2 = _
  rw [laplace_translation_difference hd hh (centre_re_bound _), norm_mul, mul_pow]
  have he : -(centredZero q * h) = ((-(h*(centredZero q).im) : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp [show (centredZero q).re = 0 from q.property, mul_comm]
  rw [he,norm_sq_one_sub_cexp,Real.cos_neg]
  dsimp only [zeroValueMass,L]
  ring

private theorem off_difference_slope (F : ℝ → ℝ) (q : offCopy) :
    Tendsto (fun h : ℝ => (offTerm F q h).re/h) (𝓝[>] 0) (𝓝 0) := by
  let z := centredZero q
  have hm := (hasDerivAt_const (0:ℂ) (1:ℂ)).sub ((hasDerivAt_const_mul (x := (0:ℂ)) (-z)).cexp)
  have hp := (hasDerivAt_const (0:ℂ) (1:ℂ)).sub ((hasDerivAt_const_mul (x := (0:ℂ)) z).cexp)
  have hd : HasDerivAt (offTerm F q) 0 0 := by
    simpa [offTerm,z] using (hm.mul hp).mul_const (L F z * L F (-z))
  have hr := Complex.continuous_re.tendsto (0:ℂ) |>.comp hd.comp_ofReal.tendsto_slope_zero_right
  have h0 : offTerm F q 0 = 0 := by simp [offTerm]
  simpa only [Function.comp_apply,zero_add,Complex.ofReal_zero,h0,sub_zero,
    Complex.smul_re,smul_eq_mul,Complex.zero_re,div_eq_inv_mul] using hr

private theorem difference_zero_formula {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (hf : BacklundConverse.FiniteOffLine) {h : ℝ} (hh : 0 ≤ h) :
    2 * (∑' q : onLineCopies, (1-Real.cos (h*(centredZero q).im)) * zeroValueMass F q) +
      (∑' q : offCopy, offTerm F q h).re = bareMixedEnergy (diff F h) (diff F h) := by
  have he := (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_increment hd hh) hf).2
  have hon := line_difference_mass hd hh
  have hoff (q : offCopy) : L (diff F h) (centredZero q) * L (diff F h) (-centredZero q) =
      offTerm F q h := by
    dsimp only [L,diff]
    rw [laplace_translation_difference hd hh (centre_re_bound _),laplace_translation_difference hd hh (neg_centredZero_re_gt_neg_four _)]
    dsimp only [offTerm]
    rw [neg_mul,neg_neg]
    ring
  change ((∑' q : onLineCopies, zeroValueMass (diff F h) q : ℝ) : ℂ) +
    (∑' q : offCopy, L (diff F h) (centredZero q) * L (diff F h) (-centredZero q)) = _ at he
  simp_rw [hon,hoff] at he
  rw [tsum_mul_left] at he
  exact congrArg Complex.re he

/-- The bare Weil energy of a ground-state increment has the same linear
term as its full energy, for any configuration of the zeros. -/
theorem criticalState_tendsto_bare_increment_div {W : ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) :
    Tendsto (fun h : ℝ => bareMixedEnergy (fun u => F u + (-1)*F (u+h))
      (fun u => F u + (-1)*F (u+h))/h) (𝓝[>] 0)
      (𝓝 (8 * criticalAliasCoefficient W * ∫ u : ℝ, F u^2 * Real.exp (-(8*u)))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hv := (criticalState_tendsto_weighted_sq_increment_div hW ht hF).const_mul
    (criticalAliasCoefficient W)
  have hlim := (criticalState_tendsto_fullEnergy_increment_div hW ht hF).sub hv
  rw [mul_zero,sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hg := criticalHalfLineEnergyDomain_increment hd (le_of_lt (show 0 < h from hh))
  have he := criticalHalfLineMixedEnergy_self W hg
  rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun u hu => by rw [hg.support u (not_lt.mp hu),zero_mul,zero_mul])] at he
  rw [← he]
  simp only [neg_one_mul,← sub_eq_add_neg,pow_two]
  ring

/-- With finitely many off-line copies, the cosine loss of the ground state's
critical-line samples has right derivative four times its confinement energy. -/
theorem criticalState_criticalLine_cosine_cusp {W : ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun h : ℝ => (∑' q : onLineCopies,
      (1-Real.cos (h*(centredZero q).im)) * zeroValueMass F q)/h) (𝓝[>] 0)
      (𝓝 (4 * criticalAliasCoefficient W * ∫ u : ℝ, F u^2 * Real.exp (-(8*u)))) := by
  classical
  letI : Fintype offCopy := (compl_onLineCopies_finite_of_finiteOffLine hf).fintype
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hsum := tendsto_finsetSum Finset.univ fun (q : offCopy) _ => off_difference_slope F q
  simp only [Finset.sum_const_zero] at hsum
  have hlim := ((criticalState_tendsto_bare_increment_div hW ht hF).sub hsum).div_const 2
  rw [sub_zero,show ∀ x y : ℝ, 8*x*y/2 = 4*x*y by intros; ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0:ℝ) < h := hh
  have hz := difference_zero_formula hd hf hh'.le
  rw [tsum_fintype,Complex.re_sum] at hz
  change (bareMixedEnergy (diff F h) (diff F h)/h -
    (∑ q : offCopy, (offTerm F q h).re/h))/2 = _
  rw [← Finset.sum_div]
  field_simp [hh'.ne']
  linarith only [hz]

/-- The first absolute ordinate moment of the ground state's critical-line
samples diverges whenever the off-line divisor is finite. -/
theorem criticalState_criticalLine_firstMoment_not_summable {W : ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine) :
    ¬ Summable (fun q : onLineCopies => |(centredZero q).im| * zeroValueMass F q) := by
  intro hm
  let γ := fun q : onLineCopies => (centredZero q).im
  let m := fun q : onLineCopies => zeroValueMass F q
  let f := fun h : ℝ => fun q : onLineCopies => h⁻¹ * ((1-Real.cos (h*γ q))*m q)
  have hp : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hl (q : onLineCopies) : Tendsto (fun h => f h q) (𝓝[>] 0) (𝓝 0) := by
    have hd := (hasDerivAt_const (0:ℝ) 1).sub (((hasDerivAt_id (0:ℝ)).mul_const (γ q)).cos)
    have hd' : HasDerivAt (fun h : ℝ => (1-Real.cos (h*γ q))*m q) 0 0 := by
      simpa using hd.mul_const (m q)
    simpa only [f,zero_add,zero_mul,Real.cos_zero,sub_self,sub_zero,smul_eq_mul] using
      hd'.tendsto_slope_zero_right
  have hb : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ q, ‖f h q‖ ≤ |γ q| * m q := by
    filter_upwards [hp] with h hh q
    have hcos := Real.abs_cos_sub_cos_le 0 (h*γ q)
    rw [Real.cos_zero,zero_sub,abs_neg,abs_mul,abs_of_pos hh,
      abs_of_nonneg (one_sub_cos_mul_nonneg h (γ q))] at hcos
    have hm0 : 0 ≤ m q := zeroValueMass_nonneg F q
    rw [Real.norm_of_nonneg (show 0 ≤ f h q from
      mul_nonneg (inv_nonneg.mpr hh.le) (mul_nonneg (one_sub_cos_mul_nonneg _ _) hm0))]
    change h⁻¹ * _ ≤ _
    rw [← div_eq_inv_mul,div_le_iff₀ hh]
    linarith only [mul_le_mul_of_nonneg_right hcos hm0]
  have hzero := tendsto_tsum_of_dominated_convergence hm hl hb
  simp only [tsum_zero,f,tsum_mul_left,← div_eq_inv_mul] at hzero
  have he := tendsto_nhds_unique (criticalState_criticalLine_cosine_cusp hW ht hF hf) hzero
  exact (mul_pos (mul_pos (by norm_num : (0:ℝ)<4) (criticalAliasCoefficient_positive hW))
    (criticalState_exponentialMass_pos hW hF)).ne' he

#print axioms criticalState_tendsto_bare_increment_div
#print axioms criticalState_criticalLine_cosine_cusp
#print axioms criticalState_criticalLine_firstMoment_not_summable

end GaloisForLFunctions.ExclusionOfTheCriticalState
