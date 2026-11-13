import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyBranch
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionHasPositiveEnergyDefect

/-!
# Rigidity at every positive confinement

Causal reflection preserves ordinary mass. Subtracting the variational
floor therefore preserves its strict energy defect. A Laplace zero kills
an attaining profile, and cancellation of one Laplace value gives simplicity.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open scoped Convolution
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry

/-- An attaining profile with a positive real Laplace zero must vanish. -/
theorem ae_eq_zero_of_minimizing_energy_of_laplace_zero
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (he : criticalHalfLineFullEnergy R F = criticalHalfLineGroundEnergy R * (∫ u, F u ^ 2))
    {s : ℝ} (hs : 0 < s) (hz : (∫ u, F u * Real.exp (s * u)) = 0) :
    F =ᵐ[volume] 0 := by
  let a : ℝ := s / Real.pi
  have ha : 0 < a := div_pos hs Real.pi_pos
  have hpa : Real.pi * a = s := by dsimp only [a]; field_simp [Real.pi_ne_zero]
  have hz' : (∫ u, Real.exp (Real.pi * a * u) * F u) = 0 := by
    simpa only [hpa, mul_comm] using hz
  have hH := hF.realCausalReflection ha hz'
  have hmass : (∫ u, realCausalReflection a F u ^ 2) = ∫ u, F u ^ 2 := by
    simpa only [add_zero, ← pow_two] using
      integral_mul_translate_realCausalReflection ha hF.integrable hF.sq 0
  have hfloor := criticalHalfLineGroundEnergy_mul_mass_le_all hR hH
  rw [criticalHalfLineFullEnergy_realCausalReflection ha hF hz', hmass, he] at hfloor
  have hcoef : 0 < criticalAliasCoefficient R * (16 * a / Real.pi) :=
    mul_pos (criticalAliasCoefficient_positive hR)
      (div_pos (mul_pos (by norm_num) ha) Real.pi_pos)
  have hnegprod : 0 ≤ -(criticalAliasCoefficient R * (16 * a / Real.pi) *
      (∫ u, realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u)))) := by
    linarith only [hfloor]
  have hneg : 0 ≤ -(∫ u, realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u))) :=
    (mul_nonneg_iff_of_pos_left hcoef).mp (by simpa only [mul_neg] using hnegprod)
  have hm : (∫ u, realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u))) = 0 :=
    le_antisymm (neg_nonneg.mp hneg)
      (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => mul_nonneg (sq_nonneg (realCausalConvolution a F u))
      (Real.exp_pos (-(8 * u))).le) (integrable_exponential_realCausalConvolution ha hF)).mp hm
  have hzero : realCausalConvolution a F =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    change realCausalConvolution a F u ^ 2 * Real.exp (-(8 * u)) = 0 at hu
    have hsq := (mul_eq_zero.mp hu).resolve_right (Real.exp_ne_zero _)
    change realCausalConvolution a F u = 0
    nlinarith only [hsq]
  have hczero : (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] cx F) =ᵐ[volume] 0 := by
    filter_upwards [hzero] with u hu
    have hh : (realCausalConvolution a F u : ℂ) = 0 := by exact_mod_cast hu
    exact (coe_realCausalConvolution a F u).symm.trans hh
  have hFzero := ae_eq_zero_of_causalExponentialConvolution_ae_zero ha
    (hF.integrable.ofReal (𝕜 := ℂ)) hczero
  filter_upwards [hFzero] with u hu
  change (F u : ℂ) = 0 at hu
  change F u = 0
  exact_mod_cast hu

/-- A nonreal right-half-plane zero also annihilates an attaining profile. -/
theorem ae_eq_zero_of_minimizing_energy_of_nonreal_laplace_zero
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (he : criticalHalfLineFullEnergy R F = criticalHalfLineGroundEnergy R * (∫ u, F u ^ 2))
    {a b : ℝ} (ha : 0 < a) (hb : b ≠ 0)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) :
    F =ᵐ[volume] 0 := by
  have hH := hF.realPairedCausalReflection ha hb hz
  have hmass : (∫ u, realPairedCausalReflection a b F u ^ 2) = ∫ u, F u ^ 2 := by
    simpa only [add_zero, ← pow_two] using
      integral_mul_translate_realPairedCausalReflection ha hb hF hz 0
  have hfloor := criticalHalfLineGroundEnergy_mul_mass_le_all hR hH
  rw [criticalHalfLineFullEnergy_realPairedCausalReflection ha hb hF hz, hmass, he] at hfloor
  have hcoef : 0 < criticalAliasCoefficient R * (4 * a * (4 / Real.pi)) :=
    mul_pos (criticalAliasCoefficient_positive hR)
      (mul_pos (mul_pos (by norm_num) ha) (by positivity))
  have hnegprod : 0 ≤ -(criticalAliasCoefficient R * (4 * a * (4 / Real.pi)) *
      pairedCausalResolventEnergy a b (4 / Real.pi) (cx F)) := by
    linarith only [hfloor]
  have hneg : 0 ≤ -pairedCausalResolventEnergy a b (4 / Real.pi) (cx F) :=
    (mul_nonneg_iff_of_pos_left hcoef).mp (by simpa only [mul_neg] using hnegprod)
  have hm : pairedCausalResolventEnergy a b (4 / Real.pi) (cx F) = 0 :=
    le_antisymm (neg_nonneg.mp hneg) (pairedCausalResolventEnergy_nonneg _ _ _ _)
  have hfirst : (∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
      (modulatedCausalConvolution a b (cx F)) u‖ ^ 2) = 0 := by
    have h1 : 0 ≤ ∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
        (modulatedCausalConvolution a b (cx F)) u‖ ^ 2 := integral_nonneg fun u => sq_nonneg _
    have h2 : 0 ≤ ∫ u, ‖causalLaplaceWeighted (4 / Real.pi)
        (modulatedCausalConvolution a (-b) (modulatedCausalReflection a b (cx F))) u‖ ^ 2 :=
      integral_nonneg fun u => sq_nonneg _
    unfold pairedCausalResolventEnergy at hm
    linarith only [h1, h2, hm]
  have hK := memLp_weighted_modulatedCausalConvolution (add_pos ha (by positivity)) b
    hF.memLp_weightedComplex
  have hKi := (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mp hK
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => sq_nonneg
      ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution a b (cx F)) u‖) hKi).mp hfirst
  have hzero : modulatedCausalConvolution a b (cx F) =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    change ‖causalLaplaceWeighted (4 / Real.pi)
      (modulatedCausalConvolution a b (cx F)) u‖ ^ 2 = 0 at hu
    have hn : ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution a b (cx F)) u‖ = 0 := by
      nlinarith only [hu]
    have hv := norm_eq_zero.mp hn
    change Complex.exp (-(Real.pi * (4 / Real.pi) * u : ℝ)) *
      modulatedCausalConvolution a b (cx F) u = 0 at hv
    exact (mul_eq_zero.mp hv).resolve_left (Complex.exp_ne_zero _)
  have hFzero := ae_eq_zero_of_modulatedCausalConvolution_ae_zero ha b
    (hF.integrable.ofReal (𝕜 := ℂ)) hzero
  filter_upwards [hFzero] with u hu
  change (F u : ℂ) = 0 at hu
  change F u = 0
  exact_mod_cast hu

/-- Every open-right-half-plane Laplace zero annihilates an attaining profile. -/
theorem ae_eq_zero_of_minimizing_energy_of_complex_laplace_zero
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (he : criticalHalfLineFullEnergy R F = criticalHalfLineGroundEnergy R * (∫ u, F u ^ 2))
    {z : ℂ} (hzpos : 0 < z.re) (hz : negativeHalfLineLaplace (cx F) z = 0) :
    F =ᵐ[volume] 0 := by
  by_cases him : z.im = 0
  · have heq : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using him
    rw [heq, negativeHalfLineLaplace_ofReal] at hz
    exact ae_eq_zero_of_minimizing_energy_of_laplace_zero hR hF he hzpos
      (Complex.ofReal_eq_zero.mp hz)
  · have ha : 0 < z.re / Real.pi := div_pos hzpos Real.pi_pos
    have hb : z.im / (2 * Real.pi) ≠ 0 :=
      div_ne_zero him (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    have heq : modulatedLaplaceRate (z.re / Real.pi) (z.im / (2 * Real.pi)) = z := by
      have hr : Real.pi * (z.re / Real.pi) = z.re := by field_simp [Real.pi_ne_zero]
      have hi : 2 * Real.pi * (z.im / (2 * Real.pi)) = z.im := by field_simp [Real.pi_ne_zero]
      unfold modulatedLaplaceRate
      rw [hr, hi]
      apply Complex.ext <;> simp
    apply ae_eq_zero_of_minimizing_energy_of_nonreal_laplace_zero hR hF he ha hb
    rw [heq]
    exact hz

private theorem square_mass_eq_zero_of_ae_zero {F : ℝ → ℝ} (hF : F =ᵐ[volume] 0) :
    (∫ u, F u ^ 2) = 0 := by
  calc
    _ = ∫ _u : ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [hF] with u hu
      change F u = 0 at hu
      simp only [hu, zero_pow two_ne_zero]
    _ = 0 := by simp

/-- Every normalized confining minimizer has a zero-free open-right-half-plane Laplace transform. -/
theorem IsHalfLineEnergyMinimizer.complexLaplace_ne_zero
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    {z : ℂ} (hzpos : 0 < z.re) : negativeHalfLineLaplace (cx F) z ≠ 0 := by
  intro hz
  have he : criticalHalfLineFullEnergy R F = criticalHalfLineGroundEnergy R * (∫ u, F u ^ 2) := by
    rw [hF.2.1, mul_one]
    exact hF.2.2
  have hm := square_mass_eq_zero_of_ae_zero
    (ae_eq_zero_of_minimizing_energy_of_complex_laplace_zero hR hF.1 he hzpos hz)
  rw [hF.2.1] at hm
  norm_num at hm

theorem IsHalfLineEnergyMinimizer.laplace_ne_zero
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F)
    {s : ℝ} (hs : 0 < s) : (∫ u, F u * Real.exp (s * u)) ≠ 0 := by
  intro hz
  apply IsHalfLineEnergyMinimizer.complexLaplace_ne_zero hR hF (z := (s : ℂ)) hs
  rw [negativeHalfLineLaplace_ofReal, hz, Complex.ofReal_zero]

/-- One positive Laplace value fixes the scalar between any two confining minimizers. -/
theorem halfLineEnergyMinimizer_eq_laplace_ratio_ae
    {R : ℝ} (hR : 0 < R) {F G : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) (hG : IsHalfLineEnergyMinimizer R G)
    {s : ℝ} (hs : 0 < s) :
    F =ᵐ[volume] fun u =>
      ((∫ v, F v * Real.exp (s * v)) / (∫ v, G v * Real.exp (s * v))) * G u := by
  let c : ℝ := -((∫ v, F v * Real.exp (s * v)) / (∫ v, G v * Real.exp (s * v)))
  have hD := hF.1.add_const_mul hG.1 c
  have heF : criticalHalfLineFullEnergy R F = criticalHalfLineGroundEnergy R * (∫ u, F u ^ 2) := by
    rw [hF.2.1, mul_one]
    exact hF.2.2
  have heG : criticalHalfLineFullEnergy R G = criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) := by
    rw [hG.2.1, mul_one]
    exact hG.2.2
  have he := criticalHalfLine_minimizing_add_const_mul hR hF.1 hG.1 heF heG c
  have hLG := IsHalfLineEnergyMinimizer.laplace_ne_zero hR hG hs
  have hz : (∫ u, (F u + c * G u) * Real.exp (s * u)) = 0 := by
    simp_rw [add_mul, mul_assoc]
    rw [integral_add (integrable_halfLineLaplace_of_domain hF.1 hs.le)
      ((integrable_halfLineLaplace_of_domain hG.1 hs.le).const_mul c), integral_const_mul]
    dsimp only [c]
    field_simp [hLG]
    ring
  have hzero := ae_eq_zero_of_minimizing_energy_of_laplace_zero hR hD he hs hz
  filter_upwards [hzero] with u hu
  change F u + c * G u = 0 at hu
  dsimp only [c] at hu
  linarith only [hu]

/-- Positive confinement has one normalized minimizing state line, with no sign assumption. -/
theorem halfLineEnergyMinimizer_unique_up_to_sign
    {R : ℝ} (hR : 0 < R) {F G : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) (hG : IsHalfLineEnergyMinimizer R G) :
    (F =ᵐ[volume] G) ∨ (F =ᵐ[volume] fun u => -G u) := by
  let c : ℝ := (∫ v, F v * Real.exp v) / (∫ v, G v * Real.exp v)
  have hp : F =ᵐ[volume] fun u => c * G u := by
    simpa only [one_mul] using halfLineEnergyMinimizer_eq_laplace_ratio_ae hR hF hG (s := 1) zero_lt_one
  have hm : (∫ u, F u ^ 2) = c ^ 2 * (∫ u, G u ^ 2) := by
    calc
      _ = ∫ u, c ^ 2 * G u ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hp] with u hu
        rw [hu, mul_pow]
      _ = _ := integral_const_mul _ _
  rw [hF.2.1, hG.2.1, mul_one] at hm
  have hc : (c - 1) * (c + 1) = 0 := by nlinarith only [hm]
  rcases mul_eq_zero.mp hc with hc | hc
  · left
    have hc1 : c = 1 := by linarith only [hc]
    simpa only [hc1, one_mul] using hp
  · right
    have hc1 : c = -1 := by linarith only [hc]
    simpa only [hc1, neg_one_mul] using hp

/-- Every positive ratio has a unique minimizing line with zero-free right-half-plane Laplace transform. -/
theorem exists_unique_laplaceZeroFree_halfLineEnergyMinimizer :
    ∀ R : ℝ, 0 < R → ∃ F : ℝ → ℝ, IsHalfLineEnergyMinimizer R F ∧
      (∀ z : ℂ, 0 < z.re → negativeHalfLineLaplace (cx F) z ≠ 0) ∧
      ∀ G : ℝ → ℝ, IsHalfLineEnergyMinimizer R G →
        G =ᵐ[volume] F ∨ G =ᵐ[volume] (fun u => -F u) := by
  intro R hR
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  exact ⟨F, hF, fun _ hz => IsHalfLineEnergyMinimizer.complexLaplace_ne_zero hR hF hz,
    fun _ hG => halfLineEnergyMinimizer_unique_up_to_sign hR hG hF⟩

#print axioms exists_unique_laplaceZeroFree_halfLineEnergyMinimizer

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
