import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExponentialProbesLieInTheEnergyDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergy

/-!
# Coercivity after cancelling one polar charge

The growing polar charge is the Laplace value at `1/2`. Its confinement
representer is the probe of exponent `17/2`, giving the sharp inequality
`9 charge(G)^2 ≤ ∫ G² exp(-8u)` by an exact square decomposition.

Subtracting the charge ratio times a critical state cancels this charge
without changing full energy. The existing transverse spectral gap then
gives coercivity on the charge-zero subspace, where the entire quadratic
pole term vanishes. Adding the square of this single charge makes the
full form coercive on the whole actual domain.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry

/-- The coefficient of the growing half-exponential in the polar kernel. -/
def growingPolarCharge (G : ℝ → ℝ) : ℝ := ∫ u, G u * Real.exp ((1 / 2 : ℝ) * u)

theorem growingPolarCharge_eq_moments {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    growingPolarCharge G = coshHalfMoment G + sinhHalfMoment G := by
  have h := (negativeHalfLineLaplace_halfPole_real hG.weighted).1
  rw [negativeHalfLineLaplace_ofReal] at h
  exact Complex.ofReal_inj.mp h

theorem growingPolarCharge_add_const_mul {G H : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hH : CriticalHalfLineEnergyDomain H) (c : ℝ) :
    growingPolarCharge (fun u => G u + c * H u) =
      growingPolarCharge G + c * growingPolarCharge H := by
  have hiG := integrable_halfLineLaplace_of_domain hG (s := 1 / 2) (by norm_num)
  have hiH := integrable_halfLineLaplace_of_domain hH (s := 1 / 2) (by norm_num)
  unfold growingPolarCharge
  simp_rw [add_mul, mul_assoc]
  rw [integral_add hiG (hiH.const_mul c), integral_const_mul]

theorem growingPolarCharge_criticalState_ne_zero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    growingPolarCharge F ≠ 0 := by
  exact criticalHalfLineGroundState_laplace_ne_zero hW ht hF (s := 1 / 2) (by norm_num)

/-- The charge representer has confinement mass and charge both equal to `1/9`. -/
theorem growingPolarCharge_probe : growingPolarCharge (probe (17 / 2)) = 1 / 9 := by
  unfold growingPolarCharge
  rw [integral_probe_mul_exp (by norm_num : (0 : ℝ) < 17 / 2 + 1 / 2)]
  norm_num

theorem exponentialPair_charge_probe {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineExponentialPair G (probe (17 / 2)) = growingPolarCharge G := by
  apply integral_congr_ae
  refine Eventually.of_forall fun u => ?_
  change G u * probe (17 / 2) u * Real.exp (-(8 * u)) =
    G u * Real.exp ((1 / 2 : ℝ) * u)
  rcases lt_or_ge u 0 with hu | hu
  · rw [probe_of_neg hu, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · simp only [hG.support u hu, zero_mul]

theorem confinementMass_charge_probe :
    (∫ u, probe (17 / 2) u ^ 2 * Real.exp (-(8 * u))) = 1 / 9 := by
  rw [← criticalHalfLineExponentialPair_self,
    exponentialPair_charge_probe (criticalHalfLineEnergyDomain_probe (by norm_num)),
    growingPolarCharge_probe]

/-- The confinement-orthogonal charge projection gives an exact square decomposition. -/
theorem confinementMass_charge_decomposition {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, (G u - 9 * growingPolarCharge G * probe (17 / 2) u) ^ 2 *
      Real.exp (-(8 * u))) + 9 * growingPolarCharge G ^ 2 =
        ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
  have h := criticalHalfLine_exponential_mass_add_const_mul hG
    (criticalHalfLineEnergyDomain_probe (by norm_num : (4 : ℝ) < 17 / 2))
    (-(9 * growingPolarCharge G))
  rw [exponentialPair_charge_probe hG, confinementMass_charge_probe] at h
  simp only [neg_mul, ← sub_eq_add_neg] at h
  nlinarith only [h]

/-- The constant nine is attained by the charge representer. -/
theorem growingPolarCharge_sq_le_confinementMass {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    9 * growingPolarCharge G ^ 2 ≤ ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
  have h := confinementMass_charge_decomposition hG
  have hp : 0 ≤ ∫ u, (G u - 9 * growingPolarCharge G * probe (17 / 2) u) ^ 2 *
      Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  linarith only [h, hp]

/-- Projection along the critical line onto the kernel of the growing polar charge. -/
def polarChargeNeutralPart (F G : ℝ → ℝ) : ℝ → ℝ :=
  fun u => G u - (growingPolarCharge G / growingPolarCharge F) * F u

theorem domain_polarChargeNeutralPart {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    CriticalHalfLineEnergyDomain (polarChargeNeutralPart F G) := by
  change CriticalHalfLineEnergyDomain (fun u => G u -
    (growingPolarCharge G / growingPolarCharge F) * F u)
  simpa only [neg_mul, sub_eq_add_neg] using
    hG.add_const_mul hF (-(growingPolarCharge G / growingPolarCharge F))

theorem growingPolarCharge_polarChargeNeutralPart {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hn : growingPolarCharge F ≠ 0) :
    growingPolarCharge (polarChargeNeutralPart F G) = 0 := by
  have h := growingPolarCharge_add_const_mul hG hF
    (-(growingPolarCharge G / growingPolarCharge F))
  simp only [neg_mul, ← sub_eq_add_neg] at h
  change growingPolarCharge (fun u => G u -
    (growingPolarCharge G / growingPolarCharge F) * F u) = 0
  rw [h, div_mul_cancel₀ _ hn, sub_self]

/-- Cancelling the charge by a critical-state multiple costs no full energy. -/
theorem fullEnergy_polarChargeNeutralPart {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F G : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineFullEnergy W₀ (polarChargeNeutralPart F G) =
      criticalHalfLineFullEnergy W₀ G := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalHalfLineFullEnergy_add_const_mul W₀ hG hdF
    (-(growingPolarCharge G / growingPolarCharge F))
  rw [criticalHalfLineMixedEnergy_symm W₀ hG hdF,
    criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hG,
    criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF,
    mul_zero, mul_zero, add_zero, add_zero] at h
  change criticalHalfLineFullEnergy W₀ (fun u => G u -
    (growingPolarCharge G / growingPolarCharge F) * F u) = criticalHalfLineFullEnergy W₀ G
  simpa only [neg_mul, sub_eq_add_neg] using h

/-- Vanishing of one charge removes the entire quadratic pole form. -/
theorem fullEnergy_of_growingPolarCharge_zero (R : ℝ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hz : growingPolarCharge G = 0) :
    criticalHalfLineFullEnergy R G = archForm G - primeSum G +
      criticalAliasCoefficient R * (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) := by
  rw [growingPolarCharge_eq_moments hG] at hz
  have hc : coshHalfMoment G = -sinhHalfMoment G := by linarith only [hz]
  unfold criticalHalfLineFullEnergy
  rw [hc]
  ring

/-- Every full energy has an equal pole-free representative on the charge-zero subspace. -/
theorem fullEnergy_eq_chargeNeutral_poleFreeForm {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F G : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineFullEnergy W₀ G =
      archForm (polarChargeNeutralPart F G) - primeSum (polarChargeNeutralPart F G) +
        criticalAliasCoefficient W₀ * (∫ u in Iio 0,
          polarChargeNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  rw [← fullEnergy_polarChargeNeutralPart hW ht hF hG]
  exact fullEnergy_of_growingPolarCharge_zero W₀ (domain_polarChargeNeutralPart hdF hG)
    (growingPolarCharge_polarChargeNeutralPart hdF hG
      (growingPolarCharge_criticalState_ne_zero hW ht hF))

private theorem charge_ordinary_neutralPart {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    growingPolarCharge (criticalHalfLineNeutralPart F G) = growingPolarCharge G -
      (∫ u, F u * G u) * growingPolarCharge F := by
  change growingPolarCharge (fun u => G u - (∫ v, F v * G v) * F u) = _
  simpa only [neg_mul, sub_eq_add_neg] using
    growingPolarCharge_add_const_mul hG hF (-(∫ u, F u * G u))

/-- The transverse gap survives replacing ordinary orthogonality by charge cancellation. -/
theorem criticalState_charge_zero_coercivity {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      growingPolarCharge G = 0 →
      γ * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤ criticalHalfLineFullEnergy W₀ G := by
  obtain ⟨δ, hδ, hgap⟩ := criticalHalfLineFullEnergy_controls_neutralPart hW ht hF
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hq : 0 < growingPolarCharge F ^ 2 := by
    have hn := growingPolarCharge_criticalState_ne_zero hW ht hF
    positivity
  have hM : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  let K := 18 * growingPolarCharge F ^ 2 + 2 * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨δ * (9 * growingPolarCharge F ^ 2) / K, by positivity, ?_⟩
  intro G hG hz
  have hN := hdF.neutralPart hG
  have hc := growingPolarCharge_sq_le_confinementMass hN
  rw [charge_ordinary_neutralPart hdF hG, hz, zero_sub] at hc
  have hm := criticalHalfLine_exponential_mass_add_const_mul_le hN hdF (∫ u, F u * G u)
  have he (u : ℝ) : criticalHalfLineNeutralPart F G u + (∫ v, F v * G v) * F u = G u := by
    dsimp only [criticalHalfLineNeutralPart]
    ring
  simp_rw [he] at hm
  have hd := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 9 * growingPolarCharge F ^ 2)
  have hp := mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
  have hb : 9 * growingPolarCharge F ^ 2 * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
      K * (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) := by
    dsimp only [K]
    nlinarith only [hd, hp]
  have hs := mul_le_mul_of_nonneg_left hb hδ.le
  have hg := mul_le_mul_of_nonneg_left (hgap hG) hK.le
  calc
    _ = (δ * (9 * growingPolarCharge F ^ 2 *
        (∫ u, G u ^ 2 * Real.exp (-(8 * u))))) / K := by ring
    _ ≤ _ := (div_le_iff₀ hK).mpr (by nlinarith only [hs, hg])

/-- Full energy controls the charge-neutral representative in the confinement norm. -/
theorem criticalState_energy_controls_chargeNeutralPart {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      γ * (∫ u, polarChargeNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) ≤
        criticalHalfLineFullEnergy W₀ G := by
  obtain ⟨γ, hγ, hg⟩ := criticalState_charge_zero_coercivity hW ht hF
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  refine ⟨γ, hγ, ?_⟩
  intro G hG
  have h := hg (domain_polarChargeNeutralPart hdF hG)
    (growingPolarCharge_polarChargeNeutralPart hdF hG
      (growingPolarCharge_criticalState_ne_zero hW ht hF))
  rwa [fullEnergy_polarChargeNeutralPart hW ht hF hG] at h

/-- A single charge square repairs the sole zero-energy direction. -/
theorem criticalState_one_charge_coercivity {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ η : ℝ, 0 < η ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      η * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
        criticalHalfLineFullEnergy W₀ G + growingPolarCharge G ^ 2 := by
  obtain ⟨γ, hγ, hgap⟩ := criticalState_energy_controls_chargeNeutralPart hW ht hF
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hq := growingPolarCharge_criticalState_ne_zero hW ht hF
  have hM : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  let C := γ * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) / growingPolarCharge F ^ 2
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hγ.le hM) (sq_nonneg _)
  refine ⟨(γ / 2) / (1 + C), by positivity, ?_⟩
  intro G hG
  have hm := criticalHalfLine_exponential_mass_add_const_mul_le
    (domain_polarChargeNeutralPart hdF hG) hdF (growingPolarCharge G / growingPolarCharge F)
  have he (u : ℝ) : polarChargeNeutralPart F G u +
      (growingPolarCharge G / growingPolarCharge F) * F u = G u := by
    dsimp only [polarChargeNeutralPart]
    ring
  simp_rw [he] at hm
  have hs := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ γ / 2)
  have hc : γ / 2 * (2 * (∫ u, polarChargeNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) +
      2 * (growingPolarCharge G / growingPolarCharge F) ^ 2 *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) =
      γ * (∫ u, polarChargeNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) +
        C * growingPolarCharge G ^ 2 := by
    dsimp only [C]
    field_simp [hq]
    <;> ring
  rw [hc] at hs
  have hb : γ / 2 * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
      criticalHalfLineFullEnergy W₀ G + C * growingPolarCharge G ^ 2 :=
    hs.trans (add_le_add (hgap hG) le_rfl)
  have hQ := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW ht hG
  have hCQ := mul_nonneg hC hQ
  calc
    _ = (γ / 2 * (∫ u, G u ^ 2 * Real.exp (-(8 * u)))) / (1 + C) := by ring
    _ ≤ _ := (div_le_iff₀ (by positivity : 0 < 1 + C)).mpr
      (by nlinarith only [hb, hCQ, sq_nonneg (growingPolarCharge G)])

/-- The unconditional alternative includes coercivity after pinning one polar charge. -/
theorem riemannHypothesis_or_one_polar_charge_coercivity :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ) (η : ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ 0 < η ∧
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        η * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
          criticalHalfLineFullEnergy W₀ G + growingPolarCharge G ^ 2 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · obtain ⟨η, hη, h⟩ := criticalState_one_charge_coercivity hW ht hF
    exact Or.inr ⟨W₀, F, η, hW, ht, hF, hη, fun G hG => h hG⟩

#print axioms fullEnergy_eq_chargeNeutral_poleFreeForm
#print axioms riemannHypothesis_or_one_polar_charge_coercivity

end GaloisForLFunctions.ExclusionOfTheCriticalState
