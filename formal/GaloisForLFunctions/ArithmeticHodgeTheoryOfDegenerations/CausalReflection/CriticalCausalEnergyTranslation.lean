import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoTerminalSupportGap
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateIsUniqueUpToSign

/-!
# Translation covariance of the critical half-line energy

The weak ground-state equation removes the mixed term with the critical
state. Causal translation then contributes exactly the exponential mass
defect. Moving a terminal wall produces a sharp weighted energy floor.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

/-- The real bilinear pairing associated with the eighth exponential mass. -/
def criticalHalfLineExponentialPair (F G : ℝ → ℝ) : ℝ :=
  ∫ u, F u * G u * Real.exp (-(8 * u))

theorem criticalHalfLineExponentialPair_self (F : ℝ → ℝ) :
    criticalHalfLineExponentialPair F F = ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  simp only [criticalHalfLineExponentialPair, pow_two]

theorem criticalHalfLineExponentialPair_symm (F G : ℝ → ℝ) :
    criticalHalfLineExponentialPair F G = criticalHalfLineExponentialPair G F := by
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    change F u * G u * Real.exp (-(8 * u)) = G u * F u * Real.exp (-(8 * u))
    ring

/-- The exponential pairing scales by the common translation. -/
theorem criticalHalfLineExponentialPair_comp_add_right (F G : ℝ → ℝ) (c : ℝ) :
    criticalHalfLineExponentialPair (fun u => F (u + c)) (fun u => G (u + c)) =
      Real.exp (8 * c) * criticalHalfLineExponentialPair F G := by
  unfold criticalHalfLineExponentialPair
  calc
    _ = ∫ u, Real.exp (8 * c) *
        (F (u + c) * G (u + c) * Real.exp (-(8 * (u + c)))) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun u => ?_
      have he : Real.exp (8 * c) * Real.exp (-(8 * (u + c))) = Real.exp (-(8 * u)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change F (u + c) * G (u + c) * Real.exp (-(8 * u)) = _
      rw [← he]
      ring
    _ = Real.exp (8 * c) *
        ∫ u, F (u + c) * G (u + c) * Real.exp (-(8 * (u + c))) := integral_const_mul _ _
    _ = _ := by
      rw [integral_add_right_eq_self
        (fun u => F u * G u * Real.exp (-(8 * u))) c]

/-- Polarization proves integrability without introducing another weighted domain. -/
theorem CriticalHalfLineEnergyDomain.integrable_exponentialCross {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    Integrable (fun u => F u * G u * Real.exp (-(8 * u))) := by
  have hs : Integrable (fun u => (F u + G u) ^ 2 * Real.exp (-(8 * u))) := by
    simpa only [one_mul] using (hF.add_const_mul hG 1).exponential
  apply (((hs.sub hF.exponential).sub hG.exponential).const_mul (1 / 2 : ℝ)).congr
  exact Eventually.of_forall fun u => by
    change (1 / 2 : ℝ) * (((F u + G u) ^ 2 * Real.exp (-(8 * u)) -
      F u ^ 2 * Real.exp (-(8 * u))) - G u ^ 2 * Real.exp (-(8 * u))) = _
    ring

/-- The full mixed form is symmetric on its actual domain. -/
theorem criticalHalfLineMixedEnergy_symm (R : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineMixedEnergy R F G = criticalHalfLineMixedEnergy R G F := by
  have hfg := criticalHalfLineFullEnergy_add_const_mul R hF hG 1
  have hgf := criticalHalfLineFullEnergy_add_const_mul R hG hF 1
  simp only [one_mul, one_pow, mul_one] at hfg hgf
  have he : (fun u => G u + F u) = (fun u => F u + G u) := funext fun _ => add_comm _ _
  rw [he] at hgf
  linarith only [hfg, hgf]

/-- Moving a negative-support profile further left preserves the actual domain. -/
theorem CriticalHalfLineEnergyDomain.causalTranslate {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {h : ℝ} (hh : 0 ≤ h) :
    CriticalHalfLineEnergyDomain (fun u => F (u + h)) :=
  hF.comp_add_right h (fun _ hu => hF.support _ (add_nonneg hu hh))

/-- Adding any ground-state multiple to a causal translate changes no mixed energy. -/
theorem criticalHalfLineFullEnergy_causal_ground_shear
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {h : ℝ} (hh : 0 ≤ h) (c : ℝ) :
    criticalHalfLineFullEnergy W₀ (fun u => G (u + h) + c * F u) =
      criticalHalfLineFullEnergy W₀ G + criticalAliasCoefficient W₀ *
        (Real.exp (8 * h) - 1) * criticalHalfLineExponentialPair G G := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hdT := hG.causalTranslate hh
  rw [criticalHalfLineFullEnergy_add_const_mul W₀ hdT hdF,
    criticalHalfLineMixedEnergy_symm W₀ hdT hdF,
    criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hdT,
    criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF,
    criticalHalfLineFullEnergy_comp_add_right hG h W₀
      (fun u hu => hG.support _ (add_nonneg hu hh)),
    criticalHalfLineExponentialPair_self]
  ring

/-- A terminal wall gives an explicit lower bound in the exponential norm. -/
theorem criticalHalfLineFullEnergy_ge_terminal_wall
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H)
    {h : ℝ} (hh : 0 ≤ h) (hgap : ∀ u, -h ≤ u → H u = 0) :
    criticalAliasCoefficient W₀ * (1 - Real.exp (-(8 * h))) *
      criticalHalfLineExponentialPair H H ≤ criticalHalfLineFullEnergy W₀ H := by
  let G : ℝ → ℝ := fun u => H (u + (-h))
  have hdG : CriticalHalfLineEnergyDomain G :=
    hH.comp_add_right (-h) (fun u hu => hgap _ (by linarith only [hu]))
  have hback : (fun u => G (u + h)) = H := by
    funext u
    dsimp only [G]
    congr 1
    ring
  have he := criticalHalfLineFullEnergy_comp_add_right hdG h W₀
    (fun u hu => hdG.support _ (add_nonneg hu hh))
  rw [hback, ← criticalHalfLineExponentialPair_self] at he
  have hm := criticalHalfLineExponentialPair_comp_add_right G G h
  rw [hback] at hm
  have hpos := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold hdG
  have hcoef : (1 - Real.exp (-(8 * h))) * Real.exp (8 * h) = Real.exp (8 * h) - 1 := by
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = criticalAliasCoefficient W₀ * (Real.exp (8 * h) - 1) *
        criticalHalfLineExponentialPair G G := by
      rw [hm]
      calc
        _ = criticalAliasCoefficient W₀ *
            ((1 - Real.exp (-(8 * h))) * Real.exp (8 * h)) *
            criticalHalfLineExponentialPair G G := by ring
        _ = _ := by rw [hcoef]
    _ ≤ criticalHalfLineFullEnergy W₀ G + criticalAliasCoefficient W₀ *
        (Real.exp (8 * h) - 1) * criticalHalfLineExponentialPair G G :=
      le_add_of_nonneg_left hpos
    _ = _ := he.symm

/-- Every zero-energy profile lies on the actual critical-state line. -/
theorem criticalHalfLineFullEnergy_zero_eq_laplace_ratio_ae
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (heG : criticalHalfLineFullEnergy W₀ G = 0) :
    G =ᵐ[volume] fun u =>
      ((∫ v, G v * Real.exp v) / (∫ v, F v * Real.exp v)) * F u := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  let c : ℝ := (∫ v, G v * Real.exp v) / (∫ v, F v * Real.exp v)
  have hd := hG.add_const_mul hdF (-c)
  have he : criticalHalfLineFullEnergy W₀ (fun u => G u + (-c) * F u) = 0 := by
    rw [criticalHalfLineFullEnergy_add_const_mul W₀ hG hdF,
      criticalHalfLineMixedEnergy_symm W₀ hG hdF,
      criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hG,
      heG, criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF]
    ring
  have hLF : (∫ u, F u * Real.exp u) ≠ 0 := by
    simpa only [one_mul] using
      criticalHalfLineGroundState_laplace_ne_zero hW hthreshold hF (s := 1) zero_lt_one
  have hiF : Integrable (fun u => F u * Real.exp u) := by
    simpa only [one_mul] using integrable_halfLineLaplace_of_domain hdF (s := 1) zero_le_one
  have hiG : Integrable (fun u => G u * Real.exp u) := by
    simpa only [one_mul] using integrable_halfLineLaplace_of_domain hG (s := 1) zero_le_one
  have hz : (∫ u, (G u + (-c) * F u) * Real.exp u) = 0 := by
    simp_rw [add_mul, mul_assoc]
    rw [integral_add hiG (hiF.const_mul (-c)), integral_const_mul]
    dsimp only [c]
    field_simp [hLF]
    ring
  have hz' : (∫ u, (G u + (-c) * F u) * Real.exp (1 * u)) = 0 := by
    simpa only [one_mul] using hz
  have hh := ae_eq_zero_of_criticalHalfLineFullEnergy_eq_zero_of_laplace_zero
    hW hthreshold hd he zero_lt_one hz'
  filter_upwards [hh] with u hu
  change G u + (-c) * F u = 0 at hu
  change G u = c * F u
  linarith only [hu]

/-- A translated actual critical state attains the terminal-wall energy floor. -/
theorem criticalHalfLineGroundState_attains_terminal_wall
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {h : ℝ} (hh : 0 ≤ h) :
    criticalHalfLineFullEnergy W₀ (fun u => F (u + h)) =
      criticalAliasCoefficient W₀ * (1 - Real.exp (-(8 * h))) *
        criticalHalfLineExponentialPair (fun u => F (u + h)) (fun u => F (u + h)) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  rw [criticalHalfLineFullEnergy_comp_add_right hdF h W₀
      (fun u hu => hdF.support _ (add_nonneg hu hh)),
    criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF, zero_add,
    criticalHalfLineExponentialPair_comp_add_right, criticalHalfLineExponentialPair_self]
  have hcoef : (1 - Real.exp (-(8 * h))) * Real.exp (8 * h) = Real.exp (8 * h) - 1 := by
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = criticalAliasCoefficient W₀ *
        ((1 - Real.exp (-(8 * h))) * Real.exp (8 * h)) *
          ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by rw [hcoef]
    _ = _ := by ring

#print axioms criticalHalfLineFullEnergy_causal_ground_shear
#print axioms criticalHalfLineFullEnergy_ge_terminal_wall
#print axioms criticalHalfLineFullEnergy_zero_eq_laplace_ratio_ae
#print axioms criticalHalfLineGroundState_attains_terminal_wall

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
