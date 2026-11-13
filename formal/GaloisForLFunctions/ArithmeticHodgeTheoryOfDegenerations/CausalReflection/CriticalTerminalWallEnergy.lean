import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergyTranslation

/-!
# Exact ground-energy curve for a displaced terminal wall

Translation turns the wall energy deficit into the full critical energy.
Its nullspace is the actual critical-state line, so the sharp exponential
energy floor has precisely the translated critical states as extremizers.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

theorem criticalHalfLineExponentialPair_congr_ae {F G H K : ℝ → ℝ}
    (hFH : F =ᵐ[volume] H) (hGK : G =ᵐ[volume] K) :
    criticalHalfLineExponentialPair F G = criticalHalfLineExponentialPair H K := by
  apply integral_congr_ae
  filter_upwards [hFH, hGK] with u hu hv
  change F u * G u * Real.exp (-(8 * u)) = H u * K u * Real.exp (-(8 * u))
  rw [hu, hv]

theorem criticalHalfLineExponentialPair_const_mul_self (F : ℝ → ℝ) (c : ℝ) :
    criticalHalfLineExponentialPair (fun u => c * F u) (fun u => c * F u) =
      c ^ 2 * criticalHalfLineExponentialPair F F := by
  unfold criticalHalfLineExponentialPair
  calc
    _ = ∫ u, c ^ 2 * (F u * F u * Real.exp (-(8 * u))) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by ring
    _ = _ := integral_const_mul _ _

/-- Strict positivity of the exponential weight detects exactly the zero profile. -/
theorem criticalHalfLineExponentialPair_self_eq_zero_iff {H : ℝ → ℝ}
    (hH : CriticalHalfLineEnergyDomain H) :
    criticalHalfLineExponentialPair H H = 0 ↔ H =ᵐ[volume] fun _ => 0 := by
  rw [criticalHalfLineExponentialPair_self]
  constructor
  · intro hz
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun u => mul_nonneg (sq_nonneg (H u)) (Real.exp_nonneg _))
      hH.exponential).mp hz
    filter_upwards [hae] with u hu
    have hsq : H u ^ 2 = 0 := (mul_eq_zero.mp hu).resolve_right (Real.exp_ne_zero _)
    nlinarith only [hsq]
  · intro hae
    have hz : (fun u => H u ^ 2 * Real.exp (-(8 * u))) =ᵐ[volume] fun _ => (0 : ℝ) := by
      filter_upwards [hae] with u hu
      rw [hu, zero_pow (by decide : 2 ≠ 0), zero_mul]
    rw [integral_congr_ae hz, integral_zero]

/-- A nonzero profile behind a strictly displaced wall has strictly positive critical energy. -/
theorem criticalHalfLineFullEnergy_pos_of_terminal_wall
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H)
    {h : ℝ} (hh : 0 < h) (hgap : ∀ u, -h ≤ u → H u = 0)
    (hHne : ¬ H =ᵐ[volume] fun _ => 0) :
    0 < criticalHalfLineFullEnergy W₀ H := by
  have hmass : 0 < criticalHalfLineExponentialPair H H := by
    have hn : 0 ≤ criticalHalfLineExponentialPair H H := by
      rw [criticalHalfLineExponentialPair_self]
      exact integral_nonneg fun u => mul_nonneg (sq_nonneg (H u)) (Real.exp_nonneg _)
    exact lt_of_le_of_ne hn (fun he => hHne
      ((criticalHalfLineExponentialPair_self_eq_zero_iff hH).mp he.symm))
  have hexp : Real.exp (-(8 * h)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith only [hh])
  exact (mul_pos (mul_pos (criticalAliasCoefficient_positive hW)
    (sub_pos.mpr hexp)) hmass).trans_le
      (criticalHalfLineFullEnergy_ge_terminal_wall hW hthreshold hH hh.le hgap)

/-- The wall deficit is exactly the energy of the profile translated back to the endpoint. -/
theorem criticalHalfLineFullEnergy_terminal_wall_deficit
    (R : ℝ) {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H)
    (h : ℝ) (hgap : ∀ u, -h ≤ u → H u = 0) :
    criticalHalfLineFullEnergy R H - criticalAliasCoefficient R *
      (1 - Real.exp (-(8 * h))) * criticalHalfLineExponentialPair H H =
        criticalHalfLineFullEnergy R (fun u => H (u + (-h))) := by
  have he := criticalHalfLineFullEnergy_comp_add_right hH (-h) R
    (fun u hu => hgap _ (by linarith only [hu]))
  rw [← criticalHalfLineExponentialPair_self, mul_neg] at he
  rw [he]
  ring

/-- Equality in the wall bound characterizes the entire translated ground-state line. -/
theorem criticalHalfLineFullEnergy_terminal_wall_eq_iff
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H)
    {h : ℝ} (hh : 0 ≤ h) (hgap : ∀ u, -h ≤ u → H u = 0) :
    criticalHalfLineFullEnergy W₀ H = criticalAliasCoefficient W₀ *
      (1 - Real.exp (-(8 * h))) * criticalHalfLineExponentialPair H H ↔
        ∃ c : ℝ, H =ᵐ[volume] fun u => c * F (u + h) := by
  constructor
  · intro he
    let G : ℝ → ℝ := fun u => H (u + (-h))
    have hdG : CriticalHalfLineEnergyDomain G :=
      hH.comp_add_right (-h) (fun u hu => hgap _ (by linarith only [hu]))
    have heG : criticalHalfLineFullEnergy W₀ G = 0 := by
      rw [← criticalHalfLineFullEnergy_terminal_wall_deficit W₀ hH h hgap, he, sub_self]
    have hae := criticalHalfLineFullEnergy_zero_eq_laplace_ratio_ae hW hthreshold hF hdG heG
    refine ⟨(∫ v, G v * Real.exp v) / (∫ v, F v * Real.exp v), ?_⟩
    have hat := hae.comp_tendsto
      (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
    filter_upwards [hat] with u hu
    change H ((u + h) + (-h)) = _ at hu
    simpa only [add_neg_cancel_right, Function.comp_apply] using hu
  · rintro ⟨c, hae⟩
    have hdT := (criticalHalfLineEnergyDomain_of_groundState hF).causalTranslate hh
    rw [criticalHalfLineFullEnergy_congr_ae hH (hdT.const_mul c) hae W₀,
      criticalHalfLineExponentialPair_congr_ae hae hae,
      criticalHalfLineFullEnergy_const_mul, criticalHalfLineExponentialPair_const_mul_self,
      criticalHalfLineGroundState_attains_terminal_wall hW hthreshold hF hh]
    ring

/-- The translated state has strictly positive exponential mass at every wall position. -/
theorem criticalHalfLineGroundState_translated_exponential_mass_pos
    {W₀ : ℝ} {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (h : ℝ) :
    0 < criticalHalfLineExponentialPair (fun u => F (u + h)) (fun u => F (u + h)) := by
  rw [criticalHalfLineExponentialPair_comp_add_right, criticalHalfLineExponentialPair_self]
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one
    (one_le_exponential_square_of_domain (criticalHalfLineEnergyDomain_of_groundState hF)
      hF.2.2.2.1))

/-- Failure of RH supplies an exact wall-energy curve with its full extremizer line. -/
theorem riemannHypothesis_or_exists_sharp_terminal_wall_groundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ),
      0 < W₀ ∧ (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ h : ℝ, 0 ≤ h →
      (0 < criticalHalfLineExponentialPair (fun u => F (u + h)) (fun u => F (u + h))) ∧
      (criticalHalfLineFullEnergy W₀ (fun u => F (u + h)) =
        criticalAliasCoefficient W₀ * (1 - Real.exp (-(8 * h))) *
          criticalHalfLineExponentialPair (fun u => F (u + h)) (fun u => F (u + h))) ∧
      ∀ H : ℝ → ℝ, CriticalHalfLineEnergyDomain H → (∀ u, -h ≤ u → H u = 0) →
        (criticalAliasCoefficient W₀ * (1 - Real.exp (-(8 * h))) *
          criticalHalfLineExponentialPair H H ≤ criticalHalfLineFullEnergy W₀ H) ∧
        (criticalHalfLineFullEnergy W₀ H = criticalAliasCoefficient W₀ *
          (1 - Real.exp (-(8 * h))) * criticalHalfLineExponentialPair H H ↔
            ∃ c : ℝ, H =ᵐ[volume] fun u => c * F (u + h)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨W₀, F, hW, ht, hF, ?_⟩
    intro h hh
    refine ⟨criticalHalfLineGroundState_translated_exponential_mass_pos hF h,
      criticalHalfLineGroundState_attains_terminal_wall hW ht hF hh, ?_⟩
    intro H hH hgap
    exact ⟨criticalHalfLineFullEnergy_ge_terminal_wall hW ht hH hh hgap,
      criticalHalfLineFullEnergy_terminal_wall_eq_iff hW ht hF hH hh hgap⟩

#print axioms criticalHalfLineFullEnergy_terminal_wall_deficit
#print axioms riemannHypothesis_or_exists_sharp_terminal_wall_groundState

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
