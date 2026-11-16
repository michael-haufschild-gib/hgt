import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaContractions

/-!
# The polar cost of removing the critical state's signs

Absolute value preserves the domain and the two square masses. It lowers
the Gamma form and raises the prime sum. Nevertheless its full critical
energy is strictly positive: a zero-energy modulus would itself be a
critical state of one sign, contradicting the sign law.

Consequently the increase in the polar term strictly exceeds both gains
combined. The positive and negative parts have equal strictly positive
energies, each one quarter of the modulus energy.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry

/-- Absolute value is admissible in the actual Gamma and confining domain. -/
theorem domain_abs {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    CriticalHalfLineEnergyDomain (fun u => |F u|) := by
  have hL : LipschitzWith 1 (abs : ℝ → ℝ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
  exact hF.comp_contraction hL abs_zero

private theorem integrable_jump_square {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    Integrable fun u => (F u - F (u + x)) ^ 2 := by
  have h := hF.memLp_real.sub
    (hF.memLp_real.comp_measurePreserving (measurePreserving_add_right volume x))
  simpa only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, sq_abs] using
    h.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

/-- Removing signs can only lower the Gamma form. -/
theorem archForm_abs_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    archForm (fun u => |F u|) ≤ archForm F := by
  have hA := domain_abs hF
  rw [hA.archForm_eq_levyEnergy, hF.archForm_eq_levyEnergy]
  simp only [sq_abs]
  apply add_le_add le_rfl
  apply integral_mono_ae hA.integrableOn_levyIntegrand hF.integrableOn_levyIntegrand
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply mul_le_mul_of_nonneg_left _ (archLevyDensity_pos hx).le
  apply integral_mono (integrable_jump_square hA x) (integrable_jump_square hF x)
  intro u
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
    (abs_abs_sub_abs_le_abs_sub (F u) (F (u + x))) 2

/-- Removing signs can only raise the complete, absolutely convergent prime sum. -/
theorem primeSum_le_abs {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    primeSum F ≤ primeSum (fun u => |F u|) := by
  have hA := (domain_abs hF).weighted
  have hW := hF.weighted
  have hshift (s : ℝ) : (∫ u, F u * F (u - s)) ≤ ∫ u, |F u| * |F (u - s)| := by
    apply integral_mono (integrable_mul_shift hW hW s) (integrable_mul_shift hA hA s)
    intro u
    simpa only [abs_mul] using le_abs_self (F u * F (u - s))
  change (∑' n, primePairTerm F F n) ≤ ∑' n, primePairTerm (fun u => |F u|) (fun u => |F u|) n
  apply Summable.tsum_le_tsum _ (summable_primePairTerm hW hW) (summable_primePairTerm hA hA)
  intro n
  have ha : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have hp := hshift (-Real.log n)
  simp only [sub_neg_eq_add] at hp
  exact mul_le_mul_of_nonneg_left (add_le_add (hshift (Real.log n)) hp) ha

/-- Gamma energy saved by removing signs. -/
def modulusGammaLoss (F : ℝ → ℝ) : ℝ := archForm F - archForm (fun u => |F u|)

/-- Prime correlation gained by removing signs. -/
def modulusPrimeGain (F : ℝ → ℝ) : ℝ := primeSum (fun u => |F u|) - primeSum F

/-- Increase in the literal two-charge polar form. -/
def modulusPoleGain (F : ℝ → ℝ) : ℝ :=
  (2 * coshHalfMoment (fun u => |F u|) ^ 2 - 2 * sinhHalfMoment (fun u => |F u|) ^ 2) -
    (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2)

/-- The confining potential cancels exactly in the modulus defect. -/
theorem fullEnergy_abs_sub (R : ℝ) (F : ℝ → ℝ) :
    criticalHalfLineFullEnergy R (fun u => |F u|) - criticalHalfLineFullEnergy R F =
      modulusPoleGain F - (modulusGammaLoss F + modulusPrimeGain F) := by
  simp only [criticalHalfLineFullEnergy, modulusPoleGain, modulusGammaLoss,
    modulusPrimeGain, sq_abs]
  ring

/-- The modulus of a critical state has strictly positive full energy. -/
theorem criticalState_modulus_energy_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < criticalHalfLineFullEnergy W₀ (fun u => |F u|) := by
  have hd := domain_abs (criticalHalfLineEnergyDomain_of_groundState hF)
  by_contra h
  have hle := le_of_not_gt h
  have hG : IsCriticalHalfLineGroundState W₀ (fun u => |F u|) := by
    refine ⟨hd.meas, hd.integrable, hd.sq, ?_, hd.exponential, hd.support, ?_⟩
    · simpa only [sq_abs] using hF.2.2.2.1
    · intro T hT
      have hg := lowGammaForm_le_archForm_of_integrable hd.gamma hT
      unfold criticalHalfLineFullEnergy at hle
      unfold truncatedWeilForm
      linarith only [hg, hle]
  apply criticalState_not_eventually_signed hW ht hG (s := 1) (Or.inl rfl) 0
  exact Eventually.of_forall fun u => by simpa only [one_mul] using abs_nonneg (F u)

/-- The polar penalty strictly outweighs both favorable changes in the other form terms. -/
theorem criticalState_modulus_balance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 ≤ modulusGammaLoss F ∧ 0 ≤ modulusPrimeGain F ∧
      modulusGammaLoss F + modulusPrimeGain F < modulusPoleGain F := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine ⟨sub_nonneg.mpr (archForm_abs_le hd), sub_nonneg.mpr (primeSum_le_abs hd), ?_⟩
  have he := fullEnergy_abs_sub W₀ F
  rw [criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF, sub_zero] at he
  have hp := criticalState_modulus_energy_pos hW ht hF
  linarith only [he, hp]

/-- Positive and negative parts each carry one quarter of the modulus energy. -/
theorem criticalState_sign_parts_energy {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    criticalHalfLineFullEnergy W₀ (fun u => max (F u) 0) =
        criticalHalfLineFullEnergy W₀ (fun u => |F u|) / 4 ∧
      criticalHalfLineFullEnergy W₀ (fun u => max (-F u) 0) =
        criticalHalfLineFullEnergy W₀ (fun u => |F u|) / 4 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hA := domain_abs hd
  have hv (c : ℝ) :
      criticalHalfLineFullEnergy W₀ (fun u => F u + c * |F u|) =
        c ^ 2 * criticalHalfLineFullEnergy W₀ (fun u => |F u|) := by
    rw [criticalHalfLineFullEnergy_add_const_mul W₀ hd hA,
      criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF,
      criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hA]
    ring
  have hp : (fun u => max (F u) 0) = (fun u => (1 / 2 : ℝ) * (F u + 1 * |F u|)) := by
    funext u
    rcases le_total 0 (F u) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  have hn : (fun u => max (-F u) 0) = (fun u => (-1 / 2 : ℝ) * (F u + -1 * |F u|)) := by
    funext u
    rcases le_total 0 (F u) with h | h
    · rw [max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    · rw [max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]; ring
  constructor
  · rw [hp, criticalHalfLineFullEnergy_const_mul, hv]
    ring
  · rw [hn, criticalHalfLineFullEnergy_const_mul, hv]
    ring

/-- Each sign part has positive energy although their signed difference has zero energy. -/
theorem criticalState_sign_parts_energy_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < criticalHalfLineFullEnergy W₀ (fun u => max (F u) 0) ∧
      0 < criticalHalfLineFullEnergy W₀ (fun u => max (-F u) 0) := by
  obtain ⟨hp, hn⟩ := criticalState_sign_parts_energy hW ht hF
  rw [hp, hn]
  have h := div_pos (criticalState_modulus_energy_pos hW ht hF) (by norm_num : (0 : ℝ) < 4)
  exact ⟨h, h⟩

/-- An unconditional alternative retaining the strict polar balance of the critical state. -/
theorem riemannHypothesis_or_criticalState_modulus_balance :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      0 ≤ modulusGammaLoss F ∧ 0 ≤ modulusPrimeGain F ∧
      modulusGammaLoss F + modulusPrimeGain F < modulusPoleGain F := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_modulus_balance hW ht hF⟩

#print axioms archForm_abs_le
#print axioms primeSum_le_abs
#print axioms criticalState_modulus_energy_pos
#print axioms criticalState_modulus_balance
#print axioms criticalState_sign_parts_energy
#print axioms criticalState_sign_parts_energy_pos
#print axioms riemannHypothesis_or_criticalState_modulus_balance

end GaloisForLFunctions.ExclusionOfTheCriticalState
