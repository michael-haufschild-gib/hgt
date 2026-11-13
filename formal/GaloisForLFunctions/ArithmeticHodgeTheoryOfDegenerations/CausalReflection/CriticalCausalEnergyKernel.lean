import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergyTranslation

/-!
# The exact mixed-energy kernel of causal critical translates

Polarization of the translation defect gives simultaneous mixed covariance.
Subtracting the smaller delay leaves a ground-state factor, annihilated by
the weak equation. The resulting kernel is an exponential minimum kernel
times the weighted correlation Gram kernel.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

theorem criticalHalfLineExponentialPair_add_self {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineExponentialPair (fun u => F u + G u) (fun u => F u + G u) =
      criticalHalfLineExponentialPair F F + 2 * criticalHalfLineExponentialPair F G +
        criticalHalfLineExponentialPair G G := by
  simp only [criticalHalfLineExponentialPair]
  have hp (u : ℝ) : (F u + G u) * (F u + G u) * Real.exp (-(8 * u)) =
      F u ^ 2 * Real.exp (-(8 * u)) + 2 * (F u * G u * Real.exp (-(8 * u))) +
        G u ^ 2 * Real.exp (-(8 * u)) := by ring
  simp_rw [hp]
  have hiFG : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)) +
      2 * (F u * G u * Real.exp (-(8 * u)))) :=
    hF.exponential.add ((hF.integrable_exponentialCross hG).const_mul 2)
  rw [integral_add hiFG hG.exponential,
    integral_add hF.exponential ((hF.integrable_exponentialCross hG).const_mul 2),
    integral_const_mul]
  simp only [pow_two]

/-- Causal translation has an exact bilinear exponential defect. -/
theorem criticalHalfLineMixedEnergy_causalTranslate (R : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    {h : ℝ} (hh : 0 ≤ h) :
    criticalHalfLineMixedEnergy R (fun u => F (u + h)) (fun u => G (u + h)) =
      criticalHalfLineMixedEnergy R F G + criticalAliasCoefficient R *
        (Real.exp (8 * h) - 1) * criticalHalfLineExponentialPair F G := by
  have hsum : CriticalHalfLineEnergyDomain (fun u => F u + G u) := by
    simpa only [one_mul] using hF.add_const_mul hG 1
  have hs := criticalHalfLineFullEnergy_comp_add_right hsum h R
    (fun _ hu => hsum.support _ (add_nonneg hu hh))
  have hf := criticalHalfLineFullEnergy_comp_add_right hF h R
    (fun _ hu => hF.support _ (add_nonneg hu hh))
  have hg := criticalHalfLineFullEnergy_comp_add_right hG h R
    (fun _ hu => hG.support _ (add_nonneg hu hh))
  rw [← criticalHalfLineExponentialPair_self, criticalHalfLineExponentialPair_add_self hF hG]
    at hs
  rw [← criticalHalfLineExponentialPair_self] at hf hg
  have hp := criticalHalfLineFullEnergy_add_const_mul R hF hG 1
  have hpt := criticalHalfLineFullEnergy_add_const_mul R (hF.causalTranslate hh)
    (hG.causalTranslate hh) 1
  simp only [one_mul, one_pow, mul_one] at hp hpt
  rw [hp] at hs
  rw [hf, hg] at hpt
  nlinarith only [hs, hpt]

/-- Ordered delays reduce the mixed form to a single weighted correlation. -/
theorem criticalHalfLineMixedEnergy_ground_translates_of_le
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    criticalHalfLineMixedEnergy W₀ (fun u => F (u + s)) (fun u => F (u + t)) =
      criticalAliasCoefficient W₀ * (1 - Real.exp (-(8 * s))) *
        criticalHalfLineExponentialPair (fun u => F (u + s)) (fun u => F (u + t)) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hdG := hdF.causalTranslate (sub_nonneg.mpr hst)
  have he := criticalHalfLineMixedEnergy_causalTranslate W₀ hdF hdG hs
  have hm := criticalHalfLineExponentialPair_comp_add_right F (fun u => F (u + (t - s))) s
  have hfun : (fun u => F ((u + s) + (t - s))) = (fun u => F (u + t)) := by
    funext u
    congr 1
    ring
  rw [hfun, criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hdG,
    zero_add] at he
  rw [hfun] at hm
  rw [he, hm]
  have hcoef : (1 - Real.exp (-(8 * s))) * Real.exp (8 * s) = Real.exp (8 * s) - 1 := by
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = criticalAliasCoefficient W₀ *
        ((1 - Real.exp (-(8 * s))) * Real.exp (8 * s)) *
          criticalHalfLineExponentialPair F (fun u => F (u + (t - s))) := by rw [hcoef]
    _ = _ := by ring

/-- The actual causal energy Gram kernel is the exponential minimum kernel times weighted overlap. -/
theorem criticalHalfLineMixedEnergy_ground_translates
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    criticalHalfLineMixedEnergy W₀ (fun u => F (u + s)) (fun u => F (u + t)) =
      criticalAliasCoefficient W₀ * (1 - Real.exp (-(8 * min s t))) *
        criticalHalfLineExponentialPair (fun u => F (u + s)) (fun u => F (u + t)) := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact criticalHalfLineMixedEnergy_ground_translates_of_le hW hthreshold hF hs hst
  · rw [min_eq_right hts,
      criticalHalfLineMixedEnergy_symm W₀
        ((criticalHalfLineEnergyDomain_of_groundState hF).causalTranslate hs)
        ((criticalHalfLineEnergyDomain_of_groundState hF).causalTranslate ht),
      criticalHalfLineExponentialPair_symm (fun u => F (u + s))]
    exact criticalHalfLineMixedEnergy_ground_translates_of_le hW hthreshold hF ht hts

/-- Failure of RH supplies an actual state with the exact minimum-kernel mixed energy law. -/
theorem riemannHypothesis_or_exists_causal_minimum_energy_kernel :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ),
      0 < W₀ ∧ (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      criticalHalfLineMixedEnergy W₀ (fun u => F (u + s)) (fun u => F (u + t)) =
        criticalAliasCoefficient W₀ * (1 - Real.exp (-(8 * min s t))) *
          criticalHalfLineExponentialPair (fun u => F (u + s)) (fun u => F (u + t)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, fun _ _ hs ht' =>
      criticalHalfLineMixedEnergy_ground_translates hW ht hF hs ht'⟩

#print axioms criticalHalfLineMixedEnergy_causalTranslate
#print axioms criticalHalfLineMixedEnergy_ground_translates
#print axioms riemannHypothesis_or_exists_causal_minimum_energy_kernel

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
