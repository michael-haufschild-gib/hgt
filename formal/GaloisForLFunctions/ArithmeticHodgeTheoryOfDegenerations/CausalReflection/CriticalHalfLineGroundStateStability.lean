import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyBranch
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergyDerivative

/-!
# Weighted stability of the minimizing state

The transverse gap turns variation of the confinement coefficient into a
quantitative exponential-mass distance from the critical state line.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory WindowTowerOfSpecZ

/-- Nearby normalized minimizers approach the critical state in the full exponential weight. -/
theorem criticalHalfLineGroundEnergy_minimizer_weighted_stability
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
      |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ≤ δ →
      ∀ H : ℝ → ℝ, IsHalfLineEnergyMinimizer R H →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
            K * |criticalAliasCoefficient R - criticalAliasCoefficient W₀| := by
  obtain ⟨γ, hγ, hgap⟩ := criticalHalfLineFullEnergy_controls_neutralPart hW ht hF
  let w : ℝ := ∫ u, F u ^ 2 * Real.exp (-(8 * u))
  have hw : 0 ≤ w := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  refine ⟨γ / 4, 12 * w * (1 + w) / γ, by positivity, by positivity, ?_⟩
  intro R hR hsmall H hH
  let η : ℝ := criticalAliasCoefficient R - criticalAliasCoefficient W₀
  let c : ℝ := ∫ u, F u * H u
  let N : ℝ → ℝ := criticalHalfLineNeutralPart F H
  let m : ℝ := ∫ u, N u ^ 2
  let n : ℝ := ∫ u, N u ^ 2 * Real.exp (-(8 * u))
  let v : ℝ := ∫ u, H u ^ 2 * Real.exp (-(8 * u))
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hdN : CriticalHalfLineEnergyDomain N := hdF.neutralPart hH.1
  have hm : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
  have hn : 0 ≤ n := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hv : 0 ≤ v := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hmn : m ≤ n := hdN.square_mass_le_exponential_mass
  have hmass : m = 1 - c ^ 2 := criticalHalfLineNeutralPart_square_mass hF hH.1 hH.2.1
  have hc : c ^ 2 ≤ 1 := by linarith only [hmass, hm]
  have hrepr (u : ℝ) : N u + c * F u = H u := sub_add_cancel _ _
  have hweighted := criticalHalfLine_exponential_mass_add_const_mul_le hdN hdF c
  simp only [hrepr] at hweighted
  change v ≤ 2 * n + 2 * c ^ 2 * w at hweighted
  have hcw := mul_le_mul_of_nonneg_right hc hw
  have hvbound : v ≤ 2 * n + 2 * w := by linarith only [hweighted, hcw]
  have henergy : γ * n ≤ criticalHalfLineFullEnergy W₀ H := hgap hH.1
  have he := criticalHalfLineFullEnergy_change_ratio R W₀ hH.1
  rw [hH.2.2] at he
  change criticalHalfLineGroundEnergy R = criticalHalfLineFullEnergy W₀ H + η * v at he
  have htangent := criticalHalfLineGroundEnergy_le_critical_tangent hW hR ht hF
  change criticalHalfLineGroundEnergy R ≤ η * w at htangent
  have hηw := mul_le_mul_of_nonneg_right (le_abs_self η) hw
  have hηv := mul_le_mul_of_nonneg_right (neg_abs_le η) hv
  have hvabs := mul_le_mul_of_nonneg_left hvbound (abs_nonneg η)
  have hmain : γ * n ≤ |η| * (3 * w + 2 * n) := by
    nlinarith only [henergy, he, htangent, hηw, hηv, hvabs]
  change |η| ≤ γ / 4 at hsmall
  have hsmalln := mul_le_mul_of_nonneg_right hsmall hn
  have hnupper : n ≤ (6 * w / γ) * |η| := by
    calc
      n ≤ (6 * w * |η|) / γ := (le_div_iff₀ hγ).mpr (by linarith only [hmain, hsmalln])
      _ = (6 * w / γ) * |η| := by ring
  have hsign : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (c - σ) ^ 2 ≤ m := by
    by_cases hcp : 0 ≤ c
    · refine ⟨1, Or.inl rfl, ?_⟩
      have hc1 : c ≤ 1 := by nlinarith only [hc, sq_nonneg (c - 1)]
      have hp := mul_nonneg hcp (sub_nonneg.mpr hc1)
      nlinarith only [hmass, hp]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have hc1 : -1 ≤ c := by nlinarith only [hc, sq_nonneg (c + 1)]
      have hp := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hcp))
        (show 0 ≤ 1 + c by linarith only [hc1])
      nlinarith only [hmass, hp]
  obtain ⟨σ, hσ, hσbound⟩ := hsign
  refine ⟨σ, hσ, ?_⟩
  have hσn : (c - σ) ^ 2 ≤ n := hσbound.trans hmn
  have hdistance := criticalHalfLine_exponential_mass_add_const_mul_le hdN hdF (c - σ)
  have heq (u : ℝ) : N u + (c - σ) * F u = H u - σ * F u := by
    dsimp only [N, criticalHalfLineNeutralPart, c]
    ring
  simp only [heq] at hdistance
  have hσw := mul_le_mul_of_nonneg_right hσn hw
  have htotal := mul_le_mul_of_nonneg_left hnupper (show 0 ≤ 2 * (1 + w) by positivity)
  have hid : 2 * (1 + w) * ((6 * w / γ) * |η|) =
      (12 * w * (1 + w) / γ) * |η| := by ring
  rw [hid] at htotal
  change (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
    (12 * w * (1 + w) / γ) * |η|
  change (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
    2 * n + 2 * (c - σ) ^ 2 * w at hdistance
  nlinarith only [hdistance, hσw, htotal]

#print axioms criticalHalfLineGroundEnergy_minimizer_weighted_stability

private theorem polar_difference_bound {F H : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hH : CriticalHalfLineEnergyDomain H) (σ : ℝ) :
    ((∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u)) ^ 2 ≤
      (2 * (∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2)) *
        (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) := by
  let D : ℝ → ℝ := fun u => H u - σ * F u
  have hD : CriticalHalfLineEnergyDomain D := by
    simpa only [D, neg_mul, sub_eq_add_neg] using hH.add_const_mul hF (-σ)
  have hs := exponentialSourceMass_le_of_support (Y := 0) le_rfl
    hD.meas.aestronglyMeasurable hD.sq hD.exponential
    (Eventually.of_forall fun u hu => hD.support u hu.le)
  have hs' : exponentialSourceMass D ≤ (∫ u, D u ^ 2) +
      (∫ u, D u ^ 2 * Real.exp (-(8 * u))) := by
    simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul] using hs.2
  have hm := hD.square_mass_le_exponential_mass
  have hsource : exponentialSourceMass D ≤ 2 * (∫ u, D u ^ 2 * Real.exp (-(8 * u))) := by
    linarith only [hs', hm]
  have hJ : 0 ≤ ∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hcs := (sq_integral_mul_polarSourceProfile_le hD.weighted).trans
    (mul_le_mul_of_nonneg_right hsource hJ)
  have hp : (∫ u, D u * polarSourceProfile u) =
      (∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u) := by
    have heq : (fun u => D u * polarSourceProfile u) =
        fun u => H u * polarSourceProfile u - σ * (F u * polarSourceProfile u) := by
      funext u
      dsimp only [D]
      ring
    rw [heq, integral_sub (integrable_mul_polarSourceProfile hH.weighted)
      ((integrable_mul_polarSourceProfile hF.weighted).const_mul σ), integral_const_mul]
  rw [hp] at hcs
  exact hcs.trans_eq (by ring)

/-- The same sign choice controls both the full weighted distance and the literal polar pairing. -/
theorem criticalHalfLineGroundEnergy_minimizer_weighted_and_polar_stability
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ≤ δ →
      ∀ H : ℝ → ℝ, IsHalfLineEnergyMinimizer R H →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
            C * |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ∧
          ((∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u)) ^ 2 ≤
            C * |criticalAliasCoefficient R - criticalAliasCoefficient W₀| := by
  obtain ⟨δ, K, hδ, hK, hstab⟩ := criticalHalfLineGroundEnergy_minimizer_weighted_stability hW ht hF
  let J : ℝ := ∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2
  have hJ : 0 ≤ J := integral_nonneg fun u => sq_nonneg _
  refine ⟨δ, (1 + 2 * J) * K, hδ, by positivity, ?_⟩
  intro R hR hsmall H hH
  obtain ⟨σ, hσ, hdist⟩ := hstab R hR hsmall H hH
  have hpolar := polar_difference_bound (criticalHalfLineEnergyDomain_of_groundState hF) hH.1 σ
  have hcost : 0 ≤ K * |criticalAliasCoefficient R - criticalAliasCoefficient W₀| :=
    mul_nonneg hK (abs_nonneg _)
  have hJcost := mul_nonneg hJ hcost
  have hpolar' := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2 * J by positivity)
  refine ⟨σ, hσ, ?_, ?_⟩
  · nlinarith only [hdist, hJcost]
  · change ((∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u)) ^ 2 ≤
      2 * J * (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) at hpolar
    nlinarith only [hpolar, hpolar', hcost]

/-- Failure of RH supplies an attained, locally simple ground-energy branch with its actual tangent. -/
theorem riemannHypothesis_or_exists_differentiable_criticalHalfLineGroundEnergy :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ) (δ K : ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ 0 < δ ∧ 0 ≤ K ∧
      HasDerivAt criticalHalfLineGroundEnergy
        (-(criticalAliasCoefficient W₀) *
          (∫ u, F u ^ 2 * Real.exp (-(8 * u))) / W₀) W₀ ∧
      (∀ R : ℝ, 0 < R → ∃ H : ℝ → ℝ, IsHalfLineEnergyMinimizer R H) ∧
      ∀ R : ℝ, 0 < R → |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ≤ δ →
        (∀ H L : ℝ → ℝ, IsHalfLineEnergyMinimizer R H → IsHalfLineEnergyMinimizer R L →
          H =ᵐ[volume] L ∨ H =ᵐ[volume] (fun u => -L u)) ∧
        (∀ H : ℝ → ℝ, IsHalfLineEnergyMinimizer R H →
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
              K * |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ∧
            ((∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u)) ^ 2 ≤
              K * |criticalAliasCoefficient R - criticalAliasCoefficient W₀|) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · obtain ⟨δ₁, hδ₁, huniq⟩ := criticalHalfLineGroundEnergy_minimizer_unique_near_threshold hW ht hF
    obtain ⟨δ₂, K, hδ₂, hK, hstab⟩ :=
      criticalHalfLineGroundEnergy_minimizer_weighted_and_polar_stability hW ht hF
    refine Or.inr ⟨W₀, F, min δ₁ δ₂, K, hW, ht, hF, lt_min hδ₁ hδ₂, hK,
      hasDerivAt_criticalHalfLineGroundEnergy hW ht hF,
      fun _ hR => exists_criticalHalfLineGroundEnergy_minimizer hR, ?_⟩
    intro R hR hsmall
    exact ⟨huniq R hR (hsmall.trans (min_le_left _ _)),
      hstab R hR (hsmall.trans (min_le_right _ _))⟩

#print axioms riemannHypothesis_or_exists_differentiable_criticalHalfLineGroundEnergy

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
