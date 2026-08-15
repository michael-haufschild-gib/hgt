import GaloisForLFunctions.HTGeometry.GibbsVariationalPrinciple

/-!
# The quenched causal replica mass

Replicating only the candidate preparations, with one shared source, turns the incidence mass into
the Laplace transform of the preparation action.  The mass decreases in the replica order, is
bounded below by the mass of any low-action carrier times its exponential cost, and dominates the
source mass of every low-complexity sector after the fugacity discount.

Its negative logarithm is the Gibbs action of the potential, so the exact duality between source
rarity and replicated preparation cost is the Gibbs variational principle.
-/

open MeasureTheory Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Quenched

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The quenched causal replica mass at replica order `r`. -/
def quenchedActionReplicaMass (ρ : Measure Ω) (F : Ω → ℝ) (r : ℕ) : ℝ := ∫ H, F H ^ r ∂ρ

/-- The preparation action of an accessibility. -/
def preparationActionOf (F : Ω → ℝ) : Ω → ℝ := fun H => -Real.log (F H)

/-- **The replica mass is the Laplace transform of the preparation action.** -/
theorem quenchedActionReplicaMass_eq_integral_exp (ρ : Measure Ω) {F : Ω → ℝ}
    (hF : ∀ H, 0 < F H) (r : ℕ) :
    quenchedActionReplicaMass ρ F r =
      ∫ H, Real.exp (-((r : ℝ) * preparationActionOf F H)) ∂ρ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  show F H ^ r = Real.exp (-((r : ℝ) * -Real.log (F H)))
  rw [show -((r : ℝ) * -Real.log (F H)) = (r : ℝ) * Real.log (F H) by ring,
    Real.exp_nat_mul, Real.exp_log (hF H)]

theorem quenchedActionReplicaMass_nonneg (ρ : Measure Ω) {F : Ω → ℝ} (hF : ∀ H, 0 ≤ F H) (r : ℕ) :
    0 ≤ quenchedActionReplicaMass ρ F r :=
  integral_nonneg fun H => pow_nonneg (hF H) r

theorem quenchedActionReplicaMass_le_one (ρ : Measure Ω) [IsProbabilityMeasure ρ] {F : Ω → ℝ}
    (hF : ∀ H, 0 ≤ F H) (hF1 : ∀ H, F H ≤ 1) (r : ℕ) (hint : Integrable (fun H => F H ^ r) ρ) :
    quenchedActionReplicaMass ρ F r ≤ 1 := by
  have hle : ∀ H, F H ^ r ≤ 1 := fun H => pow_le_one₀ (hF H) (hF1 H)
  calc quenchedActionReplicaMass ρ F r ≤ ∫ _H, (1 : ℝ) ∂ρ :=
        integral_mono hint (integrable_const 1) hle
    _ = 1 := by simp

/-- **The replica mass decreases in the replica order.** -/
theorem quenchedActionReplicaMass_antitone (ρ : Measure Ω) {F : Ω → ℝ} (hF : ∀ H, 0 ≤ F H)
    (hF1 : ∀ H, F H ≤ 1) {r : ℕ} (hint : Integrable (fun H => F H ^ r) ρ)
    (hint' : Integrable (fun H => F H ^ (r + 1)) ρ) :
    quenchedActionReplicaMass ρ F (r + 1) ≤ quenchedActionReplicaMass ρ F r := by
  refine integral_mono hint' hint fun H => ?_
  rw [pow_succ]
  nlinarith [hF H, hF1 H, pow_nonneg (hF H) r, pow_le_one₀ (hF H) (hF1 H) (n := r)]

/-- **Low-complexity sectors are discounted by the replica mass.**  A sector on which the
accessibility is at least `c` has source mass at most `c⁻¹ ^ r` times the replica mass. -/
theorem measureReal_le_quenchedActionReplicaMass (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {F : Ω → ℝ} (hF : ∀ H, 0 ≤ F H) {E : Set Ω} (hE : MeasurableSet E) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ H ∈ E, c ≤ F H) (r : ℕ) (hint : Integrable (fun H => F H ^ r) ρ) :
    ρ.real E ≤ (c⁻¹) ^ r * quenchedActionReplicaMass ρ F r := by
  classical
  have hpoint : ∀ H, Set.indicator E (1 : Ω → ℝ) H ≤ (c⁻¹) ^ r * F H ^ r := by
    intro H
    by_cases hH : H ∈ E
    · rw [Set.indicator_of_mem hH, Pi.one_apply]
      have hcF : c ≤ F H := hlow H hH
      have hpow : c ^ r ≤ F H ^ r := pow_le_pow_left₀ hc.le hcF r
      have hcr : (0 : ℝ) < c ^ r := by positivity
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ hcr, one_mul]
      exact hpow
    · rw [Set.indicator_of_notMem hH]
      have : (0 : ℝ) ≤ F H ^ r := pow_nonneg (hF H) r
      positivity
  have hindint : Integrable (Set.indicator E (1 : Ω → ℝ)) ρ := by
    rw [integrable_indicator_iff hE]
    exact integrableOn_const (by simp [measure_ne_top])
  have hmono := integral_mono hindint (hint.const_mul _) hpoint
  rw [integral_indicator_one hE, integral_const_mul] at hmono
  exact hmono

/-- **Rare-carrier lower bound.**  A carrier of positive source mass on which the accessibility is
at least `e^{-j}` forces the replica mass to be at least its mass times the replicated cost. -/
theorem quenchedActionReplicaMass_ge_of_carrier (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {F : Ω → ℝ} (hF : ∀ H, 0 ≤ F H) {B : Set Ω} (hB : MeasurableSet B) {j : ℝ}
    (hlow : ∀ H ∈ B, Real.exp (-j) ≤ F H) (r : ℕ) (hint : Integrable (fun H => F H ^ r) ρ) :
    ρ.real B * Real.exp (-((r : ℝ) * j)) ≤ quenchedActionReplicaMass ρ F r := by
  classical
  have hpoint : ∀ H, Real.exp (-((r : ℝ) * j)) * Set.indicator B (1 : Ω → ℝ) H ≤ F H ^ r := by
    intro H
    by_cases hH : H ∈ B
    · rw [Set.indicator_of_mem hH, Pi.one_apply, mul_one]
      have hle : Real.exp (-j) ^ r ≤ F H ^ r :=
        pow_le_pow_left₀ (Real.exp_pos _).le (hlow H hH) r
      rw [← Real.exp_nat_mul] at hle
      have hexp : (r : ℝ) * -j = -((r : ℝ) * j) := by ring
      rw [hexp] at hle
      exact hle
    · rw [Set.indicator_of_notMem hH, mul_zero]
      exact pow_nonneg (hF H) r
  have hindint : Integrable (Set.indicator B (1 : Ω → ℝ)) ρ := by
    rw [integrable_indicator_iff hB]
    exact integrableOn_const (by simp [measure_ne_top])
  have hmono := integral_mono (hindint.const_mul _) hint hpoint
  rw [integral_const_mul, integral_indicator_one hB] at hmono
  rw [mul_comm]
  exact hmono

/-- **The replica-tilted law.**  The density of the minimizing source law against the original
source is the replicated accessibility normalized by the replica mass. -/
theorem rnDeriv_tilted_quenched (ρ : Measure Ω) [IsProbabilityMeasure ρ] {F : Ω → ℝ}
    (hF : ∀ H, 0 < F H) (r : ℕ)
    (hmeas : AEMeasurable (fun H => -((r : ℝ) * preparationActionOf F H)) ρ) :
    (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H)).rnDeriv ρ =ᵐ[ρ]
      fun H => ENNReal.ofReal (F H ^ r / quenchedActionReplicaMass ρ F r) := by
  have hpt : ∀ H : Ω, Real.exp (-((r : ℝ) * preparationActionOf F H)) = F H ^ r := by
    intro H
    show Real.exp (-((r : ℝ) * -Real.log (F H))) = F H ^ r
    rw [show -((r : ℝ) * -Real.log (F H)) = (r : ℝ) * Real.log (F H) by ring,
      Real.exp_nat_mul, Real.exp_log (hF H)]
  have hmass := quenchedActionReplicaMass_eq_integral_exp ρ hF r
  filter_upwards [rnDeriv_tilted_left_self hmeas] with H hH
  rw [hH, hpt H, hmass]

/-- **Entropy expansion at the replica tilt.**  The relative entropy against the minimizing source
law is the source rarity plus the replicated preparation action plus the logarithm of the replica
mass. -/
theorem integral_llr_tilted_quenched (ρ : Measure Ω) [IsProbabilityMeasure ρ] {F : Ω → ℝ}
    (hF : ∀ H, 0 < F H) (r : ℕ)
    (hint : Integrable (fun H => Real.exp (-((r : ℝ) * preparationActionOf F H))) ρ)
    {q : Measure Ω} [IsProbabilityMeasure q] (hq : q ≪ ρ) (hllr : Integrable (llr q ρ) q)
    (hfq : Integrable (fun H => -((r : ℝ) * preparationActionOf F H)) q) :
    (∫ H, llr q (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H)) H ∂q) =
      (∫ H, llr q ρ H ∂q) + (r : ℝ) * (∫ H, preparationActionOf F H ∂q) +
        Real.log (quenchedActionReplicaMass ρ F r) := by
  rw [_root_.MeasureTheory.integral_llr_tilted_right hq hfq hint hllr,
    quenchedActionReplicaMass_eq_integral_exp ρ hF r, integral_neg, integral_const_mul]
  ring

/-- **Quenched replica-action law.**  The negative logarithm of the replica mass is the least value
of source rarity plus replicated preparation action. -/
theorem isLeast_quenchedReplicaAction (ρ : Measure Ω) [IsProbabilityMeasure ρ] {F : Ω → ℝ}
    (hF : ∀ H, 0 < F H) (r : ℕ)
    (hint : Integrable (fun H => Real.exp (-((r : ℝ) * preparationActionOf F H))) ρ)
    (hmeas : AEMeasurable (fun H => -((r : ℝ) * preparationActionOf F H)) ρ)
    (htilt : Integrable (fun H => -((r : ℝ) * preparationActionOf F H))
      (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H))) :
    IsLeast {a : ℝ | ∃ q : Measure Ω, ∃ _ : IsProbabilityMeasure q, q ≪ ρ ∧
        Integrable (llr q ρ) q ∧
        Integrable (fun H => -((r : ℝ) * preparationActionOf F H)) q ∧
        Integrable (llr q (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H))) q ∧
        a = (∫ H, llr q ρ H ∂q) + (r : ℝ) * ∫ H, preparationActionOf F H ∂q}
      (-Real.log (quenchedActionReplicaMass ρ F r)) := by
  have hrewrite : ∀ q : Measure Ω,
      gibbsAction q ρ (fun H => -((r : ℝ) * preparationActionOf F H)) =
        (∫ H, llr q ρ H ∂q) + (r : ℝ) * ∫ H, preparationActionOf F H ∂q := by
    intro q
    rw [gibbsAction]
    have hneg : (∫ H, -((r : ℝ) * preparationActionOf F H) ∂q) =
        -((r : ℝ) * ∫ H, preparationActionOf F H ∂q) := by
      rw [integral_neg, integral_const_mul]
    rw [hneg]
    ring
  have hmass := quenchedActionReplicaMass_eq_integral_exp ρ hF r
  have hbase := isLeast_gibbsAction ρ hint hmeas htilt
  rw [hmass]
  constructor
  · obtain ⟨⟨q, hqprob, hq, h1, h2, h3, h4⟩, -⟩ := hbase
    exact ⟨q, hqprob, hq, h1, h2, h3, by rw [h4, hrewrite q]⟩
  · rintro a ⟨q, hqprob, hq, h1, h2, h3, rfl⟩
    have := hbase.2 ⟨q, hqprob, hq, h1, h2, h3, (hrewrite q).symm⟩
    exact this

end Quenched

end

end GaloisForLFunctions.HTGeometry
