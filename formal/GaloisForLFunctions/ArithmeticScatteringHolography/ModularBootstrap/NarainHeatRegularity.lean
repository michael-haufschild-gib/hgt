import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellin
/-!
# Regularity of the scalar Narain heat sum

Gaussian majorants give continuity on positive heights. The explicit mass
gap upgrades convergence to exponential decay at large height.
-/

open Complex RHTower MeasureTheory Set Filter Topology Asymptotics

noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Every nonvacuum Boltzmann weight decreases with worldsheet height. -/
theorem narainBoltzmann_antitone (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (q : NonzeroScalarCharge) : Antitone (fun y => narainBoltzmann ρ σ y q.val) := by
  intro a b hab
  apply Real.exp_le_exp.mpr
  have hm := narainMassSq_pos ρ σ q.property.2
  have h := mul_le_mul_of_nonneg_right hab (mul_pos Real.pi_pos hm).le
  nlinarith only [h]

/-- Gaussian domination at half the base height gives local uniform convergence. -/
theorem continuousOn_narainScalarHeat (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    ContinuousOn (narainScalarHeat ρ σ) (Ioi 0) := by
  intro y hy
  have ha : 0 < y / 2 := half_pos hy
  have hsum : Summable (fun q : NonzeroScalarCharge => narainBoltzmann ρ σ (y / 2) q.val) :=
    (summable_narainBoltzmann ρ σ ha).comp_injective Subtype.val_injective
  have hc : ContinuousOn (narainScalarHeat ρ σ) (Ici (y / 2)) := by
    apply continuousOn_tsum
    · intro q
      unfold narainBoltzmann
      fun_prop
    · exact hsum
    · intro q z hz
      rw [Complex.norm_real, Real.norm_of_nonneg
        (show 0 ≤ narainBoltzmann ρ σ z q.val from (Real.exp_pos _).le)]
      exact narainBoltzmann_antitone ρ σ q hz
  exact (hc.continuousAt (Ici_mem_nhds (half_lt_self hy))).continuousWithinAt

theorem locallyIntegrableOn_narainScalarHeat (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    LocallyIntegrableOn (narainScalarHeat ρ σ) (Ioi 0) :=
  (continuousOn_narainScalarHeat ρ σ).locallyIntegrableOn measurableSet_Ioi


/-- The mass gap gives exponential decay after the vacuum is removed. -/
theorem narainScalarHeat_exp_tail (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    ∃ B c : ℝ, 0 ≤ B ∧ 0 < c ∧ ∀ y : ℝ, 1 ≤ y →
      ‖narainScalarHeat ρ σ y‖ ≤ B * Real.exp (-(c * y)) := by
  let K := massCoercivityConstant ρ σ
  have hK : 0 < K := massCoercivityConstant_pos ρ σ
  let b := fun q : NonzeroScalarCharge => narainBoltzmann ρ σ (1 / 2) q.val
  have hb : Summable b := (summable_narainBoltzmann ρ σ
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_injective Subtype.val_injective
  refine ⟨∑' q, b q, Real.pi / (2 * K),
    tsum_nonneg (fun _ => (Real.exp_pos _).le), div_pos Real.pi_pos (by positivity), ?_⟩
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hpoint (q : NonzeroScalarCharge) : narainBoltzmann ρ σ y q.val ≤
      b q * Real.exp (-(Real.pi / (2 * K) * y)) := by
    have hm := narainMassSq_pos ρ σ q.property.2
    have hg : 1 / K ≤ narainMassSq ρ σ q.val := narainMassSq_gap ρ σ q.property.2
    have h₁ := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) / 2 ≤ y / 2 by linarith only [hy]) hm.le
    have h₂ := mul_le_mul_of_nonneg_left hg (half_pos hy0).le
    change Real.exp _ ≤ Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : Real.pi / (2 * K) * y = Real.pi * (y / 2 * (1 / K)) := by ring
    rw [he]
    have hle : (1 / 2 : ℝ) * narainMassSq ρ σ q.val + y / 2 * (1 / K) ≤
        y * narainMassSq ρ σ q.val := by linarith only [h₁, h₂]
    nlinarith only [mul_le_mul_of_nonneg_left hle Real.pi_pos.le]
  calc
    ‖narainScalarHeat ρ σ y‖ ≤ ∑' q : NonzeroScalarCharge,
        ‖(narainBoltzmann ρ σ y q.val : ℂ)‖ :=
      norm_tsum_le_tsum_norm (summable_narainScalarHeatTerm ρ σ hy0).norm
    _ = ∑' q : NonzeroScalarCharge, narainBoltzmann ρ σ y q.val := by
      apply tsum_congr
      intro q
      rw [Complex.norm_real, Real.norm_of_nonneg
        (show 0 ≤ narainBoltzmann ρ σ y q.val from (Real.exp_pos _).le)]
    _ ≤ ∑' q, b q * Real.exp (-(Real.pi / (2 * K) * y)) :=
      ((summable_narainBoltzmann ρ σ hy0).comp_injective
        Subtype.val_injective).tsum_le_tsum hpoint (hb.mul_right _)
    _ = _ := tsum_mul_right

/-- An exponential majorant for the Mellin transform at infinity. -/
theorem exists_isBigO_narainScalarHeat_exp (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    ∃ c : ℝ, 0 < c ∧ narainScalarHeat ρ σ =O[atTop]
      (fun y : ℝ => Real.exp (-c * y)) := by
  obtain ⟨B, c, _, hc, h⟩ := narainScalarHeat_exp_tail ρ σ
  refine ⟨c, hc, IsBigO.of_bound B ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  simpa only [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul] using h y hy

#print axioms continuousOn_narainScalarHeat
#print axioms narainScalarHeat_exp_tail
#print axioms exists_isBigO_narainScalarHeat_exp

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
