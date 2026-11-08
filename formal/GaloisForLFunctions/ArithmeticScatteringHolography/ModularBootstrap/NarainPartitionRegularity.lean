import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartition

/-!
# Regularity and cusp bounds for the Narain partition

Gaussian domination gives joint measurability, horocycle continuity and
linear cusp growth. The nonvacuum mass gap improves the vacuum-subtracted
bound to exponential decay, uniformly in the angular variable.
-/

open Complex RHTower Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The literal partition is jointly measurable in both worldsheet coordinates. -/
theorem measurable_narainPartition (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    Measurable (fun p : ℝ × ℝ => narainPartition ρ σ p.1 p.2) := by
  unfold narainPartition
  apply Measurable.mul
  · fun_prop
  · apply Measurable.tsum
    intro q
    unfold narainPartitionTerm narainBoltzmann fourierChar
    fun_prop

/-- Absolute Gaussian domination gives continuity along every positive horocycle. -/
theorem continuous_narainPartition_fixedHeight (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {y : ℝ} (hy : 0 < y) : Continuous (fun x : ℝ => narainPartition ρ σ x y) := by
  have hc : ContinuousOn (fun x : ℝ => ∑' q, narainPartitionTerm ρ σ x y q) univ := by
    apply continuousOn_tsum
    · intro q
      unfold narainPartitionTerm fourierChar
      fun_prop
    · exact summable_narainBoltzmann ρ σ hy
    · intro q x _
      exact (norm_narainPartitionTerm ρ σ x y q).le
  exact continuous_const.mul (continuousOn_univ.mp hc)

/-- The full nonvacuum partition has a uniform exponential cusp tail in the angular variable. -/
theorem narainPartition_exp_cusp (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    ∃ B c : ℝ, 0 ≤ B ∧ 0 < c ∧ ∀ x y : ℝ, 1 ≤ y →
      ‖narainPartition ρ σ x y - (y : ℂ)‖ ≤ B * y * Real.exp (-(c * y)) := by
  classical
  let K := massCoercivityConstant ρ σ
  have hK : 0 < K := massCoercivityConstant_pos ρ σ
  let b := narainBoltzmann ρ σ (1 / 2)
  have hb : Summable b := summable_narainBoltzmann ρ σ (by norm_num)
  refine ⟨∑' q, b q, Real.pi / (2 * K),
    tsum_nonneg (fun _ => (Real.exp_pos _).le), div_pos Real.pi_pos (by positivity), ?_⟩
  intro x y hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  let f := fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
    if q = ((0, 0), (0, 0)) then (0 : ℂ) else narainPartitionTerm ρ σ x y q
  have hnorm (q : (ℤ × ℤ) × (ℤ × ℤ)) : ‖f q‖ ≤ narainBoltzmann ρ σ y q := by
    dsimp only [f]
    split_ifs
    · simpa only [norm_zero, narainBoltzmann] using
        (Real.exp_pos (-(Real.pi * y * narainMassSq ρ σ q))).le
    · exact (norm_narainPartitionTerm ρ σ x y q).le
  have hf : Summable f := Summable.of_norm_bounded (summable_narainBoltzmann ρ σ hy0) hnorm
  have hpoint (q : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖f q‖ ≤ b q * Real.exp (-(Real.pi / (2 * K) * y)) := by
    by_cases hq : q = ((0, 0), (0, 0))
    · simp only [f, if_pos hq, norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    · rw [show f q = narainPartitionTerm ρ σ x y q from if_neg hq,
        norm_narainPartitionTerm]
      have hm := narainMassSq_pos ρ σ hq
      have hg : 1 / K ≤ narainMassSq ρ σ q := narainMassSq_gap ρ σ hq
      have h₁ := mul_le_mul_of_nonneg_right
        (show (1 : ℝ) / 2 ≤ y / 2 by linarith only [hy]) hm.le
      have h₂ := mul_le_mul_of_nonneg_left hg (half_pos hy0).le
      change Real.exp _ ≤ Real.exp _ * Real.exp _
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have he : Real.pi / (2 * K) * y = Real.pi * (y / 2 * (1 / K)) := by ring
      rw [he]
      have hle : (1 / 2 : ℝ) * narainMassSq ρ σ q + y / 2 * (1 / K) ≤
          y * narainMassSq ρ σ q := by linarith only [h₁, h₂]
      nlinarith only [mul_le_mul_of_nonneg_left hle Real.pi_pos.le]
  have hs : ‖∑' q, f q‖ ≤ (∑' q, b q) * Real.exp (-(Real.pi / (2 * K) * y)) := by
    calc
      _ ≤ ∑' q, ‖f q‖ := norm_tsum_le_tsum_norm hf.norm
      _ ≤ ∑' q, b q * Real.exp (-(Real.pi / (2 * K) * y)) :=
        hf.norm.tsum_le_tsum hpoint (hb.mul_right _)
      _ = _ := tsum_mul_right
  have hvac : narainPartitionTerm ρ σ x y ((0, 0), (0, 0)) = 1 := by
    simp [narainPartitionTerm, narainBoltzmann, narainMassSq, targetQuadratic,
      fourierChar, chargeSpin]
  have heq : narainPartition ρ σ x y - (y : ℂ) = (y : ℂ) * ∑' q, f q := by
    rw [narainPartition, (summable_narainPartitionTerm ρ σ x hy0).tsum_eq_add_tsum_ite
      ((0, 0), (0, 0)), hvac]
    change (y : ℂ) * (1 + ∑' q, f q) - (y : ℂ) = _
    ring
  rw [heq, norm_mul, Complex.norm_of_nonneg hy0.le]
  calc
    _ ≤ y * ((∑' q, b q) * Real.exp (-(Real.pi / (2 * K) * y))) :=
      mul_le_mul_of_nonneg_left hs hy0.le
    _ = _ := by ring

/-- The partition grows at most linearly above any fixed positive height. -/
theorem narainPartition_linear_cusp (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ y → ‖narainPartition ρ σ x y‖ ≤ C * y := by
  refine ⟨∑' q, narainBoltzmann ρ σ a q,
    tsum_nonneg (fun q => (Real.exp_pos _).le), ?_⟩
  intro x y hay
  have hy : 0 < y := ha.trans_le hay
  have hpoint (q : (ℤ × ℤ) × (ℤ × ℤ)) :
      narainBoltzmann ρ σ y q ≤ narainBoltzmann ρ σ a q := by
    have hm : 0 ≤ narainMassSq ρ σ q :=
      (by positivity : (0 : ℝ) ≤ 2 * |(chargeSpin q : ℝ)|).trans
        (two_mul_abs_spin_le_massSq ρ σ q)
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hay Real.pi_pos.le) hm)
  have hsum := (summable_narainBoltzmann ρ σ hy).tsum_le_tsum hpoint
    (summable_narainBoltzmann ρ σ ha)
  rw [narainPartition, norm_mul, Complex.norm_of_nonneg hy.le]
  have hn : ‖∑' q, narainPartitionTerm ρ σ x y q‖ ≤
      ∑' q, narainBoltzmann ρ σ y q := by
    simpa only [norm_narainPartitionTerm] using
      norm_tsum_le_tsum_norm (summable_norm_narainPartitionTerm ρ σ x hy)
  calc
    _ ≤ y * ∑' q, narainBoltzmann ρ σ a q :=
      mul_le_mul_of_nonneg_left (hn.trans hsum) hy.le
    _ = _ := mul_comm _ _

#print axioms continuous_narainPartition_fixedHeight
#print axioms measurable_narainPartition
#print axioms narainPartition_exp_cusp
#print axioms narainPartition_linear_cusp
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
