import GaloisForLFunctions.RHTower.PairQubitWeakTwoLocalSpectralActionLaw

open scoped BigOperators Matrix
open Matrix Set MeasureTheory ProbabilityTheory Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem tendsto_pairQubitWeakTwoLocalGrowthFailureBudget_atTop :
    Tendsto pairQubitWeakTwoLocalGrowthFailureBudget atTop (nhds 0) := by
  have hmajorReal : Tendsto
      (fun y : ℝ => 144 * (y ^ 2 * Real.exp (-(1 * y))))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_mul_exp_neg_scaled 2 (by norm_num : (0 : ℝ) < 1)).const_mul 144
  have hmajor : Tendsto
      (fun L : ℕ => 144 * ((L : ℝ) ^ 2 * Real.exp (-(L : ℝ))))
      atTop (nhds 0) := by
    convert hmajorReal.comp tendsto_natCast_atTop_atTop using 1
    ext L
    simp
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun L => by
      unfold pairQubitWeakTwoLocalGrowthFailureBudget
      positivity) ?_ hmajor
  filter_upwards [Filter.eventually_ge_atTop 1] with L hL
  have hn : 1 ≤ L * 2 := by omega
  have hcard : Fintype.card (PauliTracelessLabel (L * 2) 2) ≤
      18 * (L * 2) ^ 2 := by
    rw [card_pauliTracelessLabel]
    simpa using Quantum.nonidentityPauliWeightCount_le (L * 2) 2 hn
  have hexp : Real.exp (-((L * 2 : ℕ) : ℝ) ^ 2 / 2) ≤
      Real.exp (-(L : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    push_cast
    nlinarith
  unfold pairQubitWeakTwoLocalGrowthFailureBudget
  calc
    (Fintype.card (PauliTracelessLabel (L * 2) 2) : ℝ) *
          (2 * Real.exp (-((L * 2 : ℕ) : ℝ) ^ 2 / 2)) ≤
        ((18 * (L * 2) ^ 2 : ℕ) : ℝ) *
          (2 * Real.exp (-(L : ℝ))) := by
      gcongr
    _ = 144 * ((L : ℝ) ^ 2 * Real.exp (-(L : ℝ))) := by
      push_cast
      ring

def pairQubitWeakTwoLocalUniformCarrierBudget (L : ℕ) (η κ : ℝ) : ℝ :=
  Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
    (((6 * (L * 2) - 4 : ℕ) : ℝ) * η)) / κ

theorem tendsto_pairQubitWeakTwoLocalUniformCarrierBudget_atTop
    {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    Tendsto (fun L => pairQubitWeakTwoLocalUniformCarrierBudget L η κ)
      atTop (nhds 0) := by
  let a := gaussianIntervalActivationMass ^ 2 / 2
  let b := 8 * a * η
  have ha : 0 < a := by
    dsimp [a]
    positivity [gaussianIntervalActivationMass_pos]
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hheight : Tendsto (fun L : ℕ => b * (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hmajor : Tendsto
      (fun L : ℕ => Real.exp (-(b * (L : ℝ))) / κ) atTop (nhds 0) := by
    simpa using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hheight).div_const κ
  refine squeeze_zero' (Filter.Eventually.of_forall fun L => by
    unfold pairQubitWeakTwoLocalUniformCarrierBudget
    positivity) ?_ hmajor
  filter_upwards [Filter.eventually_ge_atTop 1] with L hL
  unfold pairQubitWeakTwoLocalUniformCarrierBudget
  apply div_le_div_of_nonneg_right _ hκ.le
  apply Real.exp_le_exp.mpr
  have hK : 8 * L ≤ 6 * (L * 2) - 4 := by omega
  have hKreal : ((8 * L : ℕ) : ℝ) ≤ ((6 * (L * 2) - 4 : ℕ) : ℝ) := by
    exact_mod_cast hK
  have hinner : a * (((8 * L : ℕ) : ℝ) * η) ≤
      a * (((6 * (L * 2) - 4 : ℕ) : ℝ) * η) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hKreal hη.le) ha.le
  calc
    -(gaussianIntervalActivationMass ^ 2 / 2) *
          (((6 * (L * 2) - 4 : ℕ) : ℝ) * η) =
        -(a * (((6 * (L * 2) - 4 : ℕ) : ℝ) * η)) := by
      dsimp [a]
      ring
    _ ≤ -(a * (((8 * L : ℕ) : ℝ) * η)) := neg_le_neg hinner
    _ = -(b * (L : ℝ)) := by
      dsimp [b]
      push_cast
      ring

theorem tendsto_pairQubitWeakTwoLocalUniformJointBudget_atTop
    {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    Tendsto (fun L => pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitWeakTwoLocalUniformCarrierBudget L η κ)
      atTop (nhds 0) := by
  simpa using tendsto_pairQubitWeakTwoLocalGrowthFailureBudget_atTop.add
    (tendsto_pairQubitWeakTwoLocalUniformCarrierBudget_atTop hη hκ)

theorem eventually_pairQubitWeakTwoLocalUniformJointBudget_lt_one
    {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    ∀ᶠ L : ℕ in atTop,
      pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitWeakTwoLocalUniformCarrierBudget L η κ < 1 :=
  (tendsto_pairQubitWeakTwoLocalUniformJointBudget_atTop hη hκ).eventually_lt_const
    zero_lt_one

theorem exists_pairQubitWeakTwoLocalUniformJointBudgetThreshold
    {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitWeakTwoLocalUniformCarrierBudget L η κ < 1 := by
  exact Filter.eventually_atTop.1
    (eventually_pairQubitWeakTwoLocalUniformJointBudget_lt_one hη hκ)

end

end RHTower
