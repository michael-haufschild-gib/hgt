import GaloisForLFunctions.RHTower.CCMFUSuzukiConnectedThirdTangentBridge
import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalChordMeasure

open scoped ArithmeticFunction BigOperators
open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

def suzukiCriticalChordConnectedThirdRenormalization (ω : ℝ) (n : ℕ) : ℝ :=
  12 * ((suzukiCriticalChordCoefficient ω n -
      ArithmeticFunction.vonMangoldt n -
        ω * ((ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) n)) / ω ^ (2 : ℕ)) -
    8 * (((ArithmeticFunction.vonMangoldt *
      ArithmeticFunction.vonMangoldt) *
        ArithmeticFunction.vonMangoldt) n)

theorem suzukiCriticalThirdGrade_connectedRenormalization_eq (n : ℕ) :
    12 * suzukiCriticalThirdGradeCoefficient n -
        8 * (((ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) *
            ArithmeticFunction.vonMangoldt) n) =
      (shiftedEulerConnectedThirdTangentArithmetic n).re := by
  rw [suzukiCriticalThirdGradeCoefficient,
    shiftedEulerConnectedThirdTangentArithmetic_apply]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  norm_num
  ring

theorem shiftedEulerConnectedThirdTangentArithmetic_re_eq (n : ℕ) :
    (shiftedEulerConnectedThirdTangentArithmetic n).re =
      2 * ArithmeticFunction.vonMangoldt n * Real.log n ^ (2 : ℕ) := by
  rw [← suzukiCriticalThirdGrade_connectedRenormalization_eq,
    suzukiCriticalThirdGradeCoefficient]
  ring

theorem shiftedEulerConnectedThirdTangentArithmetic_re_nonneg (n : ℕ) :
    0 ≤ (shiftedEulerConnectedThirdTangentArithmetic n).re := by
  rw [shiftedEulerConnectedThirdTangentArithmetic_re_eq]
  positivity

/-- Connected Suzuki third mass is supported exactly on prime powers.  Hence the cumulant
cancellation removes every disconnected composite label without erasing a genuine Euler atom. -/
theorem shiftedEulerConnectedThirdTangentArithmetic_re_pos_iff (n : ℕ) :
    0 < (shiftedEulerConnectedThirdTangentArithmetic n).re ↔
      IsPrimePow n := by
  rw [shiftedEulerConnectedThirdTangentArithmetic_re_eq]
  constructor
  · intro h
    have hΛ : 0 < ArithmeticFunction.vonMangoldt n := by
      by_contra hnot
      have hzero : ArithmeticFunction.vonMangoldt n = 0 :=
        le_antisymm (le_of_not_gt hnot) ArithmeticFunction.vonMangoldt_nonneg
      rw [hzero] at h
      norm_num at h
    exact ArithmeticFunction.vonMangoldt_pos_iff.mp hΛ
  · intro hn
    have hΛ : 0 < ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_pos_iff.mpr hn
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast IsPrimePow.one_lt hn)
    positivity

theorem tendsto_suzukiCriticalChordConnectedThirdRenormalization (n : ℕ) :
    Tendsto (fun ω : ℝ =>
      suzukiCriticalChordConnectedThirdRenormalization ω (n + 1))
      (𝓝[>] 0)
      (𝓝 ((shiftedEulerConnectedThirdTangentArithmetic (n + 1)).re)) := by
  have h := tendsto_suzukiCriticalChordCoefficient_thirdGrade n
  have hscaled := (h.const_mul (12 : ℝ)).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      8 * (((ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) *
          ArithmeticFunction.vonMangoldt) (n + 1)))
      (𝓝[>] 0) (𝓝 _))
  rw [suzukiCriticalThirdGrade_connectedRenormalization_eq] at hscaled
  simpa only [suzukiCriticalChordConnectedThirdRenormalization] using hscaled

def ccmFUSuzukiConnectedChordPrimeEntryApprox (ω : ℝ) (n : ℕ) : ℝ :=
  16 * suzukiCriticalChordConnectedThirdRenormalization ω n /
    (Real.sqrt n * Real.log n ^ (5 : ℕ))

theorem tendsto_ccmFUSuzukiConnectedChordPrimeEntryApprox (n : ℕ) :
    Tendsto (fun ω : ℝ =>
      ccmFUSuzukiConnectedChordPrimeEntryApprox ω (n + 2))
      (𝓝[>] 0) (𝓝 (ccmGuinandWeilPrimeEntryThirdJetScale (n + 2))) := by
  have hbase := tendsto_suzukiCriticalChordConnectedThirdRenormalization (n + 1)
  have h := (hbase.const_mul (16 : ℝ)).div_const
    (Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) ^ (5 : ℕ))
  rw [ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent n]
  simpa only [ccmFUSuzukiConnectedChordPrimeEntryApprox, Nat.add_assoc,
    Nat.reduceAdd] using h

private theorem tendsto_ccmFUSuzukiConnectedChordPrimeEntryApprox_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun ω : ℝ => ccmFUSuzukiConnectedChordPrimeEntryApprox ω n)
      (𝓝[>] 0) (𝓝 (ccmGuinandWeilPrimeEntryThirdJetScale n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_comm] using
    tendsto_ccmFUSuzukiConnectedChordPrimeEntryApprox m

private theorem ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    ccmGuinandWeilPrimeEntryThirdJetScale n =
      16 * (shiftedEulerConnectedThirdTangentArithmetic n).re /
        (Real.sqrt n * Real.log n ^ (5 : ℕ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_comm] using
    ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent m

def ccmFUSuzukiConnectedChordTriangularCompletedApprox
    (b H ω : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then
      ccmFUSuzukiConnectedChordPrimeEntryApprox ω k *
        (1 - Real.log k / H)
    else 0) -
  ∫ h in b..H,
    ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
      (2 * Real.cosh (h / 2))

theorem tendsto_ccmFUSuzukiConnectedChordTriangularCompletedApprox
    (b H : ℝ) :
    Tendsto (ccmFUSuzukiConnectedChordTriangularCompletedApprox b H)
      (𝓝[>] 0)
      (𝓝 (ccmFUSuzukiConnectedThirdTangentTriangularCompletedWindow b H)) := by
  have hsum :
      Tendsto (fun ω : ℝ =>
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            ccmFUSuzukiConnectedChordPrimeEntryApprox ω k *
              (1 - Real.log k / H)
          else 0)
        (𝓝[>] 0)
        (𝓝 (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            ccmGuinandWeilPrimeEntryThirdJetScale k *
              (1 - Real.log k / H)
          else 0)) := by
    apply tendsto_finsetSum
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      exact (tendsto_ccmFUSuzukiConnectedChordPrimeEntryApprox_of_two_le
        (Finset.mem_Icc.mp hk).1).mul_const _
    · simp only [hbk, if_false]
      exact tendsto_const_nhds
  have hsumTarget :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          ccmGuinandWeilPrimeEntryThirdJetScale k *
            (1 - Real.log k / H)
        else 0) =
      ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow b H := by
    rw [ccmFUSuzukiConnectedThirdTangentTriangularPrimeWindow]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      rw [ccmGuinandWeilPrimeEntryThirdJetScale_eq_connectedSuzukiThirdTangent_of_two_le
        (Finset.mem_Icc.mp hk).1]
    · simp only [hbk, if_false]
  rw [hsumTarget] at hsum
  have hcompleted := hsum.sub (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => ∫ h in b..H,
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
        (2 * Real.cosh (h / 2))) (𝓝[>] 0) (𝓝 _))
  rw [ccmFUSuzukiConnectedThirdTangentTriangularCompletedWindow]
  change Tendsto (fun ω : ℝ =>
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      if b < Real.log k then
        ccmFUSuzukiConnectedChordPrimeEntryApprox ω k *
          (1 - Real.log k / H)
      else 0) -
    ∫ h in b..H,
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
        (2 * Real.cosh (h / 2))) (𝓝[>] 0) _
  exact hcompleted

theorem tendsto_ccmFUSuzukiConnectedChordTriangularCompletedApprox_literal
    (b H : ℝ) :
    Tendsto (ccmFUSuzukiConnectedChordTriangularCompletedApprox b H)
      (𝓝[>] 0)
      (𝓝 (ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H))) := by
  rw [ccmGuinandWeilPrimePolarTriangularWindow_eq_connectedSuzukiProducer]
  exact tendsto_ccmFUSuzukiConnectedChordTriangularCompletedApprox b H

def ccmFUSuzukiConnectedChordCofinalWall (b : ℝ) (N : ℕ) : ℝ :=
  b + (N : ℝ) + 1

theorem tendsto_ccmFUSuzukiConnectedChordCofinalWall (b : ℝ) :
    Tendsto (ccmFUSuzukiConnectedChordCofinalWall b) atTop atTop := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := tendsto_atTop_add_const_right atTop (b + 1) hnat
  apply h.congr'
  exact Filter.Eventually.of_forall fun N => by
    simp only [ccmFUSuzukiConnectedChordCofinalWall]
    ring

/-- Actual Suzuki characteristics admit a common positive parameter schedule on moving cofinal
finite heads whose connected third renormalization converges to the literal coupled
prime--polar CCM window.  Cancellation is retained inside the completed window. -/
theorem exists_suzukiConnectedChordThirdGradeLiteralCofinalSchedule (b : ℝ) :
    ∃ ω : ℕ → ℝ,
      Tendsto ω atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ =>
        ccmFUSuzukiConnectedChordTriangularCompletedApprox b
            (ccmFUSuzukiConnectedChordCofinalWall b N) (ω N) -
          ccmGuinandWeilPrimePolarWeightedWindow b
            (ccmFUSuzukiConnectedChordCofinalWall b N)
            (ccmGuinandWeilThirdGradeCesaroTriangularWeight
              (ccmFUSuzukiConnectedChordCofinalWall b N)))
        atTop (𝓝 0) ∧
      ∀ N : ℕ,
        0 < ω N ∧ ω N < 1 / ((N : ℝ) + 1) ∧
        |ccmFUSuzukiConnectedChordTriangularCompletedApprox b
              (ccmFUSuzukiConnectedChordCofinalWall b N) (ω N) -
            ccmGuinandWeilPrimePolarWeightedWindow b
              (ccmFUSuzukiConnectedChordCofinalWall b N)
              (ccmGuinandWeilThirdGradeCesaroTriangularWeight
                (ccmFUSuzukiConnectedChordCofinalWall b N))| <
          1 / ((N : ℝ) + 1) := by
  have hselect : ∀ N : ℕ, ∃ u : ℝ,
      0 < u ∧ u < 1 / ((N : ℝ) + 1) ∧
      |ccmFUSuzukiConnectedChordTriangularCompletedApprox b
            (ccmFUSuzukiConnectedChordCofinalWall b N) u -
          ccmGuinandWeilPrimePolarWeightedWindow b
            (ccmFUSuzukiConnectedChordCofinalWall b N)
            (ccmGuinandWeilThirdGradeCesaroTriangularWeight
              (ccmFUSuzukiConnectedChordCofinalWall b N))| <
        1 / ((N : ℝ) + 1) := by
    intro N
    let ε : ℝ := 1 / ((N : ℝ) + 1)
    have hε : 0 < ε := by dsimp only [ε]; positivity
    have hlimit :=
      tendsto_ccmFUSuzukiConnectedChordTriangularCompletedApprox_literal b
        (ccmFUSuzukiConnectedChordCofinalWall b N)
    have herror : ∀ᶠ u : ℝ in 𝓝[>] 0,
        ccmFUSuzukiConnectedChordTriangularCompletedApprox b
            (ccmFUSuzukiConnectedChordCofinalWall b N) u ∈
          Metric.ball
            (ccmGuinandWeilPrimePolarWeightedWindow b
              (ccmFUSuzukiConnectedChordCofinalWall b N)
              (ccmGuinandWeilThirdGradeCesaroTriangularWeight
                (ccmFUSuzukiConnectedChordCofinalWall b N))) ε :=
      hlimit.eventually (Metric.ball_mem_nhds _ hε)
    have hcap : ∀ᶠ u : ℝ in 𝓝[>] 0, u ∈ Set.Ioo 0 ε :=
      Ioo_mem_nhdsGT hε
    obtain ⟨u, huerror, hucap⟩ := (herror.and hcap).exists
    refine ⟨u, hucap.1, hucap.2, ?_⟩
    simpa only [Metric.mem_ball, Real.dist_eq] using huerror
  choose ω hωpos hωcap herror using hselect
  refine ⟨ω, ?_, ?_, fun N => ⟨hωpos N, hωcap N, herror N⟩⟩
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun N => (hωpos N).le)
      (Filter.Eventually.of_forall fun N => (hωcap N).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun N => norm_nonneg _)
      (Filter.Eventually.of_forall fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.norm_eq_abs] using (herror N).le

end

end RHTower
