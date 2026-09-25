import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.XiWeilHardyReferenceLorentzianPlane

open Complex Set

namespace RHTower

/-- Hardy supplies a horizontal Xi-zero fibre; discreteness and the open unit strip
select its rightmost zero. No Xi zero lies on the positive horizontal ray from it. -/
theorem exists_rightmost_hardy_height_xi_zero :
    ∃ ρ : ℂ, xi ρ = 0 ∧ (1 / 2 : ℝ) ≤ ρ.re ∧
      ∀ t : ℝ, 0 < t → xi (ρ + t) ≠ 0 := by
  obtain ⟨q₁, hq₁⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  let ρ₁ : ℂ := q₁
  have hzero₁ : xi ρ₁ = 0 := xi_eq_zero_of_mem_divisor_support q₁
  have hre₁ : ρ₁.re < 1 := (xi_zero_re_mem_open_unit hzero₁).2
  let K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet_weilLagFunctionCriterion ∩ K).Finite :=
    finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
    refine ⟨hzero₁, ?_⟩
    change ρ₁ ∈ Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im
    rw [Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, hre₁.le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet_weilLagFunctionCriterion ∩ K,
      ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  have hρ₀K := hρ₀mem.2
  change ρ₀ ∈ Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im at hρ₀K
  rw [Complex.mem_reProdIm] at hρ₀K
  refine ⟨ρ₀, hρ₀mem.1, ?_, ?_⟩
  · dsimp only [ρ₁] at hρ₀K
    rw [hq₁] at hρ₀K
    exact hρ₀K.1.1
  intro t ht hzero
  by_cases hle : (ρ₀ + t).re ≤ 1
  · have hmemK : ρ₀ + t ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
      refine ⟨hzero, ?_⟩
      change ρ₀ + t ∈ Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im
      rw [Complex.mem_reProdIm]
      refine ⟨⟨?_, hle⟩, ?_⟩
      · simp only [Complex.add_re, Complex.ofReal_re]
        linarith [hρ₀K.1.1]
      · simp only [Complex.add_im, Complex.ofReal_im, add_zero]
        exact hρ₀K.2
    have hcontra := hmax _ hmemK (by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith)
    simp only [Complex.add_re, Complex.ofReal_re] at hcontra
    linarith
  · exact xi_ne_zero_of_one_le_re (not_le.mp hle).le hzero

end RHTower
