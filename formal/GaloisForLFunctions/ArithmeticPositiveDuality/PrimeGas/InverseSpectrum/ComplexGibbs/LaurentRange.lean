import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.SurvivingPartition

/-! # Exact range of Laurent constants after finite omissions

The constant is defined by its punctured complex limit. Uniqueness of limits
identifies its attainable values with the reflection of the harmonic Gibbs losses.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- All real finite parts obtained by positive conserving propagators of missing dimension r. -/
def survivingConstants (r : ℕ) : Set ℝ :=
  {c | ∃ (P : Projection) (hd : MissingDimension P r) (hc : Conserving (projected P)),
    Tendsto (fun z : ℂ => survivingPartition (physicalSpectrum P hd hc) z - 1/(z-1))
      (𝓝[≠] 1) (𝓝 (c : ℂ))}

theorem mem_survivingConstants_iff (r : ℕ) (c : ℝ) :
    c ∈ survivingConstants r ↔ Real.eulerMascheroniConstant - c ∈ responseAtRank (powerResponse unitExponent) r := by
  constructor
  · rintro ⟨P,hd,hc,h⟩
    have he := Complex.ofReal_inj.mp (tendsto_nhds_unique (surviving_finite_part (physicalSpectrum P hd hc)) h)
    exact ⟨P,hd,hc,by linarith only [he]⟩
  · rintro ⟨P,hd,hc,he⟩
    refine ⟨P,hd,hc,?_⟩
    simpa only [he,sub_sub_cancel] using surviving_finite_part (physicalSpectrum P hd hc)

theorem survivingConstants_zero : survivingConstants 0 = {Real.eulerMascheroniConstant} := by
  ext c
  rw [mem_survivingConstants_iff,responseAtRank_zero,mem_singleton_iff,mem_singleton_iff,sub_eq_zero]
  exact eq_comm

theorem unit_gibbsHead (r : ℕ) : gibbsHead unitExponent r = ∑ n ∈ Finset.range r, ((n:ℝ)+1)⁻¹ := by
  simp only [gibbsHead,shellPower,unitExponent,Real.rpow_one,one_div]

/-- At positive rank both Laurent endpoints are strict, and every intermediate constant occurs. -/
theorem survivingConstants_succ (r : ℕ) :
    survivingConstants (r+1) = Ioo (Real.eulerMascheroniConstant - ∑ n ∈ Finset.range (r+1), ((n:ℝ)+1)⁻¹)
      Real.eulerMascheroniConstant := by
  rw [← unit_gibbsHead]
  ext c
  rw [mem_survivingConstants_iff,gibbs_range_at_rank]
  change (0 < Real.eulerMascheroniConstant - c ∧ Real.eulerMascheroniConstant - c < gibbsHead _ _) ↔ _
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨by linarith only [h₂],by linarith only [h₁]⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨by linarith only [h₂],by linarith only [h₁]⟩

/-- A single conserving omission can erase the Laurent constant while keeping the unit residue. -/
theorem one_omission_zero_finite_part : (0:ℝ) ∈ survivingConstants 1 := by
  rw [show (1:ℕ) = 0+1 from rfl,survivingConstants_succ]
  simp only [Finset.sum_range_one,Nat.cast_zero,zero_add,inv_one,mem_Ioo]
  exact ⟨by linarith only [Real.eulerMascheroniConstant_lt_two_thirds],
    by linarith only [Real.one_half_lt_eulerMascheroniConstant]⟩

/-- Among all finite omissions, every finite part at or below the Euler constant is realized. -/
theorem all_survivingConstants : (⋃ r, survivingConstants r) = Iic Real.eulerMascheroniConstant := by
  ext c
  have he : c ∈ ⋃ r, survivingConstants r ↔ Real.eulerMascheroniConstant-c ∈ finiteGibbsLosses unitExponent := by
    simp only [finiteGibbsLosses,mem_iUnion,mem_survivingConstants_iff]
  rw [he,finiteGibbsLosses_divergent (β := unitExponent) (show (1:ℝ) ≤ 1 from le_rfl),mem_Ici,mem_Iic]
  exact sub_nonneg

#print axioms mem_survivingConstants_iff
#print axioms survivingConstants_zero
#print axioms survivingConstants_succ
#print axioms one_omission_zero_finite_part
#print axioms all_survivingConstants

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
