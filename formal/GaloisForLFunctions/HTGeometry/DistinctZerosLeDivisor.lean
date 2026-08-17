import Mathlib.Analysis.Complex.JensenFormula

/-!
# Distinct zeros are counted by the divisor

Each zero of an analytic function contributes at least `1` to its divisor, so the number of
*distinct* zeros in a compact set never exceeds the total divisor mass there.  This is what turns a
Jensen bound on the divisor into a bound on the number of sign changes.
-/

open Complex Metric Set MeromorphicOn

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- On its domain the divisor of an analytic function is the finite vanishing order. -/
theorem divisor_eq_toNat {f : ℂ → ℂ} {K : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hzK : z ∈ K) (hord : analyticOrderAt f z ≠ ⊤) :
    MeromorphicOn.divisor f K z = ((analyticOrderAt f z).toNat : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hzK, ← ENat.coe_toNat hord]
  simp

/-- A zero of an analytic function with finite order contributes at least one to the divisor. -/
theorem one_le_divisor_of_zero {f : ℂ → ℂ} {K : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hzK : z ∈ K) (hz : f z = 0)
    (hord : analyticOrderAt f z ≠ ⊤) :
    1 ≤ MeromorphicOn.divisor f K z := by
  rw [divisor_eq_toNat hf hzK hord]
  have hne : analyticOrderAt f z ≠ 0 := by
    intro h
    rcases analyticOrderAt_eq_zero.mp h with h' | h'
    · exact h' (hf z hzK)
    · exact h' hz
  have hpos : 0 < (analyticOrderAt f z).toNat := by
    rcases Nat.eq_zero_or_pos (analyticOrderAt f z).toNat with h | h
    · exfalso
      exact hne (by rw [← ENat.coe_toNat hord, h]; rfl)
    · exact h
  exact_mod_cast hpos

/-- **The number of distinct zeros is at most the divisor mass.** -/
theorem card_le_divisor_sum {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hf : AnalyticOnNhd ℂ f K) (hord : ∀ z ∈ K, analyticOrderAt f z ≠ ⊤)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ K ∧ f z = 0) :
    (S.card : ℤ) ≤ ∑ᶠ u, MeromorphicOn.divisor f K u := by
  classical
  have hfin := (MeromorphicOn.divisor f K).finiteSupport hK
  have hsub : S ⊆ hfin.toFinset := by
    intro z hz
    obtain ⟨hzK, hzero⟩ := hS z hz
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have h1 := one_le_divisor_of_zero hf hzK hzero (hord z hzK)
    omega
  have hsum : ∑ᶠ u, MeromorphicOn.divisor f K u
      = ∑ u ∈ hfin.toFinset, MeromorphicOn.divisor f K u :=
    finsum_eq_sum_of_support_subset _ (by rw [hfin.coe_toFinset])
  rw [hsum]
  have hnn : ∀ u ∈ hfin.toFinset, 0 ≤ MeromorphicOn.divisor f K u := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have huK : u ∈ K :=
      (MeromorphicOn.divisor f K).supportWithinDomain (Function.mem_support.mpr hu)
    rw [divisor_eq_toNat hf huK (hord u huK)]
    positivity
  calc (S.card : ℤ) = ∑ _u ∈ S, (1 : ℤ) := by simp
    _ ≤ ∑ u ∈ S, MeromorphicOn.divisor f K u := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨huK, hzero⟩ := hS u hu
        exact one_le_divisor_of_zero hf huK hzero (hord u huK)
    _ ≤ ∑ u ∈ hfin.toFinset, MeromorphicOn.divisor f K u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun u hu _ => hnn u hu

end GaloisForLFunctions.HTGeometry
