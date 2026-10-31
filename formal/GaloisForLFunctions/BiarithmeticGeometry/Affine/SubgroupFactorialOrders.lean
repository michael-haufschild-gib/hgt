import GaloisForLFunctions.BiarithmeticGeometry.Affine.SubgroupOrders
import GaloisForLFunctions.BiarithmeticGeometry.Affine.FactorialTranslations

/-!
# Factorial steps have unbounded order modulo every proper rational subgroup

A bound on the quotient order of a sufficiently small factorial step would
recover any fixed outside rational by integer multiplication. Thus the quotient
orders tend to infinity, and their reciprocal orbit norms tend to zero.
-/

open Finset Filter Topology
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Factorial translation orders eventually exceed every fixed bound in a proper quotient. -/
theorem eventually_lt_subgroupOrder_factorialStep (H : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ H) (hH : H ≠ ⊤) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, M < rationalSubgroupOrder H (factorialTranslationStep n) := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : ℚ, r ∉ H := by
    by_contra! h
    apply hH
    ext r
    exact ⟨fun _ => trivial, fun _ => h r⟩
  let N := ∑ d ∈ range (M + 1), (r / (d : ℚ)).den
  filter_upwards [eventually_ge_atTop N] with n hn
  by_contra h
  let d := rationalSubgroupOrder H (factorialTranslationStep n)
  have hd : 0 < d := rationalSubgroupOrder_pos H h1 _
  have hdM : d ≤ M := Nat.le_of_not_gt h
  have hden : (r / (d : ℚ)).den ≤ n :=
    (Finset.single_le_sum (f := fun j : ℕ => (r / (j : ℚ)).den) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hdM))).trans hn
  obtain ⟨m, hm⟩ := eq_int_mul_factorialTranslationStep (r / (d : ℚ)) hden
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have he : (m : ℚ) * ((d : ℚ) * factorialTranslationStep n) = r := by
    calc
      _ = ((m : ℚ) * factorialTranslationStep n) * (d : ℚ) := by ring
      _ = (r / (d : ℚ)) * (d : ℚ) := by rw [← hm]
      _ = r := div_mul_cancel₀ r hd0
  have hmem := H.zsmul_mem (rationalSubgroupOrder_mul_mem H (factorialTranslationStep n)) m
  apply hr
  rw [← he]
  simpa only [zsmul_eq_mul] using hmem

/-- The cyclic quotient orders along factorial steps tend to infinity. -/
theorem tendsto_subgroupOrder_factorialStep (H : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ H) (hH : H ≠ ⊤) :
    Tendsto (fun n => rationalSubgroupOrder H (factorialTranslationStep n)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  exact (eventually_lt_subgroupOrder_factorialStep H h1 hH M).mono (fun _ h => h.le)

/-- The discarded identity orbit norms vanish for every proper rational subgroup containing one. -/
theorem tendsto_inv_subgroupOrder_factorialStep (H : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ H) (hH : H ≠ ⊤) :
    Tendsto (fun n => (rationalSubgroupOrder H (factorialTranslationStep n) : ℝ)⁻¹)
      atTop (𝓝 0) := by
  simpa only [Function.comp_def, one_div] using
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_subgroupOrder_factorialStep H h1 hH)

#print axioms tendsto_subgroupOrder_factorialStep
#print axioms tendsto_inv_subgroupOrder_factorialStep
end GaloisForLFunctions.BiarithmeticGeometry
