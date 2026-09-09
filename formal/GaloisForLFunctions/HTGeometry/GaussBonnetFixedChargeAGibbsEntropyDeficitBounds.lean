import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionRates

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem sqrt_entropy_gap (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x * Real.log (x / y) - x + y := by
  have hsx := Real.sq_sqrt hx.le
  have hsy := Real.sq_sqrt hy.le
  have hsxp : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsyp : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hlog : 2 * Real.log (Real.sqrt y / Real.sqrt x) = Real.log y - Real.log x := by
    rw [Real.log_div hsyp.ne' hsxp.ne', Real.log_sqrt hy.le, Real.log_sqrt hx.le]
    ring
  have hdiv : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hsxp.ne').mpr
    nlinarith
  have hright : 2 * x * (Real.sqrt y / Real.sqrt x - 1) =
      2 * Real.sqrt x * Real.sqrt y - 2 * x := by
    calc
      _ = 2 * (x / Real.sqrt x) * Real.sqrt y - 2 * x := by ring
      _ = _ := by rw [hdiv]
  have hleft : 2 * x * Real.log (Real.sqrt y / Real.sqrt x) =
      x * (Real.log y - Real.log x) := by nlinarith [congrArg (fun z => x * z) hlog]
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hsyp hsxp)) (show 0 ≤ 2 * x by positivity)
  rw [hright, hleft] at h
  rw [Real.log_div hx.ne' hy.ne']
  nlinarith

/-- Relative entropy controls square-root distinguishability from the stationary law. -/
theorem egbFixedChargeAGibbsEntropyDeficit_hellinger_lower (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2 ≤ egbFixedChargeAGibbsEntropyDeficit n m β E := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hu : ∑ _ : Fin (2 ^ (n + 3)), ((2 : ℝ) ^ (n + 3))⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
    sqrt_entropy_gap (egbFixedChargeAGibbsMarkovPopulation n m β E i)
      (((2 : ℝ) ^ (n + 3))⁻¹) (egbFixedChargeAGibbsMarkovPopulation_pos n m β E i)
      (inv_pos.mpr (pow_pos (by norm_num) _)))
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    egbFixedChargeAGibbsMarkovPopulation_mass, hu, sub_add_cancel] at h
  simpa only [egbFixedChargeAHellinger_coordinate_square,
    egbFixedChargeAGibbsEntropyDeficit, relEntropy, tsum_fintype] using h

/-- Relative entropy is bounded above by the normalized excess collision probability. -/
theorem egbFixedChargeAGibbsEntropyDeficit_collision_upper (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n m β E ≤
      (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
    mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (egbFixedChargeAGibbsMarkovPopulation_pos n m β E i)
        (show 0 < ((2 : ℝ) ^ (n + 3))⁻¹ by positivity)))
      (egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E i))
  change (∑ i, egbFixedChargeAGibbsMarkovPopulation n m β E i *
    Real.log (egbFixedChargeAGibbsMarkovPopulation n m β E i / ((2 : ℝ) ^ (n + 3))⁻¹)) ≤ _ at h
  have hpoint (x : ℝ) : x * (x / ((2 : ℝ) ^ (n + 3))⁻¹ - 1) =
      (2 : ℝ) ^ (n + 3) * x ^ 2 - x := by rw [div_inv_eq_mul]; ring
  simp only [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum,
    egbFixedChargeAGibbsMarkovPopulation_mass] at h
  rw [egbFixedChargeAGibbsEntropyDeficit, relEntropy, tsum_fintype]
  rw [egbFixedChargeAGibbsCollisionExcess_identity]
  calc
    _ ≤ (2 : ℝ) ^ (n + 3) * (∑ i, egbFixedChargeAGibbsMarkovPopulation n m β E i ^ 2) - 1 := h
    _ = _ := by field_simp

/-- Vanishing information deficit exactly identifies the uniform law. -/
theorem egbFixedChargeAGibbsEntropyDeficit_zero_iff_uniform (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n m β E = 0 ↔
      ∀ i, egbFixedChargeAGibbsMarkovPopulation n m β E i = ((2 : ℝ) ^ (n + 3))⁻¹ := by
  constructor
  · intro h i
    have hb := egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E
    rw [h, egbFixedChargeAHellinger_coordinate_square] at hb
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 ^ (n + 3))))) =>
        sq_nonneg (Real.sqrt (egbFixedChargeAGibbsMarkovPopulation n m β E j) -
          Real.sqrt (((2 : ℝ) ^ (n + 3))⁻¹))) (Finset.mem_univ i)
    have hs : Real.sqrt (egbFixedChargeAGibbsMarkovPopulation n m β E i) =
        Real.sqrt (((2 : ℝ) ^ (n + 3))⁻¹) := by nlinarith [hi.trans hb]
    have hp := Real.sq_sqrt (egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E i)
    have hu := Real.sq_sqrt (show 0 ≤ ((2 : ℝ) ^ (n + 3))⁻¹ by positivity)
    rw [hs] at hp
    linarith
  · intro h
    have hf : egbFixedChargeAGibbsMarkovPopulation n m β E =
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := funext h
    rw [egbFixedChargeAGibbsEntropyDeficit_identity, hf, egbFixedChargeAGibbsEntropy_uniform,
      sub_self]

/-- Equality in the Shannon upper bound is possible precisely at equilibrium. -/
theorem egbFixedChargeAGibbsEntropy_maximum_iff_uniform (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n m β E) = (n + 3 : ℝ) * Real.log 2 ↔
      ∀ i, egbFixedChargeAGibbsMarkovPopulation n m β E i = ((2 : ℝ) ^ (n + 3))⁻¹ := by
  rw [← egbFixedChargeAGibbsEntropyDeficit_zero_iff_uniform,
    egbFixedChargeAGibbsEntropyDeficit_identity]
  constructor <;> intro h <;> linarith

end
end GaloisForLFunctions.HTGeometry
