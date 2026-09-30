import GaloisForLFunctions.RHTower.WeilLagQuadraticInterpolation

/-!
# Thick upper excursions of the integer Weil lag

An actual upper lag excursion propagates across one entire side of a natural
arithmetic interval. The squared radius may be proportional to its height times
k*sqrt(k). This constrains the possible sparsity of high lag values without
assuming RH or an actual low-lag density estimate.
-/

open Real
namespace RHTower
noncomputable section

/-- A central upper excursion forces a full high-lag side at its height-scaled radius. -/
theorem integerLag_upper_excursion_has_height_scaled_block :
    ∀ k h : ℕ, 4 ≤ k → 2 * h ≤ k →
      ∀ M δ : ℝ, 0 ≤ M → 0 ≤ δ → (h : ℝ) ^ 2 ≤ δ * (k : ℝ) * Real.sqrt k →
        M + δ < integerLag k →
        (∀ n ∈ Finset.Icc (k - h) k, M < integerLag n) ∨
          (∀ m ∈ Finset.Icc k (k + h), M < integerLag m) := by
  intro k h hk hh M δ hM hδ hsize hhigh
  classical
  by_cases hleft : ∀ n ∈ Finset.Icc (k - h) k, M < integerLag n
  · exact Or.inl hleft
  · right
    push Not at hleft
    obtain ⟨n, hn, hnl⟩ := hleft
    intro m hm
    by_contra hml
    have hn' := Finset.mem_Icc.mp hn
    have hm' := Finset.mem_Icc.mp hm
    have hn2 : 2 ≤ n := by omega
    have hnk : n ≤ k := hn'.2
    have hkm : k ≤ m := hm'.1
    have hgap : (m : ℝ) - n ≤ 2 * h := by
      have hg : (m : ℝ) ≤ n + 2 * h := by exact_mod_cast (by omega : m ≤ n + 2 * h)
      linarith only [hg]
    have hgap0 : 0 ≤ (m : ℝ) - n := by
      have hnm : (n : ℝ) ≤ m := by exact_mod_cast (hnk.trans hkm)
      linarith only [hnm]
    have hns : (k : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : k ≤ 2 * n)
    have hsq : ((m : ℝ) - n) ^ 2 ≤ 4 * (h : ℝ) ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hgap)
        (show 0 ≤ 2 * (h : ℝ) + ((m : ℝ) - n) by positivity)
      nlinarith only [hprod]
    have hscale : ((m : ℝ) - n) ^ 2 ≤ δ * (8 * n * Real.sqrt k) := by
      calc _ ≤ 4 * (h : ℝ) ^ 2 := hsq
        _ ≤ 4 * (δ * (k : ℝ) * Real.sqrt k) := mul_le_mul_of_nonneg_left hsize (by norm_num)
        _ ≤ _ := by
          have hmul := mul_le_mul_of_nonneg_right hns (mul_nonneg hδ (Real.sqrt_nonneg (k : ℝ)))
          nlinarith only [hmul]
    have hcorrection : (((m : ℝ) - n) ^ 2 / (8 * n)) / Real.sqrt k ≤ δ := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < k)),
        div_le_iff₀ (by positivity : (0 : ℝ) < 8 * n)]
      nlinarith only [hscale]
    have hlag := integerLag_le_endpoint_ceiling_add_curvature hn2 hnk hkm hM hnl
      (le_of_not_gt hml)
    linarith only [hlag, hcorrection, hhigh]

/-- A unit-height upper excursion forces a full high-lag side on the k^(3/4) radius scale. -/
theorem integerLag_upper_excursion_has_one_sided_block :
    ∀ k h : ℕ, 4 ≤ k → 2 * h ≤ k → (h : ℝ) ^ 2 ≤ (k : ℝ) * Real.sqrt k →
      ∀ M : ℝ, 0 ≤ M → M + 1 < integerLag k →
        (∀ n ∈ Finset.Icc (k - h) k, M < integerLag n) ∨
          (∀ m ∈ Finset.Icc k (k + h), M < integerLag m) := by
  intro k h hk hh hsize M hM hhigh
  exact integerLag_upper_excursion_has_height_scaled_block k h hk hh M 1 hM
    zero_le_one (by simpa only [one_mul] using hsize) hhigh

end
end RHTower
