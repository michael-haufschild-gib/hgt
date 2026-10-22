import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceCoefficientGrowth

/-! Whole-interval bounds for the original independent-frequency Gauss factors. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

private theorem coefficient_choose_bound {w chi : ℂ} (h : Chamber w chi)
    (k : ℕ) (hk : w.re-1 ≤ k) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ‖outerCoefficient w chi n‖ ≤ D*(n+k).choose k := by
  obtain ⟨C,hC,hb⟩ := outerCoefficient_growth h
  refine ⟨max 1 (C*k.factorial),le_trans (by norm_num) (le_max_left _ _),?_⟩
  intro n
  by_cases hn : n=0
  · subst n
    simp [outerCoefficient,ordinaryHypergeometricCoefficient]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpow : (n:ℝ)^(w.re-1) ≤ (n:ℝ)^k := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hk
  have hc : n^k ≤ k.factorial*(n+k).choose k := by
    rw [← Nat.ascFactorial_eq_factorial_mul_choose]
    exact (Nat.pow_le_pow_left (Nat.le_succ n) k).trans (Nat.pow_succ_le_ascFactorial (n+1) k)
  have hc' : (n:ℝ)^k ≤ (k.factorial:ℝ)*(n+k).choose k := by exact_mod_cast hc
  calc
    ‖outerCoefficient w chi n‖ ≤ C*(n:ℝ)^(w.re-1) := hb n (Nat.pos_of_ne_zero hn)
    _ ≤ C*((k.factorial:ℝ)*(n+k).choose k) := mul_le_mul_of_nonneg_left (hpow.trans hc') hC
    _ ≤ max 1 (C*k.factorial)*(n+k).choose k := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)

/-- A bound at the actual horizon for the outer Gauss factor. The freely chosen
integer exponent may be the ceiling of Re(w), retaining every resonant frequency. -/
theorem outerFactor_bound {w chi : ℂ} (h : Chamber w chi)
    (k : ℕ) (hk : w.re-1 ≤ k) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, z ∈ Ioo 0 1 →
      ‖gaussFactor w chi true (1-z)‖ ≤ D/z^(k+1) := by
  obtain ⟨D,hD,hb⟩ := coefficient_choose_bound h k hk
  refine ⟨D,hD,fun z hz => ?_⟩
  have hx : ‖(1-z:ℝ)‖ < 1 := by rw [Real.norm_of_nonneg (sub_nonneg.mpr hz.2.le)]; linarith [hz.1]
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k hx).mul_left D
  have hn (n : ℕ) : ‖outerCoefficient w chi n*(1-(z:ℂ))^n‖ ≤
      D*((n+k).choose k*(1-z)^n) := by
    rw [norm_mul,norm_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr hz.2.le)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb n)
      (pow_nonneg (sub_nonneg.mpr hz.2.le) n)
  have ht := tsum_of_norm_bounded hs hn
  simpa [gaussFactor,radialSeries,outerSeries,ordinaryHypergeometric_sum_eq,
    smul_eq_mul,outerCoefficient,ordinaryHypergeometricCoefficient,div_eq_mul_inv] using ht

/-- Absolute Gauss summation bounds the original horizon factor across the
entire closed real radial interval. -/
theorem horizonFactor_bound {w chi : ℂ} (h : Chamber w chi) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, z ∈ Icc 0 1 → ‖gaussFactor w chi false z‖ ≤ D := by
  obtain ⟨ha,hb,hc,-⟩ := chamber_parameters h
  have hg : 0 < (gaussC w-gaussA w chi-gaussB w chi).re := by rw [gauss_gap]; norm_num
  have hs := (summable_ordinaryHypergeometricCoefficient_of_re_gap_pos _ _ _
    (avoidsNegNat_of_re_pos ha) (avoidsNegNat_of_re_pos hb) (avoidsNegNat_of_re_pos hc) hg).norm
  refine ⟨∑' n : ℕ, ‖ordinaryHypergeometricCoefficient (gaussA w chi) (gaussB w chi) (gaussC w) n‖,
    tsum_nonneg (fun _ => norm_nonneg _),fun z hz => ?_⟩
  have hn (n : ℕ) : ‖ordinaryHypergeometricCoefficient (gaussA w chi) (gaussB w chi)
      (gaussC w) n*(z:ℂ)^n‖ ≤
      ‖ordinaryHypergeometricCoefficient (gaussA w chi) (gaussB w chi) (gaussC w) n‖ := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hz.1]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hz.1 hz.2)
  have ht := tsum_of_norm_bounded hs.hasSum hn
  simpa [gaussFactor,radialSeries,horizonSeries,ordinaryHypergeometric_sum_eq,smul_eq_mul,ordinaryHypergeometricCoefficient] using ht

end
end RHTower.D4BMLaplaceRadial
