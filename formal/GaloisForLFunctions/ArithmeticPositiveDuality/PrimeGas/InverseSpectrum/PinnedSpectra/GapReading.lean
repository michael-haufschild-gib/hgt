import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Mixture

/-! # Cauchy transform of the mixed native probabilities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

theorem gap_separation {j : ℕ} {x : ℝ} (hx : occupationWeight (j+1) < x ∧ x < occupationWeight j) (n : ℕ) :
    min (occupationWeight j-x) (x-occupationWeight (j+1)) ≤ |occupationWeight n-x| := by
  by_cases h : n ≤ j
  · have he := occupationWeight_antitone h
    rw [abs_of_nonneg (sub_nonneg.mpr (hx.2.le.trans he))]
    exact (min_le_left _ _).trans (sub_le_sub_right he _)
  · have he := occupationWeight_antitone (Nat.succ_le_of_lt (lt_of_not_ge h))
    rw [abs_of_nonpos (sub_nonpos.mpr (he.trans hx.1.le)),neg_sub]
    exact (min_le_right _ _).trans (sub_le_sub_left he _)

theorem gap_inverse_bound {j : ℕ} {x : ℝ} (hx : occupationWeight (j+1) < x ∧ x < occupationWeight j) :
    ∃ C > (0:ℝ), ∀ n, |(occupationWeight n-x)⁻¹| ≤ C := by
  let d := min (occupationWeight j-x) (x-occupationWeight (j+1))
  have hd : 0 < d := lt_min (sub_pos.mpr hx.2) (sub_pos.mpr hx.1)
  exact ⟨d⁻¹,inv_pos.mpr hd,fun n => (abs_inv _).trans_le (inv_anti₀ hd (gap_separation hx n))⟩

theorem native_ne_in_gap {j : ℕ} {x : ℝ} (hx : occupationWeight (j+1) < x ∧ x < occupationWeight j) (n : ℕ) :
    occupationWeight n-x ≠ 0 :=
  abs_pos.mp ((lt_min (sub_pos.mpr hx.2) (sub_pos.mpr hx.1)).trans_le (gap_separation hx n))

/-- Vanishing of the mixed secular transform is an ordinary convergent sum at every prescribed strict gap. -/
theorem probability_secular {m : ℕ} {b : PrefixData m} (hb : StrictPrefix b) (j : Fin m) :
    HasSum (fun n => prefixProbability b n*(occupationWeight n-(b j).val)⁻¹) 0 := by
  let f (n : ℕ) := (occupationWeight n-(b j).val)⁻¹
  obtain ⟨C,_,hC⟩ := gap_inverse_bound (hb j)
  have hs : Summable (fun n => prefixProbability b n*f n) :=
    ((probability_hasSum b).summable.mul_right C).of_norm_bounded (fun n => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (probability_nonneg b n)]
      exact mul_le_mul_of_nonneg_left (hC n) (probability_nonneg b n))
  apply hs.hasSum_iff.mpr
  rw [mixture_reading b f C hC]
  have he (k : ℕ) : ∑ i, nodeResidue b k i*f (nodeIndex m k i) = 0 :=
    by simpa only [f,div_eq_mul_inv,nativeNode] using nodeResidue_secular hb k j
  simp only [he,mul_zero,tsum_zero]

/-- Heating both copies of the missing vector converts the zero secular reading into unit overlap. -/
theorem probability_resolvent_overlap {m : ℕ} {b : PrefixData m} (hb : StrictPrefix b) (j : Fin m) :
    HasSum (fun n => occupationWeight n*prefixProbability b n*(occupationWeight n-(b j).val)⁻¹) 1 := by
  have h := (probability_hasSum b).add ((probability_secular hb j).mul_left (b j).val)
  rw [mul_zero,add_zero] at h
  apply h.congr_fun
  intro n
  field_simp [native_ne_in_gap (hb j) n]
  ring

#print axioms probability_secular
#print axioms probability_resolvent_overlap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
