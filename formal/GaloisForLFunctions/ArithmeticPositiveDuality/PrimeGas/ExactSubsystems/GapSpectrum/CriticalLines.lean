import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Transition

/-! # Quadratic opening of the Fourier lines at critical damping -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology

private theorem argument_limit :
    Tendsto (fun h : ℝ => (1:ℂ)+(h:ℂ)) (𝓝[>] 0) (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1:ℂ))).add ((Complex.continuous_ofReal.tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi 0)))
  simpa only [Complex.ofReal_zero,add_zero] using ht

private theorem real_pole_limit :
    Tendsto (fun h : ℝ => (h:ℂ)*riemannZeta (1+(h:ℂ))) (𝓝[>] 0) (𝓝 1) := by
  have hp : Tendsto (fun h : ℝ => (1:ℂ)+(h:ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨argument_limit,?_⟩
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    intro he
    exact (Complex.ofReal_ne_zero.mpr hh.ne') (add_eq_left.mp he)
  apply (riemannZeta_residue_one.comp hp).congr
  intro h
  change (1+(h:ℂ)-1)*_ = _
  rw [add_sub_cancel_left]

private theorem critical_argument (h : ℝ) :
    ((((1+h)/2+(1+h)/2:ℝ)):ℂ) = 1+(h:ℂ) := by push_cast; ring

/-- The zero line divided by the square of the inverse-temperature excess tends to the partition at two. -/
theorem constant_line_quadratic_limit :
    Tendsto (fun h : ℝ => overlapCoefficient ((1+h)/2) 0 / (h:ℂ)^2) (𝓝[>] 0) (𝓝 (riemannZeta 2)) := by
  have harg := argument_limit.add argument_limit
  rw [show (1:ℂ)+1 = 2 by norm_num] at harg
  have hn := (differentiableAt_riemannZeta (by norm_num : (2:ℂ) ≠ 1)).continuousAt.tendsto.comp harg
  have hd := (Complex.continuous_ofReal.tendsto _).comp real_pole_limit.norm
  rw [norm_one,Complex.ofReal_one] at hd
  have hl := hn.div (hd.pow 2) (pow_ne_zero _ one_ne_zero)
  rw [one_pow,div_one] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  change riemannZeta ((1+(h:ℂ))+(1+(h:ℂ))) / (‖(h:ℂ)*riemannZeta (1+(h:ℂ))‖:ℂ)^2 = _
  rw [overlapCoefficient_zero (by linarith : 1/2 < (1+h)/2),
    Complex.ofReal_add ((1+h)/2+(1+h)/2) ((1+h)/2+(1+h)/2),critical_argument,
    norm_mul,Complex.norm_of_nonneg hh.le,Complex.ofReal_mul,mul_pow]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- On a reduced line the quadratic coefficient of the onset is the partition at two divided by the product of its labels. -/
theorem reduced_line_quadratic_limit {a b : ℕ+} (hc : a.Coprime b) :
    Tendsto (fun h : ℝ => overlapCoefficient ((1+h)/2) (gapFrequency (a,b)) / (h:ℂ)^2)
      (𝓝[>] 0) (𝓝 (riemannZeta 2 / (((a*b:ℕ+):ℕ):ℂ))) := by
  have hcont : Continuous (fun w : ℂ => heat w (a*b)) := by unfold heat; fun_prop
  have hh := (hcont.tendsto 1).comp argument_limit
  have hl := hh.mul constant_line_quadratic_limit
  have hval : heat 1 (a*b)*riemannZeta 2 = riemannZeta 2 / (((a*b:ℕ+):ℕ):ℂ) := by
    rw [heat_eq_cpow,Complex.cpow_neg_one,div_eq_mul_inv,mul_comm]
  change Tendsto _ _ (𝓝 (heat 1 (a*b)*riemannZeta 2)) at hl
  rw [hval] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h (hp : 0 < h)
  have hx : 1/2 < (1+h)/2 := by linarith
  have he := (div_eq_iff (overlapCoefficient_zero_ne hx)).mp (relative_overlap_line hx hc)
  rw [critical_argument] at he
  change heat (1+(h:ℂ)) (a*b) * (_ / _) = _
  rw [he,mul_div_assoc]

/-- Frequencies outside the rational energy gaps have identically zero quadratic response. -/
theorem absent_line_quadratic_limit {ω : ℝ}
    (hω : ¬∃ a b : ℕ+, a.Coprime b ∧ gapFrequency (a,b) = ω) :
    Tendsto (fun h : ℝ => overlapCoefficient ((1+h)/2) ω / (h:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_const_nhds (x := (0:ℂ))).congr'
  filter_upwards [self_mem_nhdsWithin] with h (hp : 0 < h)
  have hx : 1/2 < (1+h)/2 := by linarith
  have he : overlapCoefficient ((1+h)/2) ω = 0 := not_ne_iff.mp (fun hn => hω ((overlapCoefficient_support hx ω).mp hn))
  rw [he,zero_div]

/-- The nonzero critical response, including its strength, has an unconditional arithmetic classification. -/
theorem quadratic_line_spectrum (ω : ℝ) (z : ℂ) :
    (z ≠ 0 ∧ Tendsto (fun h : ℝ => overlapCoefficient ((1+h)/2) ω / (h:ℂ)^2) (𝓝[>] 0) (𝓝 z)) ↔
      ∃ a b : ℕ+, a.Coprime b ∧ gapFrequency (a,b) = ω ∧ riemannZeta 2 / (((a*b:ℕ+):ℕ):ℂ) = z := by
  constructor
  · rintro ⟨hz,hl⟩
    by_cases hp : ∃ a b : ℕ+, a.Coprime b ∧ gapFrequency (a,b) = ω
    · obtain ⟨a,b,hc,rfl⟩ := hp
      exact ⟨a,b,hc,rfl,tendsto_nhds_unique (reduced_line_quadratic_limit hc) hl⟩
    · exact (hz (tendsto_nhds_unique hl (absent_line_quadratic_limit hp))).elim
  · rintro ⟨a,b,hc,rfl,rfl⟩
    refine ⟨div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2:ℂ).re)) ?_,
      reduced_line_quadratic_limit hc⟩
    exact_mod_cast (a*b).ne_zero

#print axioms quadratic_line_spectrum
#print axioms constant_line_quadratic_limit
#print axioms reduced_line_quadratic_limit
#print axioms absent_line_quadratic_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
