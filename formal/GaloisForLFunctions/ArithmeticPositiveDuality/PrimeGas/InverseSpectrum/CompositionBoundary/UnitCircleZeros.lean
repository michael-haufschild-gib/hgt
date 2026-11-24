import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.LacunaryLaw

/-! # Exact zeros of the lacunary companion on its closed exterior -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open U0 U0NaturalBoundary

/-- The unit probability bound persists up to every point of the unit circle. -/
theorem companion_norm_le_one {w : ℂ} (hw : 1 ≤ ‖w‖) : ‖u0 w‖ ≤ 1 := by
  have he : u0 w = ∑' k, lacCoeff k*(w⁻¹)^k := by
    rw [lac_reindex]
    have h : u0 (w⁻¹)⁻¹ = U0sum w⁻¹ := u0_inv_eq_companion w⁻¹
    rwa [inv_inv] at h
  have hb (k : ℕ) : ‖lacCoeff k*(w⁻¹)^k‖ ≤ lacunaryMass k := by
    rw [norm_mul,norm_pow,norm_inv]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_le_one_of_one_le₀ hw))
  have hs := lacunaryMass_sum.summable.of_nonneg_of_le (fun k => norm_nonneg _) hb
  rw [he,← lacunaryMass_sum.tsum_eq]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb lacunaryMass_sum.summable)

private theorem companion_one : u0 1 = 1 := by
  have h := functional_equation (z := 1) (by norm_num)
  rw [one_pow,mul_one] at h
  linear_combination h

private theorem companion_neg_one : u0 (-1) = -1 := by
  have h := functional_equation (z := -1) (by norm_num)
  rw [neg_one_sq,companion_one] at h
  linear_combination (-1/2:ℂ)*h

private theorem tangent_disks {w : ℂ} (hw : 1 ≤ ‖w‖) (h : ‖2*w+1‖ ≤ 1) : w = -1 := by
  have he : ‖2*w+1‖^2+1-2*‖w‖^2 = 2*‖w+1‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,two_mul,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im]
    ring
  have h1 := sq_le_sq₀ (norm_nonneg _) zero_le_one |>.mpr h
  have h2 := sq_le_sq₀ zero_le_one (norm_nonneg _) |>.mpr hw
  have hh : ‖w+1‖ = 0 := by nlinarith only [he,h1,h2,sq_nonneg ‖w+1‖]
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp hh)

/-- The unique point attaining -1 is the antipode. -/
theorem companion_neg_one_iff {w : ℂ} (hw : 1 ≤ ‖w‖) : u0 w = -1 ↔ w = -1 := by
  refine ⟨fun hu => ?_,fun he => he ▸ companion_neg_one⟩
  have hf := functional_equation hw
  rw [hu] at hf
  have he : 2*w+1 = -u0 (w^2) := by linear_combination -hf
  apply tangent_disks hw
  rw [he,norm_neg]
  apply companion_norm_le_one
  rw [norm_pow]
  exact one_le_pow₀ hw

/-- The companion vanishes on its convergent exterior exactly at the two fourth roots squaring to -1. -/
theorem companion_zero_iff {w : ℂ} (hw : 1 ≤ ‖w‖) : u0 w = 0 ↔ w^2 = -1 := by
  have hsq : 1 ≤ ‖w^2‖ := by rw [norm_pow]; exact one_le_pow₀ hw
  have h := functional_equation hw
  constructor
  · intro hu
    rw [hu,mul_zero] at h
    apply (companion_neg_one_iff hsq).mp
    linear_combination -h
  · intro he
    rw [(companion_neg_one_iff hsq).mpr he,add_neg_cancel] at h
    have hn : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hw)
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero hn)

#print axioms companion_norm_le_one
#print axioms companion_neg_one_iff
#print axioms companion_zero_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
