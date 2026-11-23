import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.RelativePartition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ThermalTransition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import Mathlib.Analysis.Complex.ReImTopology

/-! # The convergence threshold survives every finite omission

At and below exponent one each surviving term dominates the shifted
harmonic sequence. The critical composition line can therefore be read
from any one surviving spectrum.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

def unitExponent : GibbsExponent := ⟨1,show (0 : ℝ) < 1 from zero_lt_one⟩

theorem occupation_rpow_eq_shellPower (β : GibbsExponent) (n : ℕ) :
    occupationWeight n ^ β.val = shellPower β n := by
  rw [shellPower,occupationWeight_eq,Real.inv_rpow (by positivity),one_div]

private theorem occupation_not_summable : ¬ Summable occupationWeight := by
  intro hs
  have he : shellPower unitExponent = occupationWeight := by
    funext n
    rw [← occupation_rpow_eq_shellPower]
    exact Real.rpow_one _
  exact (lt_irrefl (1:ℝ)) ((summable_shellPower_iff unitExponent).mp (he ▸ hs))

/-- Absolute real powers of every interlacing spectrum have abscissa one. -/
theorem summable_band_rpow_iff {r : ℕ} (b : SpectralBand r) (σ : ℝ) :
    Summable (fun n => (b n).val ^ σ) ↔ 1 < σ := by
  constructor
  · intro hs
    by_contra! hσ
    have hle (n : ℕ) : occupationWeight (n+r) ≤ (b n).val ^ σ := by
      apply (b n).property.1.trans
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (band_pos b n) (band_in_unit b n).2 hσ
    exact occupation_not_summable ((summable_nat_add_iff r).mp
      (Summable.of_nonneg_of_le (fun n => (occupationWeight_pos (n+r)).le) hle hs))
  · intro hσ
    let β : GibbsExponent := ⟨σ,zero_lt_one.trans hσ⟩
    apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (band_pos b n).le σ) _ ((summable_shellPower_iff β).mpr hσ)
    intro n
    rw [← occupation_rpow_eq_shellPower]
    exact Real.rpow_le_rpow (band_pos b n).le (b n).property.2 β.property.le

theorem summable_band_cpow_iff {r : ℕ} (b : SpectralBand r) (z : ℂ) :
    Summable (fun n => ((b n).val : ℂ) ^ z) ↔ 1 < z.re := by
  rw [← summable_norm_iff]
  simpa only [Complex.norm_cpow_eq_rpow_re_of_pos (band_pos b _)] using summable_band_rpow_iff b z.re

/-- Normalizable squared amplitudes occupy exactly the open half-plane to the right of the critical line. -/
theorem summable_band_born_iff {r : ℕ} (b : SpectralBand r) (s : ℂ) :
    Summable (fun n => ‖((b n).val : ℂ) ^ s‖ ^ 2) ↔ 1/2 < s.re := by
  have he (n : ℕ) : ‖((b n).val : ℂ) ^ s‖ ^ 2 = (b n).val ^ (2*s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (band_pos b n),← Real.rpow_two,
      ← Real.rpow_mul (band_pos b n).le,mul_comm]
  simp only [he,summable_band_rpow_iff]
  constructor <;> intro h <;> linarith only [h]

/-- A single surviving spectrum detects the isometric composition line, at every finite missing dimension. -/
theorem split_isometry_iff_surviving_frontier {r : ℕ} (b : SpectralBand r) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      s ∈ frontier {w : ℂ | Summable (fun n => ‖((b n).val : ℂ) ^ w‖ ^ 2)} := by
  have he : {w : ℂ | Summable (fun n => ‖((b n).val : ℂ) ^ w‖ ^ 2)} = Complex.re ⁻¹' Ioi (1/2:ℝ) :=
    Set.ext (fun w => summable_band_born_iff b w)
  simp only [split_isometric_iff,he,Complex.frontier_preimage_re,frontier_Ioi,mem_preimage,mem_singleton_iff]

#print axioms summable_band_rpow_iff
#print axioms summable_band_cpow_iff
#print axioms summable_band_born_iff
#print axioms split_isometry_iff_surviving_frontier

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
