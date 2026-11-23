import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.PowerChord
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.GibbsRange
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # The holomorphic relative Gibbs partition

Interlacing dominates the locally uniform series even where the two
individual Gibbs series diverge. The real measurements are its restrictions.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

theorem band_pos {r : ℕ} (b : SpectralBand r) (n : ℕ) : 0 < (b n).val :=
  (occupationWeight_pos (n+r)).trans_le (b n).property.1

def complexDrop {r : ℕ} (b : SpectralBand r) (n : ℕ) (z : ℂ) : ℂ :=
  (occupationWeight n : ℂ) ^ z - ((b n).val : ℂ) ^ z

def relativePartition {r : ℕ} (b : SpectralBand r) (z : ℂ) : ℂ := ∑' n, complexDrop b n z

theorem complexDrop_bound {r : ℕ} (b : SpectralBand r) (n : ℕ) (δ : GibbsExponent)
    {z : ℂ} (hz : δ.val ≤ z.re) :
    ‖complexDrop b n z‖ ≤ (‖z‖ / δ.val) * spectralDrop (powerResponse δ) b n :=
  norm_thermal_chord (band_pos b n) (b n).property.2 (occupation_in_unit n).2 δ.property hz

theorem summable_complexDrop {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n => complexDrop b n z) := by
  let δ : GibbsExponent := ⟨z.re,hz⟩
  exact Summable.of_norm_bounded ((summable_spectralDrop (powerResponse δ) b).mul_left _)
    (fun n => complexDrop_bound b n δ le_rfl)

/-- A real measurement bounds all complex measurements to its right. -/
theorem relativePartition_norm_le {r : ℕ} (b : SpectralBand r) (δ : GibbsExponent)
    {z : ℂ} (hz : δ.val ≤ z.re) :
    ‖relativePartition b z‖ ≤ (‖z‖ / δ.val) * relativeReading (powerResponse δ) b := by
  have ha := (summable_complexDrop b (δ.property.trans_le hz)).norm
  have hb := (summable_spectralDrop (powerResponse δ) b).mul_left (‖z‖ / δ.val)
  calc
    ‖relativePartition b z‖ ≤ ∑' n, ‖complexDrop b n z‖ := norm_tsum_le_tsum_norm ha
    _ ≤ ∑' n, (‖z‖ / δ.val) * spectralDrop (powerResponse δ) b n :=
      ha.tsum_le_tsum (fun n => complexDrop_bound b n δ hz) hb
    _ = _ := tsum_mul_left

private theorem differentiable_power (t : ℝ) (ht : 0 < t) : Differentiable ℂ (fun z : ℂ => (t : ℂ) ^ z) :=
  fun z => differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast ht.ne'))

/-- Holomorphy holds on the whole open right half-plane, including a neighborhood of the zeta pole. -/
theorem analyticAt_relativePartition {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (relativePartition b) z := by
  let δ : GibbsExponent := ⟨z.re / 2,half_pos hz⟩
  let M := ‖z‖ + 1
  let V := {w : ℂ | δ.val < w.re ∧ ‖w‖ < M}
  have ho : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hv : z ∈ V := ⟨half_lt_self hz,lt_add_one _⟩
  have hd (n : ℕ) : DifferentiableOn ℂ (complexDrop b n) V :=
    ((differentiable_power _ (occupationWeight_pos n)).sub (differentiable_power _ (band_pos b n))).differentiableOn
  have hs := (summable_spectralDrop (powerResponse δ) b).mul_left (M / δ.val)
  apply (Complex.differentiableOn_tsum_of_summable_norm hs hd ho ?_).analyticAt (ho.mem_nhds hv)
  intro n w hw
  exact (complexDrop_bound b n δ hw.1.le).trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hw.2.le δ.property.le) (drop_nonneg (powerResponse δ) b n))

/-- At a real temperature the holomorphic partition takes the measured real value. -/
theorem relativePartition_real {r : ℕ} (b : SpectralBand r) (δ : GibbsExponent) :
    relativePartition b (δ.val : ℂ) = (relativeReading (powerResponse δ) b : ℂ) := by
  rw [relativeReading,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [complexDrop,spectralDrop,powerResponse,Complex.ofReal_sub,Complex.ofReal_cpow (occupation_in_unit n).1,
    Complex.ofReal_cpow (band_in_unit b n).1]

#print axioms summable_complexDrop
#print axioms relativePartition_norm_le
#print axioms analyticAt_relativePartition
#print axioms relativePartition_real

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
