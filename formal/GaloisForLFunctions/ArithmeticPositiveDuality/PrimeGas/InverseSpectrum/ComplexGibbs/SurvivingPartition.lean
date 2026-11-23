import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.TraceAbscissa
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! # The pole of a surviving Gibbs partition

The relative heat defines a meromorphic continuation of the actual spectral
sum. Every finite omission preserves the residue and shifts the Laurent
constant by exactly the harmonic relative reading.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Continuation of the surviving spectral Gibbs sum from its trace half-plane. -/
def survivingPartition {r : ℕ} (b : SpectralBand r) (z : ℂ) : ℂ := riemannZeta z - relativePartition b z

private theorem occupation_cpow (n : ℕ) (z : ℂ) :
    (occupationWeight n : ℂ) ^ z = 1 / ((n : ℂ)+1)^z := by
  have harg : (((n : ℝ)+1 : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  simpa only [occupationWeight_eq,Complex.ofReal_inv,one_div,Complex.ofReal_add,Complex.ofReal_natCast,
    Complex.ofReal_one] using Complex.inv_cpow (((n : ℝ)+1 : ℝ) : ℂ) z harg

/-- On the absolute convergence half-plane the continuation equals the sum of the surviving levels. -/
theorem survivingPartition_eq_tsum {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 1 < z.re) :
    survivingPartition b z = ∑' n, ((b n).val : ℂ)^z := by
  have ha : Summable (fun n => (occupationWeight n : ℂ)^z) := (summable_band_cpow_iff (hotEdge 0) z).mpr hz
  have hb := (summable_band_cpow_iff b z).mpr hz
  have he : (∑' n, (occupationWeight n : ℂ)^z) = riemannZeta z := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
    exact tsum_congr (fun n => occupation_cpow n z)
  change riemannZeta z - (∑' n, ((occupationWeight n : ℂ)^z - ((b n).val : ℂ)^z)) = _
  rw [ha.tsum_sub hb,he,sub_sub_cancel]

theorem meromorphicAt_survivingPartition {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 0 < z.re) :
    MeromorphicAt (survivingPartition b) z :=
  (HTGeometry.meromorphicOn_riemannZeta z (Set.mem_univ z)).sub (analyticAt_relativePartition b hz).meromorphicAt

theorem analyticAt_survivingPartition {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 0 < z.re) (hne : z ≠ 1) :
    AnalyticAt ℂ (survivingPartition b) z :=
  (HTGeometry.analyticAt_riemannZeta hne).sub (analyticAt_relativePartition b hz)

/-- Every interlacing spectrum retains the full unit residue at one. -/
theorem surviving_residue {r : ℕ} (b : SpectralBand r) :
    Tendsto (fun z : ℂ => (z-1) * survivingPartition b z) (𝓝[≠] 1) (𝓝 1) := by
  have hL := (analyticAt_relativePartition b (z := 1) (by norm_num)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
  have ht : Tendsto (fun z : ℂ => z-1) (𝓝[≠] 1) (𝓝 0) := by
    have hn : Tendsto (fun z : ℂ => z-1) (𝓝 1) (𝓝 ((1:ℂ)-1)) := (continuous_id.sub continuous_const).tendsto 1
    simpa only [sub_self] using hn.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
  simpa only [survivingPartition,mul_sub,zero_mul,sub_zero] using riemannZeta_residue_one.sub (ht.mul hL)

/-- The finite part is measured through the punctured complex plane. -/
theorem surviving_finite_part {r : ℕ} (b : SpectralBand r) :
    Tendsto (fun z : ℂ => survivingPartition b z - 1/(z-1)) (𝓝[≠] 1)
      (𝓝 ((Real.eulerMascheroniConstant - relativeReading (powerResponse unitExponent) b : ℝ) : ℂ)) := by
  have hL := (analyticAt_relativePartition b (z := 1) (by norm_num)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
  have he : relativePartition b 1 = (relativeReading (powerResponse unitExponent) b : ℂ) :=
    relativePartition_real b unitExponent
  rw [Complex.ofReal_sub,← he]
  convert tendsto_riemannZeta_sub_one_div.sub hL using 1
  ext z
  change (riemannZeta z - relativePartition b z) - 1/(z-1) = (riemannZeta z - 1/(z-1)) - relativePartition b z
  abel

#print axioms survivingPartition_eq_tsum
#print axioms meromorphicAt_survivingPartition
#print axioms analyticAt_survivingPartition
#print axioms surviving_residue
#print axioms surviving_finite_part

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
