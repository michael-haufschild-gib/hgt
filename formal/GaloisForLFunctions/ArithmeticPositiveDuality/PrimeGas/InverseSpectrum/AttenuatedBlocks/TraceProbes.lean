import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.Probes
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.ThermalControl

/-! # Physical trace inequalities on attenuated occupation spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Relative partitions and quadratic readings extend a physical estimate to every limiting spectrum. -/
theorem trace_control_on_closure {r : ℕ} {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 ≤ p)
    (h : traceControlsAt r z p K) {b : SpectralBand r} (hb : b ∈ closure (physicalSpectra r)) :
    ‖relativePartition b z‖^p ≤ K*relativeReading quadraticResponse b := by
  let S := {c : SpectralBand r | ‖relativePartition c z‖^p ≤ K*relativeReading quadraticResponse c}
  have hs : IsClosed S := isClosed_le ((Real.continuous_rpow_const hp).comp (continuous_relativePartition_spectrum hz r).norm)
    (continuous_const.mul (continuous_relativeReading _ r))
  apply closure_minimal (t := S) _ hs hb
  rintro _ ⟨P,hd,hc,rfl⟩
  change _ ≤ K*relativeReading quadraticResponse _
  rw [quadratic_physicalReading]
  exact h P hd hc

theorem partition_at_two {r : ℕ} (b : SpectralBand r) :
    relativePartition b (2:ℂ) = (relativeReading quadraticResponse b : ℂ) := by
  have he := relativePartition_real b fourthTraceExponent
  rw [reading_at_two b _ rfl] at he
  exact he

private theorem cpow_at_two (x : ℝ) : (x:ℂ)^(2:ℂ) = ((x^2:ℝ):ℂ) := by
  rw [Complex.ofReal_pow,← Complex.cpow_natCast]
  rfl

/-- Any physical trace estimate controls every scalar ground-state chord with the identical coefficient. -/
theorem trace_ground_chord (r : ℕ) {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 ≤ p)
    (h : traceControlsAt (r+1) z p K) (t : Ioc (0:ℝ) 1) :
    ‖1-(t.val:ℂ)^z‖^p ≤ K*(1-t.val^2) := by
  obtain ⟨b,hb,he⟩ := exists_ground_attenuation r t
  have hD := he (z := 2) (by norm_num)
  rw [partition_at_two,cpow_at_two,← Complex.ofReal_one,← Complex.ofReal_sub] at hD
  have hw := trace_control_on_closure hz hp h hb
  rwa [he hz,Complex.ofReal_inj.mp hD] at hw

/-- A uniformly attenuated block loses the same fraction of its fourth trace irrespective of its position. -/
theorem trace_block_chord (N r : ℕ) {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 ≤ p)
    (h : traceControlsAt r z p K) (t : Ioc (0:ℝ) 1) :
    ‖(1-(t.val:ℂ)^z)*relativePartition (blockSpectrum N r) z‖^p ≤
      K*((1-t.val^2)*relativeReading quadraticResponse (blockSpectrum N r)) := by
  obtain ⟨b,hb,he⟩ := exists_uniform_attenuation N r t
  have hD := he (z := 2) (by norm_num)
  rw [partition_at_two,partition_at_two,cpow_at_two,← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_mul] at hD
  have hw := trace_control_on_closure hz hp h hb
  rwa [he hz,Complex.ofReal_inj.mp hD] at hw

#print axioms trace_ground_chord
#print axioms trace_block_chord

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
