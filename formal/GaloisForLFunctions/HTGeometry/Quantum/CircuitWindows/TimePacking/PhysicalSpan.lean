import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.ControlledSigns
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.IntervalCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReflectionVisitPacking

/-! # Physical time required by a comparison with the entire circuit dictionary -/
open Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TimePacking
open DiagonalSynthesis
noncomputable section

/-- If more pairwise separated orbit samples than dictionary centers
fit before time T, the Hamiltonian path length is at least e mʰ.
This applies to any centers covering the full h-gate circuit family. -/
theorem dictionary_requires_time {m h : ℕ} (H : selfAdjoint (Register (m+h)))
    {ι : Type*} [Fintype ι] (t : ι → ℝ) {a T e r : ℝ} (hT : 0≤T) (he : 0<e)
    (ht : ∀ i, t i∈Icc a (a+T))
    (hsep : ∀ i j, i≠j → e≤‖unitaryEvolution H.val (t i)-unitaryEvolution H.val (t j)‖)
    (net : Finset (Register (m+h))) (hr : 2*r<Real.sqrt 2)
    (hc : ∀ U : Register (m+h), Realizes h U →
      ∃ W∈net, ∃ z : ℂ, ‖z‖=1 ∧ ‖U-z • W‖≤r)
    (hcount : net.card<Fintype.card ι) :
    (m:ℝ)^h*e ≤ ‖H.val‖*T := by
  let L := ‖H.val‖
  have hL : 0≤L := norm_nonneg _
  let v (i : ι) := L*(t i-a)
  have hv (i : ι) : v i∈Icc 0 (0+L*T) := by
    rw [zero_add]
    exact ⟨mul_nonneg hL (sub_nonneg.mpr (ht i).1),mul_le_mul_of_nonneg_left
      (by linarith only [(ht i).2]) hL⟩
  have hgap (i j : ι) (hij : i≠j) : e≤|v i-v j| := by
    rw [show v i-v j=L*(t i-t j) by dsimp only [v]; ring,abs_mul,abs_of_nonneg hL]
    exact (hsep i j hij).trans (norm_unitaryEvolution_time_sub_le H.2 _ _)
  have hp := separated_interval_count v 0 (L*T) e (mul_nonneg hL hT) he hv hgap
  have hnat : m^h+1≤Fintype.card ι := (circuit_net_card_lower hr net hc).trans_lt hcount
  have hreal : (m:ℝ)^h+1≤Fintype.card ι := by exact_mod_cast hnat
  have hh := mul_le_mul_of_nonneg_right hreal he.le
  change (m:ℝ)^h*e≤L*T
  linarith only [hp,hh]

#print axioms dictionary_requires_time
end
end GaloisForLFunctions.HTGeometry.TimePacking
