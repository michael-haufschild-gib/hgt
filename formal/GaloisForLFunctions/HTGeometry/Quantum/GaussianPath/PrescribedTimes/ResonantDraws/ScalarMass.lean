import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.DilationCover
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.DirichletMultiples

/-! # A time-uniform lower probability for a prescribed scalar visit -/
open Set MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section

/-- At every prescribed laboratory date, the same Gaussian ensemble has
an explicit positive probability of fitting the empty circuit. -/
theorem gaussian_prescribed_scalar_mass (n Q : ℕ) (t : ℝ) :
    let M : ℕ := (Q+1)^(2^(n+2)-1)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let e := 2*Real.pi/(Q+1:ℝ)
    1 ≤ (∑ i : Fin M, ((M:ℝ)/(i.val+1:ℝ))^Fintype.card (PrefixIndex n))*
      μ.real {x | pathGateDistance n 0 x t ≤ e} := by
  intro M μ e
  let B := {x | pathGateDistance n 0 x t ≤ e}
  let b (i : Fin M) := (M:ℝ)/(i.val+1:ℝ)
  have hb (i : Fin M) : 1 ≤ b i := by
    apply (one_le_div (by positivity)).mpr
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hm : MeasurableSet B :=
    measurableSet_Iic.preimage (continuous_distance_at_time n 0 t).measurable
  apply dilation_cover_mass B hm b hb
  intro x
  let d := 2^(n+2)-1
  let f := (qubitConfigFin (n+2)).trans (finCongr (show 2^(n+2)=d+1 by
    dsimp only [d]
    exact (Nat.sub_add_cancel Nat.one_le_two_pow).symm))
  let H := prefixGenerator n x
  obtain ⟨q,hq,hqM,hfit⟩ := zero_gate_at_integer_multiple f H (t/M) Q
  let i : Fin M := ⟨q-1,by change q ≤ M at hqM; omega⟩
  have hi : i.val+1=q := Nat.sub_add_cancel hq
  have hit : (b i)⁻¹*t = (t/M)*q := by
    have hi' : (i.val:ℝ)+1=q := by exact_mod_cast hi
    change ((M:ℝ)/((i.val:ℝ)+1))⁻¹*t=_
    rw [hi',inv_div]; ring
  refine ⟨i,?_⟩
  change pathGateDistance n 0 ((b i)⁻¹ • x) t ≤ e
  rw [distance_dilate,hit]
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit

#print axioms gaussian_prescribed_scalar_mass
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
