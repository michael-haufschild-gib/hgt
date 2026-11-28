import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.RampWindows.GaussianReadings
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.PhysicalDate

/-! # A single centered spectral test for an entire physical time octave -/

open MeasureTheory ProbabilityTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
open PrescribedTimes Dephasing.PairedFields Dephasing.PairedFields.SpectralEdge
noncomputable section

/-- A shortcut at any date in [T,2T] is controlled by one centered Gaussian
phase test. Its distribution and its allowed gate count are the same at
every reading used to test the octave. -/
theorem centered_ramp_window (n s d r : ℕ) (hd : 128 ≤ d.sqrt)
    (hr : r ≤ Fintype.card (Fin (n+2) → Bool)) {T a L ρ : ℝ}
    (hT : 0<T) (ha : a∈Ioc (0:ℝ) 1) (hL : |L|≤T) (hρ : 0<ρ)
    (hvol : ((n+2:ℕ):ℝ)*(1+T) ≤ (2:ℝ)^d) :
    let N := n+2
    let m : ℝ := Fintype.card (PathLabel n)
    let j := s+⌈a*(N:ℝ)*T⌉₊
    let R := firstRanks (Fin N → Bool) r hr
    let Q := (pairLaw n).real (centeredFit n (j+j) R (sqrt 2*L) (2*(11/100+ρ)))
    pathPauliDisorderLaw.real {ω | ∃ t∈Icc T (2*T),
        HasProjectiveCircuitApproximation N (1/10) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)} ≤
      2*m*exp (-2*(d:ℝ)^2) + 200*(1+m*(2*d))*(2:ℝ)^(5*d.sqrt+17)/a*exp 1*
        (sqrt Q+8*m*(r:ℝ)^2*L^2/(T*ρ^2)) := by
  intro N m j R Q
  let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
  let X (ω : PathPauliDisorder) (i : PrefixIndex n) := pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  have hphys (ω) : numberedGenerator n (X ω)=pathHamiltonian (pathPauliDisorderShell ω n) :=
    numberedGenerator_shell _
  have hw : X ⁻¹' prescribedWindowEvent n s T T = {ω | ∃ t∈Icc T (2*T),
      HasProjectiveCircuitApproximation N (1/10) s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)} := by
    ext ω
    change (∃ t∈Icc T (T+T), HasProjectiveCircuitApproximation N (1/10) s
      (unitaryEvolution (numberedGenerator n (X ω)) t)) ↔ _
    rw [hphys,two_mul]
    rfl
  rw [←hw,show pathPauliDisorderLaw.real (X ⁻¹' prescribedWindowEvent n s T T) =
    μ.real (prescribedWindowEvent n s T T) from congrArg ENNReal.toReal
      (hX.measure_preimage (measurable_prescribedWindowEvent ..).nullMeasurableSet)]
  obtain ⟨i,hi⟩ := gaussian_ramp_window_probability n s d hd hT ha hvol
  let k := Fintype.card (PrefixIndex n)+1
  let u := readingScale k i*T
  have hTu : T ≤ u := by
    exact le_mul_of_one_le_left hT.le (le_add_of_nonneg_right (by positivity))
  let B := {x | pathGateDistance n j x u ≤ 11/100}
  have hB : MeasurableSet B := measurableSet_Iic.preimage (continuous_distance_at_time n j u).measurable
  have he : X ⁻¹' B = (fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      BlockDilations.affordableDraw n j (11/100) u := by
    ext ω
    change pathGateDistance n j (X ω) u ≤ 11/100 ↔ HasProjectiveCircuitApproximation N (11/100) j _
    rw [hasProjectiveCircuitApproximation_iff_infDist,pathGateDistance,hphys]
  have hq := centered_physical_circuit_date n j r hr (hT.trans_le hTu) (hL.trans hTu) hρ (11/100)
  have hb : μ.real B ≤ sqrt Q+8*m*(r:ℝ)^2*L^2/(T*ρ^2) := by
    rw [←show pathPauliDisorderLaw.real (X ⁻¹' B)=μ.real B from
      congrArg ENNReal.toReal (hX.measure_preimage hB.nullMeasurableSet),he]
    apply hq.trans (add_le_add le_rfl _)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hTu (sq_nonneg ρ))
  have hm : (Fintype.card (PrefixIndex n):ℝ)=m :=
    congrArg Nat.cast (Fintype.card_congr (pathCoeffEquiv n))
  rw [hm] at hi
  apply hi.trans (add_le_add le_rfl _)
  apply mul_le_mul_of_nonneg_left hb
  exact mul_nonneg (div_nonneg (by positivity) ha.1.le) (exp_pos 1).le

#print axioms centered_ramp_window
end
end GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
