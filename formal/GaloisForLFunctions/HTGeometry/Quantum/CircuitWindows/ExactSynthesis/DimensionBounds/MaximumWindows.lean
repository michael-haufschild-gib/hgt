import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Eigenlines
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NearHilbertOnset
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles

/-! # Same-error maximum bounds throughout typical Gaussian plateau windows -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
open AccuracyScales.TenthPlateau
noncomputable section

/-- One recurrent witness transfers the exact spectral circuit cap to
the actual maximum at every nonnegative physical error. -/
theorem maximum_le_dimension_squared {K m : ℕ} (hK : 2 ≤ K) (H : selfAdjoint (Register K))
    {ε : ℝ} (hε : 0 ≤ ε) (hm : IsRecurrentOrbitCircuitMaximumAt H ε m) : m ≤ 35*(2^K)^2 := by
  obtain ⟨_,w,_,hw,hv⟩ := hm.2
  obtain ⟨v,_,hmax⟩ := hv 0
  obtain ⟨z,hz,C,hC,hfit⟩ := (quadratic_evolution_gate_cap hK H v).approx hε
  exact (hmax v ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C hfit).trans hC

/-- For almost every frozen chain, the whole near-Hilbert window stays
above the square root of its own same-error maximum divided by
14√35(K+1). The measure bound holds on every observation interval. -/
theorem gaussian_maximum_windows :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let R : ℝ := (D:ℝ)/2^(14*K.sqrt)
      let G : ℝ := (2:ℝ)^(D^c)
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∃ m : ℕ, nearHilbertContinuousCircuitBudget K < m ∧ m ≤ 35*D^2 ∧
        IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧ ∃ E : Set ℝ, MeasurableSet E ∧
          (∀ a T : ℝ, 0 ≤ T → volume.real (Icc a (a+T) \ E) ≤ (4/5:ℝ)^D*(T+G)) ∧
          ∀ z∈E, ∀ h : ℝ, |h| ≤ R → ∀ s : ℕ,
            HasProjectiveCircuitApproximation K (1/10) s (unitaryEvolution H.val (z+h)) →
              m < 35*(14*(K+1)*s)^2 := by
  obtain ⟨c,hw⟩ := gaussian_tenth_error_exact_onset_and_near_hilbert_core
  refine ⟨c,?_⟩
  filter_upwards [hw,gaussian_pauli_prefix_maximum_and_occupation_quantiles] with ω hω hmax
  filter_upwards [hω,hmax] with k hk hm
  intro K D R G u H
  obtain ⟨m,hmin,hm,_⟩ := hm (1/10) (by constructor <;> norm_num)
  have hcap := maximum_le_dimension_squared (by dsimp only [K]; omega) H (by norm_num) hm
  let L := D/2^(3*K.sqrt)
  let B := D/(7*(K+1))
  let E := tenthPlateauCore H B L R
  obtain ⟨hLB,_,_,_,hE,hw,_⟩ := hk
  refine ⟨m,hmin,hcap,hm,E,hE,hw,?_⟩
  intro z hz h hh s hfit
  have hlo : B<s+L := hz h hh s hfit
  change 2^K.sqrt*L ≤ B at hLB
  have hsqrt : 1 ≤ K.sqrt := Nat.le_sqrt.mpr (by dsimp only [K]; omega)
  have htwo : 2≤(2:ℕ)^K.sqrt := (show 2=(2:ℕ)^1 by decide).le.trans
    (Nat.pow_le_pow_right (by decide) hsqrt)
  have hsl := (Nat.mul_le_mul_right L htwo).trans hLB
  have hB : B<2*s := by omega
  have hD : D < (2*s)*(7*(K+1)) := (Nat.div_lt_iff_lt_mul (by positivity : 0<7*(K+1))).mp hB
  rw [show (2*s)*(7*(K+1))=14*(K+1)*s by ring] at hD
  exact hcap.trans_lt (Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hD (by decide : 2≠0)) (by decide))

#print axioms gaussian_maximum_windows
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
