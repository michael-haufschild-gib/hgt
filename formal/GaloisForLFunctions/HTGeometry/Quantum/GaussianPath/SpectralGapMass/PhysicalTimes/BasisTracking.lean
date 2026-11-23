import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.ThreeGateUpper
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.SemicircleRebound

/-! # Physical cost of tracking the three-gate spectrum in time -/
open Matrix Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
private abbrev Basis (N : ℕ) := unitaryGroup (Fin N → Bool) ℂ

/-- Each positive date admits a three-gate fit. At a lag within a
fixed part of the first spectral semicircle, every relative change
between fitting bases costs a positive density of physical gates. -/
theorem gaussian_three_gate_basis_change :
    ∃ c > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      let fit (t : ℝ) (V : Basis (n+2)) :=
        HasProjectiveCircuitApproximation (n+2) (1/10) 3 (V.val*unitaryEvolution H.val t*star V.val)
      (∀ t ∈ Icc a T, ∃ V, fit t V) ∧
      ∀ v w : ℝ, π/3 ≤ (w-v)*circuitHamiltonianSpectralWidth H → (w-v)*circuitHamiltonianSpectralWidth H ≤ π →
      ∀ V W : Basis (n+2), fit v V → fit w W → ∀ b : ℕ,
      HasProjectiveCircuitApproximation (n+2) (1/100) b (W*V⁻¹).val → c*(n+2:ℕ) ≤ (b:ℝ) := by
  obtain ⟨K,hK,h⟩ := SpectatorCost.gaussian_semicircle_common_basis
  let c := 1/(4*K)
  obtain ⟨M,hM⟩ := exists_nat_gt (14*K)
  refine ⟨c,by dsimp only [c]; positivity,?_⟩
  filter_upwards [h,gaussian_three_gate_conjugate_upper] with ω hw hu
  intro a T ha
  filter_upwards [hw,hu a T ha,eventually_ge_atTop M] with n hn hup hMn
  intro H fit
  refine ⟨hup,?_⟩
  intro v w hl hr V W hv hw b hchange
  let U : Basis (n+2) := ⟨unitaryEvolution H.val w,unitaryEvolution_mem_unitary H.2 w⟩
  have hfit := SpectralApproximation.transfer_basis U V W hchange hw
  have hh := hn v w hl hr V 3 (2*b+3) (1/10) (1/10+2*(1/100)) (by norm_num) hv hfit
  have hlarge : 14*K ≤ (n+2:ℕ) := hM.le.trans (Nat.cast_le.mpr (by omega))
  dsimp only [c]
  rw [one_div_mul_eq_div,div_le_iff₀ (show 0<4*K by positivity)]
  push_cast at hh hlarge ⊢
  nlinarith only [hh,hlarge]

#print axioms gaussian_three_gate_basis_change

/-- Over one unit of positive physical time a grid with step π/W
admits a three-gate description at every point. Updating any choice of
fitting bases along that grid has a quadratic total gate cost. -/
theorem gaussian_basis_tracking_sum :
    ∃ c > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      let width := circuitHamiltonianSpectralWidth H
      let m := ⌊width/π⌋₊
      let t (i : ℕ) := a+i*(π/width)
      let fit (i : ℕ) (V : Basis (n+2)) :=
        HasProjectiveCircuitApproximation (n+2) (1/10) 3 (V.val*unitaryEvolution H.val (t i)*star V.val)
      (∀ i ≤ m, t i ∈ Icc a (a+1) ∧ ∃ V, fit i V) ∧
      ∀ V : ℕ → Basis (n+2), (∀ i ≤ m, fit i (V i)) → ∀ b : ℕ → ℕ,
        (∀ i < m, HasProjectiveCircuitApproximation (n+2) (1/100) (b i) (V (i+1)*(V i)⁻¹).val) →
        c*((n+2:ℕ):ℝ)^2 ≤ ∑ i ∈ Finset.range m, (b i:ℝ) := by
  obtain ⟨c,hc,hcost⟩ := gaussian_three_gate_basis_change
  obtain ⟨r,_,hr,_,hwidth⟩ := FirstAscent.gaussian_initial_clock
  obtain ⟨M,hM⟩ := exists_nat_gt (2*π/r)
  refine ⟨c*r/(2*π),by positivity,?_⟩
  filter_upwards [hcost,hwidth] with ω hω hw
  intro a ha
  filter_upwards [hω a (a+1) ha,hw,eventually_ge_atTop M] with n hpair hw hMn
  intro H width m t fit
  let N : ℝ := (n+2:ℕ)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hlo : r*N ≤ width := hw.1
  have hpos := (mul_pos hr hN).trans_le hlo
  have hlarge : 2*π ≤ r*N := by
    have hh := (div_le_iff₀ hr).mp (hM.le.trans (show (M:ℝ) ≤ N from Nat.cast_le.mpr (by omega)))
    rwa [mul_comm r]
  have hmf : (m:ℝ) ≤ width/π := Nat.floor_le (div_nonneg hpos.le pi_pos.le)
  have hm' : r*N/(2*π) ≤ m := by
    have hh := (div_lt_iff₀ pi_pos).mp (Nat.lt_floor_add_one (width/π))
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hlo,hlarge,hh]
  have hstep : 0 < π/width := div_pos pi_pos hpos
  have htime (i : ℕ) (hi : i ≤ m) : t i ∈ Icc a (a+1) := by
    have hh := (le_div_iff₀ pi_pos).mp ((Nat.cast_le.mpr hi).trans hmf)
    have hlast : (i:ℝ)*(π/width) ≤ 1 := by
      rwa [←mul_div_assoc,div_le_iff₀ hpos,one_mul]
    exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep.le),add_le_add le_rfl hlast⟩
  refine ⟨fun i hi => ⟨htime i hi,hpair.1 _ (htime i hi)⟩,?_⟩
  intro V hV b hb
  have hsum (i : ℕ) (hi : i ∈ Finset.range m) : c*N ≤ (b i:ℝ) := by
    have hi' := Finset.mem_range.mp hi
    have he : (t (i+1)-t i)*width=π := by
      dsimp only [t]
      push_cast
      field_simp [hpos.ne']
      ring
    exact hpair.2 (t i) (t (i+1)) (by rw [he]; linarith only [pi_pos]) he.le (V i) (V (i+1))
      (hV i hi'.le) (hV (i+1) hi') _ (hb i hi')
  have htot := Finset.sum_le_sum hsum
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at htot
  apply le_trans _ htot
  calc c*r/(2*π)*N^2 = (r*N/(2*π))*(c*N) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hm' (mul_nonneg hc.le hN.le)

#print axioms gaussian_basis_tracking_sum
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
