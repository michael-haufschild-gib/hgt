import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.AbsoluteDetuning
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PhaseCube
import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau

/-! # A finite phase filling clock on the Gaussian Pauli ensemble

Lift every retained relative-phase frequency to a balanced energy sum. Except
on the union of the corresponding near-resonances, the same explicit horizon
works for all centers and all time origins.
-/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev EnergyIdx (k : ℕ) := Fin (2^(k+3))
private abbrev PhysicalIdx (k : ℕ) := Fin (Fintype.card (ChainLabel (k+3)))

/-- Add the compensating anchor coefficient so a Fourier frequency becomes
a balanced sum of the physical energies. -/
def liftedPhaseMode {D d : ℕ} (e : Fin D ≃ Fin (d+1)) (p : Fin d → ℕ × ℕ) (i : Fin D) : ℤ :=
  Fin.cases (∑ j, packetCharacter p j) (fun j => -packetCharacter p j) (e i)

private theorem liftedPhaseMode_balanced {D d : ℕ} (e : Fin D ≃ Fin (d+1)) (p : Fin d → ℕ × ℕ) :
    SpectralCharacterBalanced (liftedPhaseMode e p) := by
  unfold SpectralCharacterBalanced liftedPhaseMode
  rw [Equiv.sum_comp e,Fin.sum_univ_succ]
  simp

private theorem liftedPhaseMode_ne_zero {D d M : ℕ} (e : Fin D ≃ Fin (d+1))
    (p : Fin d → ℕ × ℕ) (hp : p ∈ nonconstantPacketIndexSet M d) : liftedPhaseMode e p ≠ 0 := by
  intro h
  apply packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet hp
  funext j
  have h' := congrFun h (e.symm j.succ)
  simpa only [liftedPhaseMode,e.apply_symm_apply,Fin.cases_succ,Pi.zero_apply,neg_eq_zero] using h'

private theorem liftedPhaseMode_sum {D d : ℕ} (e : Fin D ≃ Fin (d+1)) (p : Fin d → ℕ × ℕ) (E : Fin D → ℝ) :
    ∑ i, (liftedPhaseMode e p i:ℝ)*E i = packetFreq (RHTower.zeroProjectiveFrequency (E ∘ e.symm)) p := by
  rw [← Equiv.sum_comp e.symm (fun i => (liftedPhaseMode e p i:ℝ)*E i),Fin.sum_univ_succ]
  simp only [liftedPhaseMode,e.apply_symm_apply,Fin.cases_zero,Fin.cases_succ,Int.cast_sum,Int.cast_neg,
    packetFreq,RHTower.zeroProjectiveFrequency,Function.comp_apply,packetCharacter,Int.cast_sub,Int.cast_natCast]
  rw [Finset.sum_mul,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The finite balanced modes that test all phase cubes at radius ρ. -/
def phaseClockModes {D d : ℕ} (e : Fin D ≃ Fin (d+1)) (ρ : ℝ) : Finset (Fin D → ℤ) := by
  classical
  exact (nonconstantPacketIndexSet (phaseCubeFourierCutoff d ρ) d).image (liftedPhaseMode e)

private def weightMass {D : ℕ} (m : Fin D → ℤ) : ℝ := ∑ i, |(m i:ℝ)|

/-- Detuning available outside the finite Gaussian exceptional set at energy
cutoff R and probability parameter r. -/
def phaseClockDetuning {D d : ℕ} (e : Fin D ≃ Fin (d+1)) (ρ R r : ℝ) : ℝ :=
  r^D.factorial/(1+R*∑ m ∈ phaseClockModes e ρ, weightMass m)^(D.factorial-1)

/-- Physical time horizon for every phase target and every time origin. -/
def gaussianPhaseClock {D d : ℕ} (e : Fin D ≃ Fin (d+1)) (ρ R r : ℝ) : ℝ :=
  8*(((nonconstantPacketIndexSet (phaseCubeFourierCutoff d ρ) d).card:ℝ)+1)/phaseClockDetuning e ρ R r

/-- Failure of the uniform phase clock on the energy cutoff has probability
at most 2r D! times the number of retained balanced modes. -/
theorem gaussian_pauli_phase_clock_failure_le (k d : ℕ) (e : EnergyIdx k ≃ Fin (d+1))
    {ρ R r : ℝ} (hρ : 0 < ρ) (hπ : ρ ≤ π) (hR : 0 ≤ R) (hr : 0 < r) (hr' : r ≤ 1) :
    (Measure.pi fun _ : PhysicalIdx k => gaussianReal 0 1)
      {x | let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
           (∀ i, |E i| ≤ R) ∧ ¬ ∀ σ : Equiv.Perm (EnergyIdx k), ∀ u : ℝ, ∀ c : Fin d → ℝ,
             ∃ t ∈ Icc u (u+gaussianPhaseClock e ρ R r),
               ∀ j, turnDist (t*RHTower.zeroProjectiveFrequency ((E ∘ σ) ∘ e.symm) j-c j) < ρ} ≤
      (phaseClockModes e ρ).card*ENNReal.ofReal (2*(((2^(k+3)).factorial:ℕ):ℝ)*r) := by
  classical
  let S := phaseClockModes e ρ
  let D := 2^(k+3)
  let M := phaseCubeFourierCutoff d ρ
  have hS (m) (hm : m ∈ S) : SpectralCharacterBalanced m ∧ m ≠ 0 := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    exact ⟨liftedPhaseMode_balanced e p,liftedPhaseMode_ne_zero e p hp⟩
  have hmass (m : Fin D → ℤ) : 0 ≤ weightMass m := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let V := 1+R*∑ m ∈ S, weightMass m
  have hV : 0 < V := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hR (Finset.sum_nonneg fun i _ => hmass i))
  let δ := phaseClockDetuning e ρ R r
  have hδ : 0 < δ := div_pos (pow_pos hr _) (pow_pos hV _)
  refine (measure_mono ?_).trans (gaussian_pauli_finite_mode_absolute_detuning k S hS hr hr' R)
  rintro x ⟨hE,hfail⟩
  let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
  refine ⟨hE,?_⟩
  by_contra! hfar
  apply hfail
  intro σ u c
  let ω := RHTower.zeroProjectiveFrequency ((E ∘ σ) ∘ e.symm)
  apply phaseCube_hit_at_calibrated_cutoff hρ hπ hδ ω ?_ u c
  intro p hp
  let m := liftedPhaseMode e p
  have hm : m ∈ S := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hn := hfar m hm σ
  change r^D.factorial ≤ |∑ i, (m i:ℝ)*(E ∘ σ) i| * (weightMass m*R)^(D.factorial-1) at hn
  rw [liftedPhaseMode_sum] at hn
  have hbound : weightMass m*R ≤ V := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ S) => hmass j) hm
    dsimp only [V]; linarith only [mul_le_mul_of_nonneg_left h hR]
  apply (div_le_iff₀ (pow_pos hV (D.factorial-1))).mpr
  exact hn.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (hmass m) hR) hbound _) (abs_nonneg _))

#print axioms gaussian_pauli_phase_clock_failure_le
end
end GaloisForLFunctions.HTGeometry
