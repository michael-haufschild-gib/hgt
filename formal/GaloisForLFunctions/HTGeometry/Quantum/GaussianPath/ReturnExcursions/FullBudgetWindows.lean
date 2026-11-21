import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Entropy
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SignPacking.WindowGrid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WindowOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathMicroscopicCircuitOrder

/-! # Occupation of long robustly hard windows at the full exponential budget -/
open Set Filter MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
open SpectralJets
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Sublevel hits at any time in the observation window. -/
def robustWindowHits {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ) (W : ℝ) : Set ℝ :=
  {u | ∃ t ∈ Icc u (u+W), orbitCircuitDistance H P t ≤ 1/8}

private theorem budget_window_bound {n : ℕ} (hn : 64 ≤ n) (H : selfAdjoint (Reg n))
    (hspeed : 40*‖H.val‖ ≤ (2:ℝ)^n) {G : ℝ} (hG : 0 ≤ G)
    (l : (Fin n → Bool) ≃ Fin ((2^n-1)+1))
    (hphase : ∀ y : Fin (2^n-1) → ℝ, ∃ t ∈ Icc 0 G, ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (l.symm i)) j-y j) < 1/80)
    (b e : ℕ) (hbe : 16*(b+e) ≤ 7*2^n) (a T : ℝ) (hT : 0 ≤ T) :
    (2:ℝ)^e*volume.real (robustWindowHits H (nearHilbertContinuousCircuitBudget n) ((2:ℝ)^b) ∩
      Icc a (a+T)) ≤ T+G := by
  let P := nearHilbertContinuousCircuitBudget n
  let mesh := 1/(2:ℝ)^n
  let W := (2:ℝ)^b
  let L := volume.real (robustWindowHits H P W ∩ Icc a (a+T))
  let J := plateauGridCount W mesh * (atMostQuarterCircuitNet n P).card
  have hmesh : ‖H.val‖*mesh ≤ 1/40 := by
    dsimp [mesh]; rw [mul_one_div,div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hspeed]
  have tubes := spectral_sign_visits_tube_occupation l H hG (fun x => by
    obtain ⟨t,ht,z,hz,hh⟩ := phase_interval_approaches_reflection l H 0 G hphase x
    exact ⟨t,ht,z,hz,hh.trans_lt (by norm_num)⟩)
  have h := circuit_window_occupation_at_error H (1/8) le_rfl tubes P W mesh
    (by dsimp [mesh]; positivity) hmesh a T hT
  simp only [hasProjectiveCircuitApproximation_iff_infDist] at h
  have ho : (2:ℝ)^(2^n-1)*L ≤ (J:ℝ)*(T+G) := by
    simpa only [L,robustWindowHits,orbitCircuitDistance,J,Nat.cast_mul] using h
  have hJpos : 0 < J := by
    obtain ⟨V,hV,_⟩ := atMostQuarterCircuitNet_cover (TwoQubitCircuit.one n)
      (show (TwoQubitCircuit.one n).gateCount ≤ P from Nat.zero_le _)
    exact Nat.mul_pos (Nat.succ_pos _) (Finset.card_pos.mpr ⟨V,hV⟩)
  have hcard : (2:ℕ)^e*J ≤ 2^(2^n-1) := full_budget_grid_card hn hbe
  have hc : (2:ℝ)^e*(J:ℝ) ≤ (2:ℝ)^(2^n-1) := by exact_mod_cast hcard
  apply le_of_mul_le_mul_left _ (show (0:ℝ) < J by exact_mod_cast hJpos)
  calc
    (J:ℝ)*((2:ℝ)^e*L) = ((2:ℝ)^e*J)*L := by ring
    _ ≤ (2:ℝ)^(2^n-1)*L := mul_le_mul_of_nonneg_right hc ENNReal.toReal_nonneg
    _ ≤ _ := ho

/-- In any observation interval, time origins whose next 2^b time units
include even one full-budget hit at error 1/8 have measure at most
(T+G)/2^e. Every interval of length G contains a zero-gate return. -/
theorem gaussian_full_budget_robust_windows :
    ∃ q : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let G := (2:ℝ)^(D^q)
      (∀ a : ℝ, ∃ t ∈ Icc a (a+G), HasProjectiveCircuitApproximation N (1/10:ℝ) 0
        (unitaryEvolution H.val t)) ∧
      ∀ b e : ℕ, 16*(b+e) ≤ 7*D → ∀ a T : ℝ, 0 ≤ T →
        (2:ℝ)^e * volume.real (robustWindowHits H (nearHilbertContinuousCircuitBudget N)
          ((2:ℝ)^b) ∩ Icc a (a+T)) ≤ T+G := by
  obtain ⟨q,hclock⟩ := derivativePhaseHorizon_double_upper
  obtain ⟨_,v,_,_,hmass⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨m,hm⟩ := exists_nat_gt (12+v)
  refine ⟨q,?_⟩
  filter_upwards [gaussian_path_derivative_phase_filling,hmass] with ω hf hmω
  filter_upwards [hf,(tendsto_add_atTop_nat 1).eventually hmω,eventually_ge_atTop 64,eventually_ge_atTop m]
    with k hfill hcoeff hk hlarge
  intro N D u H G
  obtain ⟨l,hl⟩ := hfill
  have hp (a : ℝ) (y : Fin (D-1) → ℝ) : ∃ t ∈ Icc a (a+G), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (l.symm i)) j-y j) < 1/80 := by
    obtain ⟨t,ht,hh⟩ := hl a y
    exact ⟨t,⟨ht.1,ht.2.trans (add_le_add le_rfl (hclock k))⟩,hh⟩
  have hN : 64 ≤ N := by dsimp [N]; omega
  have hscale : 12+v ≤ (N:ℝ) := hm.le.trans (by exact_mod_cast (show m ≤ N by dsimp [N]; omega))
  have hnorm : ‖H.val‖ ≤ (N:ℝ)^2 := calc
    _ ≤ ∑ l, |u l| := by
      change ‖pathHamiltonian u‖ ≤ _
      rw [pathHamiltonian_eq_sum]
      exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun l _ => by
        rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one])
    _ ≤ (12+v)*(N:ℝ) := path_pauli_coefficient_mass_le u v hcoeff.2
    _ ≤ _ := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _)
  have hD : 64*((N:ℝ)+1)^2 ≤ (2:ℝ)^N := by exact_mod_cast dimension_dominates_speed hN
  have hs : 40*‖H.val‖ ≤ (2:ℝ)^N := by
    apply le_trans _ hD
    nlinarith only [hnorm,sq_nonneg (N:ℝ),Nat.cast_nonneg (α := ℝ) N]
  refine ⟨fun a => phase_interval_contains_zero_gate l H a (a+G) (hp a),?_⟩
  intro b e hbe a T hT
  exact budget_window_bound hN H hs (by dsimp [G]; positivity) l
    (fun y => by simpa only [zero_add] using hp 0 y) b e hbe a T hT

#print axioms gaussian_full_budget_robust_windows
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
