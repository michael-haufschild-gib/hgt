import GaloisForLFunctions.HTGeometry.ThermodynamicPairPhaseWitness
import GaloisForLFunctions.HTGeometry.ThermodynamicPrefixPhaseObstruction

/-!
# Gate-complexity ramp for one selected thermodynamic path field

This module combines the circuit-dependent tree cut, exact physical tail energy, arbitrary
noncommuting prefix factor, and quantitative Duhamel budget into one lower law for the literal
finite restrictions of a single countable nearest-neighbour Hamiltonian field.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_exp_four_energy_difference_eq_chord
    (t a b c d : ℝ) :
    ‖Complex.exp (-(Complex.I * (t * a))) *
          Complex.exp (-(Complex.I * (t * b))) -
        Complex.exp (-(Complex.I * (t * c))) *
          Complex.exp (-(Complex.I * (t * d)))‖ =
      ‖Complex.exp (-(Complex.I * (t * (a + b - c - d)))) - 1‖ := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  have hfactor :
      Complex.exp (-(Complex.I * (t * (a : ℂ))) + -(Complex.I * (t * (b : ℂ)))) -
          Complex.exp (-(Complex.I * (t * (c : ℂ))) + -(Complex.I * (t * (d : ℂ)))) =
        Complex.exp (-(Complex.I * (t * (c : ℂ))) + -(Complex.I * (t * (d : ℂ)))) *
          (Complex.exp (-(Complex.I * (t * ((a + b - c - d : ℝ) : ℂ)))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul]
  rw [Complex.norm_exp]
  simp

theorem thermodynamicPairTailCenter_four_chord_eq
    (N K : ℕ) (A : Finset (PairQubit (N + 2)))
    (sigma : PairQubit (N + 2) → Bool) (t : ℝ) :
    let D := unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t
    ‖D (cutFourConfig A sigma false false) (cutFourConfig A sigma false false) *
          D (cutFourConfig A sigma true true) (cutFourConfig A sigma true true) -
        D (cutFourConfig A sigma false true) (cutFourConfig A sigma false true) *
          D (cutFourConfig A sigma true false) (cutFourConfig A sigma true false)‖ =
      ‖Complex.exp (-(Complex.I *
        (t * (thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma false false) +
          thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma true true) -
          thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma false true) -
          thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma true false))))) - 1‖ := by
  dsimp only
  rw [unitaryEvolution_thermodynamicPairTailCenter_diagonal]
  simp only [Matrix.diagonal_apply_eq]
  exact norm_exp_four_energy_difference_eq_chord t _ _ _ _

/-- Every selector block carries a cut-oriented unit-circle chord larger than the complete shared
circuit-plus-Duhamel error budget. -/
theorem exists_thermodynamicPairTailCenter_cut_chord
    {N K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ N + 2)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100) (ht0 : 0 ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL)
    (hphaseLo : 3 * Real.pi * ε ≤ ∑ j ∈ S, inverseSquarePhaseWeight t j)
    (hphaseHi : ∑ j ∈ S, inverseSquarePhaseWeight t j ≤ 5 * Real.pi * ε) :
    ∃ sigma : PairQubit (N + 2) → Bool,
      4 * (73 * ε / 64) < ‖
        unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t
            (cutFourConfig (firstEndpointSites S) sigma false false)
            (cutFourConfig (firstEndpointSites S) sigma false false) *
          unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t
            (cutFourConfig (firstEndpointSites S) sigma true true)
            (cutFourConfig (firstEndpointSites S) sigma true true) -
        unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t
            (cutFourConfig (firstEndpointSites S) sigma false true)
            (cutFourConfig (firstEndpointSites S) sigma false true) *
          unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t
            (cutFourConfig (firstEndpointSites S) sigma true false)
            (cutFourConfig (firstEndpointSites S) sigma true false)‖ := by
  obtain ⟨sigma, hmixed⟩ := exists_thermodynamicPairTailCenterEnergy_cut_mixed
    N K (firstEndpointSites S)
  refine ⟨sigma, ?_⟩
  rw [thermodynamicPairTailCenter_four_chord_eq]
  have hmixedC :
      ((thermodynamicPairTailCenterEnergy N K
          (cutFourConfig (firstEndpointSites S) sigma false false) : ℂ) +
        (thermodynamicPairTailCenterEnergy N K
          (cutFourConfig (firstEndpointSites S) sigma true true) : ℂ) -
        (thermodynamicPairTailCenterEnergy N K
          (cutFourConfig (firstEndpointSites S) sigma false true) : ℂ) -
        (thermodynamicPairTailCenterEnergy N K
          (cutFourConfig (firstEndpointSites S) sigma true false) : ℂ)) =
        (thermodynamicPairTailCrossingWeight N K (firstEndpointSites S) : ℂ) := by
    exact_mod_cast hmixed
  rw [hmixedC]
  let phi := t * thermodynamicPairTailCrossingWeight N K (firstEndpointSites S)
  have hphiLo : 3 * Real.pi * ε ≤ phi :=
    time_mul_thermodynamicPairTailCrossingWeight_lower hKL ht0 S hSblock hphaseLo
  have hphiHi : phi < 5 * Real.pi * ε + ε / 4 :=
    time_mul_thermodynamicPairTailCrossingWeight_upper
      hK hKL hε ht0 hthi S hSblock hphaseHi
  have hphi0 : 0 ≤ phi := by
    have hp := Real.pi_pos
    nlinarith
  have hphipi : phi ≤ Real.pi := by
    have hp := Real.pi_pos
    have hpieps : Real.pi * ε ≤ Real.pi * (1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hεsmall (le_of_lt hp)
    have heps4 : ε / 4 ≤ (1 / 100 : ℝ) / 4 := by linarith
    have hpi3 := Real.pi_gt_three
    have : 5 * Real.pi * ε + ε / 4 < Real.pi := by nlinarith
    exact le_trans (le_of_lt hphiHi) (le_of_lt this)
  have hchordLo := phase_chord_lower hphi0 hphipi
  have hsix : 6 * ε ≤ 2 * phi / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    have hp := Real.pi_pos
    nlinarith
  have hphiC : (phi : ℂ) =
      (t : ℂ) * (thermodynamicPairTailCrossingWeight N K (firstEndpointSites S) : ℂ) := by
    dsimp [phi]
    push_cast
    rfl
  rw [← hphiC]
  have hbudget : 4 * (73 * ε / 64) < 6 * ε := by nlinarith
  exact hbudget.trans_le (hsix.trans hchordLo)

/-- **Selected thermodynamic path ramp law.**  Every support-certified circuit approximating the
literal finite evolution of the selected static nearest-neighbour field during shell `K` uses at
least `K` counted two-qubit gates. -/
theorem thermodynamicPairHamiltonian_twoGateCount_ge
    {N K : ℕ} (c : List (LocalGate (PairQubit (N + 2))))
    {p : InfinitePathLabel → ℝ} {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ N + 2)
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (htlo : 128 * Real.pi * ε * K ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (hclose : ‖circuitMatrix c -
      unitaryEvolution (thermodynamicPairHamiltonian N p) t‖ ≤ ε) :
    K ≤ twoGateCount c := by
  by_contra hnot
  have hcost : twoGateCount c < K := Nat.lt_of_not_ge hnot
  obtain ⟨S, hSblock, hSdisj, hphaseLo, hphaseHi⟩ :=
    circuit_exists_inverseSquare_phase_subset c hK hKL hε htlo hthi hcost
  have ht0 : 0 ≤ t := by
    have hbase : 0 ≤ 128 * Real.pi * ε * (K : ℝ) := by positivity
    exact hbase.trans htlo
  obtain ⟨sigma, hchord⟩ := exists_thermodynamicPairTailCenter_cut_chord
    hK hKL hε hεsmall ht0 hthi S hSblock hphaseLo hphaseHi
  obtain ⟨B, hBunit, hPrefix⟩ :=
    exists_offMatrixLift_thermodynamicPairPrefixEvolution p t hKL hSblock
  let D := unitaryEvolution (thermodynamicPairTailCenterHamiltonian N K) t
  let Tref := unitaryEvolution (thermodynamicPairMobileReference N K p) t
  have hTref : Tref = offMatrixLift (firstEndpointSites S) B * D := by
    dsimp only [Tref, D]
    rw [unitaryEvolution_thermodynamicPairMobileReference, hPrefix]
  have hsize : 4 * K ≤ N * 2 + 3 := by omega
  have hthiMobile : t < 256 * Real.pi * ε * (K + 1) := by
    have hnonneg : 0 ≤ Real.pi * ε * ((K : ℝ) + 1) := by positivity
    nlinarith
  have hmobile :=
    norm_unitaryEvolution_thermodynamicPair_sub_mobileReference_lt_nine_sixtyfourths
      hK hsize hp hε ht0 hthiMobile
  have hcloseRef : ‖circuitMatrix c - Tref‖ ≤ 73 * ε / 64 := by
    have htriangle : ‖circuitMatrix c - Tref‖ ≤
        ‖circuitMatrix c - unitaryEvolution (thermodynamicPairHamiltonian N p) t‖ +
          ‖unitaryEvolution (thermodynamicPairHamiltonian N p) t - Tref‖ := by
      rw [show circuitMatrix c - Tref =
        (circuitMatrix c - unitaryEvolution (thermodynamicPairHamiltonian N p) t) +
          (unitaryEvolution (thermodynamicPairHamiltonian N p) t - Tref) by abel]
      exact norm_add_le _ _
    have hstrict :
        ‖circuitMatrix c - unitaryEvolution (thermodynamicPairHamiltonian N p) t‖ +
            ‖unitaryEvolution (thermodynamicPairHamiltonian N p) t - Tref‖ <
          ε + 9 * ε / 64 := add_lt_add_of_le_of_lt hclose hmobile
    have : ‖circuitMatrix c - Tref‖ < 73 * ε / 64 := by
      calc
        ‖circuitMatrix c - Tref‖ ≤ _ := htriangle
        _ < ε + 9 * ε / 64 := hstrict
        _ = 73 * ε / 64 := by ring
    exact this.le
  have hDnorm : ∀ a b : Bool,
      ‖D (cutFourConfig (firstEndpointSites S) sigma a b)
        (cutFourConfig (firstEndpointSites S) sigma a b)‖ = 1 := by
    intro a b
    dsimp only [D]
    rw [unitaryEvolution_thermodynamicPairTailCenter_diagonal]
    simp [Complex.norm_exp]
  exact false_of_mobilePrefix_cutFourPhaseWitness c hSdisj hcloseRef
    hBunit hTref hDnorm hchord

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
