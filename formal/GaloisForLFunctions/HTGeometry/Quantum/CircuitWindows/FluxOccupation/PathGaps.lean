import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryCount
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-! # Deterministic lower flux and upper phase speed from Pauli coefficients -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section
open EmptyVisitFlux

/-- The sum of absolute couplings bounds every energy in magnitude. -/
theorem path_abs_energy {n : ℕ} (u : PathShell n) (i : Fin (n+2) → Bool) :
    |(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i| ≤ ∑ l : PathLabel n, |u l| := by
  apply (abs_eigenvalue_le_l2_opNorm (isSelfAdjoint_pathHamiltonian u).isHermitian i).trans
  rw [pathHamiltonian_eq_sum]
  refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun l _ => ?_)
  rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]

/-- The mass cancels between the entry flux and the length of a
one-step product-formula interval. The estimate holds for every path. -/
theorem path_pair_turn_lower {n : ℕ} (u : PathShell n) :
    let D : ℕ := 2^(n+2)
    let J := Fintype.card (PathLabel n)
    let M := ∑ l : PathLabel n, |u l|
    let E := fun j => -(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j
    (D:ℝ)^2*M ≤ 4*π*(J:ℝ)*pairTurnRate E := by
  intro D J M E
  let V := ∑ l : PathLabel n, (u l)^2
  let S := ∑ p : (Fin (n+2) → Bool)×(Fin (n+2) → Bool), max 0 (E p.1-E p.2)
  obtain ⟨ht,hv⟩ := path_spectral_moments u
  have hzero : ∑ j, E j=0 := by simp only [E,Finset.sum_neg_distrib,ht,neg_zero]
  have hsq : ∑ j, E j^2=(D:ℝ)*V := by simpa only [E,neg_sq] using hv
  have hb (i j) : E i-E j ≤ 2*M := by
    have hi := (abs_le.mp (path_abs_energy u i)).1
    have hj := (abs_le.mp (path_abs_energy u j)).2
    dsimp only [E]
    linarith only [hi,hj]
  have h := centered_gap_mass E hzero hb
  rw [hsq,show Fintype.card (Fin (n+2) → Bool)=D by simp [D]] at h
  change (D:ℝ)*((D:ℝ)*V) ≤ 2*M*S at h
  have hs : M^2 ≤ (J:ℝ)*V := sq_sum_abs_le_card_mul_sum_sq _
  have he : pairTurnRate E = S/(2*π) := by rw [pairTurnRate,←Finset.sum_div]
  rw [he,show 4*π*(J:ℝ)*(S/(2*π))=2*(J:ℝ)*S by field_simp; ring]
  have hM : 0≤M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rcases eq_or_lt_of_le hM with h0 | hp
  · rw [←h0,mul_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  apply le_of_mul_le_mul_left _ hp
  calc
    M*((D:ℝ)^2*M) = (D:ℝ)^2*M^2 := by ring
    _ ≤ (D:ℝ)^2*((J:ℝ)*V) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = (J:ℝ)*((D:ℝ)*((D:ℝ)*V)) := by ring
    _ ≤ (J:ℝ)*(2*M*S) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = M*(2*(J:ℝ)*S) := by ring

/-- Every spectral velocity is within M/(2π) of zero. -/
theorem path_velocity_width {n : ℕ} (u : PathShell n) :
    let M := ∑ l : PathLabel n, |u l|
    let w := fun j => -(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j/(2*π)
    Finset.univ.sup' Finset.univ_nonempty w-Finset.univ.inf' Finset.univ_nonempty w ≤ M/π := by
  intro M w
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty w
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty w
  rw [hi,hj]
  have ha := abs_le.mp (path_abs_energy u i)
  have hb := abs_le.mp (path_abs_energy u j)
  dsimp only [w]
  rw [←sub_div,show M/π=2*M/(2*π) by field_simp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith only [ha.1,hb.2]

#print axioms path_pair_turn_lower
#print axioms path_velocity_width
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
