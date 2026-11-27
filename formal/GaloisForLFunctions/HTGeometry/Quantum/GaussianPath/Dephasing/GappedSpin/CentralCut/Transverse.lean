import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.PacketSplit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.Propagator
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliNoncontextualCircuit
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich

/-! # Removing transverse Pauli coefficients at one physical site -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section
variable {n : ℕ}

def axial (q : Fin (n+2)) (l : PathLabel n) : Prop :=
  pathWord l q=none ∨ pathWord l q=some 2

abbrev core (q : Fin (n+2)) := restricted (axial q)
abbrev offAxis (q : Fin (n+2)) := restricted (fun l => ¬axial q l)
abbrev spin (q : Fin (n+2)) := finitePauliMatrix (onsiteWord q 2)

theorem core_longitudinal (q : Fin (n+2)) (u : PathShell n) : longitudinalAt q (core q u) := by
  classical
  intro l hl
  by_contra h
  exact hl (restricted_zero (P:=axial q) u h)

private theorem spin_commute_iff (q : Fin (n+2)) (l : PathLabel n) :
    Commute (spin q) (finitePauliMatrix (pathWord l)) ↔ axial q l := by
  rw [finitePauli_commute_iff_sign]
  change finitePauliConjugationSign (singlePauliAxisLabel q 2) (pathWord l)=1 ↔ _
  rw [finitePauliConjugationSign_singlePauliAxisLabel]
  by_cases h : axial q l
  · rcases h with h|h <;> simp [h,axial,boolPauliConjugationSign]
  · have he := not_or.mp h
    simp [axial,boolPauliConjugationSign,he.1,he.2,Ne.symm he.2,neg_ne_self.mpr (one_ne_zero : (1:ℂ)≠0)]

private theorem spin_core (q : Fin (n+2)) (u : PathShell n) :
    Commute (spin q) (pathHamiltonian (core q u)) := by
  classical
  rw [pathHamiltonian_eq_sum]
  apply Commute.sum_right
  intro l _
  by_cases h : axial q l
  · rw [restricted_eq u h]
    exact ((spin_commute_iff q l).mpr h).smul_right _
  · rw [restricted_zero u h,Complex.ofReal_zero,zero_smul]
    exact Commute.zero_right _

private theorem spin_offAxis (q : Fin (n+2)) (u : PathShell n) :
    spin q*pathHamiltonian (offAxis q u)=-(pathHamiltonian (offAxis q u)*spin q) := by
  classical
  rw [pathHamiltonian_eq_sum,mul_sum,sum_mul,←sum_neg_distrib]
  apply sum_congr rfl
  intro l _
  by_cases h : axial q l
  · have hz : (offAxis q u) l=0 := restricted_zero (P:=fun x => ¬axial q x) u (not_not_intro h)
    rw [hz,Complex.ofReal_zero,zero_smul,mul_zero,zero_mul,neg_zero]
  · have ha := finitePauliMatrix_anticommute_of_not_commute (onsiteWord q 2) (pathWord l)
      (fun hc => h ((spin_commute_iff q l).mp hc))
    change spin q * finitePauliMatrix (pathWord l) = -(finitePauliMatrix (pathWord l) * spin q) at ha
    rw [mul_smul_comm,smul_mul_assoc,ha,smul_neg]

/-- Longitudinal terms enter the gap. Only the transverse part pays
the error growing with time, and its contribution there is quadratic. -/
theorem core_evolution_bound (q : Fin (n+2)) (u : PathShell n) (h : ℝ)
    (hg : ‖pathHamiltonian (core q u)-h • spin q‖<h) (t : ℝ) :
    let V := pathHamiltonian (offAxis q u)
    let W := pathHamiltonian (core q u)-h • spin q
    ‖unitaryEvolution (pathHamiltonian u) t-unitaryEvolution (pathHamiltonian (core q u)) t‖ ≤
      (2+|t| * ‖V‖)*(‖V‖/(2*(h-‖W‖))) := by
  intro V W
  letI : CStarAlgebra (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) := {}
  have hz := (finitePauliMatrix_isHermitian (onsiteWord q 2)).isSelfAdjoint
  have hsum : h • spin q+W=pathHamiltonian (core q u) := by dsimp only [W]; abel
  have hself : IsSelfAdjoint (h • spin q) := by
    change star (h • spin q)=h • spin q
    rw [star_smul,star_trivial,hz.star_eq]
  have hc := (spin_core q u).sub_right ((Commute.refl (spin q)).smul_right h)
  have he := transverse_evolution (spin q) W V hz ((isSelfAdjoint_pathHamiltonian _).sub hself)
    (isSelfAdjoint_pathHamiltonian _) (finitePauliMatrix_mul_self _) (norm_finitePauliMatrix _).le
    hc.eq (spin_offAxis q u) hg t
  change ‖unitaryEvolution (h • spin q+W+V) t-unitaryEvolution (h • spin q+W) t‖≤_ at he
  rw [hsum,←sum_restricted (axial q) u] at he
  exact he

#print axioms core_evolution_bound
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
