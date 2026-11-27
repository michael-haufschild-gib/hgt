import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.IsolatedControls.BranchComparison
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.LongitudinalWord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.LongitudinalSpins.ProbeShift

/-! # A physical pulse interchanges transverse branches of a nearly isolated spin -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls
open private packet_sum fieldAt from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.LongitudinalWord
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where

private theorem spin_supported {n : ℕ} (s : Fin (n+2)) (a : Fin 3) :
    IsSiteSupported {s} (finitePauliMatrix (onsiteWord s a)) := by
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro j hj
  simp only [onsiteWord,if_neg (show j≠s from fun e => hj (Finset.mem_singleton.mpr e))]

/-- At the longitudinal quarter-turn there is an exact interchange of
the transverse branches within the physical Duhamel error. -/
theorem isolated_interchange {n : ℕ} (u : PathShell n) (s : Fin (n+2))
    {q η : ℝ} (hq : 0<q) (hη : 0≤η) (hs : isolatedLongitudinalSite u q η s) :
    let P := pauliControlProjection (onsiteWord s 0) true
    let T := unitaryEvolution (pathHamiltonian u) (π/(2*q))
    let X := finitePauliMatrix (onsiteWord s 0)
    ∃ V ∈ unitary (Reg n), V*P=(1-P)*V ∧ V*X= -(X*V) ∧ ‖V-T‖ ≤ π/(2*q)*(21*η) := by
  let S : Finset (Fin (n+2)) := {s}
  let K := pathHamiltonianOnSites Sᶜ u
  let X := finitePauliMatrix (onsiteWord s 0)
  let Z := finitePauliMatrix (onsiteWord s 2)
  let J := K+(q:ℂ) • Z
  let a := π/(2*q)
  let V := unitaryEvolution J a
  have ha : 0<a := div_pos pi_pos (by positivity)
  have hK := pathHamiltonianOnSites_isSiteSupported Sᶜ u
  have hcod := commute_of_isSiteSupported_disjoint disjoint_compl_left hK (spin_supported s 2)
  have hcx := commute_of_isSiteSupported_disjoint disjoint_compl_left (isSiteSupported_unitaryEvolution hK a)
    (spin_supported s 0)
  have hsgn : finitePauliConjugationSign (onsiteWord s 2) (onsiteWord s 0)= -1 := by
    rw [show onsiteWord s 2=singlePauliAxisLabel s 2 from rfl,finitePauliConjugationSign_singlePauliAxisLabel]
    norm_num [onsiteWord,boolPauliConjugationSign]
  have hB := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonianOnSites Sᶜ u) a
  have hJ : J=K+pathHamiltonian (longitudinalPacket S q) := by
    rw [packet_sum]
    simp only [S,Finset.sum_singleton,fieldAt,J,Z]
  have hself : IsSelfAdjoint J := by
    rw [hJ]
    exact (isSelfAdjoint_pathHamiltonianOnSites _ _).add (isSelfAdjoint_pathHamiltonian _)
  have hV := unitaryEvolution_mem_unitary hself a
  have hsft := LongitudinalSpins.longitudinal_sign (onsiteWord s 2) (onsiteWord s 0) K hcod hsgn ha.ne' 0
  have hqa : π/(2*a)=q := by dsimp only [a]; field_simp [pi_ne_zero]
  have hconj : V*X*star V= -X := by
    dsimp only at hsft
    rw [zero_add,hqa,Complex.ofReal_zero,zero_smul,add_zero,hcx.eq,mul_assoc,(Unitary.mem_iff.mp hB).2,mul_one] at hsft
    exact hsft
  have hanti : V*X= -(X*V) := by
    calc
      V*X = (V*X*star V)*V := by rw [mul_assoc (V*X),(Unitary.mem_iff.mp hV).1,mul_one]
      _ = _ := by rw [hconj,neg_mul]
  let P := pauliControlProjection (onsiteWord s 0) true
  have hcompl : 1-P=pauliControlProjection (onsiteWord s 0) false := by
    rw [←pauliControlProjection_add (onsiteWord s 0)]
    exact add_sub_cancel_right ..
  have hflip : V*P=(1-P)*V := by
    rw [hcompl]
    change V*((1/2:ℂ) • (1-X))=((1/2:ℂ) • (1+X))*V
    rw [Matrix.mul_smul,Matrix.smul_mul,mul_sub,add_mul,mul_one,one_mul,hanti,sub_neg_eq_add]
  have hd := isolated_field_replacement_error u S q η hη (fun i hi => (Finset.mem_singleton.mp hi) ▸ hs)
  have he := norm_unitaryEvolution_sub_le J (pathHamiltonian u) hself (isSelfAdjoint_pathHamiltonian _) a
  have hdJ : ‖J-pathHamiltonian u‖ ≤ 21*η := by
    rw [norm_sub_rev,hJ]
    simpa only [S,Finset.card_singleton,Nat.cast_one,mul_one] using hd
  rw [abs_of_pos ha] at he
  exact ⟨V,hV,hflip,hanti,he.trans (mul_le_mul_of_nonneg_left hdJ ha.le)⟩

theorem pulse_commutes {n : ℕ} (u : PathShell n) (a t : ℝ) (z : ℂ) :
    Commute (unitaryEvolution (pathHamiltonian u) a) (z • unitaryEvolution (pathHamiltonian u) t) := by
  let L := (-Complex.I) • pathHamiltonian u
  exact ((((Commute.refl L).smul_left a).smul_right t).exp).smul_right z

/-- Testing a controlled operator against any physical date costs only
the perturbation during the short interchange. -/
theorem isolated_branch_distance {n : ℕ} (u : PathShell n) (s : Fin (n+2))
    {q η : ℝ} (hq : 0<q) (hη : 0≤η) (hs : isolatedLongitudinalSite u q η s)
    (W : Reg n) (hW : ‖W‖≤1)
    (hfix : W*pauliControlProjection (onsiteWord s 0) false=pauliControlProjection (onsiteWord s 0) false)
    (z : ℂ) (t : ℝ) :
    ‖W-1‖/2 ≤ ‖W-z • unitaryEvolution (pathHamiltonian u) t‖+π/(2*q)*(21*η) := by
  let P := pauliControlProjection (onsiteWord s 0) true
  let X := finitePauliMatrix (onsiteWord s 0)
  have hcompl : 1-P=pauliControlProjection (onsiteWord s 0) false := by
    rw [←pauliControlProjection_add (onsiteWord s 0)]
    exact add_sub_cancel_right ..
  have hp : ‖P‖ ≤ 1 := by
    change ‖(1/2:ℂ) • (1-X)‖ ≤ _
    rw [norm_smul,norm_div,norm_one,Complex.norm_ofNat]
    have hh := norm_sub_le (1:Reg n) X
    rw [norm_one,show ‖X‖=1 from norm_finitePauliMatrix _] at hh
    linarith only [hh]
  obtain ⟨V,hV,hflip,_,herr⟩ := isolated_interchange u s hq hη hs
  have ht := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) (π/(2*q))
  exact (controlled_distance hp hV hflip (by rwa [hcompl]) hW (CStarRing.norm_of_mem_unitary ht).le
    (pulse_commutes u _ t z)).trans (add_le_add_left herr _)

#print axioms isolated_branch_distance
end
end GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls
