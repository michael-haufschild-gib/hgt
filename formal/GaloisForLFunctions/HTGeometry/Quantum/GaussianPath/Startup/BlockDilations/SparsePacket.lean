import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound

/-! # Detecting a local rotation in the presence of arbitrary exterior gates -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- A nonidentity Pauli word cannot lie in two disjoint packets. -/
theorem packet_support_intersects {n : ℕ} {R T : Finset (Fin (n+2))} {l : PathLabel n}
    (hR : PathWordSupportedIn R l) (hT : PathWordSupportedIn T l) : ¬Disjoint R T := by
  intro hd
  apply pathWord_ne_identity l
  funext v
  by_cases hv : v∈R
  · exact hT v (fun h => Finset.disjoint_left.mp hd hv h)
  · exact hR v hv

private theorem restrict_inter {n : ℕ} (R T : Finset (Fin (n+2))) (u : PathShell n) :
    pathHamiltonianOnSites T (pathShellOnSites R u) = pathHamiltonianOnSites (R∩T) u := by
  apply Finset.sum_congr rfl
  intro l _
  have he : PathWordSupportedIn (R∩T) l ↔ PathWordSupportedIn R l ∧ PathWordSupportedIn T l := by
    constructor
    · intro h
      exact ⟨fun v hv => h v (fun hx => hv (Finset.mem_inter.mp hx).1),
        fun v hv => h v (fun hx => hv (Finset.mem_inter.mp hx).2)⟩
    · rintro ⟨hR,hT⟩ v hv
      by_cases h : v∈R
      · exact hT v (fun h' => hv (Finset.mem_inter.mpr ⟨h,h'⟩))
      · exact hR v h
  by_cases hR : PathWordSupportedIn R l <;> by_cases hT : PathWordSupportedIn T l <;>
    simp [pathShellOnSites,he,hR,hT]

/-- A fit on an arbitrary set of wires yields a scalar fit on a packet.
Only wires in their intersection enter the penalty. The fit can use
all remaining wires, at arbitrary depth. -/
theorem packet_scalar_comparison {n : ℕ} (R S : Finset (Fin (n+2))) (u : PathShell n)
    (C : Reg (n+2)) (hC : IsSiteSupported S C) (t : ℝ) :
    let H := pathHamiltonianOnSites R u
    ∃ z : ℂ, ‖unitaryEvolution H t - z • (1 : Reg (n+2))‖ ≤
      ‖unitaryEvolution H t-C‖ +
        2*|t| *(sqrt (21*((R∩S).card:ℝ))*‖pathShellOnSites R u‖) := by
  intro H
  let v := pathShellOnSites R u
  let J := R∩S
  let K := pathHamiltonianOnSites Jᶜ v
  have hdis : Disjoint (R∩Jᶜ) S := Finset.disjoint_left.mpr fun i hi hs =>
    (Finset.mem_compl.mp (Finset.mem_inter.mp hi).2) (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,hs⟩)
  have hK : IsSiteSupported (R∩Jᶜ) K := by
    rw [show K=pathHamiltonianOnSites (R∩Jᶜ) u from restrict_inter R Jᶜ u]
    exact pathHamiltonianOnSites_isSiteSupported _ _
  obtain ⟨z,hz⟩ := truncated_local_evolution_scalar_bound hdis
    ⟨H,isSelfAdjoint_pathHamiltonianOnSites R u⟩ ⟨K,isSelfAdjoint_pathHamiltonianOnSites _ _⟩ hK C hC t
  have hsq := path_idle_deletion_norm_sq J v
  have hb : ‖H-K‖≤ sqrt (21*(J.card:ℝ))*‖v‖ := by
    rw [show H=pathHamiltonian v from pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites R u]
    have hh := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),Real.sqrt_mul (by positivity),Real.sqrt_sq (norm_nonneg _)] at hh
  exact ⟨z,hz.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by positivity)))⟩

/-- A packet's spectral chord detects the number of its wires used by
any approximant. The two selected energies may be anywhere in its
spectrum and the test applies at every real time. -/
theorem packet_chord_floor {n : ℕ} (R S : Finset (Fin (n+2))) (u : PathShell n)
    (C : Reg (n+2)) (hC : IsSiteSupported S C) (i j : Fin (n+2) → Bool) (t : ℝ) :
    let H := pathHamiltonianOnSites R u
    let E := (isSelfAdjoint_pathHamiltonianOnSites R u).isHermitian.eigenvalues
    ‖anchorPhase E i t - anchorPhase E j t‖ ≤
      2*(‖unitaryEvolution H t-C‖ +
        2*|t| *(sqrt (21*((R∩S).card:ℝ))*‖pathShellOnSites R u‖)) := by
  intro H E
  obtain ⟨z,hz⟩ := packet_scalar_comparison R S u C hC t
  have hH := (isSelfAdjoint_pathHamiltonianOnSites R u).isHermitian
  have hi := (spectral_point_scalar_error_le hH i t z).trans hz
  have hj := (spectral_point_scalar_error_le hH j t z).trans hz
  have he := norm_sub_le_norm_sub_add_norm_sub (anchorPhase E i t) z (anchorPhase E j t)
  rw [norm_sub_rev z] at he
  exact he.trans ((add_le_add hi hj).trans_eq (two_mul _).symm)

#print axioms packet_scalar_comparison
#print axioms packet_chord_floor
end
end GaloisForLFunctions.HTGeometry.BlockDilations
