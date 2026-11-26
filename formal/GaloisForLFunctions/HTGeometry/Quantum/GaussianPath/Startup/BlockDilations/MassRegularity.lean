import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.IdealCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PacketMass

/-! # Forcing regular local rotations from total physical disorder mass -/

open Finset Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {I : Type*} [Fintype I] {n : ℕ}

/-- The total longitudinal mass is controlled by the number of packets
whose rotation fails one of the two sparse fits. High-energy packets
are charged collectively against the full squared coefficient norm. -/
theorem regular_mass_bound (R : I→Finset (Fin (n+2)))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j))) (u : PathShell n)
    (L r : ℕ) (hL : ∀ i, (R i).card≤L) {m C h e : ℝ}
    (hm : 0 ≤ m) (hC : 0 < C) (hh : 0≤h) (hc : π≤2*h*m)
    (he : 2*e+h*C*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1) :
    open Classical in
    let G := univ.filter fun i => regularPacket (R i) u h e r
    ∑ i, longitudinal (R i) u ≤ Fintype.card I*m+G.card*(sqrt L*C)+sqrt L/C*‖u‖^2 := by
  classical
  intro G
  let B := univ.filter fun i => m≤longitudinal (R i) u ∧ ‖pathShellOnSites (R i) u‖≤C
  have hsub : B⊆G := by
    intro i hi
    obtain ⟨hiL,hiC⟩ := (mem_filter.mp hi).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_⟩
    · rw [restricted_longitudinal]
      exact hc.trans (mul_le_mul_of_nonneg_left hiL (mul_nonneg zero_le_two hh))
    · apply lt_of_le_of_lt (add_le_add le_rfl ?_) he
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hiC hh) (by positivity)
  have hbd := longitudinal_mass_forces_packets R hR u L hL hm hC
  exact hbd.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (card_le_card hsub)) (mul_nonneg (sqrt_nonneg _) hC.le))) le_rfl)

#print axioms regular_mass_bound
end
end GaloisForLFunctions.HTGeometry.BlockDilations
