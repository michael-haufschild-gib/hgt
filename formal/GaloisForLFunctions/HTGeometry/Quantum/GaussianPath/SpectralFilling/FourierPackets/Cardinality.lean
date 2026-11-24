import GaloisForLFunctions.HTGeometry.PeriodicTentMultiplicativeWindowLaw

/-! # Number of nonconstant product Fejér sheets -/
namespace GaloisForLFunctions.HTGeometry

/-- Each phase coordinate contributes a pair of Fourier indices between zero and the cutoff. -/
theorem nonconstant_phase_packet_card_le (M d : ℕ) : (nonconstantPacketIndexSet M d).card ≤ (M+1)^(2*d) := by
  apply (Finset.card_le_card (Finset.sdiff_subset : nonconstantPacketIndexSet M d ⊆ _)).trans_eq
  simp only [Fintype.card_piFinset,Finset.card_product,Finset.card_range,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← sq,← pow_mul]

end GaloisForLFunctions.HTGeometry
