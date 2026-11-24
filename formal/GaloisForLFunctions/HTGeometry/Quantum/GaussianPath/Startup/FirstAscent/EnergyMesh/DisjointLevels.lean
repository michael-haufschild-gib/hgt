import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum

/-! # Joint energies of disjoint supported operators -/

open Matrix Set
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Any level of one packet and any level of a disjoint packet occur
together in the spectrum of their sum. -/
theorem disjoint_sum_level {N : ℕ} {S T : Finset (Fin N)} (hd : Disjoint S T)
    {X Y : Reg N} (hX : IsSiteSupported S X) (hY : IsSiteSupported T Y)
    (hx : X.IsHermitian) (hy : Y.IsHermitian) (i j : Fin N→Bool) :
    ∃ k, (hx.add hy).eigenvalues k=hx.eigenvalues i+hy.eigenvalues j := by
  classical
  obtain ⟨B,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hX
  obtain ⟨C,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hY
  have hb := isHermitian_of_isHermitian_liftLocalMatrix S hx
  have hc := isHermitian_of_isHermitian_liftLocalMatrix T hy
  have hi : hx.eigenvalues i ∈ range hb.eigenvalues :=
    range_eigenvalues_liftLocalMatrix S hb ▸ mem_range_self i
  have hj : hy.eigenvalues j ∈ range hc.eigenvalues :=
    range_eigenvalues_liftLocalMatrix T hc ▸ mem_range_self j
  obtain ⟨a,ha⟩ := hi
  obtain ⟨b,hb'⟩ := hj
  change _ ∈ range (hx.add hy).eigenvalues
  rw [range_eigenvalues_add_liftLocalMatrix_disjoint hd hb hc (hx.add hy)]
  exact ⟨(a,b),congrArg₂ (·+·) ha hb'⟩

end
end GaloisForLFunctions.HTGeometry.FirstAscent
