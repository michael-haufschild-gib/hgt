import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Energy widths under perturbations and disjoint sums -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Perturbing a Hamiltonian in operator norm moves its energy diameter by
at most twice the perturbation. -/
theorem width_perturb {N : ℕ} (H K : selfAdjoint (Reg N)) :
    circuitHamiltonianSpectralWidth K ≤ circuitHamiltonianSpectralWidth H+2*‖K.val-H.val‖ := by
  obtain ⟨c,hc,_⟩ := exists_optimal_scalarCenteredHamiltonian H
  obtain ⟨_,_,hk⟩ := exists_optimal_scalarCenteredHamiltonian K
  have h := norm_sub_le_norm_sub_add_norm_sub K.val H.val ((c:ℂ) • 1)
  change ‖(scalarCenteredHamiltonian K c).val‖ ≤ ‖K.val-H.val‖+
    ‖(scalarCenteredHamiltonian H c).val‖ at h
  rw [hc] at h
  linarith only [h,hk c]

/-- The energy diameter is subadditive, by centering each summand at its
own optimal scalar. -/
theorem width_add_le {N : ℕ} (H K : selfAdjoint (Reg N)) :
    circuitHamiltonianSpectralWidth (H+K) ≤
      circuitHamiltonianSpectralWidth H+circuitHamiltonianSpectralWidth K := by
  obtain ⟨a,ha,_⟩ := exists_optimal_scalarCenteredHamiltonian H
  obtain ⟨b,hb,_⟩ := exists_optimal_scalarCenteredHamiltonian K
  obtain ⟨_,_,hmin⟩ := exists_optimal_scalarCenteredHamiltonian (H+K)
  have he : (scalarCenteredHamiltonian (H+K) (a+b)).val =
      (scalarCenteredHamiltonian H a).val+(scalarCenteredHamiltonian K b).val := by
    change H.val+K.val-(((a+b:ℝ):ℂ) • 1)=(H.val-((a:ℂ) • 1))+(K.val-((b:ℂ) • 1))
    rw [Complex.ofReal_add,add_smul]
    abel
  have hh := hmin (a+b)
  rw [he] at hh
  have hl := norm_add_le (scalarCenteredHamiltonian H a).val (scalarCenteredHamiltonian K b).val
  rw [ha,hb] at hl
  linarith only [hh,hl]

private theorem sum_level {N : ℕ} {S T : Finset (Fin N)} (hd : Disjoint S T)
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

/-- The extreme energy gaps of disjoint registers can be realized
simultaneously. -/
theorem width_disjoint_sum_lower {N : ℕ} {S T : Finset (Fin N)} (hd : Disjoint S T)
    (H K : selfAdjoint (Reg N)) (hH : IsSiteSupported S H.val) (hK : IsSiteSupported T K.val) :
    circuitHamiltonianSpectralWidth H+circuitHamiltonianSpectralWidth K ≤
      circuitHamiltonianSpectralWidth (H+K) := by
  let E := H.2.isHermitian.eigenvalues
  let F := K.2.isHermitian.eigenvalues
  let G := (H+K).2.isHermitian.eigenvalues
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty E
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty E
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty F
  obtain ⟨d,_,hd'⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty F
  obtain ⟨u,hu⟩ := sum_level hd hH hK H.2.isHermitian K.2.isHermitian a c
  obtain ⟨v,hv⟩ := sum_level hd hH hK H.2.isHermitian K.2.isHermitian b d
  change G u=E a+F c at hu
  change G v=E b+F d at hv
  change (Finset.univ.sup' _ E-Finset.univ.inf' _ E)+(Finset.univ.sup' _ F-Finset.univ.inf' _ F) ≤
    Finset.univ.sup' _ G-Finset.univ.inf' _ G
  rw [ha,hb,hc,hd']
  linarith only [Finset.le_sup' G (Finset.mem_univ u),Finset.inf'_le G (Finset.mem_univ v),hu,hv]

/-- Energy diameter adds exactly under a disjoint sum. -/
theorem width_disjoint_sum {N : ℕ} {S T : Finset (Fin N)} (hd : Disjoint S T)
    (H K : selfAdjoint (Reg N)) (hH : IsSiteSupported S H.val) (hK : IsSiteSupported T K.val) :
    circuitHamiltonianSpectralWidth (H+K) =
      circuitHamiltonianSpectralWidth H+circuitHamiltonianSpectralWidth K :=
  le_antisymm (width_add_le H K) (width_disjoint_sum_lower hd H K hH hK)

#print axioms width_disjoint_sum
end
end GaloisForLFunctions.HTGeometry.FirstAscent
