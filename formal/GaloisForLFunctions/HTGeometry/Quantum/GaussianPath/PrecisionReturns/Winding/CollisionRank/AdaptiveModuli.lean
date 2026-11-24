import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.FirstDivisors
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.ResidueForest

/-! # Rank bound uniform over the moduli of a physical first return -/

open Filter Set MeasureTheory Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- A modulus of precision exponent h must distinguish at least D−n−1
nonzero winding residues whenever h exceeds (D−2−n)/(n+1). The winding,
partition and modulus may all be selected at the observed return. -/
theorem gaussian_adaptive_modulus_rank :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∃ A > (0:ℝ), ∀ a > (0:ℝ), ∀ s : ℕ, s+1 < N → ∀ n : ℕ, 0 < n → n+2 ≤ D →
        ∀ h : ℝ, (((D-2:ℕ):ℝ)-(n:ℝ))/((n:ℝ)+1)<h →
        ∀ᶠ ε in 𝓝[>] (0:ℝ),
          let t := firstVisit H a s ε
          let R := physicalArc (A*ε)
          (∃ b z, Anchored w t R b z) ∧
            ∀ b z, Anchored w t R b z → ∀ d : ℕ, 0<d → h ≤ log (d:ℝ)/log (1/ε) →
              D ≤ (residues z d).card+n+1 := by
  classical
  filter_upwards [gaussian_first_divisor_exponent] with ω hω k
  intro N D H w
  obtain ⟨A,hA,hh⟩ := hω k
  refine ⟨A,hA,?_⟩
  intro a ha s hs n hn hsize h hexp
  let I := Fin N → Bool
  have hI : Fintype.card I = D := by simp [I,D]
  let valid (leaf root : Fin (n+1) → I) := Function.Injective leaf ∧ ∀ i j, root i ≠ leaf j
  let P (ε : ℝ) (leaf root : Fin (n+1) → I) :=
    let t := firstVisit H a s ε
    let R := physicalArc (A*ε)
    (∃ b z, Anchored w t R b z) ∧ ∀ b z, Anchored w t R b z → ∀ d : ℕ, 0<d →
      (∀ i, (d:ℤ) ∣ z (leaf i)-z (root i)) → log (d:ℝ)/log (1/ε)<h
  have hall (leaf root : Fin (n+1) → I) :
      ∀ᶠ ε in 𝓝[>] (0:ℝ), valid leaf root → P ε leaf root := by
    by_cases hv : valid leaf root
    · exact (hh a ha s hs n hn leaf root hv.1 hv.2 h hexp).mono fun _ hp _ => hp
    · exact Filter.Eventually.of_forall fun _ hv' => (hv hv').elim
  have hzero : (residues (fun _ : I => (0:ℤ)) 1).card=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx',hm⟩ := Finset.mem_erase.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
    exact hx' (by simp)
  obtain ⟨l₀,r₀,hi₀,hd₀,_⟩ := exists_residue_forest (fun _ : I => (0:ℤ)) 1 (n+1)
    (by rw [hzero,hI]; omega)
  filter_upwards [eventually_all.mpr (fun l => eventually_all.mpr (hall l))] with ε hε
  intro t R
  refine ⟨(hε l₀ r₀ ⟨hi₀,hd₀⟩).1,?_⟩
  intro b z hz d hd hmod
  by_contra! hfew
  obtain ⟨l,r,hi,hr,he⟩ := exists_residue_forest z d (n+1) (by rw [hI]; omega)
  exact (hε l r ⟨hi,hr⟩).2 b z hz d hd he |>.not_ge hmod

#print axioms gaussian_adaptive_modulus_rank
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
