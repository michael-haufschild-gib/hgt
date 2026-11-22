import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.ProjectedInteractions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.PhaseDistance
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Linear stability of scalar returns for all disconnected circuits -/
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section

private theorem conjugation_gap {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (U V K : Matrix d d ℂ) (hu : U∈unitary _) (hv : V∈unitary _) :
    ‖U*K*star U-V*K*star V‖ ≤ 2*‖K‖*‖U-V‖ := by
  have he : U*K*star U-V*K*star V=(U-V)*K*star U+V*K*star (U-V) := by
    rw [star_sub]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(U-V)*K*star U‖+‖V*K*star (U-V)‖ := norm_add_le _ _
    _ = ‖(U-V)*K‖+‖K*star (U-V)‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),mul_assoc V,
        CStarRing.norm_mem_unitary_mul _ hv]
    _ ≤ ‖U-V‖*‖K‖+‖K‖*‖U-V‖ := by
      simpa only [norm_star] using add_le_add (norm_mul_le (U-V) K) (norm_mul_le K (star (U-V)))
    _ = _ := by ring

private theorem one_cut {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) (r : Fin (n+2)→Bool)
    (hjoint : ∀ X : Register (n+2), Commute X (pathHamiltonian u) →
      Commute X (bondPart u (crossingEdges S)) → X=X r r • (1 : Register (n+2))) :
    ∃ A > (0:ℝ), ∀ U : Register (n+2), U∈unitary _ → Commute (pathHamiltonian u) U →
      ∀ C : TwoQubitCircuit (n+2),
      (∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S) →
      ∀ z : ℂ, ‖z‖=1 →
        ‖U-U r r • 1‖ ≤ A*‖U-z • C.eval.val‖ := by
  let H := pathHamiltonian u
  let W := bondPart u (crossingEdges S)
  let E := LinearMap.toContinuousLinearMap (cutProjection S)
  obtain ⟨K,hK,hbound⟩ := (UntouchedSites.scalar_commutant_iff_estimate r H (fun _ : Unit => W)).mp
    (fun X hH hW => hjoint X hH.symm (hW ()).symm)
  let L := 2*(‖E‖*‖H‖+‖W‖)
  refine ⟨1+K*L,by dsimp [L]; positivity,?_⟩
  intro U hU hH C hc z hz
  let V := z • C.eval.val
  let δ := ‖U-V‖
  have hphase : star z*z=1 := by
    simp [Complex.star_def,mul_comm (starRingEnd ℂ z) z,Complex.mul_conj',hz]
  have hV : V∈unitary (Register (n+2)) := by
    rw [Unitary.mem_iff]
    simp only [V,star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      (Unitary.mem_iff.mp C.eval.property).1,(Unitary.mem_iff.mp C.eval.property).2,hphase,
      mul_comm z (star z),one_smul,and_self]
  have unphase (M : Register (n+2)) : V*M*star V=C.eval.val*M*star C.eval.val := by
    simp only [V,star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hphase,
      mul_comm z (star z),one_smul]
  have hfix : U*H*star U=H := by rw [hH.symm.eq,mul_assoc,(Unitary.mem_iff.mp hU).2,mul_one]
  have h₁ : ‖H-V*H*star V‖ ≤ 2*‖H‖*δ := hfix ▸ conjugation_gap U V H hU hV
  have hmap : E (H-V*H*star V)=W-V*W*star V := by
    change cutProjection S (H-V*H*star V)=_
    rw [map_sub,unphase,cutProjection_circuit C S hc,projection_hamiltonian,unphase]
  have h₂ := E.le_opNorm (H-V*H*star V)
  rw [hmap] at h₂
  have h₃ := conjugation_gap V U W hV hU
  rw [norm_sub_rev V U] at h₃
  have hW : ‖W*U-U*W‖ ≤ L*δ := by
    have he : W*U-U*W=(W-U*W*star U)*U := by
      rw [sub_mul,mul_assoc (U*W),(Unitary.mem_iff.mp hU).1,mul_one]
    rw [he,CStarRing.norm_mul_mem_unitary _ hU]
    have hsum := norm_sub_le_norm_sub_add_norm_sub W (V*W*star V) (U*W*star U)
    dsimp only [L]
    nlinarith only [hsum,h₂,h₃,mul_le_mul_of_nonneg_left h₁ (norm_nonneg E)]
  have htest := hbound U
  rw [hH.eq,sub_self,norm_zero,max_eq_right (norm_nonneg _),pi_norm_const] at htest
  nlinarith only [htest,mul_le_mul_of_nonneg_left hW hK.le,norm_nonneg (U-V)]

/-- The only disconnected circuit symmetry of a generic Gaussian path is
scalar. Quantitatively, for every symmetry U, its distance to the scalar
line is controlled by its distance to any disconnected circuit. -/
theorem gaussian_cut_symmetry_stability :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      let r : Fin (n+2)→Bool := fun _ => false
      ∃ A > (0:ℝ), ∀ (S : Finset (Fin (n+2))), S.Nonempty → Sᶜ.Nonempty →
        ∀ U : Register (n+2), U∈unitary _ → Commute H U → ∀ C : TwoQubitCircuit (n+2),
        (∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S) →
        ∀ z : ℂ, ‖z‖=1 → ‖U-U r r • 1‖ ≤ A*‖U-z • C.eval.val‖ := by
  classical
  filter_upwards [gaussian_bond_joint_scalar] with ω hω n
  intro H r
  let u := pathPauliDisorderShell ω n
  have h (S : Finset (Fin (n+2))) : ∃ A > (0:ℝ), S.Nonempty → Sᶜ.Nonempty →
      ∀ U : Register (n+2), U∈unitary _ → Commute H U → ∀ C : TwoQubitCircuit (n+2),
        (∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S) →
        ∀ z : ℂ, ‖z‖=1 →
        ‖U-U r r • 1‖ ≤ A*‖U-z • C.eval.val‖ := by
    by_cases hs : S.Nonempty
    · by_cases ht : Sᶜ.Nonempty
      · obtain ⟨A,hA,hc⟩ := one_cut u S r (hω n _ (crossing_nonempty S hs ht))
        exact ⟨A,hA,fun _ _ => hc⟩
      · exact ⟨1,one_pos,fun _ h => (ht h).elim⟩
    · exact ⟨1,one_pos,fun h => (hs h).elim⟩
  choose K hK hcontrol using h
  let A := 1+∑ S, K S
  have hsum : 0≤∑ S, K S := Finset.sum_nonneg fun S _ => (hK S).le
  refine ⟨A,by dsimp [A]; linarith only [hsum],?_⟩
  intro S hS hT U hU hH C hcut z hz
  have hh := hcontrol S hS hT U hU hH C hcut z hz
  have hKA : K S≤A := by
    have h := Finset.single_le_sum (s:=Finset.univ) (fun j _ => (hK j).le) (Finset.mem_univ S)
    dsimp [A]; linarith only [h]
  exact hh.trans (mul_le_mul_of_nonneg_right hKA (norm_nonneg _))

/-- Below N−1 gates a disconnected cut always exists, including when
every qubit is touched. The comparison is simultaneous over all budgets. -/
theorem gaussian_disconnected_scalar_return :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∃ A > (0:ℝ), ∀ (t ε : ℝ) (s : ℕ), s<n+1 →
        HasProjectiveCircuitApproximation (n+2) ε s (unitaryEvolution H t) →
        HasProjectiveCircuitApproximation (n+2) (A*ε) 0 (unitaryEvolution H t) := by
  filter_upwards [gaussian_cut_symmetry_stability] with ω hω n
  intro H
  obtain ⟨A,hA,h⟩ := hω n
  refine ⟨2*A,mul_pos two_pos hA,?_⟩
  rintro t ε s hs ⟨z,hz,C,hC,he⟩
  obtain ⟨S,hS,hT,hcut⟩ := DisconnectedSpectra.circuit_cut C (by omega)
  let U := unitaryEvolution H t
  let r : Fin (n+2)→Bool := fun _ => false
  have hH : IsSelfAdjoint H := isSelfAdjoint_pathHamiltonian _
  have hU : U∈unitary (Register (n+2)) := unitaryEvolution_mem_unitary hH t
  have hcomm : Commute H U := (((Commute.refl H).smul_right (-Complex.I)).smul_right t).exp_right
  have hbound := h S hS hT U hU hcomm C hcut z hz
  let c := anchorPhase hH.isHermitian.eigenvalues r t
  have hphase := norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar hH.isHermitian r t (U r r)
  refine ⟨c,by simp [c,anchorPhase,Complex.norm_exp],TwoQubitCircuit.one _,le_rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖U-c • 1‖ ≤ 2*A*ε
  change ‖U-c • 1‖ ≤ 2*‖U-U r r • 1‖ at hphase
  exact hphase.trans ((mul_le_mul_of_nonneg_left
    (hbound.trans (mul_le_mul_of_nonneg_left he hA.le)) zero_le_two).trans_eq (mul_assoc ..).symm)

#print axioms gaussian_disconnected_scalar_return
end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
