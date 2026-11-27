import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EigenstatePreparation.BellBlocks.SpinSignals

/-! # Local coefficient error at the two spins of a Bell dimer -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section
variable {n : ℕ}

/-- Only the XX and ZZ directions on the selected edge are energized. -/
def dimerCoeff (e : Fin (n+1)) (l : PathLabel n) : ℝ :=
  (if l=Sum.inr (e,(0,0)) then 1 else 0)+(if l=Sum.inr (e,(2,2)) then 2 else 0)

private def sites (e : Fin (n+1)) : Finset (Fin (n+2)) := {e.castSucc,e.succ}
private def incident (e : Fin (n+1)) := (sites e).biUnion pathIncidentLabels
private def center (e : Fin (n+1)) : PathShell n := WithLp.toLp 2 (dimerCoeff e)

private theorem supported_edge (e : Fin (n+1)) (a b : Fin 3) :
    PathWordSupportedIn (sites e) (.inr (e,(a,b))) := by
  intro v hv
  have h : v≠e.castSucc ∧ v≠e.succ := by simpa [sites] using hv
  simp [pathWord,couplingWord,h.1,h.2]

private theorem restricted_coeff (e : Fin (n+1)) (l : PathLabel n) :
    (if PathWordSupportedIn (sites e) l then center e l else 0)=dimerCoeff e l := by
  change (if _ then dimerCoeff e l else 0)=_
  by_cases hx : l=Sum.inr (e,(0,0))
  · subst l; rw [if_pos (supported_edge e _ _)]
  by_cases hz : l=Sum.inr (e,(2,2))
  · subst l; rw [if_pos (supported_edge e _ _)]
  simp [dimerCoeff,hx,hz]

private theorem replacement (u : PathShell n) (e : Fin (n+1)) :
    pathHamiltonianPacketReference (sites e)ᶜ (sites e) u (center e)=dimerModel u e := by
  change _+pathHamiltonianOnSites (sites e) (center e)=_+_
  congr 1
  rw [pathHamiltonianOnSites]
  simp only [restricted_coeff,dimerCoeff,Complex.ofReal_add,add_smul,sum_add_distrib]
  simp [apply_ite,ite_smul, pathWord, two_smul]

private theorem incident_edge (e : Fin (n+1)) (a b : Fin 3) :
    Sum.inr (e,(a,b)) ∈ incident e := by
  apply mem_biUnion.mpr
  exact ⟨e.castSucc,by simp [sites],mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩⟩

/-- Changing the local coordinates by at most η costs at most 42η,
independently of the fields and interactions in the rest of the chain. -/
theorem dimer_replacement_error (u : PathShell n) (e : Fin (n+1)) {η : ℝ} (hη : 0≤η)
    (h : ∀ v ∈ ({e.castSucc,e.succ}:Finset (Fin (n+2))), ∀ l, pathIncident v l →
      |u l-dimerCoeff e l|≤η) : ‖dimerModel u e-pathHamiltonian u‖≤42*η := by
  classical
  let err l := |u l-pathPacketReferenceCoeff (sites e)ᶜ (sites e) u (center e) l|
  have hon (l) (hl : l∈incident e) : err l≤η := by
    obtain ⟨v,hv,hl⟩ := Finset.mem_biUnion.mp hl
    have hi := (mem_filter.mp hl).2
    have hn : ¬PathWordSupportedIn (sites e)ᶜ l := fun hsup =>
      pathWord_ne_none_of_incident hi (hsup v (by simpa using hv))
    simpa only [err,pathPacketReferenceCoeff,if_neg hn,zero_add,restricted_coeff] using h v hv l hi
  have hoff (l : PathLabel n) (_ : l∈univ) (hl : l∉incident e) : err l=0 := by
    have hn (a b : Fin 3) : l≠Sum.inr (e,(a,b)) := fun h => hl (h.symm ▸ incident_edge e a b)
    simp only [err,pathPacketReferenceCoeff,if_pos (path_supported_compl_of_not_incident (sites e) l hl),
      restricted_coeff,dimerCoeff,if_neg (hn _ _),add_zero,sub_self,abs_zero]
  have hc : ((incident e).card:ℝ)≤42 := by
    have hne : e.castSucc≠e.succ := by intro he; have := congrArg Fin.val he; change e.val=e.val+1 at this; omega
    exact_mod_cast (by simpa [sites,incident,hne] using pathIncident_union_card (sites e) :
      (incident e).card≤42)
  rw [norm_sub_rev,←replacement]
  apply (norm_pathHamiltonian_sub_packetReference_le _ _ _ _).trans
  change ∑ l, err l≤_
  rw [←sum_subset (subset_univ (incident e)) hoff]
  exact (sum_le_sum hon).trans ((by simp only [sum_const,nsmul_eq_mul] : ∑ _ ∈ incident e, η =
    ((incident e).card:ℝ)*η).le.trans (mul_le_mul_of_nonneg_right hc hη))

#print axioms dimer_replacement_error
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
