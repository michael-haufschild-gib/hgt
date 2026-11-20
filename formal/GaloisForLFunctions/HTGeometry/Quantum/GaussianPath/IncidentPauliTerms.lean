import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction

/-! # Pauli terms incident to sites of an open nearest-neighbour path -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Whether a path label acts nontrivially at the specified site. -/
def pathIncident {n : ℕ} (v : Fin (n+2)) : PathLabel n → Prop
  | .inl (w,_) => w = v
  | .inr (e,_) => e.castSucc = v ∨ e.succ = v

/-- All onsite and edge labels incident to the specified site. -/
def pathIncidentLabels {n : ℕ} (v : Fin (n+2)) : Finset (PathLabel n) := by
  classical
  exact Finset.univ.filter (pathIncident v)

/-- Three onsite directions and at most nine Pauli couplings on either
incident edge meet a given site. Endpoints only decrease this count. -/
theorem pathIncidentLabels_card {n : ℕ} (v : Fin (n+2)) : (pathIncidentLabels v).card ≤ 21 := by
  classical
  let code : PathLabel n → Fin 3 ⊕ ((Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3))
    | .inl (_,q) => .inl q
    | .inr (e,ab) => if e.castSucc = v then .inr (.inl ab) else .inr (.inr ab)
  have valid (l) (hl : l ∈ pathIncidentLabels v) : pathIncident v l := (Finset.mem_filter.mp hl).2
  have hinj : Set.InjOn code (↑(pathIncidentLabels v)) := by
    intro l hl t ht eq
    have h := valid l hl
    have k := valid t ht
    rcases l with ⟨s,q⟩ | ⟨e,ab⟩ <;> rcases t with ⟨w,r⟩ | ⟨f,cd⟩
    · have hs : s = v := h
      have hw : w = v := k
      simpa [code,hs,hw] using eq
    · by_cases hf : f.castSucc = v <;> simp [code,hf] at eq
    · by_cases he : e.castSucc = v <;> simp [code,he] at eq
    · change e.castSucc = v ∨ e.succ = v at h
      change f.castSucc = v ∨ f.succ = v at k
      by_cases he : e.castSucc = v <;> by_cases hf : f.castSucc = v <;> simp [code,he,hf] at eq
      · have hef : e = f := Fin.castSucc_injective _ (he.trans hf.symm)
        simp [hef,eq]
      · have hef : e = f := Fin.succ_injective _ ((h.resolve_left he).trans (k.resolve_left hf).symm)
        simp [hef,eq]
  have hcard := Finset.card_le_card_of_injOn code (fun _ _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_sum,Fintype.card_prod] using hcard

theorem pathWord_none_of_not_incidentSite {n : ℕ} (v : Fin (n+2)) (l : PathLabel n)
    (h : ¬pathIncident v l) : pathWord l v = none := by
  rcases l with ⟨w,q⟩ | ⟨e,ab⟩
  · change ¬w = v at h
    simp [pathWord,onsiteWord,Ne.symm h]
  · change ¬(e.castSucc = v ∨ e.succ = v) at h
    rw [not_or] at h
    simp [pathWord,couplingWord,Ne.symm h.1,Ne.symm h.2]

theorem pathWord_ne_none_of_incident {n : ℕ} {v : Fin (n+2)} {l : PathLabel n}
    (h : pathIncident v l) : pathWord l v ≠ none := by
  rcases l with ⟨w,q⟩ | ⟨e,ab⟩
  · change w = v at h
    simp [pathWord,onsiteWord,h]
  · change e.castSucc = v ∨ e.succ = v at h
    rcases h with rfl | rfl
    · simp [pathWord,couplingWord]
    · have hne : e.succ ≠ e.castSucc := by
        intro he; have := congrArg Fin.val he; simp at this
      simp [pathWord,couplingWord,hne]

/-- At most 21 terms per selected site can change when the sites are removed. -/
theorem pathIncident_union_card {n : ℕ} (S : Finset (Fin (n+2))) :
    (S.biUnion pathIncidentLabels).card ≤ 21*S.card := calc
  _ ≤ ∑ v ∈ S, (pathIncidentLabels v).card := Finset.card_biUnion_le
  _ ≤ ∑ _v ∈ S, 21 := Finset.sum_le_sum fun v _ => pathIncidentLabels_card v
  _ = _ := by simp [mul_comm]

/-- Every term outside the union is supported in the complementary sites. -/
theorem path_supported_compl_of_not_incident {n : ℕ} (S : Finset (Fin (n+2)))
    (l : PathLabel n) (hl : l ∉ S.biUnion pathIncidentLabels) : PathWordSupportedIn Sᶜ l := by
  classical
  intro v hv
  have hS : v ∈ S := by simpa using hv
  apply pathWord_none_of_not_incidentSite
  intro hinc
  exact hl (Finset.mem_biUnion.mpr ⟨v,hS,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hinc⟩⟩)

end
end GaloisForLFunctions.HTGeometry
