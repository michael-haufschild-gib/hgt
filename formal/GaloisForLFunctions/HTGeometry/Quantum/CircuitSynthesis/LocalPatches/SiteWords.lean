import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PauliTerm
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PatchLists
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord

/-! # Sorting Pauli generators by the left endpoint of their support -/
open Matrix NormedSpace Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
attribute [local instance] instCStarAlgebraRegister

/-- The onsite location or the left endpoint of a bond. -/
def leftSite {n : ℕ} : PathLabel n → ℕ
  | .inl (s,_) => s.val
  | .inr (e,_) => e.val

private def siteLabels (n i : ℕ) := Finset.univ.filter fun l : PathLabel n => leftSite l=i

private theorem leftSite_lt {n : ℕ} (l : PathLabel n) : leftSite l < n+2 := by
  rcases l with ⟨s,_⟩|⟨e,_⟩
  · exact s.isLt
  · exact e.isLt.trans (by omega)

private theorem at_leftSite {n : ℕ} (l : PathLabel n) (v : Fin (n+2)) (h : leftSite l=v.val) :
    pathIncident v l := by
  rcases l with ⟨s,_⟩|⟨e,_⟩
  · exact Fin.ext h
  · exact Or.inl (Fin.ext h)

private theorem siteLabels_card (n i : ℕ) : (siteLabels n i).card ≤ 21 := by
  classical
  by_cases hi : i < n+2
  · let v : Fin (n+2) := ⟨i,hi⟩
    apply le_trans _ (pathIncidentLabels_card v)
    apply card_le_card
    intro l hl
    exact mem_filter.mpr ⟨mem_univ _,at_leftSite l v (mem_filter.mp hl).2⟩
  · have h : siteLabels n i = ∅ := eq_empty_iff_forall_notMem.mpr fun l hl =>
      hi ((mem_filter.mp hl).2 ▸ leftSite_lt l)
    simp [h]

private theorem support_bounds {n : ℕ} {l : PathLabel n} {v : Fin (n+2)}
    (h : v ∈ labelSupport (pathWord l)) : leftSite l ≤ v.val ∧ v.val ≤ leftSite l+1 := by
  have hi : pathIncident v l := by
    by_contra hh
    exact (mem_labelSupport.mp h) (pathWord_none_of_not_incidentSite v l hh)
  rcases l with ⟨s,q⟩|⟨e,ab⟩
  · obtain rfl : s=v := hi
    simp [leftSite]
  · rcases (show e.castSucc=v ∨ e.succ=v from hi) with rfl|rfl <;> simp [leftSite]

/-- Each list contains the interactions starting at its site. -/
def siteWords {n : ℕ} (u : PathShell n) (i : ℕ) : List (Register (n+2)) :=
  (siteLabels n i).toList.map (pathTermGenerator u)

theorem siteWords_length {n : ℕ} (u : PathShell n) (i : ℕ) : (siteWords u i).length ≤ 21 := by
  simpa [siteWords] using siteLabels_card n i

private theorem sum_siteWords {n : ℕ} (u : PathShell n) (i : ℕ) :
    (siteWords u i).sum = ∑ l ∈ siteLabels n i, pathTermGenerator u l := by simp [siteWords]

theorem siteWords_sum {n : ℕ} (u : PathShell n) :
    intervalSum (fun i => (siteWords u i).sum) 0 (n+2) = (-Complex.I) • pathHamiltonian u := by
  classical
  simp only [intervalSum,Nat.Ico_zero_eq_range,sum_siteWords,siteLabels,sum_filter]
  rw [sum_comm,pathHamiltonian_eq_sum,Finset.smul_sum]
  apply sum_congr rfl
  intro l _
  simp [leftSite_lt l,pathTermGenerator]

theorem siteWords_mass {n : ℕ} (u : PathShell n) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ l, |u l| ≤ R) (i : ℕ) : ProductFormula.mass (siteWords u i) ≤ 21*R := by
  have he : ProductFormula.mass (siteWords u i) = ∑ l ∈ siteLabels n i, ‖pathTermGenerator u l‖ := by
    simp [ProductFormula.mass,siteWords]
  rw [he]
  calc
    _ ≤ ∑ _l ∈ siteLabels n i, R := sum_le_sum fun l _ => (pathTerm_properties u l).1.le.trans (h l)
    _ = ((siteLabels n i).card:ℝ)*R := by simp
    _ ≤ 21*R := mul_le_mul_of_nonneg_right (by exact_mod_cast siteLabels_card n i) hR

theorem siteWords_properties {n : ℕ} (u : PathShell n) (i : ℕ) (x : Register (n+2))
    (h : x ∈ siteWords u i) : x ∈ skewAdjoint (Register (n+2)) ∧ OneGateFlow x := by
  obtain ⟨l,_,rfl⟩ := List.mem_map.mp h
  exact (pathTerm_properties u l).2

theorem siteWords_commute {n : ℕ} (u : PathShell n) (i j : ℕ) (hij : i+1<j) :
    Commute (siteWords u i).sum (siteWords u j).sum := by
  rw [sum_siteWords,sum_siteWords]
  apply Commute.sum_left
  intro l hl
  apply Commute.sum_right
  intro q hq
  have hd : Disjoint (labelSupport (pathWord l)) (labelSupport (pathWord q)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have h₁ := (support_bounds hv).2
    have h₂ := (support_bounds hw).1
    rw [(mem_filter.mp hl).2] at h₁
    rw [(mem_filter.mp hq).2] at h₂
    omega
  have hh := commute_finitePauliMatrix_of_disjoint hd
  exact (((hh.smul_left (u l : ℂ)).smul_left (-Complex.I)).smul_right (u q : ℂ)).smul_right (-Complex.I)

end
end GaloisForLFunctions.HTGeometry.LocalPatches
