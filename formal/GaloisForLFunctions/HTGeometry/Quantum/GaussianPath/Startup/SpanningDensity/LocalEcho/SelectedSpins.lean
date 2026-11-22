import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.SparseBrackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.SpinMasks

/-! # The diagonal energy left by two disjoint spin flips -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section
variable {n : ℕ}

def ends (Q : Finset (Fin (n+1))) : Finset (Fin (n+2)) := Q.biUnion fun e => {e.castSucc,e.succ}

private theorem mem_near_of_incident {Q : Finset (Fin (n+1))} {l : PathLabel n} {v : Fin (n+2)}
    (hv : v∈ends Q) (hl : pathIncident v l) : l∈nearBonds Q := by
  obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hv
  have hz : pathIncident v (zz e) := by
    simpa only [zz,pathIncident,Finset.mem_insert,Finset.mem_singleton,eq_comm] using hv
  have hd := Finset.not_disjoint_iff.mpr ⟨v,mem_labelSupport.mpr (pathWord_ne_none_of_incident hz),
    mem_labelSupport.mpr (pathWord_ne_none_of_incident hl)⟩
  exact Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_insert_of_mem (mem_pathOverlaps.mpr hd)⟩

/-- Spin flips have no effect on words outside the selected bond neighborhoods. -/
theorem off_sign {Q : Finset (Fin (n+1))} {S : Finset (Fin (n+2))} (hs : S⊆ends Q)
    (l : PathLabel n) (hl : l∉nearBonds Q) : wordSign S l=1 := by
  have ho (v : Fin (n+2)) (hv : pathIncident v l) : v∉S := fun h => hl (mem_near_of_incident (hs h) hv)
  rcases l with ⟨i,a⟩|⟨e,a,b⟩
  · simp [wordSign,axisSign,ho i rfl]
  · simp [wordSign,axisSign,ho _ (Or.inl rfl),ho _ (Or.inr rfl)]

theorem mixed_coord_abs (S T : Finset (Fin (n+2))) (u : PathShell n) (l : PathLabel n) :
    |mixedShell S T u l| ≤ 4*|u l| := by
  have h (V : Finset (Fin (n+2))) : |1-wordSign V l|≤2 := by
    simpa only [abs_one,wordSign_abs,one_add_one_eq_two] using abs_sub (1:ℝ) (wordSign V l)
  change |(1-wordSign S l)*(1-wordSign T l)*u l| ≤ _
  rw [abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_right ((mul_le_mul (h S) (h T) (abs_nonneg _) zero_le_two).trans_eq (by norm_num)) (abs_nonneg _)

private theorem mixed_off {Q : Finset (Fin (n+1))} {S : Finset (Fin (n+2))} (T : Finset (Fin (n+2)))
    (hs : S⊆ends Q) (u : PathShell n) (l : PathLabel n) (hl : l∉nearBonds Q) : mixedShell S T u l=0 := by
  change (1-wordSign S l)*_*_=0
  rw [off_sign hs l hl,sub_self,zero_mul,zero_mul]

theorem mixed_bounds (u : PathShell n) (Q : Finset (Fin (n+1))) (S T : Finset (Fin (n+2))) (hs : S⊆ends Q)
    (M : ℝ) (hM : 0≤M) (hm : ∀ e∈Q, localMass u e ≤ M^2) :
    (∀ l, |mixedShell S T u l| ≤ 4*M) ∧ ‖mixedShell S T u‖^2 ≤ 43*Q.card*(4*M)^2 := by
  have hc (l : PathLabel n) : |mixedShell S T u l| ≤ 4*M := by
    by_cases hl : l∈nearBonds Q
    · obtain ⟨e,he,h⟩ := Finset.mem_biUnion.mp hl
      have hb := (coord_le_localMass u e h (Finset.mem_insert_self ..)).trans (hm e he)
      exact (mixed_coord_abs S T u l).trans (mul_le_mul_of_nonneg_left (le_of_sq_le_sq (by rwa [sq_abs]) hM) (by norm_num))
    · rw [mixed_off T hs u l hl,abs_zero]; positivity
  refine ⟨hc,?_⟩
  rw [EuclideanSpace.norm_sq_eq,←Finset.sum_subset (Finset.subset_univ (nearBonds Q)) (fun l _ hl => by
    rw [mixed_off T hs u l hl,norm_zero,zero_pow (by decide : 2 ≠ 0)])]
  apply (Finset.sum_le_sum (fun l (_ : l∈nearBonds Q) => pow_le_pow_left₀ (norm_nonneg _) (hc l) 2)).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast nearBonds_card Q) (sq_nonneg _)

/-- Disjoint flips annihilate the onsite fields. The remaining Ising
couplings can have either sign and occupy any subset of the path. -/
theorem mixed_energy (u : PathShell n) {S T : Finset (Fin (n+2))} (hd : Disjoint S T) (x : Fin (n+2)→Bool) :
    pathDiagEnergy (mixedShell S T u) x = ∑ e : Fin (n+1), mixedShell S T u (zz e)*(spin (x e.castSucc)*spin (x e.succ)) := by
  have hon (i : Fin (n+2)) : mixedShell S T u (.inl (i,2))=0 := by
    by_cases hi : i∈S
    · simp [mixedShell,wordSign,axisSign,Finset.disjoint_left.mp hd hi]
    · simp [mixedShell,wordSign,axisSign,hi]
  unfold pathDiagEnergy
  simp only [hon,zero_mul,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro e _
  have he : e.castSucc ≠ e.succ := fun h => by have := congrArg Fin.val h; simp at this
  simp [zz,zSetSign,spin,he]

/-- A selected edge is flipped at exactly one endpoint by each mask. -/
theorem mixed_crossed (u : PathShell n) (V S : Finset (Fin (n+2))) (e : Fin (n+1))
    (hl : e.castSucc∈V) (hr : e.succ∈V) (h : e.castSucc∈S ↔ e.succ∉S) :
    mixedShell (V∩S) (V\S) u (zz e)=4*u (zz e) := by
  have haxis : (2 : Fin 3) ≠ 0 := by decide
  by_cases he : e.castSucc∈S
  · norm_num [mixedShell,zz,wordSign,axisSign,hl,hr,he,h.mp he,haxis]
  · have hm : e.succ∈S := by by_contra hh; exact he (h.mpr hh)
    norm_num [mixedShell,zz,wordSign,axisSign,hl,hr,he,hm,haxis]

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
