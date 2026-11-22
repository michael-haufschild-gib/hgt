import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.Degree.JointVariables
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.TraceAtBackground
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFiniteFrames

/-! # Degree bound for the rectangular longitudinal trace polynomial -/
open MvPolynomial Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {ρ κ R : Type*} [CommRing R]

def withoutFields : MvPolynomial (Option (ρ ⊕ κ)) R →ₐ[R] MvPolynomial (Option ρ) R :=
  aeval fun o => match o with
    | none => X none
    | some (.inl j) => X (some j)
    | some (.inr _) => 0

private theorem without_background (c : MvPolynomial ρ R) :
    withoutFields (κ := κ) (rename backgroundSlot c) = rename some c := by
  induction c using MvPolynomial.induction_on with
  | C c => simp [withoutFields]
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul_X a i ha =>
    simp only [map_mul,rename_X,ha]
    congr 1
    simp [withoutFields,backgroundSlot]

private theorem without_joint (q : MvPolynomial (Option κ) (MvPolynomial ρ R)) :
    withoutFields (joint q) = atZeroField q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [atZeroField,without_background]
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul_X a i ha =>
    simp only [map_mul,ha,joint_X]
    congr 1
    cases i <;> simp [withoutFields,fieldSlot,atZeroField]

private theorem without_degree [Nontrivial R] (q : MvPolynomial (Option (ρ ⊕ κ)) R) :
    (withoutFields q).totalDegree ≤ q.totalDegree := by
  apply BiarithmeticGeometry.ParsellVinogradov.totalDegree_algHom_le
  intro i
  rcases i with _ | (j|j) <;> simp [withoutFields]

variable [Fintype κ] {D d m : ℕ} [Nontrivial R]

private theorem joint_field_degree (u : κ → R) :
    (joint (ρ := ρ) (fieldPoly (fun i => (C (u i) : MvPolynomial ρ R)))).totalDegree ≤ 1 := by
  simp only [fieldPoly,map_sum,map_mul,joint_C,rename_C,joint_X]
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C,totalDegree_X,zero_add])

private theorem joint_char_entry (M : Matrix (Fin D) (Fin D) (MvPolynomial ρ R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (u : Fin D → κ → R) (i j : Fin D) :
    let f := fun j => fieldPoly (fun a => (C (u j a) : MvPolynomial ρ R))
    let A := scalar (Fin D) (X (R := MvPolynomial ρ R) (none : Option κ)) - M.map C - diagonal f
    (joint (A i j)).totalDegree ≤ 1 := by
  intro f A
  have hm := (totalDegree_rename_le (backgroundSlot (κ := κ)) (M i j)).trans (hM i j)
  simp only [A,Matrix.sub_apply,scalar_apply,Matrix.map_apply,map_sub,joint_C]
  by_cases he : i=j
  · subst j
    simp only [diagonal_apply_eq,joint_X]
    refine (totalDegree_sub _ _).trans (max_le ?_ (joint_field_degree (u i)))
    exact (totalDegree_sub _ _).trans (max_le (le_of_eq (totalDegree_X _)) hm)
  · simp only [diagonal_apply_ne _ he,map_zero,zero_sub,sub_zero,totalDegree_neg]
    exact hm

private theorem joint_char_degree (M : Matrix (Fin D) (Fin D) (MvPolynomial ρ R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (u : Fin D → κ → R) :
    (joint (fieldCharacteristic M (fun j i => C (u j i)))).totalDegree ≤ D := by
  rw [fieldCharacteristic,RingHom.map_det]
  exact (determinant_degree _ 1 (joint_char_entry M hM u)).trans_eq (Nat.mul_one D)

/-- The degree counts background couplings and the energy in the same grading. Introducing
the perturbation variables before differentiation keeps the bound linear in field order. -/
theorem fieldRow_degree [Fintype ρ] (M : Matrix (Fin D) (Fin D) (MvPolynomial ρ R)) (hM : ∀ i j, (M i j).totalDegree ≤ 1)
    (u : Fin D → κ → R) (L : ℕ) (w : List κ) (hw : w.length ≤ L) :
    (fieldRow M u L w).totalDegree ≤ 1+2*L*D := by
  rw [fieldRow,←without_joint]
  apply (without_degree _).trans
  rw [joint_fieldJet]
  apply (jetRow_degree _ _ _ ?_).trans
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (joint_char_degree M hM u)) 1
  · intro v hv
    cases hv
    simpa only [List.length_map] using hw

theorem fieldTraceMinor_degree (M : Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) {n : ℕ} (u : Fin D → Fin n → R) (L : ℕ)
    (w : Fin d → List (Fin n)) (hw : ∀ i, (w i).length ≤ L) (k : Fin d → Fin D) :
    (fieldTraceMinor M u w L k).totalDegree ≤ d*((1+2*L*D)+D-1) :=
  traceMinor_degree M hM _ _ (fun i => fieldRow_degree M hM u L (w i) (hw i)) k

#print axioms fieldTraceMinor_degree
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
