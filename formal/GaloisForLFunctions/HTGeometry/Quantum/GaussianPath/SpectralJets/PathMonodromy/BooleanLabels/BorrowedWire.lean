import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.PathMonodromy.BooleanLabels.Switches

/-! # Arbitrarily many Boolean controls with a single borrowed wire -/

open Finset Equiv
namespace GaloisForLFunctions.HTGeometry.PathMonodromy.BooleanLabels
noncomputable section
variable {I : Type*} [DecidableEq I]

/-- Toggling the borrowed wire before the second controlled flip and
restoring it afterwards cancels its unknown initial value. -/
theorem add_control (S : Finset I) (k b t : I) (hb : b∉S) (ht : t∉S)
    (hbt : b≠t) (hkb : k≠b) (hkt : k≠t) :
    let F := flip S b hb
    let G := flip {b,k} t (by simp [hbt.symm,hkt.symm])
    F*G*F*G=flip (insert k S) t (by simp [hkt.symm,ht]) := by
  intro F G
  let htG : t∉({b,k}:Finset I) := by simp [hbt.symm,hkt.symm]
  ext x i
  by_cases hit : i=t
  · subst i
    simp only [F,G,Perm.mul_apply,flip_other S hb hbt.symm,flip_self,
      active_insert,active_singleton,flip_other _ htG hbt,flip_other _ htG hkt,
      flip_other S hb hkb,active_flip ht]
    cases x t <;> cases x b <;> cases x k <;> cases active S x <;> rfl
  by_cases hib : i=b
  · subst i
    simp only [F,G,Perm.mul_apply,flip_self,flip_other _ htG hbt,flip_other _ _ hbt,
      active_flip ht,active_flip hb]
    cases x b <;> cases active S x <;> rfl
  simp only [F,G,Perm.mul_apply,flip_other _ _ hib,flip_other _ _ hit]

/-- NOT, CNOT and two-control Toffoli flips generate a flip with any
number of controls as soon as a distinct spare wire is available. -/
theorem flip_mem_of_borrowed (G : Subgroup (Perm (I→Bool)))
    (hsmall : ∀ (S : Finset I) (t : I) (ht : t∉S), S.card≤2 → flip S t ht∈G)
    (S : Finset I) (t b : I) (ht : t∉S) (hb : b∉S) (hbt : b≠t) : flip S t ht∈G := by
  induction S using Finset.induction_on generalizing t b with
  | empty => exact hsmall _ _ _ (by simp)
  | @insert k S hk ih =>
    have ht' := not_mem_insert.mp ht
    have hb' := not_mem_insert.mp hb
    have hF := ih b t hb'.2 ht'.2 hbt.symm
    have htG : t∉({b,k}:Finset I) := by simp [hbt.symm,ht'.1]
    have hcard : ({b,k}:Finset I).card≤2 := (card_insert_le ..).trans (by simp)
    have hG := hsmall {b,k} t htG hcard
    have h := add_control S k b t hb'.2 ht'.2 hbt hb'.1.symm ht'.1.symm
    exact h ▸ G.mul_mem (G.mul_mem (G.mul_mem hF hG) hF) hG

#print axioms flip_mem_of_borrowed
end
end GaloisForLFunctions.HTGeometry.PathMonodromy.BooleanLabels
