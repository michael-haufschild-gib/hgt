import GaloisForLFunctions.HTGeometry.InvolutiveSubspaceParityDecomposition

/-!
# Simultaneous parity grading of an invariant subspace

A subspace stable under a finite family of commuting involutions is the sum of its simultaneous
parity components, indexed by sign patterns on the family.  The induction splits off one involution
at a time and records its sign in the pattern, so no averaging projector and no character theory is
needed.

Independently of that, a subspace which is graded by an independent family meets every partial sum
of the family gradewise: the modular law plus disjointness of complementary partial sums does it.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section GradedIntersection

variable {K X ι : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- **A graded subspace meets a partial sum of the grading gradewise.** -/
theorem inf_biSup_eq_biSup_inf_of_graded (V : ι → Submodule K X) (hV : iSupIndep V)
    (U : Submodule K X) (hU : U = ⨆ i, U ⊓ V i) (S : Set ι) :
    U ⊓ (⨆ i ∈ S, V i) = ⨆ i ∈ S, (U ⊓ V i) := by
  classical
  have hAC : (⨆ i ∈ S, U ⊓ V i) ≤ ⨆ i ∈ S, V i :=
    iSup₂_le fun i hi => le_trans inf_le_right (le_biSup V hi)
  refine le_antisymm ?_ (le_inf (iSup₂_le fun i _ => inf_le_left) hAC)
  have hUAB : U ≤ (⨆ i ∈ S, U ⊓ V i) ⊔ ⨆ i ∈ Sᶜ, U ⊓ V i := by
    refine hU.le.trans (iSup_le fun i => ?_)
    by_cases hi : i ∈ S
    · exact le_sup_of_le_left (le_biSup (fun i => U ⊓ V i) hi)
    · exact le_sup_of_le_right (le_biSup (fun i => U ⊓ V i) hi)
  have hBC : Disjoint (⨆ i ∈ Sᶜ, U ⊓ V i) (⨆ i ∈ S, V i) := by
    refine Disjoint.mono_left (iSup₂_le fun i hi => le_trans inf_le_right (le_biSup V hi)) ?_
    exact hV.disjoint_biSup_biSup (disjoint_compl_left)
  calc U ⊓ ⨆ i ∈ S, V i
      ≤ ((⨆ i ∈ S, U ⊓ V i) ⊔ ⨆ i ∈ Sᶜ, U ⊓ V i) ⊓ ⨆ i ∈ S, V i :=
        inf_le_inf_right _ hUAB
    _ = (⨆ i ∈ S, U ⊓ V i) ⊔ ((⨆ i ∈ Sᶜ, U ⊓ V i) ⊓ ⨆ i ∈ S, V i) :=
        sup_inf_assoc_of_le _ hAC
    _ = ⨆ i ∈ S, U ⊓ V i := by rw [hBC.eq_bot, sup_bot_eq]

end GradedIntersection

section Grading

variable {K X J : Type*} [Field K] [AddCommGroup X] [Module K X] [DecidableEq J]

/-- The simultaneous parity subspace of a family of involutions, cut out on a finite index set by a
sign pattern. -/
def simultaneousParitySubspace (T : J → X ≃ₗ[K] X) (F : Finset J) (s : J → Bool) :
    Submodule K X :=
  ⨅ j ∈ F, (if s j then involutiveEvenSubspace (T j) else involutiveOddSubspace (T j))

omit [DecidableEq J] in
@[simp] theorem simultaneousParitySubspace_empty (T : J → X ≃ₗ[K] X) (s : J → Bool) :
    simultaneousParitySubspace T ∅ s = ⊤ := by
  simp [simultaneousParitySubspace]

theorem simultaneousParitySubspace_insert (T : J → X ≃ₗ[K] X) {j : J} {F : Finset J}
    (s : J → Bool) :
    simultaneousParitySubspace T (insert j F) s
      = (if s j then involutiveEvenSubspace (T j) else involutiveOddSubspace (T j))
          ⊓ simultaneousParitySubspace T F s := by
  rw [simultaneousParitySubspace, simultaneousParitySubspace, Finset.iInf_insert]

theorem simultaneousParitySubspace_update (T : J → X ≃ₗ[K] X) {j : J} {F : Finset J}
    (hj : j ∉ F) (s : J → Bool) (b : Bool) :
    simultaneousParitySubspace T F (Function.update s j b)
      = simultaneousParitySubspace T F s := by
  refine iInf_congr fun k => iInf_congr fun hk => ?_
  have hkj : k ≠ j := fun h => hj (h ▸ hk)
  rw [Function.update_of_ne hkj]

/-- **A subspace stable under a finite family of commuting involutions is the sum of its
simultaneous parity components.** -/
theorem invariantSubspace_eq_iSup_simultaneousParitySubspace
    (h2 : (2 : K) ≠ 0) (T : J → X ≃ₗ[K] X)
    (hinvol : ∀ j, ∀ x, T j (T j x) = x)
    (hcomm : ∀ j k, ∀ x, T j (T k x) = T k (T j x))
    (F : Finset J) (U : Submodule K X)
    (hstable : ∀ j, U.map (T j : X →ₗ[K] X) ≤ U) :
    U = ⨆ s : J → Bool, (U ⊓ simultaneousParitySubspace T F s) := by
  classical
  induction F using Finset.induction_on generalizing U with
  | empty =>
      refine le_antisymm ?_ (iSup_le fun s => inf_le_left)
      refine le_trans ?_ (le_iSup _ (fun _ : J => true))
      simp
  | @insert j F hj ih =>
      have hsplit : U = (U ⊓ involutiveEvenSubspace (T j)) ⊔ (U ⊓ involutiveOddSubspace (T j)) :=
        invariantSubspace_eq_even_sup_odd (T j) (hinvol j) h2 U (hstable j)
      have hEstable : ∀ k, (U ⊓ involutiveEvenSubspace (T j)).map ((T k : X →ₗ[K] X))
          ≤ U ⊓ involutiveEvenSubspace (T j) := fun k =>
        evenPart_map_le_of_commuting_involutions (T j) (T k) (fun x => hcomm j k x) U (hstable k)
      have hOstable : ∀ k, (U ⊓ involutiveOddSubspace (T j)).map ((T k : X →ₗ[K] X))
          ≤ U ⊓ involutiveOddSubspace (T j) := fun k =>
        oddPart_map_le_of_commuting_involutions (T j) (T k) (fun x => hcomm j k x) U (hstable k)
      have hE := ih (U ⊓ involutiveEvenSubspace (T j)) hEstable
      have hO := ih (U ⊓ involutiveOddSubspace (T j)) hOstable
      refine le_antisymm (hsplit.le.trans (sup_le ?_ ?_)) (iSup_le fun s => inf_le_left)
      · refine hE.le.trans (iSup_le fun s => ?_)
        refine le_trans ?_ (le_iSup _ (Function.update s j true))
        have hif : (if (Function.update s j true) j = true then involutiveEvenSubspace (T j)
            else involutiveOddSubspace (T j)) = involutiveEvenSubspace (T j) := by simp
        rw [simultaneousParitySubspace_insert, hif,
          simultaneousParitySubspace_update T hj s true]
        exact le_inf (le_trans inf_le_left inf_le_left)
          (le_inf (le_trans inf_le_left inf_le_right) inf_le_right)
      · refine hO.le.trans (iSup_le fun s => ?_)
        refine le_trans ?_ (le_iSup _ (Function.update s j false))
        have hif : (if (Function.update s j false) j = true then involutiveEvenSubspace (T j)
            else involutiveOddSubspace (T j)) = involutiveOddSubspace (T j) := by simp
        rw [simultaneousParitySubspace_insert, hif,
          simultaneousParitySubspace_update T hj s false]
        exact le_inf (le_trans inf_le_left inf_le_left)
          (le_inf (le_trans inf_le_left inf_le_right) inf_le_right)

end Grading

end

end GaloisForLFunctions.HTGeometry
