import GaloisForLFunctions.HTGeometry.FiniteUnitaryFundamentalGroup
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarReindex

/-!
# Coordinate-independent finite-unitary fundamental groups

Reindexing transports determinant classification from `Fin (n+1)` to every
nonempty finite index type. Thus the classification applies to the same
matrix carriers as the Haar and special-unitary normalization interfaces.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Coordinate reindexing as a continuous group homomorphism. -/
def finiteUnitaryReindexHom (e : ι ≃ κ) :
    Matrix.unitaryGroup ι ℂ →ₜ* Matrix.unitaryGroup κ ℂ :=
  { unitaryGroupReindex e with continuous_toFun := continuous_unitaryGroupReindex e }

/-- Inverse coordinate reindexing cancels before taking loop classes. -/
theorem finiteUnitaryReindexHom_symm_comp (e : ι ≃ κ) :
    (finiteUnitaryReindexHom e.symm).comp (finiteUnitaryReindexHom e) =
      ContinuousMonoidHom.id (Matrix.unitaryGroup ι ℂ) := by
  apply ContinuousMonoidHom.ext
  intro U
  exact unitaryGroupReindex_symm_apply e U

/-- Determinant is independent of the finite coordinate carrier. -/
theorem finiteUnitaryDeterminant_comp_reindex (e : ι ≃ κ) :
    (finiteUnitaryDeterminant κ).comp (finiteUnitaryReindexHom e) =
      finiteUnitaryDeterminant ι := by
  ext U
  change (Matrix.reindexAlgEquiv ℂ ℂ e (U : Matrix ι ι ℂ)).det =
    (U : Matrix ι ι ℂ).det
  simp

private theorem reindexFundamentalGroup_injective (e : ι ≃ κ) :
    Function.Injective (fundamentalGroupContinuousHom (finiteUnitaryReindexHom e)) := by
  have h : Function.LeftInverse
      (fundamentalGroupContinuousHom (finiteUnitaryReindexHom e.symm))
      (fundamentalGroupContinuousHom (finiteUnitaryReindexHom e)) := by
    intro p
    have heq := congrArg (fun f => fundamentalGroupContinuousHom f p)
      (finiteUnitaryReindexHom_symm_comp e)
    simpa only [fundamentalGroupContinuousHom_comp, MonoidHom.comp_apply,
      fundamentalGroupContinuousHom_id, MonoidHom.id_apply] using heq
  exact h.injective

/-- Determinant classifies loop classes for every nonempty finite matrix carrier. -/
theorem finiteUnitaryDeterminant_fundamentalGroup_bijective_index [Nonempty ι] :
    Function.Bijective (fundamentalGroupContinuousHom (finiteUnitaryDeterminant ι)) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)))
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  constructor
  · intro p q hpq
    apply reindexFundamentalGroup_injective e
    apply (finiteUnitaryDeterminant_fundamentalGroup_bijective n).1
    have hcomm := congrArg fundamentalGroupContinuousHom
      (finiteUnitaryDeterminant_comp_reindex e)
    rw [fundamentalGroupContinuousHom_comp] at hcomm
    exact (DFunLike.congr_fun hcomm p).trans (hpq.trans (DFunLike.congr_fun hcomm q).symm)
  · let i0 : ι := Classical.choice inferInstance
    have h : Function.RightInverse
        (fundamentalGroupContinuousHom (finiteUnitaryCircleSection i0))
        (fundamentalGroupContinuousHom (finiteUnitaryDeterminant ι)) := by
      intro p
      have heq := congrArg (fun f => fundamentalGroupContinuousHom f p)
        (finiteUnitaryDeterminant_comp_section i0)
      simpa only [fundamentalGroupContinuousHom_comp, MonoidHom.comp_apply,
        fundamentalGroupContinuousHom_id, MonoidHom.id_apply] using heq
    exact h.surjective

/-- Integer classification without choosing a standard finite coordinate type. -/
def finiteUnitaryFundamentalGroupEquivInt_index [Nonempty ι] :
    FundamentalGroup (Matrix.unitaryGroup ι ℂ) 1 ≃* Multiplicative ℤ :=
  (MulEquiv.ofBijective (fundamentalGroupContinuousHom (finiteUnitaryDeterminant ι))
    finiteUnitaryDeterminant_fundamentalGroup_bijective_index).trans
      circleFundamentalGroupEquivInt

end

end GaloisForLFunctions.HTGeometry
