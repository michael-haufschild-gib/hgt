import GaloisForLFunctions.WindowedLandauTheory.SatakeDualWeyl.Statement

namespace WindowedLandauTheory.UG.P

open Matrix MvPolynomial

theorem standard_action_mul_holds : WindowedLandauTheory.UG.StdActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold WindowedLandauTheory.UG.stdAct
    rw [Units.val_mul, Matrix.mulVecLin_mul]
  · unfold WindowedLandauTheory.UG.stdAct
    rw [Units.val_one, Matrix.mulVecLin_one]

theorem tensor_action_mul_holds : WindowedLandauTheory.UG.TensActMul := by
  intro O _ n _ _ k g h
  refine ⟨?_, ?_⟩
  · unfold WindowedLandauTheory.UG.tensAct
    rw [← PiTensorProduct.map_comp]
    congr 1
    funext i
    exact (standard_action_mul_holds O n g h).1
  · unfold WindowedLandauTheory.UG.tensAct
    have : (fun _ : Fin k => WindowedLandauTheory.UG.stdAct O n 1) = fun _ => LinearMap.id :=
      funext fun _ => (standard_action_mul_holds O n 1 1).2
    rw [this, PiTensorProduct.map_id]

theorem linSubst_comp (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (M N : Matrix n n O) :
    (WindowedLandauTheory.UG.linSubst O n M).comp (WindowedLandauTheory.UG.linSubst O n N) = WindowedLandauTheory.UG.linSubst O n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [WindowedLandauTheory.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem linSubst_one (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    WindowedLandauTheory.UG.linSubst O n 1 = AlgHom.id O _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [WindowedLandauTheory.UG.linSubst, Matrix.one_apply]

theorem polynomial_action_mul_holds : WindowedLandauTheory.UG.PolyActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold WindowedLandauTheory.UG.polyAct
    rw [linSubst_comp, _root_.mul_inv_rev, Units.val_mul]
  · unfold WindowedLandauTheory.UG.polyAct
    rw [inv_one, Units.val_one, linSubst_one]

end WindowedLandauTheory.UG.P
