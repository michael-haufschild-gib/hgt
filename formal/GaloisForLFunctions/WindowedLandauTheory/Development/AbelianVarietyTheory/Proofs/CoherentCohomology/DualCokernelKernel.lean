import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalRing.Module

/-! The dual cokernel of a matrix represents its kernel over any coefficient
algebra. Over a local ring, a one-dimensional fibre makes it cyclic. -/

noncomputable section

open TensorProduct

namespace GlobalTheory.MatrixKernels

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {a b : ℕ}

abbrev DualCokernel (D : Matrix (Fin b) (Fin a) R) :=
  (Fin a → R) ⧸ LinearMap.range D.transpose.mulVecLin

/-- The images of the coordinate vectors generate the dual cokernel. -/
def coordinate (D : Matrix (Fin b) (Fin a) R) (i : Fin a) : DualCokernel D :=
  (LinearMap.range D.transpose.mulVecLin).mkQ (Pi.single i 1)

private theorem transpose_column (D : Matrix (Fin b) (Fin a) R) (j : Fin b) :
    D.transpose.mulVecLin (Pi.single j 1) = D j := by
  ext i
  simp

private theorem eval_matrix_row (D : Matrix (Fin b) (Fin a) R)
    (v : Fin a → S) (j : Fin b) :
    (Pi.basisFun R (Fin a)).constr R v (D j) = ((D.map (algebraMap R S)).mulVec v) j := by
  rw [Module.Basis.constr_apply, Finsupp.sum_fintype]
  · simp [Matrix.mulVec, dotProduct, Algebra.smul_def]
  · simp

/-- A functional on the transpose cokernel is a solution of the original
linear equations over the coefficient algebra. -/
def kernelEquiv (D : Matrix (Fin b) (Fin a) R) :
    (DualCokernel D →ₗ[R] S) ≃ₗ[S] LinearMap.ker (D.map (algebraMap R S)).mulVecLin := by
  let N := LinearMap.range D.transpose.mulVecLin
  let v (q : DualCokernel D →ₗ[R] S) (i : Fin a) := q (coordinate D i)
  have hv (q : DualCokernel D →ₗ[R] S) : (D.map (algebraMap R S)).mulVec (v q) = 0 := by
    have he : (Pi.basisFun R (Fin a)).constr R (v q) = q.comp N.mkQ := by
      apply (Pi.basisFun R (Fin a)).ext
      intro i
      rw [Module.Basis.constr_basis, Pi.basisFun_apply]
      rfl
    funext j
    rw [← eval_matrix_row D (v q) j, he, ← transpose_column D j, LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _), map_zero]
    rfl
  let f : (DualCokernel D →ₗ[R] S) →ₗ[S]
      LinearMap.ker (D.map (algebraMap R S)).mulVecLin :=
    { toFun := fun q => ⟨v q, hv q⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro q q' e
    have h : q.comp N.mkQ = q'.comp N.mkQ := by
      apply (Pi.basisFun R (Fin a)).ext
      intro i
      rw [Pi.basisFun_apply]
      exact congrFun (congrArg Subtype.val e) i
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    exact LinearMap.congr_fun h x
  · intro w
    let m := (Pi.basisFun R (Fin a)).constr R w.1
    have hm : m.comp D.transpose.mulVecLin = 0 := by
      apply (Pi.basisFun R (Fin b)).ext
      intro j
      rw [Pi.basisFun_apply]
      change m (D.transpose.mulVecLin (Pi.single j 1)) = 0
      rw [transpose_column D j, eval_matrix_row D]
      exact congrFun w.2 j
    let g := N.liftQ m fun _ ⟨x, hx⟩ => hx ▸ LinearMap.congr_fun hm x
    refine ⟨g, Subtype.ext (funext fun i => ?_)⟩
    change g (Submodule.Quotient.mk (Pi.single i 1)) = w.1 i
    dsimp only [g]
    rw [Submodule.liftQ_apply, ← Pi.basisFun_apply, Module.Basis.constr_basis]

theorem kernelEquiv_apply (D : Matrix (Fin b) (Fin a) R)
    (q : DualCokernel D →ₗ[R] S) (i : Fin a) :
    (kernelEquiv D q).1 i = q (coordinate D i) := rfl

/-- A one-dimensional residue kernel gives a cyclic dual cokernel. -/
theorem exists_quotient_equiv_of_residue_finrank_one [IsLocalRing R]
    (D : Matrix (Fin b) (Fin a) R)
    (h : Module.finrank (IsLocalRing.ResidueField R)
      (LinearMap.ker (D.map (IsLocalRing.residue R)).mulVecLin) = 1) :
    ∃ I : Ideal R, I ≤ IsLocalRing.maximalIdeal R ∧
      Nonempty (DualCokernel D ≃ₗ[R] R ⧸ I) := by
  let k := IsLocalRing.ResidueField R
  let Q := DualCokernel D
  let e : (Q →ₗ[R] k) ≃ₗ[k] Module.Dual k (k ⊗[R] Q) :=
    (LinearMap.ringLmapEquivSelf k k (Q →ₗ[R] k)).symm.trans
      (TensorProduct.AlgebraTensorModule.lift.equiv R k k k Q k)
  have hfin : Module.finrank k (k ⊗[R] Q) = 1 := by
    rw [← Subspace.dual_finrank_eq, ← e.finrank_eq, (kernelEquiv (S := k) D).finrank_eq]
    exact h
  let basis := Module.finBasisOfFinrankEq k (k ⊗[R] Q) hfin
  obtain ⟨x, hx⟩ := TensorProduct.mk_surjective R Q k Ideal.Quotient.mk_surjective (basis 0)
  have htop : Submodule.span R ({x} : Set Q) = ⊤ := by
    have h := IsLocalRing.span_eq_top_of_tmul_eq_basis (fun _ : Fin 1 => x) basis
      (fun j => by rw [Subsingleton.elim j (0 : Fin 1)]; exact hx)
    simpa only [Set.range_const] using h
  let π := LinearMap.toSpanSingleton R Q x
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top]
    exact (LinearMap.range_toSpanSingleton (R := R) x).trans htop
  let I := LinearMap.ker π
  let E : (R ⧸ I) ≃ₗ[R] Q := π.quotKerEquivOfSurjective hsurj
  have hn : ¬ Subsingleton Q := fun hq => by
    letI := hq
    have hzero : Module.finrank k (k ⊗[R] Q) = 0 := Module.finrank_zero_of_subsingleton
    exact Nat.zero_ne_one (hzero.symm.trans hfin)
  have hproper : I ≠ ⊤ := by
    intro hi
    have e0 : π = 0 := LinearMap.ker_eq_top.mp hi
    apply hn
    refine ⟨fun z w => ?_⟩
    obtain ⟨r, rfl⟩ := hsurj z
    obtain ⟨s, rfl⟩ := hsurj w
    simp [e0]
  exact ⟨I, IsLocalRing.le_maximalIdeal hproper, ⟨E.symm⟩⟩

/-- The dual cokernel in basis coordinates agrees with the cokernel of the
dual of the original linear map. -/
def dualCokernelEquiv {P Q : Type} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (p : Module.Basis (Fin a) R P)
    (q : Module.Basis (Fin b) R Q) (d : P →ₗ[R] Q) :
    (Module.Dual R P ⧸ LinearMap.range d.dualMap) ≃ₗ[R] DualCokernel (LinearMap.toMatrix p q d) := by
  have h (x : Module.Dual R Q) :
      p.dualBasis.equivFun (d.dualMap x) =
        (LinearMap.toMatrix p q d).transpose.mulVecLin (q.dualBasis.equivFun x) := by
    rw [← LinearMap.toMatrix_transpose, Matrix.mulVecLin_apply]
    exact (LinearMap.toMatrix_mulVec_repr q.dualBasis p.dualBasis _ x).symm
  refine Submodule.Quotient.equiv _ _ p.dualBasis.equivFun ?_
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, (h z).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨z', rfl⟩ := q.dualBasis.equivFun.surjective z
    exact ⟨_, ⟨z', rfl⟩, h z'⟩

end GlobalTheory.MatrixKernels
