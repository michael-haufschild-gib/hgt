import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeCartan
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpResidue
import GaloisForLFunctions.HTGeometry.DifferentialOperatorSemilinearMatrix

/-!
# Uniqueness of completed pseudodifferential Cartan coweights

A completed-skew linear equivalence preserving the standard valuation lattice restricts to an
integral linear equivalence.  Reduction of its matrix modulo the strict valuation ideal is a unit
over the residue skew field.  Zero patterns of that unit give Hall dimension inequalities for all
coweight sublevel sets.  Applying the same argument to the inverse recovers every multiplicity,
so two diagonal lattices in one standard frame have coweights differing only by a permutation.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

section MatrixSupport

variable {D : Type v} [DivisionRing D] {r : ℕ}

private def extendFromFinset (A : Finset (Fin r)) (x : A → D) : Fin r → D :=
  fun i => if hi : i ∈ A then x ⟨i, hi⟩ else 0

/-- An invertible matrix whose selected input rows are supported on selected output columns forces
the input set to have no larger cardinality.  This is the division-ring form of the Hall rank
inequality. -/
theorem card_le_card_of_matrixUnit_rowSupport
    (U : (Matrix (Fin r) (Fin r) D)ˣ) (A B : Finset (Fin r))
    (hsupport : ∀ i ∈ A, ∀ j, (U : Matrix (Fin r) (Fin r) D) i j ≠ 0 → j ∈ B) :
    A.card ≤ B.card := by
  classical
  let f : (A → D) →ₗ[D] (B → D) :=
    { toFun := fun x j => Matrix.vecMul (extendFromFinset A x)
        (U : Matrix (Fin r) (Fin r) D) j.1
      map_add' := by
        intro x y
        funext j
        change Matrix.vecMul (extendFromFinset A (x + y))
          (U : Matrix (Fin r) (Fin r) D) j.1 =
          Matrix.vecMul (extendFromFinset A x) (U : Matrix (Fin r) (Fin r) D) j.1 +
            Matrix.vecMul (extendFromFinset A y) (U : Matrix (Fin r) (Fin r) D) j.1
        change (∑ i, extendFromFinset A (x + y) i *
          (U : Matrix (Fin r) (Fin r) D) i j.1) =
          (∑ i, extendFromFinset A x i * (U : Matrix (Fin r) (Fin r) D) i j.1) +
          ∑ i, extendFromFinset A y i * (U : Matrix (Fin r) (Fin r) D) i j.1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ A <;> simp [extendFromFinset, hi, add_mul]
      map_smul' := by
        intro c x
        funext j
        change Matrix.vecMul (extendFromFinset A (c • x))
          (U : Matrix (Fin r) (Fin r) D) j.1 =
          c * Matrix.vecMul (extendFromFinset A x)
            (U : Matrix (Fin r) (Fin r) D) j.1
        change (∑ i, extendFromFinset A (c • x) i *
          (U : Matrix (Fin r) (Fin r) D) i j.1) =
          c * ∑ i, extendFromFinset A x i * (U : Matrix (Fin r) (Fin r) D) i j.1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ A <;> simp [extendFromFinset, hi, mul_assoc] }
  have hf : Function.Injective f := by
    intro x y hxy
    let x' : Fin r → D := extendFromFinset A x
    let y' : Fin r → D := extendFromFinset A y
    have hmul : Matrix.vecMul x' (U : Matrix (Fin r) (Fin r) D) =
        Matrix.vecMul y' (U : Matrix (Fin r) (Fin r) D) := by
      funext j
      by_cases hj : j ∈ B
      · have hjxy := congrFun hxy ⟨j, hj⟩
        exact hjxy
      · rw [Matrix.vecMul, Matrix.vecMul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ A
        · have hU : (U : Matrix (Fin r) (Fin r) D) i j = 0 := by
            by_contra hU
            exact hj (hsupport i hi j hU)
          simp [x', y', hi, hU]
        · simp [x', y', extendFromFinset, hi]
    have hfull : x' = y' := by
      have h := congrArg
        (fun z => Matrix.vecMul z ((U⁻¹ : (Matrix (Fin r) (Fin r) D)ˣ) :
          Matrix (Fin r) (Fin r) D)) hmul
      simpa [Matrix.vecMul_vecMul] using h
    funext i
    have hi := congrFun hfull i.1
    simpa [x', y', extendFromFinset, i.2] using hi
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_pi] using hdim

end MatrixSupport

section Stabilizer

variable {r : ℕ}

private def completedPseudoDiffOpIntegralVecCoe
    (x : Fin r → CompletedPseudoDiffOpInteger (K := K)) :
    Fin r → CompletedPseudoDiffOp K := fun i => x i

/-- A completed-skew linear equivalence preserving the standard lattice restricts to an integral
linear equivalence on its coordinate module. -/
noncomputable def restrictCompletedPseudoDiffOpStandardLinearEquiv
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) :
    (Fin r → CompletedPseudoDiffOpInteger (K := K)) ≃ₗ[
      CompletedPseudoDiffOpInteger (K := K)]
      (Fin r → CompletedPseudoDiffOpInteger (K := K)) where
  toFun x i := by
    let xF := completedPseudoDiffOpIntegralVecCoe x
    have hx : xF ∈ (standardCompletedPseudoDiffOpLattice
        (K := K) (ι := Fin r)).carrier :=
      (mem_standardCompletedPseudoDiffOpLattice_iff xF).2 fun j => (x j).property
    have he : e xF ∈ (mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))).carrier :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e _ _).2 ⟨xF, hx, rfl⟩
    rw [hstd] at he
    exact ⟨e xF i, (mem_standardCompletedPseudoDiffOpLattice_iff (e xF)).1 he i⟩
  invFun y i := by
    let yF := completedPseudoDiffOpIntegralVecCoe y
    have hy : yF ∈ (standardCompletedPseudoDiffOpLattice
        (K := K) (ι := Fin r)).carrier :=
      (mem_standardCompletedPseudoDiffOpLattice_iff yF).2 fun j => (y j).property
    refine ⟨e.symm yF i, ?_⟩
    have hpre : e.symm yF ∈ (standardCompletedPseudoDiffOpLattice
        (K := K) (ι := Fin r)).carrier := by
      have hy' : yF ∈ (mapCompletedPseudoDiffOpLatticeLinear e
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))).carrier := by
        rw [hstd]
        exact hy
      rcases (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e _ yF).1 hy' with
        ⟨x, hx, hex⟩
      have heq : e.symm yF = x := by rw [← hex]; simp
      rwa [heq]
    exact (mem_standardCompletedPseudoDiffOpLattice_iff (e.symm yF)).1 hpre i
  left_inv x := by
    ext i
    change e.symm (e (completedPseudoDiffOpIntegralVecCoe x)) i = x i
    simp [completedPseudoDiffOpIntegralVecCoe]
  right_inv y := by
    ext i
    change e (e.symm (completedPseudoDiffOpIntegralVecCoe y)) i = y i
    simp [completedPseudoDiffOpIntegralVecCoe]
  map_add' x y := by
    ext i
    change e (completedPseudoDiffOpIntegralVecCoe (x + y)) i =
      e (completedPseudoDiffOpIntegralVecCoe x) i +
        e (completedPseudoDiffOpIntegralVecCoe y) i
    rw [show completedPseudoDiffOpIntegralVecCoe (x + y) =
      completedPseudoDiffOpIntegralVecCoe x + completedPseudoDiffOpIntegralVecCoe y by rfl]
    exact congrFun (e.map_add _ _) i
  map_smul' c x := by
    ext i
    change e (completedPseudoDiffOpIntegralVecCoe (c • x)) i =
      (c : CompletedPseudoDiffOp K) * e (completedPseudoDiffOpIntegralVecCoe x) i
    rw [show completedPseudoDiffOpIntegralVecCoe (c • x) =
      (c : CompletedPseudoDiffOp K) • completedPseudoDiffOpIntegralVecCoe x by rfl]
    exact congrFun (e.map_smul (c : CompletedPseudoDiffOp K) _) i

/-- Integral coordinate matrix of a standard-lattice stabilizer, packaged with its inverse. -/
noncomputable def completedPseudoDiffOpStandardStabilizerMatrixUnit
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) :
    (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOpInteger (K := K)))ˣ := by
  let E := restrictCompletedPseudoDiffOpStandardLinearEquiv e hstd
  exact basisMapMatrixUnitOfSemilinearEquiv
    (σ := RingEquiv.refl (CompletedPseudoDiffOpInteger (K := K)))
    (Pi.basisFun (CompletedPseudoDiffOpInteger (K := K)) (Fin r)) E E.symm
    E.map_add E.map_smul E.symm.map_add E.symm.map_smul
    E.apply_symm_apply E.symm_apply_apply

/-- Entry of the integral stabilizer matrix is the corresponding ambient basis coefficient. -/
theorem completedPseudoDiffOpStandardStabilizerMatrixUnit_apply
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (i j : Fin r) :
    ((completedPseudoDiffOpStandardStabilizerMatrixUnit e hstd :
        Matrix (Fin r) (Fin r) (CompletedPseudoDiffOpInteger (K := K))) i j :
      CompletedPseudoDiffOp K) =
      e (Pi.basisFun (CompletedPseudoDiffOp K) (Fin r) i) j := by
  classical
  simp [completedPseudoDiffOpStandardStabilizerMatrixUnit,
    basisMapMatrixUnitOfSemilinearEquiv, basisMapMatrix,
    restrictCompletedPseudoDiffOpStandardLinearEquiv]
  apply congrArg (fun z : Fin r → CompletedPseudoDiffOp K => e z j)
  funext k
  by_cases hik : i = k <;> simp [completedPseudoDiffOpIntegralVecCoe, hik]

/-- Entrywise ring maps induce a monoid homomorphism on square matrices. -/
def matrixMapMonoidHom {R S : Type*} [Semiring R] [Semiring S]
    (q : R →+* S) (r : ℕ) : Matrix (Fin r) (Fin r) R →*
      Matrix (Fin r) (Fin r) S where
  toFun M := M.map q
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' A B := Matrix.map_mul

/-- Reduction of a standard-lattice stabilizer is an invertible matrix over the residue skew
field. -/
noncomputable def completedPseudoDiffOpStandardStabilizerResidueMatrixUnit
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) :
    (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOpResidue K))ˣ :=
  Units.map (matrixMapMonoidHom completedPseudoDiffOpResidueMap r)
    (completedPseudoDiffOpStandardStabilizerMatrixUnit e hstd)

/-- A nonzero residue entry of a standard-lattice stabilizer can only carry a coweight coordinate
to one of no larger weight. -/
theorem coweight_le_of_standardStabilizer_residue_entry_ne_zero
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (m n : Fin r → ℤ)
    (hmn : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n)
    (i j : Fin r)
    (hij : (completedPseudoDiffOpStandardStabilizerResidueMatrixUnit e hstd :
      Matrix (Fin r) (Fin r) (CompletedPseudoDiffOpResidue K)) i j ≠ 0) :
    n j ≤ m i := by
  classical
  let UO := completedPseudoDiffOpStandardStabilizerMatrixUnit e hstd
  let a : CompletedPseudoDiffOp K :=
    e (Pi.basisFun (CompletedPseudoDiffOp K) (Fin r) i) j
  have hq : completedPseudoDiffOpResidueMap (UO.1 i j) ≠ 0 := by
    exact hij
  have hvalO := (completedPseudoDiffOpResidueMap_ne_zero_iff (UO.1 i j)).1 hq
  have hval : completedPseudoDiffOpValuation a = 1 := by
    change completedPseudoDiffOpValuation
      (e (Pi.basisFun (CompletedPseudoDiffOp K) (Fin r) i) j) = 1
    rw [← completedPseudoDiffOpStandardStabilizerMatrixUnit_apply e hstd i j]
    exact hvalO
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, map_zero] at hval
    exact zero_ne_one hval
  let au : (CompletedPseudoDiffOp K)ˣ := Units.mk0 a ha0
  have hau : completedPseudoDiffOpUnitAddValue au = 0 := by
    apply WithTop.coe_injective
    rw [← completedPseudoDiffOpAddValue_unit_eq_coe]
    change Multiplicative.toAdd (completedPseudoDiffOpValuation a) = (0 : WithTop ℤ)
    rw [hval]
    rfl
  let v := completedPseudoDiffOpCoweightBasisVector (K := K) m i
  have hv : v ∈ (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier :=
    completedPseudoDiffOpCoweightBasisVector_mem m i
  have hev : e v ∈ (mapCompletedPseudoDiffOpLatticeLinear e
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m)).carrier :=
    (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e _ _).2 ⟨v, hv, rfl⟩
  rw [hmn] at hev
  have hj := (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff n (e v)).1 hev j
  have hvEq : v =
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ m i : CompletedPseudoDiffOp K) •
        Pi.basisFun (CompletedPseudoDiffOp K) (Fin r) i := by
    funext k
    by_cases hik : i = k
    · subst k
      simp [v, completedPseudoDiffOpCoweightBasisVector,
        diagonalRightMulCompletedPseudoIntegerVecLinearEquiv,
        completedPseudoDiffOpUniformizerCoweight]
    · simp [v, completedPseudoDiffOpCoweightBasisVector,
        diagonalRightMulCompletedPseudoIntegerVecLinearEquiv,
        completedPseudoDiffOpUniformizerCoweight, hik]
  rw [hvEq, e.map_smul] at hj
  let u : (CompletedPseudoDiffOp K)ˣ :=
    completedPseudoDiffOpUniformizerUnit (K := K) ^ m i * au *
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ n j)⁻¹
  have hu : (u : CompletedPseudoDiffOp K) ∈ CompletedPseudoDiffOpInteger (K := K) := by
    simpa [u, au, a, completedPseudoDiffOpUniformizerCoweight, mul_assoc] using hj
  rw [coe_unit_mem_completedPseudoDiffOpInteger_iff] at hu
  dsimp [u] at hu
  rw [completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow, hau,
    completedPseudoDiffOpUnitAddValue_inv,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hu
  omega

/-- Coweight coordinates at most a given integral threshold. -/
def completedPseudoDiffOpCoweightSublevel
    (m : Fin r → ℤ) (t : ℤ) : Finset (Fin r) :=
  Finset.univ.filter fun i => m i ≤ t

/-- A standard-lattice stabilizer mapping one diagonal lattice to another cannot decrease the
number of coordinates below any threshold. -/
theorem card_coweightSublevel_le_of_standardStabilizer
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (m n : Fin r → ℤ)
    (hmn : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n)
    (t : ℤ) :
    (completedPseudoDiffOpCoweightSublevel m t).card ≤
      (completedPseudoDiffOpCoweightSublevel n t).card := by
  classical
  apply card_le_card_of_matrixUnit_rowSupport
    (completedPseudoDiffOpStandardStabilizerResidueMatrixUnit e hstd)
  intro i hi j hij
  rw [completedPseudoDiffOpCoweightSublevel, Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ _,
    (coweight_le_of_standardStabilizer_residue_entry_ne_zero
      e hstd m n hmn i j hij).trans hi.2⟩

/-- A standard-lattice stabilizer preserves every coweight sublevel cardinality. -/
theorem card_coweightSublevel_eq_of_standardStabilizer
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (m n : Fin r → ℤ)
    (hmn : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n)
    (t : ℤ) :
    (completedPseudoDiffOpCoweightSublevel m t).card =
      (completedPseudoDiffOpCoweightSublevel n t).card := by
  apply le_antisymm
  · exact card_coweightSublevel_le_of_standardStabilizer e hstd m n hmn t
  · have hstd' : mapCompletedPseudoDiffOpLatticeLinear e.symm
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
        standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
      calc
        _ = mapCompletedPseudoDiffOpLatticeLinear e.symm
            (mapCompletedPseudoDiffOpLatticeLinear e
              (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) :=
          congrArg (mapCompletedPseudoDiffOpLatticeLinear e.symm) hstd.symm
        _ = _ := by
          rw [mapCompletedPseudoDiffOpLatticeLinear_trans,
            LinearEquiv.self_trans_symm, mapCompletedPseudoDiffOpLatticeLinear_refl]
    have hnm : mapCompletedPseudoDiffOpLatticeLinear e.symm
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n) =
        standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m := by
      calc
        _ = mapCompletedPseudoDiffOpLatticeLinear e.symm
            (mapCompletedPseudoDiffOpLatticeLinear e
              (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m)) :=
          congrArg (mapCompletedPseudoDiffOpLatticeLinear e.symm) hmn.symm
        _ = _ := by
          rw [mapCompletedPseudoDiffOpLatticeLinear_trans,
            LinearEquiv.self_trans_symm, mapCompletedPseudoDiffOpLatticeLinear_refl]
    exact card_coweightSublevel_le_of_standardStabilizer e.symm hstd' n m hnm t

/-- Coweight coordinates equal to one specified integer. -/
def completedPseudoDiffOpCoweightFiber
    (m : Fin r → ℤ) (z : ℤ) : Finset (Fin r) :=
  Finset.univ.filter fun i => m i = z

theorem completedPseudoDiffOpCoweightFiber_eq_sdiff
    (m : Fin r → ℤ) (z : ℤ) :
    completedPseudoDiffOpCoweightFiber m z =
      completedPseudoDiffOpCoweightSublevel m z \
        completedPseudoDiffOpCoweightSublevel m (z - 1) := by
  classical
  ext i
  simp [completedPseudoDiffOpCoweightFiber,
    completedPseudoDiffOpCoweightSublevel]
  omega

/-- Equality of all sublevel counts gives equality of every exact coweight multiplicity. -/
theorem card_coweightFiber_eq_of_sublevels
    (m n : Fin r → ℤ)
    (hsub : ∀ t,
      (completedPseudoDiffOpCoweightSublevel m t).card =
        (completedPseudoDiffOpCoweightSublevel n t).card)
    (z : ℤ) :
    (completedPseudoDiffOpCoweightFiber m z).card =
      (completedPseudoDiffOpCoweightFiber n z).card := by
  classical
  rw [completedPseudoDiffOpCoweightFiber_eq_sdiff,
    completedPseudoDiffOpCoweightFiber_eq_sdiff,
    Finset.card_sdiff, Finset.card_sdiff]
  have hm : completedPseudoDiffOpCoweightSublevel m (z - 1) ∩
      completedPseudoDiffOpCoweightSublevel m z =
      completedPseudoDiffOpCoweightSublevel m (z - 1) := by
    ext i
    simp [completedPseudoDiffOpCoweightSublevel]
    omega
  have hn : completedPseudoDiffOpCoweightSublevel n (z - 1) ∩
      completedPseudoDiffOpCoweightSublevel n z =
      completedPseudoDiffOpCoweightSublevel n (z - 1) := by
    ext i
    simp [completedPseudoDiffOpCoweightSublevel]
    omega
  rw [hm, hn, hsub z, hsub (z - 1)]

/-- **Uniqueness of the completed Cartan coweight.**  If a completed-skew frame preserves the
standard lattice and maps `L_m` to `L_n`, then `m` and `n` differ only by a Weyl permutation. -/
theorem exists_perm_of_standardStabilizer_map_coweight
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (hstd : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (m n : Fin r → ℤ)
    (hmn : mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n) :
    ∃ w : Equiv.Perm (Fin r), m = fun i => n (w i) := by
  classical
  have hfiber : ∀ z : ℤ,
      Fintype.card {i : Fin r // m i = z} =
        Fintype.card {i : Fin r // n i = z} := by
    intro z
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact card_coweightFiber_eq_of_sublevels m n
      (card_coweightSublevel_eq_of_standardStabilizer e hstd m n hmn) z
  let wFiber : ∀ z : ℤ, {i : Fin r // m i = z} ≃ {i : Fin r // n i = z} :=
    fun z => Fintype.equivOfCardEq (hfiber z)
  let w : Equiv.Perm (Fin r) := Equiv.ofFiberEquiv wFiber
  refine ⟨w, ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map wFiber i).symm

/-- **Frame-independence of the completed Cartan coweight.**  Any two simultaneous Cartan
reductions of the same ordered lattice pair have coweights differing only by a Weyl permutation.
-/
theorem exists_perm_of_completedPseudoDiffOpLattice_pair_cartan
    (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (e f : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (m n : Fin r → ℤ)
    (heL : mapCompletedPseudoDiffOpLatticeLinear e L =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (heM : mapCompletedPseudoDiffOpLatticeLinear e M =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m)
    (hfL : mapCompletedPseudoDiffOpLatticeLinear f L =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (hfM : mapCompletedPseudoDiffOpLatticeLinear f M =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n) :
    ∃ w : Equiv.Perm (Fin r), m = fun i => n (w i) := by
  let g := e.symm.trans f
  have heL' : mapCompletedPseudoDiffOpLatticeLinear e.symm
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) = L := by
    calc
      _ = mapCompletedPseudoDiffOpLatticeLinear e.symm
          (mapCompletedPseudoDiffOpLatticeLinear e L) :=
        congrArg (mapCompletedPseudoDiffOpLatticeLinear e.symm) heL.symm
      _ = _ := by
        rw [mapCompletedPseudoDiffOpLatticeLinear_trans,
          LinearEquiv.self_trans_symm, mapCompletedPseudoDiffOpLatticeLinear_refl]
  have heM' : mapCompletedPseudoDiffOpLatticeLinear e.symm
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) = M := by
    calc
      _ = mapCompletedPseudoDiffOpLatticeLinear e.symm
          (mapCompletedPseudoDiffOpLatticeLinear e M) :=
        congrArg (mapCompletedPseudoDiffOpLatticeLinear e.symm) heM.symm
      _ = _ := by
        rw [mapCompletedPseudoDiffOpLatticeLinear_trans,
          LinearEquiv.self_trans_symm, mapCompletedPseudoDiffOpLatticeLinear_refl]
  have hgL : mapCompletedPseudoDiffOpLatticeLinear g
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, heL', hfL]
  have hgM : mapCompletedPseudoDiffOpLatticeLinear g
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, heM', hfM]
  exact exists_perm_of_standardStabilizer_map_coweight g hgL m n hgM

end Stabilizer

end

end DiffOp

end GaloisForLFunctions.HTGeometry
