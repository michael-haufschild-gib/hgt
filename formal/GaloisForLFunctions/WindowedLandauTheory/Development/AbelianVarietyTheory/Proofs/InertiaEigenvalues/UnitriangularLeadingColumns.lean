import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter

/-! An upper unitriangular matrix fixing the leading coordinate vectors
has identity first diagonal block. Fixing one more vector cuts out the
first column of the upper-right rectangle. -/

noncomputable section
open scoped Classical
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- A matrix fixes the first `k` standard coordinate vectors. -/
def FixLeadingColumns (k : ℕ) (M : Mt g n) : Prop :=
  ∀ i j : Fin n, j.val < k → M i j = (1 : Mt g n) i j

/-- The first column of an upper unitriangular matrix is the first standard vector. -/
theorem fixLeadingColumns_one {M : Mt g n} (h : IsUniUp M) : FixLeadingColumns 1 M := by
  intro i j hj
  by_cases hij : i = j
  · subst j
    rw [(h i i).2 rfl, Matrix.one_apply_eq]
  · have hj' : j.val < i.val := by
      have e : i.val ≠ j.val := fun e => hij (Fin.ext e)
      omega
    rw [(h i j).1 hj', Matrix.one_apply_ne hij]

variable {a b : ℕ}

private theorem castAdd_ne_natAdd (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have e : i.val = a + j.val := congrArg Fin.val h
  have hi := i.isLt
  omega

/-- An identity leading block and unitriangular trailing block assemble to
an upper unitriangular matrix. -/
theorem isUniUp_upperBlockMatrix (X : Matrix (Fin a) (Fin b) (ZMod g))
    {D : Mt g b} (hD : IsUniUp D) : IsUniUp (upperBlockMatrix (1 : Mt g a) X D) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁]
    exact ⟨fun h => Matrix.one_apply_ne (fun e => (ne_of_gt h) (congrArg (Fin.castAdd b) e)),
      fun h => by rw [Fin.castAdd_inj.mp h, Matrix.one_apply_eq]⟩
  · have hne := castAdd_ne_natAdd i j
    refine ⟨fun h => ?_, fun h => (hne h).elim⟩
    change a + j.val < i.val at h
    omega
  · refine ⟨fun _ => ?_, fun h => (castAdd_ne_natAdd j i h.symm).elim⟩
    simp [upperBlockMatrix]
  · simp only [upperBlockMatrix, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂]
    exact ⟨fun h => (hD i j).1 (Nat.lt_of_add_lt_add_left h),
      fun h => (hD i j).2 ((Fin.natAdd_inj a).mp h)⟩

theorem fixLeadingColumns_upperBlockMatrix (X : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    FixLeadingColumns a (upperBlockMatrix (1 : Mt g a) X D) := by
  intro i j hj
  let j' : Fin a := ⟨j.val, hj⟩
  rw [← show Fin.castAdd b j' = j from Fin.ext rfl]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [upperBlockMatrix, Matrix.one_apply, Fin.castAdd_inj]
  · simp [upperBlockMatrix, (castAdd_ne_natAdd j' i).symm]

/-- Within the upper unitriangular group, fixing the leading coordinates
gives an identity leading block. -/
theorem exists_upperBlockUnit_of_fixLeadingColumns (x : upperUnitriangular g (a + b))
    (h : FixLeadingColumns a x.val.val) :
    ∃ (X : Matrix (Fin a) (Fin b) (ZMod g)) (D : upperUnitriangular g b),
      x.val = upperBlockUnit 1 X D.val := by
  have hx : IsUniUp x.val.val := x.property
  let p : twoBlockParabolic g a b :=
    ⟨x.val, fun i j hj hi => (hx i j).1 (hj.trans_le hi)⟩
  let l := twoBlockLevi p
  have hA : l.1 = 1 := by
    apply Units.ext
    change tl a x.val.val = 1
    ext i j
    rw [tl_apply_add, h _ _ j.isLt]
    simp [Matrix.one_apply, Fin.castAdd_inj]
  have hD : l.2 ∈ upperUnitriangular g b := by
    intro i j
    change (j < i → br a b x.val.val i j = 0) ∧ (i = j → br a b x.val.val i j = 1)
    rw [br_apply_add]
    exact ⟨fun h => (hx _ _).1 (Nat.add_lt_add_left h _),
      fun h => (hx _ _).2 (congrArg (Fin.natAdd a) h)⟩
  refine ⟨upperRightBlock x.val.val, ⟨l.2, hD⟩, ?_⟩
  exact (upperBlockUnit_eq_of_mem_parabolic p).symm.trans
    (congrArg (fun A => upperBlockUnit A (upperRightBlock x.val.val) l.2) hA)

/-- For a unitriangular trailing block, one more fixed leading column is
equivalent to vanishing of the first column of the rectangle. -/
theorem fixLeadingColumns_succ_iff {X : Matrix (Fin a) (Fin (b + 1)) (ZMod g)}
    {D : Mt g (b + 1)} (hD : IsUniUp D) :
    FixLeadingColumns (a + 1) (upperBlockMatrix (1 : Mt g a) X D) ↔ ∀ i, X i 0 = 0 := by
  constructor
  · intro h i
    have e := h (Fin.castAdd (b + 1) i) (Fin.natAdd a 0) (by simp)
    simpa [upperBlockMatrix, Matrix.one_apply, castAdd_ne_natAdd] using e
  · intro h i j hj
    by_cases hlt : j.val < a
    · exact fixLeadingColumns_upperBlockMatrix X D i j hlt
    · have hj' : Fin.natAdd a (0 : Fin (b + 1)) = j := Fin.ext (by simpa using (show a = j.val by omega))
      rw [← hj']
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp [upperBlockMatrix, castAdd_ne_natAdd, h]
      · have e := fixLeadingColumns_one hD i (0 : Fin (b + 1)) (by simp)
        simpa [upperBlockMatrix, Matrix.one_apply, Fin.natAdd_inj] using e

end GlobalTheory.GLq
