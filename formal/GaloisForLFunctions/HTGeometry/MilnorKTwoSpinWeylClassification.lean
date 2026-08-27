import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylMatrix
import Mathlib.GroupTheory.Perm.Sign

/-!
# Classification of the rank-four Spin-Weyl matrix image

The rotor-generated matrix subgroup is exactly the full determinant-one signed-monomial group.
Adjacent rotors lift every permutation.  Squares of the three `(i,3)` rotors generate every
determinant-one diagonal sign, so arbitrary signed-monomial matrices factor into permutation and
diagonal lifts.  No order computation is used.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorSpinWeyl

/-- Full determinant-one signed-monomial subgroup in rank four. -/
def detOneSignedMonomialSubgroup :
    Subgroup (Matrix (Fin 4) (Fin 4) ℝ)ˣ where
  carrier := {A | IsSignedMonomialUnit A ∧
    Matrix.det (A : Matrix (Fin 4) (Fin 4) ℝ) = 1}
  one_mem' := ⟨IsSignedMonomialUnit.one, by simp⟩
  mul_mem' := by
    rintro A B ⟨hA, hAdet⟩ ⟨hB, hBdet⟩
    refine ⟨hA.mul hB, ?_⟩
    rw [Units.val_mul, Matrix.det_mul, hAdet, hBdet, one_mul]
  inv_mem' := by
    rintro A ⟨hA, hAdet⟩
    refine ⟨hA.inv, ?_⟩
    have hdet := congrArg Matrix.det A.inv_val
    rw [Matrix.det_mul, hAdet, Matrix.det_one, mul_one] at hdet
    simpa using hdet

theorem generatedSignedMonomialSubgroup_le_detOne :
    generatedSignedMonomialSubgroup ≤ detOneSignedMonomialSubgroup := by
  intro A hA
  exact ⟨generatedSignedMonomialSubgroup_isSignedMonomial ⟨A, hA⟩,
    generatedSignedMonomialSubgroup_det_one ⟨A, hA⟩⟩

/-- A permutation has a signed-monomial lift in the rotor-generated group. -/
def HasGeneratedSignedLift (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∃ (A : generatedSignedMonomialSubgroup) (c : Fin 4 → ℝˣ),
    (∀ p, c p = 1 ∨ c p = -1) ∧
      (A.1 : Matrix (Fin 4) (Fin 4) ℝ) = signedMonomialMatrix σ c

theorem hasGeneratedSignedLift_one :
    HasGeneratedSignedLift (1 : Equiv.Perm (Fin 4)) := by
  refine ⟨1, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  simp [signedMonomialMatrix_one]

theorem HasGeneratedSignedLift.mul {σ τ : Equiv.Perm (Fin 4)}
    (hσ : HasGeneratedSignedLift σ) (hτ : HasGeneratedSignedLift τ) :
    HasGeneratedSignedLift (σ * τ) := by
  obtain ⟨A, c, hc, hA⟩ := hσ
  obtain ⟨B, d, hd, hB⟩ := hτ
  refine ⟨A * B, fun p => c (τ p) * d p, ?_, ?_⟩
  · intro p
    rcases hc (τ p) with hc' | hc' <;>
      rcases hd p with hd' | hd' <;>
      simp [hc', hd']
  · change (A.1 : Matrix (Fin 4) (Fin 4) ℝ) *
      (B.1 : Matrix (Fin 4) (Fin 4) ℝ) = _
    rw [hA, hB, signedMonomialMatrix_mul]
    rfl

theorem hasGeneratedSignedLift_adjacent (i : Fin 3) :
    HasGeneratedSignedLift (Equiv.swap i.castSucc i.succ) := by
  have hij : (i.castSucc : Fin 4) ≠ i.succ := Fin.ne_of_lt i.castSucc_lt_succ
  let G := spinWeylMatrixGenerator (i.castSucc : Fin 4) i.succ hij
  have hG : G ∈ generatedSignedMonomialSubgroup :=
    Subgroup.subset_closure ⟨i.castSucc, i.succ, hij, rfl⟩
  refine ⟨⟨G, hG⟩,
    steinbergWeylRootScale (i := (i.castSucc : Fin 4)) (j := i.succ) (1 : ℝˣ),
    ?_, ?_⟩
  · intro p
    by_cases hpi : p = (i.castSucc : Fin 4)
    · subst p
      simp [steinbergWeylRootScale]
    · by_cases hpj : p = i.succ
      · subst p
        simp [steinbergWeylRootScale, Ne.symm hij]
      · simp [steinbergWeylRootScale, hpi, hpj]
  · exact spinWeylMatrixGenerator_signedMonomial _ _ hij

theorem hasGeneratedSignedLift_all (σ : Equiv.Perm (Fin 4)) :
    HasGeneratedSignedLift σ := by
  have hmem : σ ∈ Submonoid.closure
      (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ 3]
    exact Submonoid.mem_top σ
  induction hmem using Submonoid.closure_induction with
  | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      exact hasGeneratedSignedLift_adjacent i
  | one => exact hasGeneratedSignedLift_one
  | mul σ τ _ _ hσ hτ => exact hσ.mul hτ

def fin4PairFlipScale (i : Fin 3) (p : Fin 4) : ℝˣ :=
  if p = i.castSucc ∨ p = 3 then -1 else 1

/-- Square of an `(i,3)` rotor flips precisely coordinates `i` and `3`. -/
def generatedPairFlip (i : Fin 3) : generatedSignedMonomialSubgroup := by
  have hi3 : (i.castSucc : Fin 4) ≠ 3 := Fin.ne_of_lt i.isLt
  let G := spinWeylMatrixGenerator (i.castSucc : Fin 4) 3 hi3
  exact ⟨G ^ 2, generatedSignedMonomialSubgroup.pow_mem
    (Subgroup.subset_closure ⟨i.castSucc, 3, hi3, rfl⟩) 2⟩

theorem generatedPairFlip_val (i : Fin 3) :
    ((generatedPairFlip i).1 : Matrix (Fin 4) (Fin 4) ℝ) =
      signedMonomialMatrix 1 (fin4PairFlipScale i) := by
  have hi3 : (i.castSucc : Fin 4) ≠ 3 := Fin.ne_of_lt i.isLt
  simp only [generatedPairFlip]
  rw [pow_two, Units.val_mul,
    spinWeylMatrixGenerator_signedMonomial, signedMonomialMatrix_mul]
  ext r s
  fin_cases i <;> fin_cases s <;>
    simp [steinbergWeylRootScale, fin4PairFlipScale,
      signedMonomialMatrix, Equiv.swap_apply_def]

theorem det_signedMonomialMatrix_one (c : Fin 4 → ℝˣ) :
    Matrix.det (signedMonomialMatrix 1 c) = ∏ p, (c p : ℝ) := by
  rw [show signedMonomialMatrix 1 c = Matrix.diagonal (fun p => (c p : ℝ)) by
    ext r s
    by_cases hrs : r = s
    · subst r
      simp [signedMonomialMatrix]
    · simp [signedMonomialMatrix, hrs]]
  exact Matrix.det_diagonal

def generatedDiagonalSignLift (c : Fin 4 → ℝˣ) :
    generatedSignedMonomialSubgroup :=
  (if c 0 = -1 then generatedPairFlip 0 else 1) *
    (if c 1 = -1 then generatedPairFlip 1 else 1) *
      (if c 2 = -1 then generatedPairFlip 2 else 1)

theorem generatedDiagonalSignLift_val (c : Fin 4 → ℝˣ)
    (hc : ∀ p, c p = 1 ∨ c p = -1)
    (hdet : Matrix.det (signedMonomialMatrix 1 c) = 1) :
    ((generatedDiagonalSignLift c).1 : Matrix (Fin 4) (Fin 4) ℝ) =
      signedMonomialMatrix 1 c := by
  have hprod : ∏ p, (c p : ℝ) = 1 := by
    rw [← det_signedMonomialMatrix_one]
    exact hdet
  rw [Fin.prod_univ_four] at hprod
  rcases hc 0 with h0 | h0 <;>
    rcases hc 1 with h1 | h1 <;>
    rcases hc 2 with h2 | h2 <;>
    rcases hc 3 with h3 | h3
  all_goals
    norm_num [h0, h1, h2, h3] at hprod
  all_goals
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [generatedDiagonalSignLift, h0, h1, h2, h3,
        Units.val_mul, generatedPairFlip_val, signedMonomialMatrix_mul,
        fin4PairFlipScale, signedMonomialMatrix]

theorem diagonalSignedMonomial_mem_generated
    (A : (Matrix (Fin 4) (Fin 4) ℝ)ˣ) (c : Fin 4 → ℝˣ)
    (hc : ∀ p, c p = 1 ∨ c p = -1)
    (hA : (A : Matrix (Fin 4) (Fin 4) ℝ) = signedMonomialMatrix 1 c)
    (hdet : Matrix.det (A : Matrix (Fin 4) (Fin 4) ℝ) = 1) :
    A ∈ generatedSignedMonomialSubgroup := by
  have hD := generatedDiagonalSignLift_val c hc (hA ▸ hdet)
  have hAD : A = (generatedDiagonalSignLift c).1 :=
    Units.ext (hA.trans hD.symm)
  rw [hAD]
  exact (generatedDiagonalSignLift c).2

theorem detOneSignedMonomialSubgroup_le_generated :
    detOneSignedMonomialSubgroup ≤ generatedSignedMonomialSubgroup := by
  intro A hAfull
  obtain ⟨⟨σ, c, hc, hAmatrix⟩, hAdet⟩ := hAfull
  obtain ⟨G, g, hg, hGmatrix⟩ := hasGeneratedSignedLift_all σ
  let d : Fin 4 → ℝˣ := fun p => (g p)⁻¹ * c p
  have hd : ∀ p, d p = 1 ∨ d p = -1 := by
    intro p
    rcases hg p with hg' | hg' <;>
      rcases hc p with hc' | hc' <;>
      simp [d, hg', hc']
  let D : (Matrix (Fin 4) (Fin 4) ℝ)ˣ := G.1⁻¹ * A
  have hDmatrix : (D : Matrix (Fin 4) (Fin 4) ℝ) =
      signedMonomialMatrix 1 d := by
    change ((G.1⁻¹ : (Matrix (Fin 4) (Fin 4) ℝ)ˣ) :
        Matrix (Fin 4) (Fin 4) ℝ) *
      (A : Matrix (Fin 4) (Fin 4) ℝ) = _
    rw [signedMonomialMatrix_inv_data G.1 σ g hGmatrix,
      hAmatrix, signedMonomialMatrix_mul]
    congr 1
    · ext p
      simp
    · funext p
      simp [d]
  have hGdet : Matrix.det (G.1 : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
    generatedSignedMonomialSubgroup_det_one G
  have hGinvdet : Matrix.det
      ((G.1⁻¹ : (Matrix (Fin 4) (Fin 4) ℝ)ˣ) :
        Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
    have h := congrArg Matrix.det G.1.inv_val
    rw [Matrix.det_mul, hGdet, Matrix.det_one, mul_one] at h
    simpa using h
  have hDdet : Matrix.det (D : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
    change Matrix.det
      (((G.1⁻¹ : (Matrix (Fin 4) (Fin 4) ℝ)ˣ) :
          Matrix (Fin 4) (Fin 4) ℝ) *
        (A : Matrix (Fin 4) (Fin 4) ℝ)) = 1
    rw [Matrix.det_mul, hGinvdet, hAdet, one_mul]
  have hDmem : D ∈ generatedSignedMonomialSubgroup :=
    diagonalSignedMonomial_mem_generated D d hd hDmatrix hDdet
  have hfactor : G.1 * D = A := by
    simp [D]
  rw [← hfactor]
  exact generatedSignedMonomialSubgroup.mul_mem G.2 hDmem

/-- Rotor matrices are exactly the determinant-one signed-monomial matrices in rank four. -/
theorem generatedSignedMonomialSubgroup_eq_detOne :
    generatedSignedMonomialSubgroup = detOneSignedMonomialSubgroup :=
  le_antisymm generatedSignedMonomialSubgroup_le_detOne
    detOneSignedMonomialSubgroup_le_generated

end MilnorSpinWeyl
end GaloisForLFunctions.HTGeometry

end
