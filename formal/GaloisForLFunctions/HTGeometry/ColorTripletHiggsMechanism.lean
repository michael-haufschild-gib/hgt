import GaloisForLFunctions.HTGeometry.NonabelianHiggsMechanism

/-!
# Single-triplet `SU(3)` Higgs mechanism

A rank-one color vacuum retains a nontrivial gauge transformation while breaking
another explicit generator.  This contrasts with the regular two-column vacuum,
whose stabilizer is trivial.
-/

open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

def colorTripletHiggsVacuum : ColorEventMatrix :=
  !![1, 0; 0, 0; 0, 0]

theorem colorTripletHiggsVacuum_gram :
    colorGramMatrix colorTripletHiggsVacuum = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [colorGramMatrix, colorTripletHiggsVacuum, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

def colorTripletHiggsPotential (X : ColorEventMatrix) : ℝ :=
  ∑ i, ∑ j, Complex.normSq
    (colorGramMatrix X i j - colorGramMatrix colorTripletHiggsVacuum i j)

theorem colorTripletHiggsPotential_gaugeInvariant (U : ColorGaugeGroup)
    (X : ColorEventMatrix) :
    colorTripletHiggsPotential (U • X) = colorTripletHiggsPotential X := by
  change colorTripletHiggsPotential (U.1 * X) = colorTripletHiggsPotential X
  rw [colorTripletHiggsPotential, colorTripletHiggsPotential,
    colorGramMatrix_left_invariant U.1 X (colorGaugeGroup_conjTranspose_mul_self U)]

theorem colorTripletHiggsPotential_vacuum :
    colorTripletHiggsPotential colorTripletHiggsVacuum = 0 := by
  simp [colorTripletHiggsPotential]

theorem colorTripletHiggsPotential_nonneg (X : ColorEventMatrix) :
    0 ≤ colorTripletHiggsPotential X := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact Complex.normSq_nonneg _

def colorTripletHiggsMechanism : HiggsMechanism ColorGaugeGroup ColorEventMatrix where
  vacuum := colorTripletHiggsVacuum
  potential := colorTripletHiggsPotential
  gauge_invariant := colorTripletHiggsPotential_gaugeInvariant
  vacuum_zero := colorTripletHiggsPotential_vacuum
  potential_nonneg := colorTripletHiggsPotential_nonneg

theorem colorGaugeB_fixes_tripletVacuum :
    colorGaugeElementB • colorTripletHiggsVacuum = colorTripletHiggsVacuum := by
  change colorGaugeB * colorTripletHiggsVacuum = colorTripletHiggsVacuum
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [colorGaugeElementB, colorGaugeB, colorTripletHiggsVacuum,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem colorGaugeElementB_ne_one : colorGaugeElementB ≠ 1 := by
  intro h
  have hm := congrArg (fun U : ColorGaugeGroup => U.1) h
  have he := congrFun₂ hm 1 2
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  simp [colorGaugeElementB, colorGaugeB, h12] at he

theorem colorTripletHiggs_unbroken_ne_bot :
    colorTripletHiggsMechanism.unbroken ≠ ⊥ := by
  intro hbot
  have hmem : colorGaugeElementB ∈ colorTripletHiggsMechanism.unbroken := by
    rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
    exact colorGaugeB_fixes_tripletVacuum
  rw [hbot] at hmem
  exact colorGaugeElementB_ne_one (by simpa using hmem)

theorem colorGaugeA_not_fix_tripletVacuum :
    colorGaugeElementA • colorTripletHiggsVacuum ≠ colorTripletHiggsVacuum := by
  intro h
  change colorGaugeA * colorTripletHiggsVacuum = colorTripletHiggsVacuum at h
  have he := congrFun₂ h 0 0
  norm_num [colorGaugeElementA, colorGaugeA, colorTripletHiggsVacuum,
    Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem colorTripletHiggs_unbroken_ne_top :
    colorTripletHiggsMechanism.unbroken ≠ ⊤ := by
  intro htop
  have hmem : colorGaugeElementA ∈ colorTripletHiggsMechanism.unbroken := by
    rw [htop]
    simp
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff] at hmem
  exact colorGaugeA_not_fix_tripletVacuum hmem

theorem colorTripletHiggs_partiallyBroken :
    colorTripletHiggsMechanism.IsPartiallyBroken :=
  ⟨colorTripletHiggs_unbroken_ne_bot, colorTripletHiggs_unbroken_ne_top⟩

end GaloisForLFunctions.HTGeometry
