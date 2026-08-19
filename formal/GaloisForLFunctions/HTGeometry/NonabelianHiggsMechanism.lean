import GaloisForLFunctions.HTGeometry.CoatomFixedField
import GaloisForLFunctions.HTGeometry.ColorGramSpecialUnitaryOrbit
import GaloisForLFunctions.HTGeometry.HiggsMechanism

/-!
# Non-Abelian Higgs mechanisms

Two closed models expose different residual-symmetry patterns.

* The noncommutative permutation group `S₃` acts on three degenerate discrete vacua.  Selecting one
  leaves its nontrivial maximal point stabilizer, hence partial breaking `S₃ → S₂`.
* The corpus's `3 × 2` color-event carrier supports left `SU(3)`.  An explicit pair of gauge
  elements proves this concrete group non-Abelian.  The Gram-defect potential is gauge invariant,
  and the canonical regular two-column vacuum has trivial stabilizer, hence complete breaking.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Finite non-Abelian model -/

/-- Discrete orbit-well Higgs mechanism for natural `S₃` action on three states. -/
def finiteNonabelianHiggsMechanism : HiggsMechanism (Equiv.Perm (Fin 3)) (Fin 3) :=
  HiggsMechanism.canonicalOrbitWell 0

/-- Permutation group on three states is non-Abelian. -/
theorem permThree_nonabelian :
    ¬ ∀ g h : Equiv.Perm (Fin 3), g * h = h * g := by
  intro h
  have he := congrArg (fun p : Equiv.Perm (Fin 3) => p 0)
    (h (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2))
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne] at he

/-- All three finite states are degenerate zero-energy vacua. -/
theorem finiteNonabelianHiggs_all_zero (x : Fin 3) :
    finiteNonabelianHiggsMechanism.potential x = 0 := by
  apply HiggsMechanism.potential_eq_zero_of_mem_vacuumOrbit
  rw [HiggsMechanism.vacuumOrbit, MulAction.mem_orbit_iff]
  exact ⟨Equiv.swap 0 x, Equiv.swap_apply_left 0 x⟩

/-- Residual symmetry of selected finite vacuum is maximal proper subgroup. -/
theorem finiteNonabelianHiggs_unbroken_isCoatom :
    IsCoatom finiteNonabelianHiggsMechanism.unbroken :=
  isCoatom_stabilizer_perm 0

/-- Residual finite symmetry is nontrivial: transposition of other two states survives. -/
theorem finiteNonabelianHiggs_unbroken_ne_bot :
    finiteNonabelianHiggsMechanism.unbroken ≠ ⊥ := by
  intro hbot
  have hmem : Equiv.swap (1 : Fin 3) 2 ∈ finiteNonabelianHiggsMechanism.unbroken := by
    rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
    change Equiv.swap (1 : Fin 3) 2 0 = 0
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [hbot] at hmem
  have hone : Equiv.swap (1 : Fin 3) 2 = 1 := by
    change Equiv.swap (1 : Fin 3) 2 = 1 at hmem
    exact hmem
  have he := congrArg (fun p : Equiv.Perm (Fin 3) => p 1) hone
  simp at he

/-- Natural `S₃` vacuum undergoes partial, not complete, symmetry breaking. -/
theorem finiteNonabelianHiggs_partiallyBroken :
    finiteNonabelianHiggsMechanism.IsPartiallyBroken :=
  ⟨finiteNonabelianHiggs_unbroken_ne_bot,
    finiteNonabelianHiggs_unbroken_isCoatom.ne_top⟩

/-! ## `SU(3)` color-event model -/

/-- Concrete color gauge group. -/
abbrev ColorGaugeGroup := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- First explicit color-gauge rotation. -/
def colorGaugeA : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 1]

/-- Second explicit color-gauge rotation. -/
def colorGaugeB : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, 0, 1; 0, -1, 0]

/-- First explicit rotation belongs to `SU(3)`. -/
theorem colorGaugeA_mem : colorGaugeA ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [colorGaugeA, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [colorGaugeA, Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- Second explicit rotation belongs to `SU(3)`. -/
theorem colorGaugeB_mem : colorGaugeB ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [colorGaugeB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [colorGaugeB, Matrix.det_fin_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- First bundled `SU(3)` gauge element. -/
def colorGaugeElementA : ColorGaugeGroup :=
  ⟨colorGaugeA, colorGaugeA_mem⟩

/-- Second bundled `SU(3)` gauge element. -/
def colorGaugeElementB : ColorGaugeGroup :=
  ⟨colorGaugeB, colorGaugeB_mem⟩

/-- Concrete color gauge group is non-Abelian. -/
theorem colorGaugeGroup_nonabelian :
    ¬ ∀ U V : ColorGaugeGroup, U * V = V * U := by
  intro h
  have hm := congrArg (fun U : ColorGaugeGroup => U.1)
    (h colorGaugeElementA colorGaugeElementB)
  have he := congrFun₂ hm 0 1
  norm_num [colorGaugeElementA, colorGaugeElementB, colorGaugeA, colorGaugeB,
    Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- Left multiplication action of `SU(3)` on color events. -/
instance : SMul ColorGaugeGroup ColorEventMatrix :=
  ⟨fun U X => (U.1 : Matrix (Fin 3) (Fin 3) ℂ) * X⟩

/-- Left color-gauge multiplication is a genuine group action. -/
instance : MulAction ColorGaugeGroup ColorEventMatrix where
  one_smul X := by
    change (1 : Matrix (Fin 3) (Fin 3) ℂ) * X = X
    simp
  mul_smul U V X := by
    change ((U.1 * V.1) * X) = U.1 * (V.1 * X)
    rw [Matrix.mul_assoc]

/-- Canonical regular color vacuum: first two coordinate columns. -/
def colorHiggsVacuum : ColorEventMatrix :=
  fun i j => if i.val = j.val then 1 else 0

/-- Canonical color vacuum has identity Gram matrix. -/
theorem colorHiggsVacuum_gram : colorGramMatrix colorHiggsVacuum = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorGramMatrix, colorHiggsVacuum, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Squared Gram defect from orthonormal two-frame vacuum locus. -/
def colorHiggsPotential (X : ColorEventMatrix) : ℝ :=
  ∑ i, ∑ j,
    Complex.normSq (colorGramMatrix X i j - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j)

/-- Every color gauge element is a left isometry. -/
theorem colorGaugeGroup_conjTranspose_mul_self (U : ColorGaugeGroup) :
    (U.1 : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * U.1 = 1 := by
  have hunit : U.1 ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup U.2
  simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hunit

/-- Color Gram-defect potential is `SU(3)`-invariant. -/
theorem colorHiggsPotential_gaugeInvariant (U : ColorGaugeGroup) (X : ColorEventMatrix) :
    colorHiggsPotential (U • X) = colorHiggsPotential X := by
  change colorHiggsPotential (U.1 * X) = colorHiggsPotential X
  rw [colorHiggsPotential, colorHiggsPotential,
    colorGramMatrix_left_invariant U.1 X (colorGaugeGroup_conjTranspose_mul_self U)]

/-- Canonical color vacuum has zero Gram-defect potential. -/
theorem colorHiggsPotential_vacuum : colorHiggsPotential colorHiggsVacuum = 0 := by
  simp [colorHiggsPotential, colorHiggsVacuum_gram]

/-- Color Gram-defect potential is nonnegative. -/
theorem colorHiggsPotential_nonneg (X : ColorEventMatrix) :
    0 ≤ colorHiggsPotential X := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact Complex.normSq_nonneg _

/-- Non-Abelian `SU(3)` Higgs mechanism on color events. -/
def colorHiggsMechanism : HiggsMechanism ColorGaugeGroup ColorEventMatrix where
  vacuum := colorHiggsVacuum
  potential := colorHiggsPotential
  gauge_invariant := colorHiggsPotential_gaugeInvariant
  vacuum_zero := colorHiggsPotential_vacuum
  potential_nonneg := colorHiggsPotential_nonneg

/-- Canonical color vacuum is regular. -/
theorem colorHiggsVacuum_posDef : (colorGramMatrix colorHiggsVacuum).PosDef := by
  rw [colorHiggsVacuum_gram]
  exact Matrix.PosDef.one

/-- Two independent color-vacuum columns break `SU(3)` completely. -/
theorem colorHiggs_unbroken_eq_bot : colorHiggsMechanism.unbroken = ⊥ := by
  ext U
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
  constructor
  · intro hfix
    change U.1 * colorHiggsVacuum = colorHiggsVacuum at hfix
    have hUone : U.1 = 1 :=
      specialUnitary_fix_regular_event_eq_one U.1 colorHiggsVacuum U.2
        colorHiggsVacuum_posDef hfix
    exact Subtype.ext hUone
  · intro hU
    have hUone : U = 1 := by simpa using hU
    rw [hUone]
    exact one_smul _ _

end GaloisForLFunctions.HTGeometry
