import GaloisForLFunctions.RHTower.MobiusGammaXiGraphNormalComplementTangent

/-!
# Coupled-error singular-graph global wall

The critical graph-normal source/complement defect has escaped Hardy profile
`(1 + u)⁻¹ * d`, where `d` is the continued anti-causal Xi Ward response at
`1 / 2`.  The existing fixed-four Hardy--Fisher wall detects every nonzero
`d`, but that obstruction does not itself construct a lower-semibounded
coupled-error realization.

This file supplies the missing graph completion.  The mass profile is the
literal Cauchy feature at node zero.  Adding `star d` times that feature to
the Fisher vector changes its squared norm from `4` to exactly
`4 + |d|²`.  Hence the completed wall is a congruence of the unconditional
Hardy--Fisher Gram, and the uncompleted wall has the sharp global lower bound
`-|d|²` on the divisor coordinate.
-/

open Complex Filter Set Topology
open scoped BigOperators ComplexOrder

noncomputable section

namespace RHTower

/-- Adjoin the critical zero node before a finite inward Hardy packet. -/
def mobiusCriticalHardyZeroAdjoinedNodes
    {n : ℕ} (u : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cases 0 u

/-- Coordinate embedding which replaces the Fisher vector by
`F + star d • k₀`.  The extra zero-node coordinate is the singular graph
leg; all original Hardy coordinates are shifted by one. -/
def mobiusCriticalHardySingularGraphEmbedding
    {n : ℕ} (d : ℂ) :
    Matrix (Fin (n + 1) ⊕ Unit) (Fin n ⊕ Unit) ℂ
  | Sum.inl i, Sum.inl j =>
      Fin.cases 0 (fun k => if k = j then 1 else 0) i
  | Sum.inl i, Sum.inr _ => Fin.cases (star d) (fun _ => 0) i
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 1

/-- **Exact singular-graph congruence.**  The mass-perturbed wall at budget
`4 + |d|²` is the pullback of the ordinary Hardy--Fisher Gram after adjoining
the zero-node graph leg. -/
theorem mobiusCriticalMassPerturbed_exactGraphBudget_congruence
    {n : ℕ} (u : Fin n → ℂ) (d : ℂ) :
    (mobiusCriticalHardySingularGraphEmbedding (n := n) d).conjTranspose *
        mobiusCriticalUniversalHardyFisherGram
          (mobiusCriticalHardyZeroAdjoinedNodes u) *
        mobiusCriticalHardySingularGraphEmbedding (n := n) d =
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
        u d (4 + Complex.normSq d) := by
  ext a b
  rcases a with i | z <;> rcases b with j | w
  · simp [Matrix.mul_apply, mobiusCriticalHardySingularGraphEmbedding,
      mobiusCriticalHardyZeroAdjoinedNodes, Fin.sum_univ_succ,
      mobiusCriticalUniversalHardyFisherGram,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram]
  · simp [Matrix.mul_apply, mobiusCriticalHardySingularGraphEmbedding,
      mobiusCriticalHardyZeroAdjoinedNodes, Fin.sum_univ_succ,
      mobiusCriticalUniversalHardyFisherGram,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusCriticalUniversalHardyKernel,
      mobiusCriticalUniversalFisherScore,
      mobiusCriticalUniversalHardyMassProfile]
    ring
  · simp [Matrix.mul_apply, mobiusCriticalHardySingularGraphEmbedding,
      mobiusCriticalHardyZeroAdjoinedNodes, Fin.sum_univ_succ,
      mobiusCriticalUniversalHardyFisherGram,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusCriticalUniversalHardyKernel,
      mobiusCriticalUniversalFisherScore,
      mobiusCriticalUniversalHardyMassProfile]
    ring
  · simp [Matrix.mul_apply, mobiusCriticalHardySingularGraphEmbedding,
      mobiusCriticalHardyZeroAdjoinedNodes, Fin.sum_univ_succ,
      mobiusCriticalUniversalHardyFisherGram,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusCriticalUniversalHardyKernel,
      mobiusCriticalUniversalFisherScore,
      mobiusCriticalUniversalHardyMassProfile,
      Complex.normSq_eq_conj_mul_self]
    ring

/-- Every finite inward packet is positive at the exact singular graph
budget.  This is unconditional and uses the original arithmetic-limit Gram. -/
theorem mobiusCriticalMassPerturbed_exactGraphBudget_posSemidef
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) (d : ℂ) :
    (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
      u d (4 + Complex.normSq d)).PosSemidef := by
  rw [← mobiusCriticalMassPerturbed_exactGraphBudget_congruence]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  apply mobiusCriticalUniversalHardyFisherGram_posSemidef
  intro i
  refine Fin.cases ?_ (fun j => hu j) i
  simp [mobiusCriticalHardyZeroAdjoinedNodes]

/-- Changing the graph budget contributes only the squared modulus of the
divisor coordinate to an arbitrary finite quadratic form. -/
theorem mobiusCriticalMassPerturbed_budget_quadratic_eq
    {n : ℕ} (u : Fin n → ℂ) (d : ℂ) (budget : ℝ)
    (c : Fin n ⊕ Unit → ℂ) :
    dotProduct (star c)
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
            u d budget) c) =
      dotProduct (star c)
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram u d) c) +
        ((budget : ℂ) - 4) * star (c (Sum.inr ())) * c (Sum.inr ()) := by
  rw [mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
    Matrix.add_mulVec, dotProduct_add]
  simp [Matrix.single_mulVec_eq, dotProduct, Fintype.sum_sum_type]
  ring

/-- **Global uncompleted wall law.**  Deleting the singular graph leg leaves
a uniformly lower-semibounded form.  Its only negative allowance is exactly
the graph debt `|d|²` times divisor-coordinate mass. -/
theorem mobiusCriticalMassPerturbed_fixedFour_quadratic_lower
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re)
    (d : ℂ) (c : Fin n ⊕ Unit → ℂ) :
    -Complex.normSq d * Complex.normSq (c (Sum.inr ())) ≤
      (dotProduct (star c)
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram u d) c)).re := by
  have hnonneg :=
    (mobiusCriticalMassPerturbed_exactGraphBudget_posSemidef u hu d)
      |>.dotProduct_mulVec_nonneg c
  rw [mobiusCriticalMassPerturbed_budget_quadratic_eq
    u d (4 + Complex.normSq d) c] at hnonneg
  rw [RCLike.le_iff_re_im] at hnonneg
  have hreal := hnonneg.1
  have hmass :
      ((((4 + Complex.normSq d : ℝ) : ℂ) - 4) *
        star (c (Sum.inr ())) * c (Sum.inr ())).re =
        Complex.normSq d * Complex.normSq (c (Sum.inr ())) := by
    simp [Complex.normSq_apply]
    ring
  change 0 ≤
    (dotProduct (star c)
      (Matrix.mulVec
        (mobiusCriticalUniversalHardyFisherMassPerturbedGram u d) c)).re +
      ((((4 + Complex.normSq d : ℝ) : ℂ) - 4) *
        star (c (Sum.inr ())) * c (Sum.inr ())).re at hreal
  rw [hmass] at hreal
  linarith

/-- A nonnegative scalar on the divisor coordinate is a positive matrix. -/
theorem mobiusCriticalBottomSingle_posSemidef
    {n : ℕ} {delta : ℝ} (hdelta : 0 ≤ delta) :
    (Matrix.single (Sum.inr ()) (Sum.inr ()) (delta : ℂ) :
      Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ).PosSemidef := by
  have hdiag :
      (Matrix.diagonal (fun i : Fin n ⊕ Unit =>
        if i = Sum.inr () then (delta : ℂ) else 0)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ if i = Sum.inr () then (delta : ℂ) else 0
    split_ifs
    · rw [RCLike.le_iff_re_im]
      simp [hdelta]
    · exact le_rfl
  convert hdiag using 1
  ext i j
  by_cases hi : i = Sum.inr () <;>
    by_cases hj : j = Sum.inr () <;>
      simp_all [Matrix.diagonal, Matrix.single] <;> aesop

/-- Every budget above the graph threshold remains positive. -/
theorem mobiusCriticalMassPerturbedWithBudget_posSemidef
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re)
    (d : ℂ) {budget : ℝ}
    (hbudget : 4 + Complex.normSq d ≤ budget) :
    (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
      u d budget).PosSemidef := by
  have hdelta : 0 ≤ budget - (4 + Complex.normSq d) :=
    sub_nonneg.mpr hbudget
  have hsum :=
    (mobiusCriticalMassPerturbed_exactGraphBudget_posSemidef u hu d).add
      (mobiusCriticalBottomSingle_posSemidef (n := n) hdelta)
  convert hsum using 1
  ext i j
  simp [mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
    Matrix.single]
  split_ifs <;> simp_all
  all_goals ring

/-- **Exact global budget classification.**  Positivity on all finite inward
packets holds exactly when the budget pays the four-unit Fisher energy and
the singular graph debt. -/
theorem all_mobiusCriticalMassPerturbedWithBudget_posSemidef_iff
    (d : ℂ) (budget : ℝ) :
    (∀ {n : ℕ} (u : Fin n → ℂ),
      (∀ i, 0 ≤ (u i).re) →
      (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
        u d budget).PosSemidef) ↔
      4 + Complex.normSq d ≤ budget := by
  constructor
  · intro hpos
    apply four_add_normSq_le_of_all_twoNode_massPerturbedWithBudget_posSemidef
    intro t ht
    apply hpos
    intro i
    fin_cases i <;>
      simp [mobiusCriticalHardySaturationNodes, ht.le]
  · intro hbudget n u hu
    exact mobiusCriticalMassPerturbedWithBudget_posSemidef
      u hu d hbudget

/-- Actual critical escaped coefficient of the coupled floor--Möbius/Gamma
error after clock normalization. -/
def mobiusGammaXiCoupledErrorCriticalCoefficient : ℂ :=
  continuedXiAntiCausalWardResponse (1 / 2 : ℂ)

/-- Squared singular graph norm required by the actual coupled error. -/
def mobiusGammaXiCoupledErrorSingularGraphDebt : ℝ :=
  Complex.normSq mobiusGammaXiCoupledErrorCriticalCoefficient

/-- Actual coupled-error wall at an arbitrary bottom budget. -/
def mobiusGammaXiCoupledErrorWallWithBudget
    {n : ℕ} (u : Fin n → ℂ) (budget : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
    u mobiusGammaXiCoupledErrorCriticalCoefficient budget

/-- Actual graph-completed G-CE wall. -/
def mobiusGammaXiCoupledErrorSingularGraphWall
    {n : ℕ} (u : Fin n → ℂ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  mobiusGammaXiCoupledErrorWallWithBudget
    u (4 + mobiusGammaXiCoupledErrorSingularGraphDebt)

/-- Actual uncompleted wall, before paying the singular graph debt. -/
def mobiusGammaXiCoupledErrorUncompletedWall
    {n : ℕ} (u : Fin n → ℂ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  mobiusCriticalUniversalHardyFisherMassPerturbedGram
    u mobiusGammaXiCoupledErrorCriticalCoefficient

/-- **G-CE singular wall positivity.**  Every actual finite coupled-error
packet is positive in the canonical singular graph norm. -/
theorem mobiusGammaXiCoupledErrorSingularGraphWall_posSemidef
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    (mobiusGammaXiCoupledErrorSingularGraphWall u).PosSemidef := by
  exact mobiusCriticalMassPerturbed_exactGraphBudget_posSemidef
    u hu mobiusGammaXiCoupledErrorCriticalCoefficient

/-- **Actual global lower wall.**  The coupled-error wall remains globally
lower-semibounded before completion; the exact debt is concentrated on the
divisor coordinate. -/
theorem mobiusGammaXiCoupledErrorUncompletedWall_quadratic_lower
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re)
    (c : Fin n ⊕ Unit → ℂ) :
    -mobiusGammaXiCoupledErrorSingularGraphDebt *
        Complex.normSq (c (Sum.inr ())) ≤
      (dotProduct (star c)
        (Matrix.mulVec
          (mobiusGammaXiCoupledErrorUncompletedWall u) c)).re := by
  exact mobiusCriticalMassPerturbed_fixedFour_quadratic_lower
    u hu mobiusGammaXiCoupledErrorCriticalCoefficient c

/-- Exact minimal-budget classification for the actual coupled-error wall. -/
theorem all_mobiusGammaXiCoupledErrorWallWithBudget_posSemidef_iff
    (budget : ℝ) :
    (∀ {n : ℕ} (u : Fin n → ℂ),
      (∀ i, 0 ≤ (u i).re) →
      (mobiusGammaXiCoupledErrorWallWithBudget u budget).PosSemidef) ↔
      4 + mobiusGammaXiCoupledErrorSingularGraphDebt ≤ budget := by
  exact all_mobiusCriticalMassPerturbedWithBudget_posSemidef_iff
    mobiusGammaXiCoupledErrorCriticalCoefficient budget

/-- The global lower wall is sharp on the canonical two-node packets. -/
theorem tendsto_mobiusGammaXiCoupledErrorUncompletedWall_saturation :
    Tendsto (fun t : ℝ =>
      dotProduct
        (star (mobiusCriticalHardyMassSaturationCoefficients t
          mobiusGammaXiCoupledErrorCriticalCoefficient))
        (Matrix.mulVec
          (mobiusGammaXiCoupledErrorUncompletedWall
            (mobiusCriticalHardySaturationNodes t))
          (mobiusCriticalHardyMassSaturationCoefficients t
            mobiusGammaXiCoupledErrorCriticalCoefficient)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (-((mobiusGammaXiCoupledErrorSingularGraphDebt : ℝ) : ℂ))) := by
  exact tendsto_mobiusCriticalHardyMassSaturation_quadratic
    mobiusGammaXiCoupledErrorCriticalCoefficient

/-- Vanishing singular graph debt is exactly RH.  The completed wall itself
is unconditional; RH is the statement that its extra graph leg disappears. -/
theorem mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh :
    mobiusGammaXiCoupledErrorSingularGraphDebt = 0 ↔
      RiemannHypothesis := by
  rw [mobiusGammaXiCoupledErrorSingularGraphDebt,
    Complex.normSq_eq_zero,
    mobiusGammaXiCoupledErrorCriticalCoefficient,
    continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh]

end RHTower
