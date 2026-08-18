import GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorSingularGraphGlobalWall

/-!
# G-CE exact-debt cancellation and source-erasure dichotomy

The singular coupled-error wall carries the scalar boundary charge

`d = continuedXiAntiCausalWardResponse (1 / 2)`

and exact graph debt `|d|²`.  This file classifies every bounded complex-linear controller on that
scalar physical channel.

There is one unconditional visible cancellation: the opposite controller `T = -I`.  It sends
`d + T d` to zero and restores the ordinary four-unit Hardy--Fisher wall.  The cancellation is not
free or source-selective.  The controller has energy `|d|²`, and a balanced sum/difference mixer
transfers the complete two-port energy `2|d|²` to the hidden antisymmetric port.

More sharply, one-dimensional complex linearity proves the exhaustive dichotomy

`d + T d = 0  ↔  RH ∨ T = -I`.

Thus every nonerasing scalar linear cancellation is already RH.  The only unconditional branch is
universal erasure of the complete scalar Ward channel.  This rules out scalar physical
cancellation as an independent escape from the G-CE source problem; a successful producer must
act before scalarization or prove that the complementary port vanishes.
-/

open Complex Matrix
open scoped ComplexOrder

noncomputable section

namespace RHTower

/-- A scalar boundary controller erases the complete source channel when its visible coherent sum
with every possible input is zero. -/
def mobiusGammaXiDebtControllerErasesSource (T : ℂ →L[ℂ] ℂ) : Prop :=
  ∀ z : ℂ, z + T z = 0

/-- Unique bounded complex-linear controller which cancels every scalar boundary charge. -/
def mobiusGammaXiOppositeDebtController : ℂ →L[ℂ] ℂ :=
  -(ContinuousLinearMap.id ℂ ℂ)

/-- In one complex dimension, complete coherent erasure is exactly the opposite controller. -/
theorem mobiusGammaXiDebtControllerErasesSource_iff_eq_opposite
    (T : ℂ →L[ℂ] ℂ) :
    mobiusGammaXiDebtControllerErasesSource T ↔
      T = mobiusGammaXiOppositeDebtController := by
  constructor
  · intro hT
    apply ContinuousLinearMap.ext
    intro z
    have h := hT z
    simp only [mobiusGammaXiOppositeDebtController, _root_.neg_apply,
      ContinuousLinearMap.id_apply]
    linear_combination h
  · rintro rfl
    intro z
    simp [mobiusGammaXiOppositeDebtController]

/-- The opposite controller erases the scalar channel unconditionally. -/
theorem mobiusGammaXiOppositeDebtController_erasesSource :
    mobiusGammaXiDebtControllerErasesSource
      mobiusGammaXiOppositeDebtController := by
  exact
    (mobiusGammaXiDebtControllerErasesSource_iff_eq_opposite _).2 rfl

/-- Actual G-CE scalar charge left in the visible port after applying a boundary controller. -/
def mobiusGammaXiControlledCriticalResidual (T : ℂ →L[ℂ] ℂ) : ℂ :=
  mobiusGammaXiCoupledErrorCriticalCoefficient +
    T mobiusGammaXiCoupledErrorCriticalCoefficient

/-- Squared singular-graph debt retained by the controlled visible port. -/
def mobiusGammaXiControlledSingularGraphDebt (T : ℂ →L[ℂ] ℂ) : ℝ :=
  Complex.normSq (mobiusGammaXiControlledCriticalResidual T)

/-- **Exact scalar-controller dichotomy.**  Cancelling the actual G-CE charge either proves RH or
erases every possible scalar source value. -/
theorem mobiusGammaXiDebtController_cancellation_iff_rh_or_erasure
    (T : ℂ →L[ℂ] ℂ) :
    mobiusGammaXiControlledCriticalResidual T = 0 ↔
      RiemannHypothesis ∨ mobiusGammaXiDebtControllerErasesSource T := by
  let d := mobiusGammaXiCoupledErrorCriticalCoefficient
  constructor
  · intro hcancel
    by_cases hd : d = 0
    · left
      exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mp
        (by simpa [d, mobiusGammaXiCoupledErrorCriticalCoefficient] using hd)
    · right
      intro z
      have hTd : T d = -d := by
        dsimp only [mobiusGammaXiControlledCriticalResidual, d] at hcancel
        linear_combination hcancel
      have hzd : ((z / d) : ℂ) • d = z := by
        simp [smul_eq_mul, hd]
      rw [← hzd, map_smul, hTd]
      simp
  · rintro (hRH | herase)
    · have hd : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 := by
        exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mpr hRH
      simp [mobiusGammaXiControlledCriticalResidual, hd]
    · exact herase mobiusGammaXiCoupledErrorCriticalCoefficient

/-- Cancellation is exactly RH or the unique universal opposite controller. -/
theorem mobiusGammaXiDebtController_cancellation_iff_rh_or_eq_opposite
    (T : ℂ →L[ℂ] ℂ) :
    mobiusGammaXiControlledCriticalResidual T = 0 ↔
      RiemannHypothesis ∨ T = mobiusGammaXiOppositeDebtController := by
  rw [mobiusGammaXiDebtController_cancellation_iff_rh_or_erasure,
    mobiusGammaXiDebtControllerErasesSource_iff_eq_opposite]

/-- Exact controlled-debt form of the same dichotomy. -/
theorem mobiusGammaXiControlledSingularGraphDebt_eq_zero_iff
    (T : ℂ →L[ℂ] ℂ) :
    mobiusGammaXiControlledSingularGraphDebt T = 0 ↔
      RiemannHypothesis ∨ T = mobiusGammaXiOppositeDebtController := by
  rw [mobiusGammaXiControlledSingularGraphDebt, Complex.normSq_eq_zero,
    mobiusGammaXiDebtController_cancellation_iff_rh_or_eq_opposite]

/-- Removing the erasing controller branch leaves precisely RH. -/
theorem mobiusGammaXiDebtController_nonerasingCancellation_iff
    (T : ℂ →L[ℂ] ℂ) :
    (T ≠ mobiusGammaXiOppositeDebtController ∧
        mobiusGammaXiControlledCriticalResidual T = 0) ↔
      (T ≠ mobiusGammaXiOppositeDebtController ∧ RiemannHypothesis) := by
  rw [mobiusGammaXiDebtController_cancellation_iff_rh_or_eq_opposite]
  tauto

/-- Every erasing controller pays exactly one copy of the original singular graph debt. -/
theorem mobiusGammaXiDebtController_energy_eq_debt_of_erasure
    (T : ℂ →L[ℂ] ℂ) (hT : mobiusGammaXiDebtControllerErasesSource T) :
    Complex.normSq (T mobiusGammaXiCoupledErrorCriticalCoefficient) =
      mobiusGammaXiCoupledErrorSingularGraphDebt := by
  have h := hT mobiusGammaXiCoupledErrorCriticalCoefficient
  have hTd : T mobiusGammaXiCoupledErrorCriticalCoefficient =
      -mobiusGammaXiCoupledErrorCriticalCoefficient := by
    linear_combination h
  rw [hTd, Complex.normSq_neg]
  rfl

/-- Parallelogram energy conservation for visible and hidden controller ports. -/
theorem mobiusGammaXiDebtController_balancedPort_energy_conservation
    (T : ℂ →L[ℂ] ℂ) :
    Complex.normSq
        (mobiusGammaXiCoupledErrorCriticalCoefficient +
          T mobiusGammaXiCoupledErrorCriticalCoefficient) +
      Complex.normSq
        (mobiusGammaXiCoupledErrorCriticalCoefficient -
          T mobiusGammaXiCoupledErrorCriticalCoefficient) =
      2 * (mobiusGammaXiCoupledErrorSingularGraphDebt +
        Complex.normSq (T mobiusGammaXiCoupledErrorCriticalCoefficient)) := by
  rw [Complex.normSq_add, Complex.normSq_sub]
  simp only [mobiusGammaXiCoupledErrorSingularGraphDebt]
  ring

/-- On the erasing branch, normalized hidden-port energy is exactly twice the original debt. -/
theorem mobiusGammaXiDebtController_hiddenPort_energy_eq_two_debt_of_erasure
    (T : ℂ →L[ℂ] ℂ) (hT : mobiusGammaXiDebtControllerErasesSource T) :
    (1 / 2 : ℝ) * Complex.normSq
        (mobiusGammaXiCoupledErrorCriticalCoefficient -
          T mobiusGammaXiCoupledErrorCriticalCoefficient) =
      2 * mobiusGammaXiCoupledErrorSingularGraphDebt := by
  have hcancel : mobiusGammaXiControlledCriticalResidual T = 0 :=
    (mobiusGammaXiDebtController_cancellation_iff_rh_or_erasure T).2
      (Or.inr hT)
  have henergy :=
    mobiusGammaXiDebtController_balancedPort_energy_conservation T
  have hcontroller :=
    mobiusGammaXiDebtController_energy_eq_debt_of_erasure T hT
  dsimp only [mobiusGammaXiControlledCriticalResidual] at hcancel
  rw [hcancel, Complex.normSq_zero, hcontroller] at henergy
  linarith

/-- The actual opposite controller cancels the visible G-CE charge. -/
theorem mobiusGammaXiOppositeDebtController_residual_eq_zero :
    mobiusGammaXiControlledCriticalResidual
      mobiusGammaXiOppositeDebtController = 0 := by
  exact
    (mobiusGammaXiDebtController_cancellation_iff_rh_or_erasure _).2
      (Or.inr mobiusGammaXiOppositeDebtController_erasesSource)

/-- Its controller port has exactly the original debt energy. -/
theorem mobiusGammaXiOppositeDebtController_energy_eq_debt :
    Complex.normSq
        (mobiusGammaXiOppositeDebtController
          mobiusGammaXiCoupledErrorCriticalCoefficient) =
      mobiusGammaXiCoupledErrorSingularGraphDebt := by
  exact mobiusGammaXiDebtController_energy_eq_debt_of_erasure
    _ mobiusGammaXiOppositeDebtController_erasesSource

/-- Its hidden antisymmetric port retains the complete two-port debt energy. -/
theorem mobiusGammaXiOppositeDebtController_hiddenPort_energy_eq_two_debt :
    (1 / 2 : ℝ) * Complex.normSq
        (mobiusGammaXiCoupledErrorCriticalCoefficient -
          mobiusGammaXiOppositeDebtController
            mobiusGammaXiCoupledErrorCriticalCoefficient) =
      2 * mobiusGammaXiCoupledErrorSingularGraphDebt := by
  exact mobiusGammaXiDebtController_hiddenPort_energy_eq_two_debt_of_erasure
    _ mobiusGammaXiOppositeDebtController_erasesSource

/-- Controlled G-CE wall at its exact singular-graph completion budget. -/
def mobiusGammaXiControlledCoupledErrorWall
    (T : ℂ →L[ℂ] ℂ) {n : ℕ} (u : Fin n → ℂ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
    u (mobiusGammaXiControlledCriticalResidual T)
      (4 + mobiusGammaXiControlledSingularGraphDebt T)

/-- Controlled wall at an arbitrary proposed bottom budget. -/
def mobiusGammaXiControlledCoupledErrorWallWithBudget
    (T : ℂ →L[ℂ] ℂ) {n : ℕ} (u : Fin n → ℂ) (budget : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
    u (mobiusGammaXiControlledCriticalResidual T) budget

/-- Exact minimum global budget after an arbitrary scalar boundary controller. -/
theorem all_mobiusGammaXiControlledCoupledErrorWallWithBudget_posSemidef_iff
    (T : ℂ →L[ℂ] ℂ) (budget : ℝ) :
    (∀ {n : ℕ} (u : Fin n → ℂ),
      (∀ i, 0 ≤ (u i).re) →
      (mobiusGammaXiControlledCoupledErrorWallWithBudget
        T u budget).PosSemidef) ↔
      4 + mobiusGammaXiControlledSingularGraphDebt T ≤ budget := by
  exact all_mobiusCriticalMassPerturbedWithBudget_posSemidef_iff
    (mobiusGammaXiControlledCriticalResidual T) budget

/-- Every controlled finite packet is positive at its exact completed budget. -/
theorem mobiusGammaXiControlledCoupledErrorWall_posSemidef
    (T : ℂ →L[ℂ] ℂ) {n : ℕ} (u : Fin n → ℂ)
    (hu : ∀ i, 0 ≤ (u i).re) :
    (mobiusGammaXiControlledCoupledErrorWall T u).PosSemidef := by
  exact mobiusCriticalMassPerturbed_exactGraphBudget_posSemidef
    u hu (mobiusGammaXiControlledCriticalResidual T)

/-- Visible cancellation restores the ordinary four-unit Hardy--Fisher Gram exactly. -/
theorem mobiusGammaXiControlledCoupledErrorWall_eq_fourUnit_of_cancellation
    (T : ℂ →L[ℂ] ℂ)
    (hcancel : mobiusGammaXiControlledCriticalResidual T = 0)
    {n : ℕ} (u : Fin n → ℂ) :
    mobiusGammaXiControlledCoupledErrorWall T u =
      mobiusCriticalUniversalHardyFisherGram u := by
  ext i j
  rcases i with i | z <;> rcases j with j | w <;>
    simp [mobiusGammaXiControlledCoupledErrorWall,
      mobiusGammaXiControlledSingularGraphDebt, hcancel,
      mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
      mobiusCriticalUniversalHardyFisherMassPerturbedGram,
      mobiusCriticalUniversalHardyFisherGram]

/-- The actual opposite controller therefore restores the four-unit wall unconditionally. -/
theorem mobiusGammaXiOppositeDebtController_controlledWall_eq_fourUnit
    {n : ℕ} (u : Fin n → ℂ) :
    mobiusGammaXiControlledCoupledErrorWall
        mobiusGammaXiOppositeDebtController u =
      mobiusCriticalUniversalHardyFisherGram u := by
  exact
    mobiusGammaXiControlledCoupledErrorWall_eq_fourUnit_of_cancellation
      _ mobiusGammaXiOppositeDebtController_residual_eq_zero u

/-- The physically cancelled visible wall is positive on every actual inward finite packet. -/
theorem mobiusGammaXiOppositeDebtController_controlledWall_posSemidef
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    (mobiusGammaXiControlledCoupledErrorWall
      mobiusGammaXiOppositeDebtController u).PosSemidef := by
  exact mobiusGammaXiControlledCoupledErrorWall_posSemidef _ u hu

/-- **Closed physical-cancellation certificate.**  Visible debt is zero, controller pays one debt,
and hidden antisymmetric port carries total two-port debt.  This is cancellation by transfer, not
annihilation. -/
theorem mobiusGammaXiOppositeDebtController_exactPhysicalCancellation :
    mobiusGammaXiControlledCriticalResidual
        mobiusGammaXiOppositeDebtController = 0 ∧
      mobiusGammaXiControlledSingularGraphDebt
          mobiusGammaXiOppositeDebtController = 0 ∧
      Complex.normSq
          (mobiusGammaXiOppositeDebtController
            mobiusGammaXiCoupledErrorCriticalCoefficient) =
        mobiusGammaXiCoupledErrorSingularGraphDebt ∧
      (1 / 2 : ℝ) * Complex.normSq
          (mobiusGammaXiCoupledErrorCriticalCoefficient -
            mobiusGammaXiOppositeDebtController
              mobiusGammaXiCoupledErrorCriticalCoefficient) =
        2 * mobiusGammaXiCoupledErrorSingularGraphDebt := by
  refine ⟨mobiusGammaXiOppositeDebtController_residual_eq_zero, ?_,
    mobiusGammaXiOppositeDebtController_energy_eq_debt,
    mobiusGammaXiOppositeDebtController_hiddenPort_energy_eq_two_debt⟩
  rw [mobiusGammaXiControlledSingularGraphDebt,
    mobiusGammaXiOppositeDebtController_residual_eq_zero,
    Complex.normSq_zero]

end RHTower
