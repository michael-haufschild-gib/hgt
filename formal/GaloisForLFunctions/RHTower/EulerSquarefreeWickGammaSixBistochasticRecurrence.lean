import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixPositiveProjectorBridge
import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw

/-!
# EWQ–Gamma-six bistochastic recurrence

Prime `5` contains both EWQ orientations at consecutive prime-power depths.  Their pure projectors
are complementary and Pauli-Z swaps them, giving a literal period-two arithmetic clock.

The positive and negative Gamma-six half-density orientations canonically average to a two-Kraus
channel.  Lean proves this completion is completely positive and trace-preserving by its Kraus
normalization, as well as unital and positivity-preserving.  Its only action on the replica density
is dephasing by `sech(a)`.

Thus one arithmetic depth shift is exact iff `a = 0`, and the period-two source clock returns
exactly after two completed steps iff `a = 0`.  On every physical Xi fibre this exact quantum
recurrence is equivalent to RH.  The remaining producer is sharply identified: coefficient-faithful
completion must intertwine the literal depth-periodic arithmetic clock with this canonical positive
channel.
-/

open Complex Matrix
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder MatrixOrder BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

def eulerWickPrimeFive : Nat.Primes := ⟨5, by norm_num⟩

def eulerWickPrimeFiveOddDepth : PrimePowerClockIndex :=
  (eulerWickPrimeFive, 0)

def eulerWickPrimeFiveEvenDepth : PrimePowerClockIndex :=
  (eulerWickPrimeFive, 1)

theorem quadraticResidueProductPrimeCoefficient_five :
    quadraticResidueProductPrimeCoefficient eulerWickPrimeFive = -1 := by
  have hp : IsUnit (((eulerWickPrimeFive : Nat.Primes).1 : ℕ) : ZMod 12) := by
    rw [ZMod.isUnit_iff_coprime]
    norm_num [eulerWickPrimeFive]
  rw [quadraticResidueProductPrimeCoefficient_eq_quadraticCharacterTwelve_of_isUnit
    eulerWickPrimeFive hp]
  change quadraticCharacterTwelve (5 : ZMod 12) = -1
  rw [quadraticCharacterTwelve, _root_.RHTower.crtProductCharacter_apply]
  rw [show ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4) (5 : ZMod 12) =
      (((5 : ℤ) : ZMod 3), ((5 : ℤ) : ZMod 4)) by
    exact map_intCast _ 5]
  have hthree : quadraticCharacterThree (-1 : ZMod 3) = -1 := by
    simpa [quadraticCharacterThreeUnit] using quadraticCharacterThreeUnit_neg_one
  change quadraticCharacterThree (5 : ZMod 3) *
      _root_.RHTower.quadraticCharacterFour (5 : ZMod 4) = -1
  rw [show (5 : ZMod 3) = -1 by decide,
    show (5 : ZMod 4) = 1 by decide, hthree]
  simp

theorem eulerWickQuadraticDepthCharacter_five_odd :
    eulerWickQuadraticDepthCharacter eulerWickPrimeFiveOddDepth = -1 := by
  simp [eulerWickQuadraticDepthCharacter, eulerWickPrimeFiveOddDepth,
    quadraticResidueProductPrimeCoefficient_five]

theorem eulerWickQuadraticDepthCharacter_five_even :
    eulerWickQuadraticDepthCharacter eulerWickPrimeFiveEvenDepth = 1 := by
  simp [eulerWickQuadraticDepthCharacter, eulerWickPrimeFiveEvenDepth,
    quadraticResidueProductPrimeCoefficient_five]

def eulerWickReplicaPauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

theorem eulerWickReplicaPauliZ_conjTranspose :
    eulerWickReplicaPauliZᴴ = eulerWickReplicaPauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaPauliZ, Matrix.conjTranspose_apply]

theorem eulerWickReplicaPauliZ_sq :
    eulerWickReplicaPauliZ * eulerWickReplicaPauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaPauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem eulerWickPrimeFive_projector_resolution :
    eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth +
        eulerWickReplicaPureProjector eulerWickPrimeFiveEvenDepth = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_five_odd,
      eulerWickQuadraticDepthCharacter_five_even] <;>
    norm_num

theorem eulerWickPrimeFive_depthShift :
    eulerWickReplicaPauliZ *
          eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth *
        eulerWickReplicaPauliZ =
      eulerWickReplicaPureProjector eulerWickPrimeFiveEvenDepth := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickReplicaPauliZ, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two,
      eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_five_odd,
      eulerWickQuadraticDepthCharacter_five_even]

def eulerWickGammaSixDephasingFactor (a : ℝ) : ℝ :=
  1 / Real.cosh a

theorem eulerWickGammaSixDephasingFactor_pos (a : ℝ) :
    0 < eulerWickGammaSixDephasingFactor a := by
  exact one_div_pos.mpr (Real.cosh_pos a)

theorem eulerWickGammaSixDephasingFactor_le_one (a : ℝ) :
    eulerWickGammaSixDephasingFactor a ≤ 1 := by
  exact (div_le_one (Real.cosh_pos a)).mpr (Real.one_le_cosh a)

theorem eulerWickGammaSixDephasingFactor_eq_one_iff (a : ℝ) :
    eulerWickGammaSixDephasingFactor a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hcosh : Real.cosh a = 1 := by
      dsimp only [eulerWickGammaSixDephasingFactor] at h
      field_simp [(Real.cosh_pos a).ne'] at h
      linarith
    by_contra ha
    have hlt := Real.one_lt_cosh.mpr ha
    linarith
  · rintro rfl
    simp [eulerWickGammaSixDephasingFactor]

def eulerWickGammaSixDephasingPlusWeight (a : ℝ) : ℝ :=
  (1 + eulerWickGammaSixDephasingFactor a) / 2

def eulerWickGammaSixDephasingMinusWeight (a : ℝ) : ℝ :=
  (1 - eulerWickGammaSixDephasingFactor a) / 2

theorem eulerWickGammaSixDephasingPlusWeight_nonneg (a : ℝ) :
    0 ≤ eulerWickGammaSixDephasingPlusWeight a := by
  dsimp only [eulerWickGammaSixDephasingPlusWeight]
  linarith [eulerWickGammaSixDephasingFactor_pos a]

theorem eulerWickGammaSixDephasingMinusWeight_nonneg (a : ℝ) :
    0 ≤ eulerWickGammaSixDephasingMinusWeight a := by
  dsimp only [eulerWickGammaSixDephasingMinusWeight]
  linarith [eulerWickGammaSixDephasingFactor_le_one a]

theorem eulerWickGammaSixDephasingWeights_add (a : ℝ) :
    eulerWickGammaSixDephasingPlusWeight a +
      eulerWickGammaSixDephasingMinusWeight a = 1 := by
  simp [eulerWickGammaSixDephasingPlusWeight,
    eulerWickGammaSixDephasingMinusWeight]
  ring

/-- Two Kraus operators: identity and the arithmetic depth-flip phase. -/
def eulerWickGammaSixBalancedKrausOperator (a : ℝ) (b : Fin 2) :
    _root_.RHTower.QuantumMatrix 2 :=
  if b = 0 then
    ((Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) : ℝ) : ℂ) • 1
  else
    ((Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) : ℝ) : ℂ) •
      eulerWickReplicaPauliZ

/-- Canonical completely positive trace-preserving completion of the two EWQ depth orientations. -/
def eulerWickGammaSixBalancedKrausChannel (a : ℝ) :
    _root_.RHTower.FiniteKrausChannel 2 2 where
  operator := eulerWickGammaSixBalancedKrausOperator a
  completeness := by
    have hp := Real.sq_sqrt (eulerWickGammaSixDephasingPlusWeight_nonneg a)
    have hm := Real.sq_sqrt (eulerWickGammaSixDephasingMinusWeight_nonneg a)
    have hpC :
        ((Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) : ℝ) : ℂ) *
            ((Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) : ℝ) : ℂ) =
          (eulerWickGammaSixDephasingPlusWeight a : ℂ) := by
      exact_mod_cast (show Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) *
        Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) =
          eulerWickGammaSixDephasingPlusWeight a by simpa [pow_two] using hp)
    have hmC :
        ((Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) : ℝ) : ℂ) *
            ((Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) : ℝ) : ℂ) =
          (eulerWickGammaSixDephasingMinusWeight a : ℂ) := by
      exact_mod_cast (show Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) *
        Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) =
          eulerWickGammaSixDephasingMinusWeight a by simpa [pow_two] using hm)
    have haddC :
        (eulerWickGammaSixDephasingPlusWeight a : ℂ) +
            (eulerWickGammaSixDephasingMinusWeight a : ℂ) = 1 := by
      exact_mod_cast eulerWickGammaSixDephasingWeights_add a
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickGammaSixBalancedKrausOperator,
        eulerWickReplicaPauliZ, Matrix.mul_apply,
        Fin.sum_univ_two, hpC, hmC] <;>
      exact haddC

def eulerWickGammaSixBalancedDephasing (a : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  eulerWickGammaSixDephasingPlusWeight a • M +
    eulerWickGammaSixDephasingMinusWeight a •
      (eulerWickReplicaPauliZ * M * eulerWickReplicaPauliZ)

theorem eulerWickGammaSixBalancedKrausChannel_evolveMatrix_eq (a : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (eulerWickGammaSixBalancedKrausChannel a).evolveMatrix M =
      eulerWickGammaSixBalancedDephasing a M := by
  have hp := Real.sq_sqrt (eulerWickGammaSixDephasingPlusWeight_nonneg a)
  have hm := Real.sq_sqrt (eulerWickGammaSixDephasingMinusWeight_nonneg a)
  have hpC :
      ((Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) : ℝ) : ℂ) *
          ((Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) : ℝ) : ℂ) =
        (eulerWickGammaSixDephasingPlusWeight a : ℂ) := by
    exact_mod_cast (show Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) *
      Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) =
        eulerWickGammaSixDephasingPlusWeight a by simpa [pow_two] using hp)
  have hmC :
      ((Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) : ℝ) : ℂ) *
          ((Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) : ℝ) : ℂ) =
        (eulerWickGammaSixDephasingMinusWeight a : ℂ) := by
    exact_mod_cast (show Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) *
      Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) =
        eulerWickGammaSixDephasingMinusWeight a by simpa [pow_two] using hm)
  have hpPowC :
      ((Real.sqrt (eulerWickGammaSixDephasingPlusWeight a) : ℝ) : ℂ) ^ 2 =
        (eulerWickGammaSixDephasingPlusWeight a : ℂ) := by
    simpa [pow_two] using hpC
  have hmPowC :
      ((Real.sqrt (eulerWickGammaSixDephasingMinusWeight a) : ℝ) : ℂ) ^ 2 =
        (eulerWickGammaSixDephasingMinusWeight a : ℂ) := by
    simpa [pow_two] using hmC
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [_root_.RHTower.FiniteKrausChannel.evolveMatrix,
      eulerWickGammaSixBalancedKrausChannel,
      eulerWickGammaSixBalancedKrausOperator,
      eulerWickGammaSixBalancedDephasing,
      eulerWickReplicaPauliZ, Matrix.mul_apply, Matrix.vecMul,
      Matrix.conjTranspose_apply, dotProduct, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals rw [hpPowC, hmPowC]
  all_goals ring

theorem eulerWickGammaSixBalancedDephasing_apply (a : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    eulerWickGammaSixBalancedDephasing a M i j =
      if i = j then M i j
      else (eulerWickGammaSixDephasingFactor a : ℂ) * M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickGammaSixBalancedDephasing, eulerWickReplicaPauliZ,
      eulerWickGammaSixDephasingPlusWeight,
      eulerWickGammaSixDephasingMinusWeight,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    ring

theorem eulerWickGammaSixBalancedDephasing_one (a : ℝ) :
    eulerWickGammaSixBalancedDephasing a (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickGammaSixBalancedDephasing_apply]

theorem eulerWickGammaSixBalancedDephasing_trace (a : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (eulerWickGammaSixBalancedDephasing a M) = Matrix.trace M := by
  simp [Matrix.trace, eulerWickGammaSixBalancedDephasing_apply]

theorem eulerWickGammaSixBalancedDephasing_posSemidef (a : ℝ)
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.PosSemidef) :
    (eulerWickGammaSixBalancedDephasing a M).PosSemidef := by
  have hwplus : 0 ≤ (1 + eulerWickGammaSixDephasingFactor a) / 2 := by
    linarith [eulerWickGammaSixDephasingFactor_pos a]
  have hwminus : 0 ≤ (1 - eulerWickGammaSixDephasingFactor a) / 2 := by
    linarith [eulerWickGammaSixDephasingFactor_le_one a]
  rw [eulerWickGammaSixBalancedDephasing]
  apply Matrix.PosSemidef.add
  · exact hM.smul hwplus
  · apply Matrix.PosSemidef.smul
    · simpa [eulerWickReplicaPauliZ_conjTranspose] using
        hM.mul_mul_conjTranspose_same eulerWickReplicaPauliZ
    · exact hwminus

def eulerWickGammaSixBalancedDepthStep (a : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  eulerWickGammaSixBalancedDephasing a
    (eulerWickReplicaPauliZ * M * eulerWickReplicaPauliZ)

theorem eulerWickGammaSixBalancedDepthStep_odd_eq (a : ℝ) :
    eulerWickGammaSixBalancedDepthStep a
        (eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth) =
      !![(1 / 2 : ℂ), (eulerWickGammaSixDephasingFactor a : ℂ) / 2;
         (eulerWickGammaSixDephasingFactor a : ℂ) / 2, (1 / 2 : ℂ)] := by
  rw [eulerWickGammaSixBalancedDepthStep, eulerWickPrimeFive_depthShift]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickGammaSixBalancedDephasing_apply,
      eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_five_even] <;>
    ring

theorem eulerWickGammaSixBalancedDepthStep_exact_iff (a : ℝ) :
    eulerWickGammaSixBalancedDepthStep a
        (eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth) =
      eulerWickReplicaPureProjector eulerWickPrimeFiveEvenDepth ↔
      a = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
    rw [eulerWickGammaSixBalancedDepthStep_odd_eq] at h01
    simp [eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_five_even] at h01
    apply (eulerWickGammaSixDephasingFactor_eq_one_iff a).1
    have hre := congrArg Complex.re h01
    norm_num at hre
    linarith
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickGammaSixBalancedDepthStep_odd_eq,
        eulerWickGammaSixDephasingFactor,
        eulerWickReplicaPureProjector_apply,
        eulerWickQuadraticDepthCharacter_five_even]

theorem eulerWickGammaSixBalancedDepthStep_two_odd_eq (a : ℝ) :
    eulerWickGammaSixBalancedDepthStep a
        (eulerWickGammaSixBalancedDepthStep a
          (eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth)) =
      !![(1 / 2 : ℂ), -(eulerWickGammaSixDephasingFactor a : ℂ) ^ 2 / 2;
         -(eulerWickGammaSixDephasingFactor a : ℂ) ^ 2 / 2, (1 / 2 : ℂ)] := by
  rw [eulerWickGammaSixBalancedDepthStep_odd_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickGammaSixBalancedDepthStep,
      eulerWickGammaSixBalancedDephasing_apply,
      eulerWickReplicaPauliZ] <;>
    ring

/-- The arithmetic depth clock returns after two steps.  Its canonical balanced quantum
completion has that exact return precisely at neutral Gamma-six grade. -/
theorem eulerWickGammaSixBalancedDepthStep_two_exactReturn_iff (a : ℝ) :
    eulerWickGammaSixBalancedDepthStep a
        (eulerWickGammaSixBalancedDepthStep a
          (eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth)) =
      eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth ↔
      a = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
    rw [eulerWickGammaSixBalancedDepthStep_two_odd_eq] at h01
    simp [eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_five_odd] at h01
    have hkSqC : (eulerWickGammaSixDephasingFactor a : ℂ) ^ 2 = 1 := by
      linear_combination -2 * h01
    have hkSq : eulerWickGammaSixDephasingFactor a ^ 2 = 1 := by
      exact_mod_cast hkSqC
    have hkpos := eulerWickGammaSixDephasingFactor_pos a
    have hk : eulerWickGammaSixDephasingFactor a = 1 := by nlinarith
    exact (eulerWickGammaSixDephasingFactor_eq_one_iff a).1 hk
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickGammaSixBalancedDepthStep_two_odd_eq,
        eulerWickGammaSixDephasingFactor,
        eulerWickReplicaPureProjector_apply,
        eulerWickQuadraticDepthCharacter_five_odd] <;>
      norm_num

def EulerWickGammaSixPhysicalBalancedDepthReturn : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    let a := Real.log (5 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1
    eulerWickGammaSixBalancedDepthStep a
        (eulerWickGammaSixBalancedDepthStep a
          (eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth)) =
      eulerWickReplicaPureProjector eulerWickPrimeFiveOddDepth

theorem eulerWickGammaSixPhysicalBalancedDepthReturn_iff_riemannHypothesis :
    EulerWickGammaSixPhysicalBalancedDepthReturn ↔ RiemannHypothesis := by
  constructor
  · intro hreturn
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hzero :=
      (eulerWickGammaSixBalancedDepthStep_two_exactReturn_iff
        (Real.log (5 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).1
        (hreturn q)
    have hlog : Real.log (5 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hrate : _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hlog
    have hline :=
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickGammaSixBalancedDepthStep_two_exactReturn_iff
      (Real.log (5 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).2
    rw [(_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1), mul_zero]

end

end GaloisForLFunctions.RHTower
