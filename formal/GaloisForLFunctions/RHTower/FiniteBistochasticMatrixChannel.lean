import GaloisForLFunctions.RHTower.DissipativeQuantumReturnInformationTransition
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped BigOperators ComplexOrder Matrix MatrixOrder InnerProductSpace

noncomputable section

namespace RHTower

/-- Blockwise amplification `id_k ⊗ Φ`. -/
def finiteMatrixAmplification {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (k : ℕ) :
    Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ where
  toFun X ia jb := Φ (fun a b => X (ia.1, a) (jb.1, b)) ia.2 jb.2
  map_add' X Y := by
    ext ia jb
    exact congrFun (congrFun (Φ.map_add _ _) ia.2) jb.2
  map_smul' c X := by
    ext ia jb
    exact congrFun (congrFun (Φ.map_smul c _) ia.2) jb.2

/-- Finite-dimensional unital, trace-preserving, completely positive matrix map. -/
structure FiniteBistochasticMatrixChannel (d : ℕ) where
  toLinearMap : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ
  map_one : toLinearMap 1 = 1
  trace_preserving : ∀ X, Matrix.trace (toLinearMap X) = Matrix.trace X
  completelyPositive : ∀ (k : ℕ) (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ),
    X.PosSemidef → (finiteMatrixAmplification toLinearMap k X).PosSemidef

namespace FiniteBistochasticMatrixChannel

variable {d : ℕ} (Φ : FiniteBistochasticMatrixChannel d)

instance : CoeFun (FiniteBistochasticMatrixChannel d)
    (fun _ => Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun Φ => Φ.toLinearMap⟩

@[simp] theorem map_add (X Y : Matrix (Fin d) (Fin d) ℂ) :
    Φ (X + Y) = Φ X + Φ Y := Φ.toLinearMap.map_add X Y

@[simp] theorem map_sub (X Y : Matrix (Fin d) (Fin d) ℂ) :
    Φ (X - Y) = Φ X - Φ Y := Φ.toLinearMap.map_sub X Y

@[simp] theorem map_smul (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    Φ (c • X) = c • Φ X := Φ.toLinearMap.map_smul c X

@[simp] theorem map_zero : Φ (0 : Matrix (Fin d) (Fin d) ℂ) = 0 :=
  Φ.toLinearMap.map_zero

/-- Complete positivity implies ordinary positivity. -/
theorem map_posSemidef {X : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosSemidef) : (Φ X).PosSemidef := by
  let X₁ : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) ℂ :=
    X.submatrix Prod.snd Prod.snd
  have hX₁ : X₁.PosSemidef := hX.submatrix Prod.snd
  have hΦ := Φ.completelyPositive 1 X₁ hX₁
  have hsub := hΦ.submatrix (fun a : Fin d => (0, a))
  convert hsub using 1
  ext i j
  rfl

/-- Positive-map packaging used to transport self-adjointness. -/
def toPositiveLinearMap :
    Matrix (Fin d) (Fin d) ℂ →ₚ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  PositiveLinearMap.mk₀ Φ.toLinearMap fun _X hX =>
    Matrix.nonneg_iff_posSemidef.mpr
      (Φ.map_posSemidef (Matrix.nonneg_iff_posSemidef.mp hX))

/-- Positive complex-linear maps preserve the adjoint. -/
theorem map_conjTranspose (X : Matrix (Fin d) (Fin d) ℂ) :
    Φ (Matrix.conjTranspose X) = Matrix.conjTranspose (Φ X) := by
  have hrealInput : IsSelfAdjoint (X + Xᴴ) := by
    change (X + Xᴴ)ᴴ = X + Xᴴ
    simp [Matrix.conjTranspose_add, add_comm]
  have himagInput : IsSelfAdjoint ((Complex.I : ℂ) • (X - Xᴴ)) := by
    change ((Complex.I : ℂ) • (X - Xᴴ))ᴴ = (Complex.I : ℂ) • (X - Xᴴ)
    ext i j
    simp [Matrix.conjTranspose_apply]
    ring
  have hreal := hrealInput.map' Φ.toPositiveLinearMap
  have himag := himagInput.map' Φ.toPositiveLinearMap
  change (Φ (X + Xᴴ))ᴴ = Φ (X + Xᴴ) at hreal
  change (Φ ((Complex.I : ℂ) • (X - Xᴴ)))ᴴ =
    Φ ((Complex.I : ℂ) • (X - Xᴴ)) at himag
  rw [Φ.toLinearMap.map_add] at hreal
  rw [Φ.toLinearMap.map_smul, Φ.toLinearMap.map_sub] at himag
  ext i j
  have hr := congrFun (congrFun hreal i) j
  have hi := congrFun (congrFun himag i) j
  change star ((Φ X) j i + Φ (Matrix.conjTranspose X) j i) =
    (Φ X) i j + Φ (Matrix.conjTranspose X) i j at hr
  change star (Complex.I * ((Φ X) j i - Φ (Matrix.conjTranspose X) j i)) =
    Complex.I * ((Φ X) i j - Φ (Matrix.conjTranspose X) i j) at hi
  change Φ (Matrix.conjTranspose X) i j = star ((Φ X) j i)
  rw [star_add] at hr
  rw [star_mul, star_sub, Complex.star_def, Complex.conj_I] at hi
  have hIz (z : ℂ) : Complex.I * (z * (-Complex.I)) = z := by
    calc
      Complex.I * (z * (-Complex.I)) = -(Complex.I * Complex.I) * z := by ring
      _ = z := by rw [Complex.I_mul_I]; ring
  have hi' :
      star ((Φ X) j i) - star (Φ (Matrix.conjTranspose X) j i) =
        -((Φ X) i j - Φ (Matrix.conjTranspose X) i j) := by
    calc
      star ((Φ X) j i) - star (Φ (Matrix.conjTranspose X) j i) =
          Complex.I *
            ((star ((Φ X) j i) - star (Φ (Matrix.conjTranspose X) j i)) *
              (-Complex.I)) := (hIz _).symm
      _ = Complex.I *
          (Complex.I * ((Φ X) i j - Φ (Matrix.conjTranspose X) i j)) :=
        congrArg (fun z : ℂ => Complex.I * z) hi
      _ = -((Φ X) i j - Φ (Matrix.conjTranspose X) i j) := by
        rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have htwo :
      (2 : ℂ) * Φ (Matrix.conjTranspose X) i j =
        (2 : ℂ) * star ((Φ X) j i) := by
    linear_combination -hr - hi'
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo

/-- Product indexing of a two-by-two block matrix. -/
def finTwoProdToSum (p : Fin 2 × Fin d) : Sum (Fin d) (Fin d) :=
  if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2

/-- Sum indexing of a two-by-two block matrix. -/
def finTwoSumToProd : Sum (Fin d) (Fin d) → Fin 2 × Fin d
  | Sum.inl i => (0, i)
  | Sum.inr i => (1, i)

@[simp] theorem finTwoProdToSum_zero (i : Fin d) :
    finTwoProdToSum (0, i) = Sum.inl i := by simp [finTwoProdToSum]

@[simp] theorem finTwoProdToSum_one (i : Fin d) :
    finTwoProdToSum (1, i) = Sum.inr i := by simp [finTwoProdToSum]

@[simp] theorem finTwoProdToSum_sumToProd
    (i : Sum (Fin d) (Fin d)) :
    finTwoProdToSum (finTwoSumToProd i) = i := by
  cases i <;> simp [finTwoSumToProd]

/-- The positive block matrix used in the Kadison--Schwarz argument. -/
def kadisonInputBlock (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Sum (Fin d) (Fin d)) (Sum (Fin d) (Fin d)) ℂ :=
  Matrix.fromBlocks (Xᴴ * X) Xᴴ X 1

theorem kadisonInputBlock_posSemidef (X : Matrix (Fin d) (Fin d) ℂ) :
    (kadisonInputBlock X).PosSemidef := by
  have hOne : Matrix.PosDef (1 : Matrix (Fin d) (Fin d) ℂ) :=
    by simpa using
      (Matrix.PosDef.natCast (n := Fin d) (R := ℂ) 1 one_ne_zero)
  letI : Invertible (1 : Matrix (Fin d) (Fin d) ℂ) := invertibleOne
  rw [kadisonInputBlock]
  have hblock := (Matrix.PosDef.fromBlocks₂₂ (Xᴴ * X) Xᴴ hOne).2
    (by simpa using (Matrix.PosSemidef.zero :
      Matrix.PosSemidef (0 : Matrix (Fin d) (Fin d) ℂ)))
  simpa only [Matrix.conjTranspose_conjTranspose] using hblock

/-- **Kadison--Schwarz for finite matrix channels.** -/
theorem kadisonSchwarz (X : Matrix (Fin d) (Fin d) ℂ) :
    (Φ X)ᴴ * Φ X ≤ Φ (Xᴴ * X) := by
  let B := kadisonInputBlock X
  let M : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
    B.submatrix finTwoProdToSum finTwoProdToSum
  have hM : M.PosSemidef :=
    (kadisonInputBlock_posSemidef X).submatrix finTwoProdToSum
  have hAmp := Φ.completelyPositive 2 M hM
  have hOut := hAmp.submatrix finTwoSumToProd
  have hOutEq :
      (finiteMatrixAmplification Φ.toLinearMap 2 M).submatrix
          finTwoSumToProd finTwoSumToProd =
        Matrix.fromBlocks (Φ (Xᴴ * X)) (Φ X)ᴴ (Φ X) 1 := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [finiteMatrixAmplification, M, B, kadisonInputBlock,
              finTwoProdToSum, finTwoSumToProd]
        | inr j =>
            change Φ Xᴴ i j = (Φ X)ᴴ i j
            rw [Φ.map_conjTranspose]
    | inr i =>
        cases j with
        | inl j =>
            simp [finiteMatrixAmplification, M, B, kadisonInputBlock,
              finTwoProdToSum, finTwoSumToProd]
        | inr j =>
            change Φ (1 : Matrix (Fin d) (Fin d) ℂ) i j =
              (1 : Matrix (Fin d) (Fin d) ℂ) i j
            rw [Φ.map_one]
  rw [hOutEq] at hOut
  have hOne : Matrix.PosDef (1 : Matrix (Fin d) (Fin d) ℂ) :=
    by simpa using
      (Matrix.PosDef.natCast (n := Fin d) (R := ℂ) 1 one_ne_zero)
  letI : Invertible (1 : Matrix (Fin d) (Fin d) ℂ) := invertibleOne
  have hOut' :
      (Matrix.fromBlocks (Φ (Xᴴ * X)) (Φ X)ᴴ ((Φ X)ᴴ)ᴴ 1).PosSemidef := by
    simpa using hOut
  have hdefect :=
    (Matrix.PosDef.fromBlocks₂₂ (Φ (Xᴴ * X)) (Φ X)ᴴ hOne).1 hOut'
  have hs :
      (Φ (Xᴴ * X) - (Φ X)ᴴ * Φ X).PosSemidef := by
    simpa using hdefect
  exact sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr hs)

/-- Matrix represented as a vector in Hilbert--Schmidt geometry. -/
def matrixToHilbertSchmidt (X : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun ij => X ij.1 ij.2)

/-- Hilbert--Schmidt vector represented as a matrix. -/
def hilbertSchmidtToMatrix (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => x (i, j)

@[simp] theorem matrixToHilbertSchmidt_apply
    (X : Matrix (Fin d) (Fin d) ℂ) (ij : Fin d × Fin d) :
    matrixToHilbertSchmidt X ij = X ij.1 ij.2 := rfl

@[simp] theorem hilbertSchmidtToMatrix_apply
    (x : EuclideanSpace ℂ (Fin d × Fin d)) (i j : Fin d) :
    hilbertSchmidtToMatrix x i j = x (i, j) := rfl

@[simp] theorem hilbertSchmidtToMatrix_matrixToHilbertSchmidt
    (X : Matrix (Fin d) (Fin d) ℂ) :
    hilbertSchmidtToMatrix (matrixToHilbertSchmidt X) = X := by
  ext i j
  rfl

@[simp] theorem matrixToHilbertSchmidt_hilbertSchmidtToMatrix
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    matrixToHilbertSchmidt (hilbertSchmidtToMatrix x) = x := by
  ext ij
  rfl

/-- Frobenius norm squared is the trace of `X†X`. -/
theorem trace_conjTranspose_mul_eq_norm_sq
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    Matrix.trace
        ((hilbertSchmidtToMatrix x)ᴴ * hilbertSchmidtToMatrix x) =
      (‖x‖ ^ 2 : ℂ) := by
  have hnorm :
      (‖x‖ ^ 2 : ℂ) = ∑ ij, (‖x ij‖ ^ 2 : ℂ) := by
    norm_cast
    exact EuclideanSpace.norm_sq_eq x
  rw [hnorm, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Matrix.conjTranspose_apply]
  change star (x (j, i)) * x (j, i) = (‖x (j, i)‖ ^ 2 : ℂ)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simpa only [Complex.ofReal_pow] using
    congrArg (fun r : ℝ => (r : ℂ))
      (Complex.sq_norm (x (j, i))).symm

/-- Linear action of a matrix channel on Hilbert--Schmidt vectors. -/
def hilbertSchmidtLinearMap :
    EuclideanSpace ℂ (Fin d × Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d × Fin d) where
  toFun x := matrixToHilbertSchmidt (Φ (hilbertSchmidtToMatrix x))
  map_add' x y := by
    ext ij
    change Φ (hilbertSchmidtToMatrix (x + y)) ij.1 ij.2 =
      (Φ (hilbertSchmidtToMatrix x) + Φ (hilbertSchmidtToMatrix y)) ij.1 ij.2
    rw [show hilbertSchmidtToMatrix (x + y) =
        hilbertSchmidtToMatrix x + hilbertSchmidtToMatrix y by
      ext i j
      rfl]
    rw [Φ.map_add]
  map_smul' c x := by
    ext ij
    change Φ (hilbertSchmidtToMatrix (c • x)) ij.1 ij.2 =
      (c • Φ (hilbertSchmidtToMatrix x)) ij.1 ij.2
    rw [show hilbertSchmidtToMatrix (c • x) =
        c • hilbertSchmidtToMatrix x by
      ext i j
      rfl]
    rw [Φ.map_smul]

@[simp] theorem hilbertSchmidtLinearMap_apply
    (x : EuclideanSpace ℂ (Fin d × Fin d)) (ij : Fin d × Fin d) :
    Φ.hilbertSchmidtLinearMap x ij =
      Φ (hilbertSchmidtToMatrix x) ij.1 ij.2 := rfl

/-- **Every finite bistochastic channel contracts Hilbert--Schmidt norm.** -/
theorem norm_hilbertSchmidtLinearMap_apply_le
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖Φ.hilbertSchmidtLinearMap x‖ ≤ ‖x‖ := by
  let X := hilbertSchmidtToMatrix x
  have hKS := Φ.kadisonSchwarz X
  have htrace :=
    (Matrix.tracePositiveLinearMap (Fin d) ℂ ℂ).monotone hKS
  change Matrix.trace ((Φ X)ᴴ * Φ X) ≤
    Matrix.trace (Φ (Xᴴ * X)) at htrace
  rw [Φ.trace_preserving] at htrace
  have hsquareComplex :
      (‖Φ.hilbertSchmidtLinearMap x‖ ^ 2 : ℂ) ≤ (‖x‖ ^ 2 : ℂ) := by
    rw [← trace_conjTranspose_mul_eq_norm_sq
      (Φ.hilbertSchmidtLinearMap x),
      ← trace_conjTranspose_mul_eq_norm_sq x]
    simpa [hilbertSchmidtLinearMap, X] using htrace
  have hsquare : ‖Φ.hilbertSchmidtLinearMap x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    exact_mod_cast hsquareComplex
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

/-- Bounded Hilbert--Schmidt realization of a finite bistochastic channel. -/
def hilbertSchmidtOperator :
    EuclideanSpace ℂ (Fin d × Fin d) →L[ℂ]
      EuclideanSpace ℂ (Fin d × Fin d) :=
  LinearMap.mkContinuous Φ.hilbertSchmidtLinearMap 1 fun x => by
    simpa using Φ.norm_hilbertSchmidtLinearMap_apply_le x

@[simp] theorem hilbertSchmidtOperator_apply
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    Φ.hilbertSchmidtOperator x = Φ.hilbertSchmidtLinearMap x := rfl

/-- Operator norm form of Hilbert--Schmidt contractivity. -/
theorem norm_hilbertSchmidtOperator_le_one :
    ‖Φ.hilbertSchmidtOperator‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le Φ.hilbertSchmidtLinearMap zero_le_one _

/-- Exact persistent-sector ceiling for every finite bistochastic channel. -/
theorem returnAmplitude_exactAsymptoticCeiling
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    IsExactAsymptoticReturnAmplitudeCeiling
      (fun n : ℕ => inner ℂ x ((Φ.hilbertSchmidtOperator ^ n) x))
      (finiteContractionPersistentMass Φ.hilbertSchmidtOperator x) :=
  finiteContraction_returnAmplitude_exactAsymptoticCeiling
    Φ.hilbertSchmidtOperator Φ.norm_hilbertSchmidtOperator_le_one x

/-- Exact squared-return ceiling for every finite bistochastic channel. -/
theorem returnFidelity_exactAsymptoticCeiling
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    IsExactAsymptoticReturnFidelityCeiling
      (fun n : ℕ => inner ℂ x ((Φ.hilbertSchmidtOperator ^ n) x))
      ((finiteContractionPersistentMass Φ.hilbertSchmidtOperator x) ^ 2) :=
  finiteContraction_returnFidelity_exactAsymptoticCeiling
    Φ.hilbertSchmidtOperator Φ.norm_hilbertSchmidtOperator_le_one x

/-- Sharp late-return/no-return threshold for every finite bistochastic channel. -/
theorem returnThreshold_dichotomy
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    (∀ target : ℝ,
      target < finiteContractionPersistentMass Φ.hilbertSchmidtOperator x →
      ∀ M : ℕ, ∃ n : ℕ, M < n ∧
        target ≤
          ‖inner ℂ x ((Φ.hilbertSchmidtOperator ^ n) x)‖) ∧
    (∀ target : ℝ,
      finiteContractionPersistentMass Φ.hilbertSchmidtOperator x < target →
      ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
        ‖inner ℂ x ((Φ.hilbertSchmidtOperator ^ n) x)‖ < target) :=
  finiteContraction_returnThreshold_dichotomy
    Φ.hilbertSchmidtOperator Φ.norm_hilbertSchmidtOperator_le_one x

/-- Coupled burn-in and recurrence deadline below the channel's persistent ceiling. -/
theorem exists_return_at_target_before_deadline
    (x : EuclideanSpace ℂ (Fin d × Fin d))
    (hpersistent :
      0 < finiteContractionPersistentMass Φ.hilbertSchmidtOperator x)
    (target : ℝ) (htarget0 : 0 ≤ target)
    (htarget :
      target < finiteContractionPersistentMass Φ.hilbertSchmidtOperator x) :
    ∃ B N : ℕ,
      IsUniversalWeightedFloquetFidelityDeadline
        (finiteContractionPeripheralWeight Φ.hilbertSchmidtOperator x)
        ((finiteContractionPersistentMass Φ.hilbertSchmidtOperator x - target) /
          (2 * finiteContractionPersistentMass Φ.hilbertSchmidtOperator x)) N ∧
      ∃ n : ℕ, B < n ∧ n ≤ (B + 1) * N ∧
        target ≤
          ‖inner ℂ x ((Φ.hilbertSchmidtOperator ^ n) x)‖ :=
  finiteContraction_exists_return_at_target_before_deadline
    Φ.hilbertSchmidtOperator Φ.norm_hilbertSchmidtOperator_le_one x
      hpersistent target htarget0 htarget

/-- Reverse-water deadline specialization for every channel with at least two peripheral modes. -/
theorem exists_return_at_target_before_waterDeadline
    (x : EuclideanSpace ℂ (Fin d × Fin d))
    (hpersistent :
      0 < finiteContractionPersistentMass Φ.hilbertSchmidtOperator x)
    (hperipheral :
      2 ≤ Fintype.card
        (FiniteContractionPeripheralEigenvalue Φ.hilbertSchmidtOperator))
    (target : ℝ) (htarget0 : 0 ≤ target)
    (htarget :
      target < finiteContractionPersistentMass Φ.hilbertSchmidtOperator x) :
    let eta :=
      (finiteContractionPersistentMass Φ.hilbertSchmidtOperator x - target) /
        (2 * finiteContractionPersistentMass Φ.hilbertSchmidtOperator x)
    ∃ (heta0 : 0 < eta) (heta1 : eta ≤ 1) (B n : ℕ),
      B < n ∧
      n ≤ (B + 1) *
        universalWeightedFloquetFidelityRecurrenceTime
          hperipheral
          (finiteContractionPeripheralWeight Φ.hilbertSchmidtOperator x)
          (finiteContractionPeripheralWeight_nonneg
            Φ.hilbertSchmidtOperator x hpersistent)
          (sum_finiteContractionPeripheralWeight
            Φ.hilbertSchmidtOperator x hpersistent)
          eta heta0 heta1 ∧
      target ≤ ‖inner ℂ x ((Φ.hilbertSchmidtOperator ^ n) x)‖ :=
  finiteContraction_exists_return_at_target_before_waterDeadline
    Φ.hilbertSchmidtOperator Φ.norm_hilbertSchmidtOperator_le_one x
      hpersistent hperipheral target htarget0 htarget

end FiniteBistochasticMatrixChannel
end RHTower
