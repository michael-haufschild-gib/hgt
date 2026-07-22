import GaloisForLFunctions.RHTower.SoninPrincipalRelativeIdeal
import GaloisForLFunctions.RHTower.SoninPrincipalShellCyclicTrace
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Unique signed finite part on finite Sonin principal-relative systems

For an injective finite prime system, the exact Sonin principal shell and the retained
Schatten-1 relative ideal form a direct sum.  The direct presentation carries the unique signed
finite part whose principal value is the logarithmic orbital trace and whose relative value is
the ordinary operator trace.

This closes the finite-prime principal-relative trace interface.  It does not assert cofinal
compatibility, a Burnol archimedean completion, a lower floor, or RH.
-/

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

namespace RHTower

open ContinuousLinearMap

/-- A presentation of an operator as a finite prime principal shell plus an exact relative
correction. -/
structure SoninPrincipalRelativePresentation
    {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) where
  coefficient : Matrix (Fin n) (Fin n) ℂ
  relative : evenSubspace →L[ℂ] evenSubspace
  relative_mem : IsSoninPrincipalRelativeIdeal relative

namespace SoninPrincipalRelativePresentation

variable {n : ℕ} {a : ℝ} {p : Fin n → ℕ} {hp : ∀ i, (p i).Prime}

@[ext]
theorem ext {X Y : SoninPrincipalRelativePresentation a p hp}
    (hcoeff : X.coefficient = Y.coefficient)
    (hrelative : X.relative = Y.relative) : X = Y := by
  cases X
  cases Y
  simp_all

instance : Zero (SoninPrincipalRelativePresentation a p hp) where
  zero := ⟨0, 0, IsSoninPrincipalRelativeIdeal.zero⟩

instance : Add (SoninPrincipalRelativePresentation a p hp) where
  add X Y :=
    ⟨X.coefficient + Y.coefficient, X.relative + Y.relative,
      X.relative_mem.add Y.relative_mem⟩

instance : Neg (SoninPrincipalRelativePresentation a p hp) where
  neg X := ⟨-X.coefficient, -X.relative, X.relative_mem.neg⟩

instance : SMul ℂ (SoninPrincipalRelativePresentation a p hp) where
  smul c X := ⟨c • X.coefficient, c • X.relative, X.relative_mem.smul c⟩

@[simp] theorem coefficient_zero :
    (0 : SoninPrincipalRelativePresentation a p hp).coefficient = 0 := rfl

@[simp] theorem relative_zero :
    (0 : SoninPrincipalRelativePresentation a p hp).relative = 0 := rfl

@[simp] theorem coefficient_add
    (X Y : SoninPrincipalRelativePresentation a p hp) :
    (X + Y).coefficient = X.coefficient + Y.coefficient := rfl

@[simp] theorem relative_add
    (X Y : SoninPrincipalRelativePresentation a p hp) :
    (X + Y).relative = X.relative + Y.relative := rfl

@[simp] theorem coefficient_neg (X : SoninPrincipalRelativePresentation a p hp) :
    (-X).coefficient = -X.coefficient := rfl

@[simp] theorem relative_neg (X : SoninPrincipalRelativePresentation a p hp) :
    (-X).relative = -X.relative := rfl

@[simp] theorem coefficient_smul (c : ℂ)
    (X : SoninPrincipalRelativePresentation a p hp) :
    (c • X).coefficient = c • X.coefficient := rfl

@[simp] theorem relative_smul (c : ℂ)
    (X : SoninPrincipalRelativePresentation a p hp) :
    (c • X).relative = c • X.relative := rfl

/-- The represented bounded operator. -/
def toOperator (X : SoninPrincipalRelativePresentation a p hp) :
    evenSubspace →L[ℂ] evenSubspace :=
  finitePrimeSoninPrincipalShellCombination a p hp X.coefficient + X.relative

end SoninPrincipalRelativePresentation

section ShellLinearity

variable {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)

@[simp]
theorem finitePrimeSoninPrincipalShellCombination_zero :
    finitePrimeSoninPrincipalShellCombination a p hp 0 = 0 := by
  classical
  unfold finitePrimeSoninPrincipalShellCombination
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [Matrix.zero_apply]
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem finitePrimeSoninPrincipalShellCombination_add
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninPrincipalShellCombination a p hp (A + B) =
      finitePrimeSoninPrincipalShellCombination a p hp A +
        finitePrimeSoninPrincipalShellCombination a p hp B := by
  classical
  unfold finitePrimeSoninPrincipalShellCombination
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.add_apply]
  apply ContinuousLinearMap.ext
  intro x
  exact add_smul (A i j) (B i j)
    ((evenSoninMixedShellTranslation a (p i : ℝ) (p j : ℝ)
      (by exact_mod_cast (hp i).one_lt) (by exact_mod_cast (hp j).one_lt)) x)

theorem finitePrimeSoninPrincipalShellCombination_neg
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninPrincipalShellCombination a p hp (-A) =
      -finitePrimeSoninPrincipalShellCombination a p hp A := by
  classical
  unfold finitePrimeSoninPrincipalShellCombination
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.neg_apply]
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem finitePrimeSoninPrincipalShellCombination_sub
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninPrincipalShellCombination a p hp (A - B) =
      finitePrimeSoninPrincipalShellCombination a p hp A -
        finitePrimeSoninPrincipalShellCombination a p hp B := by
  rw [sub_eq_add_neg, finitePrimeSoninPrincipalShellCombination_add,
    finitePrimeSoninPrincipalShellCombination_neg, sub_eq_add_neg]

theorem finitePrimeSoninPrincipalShellCombination_smul
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninPrincipalShellCombination a p hp (c • A) =
      c • finitePrimeSoninPrincipalShellCombination a p hp A := by
  classical
  unfold finitePrimeSoninPrincipalShellCombination
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.smul_apply]
  exact mul_smul c (A i j)
    (evenSoninMixedShellTranslation a (p i : ℝ) (p j : ℝ)
      (by exact_mod_cast (hp i).one_lt) (by exact_mod_cast (hp j).one_lt))

end ShellLinearity

namespace SoninPrincipalRelativePresentation

variable {n : ℕ} {a : ℝ} {p : Fin n → ℕ} {hp : ∀ i, (p i).Prime}

@[simp]
theorem toOperator_zero :
    toOperator (0 : SoninPrincipalRelativePresentation a p hp) = 0 := by
  simp [toOperator]

theorem toOperator_add (X Y : SoninPrincipalRelativePresentation a p hp) :
    toOperator (X + Y) = toOperator X + toOperator Y := by
  rw [toOperator, toOperator, toOperator, coefficient_add, relative_add,
    finitePrimeSoninPrincipalShellCombination_add]
  abel

theorem toOperator_neg (X : SoninPrincipalRelativePresentation a p hp) :
    toOperator (-X) = -toOperator X := by
  rw [toOperator, toOperator, coefficient_neg, relative_neg,
    finitePrimeSoninPrincipalShellCombination_neg]
  abel

theorem toOperator_smul (c : ℂ) (X : SoninPrincipalRelativePresentation a p hp) :
    toOperator (c • X) = c • toOperator X := by
  rw [toOperator, toOperator, coefficient_smul, relative_smul,
    finitePrimeSoninPrincipalShellCombination_smul, smul_add]

/-- **Directness of the finite prime principal-relative presentation.** -/
theorem toOperator_injective
    (ha : 0 < a) (hinj : Function.Injective p) :
    Function.Injective
      (toOperator : SoninPrincipalRelativePresentation a p hp →
        evenSubspace →L[ℂ] evenSubspace) := by
  intro X Y hXY
  have hshellEq :
      finitePrimeSoninPrincipalShellCombination a p hp
          (X.coefficient - Y.coefficient) =
        Y.relative - X.relative := by
    rw [finitePrimeSoninPrincipalShellCombination_sub]
    unfold toOperator at hXY
    calc
      finitePrimeSoninPrincipalShellCombination a p hp X.coefficient -
          finitePrimeSoninPrincipalShellCombination a p hp Y.coefficient =
        (finitePrimeSoninPrincipalShellCombination a p hp X.coefficient + X.relative) -
          (finitePrimeSoninPrincipalShellCombination a p hp Y.coefficient + X.relative) := by
            abel
      _ = (finitePrimeSoninPrincipalShellCombination a p hp Y.coefficient + Y.relative) -
          (finitePrimeSoninPrincipalShellCombination a p hp Y.coefficient + X.relative) := by
            rw [hXY]
      _ = Y.relative - X.relative := by abel
  have hshellMem : IsSoninPrincipalRelativeIdeal
      (finitePrimeSoninPrincipalShellCombination a p hp
        (X.coefficient - Y.coefficient)) :=
    (Y.relative_mem.sub X.relative_mem).of_eq hshellEq.symm
  have hdiff : X.coefficient - Y.coefficient = 0 := by
    by_contra hne
    exact finitePrimeSoninPrincipalShellCombination_not_mem_relativeIdeal_of_ne_zero
      a ha p hp hinj (X.coefficient - Y.coefficient) hne hshellMem
  have hcoeff : X.coefficient = Y.coefficient := sub_eq_zero.mp hdiff
  have hrelative : X.relative = Y.relative := by
    have hsame :
        finitePrimeSoninPrincipalShellCombination a p hp X.coefficient + X.relative =
          finitePrimeSoninPrincipalShellCombination a p hp X.coefficient + Y.relative := by
      simpa only [toOperator, hcoeff] using hXY
    exact add_left_cancel hsame
  exact ext hcoeff hrelative

/-- Principal logarithmic trace of a coefficient matrix. -/
def principalTrace (p : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i, A i i * (Real.log (p i) : ℂ)

@[simp]
theorem principalTrace_zero (p : Fin n → ℕ) : principalTrace p 0 = 0 := by
  classical
  simp [principalTrace]

theorem principalTrace_add (p : Fin n → ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    principalTrace p (A + B) = principalTrace p A + principalTrace p B := by
  classical
  simp [principalTrace, add_mul, Finset.sum_add_distrib]

theorem principalTrace_neg (p : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    principalTrace p (-A) = -principalTrace p A := by
  classical
  simp [principalTrace, Finset.sum_neg_distrib]

theorem principalTrace_smul (p : Fin n → ℕ) (c : ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    principalTrace p (c • A) = c * principalTrace p A := by
  classical
  simp [principalTrace, mul_assoc, Finset.mul_sum]

/-- The signed finite part of a principal-relative presentation. -/
def finitePart (X : SoninPrincipalRelativePresentation a p hp) : ℂ :=
  principalTrace p X.coefficient + opTrace X.relative

@[simp]
theorem finitePart_zero :
    finitePart (0 : SoninPrincipalRelativePresentation a p hp) = 0 := by
  simp [finitePart]

theorem finitePart_add (X Y : SoninPrincipalRelativePresentation a p hp) :
    finitePart (X + Y) = finitePart X + finitePart Y := by
  rw [finitePart, finitePart, finitePart, coefficient_add, relative_add,
    principalTrace_add,
    opTrace_add_of_memSchattenClass_one
      X.relative_mem.memSchattenClass_one Y.relative_mem.memSchattenClass_one]
  ring

theorem finitePart_neg (X : SoninPrincipalRelativePresentation a p hp) :
    finitePart (-X) = -finitePart X := by
  rw [finitePart, finitePart, coefficient_neg, relative_neg,
    principalTrace_neg, opTrace_neg]
  ring

theorem finitePart_smul (c : ℂ) (X : SoninPrincipalRelativePresentation a p hp) :
    finitePart (c • X) = c * finitePart X := by
  rw [finitePart, finitePart, coefficient_smul, relative_smul,
    principalTrace_smul, opTrace_smul]
  ring

/-- The signed finite part depends only on the represented operator. -/
theorem finitePart_eq_of_toOperator_eq
    (ha : 0 < a) (hinj : Function.Injective p)
    {X Y : SoninPrincipalRelativePresentation a p hp}
    (hXY : toOperator X = toOperator Y) :
    finitePart X = finitePart Y := by
  rw [toOperator_injective ha hinj hXY]

/-- Bounded cyclicity of the ordinary trace on the exact relative component. -/
theorem opTrace_mul_relative_eq
    (X : SoninPrincipalRelativePresentation a p hp)
    (L : evenSubspace →L[ℂ] evenSubspace) :
    opTrace (L * X.relative) = opTrace (X.relative * L) := by
  simpa only [ContinuousLinearMap.mul_def] using
    X.relative_mem.memSchattenClass_one.one_opTrace_comp_comm L

/-- Canonical presentation of an actual finite prime Sonin Gram combination. -/
def ofQuadraticCorner
    (ha : 0 < a) (A : Matrix (Fin n) (Fin n) ℂ) :
    SoninPrincipalRelativePresentation a p hp where
  coefficient := A
  relative := finitePrimeSoninQuadraticCornerCombination a p hp A -
    finitePrimeSoninPrincipalShellCombination a p hp A
  relative_mem :=
    finitePrimeSoninQuadraticCorner_principalRelativeEq_shellCombination
      a ha p hp A

theorem toOperator_ofQuadraticCorner
    (ha : 0 < a) (A : Matrix (Fin n) (Fin n) ℂ) :
    toOperator (ofQuadraticCorner (p := p) (hp := hp) ha A) =
      finitePrimeSoninQuadraticCornerCombination a p hp A := by
  unfold toOperator ofQuadraticCorner
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply, sub_apply]
  abel

/-- **Exact finite-prime anomaly formula.**  The actual Gram finite part is its logarithmic
principal trace plus the ordinary trace of the unique Schatten-1 residual. -/
theorem finitePart_ofQuadraticCorner
    (ha : 0 < a) (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePart (ofQuadraticCorner (p := p) (hp := hp) ha A) =
      principalTrace p A +
        opTrace (finitePrimeSoninQuadraticCornerCombination a p hp A -
          finitePrimeSoninPrincipalShellCombination a p hp A) := by
  rfl

end SoninPrincipalRelativePresentation

end RHTower
