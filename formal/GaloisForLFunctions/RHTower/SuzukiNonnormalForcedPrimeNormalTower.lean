import GaloisForLFunctions.RHTower.SuzukiVolterraLogGradeRecurrence
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Nonnormal source-forced prime-normal tower

Exact all-grade coefficient tower and finite telescoping residual for arbitrary bounded prime
adjacency, without self-adjointness, normality, or spectral assumptions.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Half-integer inverse-log source order. -/
def suzukiForcedPrimeNormalOrder (m : ℕ) : ℝ := m + 1 / 2

/-- Coefficient at the `k`-th nonnormal prime descendant forced from source order `m+1/2`. -/
def suzukiForcedPrimeNormalFactor (m : ℕ) : ℕ → ℝ
  | 0 => ((2 * m + 1 : ℕ) : ℝ) / (4 * m + 4)
  | k + 1 =>
      suzukiForcedPrimeNormalFactor m k *
        (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8))

@[simp] theorem suzukiForcedPrimeNormalFactor_zero (m : ℕ) :
    suzukiForcedPrimeNormalFactor m 0 = ((2 * m + 1 : ℕ) : ℝ) / (4 * m + 4) := rfl

@[simp] theorem suzukiForcedPrimeNormalFactor_succ (m k : ℕ) :
    suzukiForcedPrimeNormalFactor m (k + 1) =
      suzukiForcedPrimeNormalFactor m k *
        (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8)) := rfl

theorem suzukiForcedPrimeNormalFactor_source (m : ℕ) :
    -(2 * suzukiForcedPrimeNormalOrder m + 1) * suzukiForcedPrimeNormalFactor m 0 =
      -suzukiForcedPrimeNormalOrder m := by
  rw [suzukiForcedPrimeNormalOrder, suzukiForcedPrimeNormalFactor_zero]
  push_cast
  field_simp
  ring

theorem suzukiForcedPrimeNormalFactor_cancel (m k : ℕ) :
    -(2 * suzukiForcedPrimeNormalOrder m + 2 * (k + 1) + 1) *
        suzukiForcedPrimeNormalFactor m (k + 1) +
      (suzukiForcedPrimeNormalOrder m + (k + 1)) *
        suzukiForcedPrimeNormalFactor m k = 0 := by
  rw [suzukiForcedPrimeNormalOrder, suzukiForcedPrimeNormalFactor_succ]
  push_cast
  field_simp
  ring

theorem suzukiForcedPrimeNormalFactor_pos (m k : ℕ) :
    0 < suzukiForcedPrimeNormalFactor m k := by
  induction k with
  | zero => rw [suzukiForcedPrimeNormalFactor_zero]; positivity
  | succ k ih => rw [suzukiForcedPrimeNormalFactor_succ]; positivity

theorem suzukiForcedPrimeNormalFactor_le_half_pow (m k : ℕ) :
    suzukiForcedPrimeNormalFactor m k ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  induction k with
  | zero =>
      rw [suzukiForcedPrimeNormalFactor_zero, pow_one]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * m + 4)).mpr
      norm_num
      linarith
  | succ k ih =>
      rw [suzukiForcedPrimeNormalFactor_succ, pow_succ]
      have hratio :
          (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8)) ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (m + k) + 8)).mpr
        norm_num
        linarith
      calc
        suzukiForcedPrimeNormalFactor m k *
            (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8)) ≤
            (1 / 2 : ℝ) ^ (k + 1) *
              (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ (1 / 2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)

theorem suzukiForcedPrimeNormalFactor_zeroOrder_eq (k : ℕ) :
    suzukiForcedPrimeNormalFactor 0 k = suzukiPrimeNormalGradeFactor (k + 1) := by
  induction k with
  | zero => norm_num [suzukiForcedPrimeNormalFactor, suzukiPrimeNormalGradeFactor]
  | succ k ih =>
      rw [suzukiForcedPrimeNormalFactor_succ, ih,
        suzukiPrimeNormalGradeFactor_succ]
      congr 1
      push_cast
      ring

/-- The forced coefficient is exactly the tail quotient of the universal prime-normal
grade sequence. -/
theorem suzukiForcedPrimeNormalFactor_mul_gradeFactor (m k : ℕ) :
    suzukiForcedPrimeNormalFactor m k * suzukiPrimeNormalGradeFactor m =
      suzukiPrimeNormalGradeFactor (m + k + 1) := by
  induction k with
  | zero =>
      rw [suzukiForcedPrimeNormalFactor_zero]
      conv_rhs => rw [show m + 0 + 1 = m + 1 by omega,
        suzukiPrimeNormalGradeFactor_succ]
      ring
  | succ k ih =>
      rw [suzukiForcedPrimeNormalFactor_succ]
      calc
        (suzukiForcedPrimeNormalFactor m k *
              (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8))) *
            suzukiPrimeNormalGradeFactor m =
            (suzukiForcedPrimeNormalFactor m k *
              suzukiPrimeNormalGradeFactor m) *
              (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8)) := by ring
        _ = suzukiPrimeNormalGradeFactor (m + k + 1) *
              (((2 * (m + k) + 3 : ℕ) : ℝ) / (4 * (m + k) + 8)) := by rw [ih]
        _ = suzukiPrimeNormalGradeFactor (m + (k + 1) + 1) := by
          rw [show m + (k + 1) + 1 = (m + k + 1) + 1 by omega,
            suzukiPrimeNormalGradeFactor_succ]
          congr 1
          push_cast
          ring

section NonnormalTower

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The actual `k`-th forced descendant under an arbitrary bounded, possibly nonnormal,
prime adjacency. -/
def suzukiForcedPrimeNormalTower
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) : X :=
  (suzukiForcedPrimeNormalFactor m k : ℂ) • ((B ^ k) A)

/-- Grade zero lands on the original power source with the exact Volterra coefficient. -/
theorem suzukiForcedPrimeNormalTower_source
    (B : X →L[ℂ] X) (A : X) (m : ℕ) :
    ((-(2 * suzukiForcedPrimeNormalOrder m + 1) : ℝ) : ℂ) •
        suzukiForcedPrimeNormalTower B A m 0 =
      ((-suzukiForcedPrimeNormalOrder m : ℝ) : ℂ) • A := by
  rw [suzukiForcedPrimeNormalTower]
  simp only [pow_zero, one_apply_eq_self, smul_smul]
  congr 1
  exact_mod_cast suzukiForcedPrimeNormalFactor_source m

/-- Applying the nonnormal adjacency advances the tower by one operator word, with no
self-adjointness or normality premise. -/
theorem suzukiForcedPrimeNormalTower_apply
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) :
    B (suzukiForcedPrimeNormalTower B A m k) =
      (suzukiForcedPrimeNormalFactor m k : ℂ) • ((B ^ (k + 1)) A) := by
  rw [suzukiForcedPrimeNormalTower, map_smul]
  congr 1
  rw [pow_succ']
  rfl

/-- Every interior grade cancels exactly in the forced prime-normal differential equation. -/
theorem suzukiForcedPrimeNormalTower_cancel
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) :
    ((-(2 * suzukiForcedPrimeNormalOrder m + 2 * (k + 1) + 1) : ℝ) : ℂ) •
          suzukiForcedPrimeNormalTower B A m (k + 1) +
        ((suzukiForcedPrimeNormalOrder m + (k + 1) : ℝ) : ℂ) •
          B (suzukiForcedPrimeNormalTower B A m k) = 0 := by
  rw [suzukiForcedPrimeNormalTower, suzukiForcedPrimeNormalTower_apply]
  simp only [smul_smul, ← add_smul, smul_eq_zero]
  left
  exact_mod_cast suzukiForcedPrimeNormalFactor_cancel m k

/-- Uniform all-grade majorant.  Nonnormality costs only powers of the bounded adjacency norm;
the source-normal coefficient contracts by one half at every grade. -/
theorem norm_suzukiForcedPrimeNormalTower_le
    [Nontrivial X] (B : X →L[ℂ] X) (A : X) (m k : ℕ) :
    ‖suzukiForcedPrimeNormalTower B A m k‖ ≤
      (1 / 2 : ℝ) ^ (k + 1) * ‖B‖ ^ k * ‖A‖ := by
  rw [suzukiForcedPrimeNormalTower, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suzukiForcedPrimeNormalFactor_pos m k)]
  have hpow : ‖B ^ k‖ ≤ ‖B‖ ^ k := norm_pow_le B k
  have happ : ‖(B ^ k) A‖ ≤ ‖B ^ k‖ * ‖A‖ := (B ^ k).le_opNorm A
  calc
    suzukiForcedPrimeNormalFactor m k * ‖(B ^ k) A‖ ≤
        suzukiForcedPrimeNormalFactor m k * (‖B ^ k‖ * ‖A‖) :=
      mul_le_mul_of_nonneg_left happ (suzukiForcedPrimeNormalFactor_pos m k).le
    _ ≤ suzukiForcedPrimeNormalFactor m k * (‖B‖ ^ k * ‖A‖) := by
      gcongr
      exact (suzukiForcedPrimeNormalFactor_pos m k).le
    _ ≤ (1 / 2 : ℝ) ^ (k + 1) * (‖B‖ ^ k * ‖A‖) :=
      mul_le_mul_of_nonneg_right (suzukiForcedPrimeNormalFactor_le_half_pow m k)
        (mul_nonneg (pow_nonneg (norm_nonneg B) k) (norm_nonneg A))
    _ = (1 / 2 : ℝ) ^ (k + 1) * ‖B‖ ^ k * ‖A‖ := by ring

section RealProfiles

variable [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]

/-- One exact inverse-log profile term, written in the unrestricted logarithmic coordinate
`L = exp t`. -/
def suzukiForcedPrimeNormalTerm
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) : X :=
  Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t) •
    suzukiForcedPrimeNormalTower B A m k

/-- Declared derivative of one exact profile term. -/
def suzukiForcedPrimeNormalTermDeriv
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) : X :=
  (-(suzukiForcedPrimeNormalOrder m + k + 1) *
      Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t)) •
    suzukiForcedPrimeNormalTower B A m k

omit [IsScalarTower ℝ ℂ X] in
theorem hasDerivAt_suzukiForcedPrimeNormalTerm
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) :
    HasDerivAt (suzukiForcedPrimeNormalTerm B A m k)
      (suzukiForcedPrimeNormalTermDeriv B A m k t) t := by
  let lam : ℝ := suzukiForcedPrimeNormalOrder m + k + 1
  have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-lam * s))
      (Real.exp (-lam * t) * -lam) t :=
    by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (-lam * t)).comp t hlin
  have hsmul : HasDerivAt
      (fun s : ℝ => Real.exp (-lam * s) • suzukiForcedPrimeNormalTower B A m k)
      ((Real.exp (-lam * t) * -lam) • suzukiForcedPrimeNormalTower B A m k) t :=
    hexp.smul_const (suzukiForcedPrimeNormalTower B A m k)
  change HasDerivAt
    (fun s : ℝ => Real.exp (-lam * s) • suzukiForcedPrimeNormalTower B A m k)
    ((-lam * Real.exp (-lam * t)) • suzukiForcedPrimeNormalTower B A m k) t
  simpa only [mul_comm] using hsmul

/-- Reparametrized prime-normal differential expression.  Its zero set is exactly
`(2L-B)F_L' + F = 0` under `L = exp t`. -/
def suzukiNonnormalPrimeExpression
    (B : X →L[ℂ] X) (t : ℝ) (F Fdot : X) : X :=
  (2 * Real.exp t) • Fdot - B Fdot + Real.exp t • F

omit [IsScalarTower ℝ ℂ X] in
theorem suzukiNonnormalPrimeExpression_add
    (B : X →L[ℂ] X) (t : ℝ) (F G Fdot Gdot : X) :
    suzukiNonnormalPrimeExpression B t (F + G) (Fdot + Gdot) =
      suzukiNonnormalPrimeExpression B t F Fdot +
        suzukiNonnormalPrimeExpression B t G Gdot := by
  simp [suzukiNonnormalPrimeExpression, map_add]
  abel

/-- A single term contributes one diagonal grade and one next-word grade. -/
theorem suzukiNonnormalPrimeExpression_term
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) :
    suzukiNonnormalPrimeExpression B t
        (suzukiForcedPrimeNormalTerm B A m k t)
        (suzukiForcedPrimeNormalTermDeriv B A m k t) =
      (-(2 * suzukiForcedPrimeNormalOrder m + 2 * k + 1) *
          Real.exp (-(suzukiForcedPrimeNormalOrder m + k) * t)) •
        suzukiForcedPrimeNormalTower B A m k +
      ((suzukiForcedPrimeNormalOrder m + k + 1) *
          Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t)) •
        B (suzukiForcedPrimeNormalTower B A m k) := by
  simp only [suzukiNonnormalPrimeExpression, suzukiForcedPrimeNormalTerm,
    suzukiForcedPrimeNormalTermDeriv, smul_smul,
    ContinuousLinearMap.map_smul_of_tower, sub_eq_add_neg]
  have hexp1 :
      Real.exp t * Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t) =
        Real.exp (-(suzukiForcedPrimeNormalOrder m + k) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htwo :
      (2 * Real.exp t) *
          (-(suzukiForcedPrimeNormalOrder m + k + 1) *
            Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t)) =
        (-(2 * (suzukiForcedPrimeNormalOrder m + k + 1)) *
          Real.exp (-(suzukiForcedPrimeNormalOrder m + k) * t)) := by
    calc
      _ = -(2 * (suzukiForcedPrimeNormalOrder m + k + 1)) *
          (Real.exp t *
            Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t)) := by ring
      _ = _ := by rw [hexp1]
  rw [htwo, hexp1]
  module

/-- Source profile appearing on the right side of the forced prime-normal equation. -/
def suzukiForcedPrimeNormalSourceProfile (A : X) (m : ℕ) (t : ℝ) : X :=
  (-suzukiForcedPrimeNormalOrder m *
      Real.exp (-suzukiForcedPrimeNormalOrder m * t)) • A

/-- Diagonal contribution of one inverse-log grade. -/
def suzukiForcedPrimeNormalDiagonal
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) : X :=
  (-(2 * suzukiForcedPrimeNormalOrder m + 2 * k + 1) *
      Real.exp (-(suzukiForcedPrimeNormalOrder m + k) * t)) •
    suzukiForcedPrimeNormalTower B A m k

/-- One omitted next-word residual exposed by truncating after grade `k`. -/
def suzukiForcedPrimeNormalResidual
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) : X :=
  ((suzukiForcedPrimeNormalOrder m + k + 1) *
      Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t)) •
    B (suzukiForcedPrimeNormalTower B A m k)

theorem suzukiNonnormalPrimeExpression_term_packet
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) :
    suzukiNonnormalPrimeExpression B t
        (suzukiForcedPrimeNormalTerm B A m k t)
        (suzukiForcedPrimeNormalTermDeriv B A m k t) =
      suzukiForcedPrimeNormalDiagonal B A m k t +
        suzukiForcedPrimeNormalResidual B A m k t := by
  simpa only [suzukiForcedPrimeNormalDiagonal,
    suzukiForcedPrimeNormalResidual] using
      suzukiNonnormalPrimeExpression_term B A m k t

/-- The first diagonal grade is exactly the original forced source. -/
theorem suzukiForcedPrimeNormalDiagonal_zero
    (B : X →L[ℂ] X) (A : X) (m : ℕ) (t : ℝ) :
    suzukiForcedPrimeNormalDiagonal B A m 0 t =
      suzukiForcedPrimeNormalSourceProfile A m t := by
  have hsource :
      (-(2 * suzukiForcedPrimeNormalOrder m + 1) : ℝ) •
          suzukiForcedPrimeNormalTower B A m 0 =
        (-suzukiForcedPrimeNormalOrder m : ℝ) • A := by
    simpa only [← Complex.coe_algebraMap, algebraMap_smul] using
      suzukiForcedPrimeNormalTower_source B A m
  rw [suzukiForcedPrimeNormalDiagonal,
    suzukiForcedPrimeNormalSourceProfile]
  norm_num only [Nat.cast_zero, mul_zero, add_zero]
  calc
    (-(2 * suzukiForcedPrimeNormalOrder m + 1) *
          Real.exp (-suzukiForcedPrimeNormalOrder m * t)) •
        suzukiForcedPrimeNormalTower B A m 0 =
      Real.exp (-suzukiForcedPrimeNormalOrder m * t) •
        ((-(2 * suzukiForcedPrimeNormalOrder m + 1)) •
          suzukiForcedPrimeNormalTower B A m 0) := by
            rw [smul_smul]
            congr 1
            ring
    _ = Real.exp (-suzukiForcedPrimeNormalOrder m * t) •
        ((-suzukiForcedPrimeNormalOrder m) • A) := by rw [hsource]
    _ = (-suzukiForcedPrimeNormalOrder m *
          Real.exp (-suzukiForcedPrimeNormalOrder m * t)) • A := by
            rw [smul_smul]
            congr 1
            ring

/-- Adjacent grades telescope with no spectral or normality hypothesis on `B`. -/
theorem suzukiForcedPrimeNormalResidual_add_diagonal_succ
    (B : X →L[ℂ] X) (A : X) (m k : ℕ) (t : ℝ) :
    suzukiForcedPrimeNormalResidual B A m k t +
      suzukiForcedPrimeNormalDiagonal B A m (k + 1) t = 0 := by
  have hcancel :
      (-(2 * suzukiForcedPrimeNormalOrder m + 2 * (k + 1) + 1) : ℝ) •
          suzukiForcedPrimeNormalTower B A m (k + 1) +
        (suzukiForcedPrimeNormalOrder m + (k + 1) : ℝ) •
          B (suzukiForcedPrimeNormalTower B A m k) = 0 := by
    simpa only [← Complex.coe_algebraMap, algebraMap_smul] using
      suzukiForcedPrimeNormalTower_cancel B A m k
  rw [suzukiForcedPrimeNormalResidual, suzukiForcedPrimeNormalDiagonal]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [show suzukiForcedPrimeNormalOrder m + (k + 1 : ℝ) =
      suzukiForcedPrimeNormalOrder m + k + 1 by ring]
  let e : ℝ := Real.exp (-(suzukiForcedPrimeNormalOrder m + k + 1) * t)
  change
    ((suzukiForcedPrimeNormalOrder m + k + 1) * e) •
        B (suzukiForcedPrimeNormalTower B A m k) +
      (-(2 * suzukiForcedPrimeNormalOrder m + 2 * (k + 1) + 1) * e) •
        suzukiForcedPrimeNormalTower B A m (k + 1) = 0
  calc
    _ = e •
        ((suzukiForcedPrimeNormalOrder m + (k + 1) : ℝ) •
            B (suzukiForcedPrimeNormalTower B A m k) +
          (-(2 * suzukiForcedPrimeNormalOrder m + 2 * (k + 1) + 1) : ℝ) •
            suzukiForcedPrimeNormalTower B A m (k + 1)) := by
              rw [smul_add, smul_smul, smul_smul]
              congr 2 <;> ring
    _ = 0 := by rw [add_comm, hcancel, smul_zero]

/-- Prefix containing grades `0,...,N`. -/
def suzukiForcedPrimeNormalPartial
    (B : X →L[ℂ] X) (A : X) (m : ℕ) : ℕ → ℝ → X
  | 0, t => suzukiForcedPrimeNormalTerm B A m 0 t
  | N + 1, t => suzukiForcedPrimeNormalPartial B A m N t +
      suzukiForcedPrimeNormalTerm B A m (N + 1) t

/-- Exact derivative packet for the finite prefix. -/
def suzukiForcedPrimeNormalPartialDeriv
    (B : X →L[ℂ] X) (A : X) (m : ℕ) : ℕ → ℝ → X
  | 0, t => suzukiForcedPrimeNormalTermDeriv B A m 0 t
  | N + 1, t => suzukiForcedPrimeNormalPartialDeriv B A m N t +
      suzukiForcedPrimeNormalTermDeriv B A m (N + 1) t

omit [IsScalarTower ℝ ℂ X] in
theorem hasDerivAt_suzukiForcedPrimeNormalPartial
    (B : X →L[ℂ] X) (A : X) (m N : ℕ) (t : ℝ) :
    HasDerivAt (suzukiForcedPrimeNormalPartial B A m N)
      (suzukiForcedPrimeNormalPartialDeriv B A m N t) t := by
  induction N with
  | zero =>
      simpa only [suzukiForcedPrimeNormalPartial,
        suzukiForcedPrimeNormalPartialDeriv] using
          hasDerivAt_suzukiForcedPrimeNormalTerm B A m 0 t
  | succ N ih =>
      change HasDerivAt
        (fun x => suzukiForcedPrimeNormalPartial B A m N x +
          suzukiForcedPrimeNormalTerm B A m (N + 1) x)
        (suzukiForcedPrimeNormalPartialDeriv B A m N t +
          suzukiForcedPrimeNormalTermDeriv B A m (N + 1) t) t
      exact ih.add (hasDerivAt_suzukiForcedPrimeNormalTerm B A m (N + 1) t)

/-- Every finite prefix solves the forced equation up to exactly one next-word residual.
All interior grades cancel, for arbitrary bounded and possibly nonnormal `B`. -/
theorem suzukiNonnormalPrimeExpression_partial_eq_source_add_residual
    (B : X →L[ℂ] X) (A : X) (m N : ℕ) (t : ℝ) :
    suzukiNonnormalPrimeExpression B t
        (suzukiForcedPrimeNormalPartial B A m N t)
        (suzukiForcedPrimeNormalPartialDeriv B A m N t) =
      suzukiForcedPrimeNormalSourceProfile A m t +
        suzukiForcedPrimeNormalResidual B A m N t := by
  induction N with
  | zero =>
      rw [suzukiForcedPrimeNormalPartial,
        suzukiForcedPrimeNormalPartialDeriv,
        suzukiNonnormalPrimeExpression_term_packet,
        suzukiForcedPrimeNormalDiagonal_zero]
  | succ N ih =>
      rw [suzukiForcedPrimeNormalPartial,
        suzukiForcedPrimeNormalPartialDeriv,
        suzukiNonnormalPrimeExpression_add, ih,
        suzukiNonnormalPrimeExpression_term_packet]
      calc
        (suzukiForcedPrimeNormalSourceProfile A m t +
              suzukiForcedPrimeNormalResidual B A m N t) +
            (suzukiForcedPrimeNormalDiagonal B A m (N + 1) t +
              suzukiForcedPrimeNormalResidual B A m (N + 1) t) =
          suzukiForcedPrimeNormalSourceProfile A m t +
            (suzukiForcedPrimeNormalResidual B A m N t +
              suzukiForcedPrimeNormalDiagonal B A m (N + 1) t) +
            suzukiForcedPrimeNormalResidual B A m (N + 1) t := by abel
        _ = suzukiForcedPrimeNormalSourceProfile A m t +
            suzukiForcedPrimeNormalResidual B A m (N + 1) t := by
              rw [suzukiForcedPrimeNormalResidual_add_diagonal_succ,
                add_zero]

end RealProfiles

end NonnormalTower

end

end GaloisForLFunctions.RHTower
