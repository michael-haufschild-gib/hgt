import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedDampingWorkOfTheMobiusEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The signed-work demand is strictly weaker than the tangent norm

Cauchy–Schwarz shows that a horizon-uniform bound on the pronic norm of the damping tangent pays
the continuation budget.  The converse fails, and the separation is visible already in two pronic
cells: a row that rotates in the `(1, 2)` plane at frequency `K` has

* constant pronic energy `1` — the rotation is an isometry of the receiver norm,
* identically vanishing complete signed work — so the linear continuation bound holds with the
  budget `0`,
* tangent pronic norm `|K|` — unbounded as `K` grows.

So the continuation demand constrains the *component of the tangent along the source*, and says
nothing about the size of the tangent.  Large tangential motion is free; only motion that
increases the energy going backwards has to be paid for.

This family is a countermodel, not an arithmetic source: it is used only to separate two
hypotheses about the same receiver geometry.  Its message for the arithmetic problem is that the
unproved horizon-uniform bound on `‖E_η‖_T` is a strictly stronger demand than the continuation
inequality, so the latter must be attacked directly rather than through the tangent norm.
-/

open Finset Set RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- A row supported on the first two pronic cells, rotating at frequency `K`. -/
def rotatingRow (K ε : ℝ) : ℕ → ℝ := fun n =>
  if n = 1 then Real.sqrt 2 * Real.cos (K * ε)
  else if n = 2 then Real.sqrt 6 * Real.sin (K * ε) else 0

/-- Its damping tangent. -/
def rotatingTangent (K ε : ℝ) : ℕ → ℝ := fun n =>
  if n = 1 then Real.sqrt 2 * (-Real.sin (K * ε) * K)
  else if n = 2 then Real.sqrt 6 * (Real.cos (K * ε) * K) else 0

theorem sum_Icc_one_two (f : ℕ → ℝ) : ∑ n ∈ Icc 1 2, f n = f 1 + f 2 := by
  have h : (Icc 1 2 : Finset ℕ) = {1, 2} := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]
  simp

/-- The pronic norm at horizon two, with its two weights `1·2` and `2·3`. -/
theorem pronicNorm_two_eq (v : ℕ → ℝ) :
    pronicNorm 2 v = Real.sqrt (v 1 ^ 2 / 2 + v 2 ^ 2 / 6) := by
  unfold pronicNorm
  congr 1
  rw [sum_Icc_one_two]
  norm_num

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt_six_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

theorem rotatingRow_one (K ε : ℝ) : rotatingRow K ε 1 = Real.sqrt 2 * Real.cos (K * ε) := by
  simp [rotatingRow]

theorem rotatingRow_two (K ε : ℝ) : rotatingRow K ε 2 = Real.sqrt 6 * Real.sin (K * ε) := by
  simp [rotatingRow]

theorem rotatingTangent_one (K ε : ℝ) :
    rotatingTangent K ε 1 = Real.sqrt 2 * (-Real.sin (K * ε) * K) := by simp [rotatingTangent]

theorem rotatingTangent_two (K ε : ℝ) :
    rotatingTangent K ε 2 = Real.sqrt 6 * (Real.cos (K * ε) * K) := by simp [rotatingTangent]

/-- The rotation is an isometry of the receiver norm: the energy is constant in the damping. -/
theorem pronicNorm_rotatingRow (K ε : ℝ) : pronicNorm 2 (rotatingRow K ε) = 1 := by
  rw [pronicNorm_two_eq]
  have hkey : rotatingRow K ε 1 ^ 2 / 2 + rotatingRow K ε 2 ^ 2 / 6 = 1 := by
    rw [rotatingRow_one, rotatingRow_two]
    linear_combination (Real.cos (K * ε) ^ 2 / 2) * sqrt_two_sq +
      (Real.sin (K * ε) ^ 2 / 6) * sqrt_six_sq + Real.sin_sq_add_cos_sq (K * ε)
  rw [hkey, Real.sqrt_one]

/-- The tangent norm is the rotation frequency: unbounded over the family. -/
theorem pronicNorm_rotatingTangent (K ε : ℝ) : pronicNorm 2 (rotatingTangent K ε) = |K| := by
  rw [pronicNorm_two_eq]
  have hkey : rotatingTangent K ε 1 ^ 2 / 2 + rotatingTangent K ε 2 ^ 2 / 6 = K ^ 2 := by
    rw [rotatingTangent_one, rotatingTangent_two]
    linear_combination ((Real.sin (K * ε) * K) ^ 2 / 2) * sqrt_two_sq +
      ((Real.cos (K * ε) * K) ^ 2 / 6) * sqrt_six_sq + K ^ 2 * Real.sin_sq_add_cos_sq (K * ε)
  rw [hkey, Real.sqrt_sq_eq_abs]

/-- The complete signed work vanishes identically: the tangent is pronic-orthogonal to the row. -/
theorem signedWork_rotatingRow (K ε : ℝ) :
    ∑ n ∈ Icc 1 2, rotatingRow K ε n * rotatingTangent K ε n / ((n : ℝ) * ((n : ℝ) + 1)) = 0 := by
  rw [sum_Icc_one_two]
  simp only [rotatingRow_one, rotatingRow_two, rotatingTangent_one, rotatingTangent_two]
  norm_num
  linear_combination (-(Real.cos (K * ε) * Real.sin (K * ε) * K) / 2) * sqrt_two_sq +
    (Real.sin (K * ε) * Real.cos (K * ε) * K / 6) * sqrt_six_sq

theorem hasDerivAt_rotatingRow (K ε : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rotatingRow K x n) (rotatingTangent K ε n) ε := by
  have hKx : HasDerivAt (fun x : ℝ => K * x) K ε := by
    simpa using (hasDerivAt_id' (x := ε)).const_mul K
  by_cases h1 : n = 1
  · subst h1
    have hfun : (fun x : ℝ => rotatingRow K x 1) = fun x : ℝ => Real.sqrt 2 * Real.cos (K * x) := by
      funext x
      exact rotatingRow_one K x
    rw [hfun, rotatingTangent_one]
    exact hKx.cos.const_mul _
  · by_cases h2 : n = 2
    · subst h2
      have hfun : (fun x : ℝ => rotatingRow K x 2) =
          fun x : ℝ => Real.sqrt 6 * Real.sin (K * x) := by
        funext x
        exact rotatingRow_two K x
      rw [hfun, rotatingTangent_two]
      exact hKx.sin.const_mul _
    · have hfun : (fun x : ℝ => rotatingRow K x n) = fun _ : ℝ => (0 : ℝ) := by
        funext x
        simp [rotatingRow, h1, h2]
      have hval : rotatingTangent K ε n = 0 := by simp [rotatingTangent, h1, h2]
      rw [hfun, hval]
      exact hasDerivAt_const _ _

/-- **Strict weakening.**  For every frequency there is a differentiable row family with constant
receiver energy, vanishing complete signed work, and tangent norm `|K|`.  Hence no bound on the
tangent norm can be extracted from a continuation budget, and the continuation demand is strictly
weaker than the tangent-norm demand that implies it. -/
theorem exists_vanishing_signed_work_with_large_tangent (K : ℝ) :
    ∃ v w : ℝ → ℕ → ℝ,
      (∀ ε n, HasDerivAt (fun x => v x n) (w ε n) ε) ∧
        (∀ ε, pronicNorm 2 (v ε) = 1) ∧ (∀ ε, pronicNorm 2 (w ε) = |K|) ∧
        ∀ ε, ∑ n ∈ Icc 1 2, v ε n * w ε n / ((n : ℝ) * ((n : ℝ) + 1)) = 0 :=
  ⟨rotatingRow K, rotatingTangent K, fun ε n => hasDerivAt_rotatingRow K ε n,
    fun ε => pronicNorm_rotatingRow K ε, fun ε => pronicNorm_rotatingTangent K ε,
    fun ε => signedWork_rotatingRow K ε⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
