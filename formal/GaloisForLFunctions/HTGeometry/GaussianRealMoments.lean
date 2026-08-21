import GaloisForLFunctions.HTGeometry.CompletePairing
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Moments of a centred real Gaussian

The moments of `gaussianReal 0 v` are the derivatives at `0` of its moment-generating function
`t ↦ exp (v t² / 2)`.  Differentiating that function once produces a factor `v t`, and the Leibniz
rule for `t ↦ t * h t` evaluated at the origin then gives the two-step recursion

```text
m₀ = 1,   m₁ = 0,   m_{n+2} = (n + 1) * v * m_n ,
```

which is exactly the recursion satisfied by the complete-pairing sum of a word of `n` equal letters
with constant kernel `v`.  Hence

```text
∫ x ^ n ∂(gaussianReal 0 v) = completePairing (fun _ _ => v) (List.replicate n a) ,
```

the diagonal case of Isserlis' theorem.
-/

open Real MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

/-! ## The generating function -/

/-- The moment-generating function of a centred real Gaussian of variance `v`. -/
noncomputable def gaussKernel (v : ℝ) : ℝ → ℝ := fun t => Real.exp (v * t ^ 2 / 2)

@[simp] theorem gaussKernel_zero (v : ℝ) : gaussKernel v 0 = 1 := by
  simp [gaussKernel]

theorem hasDerivAt_gaussKernel (v t : ℝ) :
    HasDerivAt (gaussKernel v) (v * (t * gaussKernel v t)) t := by
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have h1 : HasDerivAt (fun t : ℝ => v * t ^ 2 / 2) (v * t) t := by
    have h := (hp.const_mul v).div_const 2
    have heq : v * (2 * t) / 2 = v * t := by ring
    rwa [heq] at h
  rw [show v * (t * gaussKernel v t) = Real.exp (v * t ^ 2 / 2) * (v * t) from by
    simp only [gaussKernel]; ring]
  exact h1.exp

theorem deriv_gaussKernel (v : ℝ) :
    deriv (gaussKernel v) = fun t => v * (t * gaussKernel v t) :=
  funext fun t => (hasDerivAt_gaussKernel v t).deriv

theorem contDiff_gaussKernel (v : ℝ) : ContDiff ℝ (⊤ : WithTop ℕ∞) (gaussKernel v) :=
  Real.contDiff_exp.comp ((contDiff_const.mul (contDiff_id.pow 2)).div_const 2)

theorem differentiable_iteratedDeriv_gaussKernel (v : ℝ) (m : ℕ) :
    Differentiable ℝ (iteratedDeriv m (gaussKernel v)) :=
  (contDiff_gaussKernel v).differentiable_iteratedDeriv m
    (by exact_mod_cast WithTop.coe_lt_top (m : ℕ∞))

/-! ## Leibniz for multiplication by the coordinate -/

/-- **Leibniz rule for `t ↦ t * h t`.**  Each differentiation either hits `h` or removes the factor
`t`, so the `n`-th derivative is `t * h⁽ⁿ⁾ t + n * h⁽ⁿ⁻¹⁾ t`. -/
theorem iteratedDeriv_id_mul (h : ℝ → ℝ) (hdiff : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m h)) :
    ∀ n : ℕ, iteratedDeriv (n + 1) (fun t => t * h t)
      = fun t => t * iteratedDeriv (n + 1) h t + (n + 1 : ℝ) * iteratedDeriv n h t := by
  intro n
  induction n with
  | zero =>
      rw [iteratedDeriv_one]
      funext t
      have hd : HasDerivAt (fun t : ℝ => t * h t) (1 * h t + t * deriv h t) t :=
        (hasDerivAt_id t).mul ((hdiff 0).differentiableAt.hasDerivAt.congr_deriv (by
          simp [iteratedDeriv_zero]))
      rw [hd.deriv]
      simp [iteratedDeriv_one, iteratedDeriv_zero]
      ring
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have hd : HasDerivAt
          (fun t : ℝ => t * iteratedDeriv (n + 1) h t + (n + 1 : ℝ) * iteratedDeriv n h t)
          ((1 * iteratedDeriv (n + 1) h t + t * deriv (iteratedDeriv (n + 1) h) t)
            + (n + 1 : ℝ) * deriv (iteratedDeriv n h) t) t :=
        ((hasDerivAt_id t).mul (hdiff (n + 1) t).hasDerivAt).add
          (((hdiff n) t).hasDerivAt.const_mul _)
      rw [hd.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
      push_cast
      ring

/-! ## The moment recursion -/

/-- The derivatives at the origin of the Gaussian generating function satisfy the double-factorial
recursion. -/
theorem iteratedDeriv_gaussKernel_zero_succ_succ (v : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (gaussKernel v) 0
      = (n + 1 : ℝ) * v * iteratedDeriv n (gaussKernel v) 0 := by
  have hstep : iteratedDeriv (n + 2) (gaussKernel v)
      = iteratedDeriv (n + 1) (fun t => v * (t * gaussKernel v t)) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, iteratedDeriv_succ', deriv_gaussKernel]
  rw [hstep]
  rw [iteratedDeriv_const_mul_field v (fun t => t * gaussKernel v t)]
  rw [iteratedDeriv_id_mul (gaussKernel v) (differentiable_iteratedDeriv_gaussKernel v) n]
  simp
  ring

@[simp] theorem iteratedDeriv_gaussKernel_zero_zero (v : ℝ) :
    iteratedDeriv 0 (gaussKernel v) 0 = 1 := by
  simp [iteratedDeriv_zero]

@[simp] theorem iteratedDeriv_gaussKernel_zero_one (v : ℝ) :
    iteratedDeriv 1 (gaussKernel v) 0 = 0 := by
  rw [iteratedDeriv_one, deriv_gaussKernel]
  simp

/-! ## Moments of the Gaussian measure -/

/-- The moments of a centred real Gaussian are the derivatives of its generating function. -/
theorem integral_pow_gaussianReal (v : NNReal) (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 v) = iteratedDeriv n (gaussKernel (v : ℝ)) 0 := by
  have hset : integrableExpSet (fun x : ℝ => x) (gaussianReal 0 v) = Set.univ := by
    ext t
    simp [integrableExpSet, integrable_exp_mul_gaussianReal t]
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 v)) := by
    rw [hset]
    simp
  have hmgf := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v) h0 n
  rw [mgf_fun_id_gaussianReal] at hmgf
  have hfun : (fun t : ℝ => rexp ((0 : ℝ) * t + (v : ℝ) * t ^ 2 / 2)) = gaussKernel (v : ℝ) := by
    funext t
    simp [gaussKernel]
  rw [hfun] at hmgf
  rw [hmgf]
  simp

/-- **The moment recursion for a centred real Gaussian.** -/
theorem integral_pow_gaussianReal_succ_succ (v : NNReal) (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂(gaussianReal 0 v)
      = (n + 1 : ℝ) * (v : ℝ) * ∫ x, x ^ n ∂(gaussianReal 0 v) := by
  rw [integral_pow_gaussianReal, integral_pow_gaussianReal,
    iteratedDeriv_gaussKernel_zero_succ_succ]

@[simp] theorem integral_pow_zero_gaussianReal (v : NNReal) :
    ∫ x, x ^ 0 ∂(gaussianReal 0 v) = 1 := by
  rw [integral_pow_gaussianReal]
  simp

@[simp] theorem integral_pow_one_gaussianReal (v : NNReal) :
    ∫ x, x ^ 1 ∂(gaussianReal 0 v) = 0 := by
  rw [integral_pow_gaussianReal]
  simp

/-! ## The diagonal case of Isserlis' theorem -/

/-- **The diagonal case of Isserlis' theorem.**  The `n`-th moment of a centred real Gaussian is the
complete-pairing sum of a word of `n` equal letters whose kernel is the variance. -/
theorem integral_pow_gaussianReal_eq_completePairing {α : Type*} (v : NNReal) (a : α) (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 v)
      = completePairing (fun _ _ : α => (v : ℝ)) (List.replicate n a) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | (m + 2) =>
      rw [integral_pow_gaussianReal_succ_succ, ih m (by omega),
        completePairing_replicate_succ_succ]

end GaloisForLFunctions.HTGeometry
