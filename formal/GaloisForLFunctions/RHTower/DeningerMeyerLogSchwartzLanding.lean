import GaloisForLFunctions.RHTower.DeningerMeyerRapidDecayLanding
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Full log-Schwartz landing of Meyer's Poisson operator

Meyer's archimedean target is a Bruhat--Schwartz space for the multiplicative
group, not merely a space of continuous functions with value-level endpoint
decay.  Ordinary `𝓢(ℝ, ℂ)` in logarithmic radius is a necessary consequence;
the actual all-weight target is the stronger intersection requiring decay
against every exponential weight.

This file proves the missing all-derivative statement.  If

`E f(x) = x f'(x)`,

then termwise differentiation on every lower half-line gives

`d^k/dt^k Zf(exp t) = Z(E^k f)(exp t)`.

At the negative end one must not assume, without proof, that every Euler
iterate remains in Meyer's two-zero-mode source.  Instead we differentiate the
already proved Poisson reflection.  With `A = -(1 + E)` this gives the exact
identity

`Z(E^k f)(exp t) = exp(-t) Z(A^k (𝓕 f))(exp(-t))`.

Euler iteration preserves evenness and the physical zero mode.  The large-end
Schwartz estimate therefore controls both sides and proves rapid decay of every
logarithmic derivative.  Consequently the radial Poisson image is ordinary
Schwartz and, more strongly, has all-derivative decay against every
exponential weight.

No Riemann-hypothesis premise, positivity assumption, spectral realization,
numerical computation, or source-provenance hypothesis occurs.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform SchwartzMap
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Euler differentiation on the Schwartz source -/

/-- Multiplicative Euler derivative `E f(x) = x f'(x)` on Schwartz space. -/
def deningerMeyerEulerCLM :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) ∘L
    SchwartzMap.derivCLM ℂ ℂ

private theorem deningerMeyer_cast_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) :=
  Complex.hasTemperateGrowth_ofReal

@[simp]
theorem deningerMeyerEulerCLM_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deningerMeyerEulerCLM f x = (x : ℂ) * deriv f x := by
  simp [deningerMeyerEulerCLM,
    SchwartzMap.smulLeftCLM_apply_apply
      deningerMeyer_cast_hasTemperateGrowth]

/-- Iteration of the Euler derivative. -/
def deningerMeyerEulerIterate (k : ℕ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  deningerMeyerEulerCLM ^ k

@[simp]
theorem deningerMeyerEulerIterate_zero
    (f : SchwartzMap ℝ ℂ) :
    deningerMeyerEulerIterate 0 f = f := by
  simp [deningerMeyerEulerIterate]

theorem deningerMeyerEulerIterate_succ
    (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    deningerMeyerEulerIterate (k + 1) f =
      deningerMeyerEulerCLM (deningerMeyerEulerIterate k f) := by
  simp [deningerMeyerEulerIterate, pow_succ', mul_apply_eq_comp]

/-- Poisson sum in logarithmic radius. -/
def deningerMeyerLogSum
    (f : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  deningerMeyerSum f (Real.exp t)

/-! ## Local termwise differentiation -/

private theorem summable_shifted_inverse_square_scaled
    (C a : ℝ) :
    Summable (fun n : ℕ =>
      C / (a ^ 2 * (((n : ℝ) + 1) ^ 2))) := by
  have hbase :
      Summable (fun n : ℕ =>
        1 / ((((n : ℝ) + 1)) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr
      (by norm_num : 1 < 2)
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr h
  have hscaled := hbase.mul_left (C / a ^ 2)
  refine hscaled.congr fun n => ?_
  field_simp

private theorem deningerMeyerEuler_term_bound
    (f : SchwartzMap ℝ ℂ) (T : ℝ) (n : ℕ)
    {t : ℝ} (ht : T < t) :
    ‖deningerMeyerEulerCLM f
        (((n : ℝ) + 1) * Real.exp t)‖ ≤
      SchwartzMap.seminorm ℂ 2 0 (deningerMeyerEulerCLM f) /
        ((Real.exp T) ^ 2 * (((n : ℝ) + 1) ^ 2)) := by
  let g := deningerMeyerEulerCLM f
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hT : 0 < Real.exp T := Real.exp_pos T
  have het : Real.exp T < Real.exp t :=
    Real.exp_lt_exp.mpr ht
  have harg :
      0 < ((n : ℝ) + 1) * Real.exp t :=
    mul_pos hn (Real.exp_pos t)
  have hsem :=
    SchwartzMap.norm_pow_mul_le_seminorm ℂ g 2
      (((n : ℝ) + 1) * Real.exp t)
  have hden :
      0 < ‖((n : ℝ) + 1) * Real.exp t‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr harg.ne') _
  have hraw :
      ‖g (((n : ℝ) + 1) * Real.exp t)‖ ≤
        SchwartzMap.seminorm ℂ 2 0 g /
          ‖((n : ℝ) + 1) * Real.exp t‖ ^ 2 := by
    apply (le_div_iff₀ hden).2
    simpa [mul_comm] using hsem
  have hS :
      0 ≤ SchwartzMap.seminorm ℂ 2 0 g := by positivity
  have hdenle :
      (Real.exp T) ^ 2 * (((n : ℝ) + 1) ^ 2) ≤
        ‖((n : ℝ) + 1) * Real.exp t‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_pos harg, mul_pow]
    have hsquare :
        (Real.exp T) ^ 2 ≤ (Real.exp t) ^ 2 := by
      nlinarith [Real.exp_pos T, Real.exp_pos t]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hsquare
        (sq_nonneg ((n : ℝ) + 1)))
  have hminor :
      0 < (Real.exp T) ^ 2 * (((n : ℝ) + 1) ^ 2) :=
    mul_pos (sq_pos_of_pos hT) (sq_pos_of_pos hn)
  exact hraw.trans
    (div_le_div_of_nonneg_left hS hminor hdenle)

private theorem hasDerivAt_deningerMeyer_log_summand
    (f : SchwartzMap ℝ ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => f (((n : ℝ) + 1) * Real.exp s))
      (deningerMeyerEulerCLM f
        (((n : ℝ) + 1) * Real.exp t)) t := by
  change HasDerivAt
    (f ∘ fun s : ℝ => ((n : ℝ) + 1) * Real.exp s)
    (deningerMeyerEulerCLM f
      (((n : ℝ) + 1) * Real.exp t)) t
  have harg :
      HasDerivAt
        (fun s : ℝ => ((n : ℝ) + 1) * Real.exp s)
        (((n : ℝ) + 1) * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul ((n : ℝ) + 1)
  simpa only [Function.comp_apply, deningerMeyerEulerCLM_apply,
      Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_exp] using
    (f.hasDerivAt
      (((n : ℝ) + 1) * Real.exp t)).scomp t harg

/--
Exact first logarithmic derivative of the positive Poisson sum.  The proof is
local on an arbitrary half-line `Ioi T`, where all summand derivatives have one
summable Schwartz-seminorm majorant.
-/
theorem hasDerivAt_deningerMeyerLogSum
    (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (deningerMeyerLogSum f)
      (deningerMeyerLogSum (deningerMeyerEulerCLM f) t) t := by
  change HasDerivAt
    (fun z : ℝ =>
      ∑' n : ℕ, f (((n : ℝ) + 1) * Real.exp z))
    (∑' n : ℕ, deningerMeyerEulerCLM f
      (((n : ℝ) + 1) * Real.exp t)) t
  let T := t - 1
  let C :=
    SchwartzMap.seminorm ℂ 2 0 (deningerMeyerEulerCLM f)
  let u : ℕ → ℝ := fun n =>
    C / ((Real.exp T) ^ 2 * (((n : ℝ) + 1) ^ 2))
  have hu : Summable u :=
    summable_shifted_inverse_square_scaled C (Real.exp T)
  have hTt : T < t := by
    dsimp [T]
    linarith
  have hsum0 :
      Summable (fun n : ℕ =>
        f (((n : ℝ) + 1) * Real.exp t)) :=
    deningerMeyerPositiveSum_summable f
      (Real.exp_ne_zero t)
  have h :=
    hasDerivAt_tsum_of_isPreconnected
      (g := fun (n : ℕ) (s : ℝ) =>
        f (((n : ℝ) + 1) * Real.exp s))
      (g' := fun (n : ℕ) (s : ℝ) =>
        deningerMeyerEulerCLM f
          (((n : ℝ) + 1) * Real.exp s))
      (t := Ioi T) (y₀ := t) (y := t)
      hu isOpen_Ioi isPreconnected_Ioi
      (fun n s _ =>
        hasDerivAt_deningerMeyer_log_summand f n s)
      (fun n s hs => by
        simpa [u, C] using
          deningerMeyerEuler_term_bound f T n hs)
      hTt hsum0 hTt
  exact h

theorem deriv_deningerMeyerLogSum
    (f : SchwartzMap ℝ ℂ) :
    deriv (deningerMeyerLogSum f) =
      deningerMeyerLogSum (deningerMeyerEulerCLM f) := by
  funext t
  exact (hasDerivAt_deningerMeyerLogSum f t).deriv

/-- Every iterated log derivative is the Poisson sum of the corresponding
Euler iterate of the source. -/
theorem iteratedDeriv_deningerMeyerLogSum
    (f : SchwartzMap ℝ ℂ) (k : ℕ) :
    iteratedDeriv k (deningerMeyerLogSum f) =
      deningerMeyerLogSum (deningerMeyerEulerIterate k f) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih,
        deriv_deningerMeyerLogSum,
        deningerMeyerEulerIterate_succ]

/-- The log-radius Poisson sum is smooth for every Schwartz source. -/
theorem contDiff_deningerMeyerLogSum
    (f : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (deningerMeyerLogSum f) := by
  rw [contDiff_infty]
  intro N
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _
  rw [iteratedDeriv_deningerMeyerLogSum]
  exact fun t =>
    (hasDerivAt_deningerMeyerLogSum
      (deningerMeyerEulerIterate k f) t).differentiableAt

/-! ## Parity and the reflected Euler operator -/

/-- Fourier-side Euler operator forced by differentiating
`exp(-t) Zg(exp(-t))`: `A = -(1 + E)`. -/
def deningerMeyerReflectedEulerCLM :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  -(ContinuousLinearMap.id ℂ (SchwartzMap ℝ ℂ) +
    deningerMeyerEulerCLM)

@[simp]
theorem deningerMeyerReflectedEulerCLM_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deningerMeyerReflectedEulerCLM f x =
      -(f x + (x : ℂ) * deriv f x) := by
  simp [deningerMeyerReflectedEulerCLM,
    deningerMeyerEulerCLM_apply]

/-- Iteration of the reflected Euler operator. -/
def deningerMeyerReflectedEulerIterate (k : ℕ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  deningerMeyerReflectedEulerCLM ^ k

@[simp]
theorem deningerMeyerReflectedEulerIterate_zero
    (f : SchwartzMap ℝ ℂ) :
    deningerMeyerReflectedEulerIterate 0 f = f := by
  simp [deningerMeyerReflectedEulerIterate]

theorem deningerMeyerReflectedEulerIterate_succ
    (k : ℕ) (f : SchwartzMap ℝ ℂ) :
    deningerMeyerReflectedEulerIterate (k + 1) f =
      deningerMeyerReflectedEulerCLM
        (deningerMeyerReflectedEulerIterate k f) := by
  simp [deningerMeyerReflectedEulerIterate, pow_succ',
    mul_apply_eq_comp]

/-- The derivative of an even smooth complex function is odd. -/
private theorem deriv_neg_eq_neg_of_even
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have hleft :
      HasDerivAt
        (f ∘ fun y : ℝ => -y)
        ((-1 : ℝ) • deriv f (-x)) x :=
    (f.hasDerivAt (-x)).scomp x (hasDerivAt_neg x)
  have heq :
      (f ∘ fun y : ℝ => -y) = f := by
    funext y
    exact heven y
  have hleft' :
      HasDerivAt f ((-1 : ℝ) • deriv f (-x)) x := by
    simpa only [heq] using hleft
  have hu :=
    hleft'.unique (f.hasDerivAt x)
  have hu' :
      -deriv f (-x) = deriv f x := by
    simpa only [Complex.real_smul, Complex.ofReal_neg,
      Complex.ofReal_one, neg_mul, one_mul] using hu
  simpa only [neg_neg] using congrArg Neg.neg hu'

/-- Euler differentiation preserves evenness. -/
theorem deningerMeyerEulerCLM_even
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    ∀ x : ℝ,
      deningerMeyerEulerCLM f (-x) =
        deningerMeyerEulerCLM f x := by
  intro x
  rw [deningerMeyerEulerCLM_apply,
    deningerMeyerEulerCLM_apply,
    deriv_neg_eq_neg_of_even f heven x]
  push_cast
  ring

/-- Euler differentiation preserves vanishing at the physical origin. -/
@[simp]
theorem deningerMeyerEulerCLM_zero
    (f : SchwartzMap ℝ ℂ) :
    deningerMeyerEulerCLM f 0 = 0 := by
  simp

theorem deningerMeyerEulerIterate_even_zero
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hf0 : f 0 = 0) (k : ℕ) :
    (∀ x : ℝ,
      deningerMeyerEulerIterate k f (-x) =
        deningerMeyerEulerIterate k f x) ∧
      deningerMeyerEulerIterate k f 0 = 0 := by
  induction k with
  | zero =>
      simpa using And.intro heven hf0
  | succ k ih =>
      rw [deningerMeyerEulerIterate_succ]
      exact
        ⟨deningerMeyerEulerCLM_even _ ih.1,
          deningerMeyerEulerCLM_zero _⟩

/-- The reflected Euler operator preserves evenness and the physical zero mode. -/
theorem deningerMeyerReflectedEulerCLM_even_zero
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hf0 : f 0 = 0) :
    (∀ x : ℝ,
      deningerMeyerReflectedEulerCLM f (-x) =
        deningerMeyerReflectedEulerCLM f x) ∧
      deningerMeyerReflectedEulerCLM f 0 = 0 := by
  constructor
  · intro x
    rw [deningerMeyerReflectedEulerCLM_apply,
      deningerMeyerReflectedEulerCLM_apply,
      heven,
      deriv_neg_eq_neg_of_even f heven x]
    push_cast
    ring
  · simp [deningerMeyerReflectedEulerCLM_apply, hf0]

theorem deningerMeyerReflectedEulerIterate_even_zero
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hf0 : f 0 = 0) (k : ℕ) :
    (∀ x : ℝ,
      deningerMeyerReflectedEulerIterate k f (-x) =
        deningerMeyerReflectedEulerIterate k f x) ∧
      deningerMeyerReflectedEulerIterate k f 0 = 0 := by
  induction k with
  | zero =>
      simpa using And.intro heven hf0
  | succ k ih =>
      rw [deningerMeyerReflectedEulerIterate_succ]
      exact deningerMeyerReflectedEulerCLM_even_zero _ ih.1 ih.2

/-! ## Differentiated Poisson reflection -/

/-- Paugam's weighted inversion in logarithmic radius. -/
def deningerMeyerLogReflection
    (g : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * deningerMeyerLogSum g (-t)

theorem deningerMeyerLogSum_reflection
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (t : ℝ) :
    deningerMeyerLogSum f t =
      deningerMeyerLogReflection
        (FourierTransform.fourierCLE ℂ
          (SchwartzMap ℝ ℂ) f) t := by
  simpa [deningerMeyerLogSum, deningerMeyerLogReflection,
      Real.exp_neg] using
    (deningerMeyerPoisson_reflection f hf (Real.exp_pos t))

private theorem deningerMeyerLogSum_reflectedEuler
    (g : SchwartzMap ℝ ℂ) (t : ℝ) :
    deningerMeyerLogSum (deningerMeyerReflectedEulerCLM g) t =
      -(deningerMeyerLogSum g t +
        deningerMeyerLogSum (deningerMeyerEulerCLM g) t) := by
  change deningerMeyerSum (deningerMeyerReflectedEulerCLM g)
      (Real.exp t) =
    -(deningerMeyerSum g (Real.exp t) +
      deningerMeyerSum (deningerMeyerEulerCLM g) (Real.exp t))
  have hne : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have hmap :=
    (deningerMeyerPositiveSumLM (Real.exp t) hne).map_neg
      (g + deningerMeyerEulerCLM g)
  rw [(deningerMeyerPositiveSumLM (Real.exp t) hne).map_add] at hmap
  simpa [deningerMeyerReflectedEulerCLM] using hmap

theorem hasDerivAt_deningerMeyerLogReflection
    (g : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (deningerMeyerLogReflection g)
      (deningerMeyerLogReflection
        (deningerMeyerReflectedEulerCLM g) t) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t :=
    hasDerivAt_neg t
  have hexpR :
      HasDerivAt (fun s : ℝ => Real.exp (-s))
        (-Real.exp (-t)) t := by
    have hraw :
        HasDerivAt
          (Real.exp ∘ fun s : ℝ => -s)
          (-Real.exp (-t)) t :=
      ((Real.hasDerivAt_exp (-t)).comp t hneg).congr_deriv
        (by simp)
    apply hraw.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hexpC :
      HasDerivAt (fun s : ℝ => (Real.exp (-s) : ℂ))
        (-Real.exp (-t) : ℂ) t := by
    simpa only [Complex.ofReal_neg] using hexpR.ofReal_comp
  have hlog :
      HasDerivAt
        (fun s : ℝ => deningerMeyerLogSum g (-s))
        (-deningerMeyerLogSum (deningerMeyerEulerCLM g) (-t)) t := by
    have h :=
      (hasDerivAt_deningerMeyerLogSum g (-t)).scomp t hneg
    have h' :
        HasDerivAt
          (deningerMeyerLogSum g ∘ fun s : ℝ => -s)
          (-deningerMeyerLogSum
            (deningerMeyerEulerCLM g) (-t)) t :=
      h.congr_deriv (by
        simp only [Complex.real_smul, Complex.ofReal_neg,
          Complex.ofReal_one, neg_mul, one_mul])
    apply h'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hmul := hexpC.mul hlog
  have hcoef :
      (-Real.exp (-t) : ℂ) *
          deningerMeyerLogSum g (-t) +
        (Real.exp (-t) : ℂ) *
          -deningerMeyerLogSum
            (deningerMeyerEulerCLM g) (-t) =
        (Real.exp (-t) : ℂ) *
          deningerMeyerLogSum
            (deningerMeyerReflectedEulerCLM g) (-t) := by
    rw [deningerMeyerLogSum_reflectedEuler]
    ring
  apply (hmul.congr_deriv hcoef).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem deriv_deningerMeyerLogReflection
    (g : SchwartzMap ℝ ℂ) :
    deriv (deningerMeyerLogReflection g) =
      deningerMeyerLogReflection
        (deningerMeyerReflectedEulerCLM g) := by
  funext t
  exact (hasDerivAt_deningerMeyerLogReflection g t).deriv

theorem iteratedDeriv_deningerMeyerLogReflection
    (g : SchwartzMap ℝ ℂ) (k : ℕ) :
    iteratedDeriv k (deningerMeyerLogReflection g) =
      deningerMeyerLogReflection
        (deningerMeyerReflectedEulerIterate k g) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih,
        deriv_deningerMeyerLogReflection,
        deningerMeyerReflectedEulerIterate_succ]

/--
Exact all-order differentiated Poisson reflection.  This is the identity that
supplies the negative log-end estimates without an unproved Euler invariance of
the full two-zero-mode source.
-/
theorem deningerMeyerEulerIterate_logSum_reflection
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (k : ℕ) (t : ℝ) :
    deningerMeyerLogSum (deningerMeyerEulerIterate k f) t =
      deningerMeyerLogReflection
        (deningerMeyerReflectedEulerIterate k
          (FourierTransform.fourierCLE ℂ
            (SchwartzMap ℝ ℂ) f)) t := by
  have hfun :
      deningerMeyerLogSum f =
        deningerMeyerLogReflection
          (FourierTransform.fourierCLE ℂ
            (SchwartzMap ℝ ℂ) f) := by
    funext s
    exact deningerMeyerLogSum_reflection f hf s
  calc
    deningerMeyerLogSum (deningerMeyerEulerIterate k f) t =
        iteratedDeriv k (deningerMeyerLogSum f) t := by
      rw [iteratedDeriv_deningerMeyerLogSum]
    _ = iteratedDeriv k
        (deningerMeyerLogReflection
          (FourierTransform.fourierCLE ℂ
            (SchwartzMap ℝ ℂ) f)) t := by
      rw [hfun]
    _ = deningerMeyerLogReflection
        (deningerMeyerReflectedEulerIterate k
          (FourierTransform.fourierCLE ℂ
            (SchwartzMap ℝ ℂ) f)) t := by
      rw [iteratedDeriv_deningerMeyerLogReflection]

/-! ## Uniform bounds for every logarithmic derivative -/

/--
Large-end bound under exactly the hypotheses used there: evenness and vanishing
of the physical zero mode.  No Fourier zero-mode hypothesis is needed.
-/
theorem deningerMeyerSum_large_bound_of_even_zero
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hf0 : f 0 = 0)
    (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖deningerMeyerSum f x‖ ≤
      ccmRationalArchimedeanDecayConstant f N /
        x ^ ccmRationalArchimedeanDecayExponent N := by
  have htrace :=
    deningerMeyerLatticeTrace_eq_two_sum
      f heven hf0 hx.ne'
  calc
    ‖deningerMeyerSum f x‖ ≤
        ‖ccmRationalArchimedeanLatticeTrace f x‖ := by
      rw [htrace, norm_mul]
      norm_num
      nlinarith [norm_nonneg (deningerMeyerSum f x)]
    _ ≤ ccmRationalArchimedeanDecayConstant f N /
          x ^ ccmRationalArchimedeanDecayExponent N :=
      ccmRationalArchimedeanLatticeTrace_large_bound
        f hf0 N hx

private theorem pow_mul_decay_two_le_factorial
    (k : ℕ) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) :
    s ^ k * (C / Real.exp s ^ 2) ≤
      (k.factorial : ℝ) * C := by
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hpoly :
      s ^ k ≤ (k.factorial : ℝ) * Real.exp s := by
    have h := Real.pow_div_factorial_le_exp s hs k
    have h' := (div_le_iff₀ hfac).mp h
    nlinarith
  have hepos : 0 < Real.exp s := Real.exp_pos s
  have heone : 1 ≤ Real.exp s := Real.one_le_exp hs
  rw [show s ^ k * (C / Real.exp s ^ 2) =
      (s ^ k * C) / Real.exp s ^ 2 by ring]
  apply (div_le_iff₀ (sq_pos_of_pos hepos)).2
  calc
    s ^ k * C ≤
        ((k.factorial : ℝ) * Real.exp s) * C := by
      exact mul_le_mul_of_nonneg_right hpoly hC
    _ ≤ ((k.factorial : ℝ) * C) * Real.exp s ^ 2 := by
      have hepow : Real.exp s ≤ Real.exp s ^ 2 := by
        nlinarith [Real.exp_pos s]
      have hfacC :
          0 ≤ (k.factorial : ℝ) * C := by positivity
      calc
        ((k.factorial : ℝ) * Real.exp s) * C =
            ((k.factorial : ℝ) * C) * Real.exp s := by ring
        _ ≤ ((k.factorial : ℝ) * C) * Real.exp s ^ 2 :=
          mul_le_mul_of_nonneg_left hepow hfacC
    _ = (k.factorial : ℝ) * C * Real.exp s ^ 2 := by ring

private theorem pow_mul_reflected_decay_two_le_factorial
    (k : ℕ) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) :
    s ^ k *
        (Real.exp s * (C / Real.exp s ^ 2)) ≤
      (k.factorial : ℝ) * C := by
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hpoly :
      s ^ k ≤ (k.factorial : ℝ) * Real.exp s := by
    have h := Real.pow_div_factorial_le_exp s hs k
    have h' := (div_le_iff₀ hfac).mp h
    nlinarith
  have hepos : 0 < Real.exp s := Real.exp_pos s
  rw [show Real.exp s * (C / Real.exp s ^ 2) =
      C / Real.exp s by
        field_simp]
  rw [show s ^ k * (C / Real.exp s) =
      (s ^ k * C) / Real.exp s by ring]
  apply (div_le_iff₀ hepos).2
  calc
    s ^ k * C ≤
        ((k.factorial : ℝ) * Real.exp s) * C :=
      mul_le_mul_of_nonneg_right hpoly hC
    _ = (k.factorial : ℝ) * C * Real.exp s := by ring

/-- Positive-log-end weighted bound for one Euler derivative. -/
theorem deningerMeyerEulerLogSum_nonneg_bound
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hf0 : f 0 = 0)
    (k n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖t‖ ^ k *
        ‖deningerMeyerLogSum
          (deningerMeyerEulerIterate n f) t‖ ≤
      (k.factorial : ℝ) *
        ccmRationalArchimedeanDecayConstant
          (deningerMeyerEulerIterate n f) 0 := by
  let g := deningerMeyerEulerIterate n f
  let C := ccmRationalArchimedeanDecayConstant g 0
  have hgz := deningerMeyerEulerIterate_even_zero
    f heven hf0 n
  have hlarge :=
    deningerMeyerSum_large_bound_of_even_zero
      g hgz.1 hgz.2 0 (Real.exp_pos t)
  have hlarge' :
      ‖deningerMeyerLogSum g t‖ ≤
        C / Real.exp t ^ 2 := by
    simpa [deningerMeyerLogSum, C,
      ccmRationalArchimedeanDecayExponent] using hlarge
  have hC : 0 ≤ C :=
    ccmRationalArchimedeanDecayConstant_nonneg g 0
  rw [Real.norm_eq_abs, abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left hlarge'
      (pow_nonneg ht k)).trans
    (pow_mul_decay_two_le_factorial k ht hC)

/-- Negative-log-end weighted bound obtained from differentiated Poisson
reflection and a large-end estimate for the reflected Euler iterate. -/
theorem deningerMeyerEulerLogSum_nonpos_bound
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (k n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    ‖t‖ ^ k *
        ‖deningerMeyerLogSum
          (deningerMeyerEulerIterate n f) t‖ ≤
      (k.factorial : ℝ) *
        ccmRationalArchimedeanDecayConstant
          (deningerMeyerReflectedEulerIterate n
            (FourierTransform.fourierCLE ℂ
              (SchwartzMap ℝ ℂ) f)) 0 := by
  let Ff :=
    FourierTransform.fourierCLE ℂ
      (SchwartzMap ℝ ℂ) f
  let g := deningerMeyerReflectedEulerIterate n Ff
  let C := ccmRationalArchimedeanDecayConstant g 0
  obtain ⟨heven, _, hF0⟩ :=
    (deningerMeyerCap_mem_iff f).mp hf
  have hFeven := deningerFourier_even_of_even f heven
  have hgz :=
    deningerMeyerReflectedEulerIterate_even_zero
      Ff hFeven hF0 n
  have hs : 0 ≤ -t := neg_nonneg.mpr ht
  have hlarge :=
    deningerMeyerSum_large_bound_of_even_zero
      g hgz.1 hgz.2 0 (Real.exp_pos (-t))
  have hlarge' :
      ‖deningerMeyerLogSum g (-t)‖ ≤
        C / Real.exp (-t) ^ 2 := by
    simpa [deningerMeyerLogSum, C,
      ccmRationalArchimedeanDecayExponent] using hlarge
  have href :=
    deningerMeyerEulerIterate_logSum_reflection
      f hf n t
  have href' :
      deningerMeyerLogSum
          (deningerMeyerEulerIterate n f) t =
        (Real.exp (-t) : ℂ) *
          deningerMeyerLogSum g (-t) := by
    simpa [deningerMeyerLogReflection, g, Ff] using href
  have hnorm :
      ‖deningerMeyerLogSum
          (deningerMeyerEulerIterate n f) t‖ ≤
        Real.exp (-t) *
          (C / Real.exp (-t) ^ 2) := by
    rw [href', norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (-t))]
    exact mul_le_mul_of_nonneg_left hlarge'
      (Real.exp_pos (-t)).le
  have hC : 0 ≤ C :=
    ccmRationalArchimedeanDecayConstant_nonneg g 0
  rw [Real.norm_eq_abs, abs_of_nonpos ht]
  exact (mul_le_mul_of_nonneg_left hnorm
      (pow_nonneg hs k)).trans
    (pow_mul_reflected_decay_two_le_factorial
      k hs hC)

/--
One explicit global bound for every defining Schwartz seminorm of the
log-radius Poisson sum.
-/
theorem deningerMeyerLogSum_schwartz_bound
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (k n : ℕ) (t : ℝ) :
    ‖t‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (deningerMeyerLogSum f) t‖ ≤
      (k.factorial : ℝ) *
        (ccmRationalArchimedeanDecayConstant
            (deningerMeyerEulerIterate n f) 0 +
          ccmRationalArchimedeanDecayConstant
            (deningerMeyerReflectedEulerIterate n
              (FourierTransform.fourierCLE ℂ
                (SchwartzMap ℝ ℂ) f)) 0) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_deningerMeyerLogSum]
  obtain ⟨heven, hf0, _⟩ :=
    (deningerMeyerCap_mem_iff f).mp hf
  have hCpos :
      0 ≤ ccmRationalArchimedeanDecayConstant
        (deningerMeyerEulerIterate n f) 0 :=
    ccmRationalArchimedeanDecayConstant_nonneg _ _
  have hCneg :
      0 ≤ ccmRationalArchimedeanDecayConstant
        (deningerMeyerReflectedEulerIterate n
          (FourierTransform.fourierCLE ℂ
            (SchwartzMap ℝ ℂ) f)) 0 :=
    ccmRationalArchimedeanDecayConstant_nonneg _ _
  by_cases ht : 0 ≤ t
  · exact
      (deningerMeyerEulerLogSum_nonneg_bound
        f heven hf0 k n ht).trans
        (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right hCneg)
          (by positivity))
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    exact
      (deningerMeyerEulerLogSum_nonpos_bound
        f hf k n ht').trans
        (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hCpos)
          (by positivity))

/-! ## Ordinary log-Schwartz corollary -/

/--
The Poisson sum of one Meyer source, bundled in ordinary log-Schwartz space.
This is a necessary corollary of the all-weight result below, not the full
multiplicative Bruhat--Schwartz target.
-/
def deningerMeyerLogSchwartz
    (f : DeningerMeyerCap) : SchwartzMap ℝ ℂ where
  toFun := deningerMeyerLogSum f
  smooth' := contDiff_deningerMeyerLogSum f
  decay' k n :=
    ⟨(k.factorial : ℝ) *
        (ccmRationalArchimedeanDecayConstant
            (deningerMeyerEulerIterate n f) 0 +
          ccmRationalArchimedeanDecayConstant
            (deningerMeyerReflectedEulerIterate n
              (FourierTransform.fourierCLE ℂ
                (SchwartzMap ℝ ℂ) f)) 0),
      deningerMeyerLogSum_schwartz_bound f f.property k n⟩

@[simp]
theorem deningerMeyerLogSchwartz_apply
    (f : DeningerMeyerCap) (t : ℝ) :
    deningerMeyerLogSchwartz f t =
      deningerMeyerSum f (Real.exp t) :=
  rfl

/-- Radial Meyer--Poisson operator into the ordinary log-Schwartz corollary. -/
def deningerMeyerLogSchwartzLM :
    DeningerMeyerCap →ₗ[ℂ] SchwartzMap ℝ ℂ where
  toFun := deningerMeyerLogSchwartz
  map_add' f g := by
    ext t
    change deningerMeyerSum (↑(f + g) : SchwartzMap ℝ ℂ)
        (Real.exp t) =
      deningerMeyerSum f (Real.exp t) +
        deningerMeyerSum g (Real.exp t)
    exact
      (deningerMeyerPositiveSumLM
        (Real.exp t) (Real.exp_ne_zero t)).map_add f g
  map_smul' c f := by
    ext t
    change deningerMeyerSum (↑(c • f) : SchwartzMap ℝ ℂ)
        (Real.exp t) =
      c • deningerMeyerSum f (Real.exp t)
    exact
      (deningerMeyerPositiveSumLM
        (Real.exp t) (Real.exp_ne_zero t)).map_smul c f

@[simp]
theorem deningerMeyerLogSchwartzLM_apply
    (f : DeningerMeyerCap) (t : ℝ) :
    deningerMeyerLogSchwartzLM f t =
      deningerMeyerSum f (Real.exp t) :=
  rfl

/-! ## Full multiplicative Schwartz decay (all exponential weights) -/

/--
Arbitrary multiplicative-power large-end decay under evenness and the physical
zero mode alone.
-/
theorem deningerMeyerSum_isBigO_atTop_of_even_zero
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hf0 : f 0 = 0) (a : ℝ) :
    deningerMeyerSum f =O[atTop]
      fun x : ℝ => x ^ (-a) := by
  let N : ℕ := ⌈max a 0⌉₊
  let p : ℕ := ccmRationalArchimedeanDecayExponent N
  let C : ℝ := ccmRationalArchimedeanDecayConstant f N
  have hC : 0 ≤ C :=
    ccmRationalArchimedeanDecayConstant_nonneg f N
  have hap : a ≤ (p : ℝ) := by
    have hceil : max a 0 ≤ (N : ℝ) := Nat.le_ceil _
    have hNp : (N : ℝ) ≤ (p : ℝ) := by
      have hnat :
          N ≤ ccmRationalArchimedeanDecayExponent N := by
        simp [ccmRationalArchimedeanDecayExponent]
        omega
      exact_mod_cast hnat
    exact (le_max_left a 0).trans (hceil.trans hNp)
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := one_pos.trans_le hx
  have hlarge :=
    deningerMeyerSum_large_bound_of_even_zero
      f heven hf0 N hxpos
  have hlarge' :
      ‖deningerMeyerSum f x‖ ≤ C / x ^ p := by
    simpa [C, p] using hlarge
  have hrpow :
      x ^ (-(p : ℝ)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hap)
  have hrewrite :
      C / x ^ p = C * x ^ (-(p : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_neg hxpos.le]
  rw [show ‖x ^ (-a)‖ = x ^ (-a) by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]]
  exact hlarge'.trans_eq hrewrite |>.trans
    (mul_le_mul_of_nonneg_left hrpow hC)

theorem deningerMeyerLogSum_isBigO_atTop_power_of_even_zero
    (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hf0 : f 0 = 0) (a : ℝ) :
    deningerMeyerLogSum f =O[atTop]
      fun t : ℝ => Real.exp t ^ (-a) := by
  have hcomp :=
    (deningerMeyerSum_isBigO_atTop_of_even_zero
      f heven hf0 a).comp_tendsto
        Real.tendsto_exp_atTop
  apply hcomp.congr'
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- Every Euler derivative has arbitrary exponential decay at the positive
logarithmic end. -/
theorem iteratedDeriv_deningerMeyerLogSum_isBigO_atTop_power
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (n : ℕ) (a : ℝ) :
    iteratedDeriv n (deningerMeyerLogSum f) =O[atTop]
      fun t : ℝ => Real.exp t ^ (-a) := by
  obtain ⟨heven, hf0, _⟩ :=
    (deningerMeyerCap_mem_iff f).mp hf
  rw [iteratedDeriv_deningerMeyerLogSum]
  have hgz :=
    deningerMeyerEulerIterate_even_zero
      f heven hf0 n
  exact
    deningerMeyerLogSum_isBigO_atTop_power_of_even_zero
      (deningerMeyerEulerIterate n f)
      hgz.1 hgz.2 a

/-- Every Euler derivative has arbitrary exponential decay at the negative
logarithmic end, by differentiated Poisson reflection. -/
theorem iteratedDeriv_deningerMeyerLogSum_isBigO_atBot_power
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap)
    (n : ℕ) (b : ℝ) :
    iteratedDeriv n (deningerMeyerLogSum f) =O[atBot]
      fun t : ℝ => Real.exp t ^ b := by
  let N : ℕ := ⌈max (b + 1) 0⌉₊
  let p : ℕ := ccmRationalArchimedeanDecayExponent N
  let q : ℕ := p - 1
  let Ff :=
    FourierTransform.fourierCLE ℂ
      (SchwartzMap ℝ ℂ) f
  let g := deningerMeyerReflectedEulerIterate n Ff
  let C := ccmRationalArchimedeanDecayConstant g N
  have hpgt : 1 < p := by
    exact ccmRationalArchimedeanDecayExponent_gt_one N
  have hpq : p = q + 1 := by
    dsimp [q]
    omega
  have hbq : b ≤ (q : ℝ) := by
    have hceil :
        max (b + 1) 0 ≤ (N : ℝ) := Nat.le_ceil _
    have hNq : (N : ℝ) ≤ (q : ℝ) := by
      have hnat :
          N ≤ ccmRationalArchimedeanDecayExponent N - 1 := by
        simp [ccmRationalArchimedeanDecayExponent]
        omega
      exact_mod_cast hnat
    linarith [le_max_left (b + 1) 0,
      hceil.trans hNq]
  obtain ⟨heven, _, hF0⟩ :=
    (deningerMeyerCap_mem_iff f).mp hf
  have hFeven := deningerFourier_even_of_even f heven
  have hgz :=
    deningerMeyerReflectedEulerIterate_even_zero
      Ff hFeven hF0 n
  have hC : 0 ≤ C :=
    ccmRationalArchimedeanDecayConstant_nonneg g N
  rw [iteratedDeriv_deningerMeyerLogSum]
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  have hlarge :=
    deningerMeyerSum_large_bound_of_even_zero
      g hgz.1 hgz.2 N (Real.exp_pos (-t))
  have hlarge' :
      ‖deningerMeyerLogSum g (-t)‖ ≤
        C / Real.exp (-t) ^ p := by
    simpa [deningerMeyerLogSum, C, p] using hlarge
  have href :=
    deningerMeyerEulerIterate_logSum_reflection
      f hf n t
  have href' :
      deningerMeyerLogSum
          (deningerMeyerEulerIterate n f) t =
        (Real.exp (-t) : ℂ) *
          deningerMeyerLogSum g (-t) := by
    simpa [deningerMeyerLogReflection, g, Ff] using href
  have hraw :
      ‖deningerMeyerLogSum
          (deningerMeyerEulerIterate n f) t‖ ≤
        Real.exp (-t) *
          (C / Real.exp (-t) ^ p) := by
    rw [href', norm_mul, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (-t))]
    exact mul_le_mul_of_nonneg_left hlarge'
      (Real.exp_pos (-t)).le
  have heq :
      Real.exp (-t) *
          (C / Real.exp (-t) ^ p) =
        C * Real.exp t ^ q := by
    rw [Real.exp_neg, hpq, pow_succ]
    field_simp [Real.exp_ne_zero]
    rw [one_div, inv_pow, mul_assoc,
      inv_mul_cancel₀
        (pow_ne_zero q (Real.exp_ne_zero t)),
      mul_one]
  have hpow :
      Real.exp t ^ q ≤ Real.exp t ^ b := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge
      (Real.exp_pos t) (Real.exp_le_one_iff.mpr ht) hbq
  rw [show ‖Real.exp t ^ b‖ =
      Real.exp t ^ b by
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (Real.rpow_nonneg (Real.exp_pos t).le b)]]
  exact hraw.trans_eq heq |>.trans
    (mul_le_mul_of_nonneg_left hpow hC)

/--
Underlying all-weight multiplicative Schwartz condition in log radius.  This is
strictly stronger than ordinary additive Schwartz decay: every derivative
decays faster than every exponential at both ends.
-/
structure DeningerMeyerStrongLogDecay (h : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ h
  decayTop : ∀ (n : ℕ) (a : ℝ),
    iteratedDeriv n h =O[atTop]
      fun t : ℝ => Real.exp t ^ (-a)
  decayBot : ∀ (n : ℕ) (b : ℝ),
    iteratedDeriv n h =O[atBot]
      fun t : ℝ => Real.exp t ^ b

/-- Full, all-derivative, all-weight Meyer landing. -/
theorem deningerMeyerLogSum_strongLogDecay
    (f : SchwartzMap ℝ ℂ) (hf : f ∈ DeningerMeyerCap) :
    DeningerMeyerStrongLogDecay
      (deningerMeyerLogSum f) where
  smooth := contDiff_deningerMeyerLogSum f
  decayTop :=
    iteratedDeriv_deningerMeyerLogSum_isBigO_atTop_power
      f hf
  decayBot :=
    iteratedDeriv_deningerMeyerLogSum_isBigO_atBot_power
      f hf

end

end RHTower
