import GaloisForLFunctions.RHTower.DeningerExpAverage
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The linear flow on the unit torus and its character averages

The linear flow `t ↦ (t λ_i)_i` on the `d`-dimensional unit torus turns each exponential monomial
into a one-frequency oscillation: the character `n` becomes `exp (2π i ⟨n, λ⟩ t)`.  Hence its time
average over `[0, T]` is the elementary exponential average, which vanishes as `T → ∞` exactly
when the frequency `⟨n, λ⟩` is nonzero.

* `deningerTorusFlow` : the linear flow.
* `deningerFrequency` : the frequency `⟨n, λ⟩` of a character along the flow.
* `deningerMFourier_flow` : the character along the flow is a one-frequency oscillation.
* `deningerFlowAverage_mFourier_tendsto` : nonzero frequencies have vanishing mean.
* `deningerFlowAverage_mFourier_zero_freq` : the trivial character has mean one.
-/

namespace RHTower

open UnitAddTorus Filter Topology

section TorusFlow

variable {d : Type*} [Fintype d]

/-- The linear flow on the unit torus with velocity vector `lam`. -/
def deningerTorusFlow (lam : d → ℝ) (t : ℝ) : UnitAddTorus d :=
  fun i => ((t * lam i : ℝ) : AddCircle (1 : ℝ))

omit [Fintype d] in
theorem deningerTorusFlow_continuous (lam : d → ℝ) : Continuous (deningerTorusFlow lam) := by
  refine continuous_pi fun i => ?_
  exact continuous_quotient_mk'.comp (continuous_id.mul continuous_const)

/-- The frequency of the character `n` along the flow with velocity `lam`. -/
def deningerFrequency (n : d → ℤ) (lam : d → ℝ) : ℝ := ∑ i, (n i : ℝ) * lam i

@[simp] theorem deningerFrequency_zero (lam : d → ℝ) :
    deningerFrequency (0 : d → ℤ) lam = 0 := by
  simp [deningerFrequency]

/-- **A character along the linear flow is a one-frequency oscillation.**  Each factor of the
monomial contributes its own exponential, and the exponents add up to `2π ⟨n, λ⟩ t`. -/
theorem deningerMFourier_flow (n : d → ℤ) (lam : d → ℝ) (t : ℝ) :
    mFourier n (deningerTorusFlow lam t)
      = Complex.exp ((2 * Real.pi * deningerFrequency n lam * t : ℝ) * Complex.I) := by
  have key : ∑ i : d, 2 * Real.pi * (n i : ℝ) * (t * lam i)
      = 2 * Real.pi * deningerFrequency n lam * t := by
    rw [deningerFrequency, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ i : d, fourier (n i) (deningerTorusFlow lam t i)
      = Complex.exp (((2 * Real.pi * (n i : ℝ) * (t * lam i) : ℝ) : ℂ) * Complex.I) := by
    intro i
    show fourier (n i) (((t * lam i : ℝ) : AddCircle (1 : ℝ))) = _
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  show ∏ i : d, fourier (n i) (deningerTorusFlow lam t i) = _
  rw [Finset.prod_congr rfl fun i _ => hterm i, ← Complex.exp_sum, ← Finset.sum_mul,
    ← Complex.ofReal_sum, key]

/-- The time average of a continuous function along the flow. -/
noncomputable def deningerFlowAverage (lam : d → ℝ) (f : C(UnitAddTorus d, ℂ)) (T : ℝ) : ℂ :=
  (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, f (deningerTorusFlow lam t)

/-- The flow average of a character is the elementary exponential average at its frequency. -/
theorem deningerFlowAverage_mFourier (n : d → ℤ) (lam : d → ℝ) (T : ℝ) :
    deningerFlowAverage lam (mFourier n) T
      = deningerExpAverage (2 * Real.pi * deningerFrequency n lam) T := by
  rw [deningerFlowAverage, deningerExpAverage]
  congr 1
  exact intervalIntegral.integral_congr fun t _ => deningerMFourier_flow n lam t

/-- **A character with nonzero frequency has vanishing mean along the flow.** -/
theorem deningerFlowAverage_mFourier_tendsto (n : d → ℤ) (lam : d → ℝ)
    (hn : deningerFrequency n lam ≠ 0) :
    Tendsto (deningerFlowAverage lam (mFourier n)) atTop (nhds 0) := by
  have ha : 2 * Real.pi * deningerFrequency n lam ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hn
  have hfun : deningerFlowAverage lam (mFourier n)
      = deningerExpAverage (2 * Real.pi * deningerFrequency n lam) :=
    funext fun T => deningerFlowAverage_mFourier n lam T
  rw [hfun]
  exact deningerExpAverage_tendsto_zero ha

/-- **The trivial character has mean one.** -/
theorem deningerFlowAverage_mFourier_zero_freq (lam : d → ℝ) {T : ℝ} (hT : T ≠ 0) :
    deningerFlowAverage lam (mFourier (0 : d → ℤ)) T = 1 := by
  have hone : ∀ t : ℝ, (mFourier (0 : d → ℤ)) (deningerTorusFlow lam t) = 1 := by
    intro t
    rw [mFourier_zero]
    rfl
  rw [deningerFlowAverage, intervalIntegral.integral_congr fun t _ => hone t]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hT)

end TorusFlow

end RHTower
