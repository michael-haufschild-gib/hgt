import GaloisForLFunctions.RHTower.XiSliceRealAxisGrowth
import GaloisForLFunctions.RHTower.XiHorizontalAbsoluteMonotonicityStrip
import GaloisForLFunctions.RHTower.XiHorizontalAbsoluteMonotonicityWindow

/-!
# The slice on the real axis right of the critical strip: growth and absolute monotonicity

Let `S(t, y) = |ξ(½+y+it)|²` for real `y` (`xiSliceReal`).

* **Growth at rate `log t`** (`xiSliceReal_growth_euler`).  For `η > 0`, `t ≥ 8` and
  `½ + η ≤ y₁ ≤ y₂ ≤ t/2`,

    `S(y₁) e^{(log(t/2) − 2C_η)(y₂−y₁)} ≤ S(y₂) ≤ S(y₁) e^{(log t + 2C_η)(y₂−y₁)}`,

  because `∂_y log S(t, y) = Re L(½+y+it)` lies in `[log(t/2) − 2C_η, log t + 2C_η]` there
  (`xiSliceLogDeriv_real_bounds_euler`).  This extends `xiSliceReal_growth` from `y ≥ 1` to the whole
  half-line `y ≥ ½ + η`.
* **Absolute monotonicity propagates to the right** (`iteratedDeriv_xiSliceProduct_nonneg_of_le`).
  If every Taylor coefficient of the slice at `x₀` is nonnegative, so is every derivative at every
  real `x ≥ x₀`: `S^{(n)}(x) = Σ_k (x − x₀)^k/k! · S^{(n+k)}(x₀)`.  With the unconditional
  absolute monotonicity at `x₀ = ½` (`horizontalAbsMono_half`), every derivative of the slice is
  nonnegative on `[½, ∞)` at every height (`iteratedDeriv_xiSliceProduct_nonneg_of_half_le`).
-/

open Complex
open scoped ComplexOrder Nat

namespace RHTower

noncomputable section

/-- **Growth of the real slice at rate `log t`** on `y ≥ ½ + η`. -/
theorem xiSliceReal_growth_euler {t η : ℝ} (hη : 0 < η) (ht : 8 ≤ t) {y₁ y₂ : ℝ}
    (h1 : 1 / 2 + η ≤ y₁) (h12 : y₁ ≤ y₂) (h2 : y₂ ≤ t / 2) :
    xiSliceReal t y₁ * Real.exp ((Real.log (t / 2) - 2 * xiEulerConstant η) * (y₂ - y₁))
        ≤ xiSliceReal t y₂ ∧
      xiSliceReal t y₂ ≤
        xiSliceReal t y₁ * Real.exp ((Real.log t + 2 * xiEulerConstant η) * (y₂ - y₁)) := by
  set D : Set ℝ := Set.Icc (1 / 2 + η) (t / 2) with hD
  set g : ℝ → ℝ := fun y => Real.log (xiSliceReal t y) with hg
  have hpos : ∀ y ∈ D, 0 < xiSliceReal t y := fun y hy => xiSliceReal_pos t (by linarith [hy.1])
  have hgder : ∀ y ∈ D, HasDerivAt g (xiSliceLogDeriv t y).re y := by
    intro y hy
    have h := (hasDerivAt_xiSliceReal t (by linarith [hy.1] : (1 : ℝ) / 2 < y)).log
      (hpos y hy).ne'
    convert h using 1
    field_simp [(hpos y hy).ne']
  have hcont : ContinuousOn g D := fun y hy => (hgder y hy).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior D) := fun y hy =>
    (hgder y (interior_subset hy)).differentiableAt.differentiableWithinAt
  have hbounds : ∀ y ∈ interior D,
      Real.log (t / 2) - 2 * xiEulerConstant η ≤ deriv g y ∧
        deriv g y ≤ Real.log t + 2 * xiEulerConstant η := by
    intro y hy
    have hyD := interior_subset hy
    rw [(hgder y hyD).deriv]
    obtain ⟨-, hlo, hhi⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := y) (η := η)
      hη ht hyD.1 hyD.2
    exact ⟨hlo, hhi⟩
  have hy₁ : y₁ ∈ D := ⟨h1, by linarith⟩
  have hy₂ : y₂ ∈ D := ⟨by linarith, h2⟩
  have hlow := (convex_Icc (1 / 2 + η) (t / 2)).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun y hy => (hbounds y hy).1) y₁ hy₁ y₂ hy₂ h12
  have hup := (convex_Icc (1 / 2 + η) (t / 2)).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun y hy => (hbounds y hy).2) y₁ hy₁ y₂ hy₂ h12
  simp only [hg] at hlow hup
  have hp1 := hpos y₁ hy₁
  have hp2 := hpos y₂ hy₂
  constructor
  · rw [← Real.exp_log hp1, ← Real.exp_log hp2, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_log hp1, ← Real.exp_log hp2, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

/-- **Taylor shift between real centres.**  `S^{(n)}(x) = Σ_k (x − x₀)^k/k! · S^{(n+k)}(x₀)`. -/
theorem hasSum_iteratedDeriv_xiSliceProduct_shift (t : ℝ) (n : ℕ) (x₀ x : ℂ) :
    HasSum (fun k : ℕ => ((k ! : ℂ))⁻¹ * ((x - x₀) ^ k
        * iteratedDeriv (n + k) (xiSliceProduct t) x₀))
      (iteratedDeriv n (xiSliceProduct t) x) := by
  have hG : Differentiable ℂ (iteratedDeriv n (xiSliceProduct t)) :=
    ((differentiable_xiSliceProduct t).contDiff (n := ⊤)).differentiable_iteratedDeriv n
      (WithTop.coe_lt_top _)
  have h := Complex.hasSum_taylorSeries_of_entire hG x₀ x
  simp only [smul_eq_mul, iteratedDeriv_iteratedDeriv_comm] at h
  exact h

/-- **Absolute monotonicity propagates to the right.**  If every Taylor coefficient of the slice at
the real point `x₀` is nonnegative, so is every derivative at every real `x ≥ x₀`. -/
theorem iteratedDeriv_xiSliceProduct_nonneg_of_le {t x₀ x : ℝ} (h : XiHorizontalAbsMono x₀ t)
    (hx : x₀ ≤ x) (n : ℕ) : 0 ≤ iteratedDeriv n (xiSliceProduct t) (x : ℂ) := by
  have hS := hasSum_iteratedDeriv_xiSliceProduct_shift t n (x₀ : ℂ) (x : ℂ)
  set T : ℕ → ℂ := fun k => ((k ! : ℂ))⁻¹ * (((x : ℂ) - x₀) ^ k
    * iteratedDeriv (n + k) (xiSliceProduct t) (x₀ : ℂ)) with hT
  have hterm : ∀ k, 0 ≤ T k := by
    intro k
    have h1 : (0 : ℂ) ≤ ((k ! : ℂ))⁻¹ := by
      rw [show ((k ! : ℂ))⁻¹ = ((((k ! : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.zero_le_real.mpr (by positivity)
    have h2 : (0 : ℂ) ≤ ((x : ℂ) - x₀) ^ k := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (pow_nonneg (by linarith) k)
    exact mul_nonneg h1 (mul_nonneg h2 (h (n + k)))
  have hre : HasSum (fun k => (T k).re) (iteratedDeriv n (xiSliceProduct t) (x : ℂ)).re := by
    have := hS.mapL Complex.reCLM
    simpa using this
  have him : HasSum (fun k => (T k).im) (iteratedDeriv n (xiSliceProduct t) (x : ℂ)).im := by
    have := hS.mapL Complex.imCLM
    simpa using this
  have himz : ∀ k, (T k).im = 0 := fun k => (Complex.nonneg_iff.mp (hterm k)).2.symm
  rw [show (fun k => (T k).im) = fun _ => (0 : ℝ) from funext himz] at him
  refine Complex.nonneg_iff.mpr ⟨hre.nonneg fun k => (Complex.nonneg_iff.mp (hterm k)).1, ?_⟩
  exact (him.unique hasSum_zero).symm

/-- **Every derivative of the slice is nonnegative on `[½, ∞)`**, at every height. -/
theorem iteratedDeriv_xiSliceProduct_nonneg_of_half_le (t : ℝ) {x : ℝ} (hx : 1 / 2 ≤ x) (n : ℕ) :
    0 ≤ iteratedDeriv n (xiSliceProduct t) (x : ℂ) :=
  iteratedDeriv_xiSliceProduct_nonneg_of_le (horizontalAbsMono_half t) hx n

end

end RHTower
