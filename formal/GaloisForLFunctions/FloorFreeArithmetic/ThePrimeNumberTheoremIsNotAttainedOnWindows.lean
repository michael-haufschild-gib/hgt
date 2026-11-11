import GaloisForLFunctions.FloorFreeArithmetic.FiniteTopLayersAreSeenOnEveryWindow
import GaloisForLFunctions.ZeroConfigurationGeometry.TheOneOffsAreFiniteOscillationsOfThePrimeError

/-!
# The prime number theorem is not attained on windows

If the asymptotic abscissa law fails, the error of the prime number theorem is a finite
oscillation `ψ(x) − x = x^β T(log x) + O(x^{β−η})` with `T` a nonzero real trigonometric
polynomial. A nonzero trigonometric polynomial is bounded away from zero somewhere on every
window, so the error attains its own rate `x^β` on **every** multiplicative window `[x, λx]`,
`λ > 1`, beyond some point.

Contrapositively the law follows from non-attainment: whenever `ψ(x) − x = O(x^β)` with
`β > ½`, it suffices that the error is `o(x^β)` uniformly on arbitrarily late windows of one
ratio. The statement compares the error with its own rate and involves no exponent below it.

* `exists_pos_forall_window_le_abs_finiteOscillation`: the window bound for `T`.
* `psi_attained_on_every_window_of_not_asymptoticAbscissaLaw`: uniform attainment.
* `asymptoticAbscissaLaw_of_psi_window_nonAttainment`: the receiver.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open ZeroConfigurationGeometry

/-- A real trigonometric polynomial that is not identically zero is at least `ε > 0` in absolute
value somewhere on every window `[T, T + L]`, `T ≥ 0`. -/
theorem exists_pos_forall_window_le_abs_finiteOscillation {S : Finset ℝ} {c : ℝ → ℂ} {u₁ : ℝ}
    (hne : finiteOscillation S c u₁ ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ, 0 ≤ T →
      ∃ u ∈ Icc T (T + L), ε ≤ |finiteOscillation S c u| := by
  classical
  obtain ⟨μ₀, hμ₀, hd⟩ := exists_oscillationCoeff_ne_zero hne
  have hcoef : (fun μ : oscillationFrequencies S => oscillationCoeff S c μ) ≠ 0 :=
    fun h0 => hd (congrFun h0 ⟨μ₀, hμ₀⟩)
  obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_norm_realExpSum
    (fun μ : oscillationFrequencies S => (μ : ℝ)) Subtype.val_injective _ hcoef hL
  refine ⟨ε, hε, fun T hT => ?_⟩
  obtain ⟨u, hu, hbig⟩ := hwin T hT
  refine ⟨u, hu, ?_⟩
  have hn : |finiteOscillation S c u| = ‖((finiteOscillation S c u : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn, finiteOscillation_eq_sum, ← Finset.sum_coe_sort (oscillationFrequencies S)
    (fun μ => oscillationCoeff S c μ * cexp (I * μ * u))]
  refine hbig.trans (le_of_eq ?_)
  refine congrArg _ (Finset.sum_congr rfl fun μ _ => ?_)
  congr 2
  push_cast
  ring

/-- A real trigonometric polynomial is bounded by the sum of the moduli of its coefficients. -/
theorem abs_finiteOscillation_le (S : Finset ℝ) (c : ℝ → ℂ) (u : ℝ) :
    |finiteOscillation S c u| ≤ ∑ ω ∈ S, ‖c ω‖ := by
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun ω _ => ?_
  have harg : I * (ω : ℂ) * (u : ℂ) = ((ω * u : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [norm_mul, harg, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Uniform attainment for `ψ`.** If the abscissa law fails, there is `β > ½` with
`ψ(x) − x = O(x^β)` such that for every `L > 0` the error exceeds `δ e^{βu}` in absolute value
at some `u` of every late window `[T, T + L]`. -/
theorem psi_attained_on_every_window_of_not_asymptoticAbscissaLaw
    (hnot : ¬ _root_.RHTower.AsymptoticAbscissaLaw) :
    ∃ β : ℝ, 1 / 2 < β ∧
      (∃ C x₀ : ℝ, ∀ x, x₀ ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ β) ∧
      ∀ L : ℝ, 0 < L → ∃ δ U₀ : ℝ, 0 < δ ∧ ∀ T : ℝ, U₀ ≤ T → ∃ u ∈ Icc T (T + L),
        δ * Real.exp (β * u) ≤ |Chebyshev.psi (Real.exp u) - Real.exp u| := by
  obtain ⟨β, η, hβ, hη, S, c, ⟨u₁, hu₁⟩, C, x₀, hC⟩ :=
    primeErrorIsFiniteOscillation_of_not_asymptoticAbscissaLaw hnot
  set B : ℝ := ∑ ω ∈ S, ‖c ω‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun ω _ => norm_nonneg _
  refine ⟨β, hβ, ⟨|C| + B, max x₀ 1, fun x hx => ?_⟩, fun L hL => ?_⟩
  · -- the error is `O(x^β)`
    have hx1 : (1 : ℝ) ≤ x := (le_max_right x₀ 1).trans hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
    have hxβ : 0 < x ^ β := Real.rpow_pos_of_pos hx0 β
    have hmono : x ^ (β - η) ≤ x ^ β :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hη])
    have h1 := hC x ((le_max_left x₀ 1).trans hx)
    have h2 : |x ^ β * finiteOscillation S c (Real.log x)| ≤ B * x ^ β := by
      rw [abs_mul, abs_of_pos hxβ, mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_finiteOscillation_le S c _) hxβ.le
    have h3 : C * x ^ (β - η) ≤ |C| * x ^ β :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)).trans
        (mul_le_mul_of_nonneg_left hmono (abs_nonneg C))
    have h4 : |Chebyshev.psi x - x| ≤
        |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| +
          |x ^ β * finiteOscillation S c (Real.log x)| := by
      have := abs_add_le (Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x))
        (x ^ β * finiteOscillation S c (Real.log x))
      simpa only [sub_add_cancel] using this
    linarith only [h1, h2, h3, h4, add_mul |C| B (x ^ β)]
  · -- attainment on every window
    obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_abs_finiteOscillation hu₁ hL
    have hlim : Tendsto (fun u : ℝ => |C| * Real.exp (-(η * u))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun u : ℝ => Real.exp (-(η * u))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hη))
      simpa only [mul_zero] using h0.const_mul |C|
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp
      ((hlim.eventually (gt_mem_nhds (half_pos hε))).and
        ((Real.tendsto_exp_atTop.eventually_ge_atTop x₀).and (eventually_ge_atTop 0)))
    refine ⟨ε / 2, U₀, half_pos hε, fun T hT => ?_⟩
    obtain ⟨hsmallT, -, hT0⟩ := hU₀ T hT
    obtain ⟨u, hu, hbig⟩ := hwin T hT0
    obtain ⟨hsmall, hx₀u, -⟩ := hU₀ u (hT.trans hu.1)
    refine ⟨u, hu, ?_⟩
    have hE : 0 < Real.exp (β * u) := Real.exp_pos _
    have hpow : Real.exp u ^ β = Real.exp (β * u) := by
      rw [← Real.exp_mul, mul_comm]
    have hpow' : Real.exp u ^ (β - η) = Real.exp (β * u) * Real.exp (-(η * u)) := by
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    have h1 := hC (Real.exp u) hx₀u
    rw [Real.log_exp, hpow, hpow'] at h1
    have h2 : ε * Real.exp (β * u) ≤ |Real.exp (β * u) * finiteOscillation S c u| := by
      rw [abs_mul, abs_of_pos hE, mul_comm]
      exact mul_le_mul_of_nonneg_left hbig hE.le
    have h3 : |Real.exp (β * u) * finiteOscillation S c u| ≤
        |Chebyshev.psi (Real.exp u) - Real.exp u| +
          |Chebyshev.psi (Real.exp u) - Real.exp u -
            Real.exp (β * u) * finiteOscillation S c u| := by
      have := abs_sub_le (Chebyshev.psi (Real.exp u) - Real.exp u) 0
        (Chebyshev.psi (Real.exp u) - Real.exp u - Real.exp (β * u) * finiteOscillation S c u)
      have hrew : Chebyshev.psi (Real.exp u) - Real.exp u -
          (Chebyshev.psi (Real.exp u) - Real.exp u -
            Real.exp (β * u) * finiteOscillation S c u) =
          Real.exp (β * u) * finiteOscillation S c u := by ring
      rw [hrew, sub_zero, zero_sub, abs_neg] at this
      exact this
    have h4 : C * (Real.exp (β * u) * Real.exp (-(η * u))) ≤ ε / 2 * Real.exp (β * u) := by
      have h5 : C * Real.exp (-(η * u)) ≤ ε / 2 :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans hsmall.le
      have h6 := mul_le_mul_of_nonneg_right h5 hE.le
      linarith only [h6, mul_assoc C (Real.exp (-(η * u))) (Real.exp (β * u)),
        mul_comm (Real.exp (β * u)) (Real.exp (-(η * u))),
        mul_assoc C (Real.exp (β * u)) (Real.exp (-(η * u)))]
    linarith only [h1, h2, h3, h4]

/-- **Non-attainment of the prime number theorem gives the abscissa law.** Suppose that for
every `β > ½` with `ψ(x) − x = O(x^β)` there is a ratio `e^L > 1` and arbitrarily late windows
`[e^T, e^{T+L}]` on which `|ψ(x) − x| ≤ ε x^β`, for every `ε > 0`. Then the asymptotic abscissa
law holds. -/
theorem asymptoticAbscissaLaw_of_psi_window_nonAttainment
    (h : ∀ β : ℝ, 1 / 2 < β →
      (∃ C x₀ : ℝ, ∀ x, x₀ ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ β) →
      ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u ∈ Icc T (T + L),
        |Chebyshev.psi (Real.exp u) - Real.exp u| ≤ ε * Real.exp (β * u)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨β, hβ, hO, hatt⟩ := psi_attained_on_every_window_of_not_asymptoticAbscissaLaw hnot
  obtain ⟨L, hL, hwin⟩ := h β hβ hO
  obtain ⟨δ, U₀, hδ, hbig⟩ := hatt L hL
  obtain ⟨T, hT, hsmall⟩ := hwin (δ / 2) (half_pos hδ) U₀
  obtain ⟨u, hu, hge⟩ := hbig T hT
  have hE : 0 < Real.exp (β * u) := Real.exp_pos _
  have hle := hsmall u hu
  nlinarith only [hge, hle, hE, hδ]

end GaloisForLFunctions.FloorFreeArithmetic
