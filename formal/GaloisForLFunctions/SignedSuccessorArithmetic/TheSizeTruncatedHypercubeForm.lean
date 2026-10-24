import GaloisForLFunctions.SignedSuccessorArithmetic.TheHypercubeDirichletFormIsUnbounded
import Mathlib.Analysis.PSeries

/-!
# The size-truncated hypercube form

The prime-supported hypercube form `Q_ε(P)` diverges below half damping for a reason unrelated to
the zeros of `ζ` (`TheHypercubeDirichletFormIsUnbounded`). The object that can carry information
about zeros is the **size-truncated** form

  `R_ε(D) = Σ_{d₁, d₂ ≤ D} μ(d₁) μ(d₂) (d₁ d₂)^{−1/2−ε} Φ_r(d₁/d₂)`.

Under the same spectral transport it is the mean square of the truncated Möbius–Dirichlet
polynomial against the spectral weight of the step vector,

  `R_ε(D) = ∫ W(ξ) |Σ_{d ≤ D} μ(d) d^{−σ} e^{2πiξ log d}|² dξ`,  `σ = 1/2 + ε`

(`sizeHypercubeForm_eq_integral`), so it is nonnegative (`sizeHypercubeForm_nonneg`) and, for
`σ > 1`, bounded uniformly in `D` by `ζ(σ)² Φ_r(1)` (`sizeHypercubeForm_le_of_one_lt`). Its uniform
boundedness for `1/2 < σ ≤ 1` asks that `1/ζ` be square integrable against `W` on the line
`Re s = σ` as a limit of its truncations: this is where the zeros enter.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Finset
open _root_.RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius

variable {r : ℕ} (hr : 1 < r)

/-- The size-truncated hypercube form `Σ_{d₁, d₂ ≤ D} μμ (d₁d₂)^{−1/2−ε} Φ_r(d₁/d₂)`. -/
noncomputable def sizeHypercubeForm (ε : ℝ) (D : ℕ) : ℝ :=
  ∑ d₁ ∈ Icc 1 D, ∑ d₂ ∈ Icc 1 D,
    (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
      (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
        pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)

/-- `|Σ_{d ≤ D} μ(d) d^{−σ} e^{iθ log d}|²` in real coordinates. -/
noncomputable def moebiusPolySq (σ θ : ℝ) (D : ℕ) : ℝ :=
  (∑ d ∈ Icc 1 D, moebiusReal d * (d : ℝ) ^ (-σ) * Real.cos (θ * Real.log d)) ^ 2 +
    (∑ d ∈ Icc 1 D, moebiusReal d * (d : ℝ) ^ (-σ) * Real.sin (θ * Real.log d)) ^ 2

theorem moebiusPolySq_nonneg (σ θ : ℝ) (D : ℕ) : 0 ≤ moebiusPolySq σ θ D := by
  unfold moebiusPolySq; positivity

/-- The double cosine sum is the squared modulus of the truncated polynomial. -/
theorem sum_sum_cos_eq_moebiusPolySq (σ θ : ℝ) (D : ℕ) :
    ∑ d₁ ∈ Icc 1 D, ∑ d₂ ∈ Icc 1 D,
        (moebiusReal d₁ * (d₁ : ℝ) ^ (-σ)) * (moebiusReal d₂ * (d₂ : ℝ) ^ (-σ)) *
          Real.cos (θ * (Real.log d₁ - Real.log d₂)) = moebiusPolySq σ θ D := by
  have hcos : ∀ d₁ d₂ : ℕ, Real.cos (θ * (Real.log d₁ - Real.log d₂)) =
      Real.cos (θ * Real.log d₁ - θ * Real.log d₂) := fun d₁ d₂ => by ring_nf
  simp_rw [hcos]
  rw [sum_sum_mul_cos_sub (Icc 1 D) (fun d => moebiusReal d * (d : ℝ) ^ (-σ))
    (fun d => θ * Real.log d), moebiusPolySq]

/-- **Spectral form of the size-truncated form.**
`R_ε(D) = ∫ W(ξ) |Σ_{d ≤ D} μ(d) d^{−σ} e^{2πiξ log d}|² dξ`. -/
theorem sizeHypercubeForm_eq_integral (ε : ℝ) (D : ℕ) :
    sizeHypercubeForm hr ε D =
      ∫ ξ, stepSpectralWeight hr ξ * moebiusPolySq (1 / 2 + ε) (2 * Real.pi * ξ) D := by
  set a : ℕ → ℝ := fun d => moebiusReal d * (d : ℝ) ^ (-(1 / 2 + ε))
  set g : ℕ → ℕ → ℝ → ℝ := fun d₁ d₂ ξ => a d₁ * a d₂ *
    (stepSpectralWeight hr ξ * Real.cos (2 * Real.pi * ξ * (Real.log d₁ - Real.log d₂)))
  have hg : ∀ d₁ d₂, Integrable (g d₁ d₂) := fun d₁ d₂ =>
    (integrable_stepSpectralWeight_mul_cos hr _).const_mul _
  have hterm : ∀ d₁ ∈ Icc 1 D, ∀ d₂ ∈ Icc 1 D,
      moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
          (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
        pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) = ∫ ξ, g d₁ d₂ ξ := by
    intro d₁ hd₁ d₂ hd₂
    have h1 : (0 : ℝ) < d₁ := by
      have := (mem_Icc.mp hd₁).1; exact_mod_cast (show 0 < d₁ by omega)
    have h2 : (0 : ℝ) < d₂ := by
      have := (mem_Icc.mp hd₂).1; exact_mod_cast (show 0 < d₂ by omega)
    rw [dilationProfile_eq_integral hr (div_pos h1 h2), Real.log_div h1.ne' h2.ne',
      ← integral_const_mul, show (-(1 / 2 : ℝ) - ε) = -(1 / 2 + ε) by ring]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have harg : 2 * Real.pi * ((Real.log d₁ - Real.log d₂) * ξ) =
        2 * Real.pi * ξ * (Real.log d₁ - Real.log d₂) := by ring
    simp only [g, a, harg]
  rw [sizeHypercubeForm,
    Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂]
  rw [Finset.sum_congr rfl fun d₁ _ =>
      (integral_finsetSum (Icc 1 D) fun d₂ _ => hg d₁ d₂).symm,
    ← integral_finsetSum (Icc 1 D) fun d₁ _ => integrable_finsetSum _ fun d₂ _ => hg d₁ d₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [← sum_sum_cos_eq_moebiusPolySq (1 / 2 + ε) (2 * Real.pi * ξ) D, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₂ _ => ?_
  simp only [g, a]
  ring

theorem sizeHypercubeForm_nonneg (ε : ℝ) (D : ℕ) : 0 ≤ sizeHypercubeForm hr ε D := by
  rw [sizeHypercubeForm_eq_integral]
  exact integral_nonneg fun ξ =>
    mul_nonneg (stepSpectralWeight_nonneg hr ξ) (moebiusPolySq_nonneg _ _ _)

/-- `|Σ_{d ≤ D} μ(d) d^{−σ} e^{iθ log d}|² ≤ (Σ_{d ≤ D} d^{−σ})²`. -/
theorem moebiusPolySq_le (σ θ : ℝ) (D : ℕ) :
    moebiusPolySq σ θ D ≤ (∑ d ∈ Icc 1 D, (d : ℝ) ^ (-σ)) ^ 2 := by
  rw [← sum_sum_cos_eq_moebiusPolySq, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => ?_
  have hμ : ∀ d : ℕ, |moebiusReal d| ≤ 1 := fun d => by
    unfold moebiusReal
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  have hp1 : 0 ≤ (d₁ : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp2 : 0 ≤ (d₂ : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc moebiusReal d₁ * (d₁ : ℝ) ^ (-σ) * (moebiusReal d₂ * (d₂ : ℝ) ^ (-σ)) *
        Real.cos (θ * (Real.log d₁ - Real.log d₂))
      ≤ |moebiusReal d₁ * (d₁ : ℝ) ^ (-σ) * (moebiusReal d₂ * (d₂ : ℝ) ^ (-σ)) *
        Real.cos (θ * (Real.log d₁ - Real.log d₂))| := le_abs_self _
    _ ≤ (d₁ : ℝ) ^ (-σ) * (d₂ : ℝ) ^ (-σ) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hp1, abs_of_nonneg hp2]
        have hc := Real.abs_cos_le_one (θ * (Real.log d₁ - Real.log d₂))
        have := hμ d₁
        have := hμ d₂
        calc |moebiusReal d₁| * (d₁ : ℝ) ^ (-σ) * (|moebiusReal d₂| * (d₂ : ℝ) ^ (-σ)) *
              |Real.cos (θ * (Real.log d₁ - Real.log d₂))|
            ≤ 1 * (d₁ : ℝ) ^ (-σ) * (1 * (d₂ : ℝ) ^ (-σ)) * 1 := by gcongr
          _ = _ := by ring

/-- **Absolute convergence.** For `σ = 1/2 + ε > 1`, `0 ≤ R_ε(D) ≤ ζ(σ)² Φ_r(1)` uniformly in `D`. -/
theorem sizeHypercubeForm_le_of_one_lt {ε : ℝ} (hε : 1 < 1 / 2 + ε) (D : ℕ) :
    sizeHypercubeForm hr ε D ≤
      (∑' d : ℕ, ((d : ℝ) ^ (1 / 2 + ε))⁻¹) ^ 2 * pmRamanujanDilationProfile r hr 1 := by
  have hsum : Summable fun d : ℕ => ((d : ℝ) ^ (1 / 2 + ε))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr hε
  have hfin : ∑ d ∈ Icc 1 D, (d : ℝ) ^ (-(1 / 2 + ε)) ≤ ∑' d : ℕ, ((d : ℝ) ^ (1 / 2 + ε))⁻¹ := by
    have : ∑ d ∈ Icc 1 D, (d : ℝ) ^ (-(1 / 2 + ε)) = ∑ d ∈ Icc 1 D, ((d : ℝ) ^ (1 / 2 + ε))⁻¹ :=
      Finset.sum_congr rfl fun d _ => Real.rpow_neg (Nat.cast_nonneg d) _
    rw [this]
    exact hsum.sum_le_tsum _ fun d _ => by positivity
  have hfin0 : 0 ≤ ∑ d ∈ Icc 1 D, (d : ℝ) ^ (-(1 / 2 + ε)) :=
    Finset.sum_nonneg fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _
  rw [sizeHypercubeForm_eq_integral]
  have hpt : ∀ ξ, stepSpectralWeight hr ξ * moebiusPolySq (1 / 2 + ε) (2 * Real.pi * ξ) D ≤
      stepSpectralWeight hr ξ * (∑' d : ℕ, ((d : ℝ) ^ (1 / 2 + ε))⁻¹) ^ 2 := fun ξ =>
    mul_le_mul_of_nonneg_left ((moebiusPolySq_le _ _ D).trans (pow_le_pow_left₀ hfin0 hfin 2))
      (stepSpectralWeight_nonneg hr ξ)
  have hint1 : Integrable fun ξ =>
      stepSpectralWeight hr ξ * moebiusPolySq (1 / 2 + ε) (2 * Real.pi * ξ) D := by
    refine (integrable_stepSpectralWeight hr).mul_bdd
      (by unfold moebiusPolySq; fun_prop : Continuous fun ξ =>
        moebiusPolySq (1 / 2 + ε) (2 * Real.pi * ξ) D).aestronglyMeasurable
      (c := (∑ d ∈ Icc 1 D, (d : ℝ) ^ (-(1 / 2 + ε))) ^ 2) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (moebiusPolySq_nonneg _ _ _)]
    exact moebiusPolySq_le _ _ D
  have h1 := dilationProfile_eq_integral hr one_pos
  simp only [Real.log_one, zero_mul, mul_zero, Real.cos_zero, mul_one] at h1
  calc ∫ ξ, stepSpectralWeight hr ξ * moebiusPolySq (1 / 2 + ε) (2 * Real.pi * ξ) D
      ≤ ∫ ξ, stepSpectralWeight hr ξ * (∑' d : ℕ, ((d : ℝ) ^ (1 / 2 + ε))⁻¹) ^ 2 :=
        integral_mono hint1 ((integrable_stepSpectralWeight hr).mul_const _) hpt
    _ = _ := by rw [integral_mul_const, h1, mul_comm]

end GaloisForLFunctions.SignedSuccessorArithmetic
