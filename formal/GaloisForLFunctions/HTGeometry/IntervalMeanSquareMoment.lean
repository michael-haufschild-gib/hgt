import GaloisForLFunctions.HTGeometry.WeightedHolder
import GaloisForLFunctions.HTGeometry.VerticalKernelDyadicSplit

/-!
# The first moment of a line function from its mean square

Cauchy–Schwarz on an interval turns a mean-square estimate into a first moment: the moment over an
interval of length `ℓ` is at most `√ℓ` times the square root of the mean square.  When the mean square
over the symmetric range `|t| ≤ U` is affine in `U`, `Q + κU`, the moment over any interval inside
`[0, b]` is therefore at most `√Q·√b + √κ·b`: a square-root term carrying the `U`-independent part of
the mean square, and a linear term carrying its growing part.

This is the shape the dyadic height split consumes.  A kernel decaying like `1/t` charges the
square-root term a geometric series over the blocks and the linear term one constant per block, so the
`U`-independent part of a mean square is worth a bounded contribution while its growing part is worth
a logarithm.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- The square root is subadditive. -/
theorem sqrt_add_le_sqrt_add_sqrt' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hx' : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hy' : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have h1 : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-- **Cauchy–Schwarz on an interval.**  The first moment of a continuous function over `[a, b]` is at
most the square root of the length times the square root of the mean square. -/
theorem integral_norm_le_sqrt_length_mul_sqrt_meanSquare {D : ℝ → ℂ} (hD : Continuous D)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖D t‖) ≤ Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖D t‖ ^ 2) := by
  have hvol : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hm1 : AEStronglyMeasurable D (volume.restrict (Set.Icc a b)) :=
    hD.aestronglyMeasurable.restrict
  have h1 : Integrable (fun y => ‖D y‖ ^ 2) (volume.restrict (Set.Icc a b)) :=
    (hD.norm.pow 2).integrableOn_Icc
  have h2 : Integrable (fun _ : ℝ => ‖(1 : ℂ)‖ ^ 2) (volume.restrict (Set.Icc a b)) :=
    MeasureTheory.integrableOn_const hvol (by simp)
  have hcs := integral_mul_le_sqrt_mul_sqrt_measure (μ := volume.restrict (Set.Icc a b))
    (g₁ := D) (g₂ := fun _ => (1 : ℂ)) hm1 aestronglyMeasurable_const h1 h2
  simp only [norm_one, mul_one, one_pow] at hcs
  have hlen : (∫ _ : ℝ in Set.Icc a b, (1 : ℝ)) = b - a := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc, smul_eq_mul, mul_one,
      max_eq_left (by linarith)]
  rw [hlen] at hcs
  have hconv : ∀ f : ℝ → ℝ, (∫ t in a..b, f t) = ∫ t in Set.Icc a b, f t := by
    intro f
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv (fun t => ‖D t‖), hconv (fun t => ‖D t‖ ^ 2), mul_comm]
  exact hcs

/-- **The first moment from an affine mean square.**  If the mean square over `|t| ≤ b` is at most
`Q + κb`, then the first moment over any interval inside `[0, b]` is at most `√Q·√b + √κ·b`. -/
theorem integral_norm_le_sqrt_affine {D : ℝ → ℂ} (hD : Continuous D) {Q κ : ℝ} (hQ : 0 ≤ Q)
    (hκ : 0 ≤ κ) {a b : ℝ}
    (hms : (∫ t in Set.Icc (-b) b, ‖D t‖ ^ 2) ≤ Q + κ * b)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    (∫ t in a..b, ‖D t‖) ≤ Real.sqrt Q * Real.sqrt b + Real.sqrt κ * b := by
  have hsq : Integrable (fun y => ‖D y‖ ^ 2) (volume.restrict (Set.Icc (-b) b)) :=
    (hD.norm.pow 2).integrableOn_Icc
  have hmono : (∫ t in a..b, ‖D t‖ ^ 2) ≤ ∫ t in Set.Icc (-b) b, ‖D t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    refine MeasureTheory.setIntegral_mono_set hsq ?_ ?_
    · filter_upwards with t
      positivity
    · refine Filter.Eventually.of_forall fun t ht => ?_
      exact Set.mem_Icc.2 ⟨by linarith [ht.1], ht.2⟩
  have hbnd : (∫ t in a..b, ‖D t‖ ^ 2) ≤ Q + κ * b := le_trans hmono hms
  have hlen : Real.sqrt (b - a) ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
  calc (∫ t in a..b, ‖D t‖)
      ≤ Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖D t‖ ^ 2) :=
        integral_norm_le_sqrt_length_mul_sqrt_meanSquare hD hab
    _ ≤ Real.sqrt b * Real.sqrt (Q + κ * b) := by
        refine mul_le_mul hlen (Real.sqrt_le_sqrt hbnd) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt b * (Real.sqrt Q + Real.sqrt (κ * b)) := by
        refine mul_le_mul_of_nonneg_left (sqrt_add_le_sqrt_add_sqrt' hQ (by positivity))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt Q * Real.sqrt b + Real.sqrt κ * b := by
        rw [Real.sqrt_mul hκ b]
        have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
        ring_nf
        nlinarith [hbb, Real.sqrt_nonneg b, Real.sqrt_nonneg Q, Real.sqrt_nonneg κ]

/-- **The vertical integral against a first-order kernel, from a mean square.**  For a continuous line
function whose mean square over `|t| ≤ U` is at most `Q + κU`, and a kernel bounded by `C/t` beyond
`t₀`, the integral over `[t₀, t₀·2^M]` is at most

`C·√Q·√2·(1 − √2/2)⁻¹/√t₀ + 2C·√κ·M`.

The first term is independent of `M`: the `U`-independent part of the mean square is charged a
geometric series by the kernel's decay.  Only the growing part of the mean square is charged per
block, and it therefore costs a factor logarithmic in the height. -/
theorem integral_norm_mul_kernel_le_of_affine_meanSquare {D : ℝ → ℂ} (hD : Continuous D)
    {G : ℝ → ℝ} (hGc : Continuous G) {Q κ C t₀ : ℝ} (hQ : 0 ≤ Q) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (ht₀ : 0 < t₀)
    (hms : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖D t‖ ^ 2) ≤ Q + κ * U)
    (hG : ∀ t, t₀ ≤ t → G t ≤ C / t) (M : ℕ) :
    (∫ t in t₀..(t₀ * 2 ^ M), ‖D t‖ * G t)
      ≤ (C * Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * C * Real.sqrt κ * M := by
  have hpow : ∀ m : ℕ, (0 : ℝ) < t₀ * 2 ^ m := fun m => by positivity
  have hge : ∀ m : ℕ, t₀ ≤ t₀ * 2 ^ m := by
    intro m
    have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith [ht₀.le]
  have hstep : ∀ m : ℕ, t₀ * 2 ^ m ≤ t₀ * 2 ^ (m + 1) := by
    intro m
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) ht₀.le
  refine integral_mul_kernel_le_of_affine_block_moment (F := fun t => ‖D t‖) ht₀ hC
    (Real.sqrt_nonneg Q) (fun t => norm_nonneg _) hG
    (fun m _ => (hD.norm.intervalIntegrable _ _))
    (fun m _ => ((hD.norm.mul hGc).intervalIntegrable _ _))
    (fun m _ => ?_)
  exact integral_norm_le_sqrt_affine hD hQ hκ (hms _ (hge (m + 1))) (hpow m).le (hstep m)
    (hpow (m + 1))

end GaloisForLFunctions.HTGeometry
end
