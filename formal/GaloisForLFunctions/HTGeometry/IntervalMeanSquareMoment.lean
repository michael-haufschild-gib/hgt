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
    (hms : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖D t‖ ^ 2) ≤ Q + κ * U) (M : ℕ)
    (hG : ∀ t, t₀ ≤ t → t ≤ t₀ * 2 ^ M → G t ≤ C / t) :
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

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- The integral over a symmetric range is invariant under reflection. -/
theorem integral_Icc_comp_neg (f : ℝ → ℝ) {U : ℝ} (hU : 0 ≤ U) :
    (∫ t in Set.Icc (-U) U, f (-t)) = ∫ t in Set.Icc (-U) U, f t := by
  have hle : -U ≤ U := by linarith
  have hconv : ∀ g : ℝ → ℝ, (∫ t in Set.Icc (-U) U, g t) = ∫ t in (-U)..U, g t := by
    intro g
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv (fun t => f (-t)), hconv f]
  rw [intervalIntegral.integral_comp_neg f]
  norm_num

/-- The mean square over a symmetric range is invariant under reflection. -/
theorem integral_Icc_normSq_comp_neg (D : ℝ → ℂ) {U : ℝ} (hU : 0 ≤ U) :
    (∫ t in Set.Icc (-U) U, ‖D (-t)‖ ^ 2) = ∫ t in Set.Icc (-U) U, ‖D t‖ ^ 2 :=
  integral_Icc_comp_neg (fun t => ‖D t‖ ^ 2) hU

/-- **The low range of a vertical integral.**  On `|t| ≤ t₀` the kernel is bounded, so Cauchy–Schwarz
against the mean square at height `t₀` bounds the contribution by `C₀·√(2t₀)·√(Q + κt₀)`. -/
theorem integral_norm_mul_kernel_low_le {D : ℝ → ℂ} (hD : Continuous D) {G : ℝ → ℝ}
    (hGc : Continuous G) {C₀ Q κ t₀ : ℝ} (hC₀ : 0 ≤ C₀) (ht₀ : 0 < t₀)
    (hGlow : ∀ t, |t| ≤ t₀ → G t ≤ C₀)
    (hms : (∫ t in Set.Icc (-t₀) t₀, ‖D t‖ ^ 2) ≤ Q + κ * t₀) :
    (∫ t in (-t₀)..t₀, ‖D t‖ * G t) ≤ C₀ * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀)) := by
  have hle : -t₀ ≤ t₀ := by linarith
  have hmono : (∫ t in (-t₀)..t₀, ‖D t‖ * G t) ≤ ∫ t in (-t₀)..t₀, ‖D t‖ * C₀ := by
    refine intervalIntegral.integral_mono_on hle ((hD.norm.mul hGc).intervalIntegrable _ _)
      ((hD.norm.mul continuous_const).intervalIntegrable _ _) ?_
    intro t ht
    exact mul_le_mul_of_nonneg_left (hGlow t (abs_le.2 ⟨ht.1, ht.2⟩)) (norm_nonneg _)
  rw [intervalIntegral.integral_mul_const] at hmono
  have hcs : (∫ t in (-t₀)..t₀, ‖D t‖)
      ≤ Real.sqrt (t₀ - -t₀) * Real.sqrt (∫ t in (-t₀)..t₀, ‖D t‖ ^ 2) :=
    integral_norm_le_sqrt_length_mul_sqrt_meanSquare hD hle
  have hlen : t₀ - -t₀ = 2 * t₀ := by ring
  rw [hlen] at hcs
  have hmsint : (∫ t in (-t₀)..t₀, ‖D t‖ ^ 2) ≤ Q + κ * t₀ := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hms
  have hsq : Real.sqrt (∫ t in (-t₀)..t₀, ‖D t‖ ^ 2) ≤ Real.sqrt (Q + κ * t₀) :=
    Real.sqrt_le_sqrt hmsint
  calc (∫ t in (-t₀)..t₀, ‖D t‖ * G t)
      ≤ (∫ t in (-t₀)..t₀, ‖D t‖) * C₀ := hmono
    _ ≤ (Real.sqrt (2 * t₀) * Real.sqrt (∫ t in (-t₀)..t₀, ‖D t‖ ^ 2)) * C₀ :=
        mul_le_mul_of_nonneg_right hcs hC₀
    _ ≤ (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀)) * C₀ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) hC₀
    _ = C₀ * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀)) := by ring

/-- **The vertical integral over a symmetric range.**  The dyadic bound applies to both flanks — the
negative one after reflection, under which a symmetric kernel and the mean square are invariant — and
the low range contributes the bounded-kernel term.  Nothing but the block count `M` depends on the
height. -/
theorem integral_symm_norm_mul_kernel_le {D : ℝ → ℂ} (hD : Continuous D) {G : ℝ → ℝ}
    (hGc : Continuous G) (hGsym : ∀ t, G (-t) = G t)
    {C C₀ Q κ t₀ : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hQ : 0 ≤ Q) (hκ : 0 ≤ κ) (ht₀ : 0 < t₀)
    (hGlow : ∀ t, |t| ≤ t₀ → G t ≤ C₀)
    (hms : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖D t‖ ^ 2) ≤ Q + κ * U) (M : ℕ)
    (hG : ∀ t, t₀ ≤ t → t ≤ t₀ * 2 ^ M → G t ≤ C / t) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M), ‖D t‖ * G t)
      ≤ 2 * ((C * Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
              + 2 * C * Real.sqrt κ * M)
          + C₀ * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀)) := by
  have hone : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  have hb : t₀ ≤ t₀ * 2 ^ M := by nlinarith [ht₀.le]
  have hb0 : (0 : ℝ) < t₀ * 2 ^ M := by positivity
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun t => ‖D t‖ * G t) volume u v :=
    fun u v => (hD.norm.mul hGc).intervalIntegrable _ _
  -- the three ranges
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t => ‖D t‖ * G t) (μ := volume) (a := -(t₀ * 2 ^ M)) (b := -t₀) (c := t₀)
    (hint _ _) (hint _ _)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t => ‖D t‖ * G t) (μ := volume) (a := -(t₀ * 2 ^ M)) (b := t₀)
    (c := t₀ * 2 ^ M) (hint _ _) (hint _ _)
  -- the positive flank
  have hpos : (∫ t in t₀..(t₀ * 2 ^ M), ‖D t‖ * G t)
      ≤ (C * Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * C * Real.sqrt κ * M :=
    integral_norm_mul_kernel_le_of_affine_meanSquare hD hGc hQ hκ hC ht₀ hms M hG
  -- the negative flank, after reflection
  have hrefl : (∫ t in (-(t₀ * 2 ^ M))..(-t₀), ‖D t‖ * G t)
      = ∫ t in t₀..(t₀ * 2 ^ M), ‖D (-t)‖ * G (-t) := by
    rw [intervalIntegral.integral_comp_neg (fun t => ‖D t‖ * G t)]
  have hnegms : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖D (-t)‖ ^ 2) ≤ Q + κ * U := by
    intro U hU
    rw [integral_Icc_normSq_comp_neg D (by linarith)]
    exact hms U hU
  have hnegG : ∀ t, t₀ ≤ t → t ≤ t₀ * 2 ^ M → G (-t) ≤ C / t := by
    intro t ht htop
    rw [hGsym t]
    exact hG t ht htop
  have hneg : (∫ t in t₀..(t₀ * 2 ^ M), ‖D (-t)‖ * G (-t))
      ≤ (C * Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * C * Real.sqrt κ * M :=
    integral_norm_mul_kernel_le_of_affine_meanSquare (hD.comp continuous_neg)
      (hGc.comp continuous_neg) hQ hκ hC ht₀ hnegms M hnegG
  -- the low range
  have hlow : (∫ t in (-t₀)..t₀, ‖D t‖ * G t)
      ≤ C₀ * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀)) :=
    integral_norm_mul_kernel_low_le hD hGc hC₀ ht₀ hGlow (hms t₀ le_rfl)
  rw [hrefl] at hsplit1
  linarith [hsplit1, hsplit2]

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- Cauchy–Schwarz on an interval, for two functions. -/
theorem integral_norm_mul_norm_le_sqrt_mul_sqrt {A B : ℝ → ℂ} (hA : Continuous A)
    (hB : Continuous B) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖A t‖ * ‖B t‖)
      ≤ Real.sqrt (∫ t in a..b, ‖A t‖ ^ 2) * Real.sqrt (∫ t in a..b, ‖B t‖ ^ 2) := by
  have hm1 : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)) :=
    hA.aestronglyMeasurable.restrict
  have hm2 : AEStronglyMeasurable B (volume.restrict (Set.Icc a b)) :=
    hB.aestronglyMeasurable.restrict
  have h1 : Integrable (fun y => ‖A y‖ ^ 2) (volume.restrict (Set.Icc a b)) :=
    (hA.norm.pow 2).integrableOn_Icc
  have h2 : Integrable (fun y => ‖B y‖ ^ 2) (volume.restrict (Set.Icc a b)) :=
    (hB.norm.pow 2).integrableOn_Icc
  have hcs := integral_mul_le_sqrt_mul_sqrt_measure (μ := volume.restrict (Set.Icc a b))
    hm1 hm2 h1 h2
  have hconv : ∀ f : ℝ → ℝ, (∫ t in a..b, f t) = ∫ t in Set.Icc a b, f t := by
    intro f
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv (fun t => ‖A t‖ * ‖B t‖), hconv (fun t => ‖A t‖ ^ 2), hconv (fun t => ‖B t‖ ^ 2)]
  exact hcs

/-- The root mean square over a subinterval of `[0, b]` from an affine mean square at height `b`. -/
theorem sqrt_integral_normSq_le_affine {D : ℝ → ℂ} (hD : Continuous D) {Q κ : ℝ} (hQ : 0 ≤ Q)
    (hκ : 0 ≤ κ) {a b : ℝ} (hms : (∫ t in Set.Icc (-b) b, ‖D t‖ ^ 2) ≤ Q + κ * b) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : 0 < b) :
    Real.sqrt (∫ t in a..b, ‖D t‖ ^ 2) ≤ Real.sqrt Q + Real.sqrt κ * Real.sqrt b := by
  have hsq : Integrable (fun y => ‖D y‖ ^ 2) (volume.restrict (Set.Icc (-b) b)) :=
    (hD.norm.pow 2).integrableOn_Icc
  have hmono : (∫ t in a..b, ‖D t‖ ^ 2) ≤ ∫ t in Set.Icc (-b) b, ‖D t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    refine MeasureTheory.setIntegral_mono_set hsq ?_ ?_
    · filter_upwards with t
      positivity
    · refine Filter.Eventually.of_forall fun t ht => ?_
      exact Set.mem_Icc.2 ⟨by linarith [ht.1], ht.2⟩
  calc Real.sqrt (∫ t in a..b, ‖D t‖ ^ 2) ≤ Real.sqrt (Q + κ * b) :=
        Real.sqrt_le_sqrt (le_trans hmono hms)
    _ ≤ Real.sqrt Q + Real.sqrt (κ * b) := sqrt_add_le_sqrt_add_sqrt' hQ (by positivity)
    _ = Real.sqrt Q + Real.sqrt κ * Real.sqrt b := by rw [Real.sqrt_mul hκ b]

/-- **The first moment of a product from two affine mean squares.**  Cauchy–Schwarz multiplies the two
root mean squares, and the product of two affine square roots is a constant, a `√(height)` term and a
linear term. -/
theorem integral_norm_mul_norm_le_general_affine {A B : ℝ → ℂ} (hA : Continuous A)
    (hB : Continuous B) {QA κA QB κB : ℝ} (hQA : 0 ≤ QA) (hκA : 0 ≤ κA) (hQB : 0 ≤ QB)
    (hκB : 0 ≤ κB) {a b : ℝ}
    (hmsA : (∫ t in Set.Icc (-b) b, ‖A t‖ ^ 2) ≤ QA + κA * b)
    (hmsB : (∫ t in Set.Icc (-b) b, ‖B t‖ ^ 2) ≤ QB + κB * b)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    (∫ t in a..b, ‖A t‖ * ‖B t‖)
      ≤ Real.sqrt QA * Real.sqrt QB
          + (Real.sqrt QA * Real.sqrt κB + Real.sqrt κA * Real.sqrt QB) * Real.sqrt b
          + Real.sqrt κA * Real.sqrt κB * b := by
  have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hA' : Real.sqrt (∫ t in a..b, ‖A t‖ ^ 2) ≤ Real.sqrt QA + Real.sqrt κA * Real.sqrt b :=
    sqrt_integral_normSq_le_affine hA hQA hκA hmsA ha hab hb
  have hB' : Real.sqrt (∫ t in a..b, ‖B t‖ ^ 2) ≤ Real.sqrt QB + Real.sqrt κB * Real.sqrt b :=
    sqrt_integral_normSq_le_affine hB hQB hκB hmsB ha hab hb
  calc (∫ t in a..b, ‖A t‖ * ‖B t‖)
      ≤ Real.sqrt (∫ t in a..b, ‖A t‖ ^ 2) * Real.sqrt (∫ t in a..b, ‖B t‖ ^ 2) :=
        integral_norm_mul_norm_le_sqrt_mul_sqrt hA hB hab
    _ ≤ (Real.sqrt QA + Real.sqrt κA * Real.sqrt b)
          * (Real.sqrt QB + Real.sqrt κB * Real.sqrt b) := by
        refine mul_le_mul hA' hB' (Real.sqrt_nonneg _) (by positivity)
    _ = Real.sqrt QA * Real.sqrt QB
          + (Real.sqrt QA * Real.sqrt κB + Real.sqrt κA * Real.sqrt QB) * Real.sqrt b
          + Real.sqrt κA * Real.sqrt κB * b := by
        linear_combination (Real.sqrt κA * Real.sqrt κB) * hbb

/-- **The vertical integral of a product against a first-order kernel.**  Two affine mean squares give
a block moment of the general shape, so the dyadic split bounds the integral by a constant plus a
logarithm in the height.  A third factor bounded by `V` on the range is absorbed by using the kernel
bound `V·C/t`: the statement is applied with `C` replaced by `V·C`. -/
theorem integral_norm_mul_norm_mul_kernel_le {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B)
    {G : ℝ → ℝ} (hGc : Continuous G) {QA κA QB κB C t₀ : ℝ} (hQA : 0 ≤ QA) (hκA : 0 ≤ κA)
    (hQB : 0 ≤ QB) (hκB : 0 ≤ κB) (hC : 0 ≤ C) (ht₀ : 0 < t₀)
    (hmsA : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖A t‖ ^ 2) ≤ QA + κA * U)
    (hmsB : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖B t‖ ^ 2) ≤ QB + κB * U) (M : ℕ)
    (hG : ∀ t, t₀ ≤ t → t ≤ t₀ * 2 ^ M → G t ≤ C / t) :
    (∫ t in t₀..(t₀ * 2 ^ M), (‖A t‖ * ‖B t‖) * G t)
      ≤ 2 * (C * (Real.sqrt QA * Real.sqrt QB) / t₀)
          + (C * (Real.sqrt QA * Real.sqrt κB + Real.sqrt κA * Real.sqrt QB) * Real.sqrt 2
              / Real.sqrt t₀) * (1 - Real.sqrt 2 / 2)⁻¹
          + 2 * C * (Real.sqrt κA * Real.sqrt κB) * M := by
  have hpow : ∀ m : ℕ, (0 : ℝ) < t₀ * 2 ^ m := fun m => by positivity
  have hge : ∀ m : ℕ, t₀ ≤ t₀ * 2 ^ m := by
    intro m
    have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith [ht₀.le]
  have hstep : ∀ m : ℕ, t₀ * 2 ^ m ≤ t₀ * 2 ^ (m + 1) := by
    intro m
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) ht₀.le
  refine integral_mul_kernel_le_of_general_block_moment (F := fun t => ‖A t‖ * ‖B t‖) ht₀ hC
    (by positivity) (by positivity) (fun t => by positivity) hG
    (fun m _ => ((hA.norm.mul hB.norm).intervalIntegrable _ _))
    (fun m _ => (((hA.norm.mul hB.norm).mul hGc).intervalIntegrable _ _))
    (fun m _ => ?_)
  exact integral_norm_mul_norm_le_general_affine hA hB hQA hκA hQB hκB
    (hmsA _ (hge (m + 1))) (hmsB _ (hge (m + 1))) (hpow m).le (hstep m) (hpow (m + 1))

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- **The low range of a product integral.**  On `|t| ≤ t₀` the kernel is bounded, so Cauchy–Schwarz
against the two mean squares at height `t₀` bounds the contribution. -/
theorem integral_norm_mul_norm_low_le {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B)
    {G : ℝ → ℝ} (hGc : Continuous G) {C₀ QA κA QB κB t₀ : ℝ} (hC₀ : 0 ≤ C₀) (ht₀ : 0 < t₀)
    (hGlow : ∀ t, |t| ≤ t₀ → G t ≤ C₀)
    (hmsA : (∫ t in Set.Icc (-t₀) t₀, ‖A t‖ ^ 2) ≤ QA + κA * t₀)
    (hmsB : (∫ t in Set.Icc (-t₀) t₀, ‖B t‖ ^ 2) ≤ QB + κB * t₀) :
    (∫ t in (-t₀)..t₀, (‖A t‖ * ‖B t‖) * G t)
      ≤ C₀ * (Real.sqrt (QA + κA * t₀) * Real.sqrt (QB + κB * t₀)) := by
  have hle : -t₀ ≤ t₀ := by linarith
  have hconv : ∀ f : ℝ → ℝ, (∫ t in (-t₀)..t₀, f t) = ∫ t in Set.Icc (-t₀) t₀, f t := by
    intro f
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hmono : (∫ t in (-t₀)..t₀, (‖A t‖ * ‖B t‖) * G t)
      ≤ ∫ t in (-t₀)..t₀, (‖A t‖ * ‖B t‖) * C₀ := by
    refine intervalIntegral.integral_mono_on hle
      (((hA.norm.mul hB.norm).mul hGc).intervalIntegrable _ _)
      (((hA.norm.mul hB.norm).mul continuous_const).intervalIntegrable _ _) ?_
    intro t ht
    exact mul_le_mul_of_nonneg_left (hGlow t (abs_le.2 ⟨ht.1, ht.2⟩)) (by positivity)
  rw [intervalIntegral.integral_mul_const] at hmono
  have hcs : (∫ t in (-t₀)..t₀, ‖A t‖ * ‖B t‖)
      ≤ Real.sqrt (∫ t in (-t₀)..t₀, ‖A t‖ ^ 2) * Real.sqrt (∫ t in (-t₀)..t₀, ‖B t‖ ^ 2) :=
    integral_norm_mul_norm_le_sqrt_mul_sqrt hA hB hle
  have hA' : Real.sqrt (∫ t in (-t₀)..t₀, ‖A t‖ ^ 2) ≤ Real.sqrt (QA + κA * t₀) := by
    refine Real.sqrt_le_sqrt ?_
    rw [hconv (fun t => ‖A t‖ ^ 2)]
    exact hmsA
  have hB' : Real.sqrt (∫ t in (-t₀)..t₀, ‖B t‖ ^ 2) ≤ Real.sqrt (QB + κB * t₀) := by
    refine Real.sqrt_le_sqrt ?_
    rw [hconv (fun t => ‖B t‖ ^ 2)]
    exact hmsB
  calc (∫ t in (-t₀)..t₀, (‖A t‖ * ‖B t‖) * G t)
      ≤ (∫ t in (-t₀)..t₀, ‖A t‖ * ‖B t‖) * C₀ := hmono
    _ ≤ (Real.sqrt (QA + κA * t₀) * Real.sqrt (QB + κB * t₀)) * C₀ := by
        refine mul_le_mul_of_nonneg_right (le_trans hcs ?_) hC₀
        exact mul_le_mul hA' hB' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = C₀ * (Real.sqrt (QA + κA * t₀) * Real.sqrt (QB + κB * t₀)) := by ring

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory Set

/-- **The low range of a product integral, from pointwise bounds.**  On a bounded range the pointwise
sizes of the two factors may beat their mean squares: Cauchy–Schwarz charges `√(Q_A Q_B)`, while the
pointwise route charges `V_A V_B` times the length.  For a Dirichlet polynomial `V` is its damped `ℓ¹`
mass, which for a prime weight is a logarithm smaller than the square root of its `n`-weighted mass. -/
theorem integral_norm_mul_norm_low_le_pointwise {A B : ℝ → ℂ} (hA : Continuous A)
    (hB : Continuous B) {G : ℝ → ℝ} (hGc : Continuous G) {C₀ VA VB t₀ : ℝ}
    (ht₀ : 0 < t₀) (hVA : 0 ≤ VA) (hVB : 0 ≤ VB) (hG0 : ∀ t, 0 ≤ G t)
    (hGlow : ∀ t, |t| ≤ t₀ → G t ≤ C₀)
    (hAb : ∀ t, |t| ≤ t₀ → ‖A t‖ ≤ VA) (hBb : ∀ t, |t| ≤ t₀ → ‖B t‖ ≤ VB) :
    (∫ t in (-t₀)..t₀, (‖A t‖ * ‖B t‖) * G t) ≤ (2 * t₀) * (VA * VB * C₀) := by
  have hle : -t₀ ≤ t₀ := by linarith
  have hmono : (∫ t in (-t₀)..t₀, (‖A t‖ * ‖B t‖) * G t)
      ≤ ∫ _t in (-t₀)..t₀, VA * VB * C₀ := by
    refine intervalIntegral.integral_mono_on hle
      (((hA.norm.mul hB.norm).mul hGc).intervalIntegrable _ _)
      (intervalIntegrable_const) ?_
    intro t ht
    have habs : |t| ≤ t₀ := abs_le.2 ⟨ht.1, ht.2⟩
    calc (‖A t‖ * ‖B t‖) * G t ≤ (VA * VB) * C₀ :=
          mul_le_mul (mul_le_mul (hAb t habs) (hBb t habs) (norm_nonneg _) hVA)
            (hGlow t habs) (hG0 t) (by positivity)
      _ = VA * VB * C₀ := by ring
  refine le_trans hmono (le_of_eq ?_)
  rw [intervalIntegral.integral_const]
  have hlen : t₀ - -t₀ = 2 * t₀ := by ring
  rw [hlen, smul_eq_mul]

end GaloisForLFunctions.HTGeometry
end
