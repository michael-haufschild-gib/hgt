import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothGridWeightKernel
import GaloisForLFunctions.TransThresholdPairCorrelation.PrimeSurplusAnatomyAndDirichletMeanValue
import GaloisForLFunctions.TransThresholdPairCorrelation.HeightAveragedCoalescentLocalization

/-!
# The Smooth-Window Continuous Form and the Exact Coalescent Kernel

For a weight `Ω` (compactly supported, continuous) put
`𝓜_Ω[u, v] = ∬ Ω(τ) Φ(τ − τ')² u(τ) v(τ') dτ dτ'`. Because the `τ'`-integral runs over all of `ℝ`
and `∫ Φ(x)² e^{ixy} dx = 2π g(y)`, the convolution `Φ² ⋆ P_X` is again a prime polynomial,
`(Φ² ⋆ P_X)(τ) = −2 Σ_m a_m g(log m) cos(τ log m)` (`integral_PhiSq_shift_mul_PX`), and

`𝓜_Ω[u, P_X] = −2 Σ_m a_m g(log m) ∫ Ω(τ) u(τ) cos(τ log m) dτ`   (`smoothForm_PX_right_eq`).

For `u = P_X` this is an exact pair sum with the **coalescent kernel**
`(1/π) a_n a_m g(log m) [Ω̂(log n − log m) + Ω̂(log n + log m)]`, `Ω̂(θ) = ∫ Ω(τ) cos(τθ) dτ`
(`smoothForm_PX_PX_eq`): no half-line moments, no window end effects. The diagonal is
`π⁻¹ (∫Ω) Σ a_n² g(log n)` plus a sum-frequency term, and pairs with `|log(n/m)| > θ₀` carry
`Ω̂(θ) ≤ ‖Ω^{(k)}‖₁ / θ^k`.
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower RHTower.FejerWeight GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {Φ : ℝ → ℝ}

/-- The smooth-window continuous form `𝓜_Ω[u, v] = ∬ Ω(τ) Φ(τ − τ')² u(τ) v(τ')`. -/
def smoothForm (Φ Ω u v : ℝ → ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, Ω q.1 * Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2

/-- The convolution `(Φ² ⋆ v)(τ) = ∫ Φ(τ − τ')² v(τ') dτ'`. -/
def convSq (Φ v : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ τ', Φ (τ - τ') ^ 2 * v τ'

/-- The iterated smooth form `∫ Ω(τ) u(τ) (Φ² ⋆ v)(τ) dτ`. -/
def smoothPair (Φ Ω u v : ℝ → ℝ) : ℝ := ∫ τ, Ω τ * u τ * convSq Φ v τ

/-- The cosine transform `Ω̂(θ) = ∫ Ω(τ) cos(τθ) dτ` of the window. -/
def cosTransform (Ω : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ τ, Ω τ * Real.cos (τ * θ)

/-! ## 1. Convolving with `Φ²` -/

section Convolution

variable {g v : ℝ → ℝ}

/-- `∫ τ', Φ(τ − τ')² cos(τ' y) = 2π g(y) cos(τ y)` when `Φ` is even with `∫ Φ² cos(xy) = 2π g(y)`. -/
theorem integral_PhiSq_sub_mul_cos (hΦe : ∀ x, Φ (-x) = Φ x)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y)
    (τ y : ℝ) :
    ∫ τ', Φ (τ - τ') ^ 2 * Real.cos (τ' * y) = 2 * π * g y * Real.cos (τ * y) := by
  have hcos : Integrable fun x => Φ x ^ 2 * Real.cos (x * y) :=
    hΦ2.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun x => by
      simpa using Real.abs_cos_le_one (x * y))
  have hsin : Integrable fun x => Φ x ^ 2 * Real.sin (x * y) :=
    hΦ2.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun x => by
      simpa using Real.abs_sin_le_one (x * y))
  have hodd : ∫ x, Φ x ^ 2 * Real.sin (x * y) = 0 := by
    have h := integral_neg_eq_self (fun x => Φ x ^ 2 * Real.sin (x * y)) volume
    have e : (fun x => Φ (-x) ^ 2 * Real.sin (-x * y)) = fun x => -(Φ x ^ 2 * Real.sin (x * y)) := by
      funext x; rw [hΦe, neg_mul, Real.sin_neg]; ring
    rw [e, integral_neg] at h
    linarith
  have hsub := integral_sub_left_eq_self (fun x => Φ x ^ 2 * Real.cos ((τ - x) * y)) (μ := volume) τ
  simp only [sub_sub_cancel] at hsub
  rw [hsub]
  have e : (fun x => Φ x ^ 2 * Real.cos ((τ - x) * y))
      = fun x => Real.cos (τ * y) * (Φ x ^ 2 * Real.cos (x * y))
          + Real.sin (τ * y) * (Φ x ^ 2 * Real.sin (x * y)) := by
    funext x; rw [show (τ - x) * y = τ * y - x * y by ring, Real.cos_sub]; ring
  rw [e, integral_add (hcos.const_mul _) (hsin.const_mul _), integral_const_mul, integral_const_mul,
    hFT, hodd]
  ring

/-- **`Φ² ⋆ P_X` is a prime polynomial:** `∫ Φ(τ − τ')² P_X(τ') dτ' = −2 Σ_m a_m g(log m) cos(τ log m)`. -/
theorem integral_PhiSq_sub_mul_PX (hΦe : ∀ x, Φ (-x) = Φ x)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y)
    (X τ : ℝ) :
    ∫ τ', Φ (τ - τ') ^ 2 * Zeta23.PX X τ' = -2 * primeDirichletCos g X τ := by
  have hint : ∀ n : ℕ, Integrable fun τ' => Φ (τ - τ') ^ 2 * Real.cos (τ' * Real.log n) := fun n =>
    (hΦ2.comp_sub_left τ).mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun x => by
      simpa using Real.abs_cos_le_one (x * Real.log n))
  have e : (fun τ' => Φ (τ - τ') ^ 2 * Zeta23.PX X τ')
      = fun τ' => ∑ n ∈ primeRange X, (-(1 / π) * acoef n) * (Φ (τ - τ') ^ 2 * Real.cos (τ' * Real.log n)) := by
    funext τ'
    rw [PX_eq, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by unfold ycoef; ring
  rw [e, integral_finsetSum _ fun n _ => (hint n).const_mul _]
  unfold primeDirichletCos
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_PhiSq_sub_mul_cos hΦe hΦ2 hFT, mul_comm τ (Real.log n)]
  field_simp


/-- `(Φ² ⋆ v)(τ) = ∫ Φ(x)² v(τ + x) dx` for even `Φ`. -/
theorem convSq_eq_shift (hΦe : ∀ x, Φ (-x) = Φ x) (v : ℝ → ℝ) (τ : ℝ) :
    convSq Φ v τ = ∫ x, Φ x ^ 2 * v (τ + x) := by
  unfold convSq
  rw [← integral_add_left_eq_self (fun τ' => Φ (τ - τ') ^ 2 * v τ') τ]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    simp only [show τ - (τ + x) = -x by ring, hΦe])

/-- **Slowly varying densities pass through `Φ²`.** If `|v(t + r) − v(t)| ≤ (K₁|r| + K₂r²)/t`, then
`|(Φ² ⋆ v)(t) − v(t) ∫Φ²| ≤ (K₁ ∫Φ²|x| + K₂ ∫Φ²x²)/t`. -/
theorem abs_convSq_sub_le (hΦe : ∀ x, Φ (-x) = Φ x) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦ2a : Integrable fun x => Φ x ^ 2 * |x|) (hΦ2s : Integrable fun x => Φ x ^ 2 * x ^ 2)
    (hΦc : Continuous Φ) (hvc : Continuous v) {K₁ K₂ t : ℝ}
    (hinc : ∀ r, |v (t + r) - v t| ≤ (K₁ * |r| + K₂ * r ^ 2) / t) :
    |convSq Φ v t - v t * ∫ x, Φ x ^ 2|
      ≤ (K₁ * (∫ x, Φ x ^ 2 * |x|) + K₂ * ∫ x, Φ x ^ 2 * x ^ 2) / t := by
  have hmaj : Integrable fun x => (K₁ * (Φ x ^ 2 * |x|) + K₂ * (Φ x ^ 2 * x ^ 2)) / t :=
    ((hΦ2a.const_mul K₁).add (hΦ2s.const_mul K₂)).div_const t
  have hdiff : Integrable fun x => Φ x ^ 2 * (v (t + x) - v t) := by
    refine hmaj.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc Φ x ^ 2 * |v (t + x) - v t| ≤ Φ x ^ 2 * ((K₁ * |x| + K₂ * x ^ 2) / t) :=
          mul_le_mul_of_nonneg_left (hinc x) (sq_nonneg _)
      _ = (K₁ * (Φ x ^ 2 * |x|) + K₂ * (Φ x ^ 2 * x ^ 2)) / t := by ring
  have hfull : Integrable fun x => Φ x ^ 2 * v (t + x) :=
    (hdiff.add (hΦ2.const_mul (v t))).congr (Eventually.of_forall fun x => by
      simp only [Pi.add_apply]; ring)
  have e : convSq Φ v t - v t * ∫ x, Φ x ^ 2 = ∫ x, Φ x ^ 2 * (v (t + x) - v t) := by
    rw [convSq_eq_shift hΦe, ← integral_const_mul, ← integral_sub hfull (hΦ2.const_mul (v t))]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |Φ x ^ 2 * (v (t + x) - v t)|
      ≤ ∫ x, (K₁ * (Φ x ^ 2 * |x|) + K₂ * (Φ x ^ 2 * x ^ 2)) / t := by
        refine integral_mono hdiff.abs hmaj fun x => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc Φ x ^ 2 * |v (t + x) - v t| ≤ Φ x ^ 2 * ((K₁ * |x| + K₂ * x ^ 2) / t) :=
              mul_le_mul_of_nonneg_left (hinc x) (sq_nonneg _)
          _ = (K₁ * (Φ x ^ 2 * |x|) + K₂ * (Φ x ^ 2 * x ^ 2)) / t := by ring
    _ = (K₁ * (∫ x, Φ x ^ 2 * |x|) + K₂ * ∫ x, Φ x ^ 2 * x ^ 2) / t := by
        rw [integral_div, integral_add (hΦ2a.const_mul K₁) (hΦ2s.const_mul K₂), integral_const_mul,
          integral_const_mul]

/-- **Decaying densities stay decaying.** If `|v(τ')| ≤ B/(1 + |τ'|)`, then
`|(Φ² ⋆ v)(τ)| ≤ B (∫Φ² + ∫Φ²|x|)/(1 + |τ|)`. -/
theorem abs_convSq_le_of_decay (hΦe : ∀ x, Φ (-x) = Φ x) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦ2a : Integrable fun x => Φ x ^ 2 * |x|) {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ τ', |v τ'| ≤ B / (1 + |τ'|)) (τ : ℝ) :
    |convSq Φ v τ| ≤ B * ((∫ x, Φ x ^ 2) + ∫ x, Φ x ^ 2 * |x|) / (1 + |τ|) := by
  have hτ : 0 < 1 + |τ| := by positivity
  have hpt : ∀ x, |Φ x ^ 2 * v (τ + x)| ≤ B / (1 + |τ|) * (Φ x ^ 2 + Φ x ^ 2 * |x|) := by
    intro x
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hpe : 1 + |τ| ≤ (1 + |τ + x|) * (1 + |x|) := by
      have h1 : |τ| ≤ |τ + x| + |x| := by
        have := abs_sub (τ + x) x; simp only [add_sub_cancel_right] at this; linarith
      nlinarith [abs_nonneg (τ + x), abs_nonneg x]
    have hvx : |v (τ + x)| ≤ B * (1 + |x|) / (1 + |τ|) := by
      refine (hv (τ + x)).trans ?_
      rw [div_le_div_iff₀ (by positivity) hτ]
      nlinarith [mul_le_mul_of_nonneg_left hpe hB]
    calc Φ x ^ 2 * |v (τ + x)| ≤ Φ x ^ 2 * (B * (1 + |x|) / (1 + |τ|)) :=
          mul_le_mul_of_nonneg_left hvx (sq_nonneg _)
      _ = B / (1 + |τ|) * (Φ x ^ 2 + Φ x ^ 2 * |x|) := by ring
  have hmaj : Integrable fun x => B / (1 + |τ|) * (Φ x ^ 2 + Φ x ^ 2 * |x|) :=
    (hΦ2.add hΦ2a).const_mul _
  rw [convSq_eq_shift hΦe]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |Φ x ^ 2 * v (τ + x)| ≤ ∫ x, B / (1 + |τ|) * (Φ x ^ 2 + Φ x ^ 2 * |x|) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hmaj
          (Eventually.of_forall hpt)
    _ = B * ((∫ x, Φ x ^ 2) + ∫ x, Φ x ^ 2 * |x|) / (1 + |τ|) := by
        rw [integral_const_mul, integral_add hΦ2 hΦ2a]; ring

end Convolution

/-! ## 2. Fubini under linear growth -/

/-- `q ↦ f(q.1) k(q.1 − q.2)` is integrable on `ℝ²` when `f` and `k` are. -/
theorem integrable_mul_comp_sub {f k : ℝ → ℝ} (hf : Integrable f) (hk : Integrable k) :
    Integrable fun q : ℝ × ℝ => f q.1 * k (q.1 - q.2) := by
  have h := (Integrable.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hf
    hk.comp_neg).swap
  refine h.congr (Eventually.of_forall fun q => ?_)
  simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, ContinuousLinearMap.mul_apply']
  rw [neg_sub]

section Fubini

variable {Ω u v : ℝ → ℝ} {M : ℝ}

theorem integrable_smoothForm_integrand (hΦc : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦ2a : Integrable fun x => Φ x ^ 2 * |x|) (hΩc : Continuous Ω) (huc : Continuous u)
    (hvc : Continuous v) (hΩu : Integrable fun τ => Ω τ * u τ)
    (hvb : ∀ τ τ', Ω τ ≠ 0 → |v τ'| ≤ M * (1 + |τ - τ'|)) :
    Integrable fun q : ℝ × ℝ => Ω q.1 * Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2 := by
  have hk : Integrable fun x => M * (Φ x ^ 2 + Φ x ^ 2 * |x|) := (hΦ2.add hΦ2a).const_mul M
  have hdom := integrable_mul_comp_sub hΩu.abs hk
  refine hdom.mono' (by fun_prop) (Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  by_cases hΩ : Ω q.1 = 0
  · simp [hΩ]
  · have h := hvb q.1 q.2 hΩ
    calc |Ω q.1 * Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2|
        = |Ω q.1 * u q.1| * Φ (q.1 - q.2) ^ 2 * |v q.2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Φ (q.1 - q.2)))]; ring
      _ ≤ |Ω q.1 * u q.1| * Φ (q.1 - q.2) ^ 2 * (M * (1 + |q.1 - q.2|)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = |Ω q.1 * u q.1| * (M * (Φ (q.1 - q.2) ^ 2 + Φ (q.1 - q.2) ^ 2 * |q.1 - q.2|)) := by ring

/-- **Fubini for `𝓜_Ω[u, v]` with `v` of linear growth on the support of `Ω`.** -/
theorem smoothForm_eq_smoothPair (hΦc : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦ2a : Integrable fun x => Φ x ^ 2 * |x|) (hΩc : Continuous Ω) (huc : Continuous u)
    (hvc : Continuous v) (hΩu : Integrable fun τ => Ω τ * u τ)
    (hvb : ∀ τ τ', Ω τ ≠ 0 → |v τ'| ≤ M * (1 + |τ - τ'|)) :
    smoothForm Φ Ω u v = smoothPair Φ Ω u v := by
  have hint := integrable_smoothForm_integrand hΦc hΦ2 hΦ2a hΩc huc hvc hΩu hvb
  unfold smoothForm smoothPair convSq
  rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun τ' => by simp only; ring)

/-- The iterated integrand `Ω u (Φ² ⋆ v)` is integrable under the same hypotheses. -/
theorem integrable_window_mul_convSq (hΦc : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦ2a : Integrable fun x => Φ x ^ 2 * |x|) (hΩc : Continuous Ω) (huc : Continuous u)
    (hvc : Continuous v) (hΩu : Integrable fun τ => Ω τ * u τ)
    (hvb : ∀ τ τ', Ω τ ≠ 0 → |v τ'| ≤ M * (1 + |τ - τ'|)) :
    Integrable fun τ => Ω τ * u τ * convSq Φ v τ := by
  have hint := integrable_smoothForm_integrand hΦc hΦ2 hΦ2a hΩc huc hvc hΩu hvb
  rw [Measure.volume_eq_prod] at hint
  refine hint.integral_prod_left.congr (Eventually.of_forall fun τ => ?_)
  simp only [convSq]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun τ' => by simp only; ring)

end Fubini

/-! ## 3. The exact coalescent kernel -/

section Kernel

variable {g Ω : ℝ → ℝ}

theorem integrable_window_mul_cos (hΩ : Integrable Ω) (θ : ℝ) :
    Integrable fun τ => Ω τ * Real.cos (τ * θ) :=
  hΩ.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun τ => by
    simpa using Real.abs_cos_le_one (τ * θ))

/-- **The smooth-window prime–prime form is an exact pair sum.**
`∫ Ω P_X (Φ² ⋆ P_X) = π⁻¹ Σ_{n,m} a_n a_m g(log m) (Ω̂(log n − log m) + Ω̂(log n + log m))`. -/
theorem smoothPair_PX_PX_eq (hΦe : ∀ x, Φ (-x) = Φ x)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y)
    (hΩ : Integrable Ω) (X : ℝ) :
    smoothPair Φ Ω (Zeta23.PX X) (Zeta23.PX X)
      = (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m * g (Real.log m)
          * (cosTransform Ω (Real.log n - Real.log m) + cosTransform Ω (Real.log n + Real.log m)) := by
  unfold smoothPair convSq
  simp_rw [integral_PhiSq_sub_mul_PX hΦe hΦ2 hFT X]
  -- pointwise expansion into the double sum
  have hpt : ∀ τ, Ω τ * Zeta23.PX X τ * (-2 * primeDirichletCos g X τ)
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (1 / π) * (acoef n * acoef m * g (Real.log m))
        * (Ω τ * Real.cos (τ * (Real.log n - Real.log m))
          + Ω τ * Real.cos (τ * (Real.log n + Real.log m))) := by
    intro τ
    rw [PX_eq]
    unfold primeDirichletCos ycoef
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [show τ * (Real.log n - Real.log m) = τ * Real.log n - τ * Real.log m by ring,
      show τ * (Real.log n + Real.log m) = τ * Real.log n + τ * Real.log m by ring,
      Real.cos_sub, Real.cos_add]
    field_simp
    ring
  have hint : ∀ n m : ℕ, Integrable fun τ => (1 / π) * (acoef n * acoef m * g (Real.log m))
      * (Ω τ * Real.cos (τ * (Real.log n - Real.log m))
        + Ω τ * Real.cos (τ * (Real.log n + Real.log m))) := fun n m =>
    ((integrable_window_mul_cos hΩ _).add (integrable_window_mul_cos hΩ _)).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, integral_add (integrable_window_mul_cos hΩ _)
    (integrable_window_mul_cos hΩ _)]
  unfold cosTransform
  ring

/-- `Ω̂(0) = ∫ Ω`. -/
theorem cosTransform_zero (Ω : ℝ → ℝ) : cosTransform Ω 0 = ∫ τ, Ω τ := by
  unfold cosTransform; simp

/-- **Decay of the window transform.** For `Ω ∈ C^k` vanishing off `[a, b]` and `θ ≠ 0`,
`|Ω̂(θ)| ≤ ‖Ω^{(k)}‖₁ / |θ|^k`. -/
theorem abs_cosTransform_le {a b : ℝ} (hab : a ≤ b) {k : ℕ} (hΩk : ContDiff ℝ k Ω)
    (hz : ∀ τ ∉ Icc a b, Ω τ = 0) {θ : ℝ} (hθ : θ ≠ 0) :
    |cosTransform Ω θ| ≤ (∫ τ in (a - 1)..(b + 1), |iteratedDeriv k Ω τ|) / |θ| ^ k := by
  have h := abs_intervalIntegral_mul_sin_le hab k hΩk hz hθ (π / 2)
  refine le_of_eq_of_le ?_ h
  unfold cosTransform
  have hle : a - 1 ≤ b + 1 := by linarith
  congr 1
  rw [intervalIntegral.integral_of_le hle, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun τ hτ => by
      have : τ ∉ Icc a b := fun h => hτ ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [hz τ this, zero_mul])]
  exact integral_congr_ae (Eventually.of_forall fun τ => by
    simp only; rw [show θ * τ + π / 2 = τ * θ + π / 2 by ring, Real.sin_add_pi_div_two])

/-- The coalescent pair sum: off-diagonal prime pairs with `|log n − log m| ≤ θ₀`, against the
exact kernel `π⁻¹ a_n a_m g(log m) Ω̂(log n − log m)`. -/
def coalSum (Ω g : ℝ → ℝ) (X θ₀ : ℝ) : ℝ :=
  (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ then
      acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m) else 0

/-- **The prime–prime channel localizes to the coalescent band.** For `Ω ∈ C^k` vanishing off
`[a, b]`, `0 ≤ g ≤ L`, `θ₀ > 0` and `D = ∫_{a−1}^{b+1} |Ω^{(k)}|`:
`∫ Ω P_X (Φ² ⋆ P_X) ≤ π⁻¹ (∫Ω) Σ a_n² g(log n) + coalSum + π⁻¹ L D (θ₀^{−k} + 1) (Σ a_n)²`.
The diagonal is exact, pairs with `|log(n/m)| > θ₀` pay `D/θ₀^k`, and sum frequencies
`log n + log m ≥ 2 log 2 > 1` pay `D`. -/
theorem smoothPair_PX_PX_le (hΦe : ∀ x, Φ (-x) = Φ x)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y)
    (hΩ : Integrable Ω) {a b : ℝ} (hab : a ≤ b) {k : ℕ} (hΩk : ContDiff ℝ k Ω)
    (hz : ∀ τ ∉ Icc a b, Ω τ = 0) {L θ₀ : ℝ} (hg0 : ∀ y, 0 ≤ g y) (hgL : ∀ y, g y ≤ L)
    (hθ₀ : 0 < θ₀) (X : ℝ) :
    smoothPair Φ Ω (Zeta23.PX X) (Zeta23.PX X)
      ≤ (1 / π) * (∫ τ, Ω τ) * ∑ n ∈ primeRange X, acoef n ^ 2 * g (Real.log n)
        + coalSum Ω g X θ₀
        + (1 / π) * (L * (∫ τ in (a - 1)..(b + 1), |iteratedDeriv k Ω τ|)) * ((θ₀ ^ k)⁻¹ + 1)
          * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
  rw [smoothPair_PX_PX_eq hΦe hΦ2 hFT hΩ X]
  set D := ∫ τ in (a - 1)..(b + 1), |iteratedDeriv k Ω τ| with hD
  have hD0 : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
  have hL0 : 0 ≤ L := (hg0 0).trans (hgL 0)
  have hθk : 0 < θ₀ ^ k := pow_pos hθ₀ k
  have hpt : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      acoef n * acoef m * g (Real.log m)
          * (cosTransform Ω (Real.log n - Real.log m) + cosTransform Ω (Real.log n + Real.log m))
        ≤ ((if n = m then acoef n ^ 2 * g (Real.log n) * ∫ τ, Ω τ else 0)
          + (if n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ then
              acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m) else 0))
          + L * D * ((θ₀ ^ k)⁻¹ + 1) * (acoef n * acoef m) := by
    intro n hn m hm
    have hab0 : 0 ≤ acoef n * acoef m := mul_nonneg (acoef_nonneg n) (acoef_nonneg m)
    have hc0 : 0 ≤ acoef n * acoef m * g (Real.log m) := mul_nonneg hab0 (hg0 _)
    have hcL : acoef n * acoef m * g (Real.log m) ≤ acoef n * acoef m * L :=
      mul_le_mul_of_nonneg_left (hgL _) hab0
    -- the sum frequency
    have hsum : acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n + Real.log m)
        ≤ L * D * (acoef n * acoef m) := by
      rcases acoef_eq_zero_or_two_le hn with hn0 | hn2
      · rw [hn0]; simp only [zero_mul, mul_zero, le_refl]
      rcases acoef_eq_zero_or_two_le hm with hm0 | hm2
      · rw [hm0]; simp only [zero_mul, mul_zero, le_refl]
      have h2 : (1:ℝ) ≤ Real.log n + Real.log m := by
        have := Real.log_two_gt_d9
        have hn' : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
        have hm' : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
        linarith
      have hdec := abs_cosTransform_le hab hΩk hz (θ := Real.log n + Real.log m) (by linarith)
      have hk1 : 1 ≤ |Real.log n + Real.log m| ^ k :=
        one_le_pow₀ (by rw [abs_of_pos (by linarith)]; exact h2)
      have hC : |cosTransform Ω (Real.log n + Real.log m)| ≤ D := hdec.trans (div_le_self hD0 hk1)
      calc acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n + Real.log m)
          ≤ acoef n * acoef m * g (Real.log m) * |cosTransform Ω (Real.log n + Real.log m)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hc0
        _ ≤ acoef n * acoef m * L * D := mul_le_mul hcL hC (abs_nonneg _) (by positivity)
        _ = L * D * (acoef n * acoef m) := by ring
    -- the difference frequency
    have hdiff : acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
        ≤ ((if n = m then acoef n ^ 2 * g (Real.log n) * ∫ τ, Ω τ else 0)
          + (if n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ then
              acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m) else 0))
          + L * D * (θ₀ ^ k)⁻¹ * (acoef n * acoef m) := by
      have hext : 0 ≤ L * D * (θ₀ ^ k)⁻¹ * (acoef n * acoef m) := by positivity
      by_cases hnm : n = m
      · subst hnm
        rw [if_pos rfl, if_neg (fun h => h.1 rfl), add_zero, sub_self, cosTransform_zero]
        nlinarith [hext]
      · by_cases hθ : |Real.log n - Real.log m| ≤ θ₀
        · rw [if_neg hnm, if_pos ⟨hnm, hθ⟩, zero_add]; linarith
        · rw [if_neg hnm, if_neg (fun h => hθ h.2), zero_add, zero_add]
          replace hθ := not_le.mp hθ
          have hne : Real.log n - Real.log m ≠ 0 := fun h => by
            rw [h, abs_zero] at hθ; linarith
          have hdec := abs_cosTransform_le hab hΩk hz hne
          have hk : θ₀ ^ k ≤ |Real.log n - Real.log m| ^ k := pow_le_pow_left₀ hθ₀.le hθ.le k
          have hC : |cosTransform Ω (Real.log n - Real.log m)| ≤ D * (θ₀ ^ k)⁻¹ := by
            refine hdec.trans ?_
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (inv_anti₀ hθk hk) hD0
          calc acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
              ≤ acoef n * acoef m * g (Real.log m) * |cosTransform Ω (Real.log n - Real.log m)| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) hc0
            _ ≤ acoef n * acoef m * L * (D * (θ₀ ^ k)⁻¹) :=
                mul_le_mul hcL hC (abs_nonneg _) (by positivity)
            _ = L * D * (θ₀ ^ k)⁻¹ * (acoef n * acoef m) := by ring
    have e : L * D * ((θ₀ ^ k)⁻¹ + 1) * (acoef n * acoef m)
        = L * D * (θ₀ ^ k)⁻¹ * (acoef n * acoef m) + L * D * (acoef n * acoef m) := by ring
    rw [mul_add, e]; linarith
  have hS := Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hpt n hn m hm
  simp only [Finset.sum_add_distrib] at hS
  have hdiag : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      (if n = m then acoef n ^ 2 * g (Real.log n) * ∫ τ, Ω τ else 0)
      = (∫ τ, Ω τ) * ∑ n ∈ primeRange X, acoef n ^ 2 * g (Real.log n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_ite_eq (primeRange X) n, if_pos hn]; ring
  have hsq : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, L * D * ((θ₀ ^ k)⁻¹ + 1) * (acoef n * acoef m)
      = L * D * ((θ₀ ^ k)⁻¹ + 1) * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
  rw [hdiag, hsq] at hS
  unfold coalSum
  refine (mul_le_mul_of_nonneg_left hS (by positivity : (0:ℝ) ≤ 1 / π)).trans (le_of_eq ?_)
  ring

end Kernel

/-! ## 4. Cosine integrals of slowly varying windows -/

/-- **Half-period shift.** `|∫ f(τ) cos(τy) dτ| ≤ ½ ∫ |f(τ) − f(τ − π/y)| dτ`. -/
theorem abs_integral_mul_cos_le_shift {f : ℝ → ℝ} (hf : Integrable f) {y : ℝ} (hy : y ≠ 0) :
    |∫ τ, f τ * Real.cos (τ * y)| ≤ (1 / 2) * ∫ τ, |f τ - f (τ - π / y)| := by
  set δ := π / y with hδ
  have hcos : ∀ τ, Real.cos ((τ - δ) * y) = -Real.cos (τ * y) := fun τ => by
    rw [show (τ - δ) * y = τ * y - π by rw [hδ]; field_simp, Real.cos_sub_pi]
  have hI : Integrable fun τ => f τ * Real.cos (τ * y) :=
    hf.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun τ => by
      simpa using Real.abs_cos_le_one (τ * y))
  have hfs : Integrable fun τ => f (τ - δ) := hf.comp_sub_right δ
  have hIs : Integrable fun τ => f (τ - δ) * Real.cos (τ * y) :=
    hfs.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun τ => by
      simpa using Real.abs_cos_le_one (τ * y))
  have hshift : ∫ τ, f τ * Real.cos (τ * y) = -∫ τ, f (τ - δ) * Real.cos (τ * y) := by
    rw [← integral_sub_right_eq_self (fun τ => f τ * Real.cos (τ * y)) δ, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun τ => by simp only [hcos]; ring)
  have h2 : 2 * ∫ τ, f τ * Real.cos (τ * y) = ∫ τ, (f τ - f (τ - δ)) * Real.cos (τ * y) := by
    rw [show (fun τ => (f τ - f (τ - δ)) * Real.cos (τ * y))
        = fun τ => f τ * Real.cos (τ * y) - f (τ - δ) * Real.cos (τ * y) by funext τ; ring,
      integral_sub hI hIs]
    linarith
  have habs : |∫ τ, (f τ - f (τ - δ)) * Real.cos (τ * y)| ≤ ∫ τ, |f τ - f (τ - δ)| := by
    have hD : Integrable fun τ => (f τ - f (τ - δ)) * Real.cos (τ * y) :=
      (hI.sub hIs).congr (Eventually.of_forall fun τ => by simp only [Pi.sub_apply]; ring)
    refine (abs_integral_le_integral_abs).trans (integral_mono hD.abs (hf.sub hfs).abs fun τ => ?_)
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have : |2 * ∫ τ, f τ * Real.cos (τ * y)| ≤ ∫ τ, |f τ - f (τ - δ)| := by rw [h2]; exact habs
  rw [abs_mul, abs_two] at this
  linarith

/-- **The cosine integral of a slowly varying windowed density.** Let `0 ≤ Ω ≤ 1` be `ℓ`-Lipschitz
and vanish off `[s₀, s₁]`, `s₀ > 0`, and let `|v| ≤ M` on `[s₀, s₁ + δ]` and
`|v(t + r) − v(t)| ≤ (K₁|r| + K₂r²)/t` for `t ≥ s₀`. Then for `y > 0`, `δ = π/y`:
`|∫ Ω v cos(τy)| ≤ ½ (s₁ − s₀ + δ)(ℓδM + (K₁δ + K₂δ²)/s₀)`. -/
theorem abs_integral_window_mul_cos_le {Ω v : ℝ → ℝ} {s₀ s₁ ℓ M K₁ K₂ y : ℝ} (hs : s₀ ≤ s₁)
    (hs₀ : 0 < s₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hΩc : Continuous Ω) (hvc : Continuous v) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hΩ1 : ∀ τ, Ω τ ≤ 1) (hΩL : ∀ s t, |Ω s - Ω t| ≤ ℓ * |s - t|)
    (hΩS : ∀ τ, τ ∉ Icc s₀ s₁ → Ω τ = 0) (hy : 0 < y)
    (hvM : ∀ τ ∈ Icc s₀ (s₁ + π / y), |v τ| ≤ M)
    (hinc : ∀ t, s₀ ≤ t → ∀ r, |v (t + r) - v t| ≤ (K₁ * |r| + K₂ * r ^ 2) / t) :
    |∫ τ, Ω τ * v τ * Real.cos (τ * y)|
      ≤ (1 / 2) * ((s₁ - s₀ + π / y) * (ℓ * (π / y) * M + (K₁ * (π / y) + K₂ * (π / y) ^ 2) / s₀)) := by
  set δ := π / y with hδ
  have hδ0 : 0 < δ := by positivity
  set f : ℝ → ℝ := fun τ => Ω τ * v τ with hf
  have hfc : Continuous f := hΩc.mul hvc
  have hfS : ∀ τ, τ ∉ Icc s₀ s₁ → f τ = 0 := fun τ hτ => by simp only [hf, hΩS τ hτ, zero_mul]
  have hfi : Integrable f := by
    refine (hfc.integrableOn_Icc (a := s₀) (b := s₁)).integrable_of_forall_notMem_eq_zero ?_
    exact fun τ hτ => hfS τ hτ
  have h1 := abs_integral_mul_cos_le_shift hfi hy.ne'
  -- the shifted difference vanishes off `[s₀, s₁ + δ]` and is pointwise small on it
  set E := ℓ * δ * M + (K₁ * δ + K₂ * δ ^ 2) / s₀ with hE
  have hpt : ∀ τ, |f τ - f (τ - δ)| ≤ Set.indicator (Icc s₀ (s₁ + δ)) (fun _ => E) τ := by
    intro τ
    by_cases hτ : τ ∈ Icc s₀ (s₁ + δ)
    · rw [Set.indicator_of_mem hτ]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hvM τ hτ)
      have hvτ := hvM τ hτ
      have e : f τ - f (τ - δ) = (Ω τ - Ω (τ - δ)) * v τ + Ω (τ - δ) * (v τ - v (τ - δ)) := by
        simp only [hf]; ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        have hl := hΩL τ (τ - δ)
        rw [show τ - (τ - δ) = δ by ring, abs_of_pos hδ0] at hl
        exact mul_le_mul hl hvτ (abs_nonneg _) ((abs_nonneg _).trans hl)
      · by_cases hz : Ω (τ - δ) = 0
        · rw [hz, zero_mul, abs_zero]; positivity
        · have hmem : τ - δ ∈ Icc s₀ s₁ := by
            by_contra hn; exact hz (hΩS _ hn)
          have hinc' := hinc (τ - δ) hmem.1 δ
          rw [sub_add_cancel, abs_of_pos hδ0] at hinc'
          rw [abs_mul, abs_of_nonneg (hΩ0 _)]
          have hK : (K₁ * δ + K₂ * δ ^ 2) / (τ - δ) ≤ (K₁ * δ + K₂ * δ ^ 2) / s₀ :=
            div_le_div_of_nonneg_left (by positivity) hs₀ hmem.1
          calc Ω (τ - δ) * |v τ - v (τ - δ)| ≤ 1 * ((K₁ * δ + K₂ * δ ^ 2) / s₀) :=
                mul_le_mul (hΩ1 _) (hinc'.trans hK) (abs_nonneg _) zero_le_one
            _ = (K₁ * δ + K₂ * δ ^ 2) / s₀ := one_mul _
    · rw [Set.indicator_of_notMem hτ]
      have h0 : f τ = 0 := hfS τ fun h => hτ ⟨h.1, h.2.trans (by linarith)⟩
      have h0' : f (τ - δ) = 0 := hfS (τ - δ) fun h => hτ ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [h0, h0', sub_zero, abs_zero]
  have hind : Integrable (Set.indicator (Icc s₀ (s₁ + δ)) fun _ => E) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have h2 : ∫ τ, |f τ - f (τ - δ)| ≤ (s₁ - s₀ + δ) * E := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun τ => abs_nonneg _) hind
      (Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  calc |∫ τ, Ω τ * v τ * Real.cos (τ * y)| = |∫ τ, f τ * Real.cos (τ * y)| := rfl
    _ ≤ (1 / 2) * ∫ τ, |f τ - f (τ - δ)| := h1
    _ ≤ (1 / 2) * ((s₁ - s₀ + δ) * E) := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-! ## 5. The Lorentz mean square of a weighted prime polynomial -/

section WeightedMeanSquare

variable {w : ℝ → ℝ} {B : ℝ}

theorem continuous_primeDirichletCos (w : ℝ → ℝ) (X : ℝ) : Continuous (primeDirichletCos w X) := by
  unfold primeDirichletCos; fun_prop

theorem abs_primeDirichletCos_le (hw : ∀ y, |w y| ≤ B) (X τ : ℝ) :
    |primeDirichletCos w X τ| ≤ B * ∑ n ∈ primeRange X, acoef n := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hw 0)
  unfold primeDirichletCos
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (acoef_nonneg n)]
  calc acoef n * |w (Real.log n)| * |Real.cos (τ * Real.log n)| ≤ acoef n * B * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hw _) (acoef_nonneg n)) (Real.abs_cos_le_one _)
          (abs_nonneg _) (mul_nonneg (acoef_nonneg n) hB)
    _ = B * acoef n := by ring

theorem primeDirichletCos_sq_eq (w : ℝ → ℝ) (X τ : ℝ) :
    primeDirichletCos w X τ ^ 2 = (1 / 2) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      acoef n * w (Real.log n) * (acoef m * w (Real.log m))
        * (Real.cos ((Real.log n - Real.log m) * τ) + Real.cos ((Real.log n + Real.log m) * τ)) := by
  unfold primeDirichletCos
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show (Real.log n - Real.log m) * τ = τ * Real.log n - τ * Real.log m by ring,
    show (Real.log n + Real.log m) * τ = τ * Real.log n + τ * Real.log m by ring,
    Real.cos_sub, Real.cos_add]
  ring

/-- The Fejér mean square of `C_w` is an exact pair sum with the triangle kernel. -/
theorem integral_fejer_mul_primeDirichletCos_sq {b : ℝ} (hb : 0 < b) (c : ℝ) (w : ℝ → ℝ) (X : ℝ) :
    ∫ τ, fejerBandProfile b (τ - c) * primeDirichletCos w X τ ^ 2
      = π * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * w (Real.log n) * (acoef m * w (Real.log m))
          * (triangleFn b (Real.log n - Real.log m) * Real.cos ((Real.log n - Real.log m) * c)
            + triangleFn b (Real.log n + Real.log m) * Real.cos ((Real.log n + Real.log m) * c)) := by
  have hpt : ∀ τ, fejerBandProfile b (τ - c) * primeDirichletCos w X τ ^ 2
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          (1 / 2) * (acoef n * w (Real.log n) * (acoef m * w (Real.log m)))
        * (fejerBandProfile b (τ - c) * Real.cos ((Real.log n - Real.log m) * τ)
          + fejerBandProfile b (τ - c) * Real.cos ((Real.log n + Real.log m) * τ)) := by
    intro τ
    rw [primeDirichletCos_sq_eq]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  have hint : ∀ n m : ℕ, Integrable fun τ =>
      (1 / 2) * (acoef n * w (Real.log n) * (acoef m * w (Real.log m)))
      * (fejerBandProfile b (τ - c) * Real.cos ((Real.log n - Real.log m) * τ)
        + fejerBandProfile b (τ - c) * Real.cos ((Real.log n + Real.log m) * τ)) := fun n m =>
    ((integrable_fejer_shift_mul_cos hb c _).add (integrable_fejer_shift_mul_cos hb c _)).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun m _ => hint n m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, integral_add (integrable_fejer_shift_mul_cos hb c _)
    (integrable_fejer_shift_mul_cos hb c _), integral_fejer_shift_mul_cos hb,
    integral_fejer_shift_mul_cos hb]
  ring

/-- **Fejér mean square of a weighted prime polynomial.** For `|w| ≤ B`, `0 < b ≤ 1`, `X ≥ 1`:
`∫ F_b(τ − c) C_w(τ)² ≤ π B² √e log X (3b ψ(X) + Σ_{n≤X} Λ(n)/n)`. -/
theorem integral_fejer_mul_primeDirichletCos_sq_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (c : ℝ)
    {X : ℝ} (hX : 1 ≤ X) (hw : ∀ y, |w y| ≤ B) :
    ∫ τ, fejerBandProfile b (τ - c) * primeDirichletCos w X τ ^ 2
      ≤ π * (B ^ 2 * (Real.sqrt (Real.exp 1) * Real.log X
        * (3 * b * ∑ n ∈ primeRange X, (Λ n : ℝ) + ∑ n ∈ primeRange X, (Λ n : ℝ) / n))) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hw 0)
  rw [integral_fejer_mul_primeDirichletCos_sq hb]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  have hterm : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      acoef n * w (Real.log n) * (acoef m * w (Real.log m))
          * (triangleFn b (Real.log n - Real.log m) * Real.cos ((Real.log n - Real.log m) * c)
            + triangleFn b (Real.log n + Real.log m) * Real.cos ((Real.log n + Real.log m) * c))
        ≤ B ^ 2 * (acoef n * acoef m * triangleFn b (Real.log n - Real.log m)) := by
    intro n hn m hm
    rcases acoef_eq_zero_or_two_le hn with hn0 | hn2
    · rw [hn0]; simp only [zero_mul, mul_zero, le_refl]
    rcases acoef_eq_zero_or_two_le hm with hm0 | hm2
    · rw [hm0]; simp only [zero_mul, mul_zero, le_refl]
    have hplus : triangleFn b (Real.log n + Real.log m) = 0 := by
      apply triangleFn_eq_zero hb
      have := Real.log_two_gt_d9
      have hn' : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
      have hm' : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
      rw [abs_of_pos (by linarith)]; linarith
    rw [hplus, zero_mul, add_zero]
    have ht0 := triangleFn_nonneg b (Real.log n - Real.log m)
    have hab := mul_nonneg (acoef_nonneg n) (acoef_nonneg m)
    calc acoef n * w (Real.log n) * (acoef m * w (Real.log m))
          * (triangleFn b (Real.log n - Real.log m) * Real.cos ((Real.log n - Real.log m) * c))
        ≤ |acoef n * w (Real.log n) * (acoef m * w (Real.log m))
          * (triangleFn b (Real.log n - Real.log m) * Real.cos ((Real.log n - Real.log m) * c))| :=
          le_abs_self _
      _ = acoef n * acoef m * triangleFn b (Real.log n - Real.log m)
          * (|w (Real.log n)| * |w (Real.log m)| * |Real.cos ((Real.log n - Real.log m) * c)|) := by
          simp only [abs_mul, abs_of_nonneg (acoef_nonneg n), abs_of_nonneg (acoef_nonneg m),
            abs_of_nonneg ht0]; ring
      _ ≤ acoef n * acoef m * triangleFn b (Real.log n - Real.log m) * (B * B * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul (hw _) (hw _) (abs_nonneg _) hB)
            (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)) (mul_nonneg hab ht0)
      _ = B ^ 2 * (acoef n * acoef m * triangleFn b (Real.log n - Real.log m)) := by ring
  calc ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * w (Real.log n) * (acoef m * w (Real.log m))
          * (triangleFn b (Real.log n - Real.log m) * Real.cos ((Real.log n - Real.log m) * c)
            + triangleFn b (Real.log n + Real.log m) * Real.cos ((Real.log n + Real.log m) * c))
      ≤ ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          B ^ 2 * (acoef n * acoef m * triangleFn b (Real.log n - Real.log m)) :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hterm n hn m hm
    _ = B ^ 2 * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * acoef m * triangleFn b (Real.log n - Real.log m) := by
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_sum_acoef_triangle_le hX hb hb1) (sq_nonneg B)

/-- **Lorentz-weighted mean value of a weighted prime polynomial.** For `|w| ≤ B`, `R ≥ 1`, `X ≥ 1`:
`∫ C_w(τ)² (1 + ((τ − c)/R)²)⁻¹ dτ ≤ 4π³ B² √e log X (3ψ(X) + R Σ_{n≤X} Λ(n)/n)`. -/
theorem integral_lorentz_mul_primeDirichletCos_sq_le {R : ℝ} (hR : 1 ≤ R) (c : ℝ) {X : ℝ}
    (hX : 1 ≤ X) (hw : ∀ y, |w y| ≤ B) :
    ∫ τ, lorentzW R c τ * primeDirichletCos w X τ ^ 2
      ≤ 4 * π ^ 3 * B ^ 2 * Real.sqrt (Real.exp 1) * Real.log X
        * (3 * ∑ n ∈ primeRange X, (Λ n : ℝ) + R * ∑ n ∈ primeRange X, (Λ n : ℝ) / n) := by
  have hR0 : 0 < R := by linarith
  have hb : 0 < 1 / R := by positivity
  have hb1 : 1 / R ≤ 1 := by rw [div_le_one hR0]; exact hR
  set M := B * ∑ n ∈ primeRange X, acoef n
  have hPb : ∀ τ, primeDirichletCos w X τ ^ 2 ≤ M ^ 2 := fun τ => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_primeDirichletCos_le hw X τ) 2
  have hPc := continuous_primeDirichletCos w X
  have hbdd : ∀ f : ℝ → ℝ, Integrable f → Integrable fun τ => f τ * primeDirichletCos w X τ ^ 2 :=
    fun f hf => hf.mul_bdd (c := M ^ 2) ((hPc.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hPb τ)
  have hF1 : Integrable fun τ => fejerBandProfile (1 / R) (τ - c) :=
    (integrable_fejerBandProfile hb).comp_sub_right c
  have hmono : ∫ τ, lorentzW R c τ * primeDirichletCos w X τ ^ 2
      ≤ ∫ τ, 2 * π ^ 2 * R * (fejerBandProfile (1 / R) (τ - c) * primeDirichletCos w X τ ^ 2
          + fejerBandProfile (1 / R) (τ - (c - π * R)) * primeDirichletCos w X τ ^ 2) := by
    refine integral_mono (hbdd _ (integrable_lorentzW hR0 c)) ?_ fun τ => ?_
    · exact ((hbdd _ hF1).add (hbdd _ ((integrable_fejerBandProfile hb).comp_sub_right
        (c - π * R)))).const_mul _
    · have h := lorentz_le_fejer_add_fejer hR0 c τ
      rw [show τ - (c - π * R) = τ - c + π * R by ring]
      have hP0 := sq_nonneg (primeDirichletCos w X τ)
      nlinarith [mul_le_mul_of_nonneg_right h hP0]
  refine hmono.trans ?_
  rw [integral_const_mul, integral_add (hbdd _ hF1)
    (hbdd _ ((integrable_fejerBandProfile hb).comp_sub_right (c - π * R)))]
  have e1 := integral_fejer_mul_primeDirichletCos_sq_le hb hb1 c hX hw
  have e2 := integral_fejer_mul_primeDirichletCos_sq_le hb hb1 (c - π * R) hX hw
  have hπ := Real.pi_pos
  calc 2 * π ^ 2 * R * ((∫ τ, fejerBandProfile (1 / R) (τ - c) * primeDirichletCos w X τ ^ 2)
        + ∫ τ, fejerBandProfile (1 / R) (τ - (c - π * R)) * primeDirichletCos w X τ ^ 2)
      ≤ 2 * π ^ 2 * R * (2 * (π * (B ^ 2 * (Real.sqrt (Real.exp 1) * Real.log X
          * (3 * (1 / R) * ∑ n ∈ primeRange X, (Λ n : ℝ) + ∑ n ∈ primeRange X, (Λ n : ℝ) / n))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 4 * π ^ 3 * B ^ 2 * Real.sqrt (Real.exp 1) * Real.log X
        * (3 * ∑ n ∈ primeRange X, (Λ n : ℝ) + R * ∑ n ∈ primeRange X, (Λ n : ℝ) / n) := by
        field_simp; ring

end WeightedMeanSquare

end GaloisForLFunctions.TransThresholdPairCorrelation
