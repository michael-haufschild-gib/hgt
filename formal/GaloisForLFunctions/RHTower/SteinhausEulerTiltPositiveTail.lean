import GaloisForLFunctions.RHTower.SteinhausEulerTiltPrimeSum
import GaloisForLFunctions.HTGeometry.PaleyZygmund

/-!
# A positive tail for the actual tilted prime sums

The Poisson law is not symmetric. Exact centering, the proved second/fourth
moments, an elementary absolute-moment truncation, and Paley–Zygmund applied
to the positive part give a uniform positive probability that the centered
prime sum exceeds a fixed positive multiple of its standard deviation.
The constants are independent of the cutoff. No probabilistic moment or
recurrence hypothesis is supplied to the public prime-sum conclusion.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace RHTower
open SteinhausModel

private theorem sq_le_truncated_abs_four {t : ℝ} (ht : 0 < t) (z : ℝ) :
    z ^ 2 ≤ t * |z| + z ^ 4 / t ^ 2 := by
  by_cases hz : |z| ≤ t
  · have hh := mul_le_mul_of_nonneg_right hz (abs_nonneg z)
    nlinarith [sq_abs z, div_nonneg (by positivity : 0 ≤ z ^ 4) (sq_nonneg t)]
  · have hh : t ^ 2 ≤ |z| ^ 2 := pow_le_pow_left₀ ht.le (le_of_not_ge hz) 2
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg z)
    have hd : z ^ 2 ≤ z ^ 4 / t ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos ht)]
      nlinarith [sq_abs z]
    exact hd.trans (le_add_of_nonneg_left (mul_nonneg ht.le (abs_nonneg z)))

private theorem positive_tail_of_centered_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hm : Measurable f) (hi : Integrable f μ)
    (h₂ : Integrable (fun x => f x ^ 2) μ) (h₄ : Integrable (fun x => f x ^ 4) μ)
    (hmean : ∫ x, f x ∂μ = 0) {C : ℝ} (hC : 0 < C)
    (hfour : ∫ x, f x ^ 4 ∂μ ≤ C * (∫ x, f x ^ 2 ∂μ) ^ 2)
    (hV : 0 < ∫ x, f x ^ 2 ∂μ) :
    1 / (128 * C) ≤ (μ {x | (∫ y, f y ^ 2 ∂μ) /
      (8 * Real.sqrt (2 * C * (∫ y, f y ^ 2 ∂μ))) < f x}).toReal := by
  let V := ∫ x, f x ^ 2 ∂μ
  let t := Real.sqrt (2 * C * V)
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = 2 * C * V := Real.sq_sqrt (by positivity)
  have habsi : Integrable (fun x => |f x|) μ := by simpa only [Real.norm_eq_abs] using hi.norm
  have hbound := integral_mono h₂ ((habsi.const_mul t).add (h₄.div_const (t ^ 2)))
    (fun x => sq_le_truncated_abs_four ht (f x))
  simp only [Pi.add_apply] at hbound
  have hsplit := integral_add (habsi.const_mul t) (h₄.div_const (t ^ 2))
  rw [hsplit, integral_const_mul, integral_div] at hbound
  have hrem : (∫ x, f x ^ 4 ∂μ) / t ^ 2 ≤ V / 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos ht), ht2]
    dsimp only [V]
    nlinarith
  have hfirst : V ≤ 2 * t * (∫ x, |f x| ∂μ) := by
    change V ≤ t * (∫ x, |f x| ∂μ) + (∫ x, f x ^ 4 ∂μ) / t ^ 2 at hbound
    linarith
  let g : Ω → ℝ := fun x => max (f x) 0
  have hg0 (x : Ω) : 0 ≤ g x := le_max_right _ _
  have hgm : Measurable g := hm.max measurable_const
  have hgi : Integrable g μ := by
    refine Integrable.mono' habsi hgm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hgsq (x : Ω) : g x ^ 2 ≤ f x ^ 2 := by
    by_cases hx : 0 ≤ f x
    · simp [g, max_eq_left hx]
    · simp [g, max_eq_right (le_of_not_ge hx), sq_nonneg]
  have hg₂ : Integrable (fun x => g x ^ 2) μ := by
    refine Integrable.mono' h₂ (hgm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgsq x
  have hg₂le : (∫ x, g x ^ 2 ∂μ) ≤ V := integral_mono hg₂ h₂ hgsq
  let A := ∫ x, g x ∂μ
  have hA0 : 0 ≤ A := integral_nonneg hg0
  have habs : (∫ x, |f x| ∂μ) = 2 * A := by
    simpa only [hmean, sub_zero, PosPart.posPart, A, g] using
      integral_abs_eq_two_mul_integral_posPart_sub_integral hi
  have hVA : V ≤ 4 * t * A := by rw [habs] at hfirst; nlinarith
  have ha : V / (8 * t) ≤ A / 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have ha0 : 0 ≤ V / (8 * t) := by positivity
  let E := {x | (1 / 2 : ℝ) * A < g x}
  let p := (μ E).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hpz := GaloisForLFunctions.HTGeometry.paley_zygmund hgm hg0 hgi hg₂
    (θ := 1 / 2) (by norm_num) (by norm_num)
  change (1 - 1 / 2 : ℝ) ^ 2 * A ^ 2 ≤ (∫ x, g x ^ 2 ∂μ) * p at hpz
  have hAp : A ^ 2 ≤ 4 * V * p := by
    have hmul := mul_le_mul_of_nonneg_right hg₂le hp0
    nlinarith
  have hVA2 := pow_le_pow_left₀ hV.le hVA 2
  change V ^ 2 ≤ (4 * t * A) ^ 2 at hVA2
  rw [mul_pow, mul_pow, ht2] at hVA2
  have hmul := mul_le_mul_of_nonneg_left hAp (by positivity : 0 ≤ 32 * C * V)
  have hcancel : V ^ 2 ≤ (128 * C * p) * V ^ 2 := by nlinarith
  have hp : 1 / (128 * C) ≤ p := by
    rw [div_le_iff₀ (by positivity)]
    have hh : 1 ≤ 128 * C * p := (mul_le_mul_iff_left₀ (sq_pos_of_pos hV)).mp (by
      simpa only [mul_one, one_mul, mul_comm (V ^ 2)] using hcancel)
    nlinarith
  have hsub : E ⊆ {x | V / (8 * t) < f x} := by
    intro x hx
    have hxA : A / 2 < g x := by
      change (1 / 2 : ℝ) * A < g x at hx
      linarith
    have hxg : V / (8 * t) < g x := lt_of_le_of_lt ha hxA
    change V / (8 * t) < f x
    by_cases hx0 : 0 ≤ f x
    · simpa [g, max_eq_left hx0] using hxg
    · have hh : g x = 0 := max_eq_right (le_of_not_ge hx0)
      rw [hh] at hxg
      exact False.elim (not_lt_of_ge ha0 hxg)
  exact hp.trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))

/-- The sum already has positive variance once prime two is included. -/
theorem integral_sq_steinhausEulerTiltPrimeSum_pos {N : ℕ} (hN : 3 ≤ N) :
    0 < ∫ ω, steinhausEulerTiltPrimeSum (Finset.range N) ω ^ 2 ∂steinhausEulerTiltProductMeasure := by
  have h := (integral_sq_steinhausEulerTiltPrimeSum_bounds (Finset.range N)).1
  have htwo : steinhausCriticalPrimeRadius 2 ^ 2 ≤
      ∑ n ∈ Finset.range N, steinhausCriticalPrimeRadius n ^ 2 :=
    Finset.single_le_sum (fun n _ => sq_nonneg _) (by simp; omega)
  rw [steinhausCriticalPrimeRadius_sq] at htwo
  norm_num at htwo
  linarith

/-- Explicit positive-tail bound from the proved arithmetic moment ratio. -/
theorem measure_steinhausEulerTiltPrimeSum_positive_tail {N : ℕ} (hN : 3 ≤ N) :
    1 / (128 * (3888 * 336 ^ 2 : ℝ)) ≤
      (steinhausEulerTiltProductMeasure {ω |
        (∫ η, steinhausEulerTiltPrimeSum (Finset.range N) η ^ 2 ∂steinhausEulerTiltProductMeasure) /
          (8 * Real.sqrt (2 * (3888 * 336 ^ 2 : ℝ) *
            (∫ η, steinhausEulerTiltPrimeSum (Finset.range N) η ^ 2 ∂steinhausEulerTiltProductMeasure))) <
          steinhausEulerTiltPrimeSum (Finset.range N) ω}).toReal := by
  exact positive_tail_of_centered_moments
    (measurable_steinhausEulerTiltPrimeSum (Finset.range N))
    (by simpa only [pow_one] using integrable_pow_steinhausEulerTiltPrimeSum (Finset.range N) 1)
    (integrable_pow_steinhausEulerTiltPrimeSum (Finset.range N) 2)
    (integrable_pow_steinhausEulerTiltPrimeSum (Finset.range N) 4)
    (integral_steinhausEulerTiltPrimeSum (Finset.range N)) (by positivity)
    (integral_four_steinhausEulerTiltPrimeSum_le_sq_second (Finset.range N))
    (integral_sq_steinhausEulerTiltPrimeSum_pos hN)

/-- Uniform signed escape at the standard-deviation scale for every cutoff at least three. -/
theorem exists_steinhausEulerTiltPrimeSum_positive_tail :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ N : ℕ, 3 ≤ N →
      δ ≤ (steinhausEulerTiltProductMeasure {ω |
        c * Real.sqrt (∫ η, steinhausEulerTiltPrimeSum (Finset.range N) η ^ 2
          ∂steinhausEulerTiltProductMeasure) < steinhausEulerTiltPrimeSum (Finset.range N) ω}).toReal := by
  let C : ℝ := 3888 * 336 ^ 2
  have hC : 0 < C := by positivity
  refine ⟨(8 * Real.sqrt (2 * C))⁻¹, (128 * C)⁻¹, by positivity, by positivity, ?_⟩
  intro N hN
  let V := ∫ η, steinhausEulerTiltPrimeSum (Finset.range N) η ^ 2 ∂steinhausEulerTiltProductMeasure
  have hV : 0 < V := integral_sq_steinhausEulerTiltPrimeSum_pos hN
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsC : 0 < Real.sqrt (2 * C) := Real.sqrt_pos.mpr (by positivity)
  have heq : V / (8 * Real.sqrt (2 * C * V)) = (8 * Real.sqrt (2 * C))⁻¹ * Real.sqrt V := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * C)]
    field_simp
    nlinarith [Real.sq_sqrt hV.le]
  have hh := measure_steinhausEulerTiltPrimeSum_positive_tail hN
  change 1 / (128 * C) ≤ (steinhausEulerTiltProductMeasure {ω |
    V / (8 * Real.sqrt (2 * C * V)) < steinhausEulerTiltPrimeSum (Finset.range N) ω}).toReal at hh
  simpa only [heq, one_div] using hh

end RHTower
