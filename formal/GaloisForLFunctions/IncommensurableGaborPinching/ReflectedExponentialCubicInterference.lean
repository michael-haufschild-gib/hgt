import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import GaloisForLFunctions.HTGeometry.HyperbolicModulus

/-!
# Cubic interference of reflected exponential evaluations

Exponential evaluations on `[-1,1]` have overlap `sinh z / z`, with its removable
value one at zero. Two reflected pairs produce a signed Gram matrix whose cubic
trace retains cross-height interference.
-/

open Complex Matrix Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- The normalized overlap of two exponential evaluations. -/
def exponentialOverlap (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sinh z / z

/-- The overlap is the actual integral on the interval with measure `du/2`. -/
theorem exponentialOverlap_eq_integral (z : ℂ) :
    exponentialOverlap z = (∫ u : ℝ in -1..1, Complex.exp (z * u)) / 2 := by
  by_cases hz : z = 0
  · subst z
    norm_num [exponentialOverlap]
  · rw [exponentialOverlap, if_neg hz, integral_exp_mul_complex hz, Complex.sinh]
    norm_num
    ring

@[simp] theorem exponentialOverlap_zero : exponentialOverlap 0 = 1 := by
  simp [exponentialOverlap]

@[simp] theorem exponentialOverlap_neg (z : ℂ) : exponentialOverlap (-z) = exponentialOverlap z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [exponentialOverlap, hz, Complex.sinh_neg]

@[simp] theorem exponentialOverlap_conj (z : ℂ) :
    exponentialOverlap (conj z) = conj (exponentialOverlap z) := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [exponentialOverlap, hz, Complex.sinh_conj]

/-- The overlap formula retains the literal exponential evaluation vectors. -/
theorem exponentialOverlap_eq_evaluation_inner (z w : ℂ) :
    exponentialOverlap (conj z + w) =
      (∫ u : ℝ in -1..1, conj (Complex.exp (z * u)) * Complex.exp (w * u)) / 2 := by
  rw [exponentialOverlap_eq_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [add_mul, Complex.exp_add, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal]

/-- Gram pattern of two reflected pairs, with real diagonal and height overlaps. -/
def reflectedEvaluationGram (g h : ℝ) (f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![g, 1, conj f, h;
     1, g, h, f;
     f, h, g, 1;
     h, conj f, 1, g]

/-- Reflection exchanges the two members of each pair. -/
def reflectedPairSwap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

private theorem reflectedPairSwap_mul_gram (g h : ℝ) (f : ℂ) :
    reflectedPairSwap * reflectedEvaluationGram g h f =
      !![1, (g : ℂ), (h : ℂ), f; (g : ℂ), 1, conj f, (h : ℂ); (h : ℂ), conj f, 1, (g : ℂ); f, (h : ℂ), (g : ℂ), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflectedPairSwap, reflectedEvaluationGram, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Exact cubic trace: cross-height interference survives reflection symmetry. -/
theorem reflectedEvaluation_cubic_trace (g h : ℝ) (f : ℂ) :
    (((reflectedPairSwap * reflectedEvaluationGram g h f) ^ 3).trace).re =
      4 + 12 * (g ^ 2 + h ^ 2 + (f ^ 2).re + 2 * g * h * f.re) := by
  rw [reflectedPairSwap_mul_gram]
  norm_num [Matrix.trace, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Immediately to the right of a quarter period, the cubic limiting coefficient
is strictly negative. -/
theorem exists_negative_reflected_cubic_coefficient :
    ∃ θ : ℝ, 0 < θ ∧
      24 * Real.cos θ * (Real.cos θ + Real.sin θ / θ) < 0 := by
  have hp : 0 < Real.pi / 2 := by positivity
  have hv : 0 < Real.cos (Real.pi / 2) + Real.sin (Real.pi / 2) / (Real.pi / 2) := by
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_add]
    positivity
  have hc : ContinuousAt (fun θ : ℝ => Real.cos θ + Real.sin θ / θ) (Real.pi / 2) := by
    exact Real.continuous_cos.continuousAt.add
      (Real.continuous_sin.continuousAt.div continuousAt_id hp.ne')
  have he := hc (Ioi_mem_nhds hv)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp he
  let e : ℝ := min δ Real.pi / 2
  have he0 : 0 < e := div_pos (lt_min hδ Real.pi_pos) (by norm_num)
  have hed : e < δ := by dsimp [e]; linarith only [min_le_left δ Real.pi, hδ]
  have hep : e ≤ Real.pi / 2 := by dsimp [e]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let θ : ℝ := Real.pi / 2 + e
  have hn : 0 < Real.cos θ + Real.sin θ / θ := by
    apply hnear
    rw [Real.dist_eq, show θ - Real.pi / 2 = e by dsimp [θ]; ring, abs_of_pos he0]
    exact hed
  have hcos : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
    (by dsimp [θ]; linarith only [he0])
    (by dsimp [θ]; linarith only [hep, Real.pi_pos])
  exact ⟨θ, by dsimp [θ]; positivity,
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hcos) hn⟩

/-- The real diagonal overlap and mixed complex overlap. -/
def reflectedDiagonal (x : ℝ) : ℝ := Real.sinh x / x

def reflectedMixedOverlap (x θ : ℝ) : ℂ :=
  Complex.sinh ((x : ℂ) + (θ : ℂ) * I) / ((x : ℂ) + (θ : ℂ) * I)

private theorem tendsto_inv_sinh :
    Tendsto (fun x : ℝ => (Real.sinh x)⁻¹) atTop (𝓝 0) := by
  have h := GaloisForLFunctions.HTGeometry.tendsto_freeDefectAngle_atTop.mul
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith only [hx]
  field_simp

private theorem tendsto_cosh_div_sinh :
    Tendsto (fun x : ℝ => Real.cosh x / Real.sinh x) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    (Real.tendsto_exp_neg_atTop_nhds_zero.mul tendsto_inv_sinh)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hs : 0 < Real.sinh x := lt_of_lt_of_le (by positivity)
    (GaloisForLFunctions.HTGeometry.exp_div_four_le_sinh hx)
  have he : Real.cosh x = Real.sinh x + Real.exp (-x) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  change 1 + Real.exp (-x) * (Real.sinh x)⁻¹ = Real.cosh x / Real.sinh x
  rw [he]
  field_simp

/-- The inverse diagonal overlap vanishes at large real depth. -/
theorem tendsto_inv_reflectedDiagonal :
    Tendsto (fun x : ℝ => (reflectedDiagonal x)⁻¹) atTop (𝓝 0) := by
  simpa only [reflectedDiagonal, inv_div] using
    GaloisForLFunctions.HTGeometry.tendsto_freeDefectAngle_atTop

/-- The mixed overlap divided by the diagonal overlap converges to its height phase. -/
theorem tendsto_reflectedMixedOverlap_div_diagonal (θ : ℝ) :
    Tendsto (fun x : ℝ => reflectedMixedOverlap x θ / (reflectedDiagonal x : ℂ))
      atTop (𝓝 ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) := by
  have hc : Tendsto (fun x : ℝ => ((Real.cosh x / Real.sinh x : ℝ) : ℂ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_cosh_div_sinh
  have ht : Tendsto (fun x : ℝ => ((θ / x : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_div_atTop θ)
  have hh := ((tendsto_const_nhds (x := (Real.cos θ : ℂ))).add
    ((hc.mul_const (Real.sin θ : ℂ)).mul_const I)).div
    ((tendsto_const_nhds (x := (1 : ℂ))).add (ht.mul_const I)) (by norm_num : (1 : ℂ) + 0 * I ≠ 0)
  simp only [one_mul, zero_mul, add_zero, div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by linarith only [hx]
  have hs : 0 < Real.sinh x := lt_of_lt_of_le (by positivity)
    (GaloisForLFunctions.HTGeometry.exp_div_four_le_sinh hx)
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  have hsc : (Real.sinh x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hden : (x : ℂ) + (θ : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact hx0 hre
  dsimp only [Pi.div_apply, reflectedMixedOverlap, reflectedDiagonal]
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.ofReal_div]
  field_simp <;> ring

/-- Exact normalized cubic expression in terms of normalized overlaps. -/
private theorem reflected_cubic_normalized {g : ℝ} (hg : g ≠ 0) (h : ℝ) (f : ℂ) :
    (((reflectedPairSwap * reflectedEvaluationGram g h f) ^ 3).trace).re / g ^ 2 =
      4 * (g⁻¹) ^ 2 + 12 * (1 + h ^ 2 * (g⁻¹) ^ 2 +
        ((f / (g : ℂ)) ^ 2).re + 2 * h * (f / (g : ℂ)).re) := by
  rw [reflectedEvaluation_cubic_trace, div_pow, ← Complex.ofReal_pow,
    Complex.div_ofReal_re, Complex.div_ofReal_re]
  field_simp <;> ring

/-- The normalized cubic trace has an explicit, potentially negative limit. -/
theorem tendsto_reflectedEvaluation_cubic (θ : ℝ) :
    Tendsto (fun x : ℝ =>
      (((reflectedPairSwap * reflectedEvaluationGram (reflectedDiagonal x)
        (Real.sin θ / θ) (reflectedMixedOverlap x θ)) ^ 3).trace).re /
          (reflectedDiagonal x) ^ 2)
      atTop (𝓝 (24 * Real.cos θ * (Real.cos θ + Real.sin θ / θ))) := by
  have hf := tendsto_reflectedMixedOverlap_div_diagonal θ
  have hfr := Complex.continuous_re.continuousAt.tendsto.comp hf
  have hfr2 := Complex.continuous_re.continuousAt.tendsto.comp (hf.pow 2)
  have hg := tendsto_inv_reflectedDiagonal.pow 2
  have hlim := (hg.const_mul 4).add
    (((tendsto_const_nhds (x := (1 : ℝ))).add ((hg.const_mul ((Real.sin θ / θ) ^ 2)).add
      (hfr2.add (hfr.const_mul (2 * (Real.sin θ / θ)))))).const_mul 12)
  have hvalue : 4 * (0 : ℝ) ^ 2 + 12 * (1 +
      ((Real.sin θ / θ) ^ 2 * 0 ^ 2 +
        ((((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) ^ 2).re +
          2 * (Real.sin θ / θ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I).re))) =
      24 * Real.cos θ * (Real.cos θ + Real.sin θ / θ) := by
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_two]
    nlinarith only [Real.sin_sq_add_cos_sq θ]
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hs : 0 < Real.sinh x := lt_of_lt_of_le (by positivity)
    (GaloisForLFunctions.HTGeometry.exp_div_four_le_sinh hx)
  have hg0 : reflectedDiagonal x ≠ 0 := (div_pos hs (by linarith only [hx])).ne'
  dsimp only [Function.comp_def]
  rw [reflected_cubic_normalized hg0]
  ring

/-- Genuine exponential-overlap parameters can have strictly negative cubic trace. -/
theorem exists_negative_reflectedEvaluation_cubic :
    ∃ x θ : ℝ, 0 < x ∧ 0 < θ ∧
      (((reflectedPairSwap * reflectedEvaluationGram (reflectedDiagonal x)
        (Real.sin θ / θ) (reflectedMixedOverlap x θ)) ^ 3).trace).re < 0 := by
  obtain ⟨θ, hθ, hn⟩ := exists_negative_reflected_cubic_coefficient
  have he := (tendsto_reflectedEvaluation_cubic θ).eventually (Iio_mem_nhds hn)
  obtain ⟨x, hx, hneg⟩ := (he.and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨x, θ, hneg, hθ, ?_⟩
  rcases div_neg_iff.mp hx with h | h
  · exact False.elim ((sq_nonneg _).not_gt h.2)
  · exact h.1

/-- Two heights, each carrying the two reflected real depths. -/
def reflectedExponentialParameters (x θ : ℝ) : Fin 4 → ℂ :=
  ![(x : ℂ)/2 + (θ : ℂ)*I/2, -(x : ℂ)/2 + (θ : ℂ)*I/2,
    (x : ℂ)/2 - (θ : ℂ)*I/2, -(x : ℂ)/2 - (θ : ℂ)*I/2]

/-- The literal integral Gram matrix of the four exponential evaluations. -/
def exponentialEvaluationGram (x θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => exponentialOverlap (conj (reflectedExponentialParameters x θ i) +
    reflectedExponentialParameters x θ j)

/-- Every Gram entry is an actual exponential inner product on `[-1,1]`. -/
theorem exponentialEvaluationGram_eq_integral (x θ : ℝ) (i j : Fin 4) :
    exponentialEvaluationGram x θ i j =
      (∫ u : ℝ in -1..1,
        conj (Complex.exp (reflectedExponentialParameters x θ i * u)) *
          Complex.exp (reflectedExponentialParameters x θ j * u)) / 2 :=
  exponentialOverlap_eq_evaluation_inner _ _

/-- The closed Gram formula is realized by the literal evaluation vectors. -/
theorem exponentialEvaluationGram_eq {x θ : ℝ} (hx : 0 < x) (hθ : 0 < θ) :
    exponentialEvaluationGram x θ = reflectedEvaluationGram (reflectedDiagonal x)
      (Real.sin θ / θ) (reflectedMixedOverlap x θ) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hθc : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ.ne'
  have hd : exponentialOverlap (x : ℂ) = (reflectedDiagonal x : ℂ) := by
    rw [exponentialOverlap, if_neg hxc, ← Complex.ofReal_sinh, reflectedDiagonal,
      Complex.ofReal_div]
  have hh : exponentialOverlap ((θ : ℂ) * I) = ((Real.sin θ / θ : ℝ) : ℂ) := by
    rw [exponentialOverlap, if_neg (mul_ne_zero hθc I_ne_zero),
      Complex.sinh_mul_I, ← Complex.ofReal_sin, Complex.ofReal_div]
    field_simp
  have hden : (x : ℂ) + (θ : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact hx.ne' hre
  have hf : exponentialOverlap ((x : ℂ) + (θ : ℂ) * I) = reflectedMixedOverlap x θ := by
    rw [exponentialOverlap, if_neg hden]
    rfl
  have hc : exponentialOverlap ((x : ℂ) - (θ : ℂ) * I) = conj (reflectedMixedOverlap x θ) := by
    have he : (x : ℂ) - (θ : ℂ) * I = conj ((x : ℂ) + (θ : ℂ) * I) := by simp [sub_eq_add_neg]
    rw [he, exponentialOverlap_conj, hf]
  have hn : exponentialOverlap (-(x : ℂ) - (θ : ℂ) * I) = reflectedMixedOverlap x θ := by
    rw [show -(x : ℂ) - (θ : ℂ) * I = -((x : ℂ) + (θ : ℂ) * I) by ring,
      exponentialOverlap_neg, hf]
  have hnc : exponentialOverlap (-(x : ℂ) + (θ : ℂ) * I) = conj (reflectedMixedOverlap x θ) := by
    rw [show -(x : ℂ) + (θ : ℂ) * I = -((x : ℂ) - (θ : ℂ) * I) by ring,
      exponentialOverlap_neg, hc]
  have hargs (i j : Fin 4) : conj (reflectedExponentialParameters x θ i) +
      reflectedExponentialParameters x θ j =
      (!![(x : ℂ), 0, (x : ℂ) - (θ : ℂ)*I, -(θ : ℂ)*I;
          0, -(x : ℂ), -(θ : ℂ)*I, -(x : ℂ) - (θ : ℂ)*I;
          (x : ℂ) + (θ : ℂ)*I, (θ : ℂ)*I, (x : ℂ), 0;
          (θ : ℂ)*I, -(x : ℂ) + (θ : ℂ)*I, 0, -(x : ℂ)] : Matrix (Fin 4) (Fin 4) ℂ) i j := by
    fin_cases i <;> fin_cases j <;>
      norm_num [reflectedExponentialParameters, map_add, map_sub, map_div₀, map_mul, map_ofNat] <;> ring
  ext i j
  rw [exponentialEvaluationGram, hargs]
  fin_cases i <;> fin_cases j <;>
    simp [reflectedEvaluationGram, hd, hh, hf, hc, hn, hnc, neg_mul]

/-- Cubic positivity fails for two actual reflected exponential-evaluation pairs. -/
theorem exists_negative_exponentialEvaluation_cubic :
    ∃ x θ : ℝ, 0 < x ∧ 0 < θ ∧
      (((reflectedPairSwap * exponentialEvaluationGram x θ) ^ 3).trace).re < 0 := by
  obtain ⟨x, θ, hx, hθ, hn⟩ := exists_negative_reflectedEvaluation_cubic
  exact ⟨x, θ, hx, hθ, by rw [exponentialEvaluationGram_eq hx hθ]; exact hn⟩

end GaloisForLFunctions.IncommensurableGaborPinching

#print axioms GaloisForLFunctions.IncommensurableGaborPinching.exists_negative_exponentialEvaluation_cubic
