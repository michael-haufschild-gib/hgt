import GaloisForLFunctions.HTGeometry.ComplexGaussianTranslationDefect
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# A simultaneous pointwise envelope for polynomial translation errors

The nonconstant Hasse tail gives a single nonnegative function dominating every
complex polynomial displacement in a closed disk. Its L² bound is uniform in
the coefficients and permits the displacement to vary with the real argument.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory
noncomputable section

namespace GaloisForLFunctions

/-- The complete nonconstant Hasse tail, with absolute values taken after evaluation. -/
def gaussianHasseTailEnvelope (P : Polynomial ℝ) (R : ℝ≥0) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range P.natDegree,
    (R : ℝ) ^ (k + 1) * ‖polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P) x‖

/-- The Hasse envelope is nonnegative at every real argument. -/
theorem gaussianHasseTailEnvelope_nonneg (P : Polynomial ℝ) (R : ℝ≥0) (x : ℝ) :
    0 ≤ gaussianHasseTailEnvelope P R x := by
  unfold gaussianHasseTailEnvelope
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (norm_nonneg _)

/-- A common pointwise bound for every displacement in the closed disk. -/
theorem norm_complexTranslatedPolyGauss_sub_le_envelope (P : Polynomial ℝ)
    (R : ℝ≥0) (z : Metric.closedBall (0 : ℂ) R) (x : ℝ) :
    ‖complexTranslatedPolyGauss P z x - polyGaussSchwartz P x‖ ≤
      gaussianHasseTailEnvelope P R x := by
  have hz : ‖(z : ℂ)‖ ≤ (R : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  have hid := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
    (complexTranslatedPolyGauss_sub_eq_sum P z)
  simp only [_root_.sub_apply, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul] at hid
  rw [hid]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _)
    (norm_nonneg _)

/-- The pointwise envelope is square integrable. -/
theorem memLp_gaussianHasseTailEnvelope (P : Polynomial ℝ) (R : ℝ≥0) :
    MemLp (gaussianHasseTailEnvelope P R) 2 (volume : Measure ℝ) := by
  unfold gaussianHasseTailEnvelope
  exact memLp_finsetSum _ fun k _ =>
    ((polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P)).memLp 2 volume).norm.const_mul _

/-- Schwartz L² norms agree with the real-valued function seminorm. -/
theorem lpNorm_schwartz_eq (f : SchwartzMap ℝ ℂ) :
    lpNorm f 2 (volume : Measure ℝ) = ‖f.toLp 2 (volume : Measure ℝ)‖ := by
  rw [SchwartzMap.norm_toLp, toReal_eLpNorm f.continuous.aestronglyMeasurable]

/-- The simultaneous envelope has the same exponential relative budget as a fixed shift. -/
theorem lpNorm_gaussianHasseTailEnvelope_le (P : Polynomial ℝ) (R : ℝ≥0) :
    lpNorm (gaussianHasseTailEnvelope P R) 2 (volume : Measure ℝ) ≤
      (Real.exp ((R : ℝ) * Real.sqrt (4 * π * P.natDegree)) - 1) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let A : ℝ := Real.sqrt (4 * π * P.natDegree)
  let N : ℝ := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖
  have hterm (k : ℕ) :
      lpNorm (fun x => (R : ℝ) ^ k *
        ‖polyGaussSchwartz (Polynomial.hasseDeriv k P) x‖) 2 (volume : Measure ℝ) ≤
        ((R : ℝ) * A) ^ k / (k.factorial : ℝ) * N := by
    have hfac : (0 : ℝ) < k.factorial := by positivity
    have hh := gaussianHasseDerivativeFactorialNorm_le P k
    have hh' :
        ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2 (volume : Measure ℝ)‖ ≤
          A ^ k * N / (k.factorial : ℝ) := by
      rw [le_div_iff₀ hfac]
      simpa only [A, N, mul_comm] using hh
    have hscale := lpNorm_const_smul (p := (2 : ENNReal)) ((R : ℝ) ^ k)
      (fun x => ‖polyGaussSchwartz (Polynomial.hasseDeriv k P) x‖) (volume : Measure ℝ)
    simp only [Pi.smul_def, smul_eq_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (R : ℝ) ^ k)] at hscale
    rw [hscale, lpNorm_norm (polyGaussSchwartz _).continuous.aestronglyMeasurable,
      lpNorm_schwartz_eq]
    calc
      _ ≤ (R : ℝ) ^ k * (A ^ k * N / (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hh' (by positivity)
      _ = _ := by ring
  have hexp : HasSum (fun k : ℕ => ((R : ℝ) * A) ^ k / (k.factorial : ℝ))
      (Real.exp ((R : ℝ) * A)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ((R : ℝ) * A)
  have hfull := hexp.summable.sum_le_tsum (Finset.range (P.natDegree + 1))
    (fun k _ => by positivity)
  rw [hexp.tsum_eq, Finset.sum_range_succ'] at hfull
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hfull
  have htail : (∑ k ∈ Finset.range P.natDegree,
      ((R : ℝ) * A) ^ (k + 1) / ((k + 1).factorial : ℝ)) ≤
      Real.exp ((R : ℝ) * A) - 1 := by linarith only [hfull]
  have hsum := lpNorm_sum_le
    (p := (2 : ENNReal)) (μ := (volume : Measure ℝ))
    (s := Finset.range P.natDegree)
    (f := fun k x => (R : ℝ) ^ (k + 1) *
      ‖polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P) x‖)
    (fun k _ => ((polyGaussSchwartz _).memLp 2 volume).norm.const_mul _) (by simp)
  calc
    _ ≤ ∑ k ∈ Finset.range P.natDegree,
        lpNorm (fun x => (R : ℝ) ^ (k + 1) *
          ‖polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P) x‖)
          2 (volume : Measure ℝ) := by
      change lpNorm (fun x => ∑ k ∈ Finset.range P.natDegree,
        (R : ℝ) ^ (k + 1) * ‖polyGaussSchwartz (Polynomial.hasseDeriv (k + 1) P) x‖)
        2 (volume : Measure ℝ) ≤ _
      simpa only [Finset.sum_fn] using hsum
    _ ≤ ∑ k ∈ Finset.range P.natDegree,
        (((R : ℝ) * A) ^ (k + 1) / ((k + 1).factorial : ℝ) * N) :=
      Finset.sum_le_sum fun k _ => hterm (k + 1)
    _ = (∑ k ∈ Finset.range P.natDegree,
        ((R : ℝ) * A) ^ (k + 1) / ((k + 1).factorial : ℝ)) * N := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right htail (norm_nonneg _)

end GaloisForLFunctions
