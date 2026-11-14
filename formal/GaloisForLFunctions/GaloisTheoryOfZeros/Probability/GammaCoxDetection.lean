import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Gamma–Cox zero detection

The Gamma mixture of Poisson zero-count probabilities is an explicit Laplace
transform. Its growing-shape specialization separates every real residual into
zero and nonzero cases. Finite sums give simultaneous error control and weighted
zero counts. The parameter tends through all real values, not only integers.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- Laplace transform of a Gamma law, with arbitrary positive shape and rate. -/
theorem gamma_laplace (a b u : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) :
    (∫ x : ℝ, Real.exp (-(u * x)) ∂gammaMeasure a b) =
      (b / (b + u)) ^ a := by
  unfold gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (gammaPDF a b) from (measurable_gammaPDFReal a b).ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hid : (fun x : ℝ => (gammaPDF a b x).toReal • Real.exp (-(u * x))) =
      (Ici 0).indicator (fun x : ℝ =>
        (b ^ a / Real.Gamma a) * (x ^ (a - 1) * Real.exp (-((b + u) * x)))) := by
    funext x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hb x)]
    by_cases hx : 0 ≤ x
    · rw [gammaPDFReal, if_pos hx, indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), smul_eq_mul]
      rw [mul_assoc, mul_assoc, ← Real.exp_add]
      congr 3
      ring
    · rw [gammaPDFReal, if_neg hx,
        indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx), zero_smul]
  rw [hid, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by linarith)]
  have hg := (Real.Gamma_pos_of_pos ha).ne'
  calc
    b ^ a / Real.Gamma a * ((1 / (b + u)) ^ a * Real.Gamma a) =
        b ^ a * (1 / (b + u)) ^ a := by field_simp
    _ = (b / (b + u)) ^ a := by
      rw [← Real.mul_rpow hb.le (by positivity), mul_one_div]

/-- Exponential weight of a residual; no zero indicator enters its definition. -/
def weight (K r : ℝ) : ℝ := Real.exp (-K * r ^ 2)

/-- Probability of a nonzero count after mixing Poisson intensity with Gamma(K,1). -/
def detection (K r : ℝ) : ℝ :=
  1 - Real.exp (-K * Real.log (1 + weight K r))

/-- The scalar formula is the actual integrated Poisson detection probability. -/
theorem detection_eq_gamma_integral (K r : ℝ) (hK : 0 < K) :
    detection K r = 1 - ∫ x : ℝ, Real.exp (-(weight K r * x)) ∂gammaMeasure K 1 := by
  have hw : 0 < weight K r := Real.exp_pos _
  rw [gamma_laplace K 1 (weight K r) hK zero_lt_one (Real.exp_pos _).le]
  rw [one_div, Real.inv_rpow (by positivity : 0 ≤ 1 + weight K r),
    ← Real.rpow_neg (by positivity : 0 ≤ 1 + weight K r),
    Real.rpow_def_of_pos (by positivity : 0 < 1 + weight K r)]
  simp only [detection, mul_comm]

/-- Exact miss probability at a true zero. -/
theorem detection_zero (K : ℝ) :
    detection K 0 = 1 - Real.exp (-K * Real.log 2) := by
  simp only [detection, weight, zero_pow (by omega : 2 ≠ 0), mul_zero, Real.exp_zero]
  norm_num

/-- Finite positive concentration never removes false positives completely. -/
theorem detection_pos (K r : ℝ) (hK : 0 < K) : 0 < detection K r := by
  have hw : 0 < weight K r := Real.exp_pos _
  have hl : 0 < Real.log (1 + weight K r) := Real.log_pos (by linarith)
  have he : Real.exp (-K * Real.log (1 + weight K r)) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hK) hl)
  exact sub_pos.mpr he

theorem detection_nonneg (K r : ℝ) (hK : 0 ≤ K) : 0 ≤ detection K r := by
  have hl : 0 ≤ Real.log (1 + weight K r) :=
    Real.log_nonneg (by have := (Real.exp_pos (-K * r ^ 2)).le; dsimp [weight]; linarith)
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) hl))

theorem detection_lt_one (K r : ℝ) : detection K r < 1 := by
  exact sub_lt_self 1 (Real.exp_pos _)

/-- The first-moment envelope controls every false-positive probability. -/
theorem detection_le (K r : ℝ) (hK : 0 ≤ K) : detection K r ≤ K * weight K r := by
  have hw : 0 < weight K r := Real.exp_pos _
  have hl : Real.log (1 + weight K r) ≤ weight K r := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + weight K r)
  have he := Real.add_one_le_exp (-K * Real.log (1 + weight K r))
  have hm := mul_le_mul_of_nonneg_left hl hK
  dsimp [detection]
  linarith only [he, hm]

/-- Exponential damping dominates the linearly growing mean intensity. -/
theorem tendsto_mean_nonzero (r : ℝ) (hr : r ≠ 0) :
    Tendsto (fun K => K * weight K r) atTop (𝓝 0) := by
  simpa only [Real.rpow_one, weight, mul_comm, neg_mul, mul_neg] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (r ^ 2) (sq_pos_of_ne_zero hr)

/-- Pointwise consistency holds without regularity assumptions on the residual. -/
theorem tendsto_detection (r : ℝ) :
    Tendsto (fun K => detection K r) atTop (𝓝 (if r = 0 then 1 else 0)) := by
  by_cases hr : r = 0
  · subst r
    simp only [detection_zero, ↓reduceIte]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const hlog)
    simpa only [neg_mul, sub_zero, Function.comp_def, id_eq] using tendsto_const_nhds.sub h
  · simp only [if_neg hr]
    exact squeeze_zero'
      ((eventually_ge_atTop 0).mono fun K hK => detection_nonneg K r hK)
      ((eventually_ge_atTop 0).mono fun K hK => detection_le K r hK)
      (tendsto_mean_nonzero r hr)

/-- A finite candidate family's expected weighted detections recover its zero sum. -/
theorem tendsto_weighted_detection {X : Type*} (D : Finset X) (g w : X → ℝ) :
    Tendsto (fun K => ∑ x ∈ D, w x * detection K (g x)) atTop
      (𝓝 (∑ x ∈ D, if g x = 0 then w x else 0)) := by
  classical
  convert tendsto_finsetSum D (fun x _ => (tendsto_detection (g x)).const_mul (w x)) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Per-candidate classification error, including both missed zeros and false positives. -/
def error (K r : ℝ) : ℝ := if r = 0 then 1 - detection K r else detection K r

/-- The sum of marginal errors is a universal union-bound envelope. -/
def errorBound {X : Type*} (D : Finset X) (g : X → ℝ) (K : ℝ) : ℝ :=
  ∑ x ∈ D, if g x = 0 then Real.exp (-K * Real.log 2) else K * weight K (g x)

theorem error_nonneg (K r : ℝ) (hK : 0 ≤ K) : 0 ≤ error K r := by
  unfold error
  split_ifs
  · exact sub_nonneg.mpr (detection_lt_one K r).le
  · exact detection_nonneg K r hK

theorem sum_error_le {X : Type*} (D : Finset X) (g : X → ℝ) (K : ℝ) (hK : 0 ≤ K) :
    (∑ x ∈ D, error K (g x)) ≤ errorBound D g K := by
  apply Finset.sum_le_sum
  intro x _
  dsimp [error, errorBound]
  split_ifs with h
  · rw [h, detection_zero]
    ring_nf
    exact le_rfl
  · exact detection_le K (g x) hK

theorem tendsto_errorBound {X : Type*} (D : Finset X) (g : X → ℝ) :
    Tendsto (errorBound D g) atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : Tendsto (fun K : ℝ => Real.exp (-K * Real.log 2)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def, id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const hlog)
  have h := tendsto_finsetSum D (a := fun _ => (0 : ℝ)) (fun x _ => show
      Tendsto (fun K => if g x = 0 then Real.exp (-K * Real.log 2) else K * weight K (g x))
        atTop (𝓝 0) from by
    by_cases hx : g x = 0
    · simpa only [if_pos hx] using hz
    · simpa only [if_neg hx] using tendsto_mean_nonzero (g x) hx)
  change Tendsto (fun K => ∑ x ∈ D,
    if g x = 0 then Real.exp (-K * Real.log 2) else K * weight K (g x)) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero] using h

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.gamma_laplace
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_eq_gamma_integral
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_zero
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_pos
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_nonneg
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_lt_one
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_mean_nonzero
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_detection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_weighted_detection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.error_nonneg
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.sum_error_le
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_errorBound
