import GaloisForLFunctions.HilbertMetric.DegreeFiveGaussianCurvature
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import GaloisForLFunctions.HilbertMetric.FanoCommutator
import GaloisForLFunctions.HilbertMetric.GramCurvaturePersistence
import GaloisForLFunctions.HilbertMetric.QuasiFreeFillingFano
import GaloisForLFunctions.HilbertMetric.QuasiFreeRankVarianceDiscriminant

/-!
# Discharging the residual analytic premises of the Hilbert-metric area

Three hypotheses of this area were consumed but produced nowhere: eventual nonvanishing of the
exponential inner Gram determinant, nonvanishing of a self-commutator, and strict positivity of a
scalar log-curvature numerator.  The first was proved inside one long argument and never named; the
other two are satisfiability conditions with explicit witnesses.

* **`eventually_finiteExponentialInnerGram_det_ne_zero`** — pointwise nonvanishing spreads to a
  neighbourhood, so the gauge-invariance of second log-determinant curvature needs only a value;
* **`matrixSelfCommutator_ne_zero_iff_mul_transpose_ne`** and the nilpotent Jordan block — the
  strict Fano defect is attained;
* **`scalarLogCurvatureNumerator_pos_iff`** and the unit 2-jet — strict log-curvature persistence
  holds on an explicit family.
-/

namespace GaloisForLFunctions.HilbertMetric

open Filter Topology

noncomputable section

/-! ## The exponential inner Gram determinant -/

/-- **Pointwise nonvanishing of the exponential inner Gram determinant spreads to a
neighbourhood.**  The determinant is differentiable in the bandwidth, hence continuous. -/
theorem eventually_finiteExponentialInnerGram_det_ne_zero {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (x : ι → κ → ℝ) {s : ℝ}
    (hs : (finiteExponentialInnerGram x s).det ≠ 0) :
    ∀ᶠ t in nhds s, (finiteExponentialInnerGram x t).det ≠ 0 := by
  have hdetAt := hasDerivAt_matrixDet (finiteExponentialInnerGram x)
    (fun i j => (∑ a, x i a * x j a) * finiteExponentialInnerGram x s i j)
    s (hasDerivAt_finiteExponentialInnerGram x s)
  exact (hdetAt.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hs

/-- **Gauge invariance of second log-determinant curvature from a single value.**  The eventual
nonvanishing premise is implied by nonvanishing at the point itself. -/
theorem finiteHalfGaussianDistance_logDet_secondDerivative_eq_of_det_ne_zero {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (x : ι → κ → ℝ) (s : ℝ)
    (hs : (finiteExponentialInnerGram x s).det ≠ 0) :
    deriv (deriv (fun t => Real.log (finiteHalfGaussianDistanceGram x t).det)) s =
      deriv (deriv (fun t => Real.log (finiteExponentialInnerGram x t).det)) s :=
  finiteHalfGaussianDistance_logDet_secondDerivative_eq x s
    (eventually_finiteExponentialInnerGram_det_ne_zero x hs)

/-- The exponential inner Gram at bandwidth `t` is the coherent Gaussian Gram of the coordinates
scaled by `√t`. -/
theorem finiteExponentialInnerGram_eq_gaussianCoherentGram {d n : ℕ}
    (x : Fin n → Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    finiteExponentialInnerGram x t =
      gaussianCoherentGram (fun i a => Real.sqrt t * x i a) := by
  funext i j
  show Real.exp (t * ∑ a, x i a * x j a) =
    Real.exp (coordinateDot (fun i a => Real.sqrt t * x i a) i j)
  congr 1
  rw [coordinateDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show Real.sqrt t * x i a * (Real.sqrt t * x j a) =
      Real.sqrt t * Real.sqrt t * (x i a * x j a) by ring, Real.mul_self_sqrt ht]

/-- **A separating coordinate makes the exponential inner Gram positive definite** at every
positive bandwidth. -/
theorem finiteExponentialInnerGram_posDef_of_coordinate_injective {d n : ℕ}
    (x : Fin n → Fin d → ℝ) (k : Fin d) (hx : Function.Injective fun i => x i k)
    {t : ℝ} (ht : 0 < t) :
    (finiteExponentialInnerGram x t).PosDef := by
  rw [finiteExponentialInnerGram_eq_gaussianCoherentGram x ht.le]
  refine gaussianCoherentGram_posDef_of_coordinate_injective _ k ?_
  intro i j hij
  exact hx (mul_left_cancel₀ (Real.sqrt_pos.mpr ht).ne' hij)

/-- Hence its determinant never vanishes on a separated configuration. -/
theorem finiteExponentialInnerGram_det_ne_zero_of_coordinate_injective {d n : ℕ}
    (x : Fin n → Fin d → ℝ) (k : Fin d) (hx : Function.Injective fun i => x i k)
    {t : ℝ} (ht : 0 < t) :
    (finiteExponentialInnerGram x t).det ≠ 0 :=
  ne_of_gt (finiteExponentialInnerGram_posDef_of_coordinate_injective x k hx ht).det_pos

/-- **Gauge invariance of second log-determinant curvature on a separated configuration**, with no
determinant hypothesis at all. -/
theorem finiteHalfGaussianDistance_logDet_secondDerivative_eq_of_coordinate_injective
    {d n : ℕ} (x : Fin n → Fin d → ℝ) (k : Fin d) (hx : Function.Injective fun i => x i k)
    {s : ℝ} (hs : 0 < s) :
    deriv (deriv (fun t => Real.log (finiteHalfGaussianDistanceGram x t).det)) s =
      deriv (deriv (fun t => Real.log (finiteExponentialInnerGram x t).det)) s :=
  finiteHalfGaussianDistance_logDet_secondDerivative_eq_of_det_ne_zero x s
    (finiteExponentialInnerGram_det_ne_zero_of_coordinate_injective x k hx hs)

/-! ## The self-commutator -/

/-- A self-commutator is nonzero exactly when the matrix fails to be normal. -/
theorem matrixSelfCommutator_ne_zero_iff_mul_transpose_ne {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    matrixSelfCommutator A ≠ 0 ↔ A * A.transpose ≠ A.transpose * A := by
  rw [matrixSelfCommutator, sub_ne_zero]

/-- The nilpotent Jordan block, the smallest non-normal real matrix. -/
def jordanNilpotentTwo : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

theorem matrixSelfCommutator_jordanNilpotentTwo_apply :
    matrixSelfCommutator jordanNilpotentTwo 0 0 = 1 := by
  show (jordanNilpotentTwo * jordanNilpotentTwo.transpose -
    jordanNilpotentTwo.transpose * jordanNilpotentTwo) 0 0 = 1
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp [jordanNilpotentTwo, Fin.sum_univ_two]

theorem matrixSelfCommutator_jordanNilpotentTwo_ne_zero :
    matrixSelfCommutator jordanNilpotentTwo ≠ 0 := by
  intro h
  have hval := matrixSelfCommutator_jordanNilpotentTwo_apply
  rw [h] at hval
  simp at hval

/-- **The strict Fano defect is attained.**  For the nilpotent Jordan block the square energy is
strictly below the trace of the squared column-energy matrix. -/
theorem squareEnergy_lt_trace_columnEnergy_sq_jordanNilpotentTwo :
    matrixHilbertSchmidtEnergy (jordanNilpotentTwo * jordanNilpotentTwo) <
      Matrix.trace ((jordanNilpotentTwo.transpose * jordanNilpotentTwo) *
        (jordanNilpotentTwo.transpose * jordanNilpotentTwo)) :=
  squareEnergy_lt_trace_columnEnergy_sq_of_selfCommutator_ne_zero _
    matrixSelfCommutator_jordanNilpotentTwo_ne_zero

/-! ## The scalar log-curvature numerator -/

/-- Strict positivity of the scalar log-curvature numerator is strict log-convexity of the
2-jet. -/
theorem scalarLogCurvatureNumerator_pos_iff (z z₁ z₂ : ℝ) :
    0 < scalarLogCurvatureNumerator z z₁ z₂ ↔ z₁ ^ 2 < z * z₂ := by
  rw [scalarLogCurvatureNumerator, sub_pos]

theorem scalarLogCurvatureNumerator_unit : scalarLogCurvatureNumerator 1 0 1 = 1 := by
  norm_num [scalarLogCurvatureNumerator]

/-- **Strict log-curvature persistence on an explicit family.**  A scalar 2-jet converging to the
unit jet is eventually strictly log-convex, with no positivity premise. -/
theorem eventually_pos_scalarLogCurvatureNumerator_of_tendsto_unit {α : Type*} {l : Filter α}
    {f f₁ f₂ : α → ℝ}
    (hf : Tendsto f l (nhds 1)) (hf₁ : Tendsto f₁ l (nhds 0))
    (hf₂ : Tendsto f₂ l (nhds 1)) :
    ∀ᶠ x in l, 0 < scalarLogCurvatureNumerator (f x) (f₁ x) (f₂ x) :=
  eventually_pos_scalarLogCurvatureNumerator hf hf₁ hf₂
    (by rw [scalarLogCurvatureNumerator_unit]; norm_num)

/-! ## The quasi-free sign conditions -/

/-- The diagonal frame of two orbitals. -/
def twoModeFrame : Fin 2 → Fin 2 → ℝ := fun i k => if i = k then 1 else 0

/-- One high spectral level and one at the band floor. -/
def twoModeEnergy : Fin 2 → ℝ := ![4, 0]

/-- A single half-occupied high orbital. -/
def twoModeOccupation : Fin 2 → ℝ := ![1 / 2, 0]

theorem twoModeFrame_isOrthonormal : IsOrthonormalCoordinateFrame twoModeFrame := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [twoModeFrame]

theorem twoModeOccupation_nonneg : ∀ i, 0 ≤ twoModeOccupation i := by
  intro i
  fin_cases i <;> norm_num [twoModeOccupation]

theorem twoModeEnergy_lower : ∀ k, (0 : ℝ) ≤ twoModeEnergy k := by
  intro k
  fin_cases k <;> norm_num [twoModeEnergy]

theorem twoModeEnergy_upper : ∀ k, twoModeEnergy k ≤ (4 : ℝ) := by
  intro k
  fin_cases k <;> norm_num [twoModeEnergy]

theorem quasiFreeSpectralFanoMargin_twoMode :
    quasiFreeSpectralFanoMargin twoModeFrame twoModeEnergy twoModeOccupation = -2 := by
  simp [quasiFreeSpectralFanoMargin, quasiFreeSpectralMean, quasiFreeSpectralVariance,
    quasiFreeCompressedSpectralEnergy, orbitalSpectralMean, orbitalSpectralSecondMoment,
    twoModeFrame, twoModeEnergy, twoModeOccupation, Fin.sum_univ_two]
  norm_num

/-- **A negative quasi-free Fano margin is attained.** -/
theorem quasiFreeSpectralFanoMargin_twoMode_neg :
    quasiFreeSpectralFanoMargin twoModeFrame twoModeEnergy twoModeOccupation < 0 := by
  rw [quasiFreeSpectralFanoMargin_twoMode]
  norm_num

/-- The filling-failure consequence, on the explicit configuration. -/
theorem twoMode_filling_failure :
    4 * ((0 : ℝ) * 4) * (∑ i, twoModeOccupation i) <
      (Fintype.card (Fin 2) : ℝ) * ((0 : ℝ) + 4 - 1) ^ 2 :=
  quasiFreeSpectralFanoMargin_negative_forces_filling_failure
    twoModeFrame twoModeEnergy twoModeOccupation twoModeFrame_isOrthonormal
    twoModeOccupation_nonneg 0 4 twoModeEnergy_lower twoModeEnergy_upper
    quasiFreeSpectralFanoMargin_twoMode_neg

theorem quasiFreeSpectralBandBudget_twoMode :
    quasiFreeSpectralBandBudget twoModeFrame twoModeEnergy twoModeOccupation 0 4 = 4 := by
  simp [quasiFreeSpectralBandBudget, quasiFreeSpectralMean, quasiFreeSpectralVariance,
    quasiFreeCompressedSpectralEnergy, orbitalSpectralMean, orbitalSpectralSecondMoment,
    twoModeFrame, twoModeEnergy, twoModeOccupation, Fin.sum_univ_two]
  norm_num

/-- **A positive quasi-free band budget is attained.** -/
theorem quasiFreeSpectralBandBudget_twoMode_pos :
    0 < quasiFreeSpectralBandBudget twoModeFrame twoModeEnergy twoModeOccupation 0 4 := by
  rw [quasiFreeSpectralBandBudget_twoMode]
  norm_num

/-- The tomography-free support-rank certificate, on the explicit configuration. -/
theorem twoMode_support_rank_lower_bound :
    quasiFreeSpectralMean twoModeFrame twoModeEnergy twoModeOccupation ^ 2 /
        quasiFreeSpectralBandBudget twoModeFrame twoModeEnergy twoModeOccupation 0 4 ≤
      (Fintype.card (Fin 2) : ℝ) :=
  quasiFreeSpectral_support_rank_lower_bound
    twoModeFrame twoModeEnergy twoModeOccupation twoModeFrame_isOrthonormal
    twoModeOccupation_nonneg 0 4 twoModeEnergy_lower twoModeEnergy_upper
    quasiFreeSpectralBandBudget_twoMode_pos

end

end GaloisForLFunctions.HilbertMetric
