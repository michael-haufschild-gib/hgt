import GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus
import GaloisForLFunctions.HTGeometry.CoordinateCurvatureTwoJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual hyperbolic horizon covector equation

The literal upper-half-plane metric supplies its actual connection, covariant
first derivative, divergence and rough covector Laplacian. Both lower-index
connection terms are retained in the second derivative. The area-form rotation
of a scalar gradient satisfies the actual intertwining identity with curvature
term `-V`, so its eigenvalue shift follows from the scalar field equation.

This geometric bridge does not supply an arithmetic spectral restriction or a
physical causal response. Literal cusp specialization is a separate leaf.
-/

open Complex Real Set Filter Topology
open scoped ContDiff BigOperators
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMHorizon
noncomputable section

abbrev Point := Fin 2 → ℝ
abbrev Field := Point → ℂ
abbrev Covector := Fin 2 → Field

/-- Literal horizon metric in real upper-half-plane coordinates. -/
def metric (z : Point) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun _ => (z 1 : ℂ)⁻¹ ^ (2 : ℕ))

/-- The metric jet consists of actual ordered coordinate derivatives. -/
def metricJet (z : Point) : CoordinateMetricTwoJet 2 ℂ where
  metric := metric z
  first i j k := coordDeriv i (fun q => metric q j k) z
  second i j k l := coordDeriv i (coordDeriv j (fun q => metric q k l)) z

/-- Connection obtained from the actual metric and its actual first derivative. -/
def christoffel (z : Point) (u i j : Fin 2) : ℂ :=
  (metricJet z).christoffel u i j

/-- Explicit coordinate connection table. -/
def connectionTable (Y : ℂ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, -Y⁻¹; -Y⁻¹, 0], !![Y⁻¹, 0; 0, -Y⁻¹]]

private theorem scale_hasFDerivAt (z : Point) (hz : 0 < z 1) :
    HasFDerivAt (fun q : Point => (q 1 : ℂ)⁻¹ ^ (2 : ℕ))
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).smulRight (-2 * (z 1 : ℂ)⁻¹ ^ (3 : ℕ))) z := by
  have hzC : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hY := Complex.ofRealCLM.hasFDerivAt.comp z
    ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
  have hi := (hasDerivAt_inv hzC).comp_hasFDerivAt z hY
  convert! hi.pow 2 using 1
  ext v
  simp [Complex.real_smul, smul_eq_mul]
  ring

private theorem metric_first (z : Point) (hz : 0 < z 1) (i j k : Fin 2) :
    (metricJet z).first i j k =
      if j = k then (if i = 1 then -2 * (z 1 : ℂ)⁻¹ ^ (3 : ℕ) else 0) else 0 := by
  by_cases hjk : j = k
  · subst k
    simp only [metricJet, metric, Matrix.diagonal_apply_eq, ↓reduceIte]
    rw [coordDeriv, (scale_hasFDerivAt z hz).fderiv]
    fin_cases i <;> simp
  · simp [metricJet, metric, Matrix.diagonal_apply, hjk, coordDeriv]

/-- The inverse used in the connection is the actual matrix inverse. -/
theorem metric_inverse (z : Point) (hz : 0 < z 1) :
    (metric z)⁻¹ = Matrix.diagonal (fun _ : Fin 2 => (z 1 : ℂ) ^ (2 : ℕ)) := by
  have hzC : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  apply Matrix.inv_eq_left_inv
  rw [metric, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp

/-- All connection entries are derived from the literal horizon metric. -/
theorem christoffel_eq (z : Point) (hz : 0 < z 1) (u i j : Fin 2) :
    christoffel z u i j = connectionTable (z 1) u i j := by
  simp only [christoffel, CoordinateMetricTwoJet.christoffel,
    show (metricJet z).metric = metric z from rfl, metric_inverse z hz, metric_first z hz]
  have hzC : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  fin_cases u <;> fin_cases i <;> fin_cases j <;>
    simp [connectionTable]
  all_goals field_simp

private theorem positive_nhds (z : Point) (hz : 0 < z 1) :
    ∀ᶠ q in 𝓝 z, 0 < q 1 := (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz

/-- Coordinate derivatives retain the required finite smoothness order. -/
theorem coordDeriv_contDiffAt {f : Field} {z : Point} {m : WithTop ℕ∞}
    (hf : ContDiffAt ℝ (m + 1) f z) (i : Fin 2) : ContDiffAt ℝ m (coordDeriv i f) z :=
  (hf.fderiv_right le_rfl).clm_apply contDiffAt_const

/-- The derivative of an actual coordinate derivative. -/
theorem coordDeriv_hasFDerivAt {f : Field} {z : Point} (hf : ContDiffAt ℝ 2 f z) (i : Fin 2) :
    HasFDerivAt (coordDeriv i f) ((fderiv ℝ (fderiv ℝ f) z).flip (Pi.single i 1)) z := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  simpa [coordDeriv] using hd.clm_apply (hasFDerivAt_const (Pi.single i 1) z)

/-- Actual coordinate second derivatives commute. -/
theorem coordDeriv_commute {f : Field} {z : Point} (hf : ContDiffAt ℝ 2 f z) (i j : Fin 2) :
    coordDeriv i (coordDeriv j f) z = coordDeriv j (coordDeriv i f) z := by
  change fderiv ℝ (coordDeriv j f) z (Pi.single i 1) = fderiv ℝ (coordDeriv i f) z (Pi.single j 1)
  rw [(coordDeriv_hasFDerivAt hf j).fderiv, (coordDeriv_hasFDerivAt hf i).fderiv]
  exact (hf.isSymmSndFDerivAt (by simp)).eq _ _

private theorem partial_add {f g : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun q => f q + g q) z = coordDeriv i f z + coordDeriv i g z := by
  simp only [coordDeriv, fderiv_fun_add hf hg, add_apply]

private theorem partial_sub {f g : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun q => f q - g q) z = coordDeriv i f z - coordDeriv i g z := by
  simp only [coordDeriv, fderiv_fun_sub hf hg, sub_apply]

private theorem inv_height_hasFDerivAt (z : Point) (hz : 0 < z 1) :
    HasFDerivAt (fun q : Point => (q 1 : ℂ)⁻¹)
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).smulRight (-(z 1 : ℂ)⁻¹ ^ (2 : ℕ))) z := by
  have hY := Complex.ofRealCLM.hasFDerivAt.comp z
    ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
  have h := (hasDerivAt_inv (Complex.ofReal_ne_zero.mpr hz.ne')).comp_hasFDerivAt z hY
  convert! h using 1
  ext v
  simp [Complex.real_smul, smul_eq_mul]
  ring

private theorem inv_mul_partial {f : Field} {z : Point}
    (hz : 0 < z 1) (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    coordDeriv i (fun q => (q 1 : ℂ)⁻¹ * f q) z =
      (if i = 1 then -(z 1 : ℂ)⁻¹ ^ (2 : ℕ) else 0) * f z +
        (z 1 : ℂ)⁻¹ * coordDeriv i f z := by
  change fderiv ℝ ((fun q : Point => (q 1 : ℂ)⁻¹) * f) z (Pi.single i 1) = _
  rw [((inv_height_hasFDerivAt z hz).mul hf.hasFDerivAt).fderiv]
  fin_cases i <;> simp [coordDeriv, smul_eq_mul]
  ring

/-- Actual covariant derivative of a horizon covector. -/
def covariant (V : Covector) (i j : Fin 2) (z : Point) : ℂ :=
  coordDeriv i (V j) z - ∑ k, christoffel z k i j * V k z

/-- Expanded first covariant derivative, for identifying every connection contribution. -/
def covariantFormula (V : Covector) (i j : Fin 2) (z : Point) : ℂ :=
  !![coordDeriv 0 (V 0) z - (z 1 : ℂ)⁻¹ * V 1 z,
      coordDeriv 0 (V 1) z + (z 1 : ℂ)⁻¹ * V 0 z;
      coordDeriv 1 (V 0) z + (z 1 : ℂ)⁻¹ * V 0 z,
      coordDeriv 1 (V 1) z + (z 1 : ℂ)⁻¹ * V 1 z] i j

/-- The first covariant derivative is computed from the actual metric connection. -/
theorem covariant_eq (V : Covector) (z : Point) (hz : 0 < z 1) (i j : Fin 2) :
    covariant V i j z = covariantFormula V i j z := by
  simp only [covariant, christoffel_eq z hz]
  fin_cases i <;> fin_cases j <;> simp [covariantFormula, connectionTable, Fin.sum_univ_two]

/-- Coordinate derivative of each first covariant derivative. -/
def covariantPartialFormula (V : Covector) (k i j : Fin 2) (z : Point) : ℂ :=
  let A (h : Fin 2) := (if k = 1 then -(z 1 : ℂ)⁻¹ ^ (2 : ℕ) else 0) * V h z +
    (z 1 : ℂ)⁻¹ * coordDeriv k (V h) z
  !![coordDeriv k (coordDeriv 0 (V 0)) z - A 1,
      coordDeriv k (coordDeriv 0 (V 1)) z + A 0;
      coordDeriv k (coordDeriv 1 (V 0)) z + A 0,
      coordDeriv k (coordDeriv 1 (V 1)) z + A 1] i j

/-- This derivative formula uses actual C2 fields, including the derivative of 1/Y. -/
theorem covariant_partial_eq (V : Covector) (z : Point) (hz : 0 < z 1)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) z) (k i j : Fin 2) :
    coordDeriv k (covariant V i j) z = covariantPartialFormula V k i j z := by
  have he : covariant V i j =ᶠ[𝓝 z] covariantFormula V i j := by
    filter_upwards [positive_nhds z hz] with q hq
    exact covariant_eq V q hq i j
  have hd (j : Fin 2) := (hV j).differentiableAt (by norm_num)
  have hi (j : Fin 2) := (inv_height_hasFDerivAt z hz).differentiableAt.mul (hd j)
  have hp (j l : Fin 2) := (coordDeriv_hasFDerivAt (hV j) l).differentiableAt
  change fderiv ℝ (covariant V i j) z (Pi.single k 1) = _
  rw [he.fderiv_eq]
  change coordDeriv k (covariantFormula V i j) z = _
  have hInv (l : Fin 2) :
      coordDeriv k ((fun q : Point => (q 1 : ℂ)⁻¹) * V l) z =
        (if k = 1 then -(z 1 : ℂ)⁻¹ ^ (2 : ℕ) else 0) * V l z +
          (z 1 : ℂ)⁻¹ * coordDeriv k (V l) z := inv_mul_partial hz (hd l) k
  fin_cases i <;> fin_cases j
  · change coordDeriv k (fun q => coordDeriv 0 (V 0) q - (q 1 : ℂ)⁻¹ * V 1 q) z = _
    simpa [covariantPartialFormula, hInv] using partial_sub (hp 0 0) (hi 1) k
  · change coordDeriv k (fun q => coordDeriv 0 (V 1) q + (q 1 : ℂ)⁻¹ * V 0 q) z = _
    simpa [covariantPartialFormula, hInv] using partial_add (hp 1 0) (hi 0) k
  · change coordDeriv k (fun q => coordDeriv 1 (V 0) q + (q 1 : ℂ)⁻¹ * V 0 q) z = _
    simpa [covariantPartialFormula, hInv] using partial_add (hp 0 1) (hi 0) k
  · change coordDeriv k (fun q => coordDeriv 1 (V 1) q + (q 1 : ℂ)⁻¹ * V 1 q) z = _
    simpa [covariantPartialFormula, hInv] using partial_add (hp 1 1) (hi 1) k

/-- Covariant divergence, contracted using the literal inverse metric. -/
def divergence (V : Covector) (z : Point) : ℂ :=
  ∑ i, ∑ j, (metric z)⁻¹ i j * covariant V i j z

/-- Rough covector Laplacian, retaining the connection on both lower derivative slots. -/
def roughLaplacian (V : Covector) (k : Fin 2) (z : Point) : ℂ :=
  ∑ i, ∑ j, (metric z)⁻¹ i j *
    (coordDeriv i (covariant V j k) z -
      ∑ l, christoffel z l i j * covariant V l k z -
      ∑ l, christoffel z l i k * covariant V j l z)

/-- Scalar Laplacian as the actual inverse-metric trace of the covariant Hessian. -/
def scalarLaplacian (S : Field) (z : Point) : ℂ :=
  ∑ i, ∑ j, (metric z)⁻¹ i j *
    (coordDeriv i (coordDeriv j S) z - ∑ k, christoffel z k i j * coordDeriv k S z)

/-- Scalar connection terms cancel in the metric trace. -/
theorem scalarLaplacian_eq (S : Field) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian S z = (z 1 : ℂ) ^ (2 : ℕ) *
      (coordDeriv 0 (coordDeriv 0 S) z + coordDeriv 1 (coordDeriv 1 S) z) := by
  simp only [scalarLaplacian, metric_inverse z hz, christoffel_eq z hz]
  simp [connectionTable, Fin.sum_univ_two]
  ring

/-- The trace of the actual covector derivative has no remaining connection term. -/
theorem divergence_eq (V : Covector) (z : Point) (hz : 0 < z 1) :
    divergence V z = (z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (V 0) z + coordDeriv 1 (V 1) z) := by
  simp only [divergence, metric_inverse z hz, covariant_eq V z hz]
  simp [covariantFormula, Fin.sum_univ_two]
  ring

/-- Expanded rough covector Laplacian, including the curvature contribution. -/
def roughFormula (V : Covector) (k : Fin 2) (z : Point) : ℂ :=
  ![(z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (coordDeriv 0 (V 0)) z + coordDeriv 1 (coordDeriv 1 (V 0)) z) +
      2 * (z 1 : ℂ) * (coordDeriv 1 (V 0) z - coordDeriv 0 (V 1) z) - V 0 z,
    (z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (coordDeriv 0 (V 1)) z + coordDeriv 1 (coordDeriv 1 (V 1)) z) +
      2 * (z 1 : ℂ) * (coordDeriv 1 (V 1) z + coordDeriv 0 (V 0) z) - V 1 z] k

/-- Complete contraction of actual second covariant derivatives. -/
theorem roughLaplacian_eq (V : Covector) (z : Point) (hz : 0 < z 1)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) z) (k : Fin 2) :
    roughLaplacian V k z = roughFormula V k z := by
  simp only [roughLaplacian, metric_inverse z hz, covariant_partial_eq V z hz hV,
    christoffel_eq z hz, covariant_eq V z hz]
  have hzC : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  fin_cases k <;> simp [roughFormula, covariantPartialFormula, covariantFormula,
    connectionTable, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring

private theorem partial_neg (i : Fin 2) (f : Field) :
    coordDeriv i (fun q => -f q) = fun q => -coordDeriv i f q := by
  funext q
  simp [coordDeriv]

private theorem partial_mul {f g : Field} {z : Point}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun q => f q * g q) z =
      coordDeriv i f z * g z + f z * coordDeriv i g z := by
  simp only [coordDeriv, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

private theorem height_sq_partial (z : Point) (i : Fin 2) :
    coordDeriv i (fun q : Point => (q 1 : ℂ) ^ (2 : ℕ)) z = if i = 1 then 2 * (z 1 : ℂ) else 0 := by
  have hY := Complex.ofRealCLM.hasFDerivAt.comp z
    ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
  have hd : HasFDerivAt (fun q : Point => (q 1 : ℂ) ^ (2 : ℕ)) _ z := hY.pow 2
  rw [coordDeriv, hd.fderiv]
  fin_cases i <;> simp [smul_eq_mul]

/-- Actual derivative of the scalar metric-trace Laplacian. -/
theorem scalarLaplacian_partial (S : Field) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 3 S z) (i : Fin 2) :
    coordDeriv i (scalarLaplacian S) z =
      (if i = 1 then 2 * (z 1 : ℂ) else 0) *
        (coordDeriv 0 (coordDeriv 0 S) z + coordDeriv 1 (coordDeriv 1 S) z) +
      (z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv i (coordDeriv 0 (coordDeriv 0 S)) z +
        coordDeriv i (coordDeriv 1 (coordDeriv 1 S)) z) := by
  have he : scalarLaplacian S =ᶠ[𝓝 z] (fun q => (q 1 : ℂ) ^ (2 : ℕ) *
      (coordDeriv 0 (coordDeriv 0 S) q + coordDeriv 1 (coordDeriv 1 S) q)) := by
    filter_upwards [positive_nhds z hz] with q hq
    exact scalarLaplacian_eq S q hq
  have hY : DifferentiableAt ℝ (fun q : Point => (q 1 : ℂ) ^ (2 : ℕ)) z :=
    ((Complex.ofRealCLM.hasFDerivAt.comp z
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)).pow 2).differentiableAt
  have h00 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hS 0) 0).differentiableAt
  have h11 := (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hS 1) 1).differentiableAt
  change fderiv ℝ (scalarLaplacian S) z (Pi.single i 1) = _
  rw [he.fderiv_eq]
  change coordDeriv i (fun q => (q 1 : ℂ) ^ (2 : ℕ) *
    (coordDeriv 0 (coordDeriv 0 S) q + coordDeriv 1 (coordDeriv 1 S) q)) z = _
  have hsum : DifferentiableAt ℝ (fun q : Point =>
      coordDeriv 0 (coordDeriv 0 S) q + coordDeriv 1 (coordDeriv 1 S) q) z := h00.add h11
  rw [partial_mul hY hsum, height_sq_partial, partial_add h00 h11]

private theorem third_inner_commute {S : Field} {z : Point}
    (hS : ContDiffAt ℝ 3 S z) (i j k : Fin 2) :
    coordDeriv i (coordDeriv j (coordDeriv k S)) z =
      coordDeriv i (coordDeriv k (coordDeriv j S)) z := by
  have h2 : ContDiffAt ℝ 2 S z := hS.of_le (by norm_num)
  have he : coordDeriv j (coordDeriv k S) =ᶠ[𝓝 z] coordDeriv k (coordDeriv j S) := by
    filter_upwards [h2.eventually (by simp)] with q hq
    exact coordDeriv_commute hq j k
  exact congrArg (fun L => L (Pi.single i 1)) (he.fderiv_eq (𝕜 := ℝ))

private theorem third_cycle {S : Field} {z : Point}
    (hS : ContDiffAt ℝ 3 S z) (i j k : Fin 2) :
    coordDeriv i (coordDeriv j (coordDeriv k S)) z =
      coordDeriv k (coordDeriv i (coordDeriv j S)) z := by
  rw [third_inner_commute hS i j k]
  exact coordDeriv_commute (coordDeriv_contDiffAt (m := 2) hS j) i k

/-- The oriented coexact covector uses the actual scalar coordinate derivatives. -/
def coexact (S : Field) : Covector := ![coordDeriv 1 S, fun q => -coordDeriv 0 S q]

/-- The coordinate area form of the literal horizon metric. -/
def areaForm (z : Point) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (z 1 : ℂ)⁻¹ ^ (2 : ℕ); -(z 1 : ℂ)⁻¹ ^ (2 : ℕ), 0]

/-- The rotated derivative is the literal area-form/inverse-metric contraction. -/
theorem coexact_metric_contraction (S : Field) (z : Point) (hz : 0 < z 1) (i : Fin 2) :
    (∑ j, ∑ k, areaForm z i j * (metric z)⁻¹ j k * coordDeriv k S z) = coexact S i z := by
  rw [metric_inverse z hz]
  have hzC : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  fin_cases i <;> simp [areaForm, coexact, Fin.sum_univ_two]
  all_goals field_simp

/-- Differentiating the scalar loses exactly the one order needed by this construction. -/
theorem coexact_contDiffAt {S : Field} {z : Point} {m : WithTop ℕ∞}
    (hS : ContDiffAt ℝ (m + 1) S z) (i : Fin 2) : ContDiffAt ℝ m (coexact S i) z := by
  fin_cases i
  · exact coordDeriv_contDiffAt hS 1
  · exact (coordDeriv_contDiffAt hS 0).neg

/-- Coexact covectors have zero actual covariant divergence. -/
theorem coexact_divergence (S : Field) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 2 S z) : divergence (coexact S) z = 0 := by
  rw [divergence_eq _ z hz]
  simp only [coexact, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hn : coordDeriv 1 (fun q => -coordDeriv 0 S q) z = -coordDeriv 1 (coordDeriv 0 S) z := by
    simp [coordDeriv]
  rw [hn, coordDeriv_commute hS 0 1]
  ring

/-- The actual scalar/vector intertwining identity includes the curvature term -V. -/
theorem coexact_roughLaplacian (S : Field) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 3 S z) (k : Fin 2) :
    roughLaplacian (coexact S) k z = coexact (scalarLaplacian S) k z - coexact S k z := by
  rw [roughLaplacian_eq _ z hz (fun j => coexact_contDiffAt (m := 2) hS j)]
  fin_cases k <;> simp [roughFormula, coexact, partial_neg, scalarLaplacian_partial S z hz hS]
  · rw [third_cycle hS 0 0 1]
    ring
  · rw [third_cycle hS 1 1 0, coordDeriv_commute (hS.of_le (by norm_num)) 0 1]
    ring

/-- The covector spectral shift follows from the actual scalar field equation. -/
theorem coexact_eigen_equation (S : Field) (q : ℂ) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 3 S z)
    (heq : ∀ w : Point, 0 < w 1 → scalarLaplacian S w = -q * S w) (k : Fin 2) :
    roughLaplacian (coexact S) k z = -(q + 1) * coexact S k z := by
  have he : scalarLaplacian S =ᶠ[𝓝 z] (fun w => -q * S w) := by
    filter_upwards [positive_nhds z hz] with w hw
    exact heq w hw
  have hd := (((hS.differentiableAt (by norm_num)).hasFDerivAt).const_mul (-q)).congr_of_eventuallyEq he
  have hi (j : Fin 2) : coordDeriv j (scalarLaplacian S) z = -q * coordDeriv j S z := by
    rw [coordDeriv, hd.fderiv]
    simp [coordDeriv, smul_eq_mul]
  rw [coexact_roughLaplacian S z hz hS]
  fin_cases k <;> simp [coexact, hi] <;> ring

end
end RHTower.D4BMHorizon
