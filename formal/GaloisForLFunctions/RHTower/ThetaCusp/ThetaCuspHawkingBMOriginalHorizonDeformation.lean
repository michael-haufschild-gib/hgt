import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullLinearEinsteinEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIngoingCoordinates

/-!
# Original theta metric: moved null cut and retained spin-two deformation

All sixteen components are identified with the original scalar/vector metric under
its differentiated ingoing coordinate change. Their actual exterior horizon limit
supplies the first null-surface displacement and angular generator. The original
infinite scalar equation forces the induced deformation to have zero metric trace.
Its full bilinear contraction retains independent scalar/scalar and vector/vector
terms. Distinct angular parameters retain an antisymmetric mixed Hessian term;
that mixed contraction vanishes when the angular fields coincide.

These are source-derived first-order null-cut identities. This file does not
construct a global event horizon, prove the nonlinear Raychaudhuri equation, or
identify a complete corrected physical left-QNM action with this contraction.
Second-order displacements, correction fields, boundary currents, and extinction
remain outside these conclusions. The original time and radial branches are kept.
-/

set_option autoImplicit false

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMMovingHorizon
open D4BMHorizon
noncomputable section

abbrev AngularPoint := {z : Point // 0 < z 1}

def rate (u : ℂ) (b : Bool) : ℂ := if b then u-3/2 else -u-3/2

private theorem rate_parameter (u : ℂ) (b : Bool) :
    D4BMFundamentalScalarMetric.harmonicParameter (rate u b) =
      D4BMLiteralCusp.scalarQ u := by
  cases b <;> simp only [rate, Bool.false_eq_true, if_false, if_true,
    D4BMFundamentalScalarMetric.harmonicParameter, D4BMLiteralCusp.scalarQ] <;> ring

/-- The regular ingoing expression for every component of the original first field. -/
def regularMetric (s aS aV E r y S Vx Vy : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let T := aS*E*S*(s*(s-3)/2+s*(s+1)/(2*r^(2 : ℕ)))
  let C := -aS*E*S*s*(r-1)*(2*r+s+1)/(2*r^(2 : ℕ)*(r+1))
  let R := aS*E*S*s*(2*r+s+1)/(r^(2 : ℕ)*(r+1)^(2 : ℕ))
  let A := -aS*E*S*(r^(2 : ℕ)+s*(s+1)/2)*y⁻¹^(2 : ℕ)
  let t := -s*aV*E/r
  let d := -s*aV*E/(r*(r+1))
  !![T,C,t*Vx,t*Vy; C,R,d*Vx,d*Vy; t*Vx,d*Vx,A,0; t*Vy,d*Vy,0,A]

/-- Exact tensor identification at every exterior point, before taking a horizon limit. -/
theorem regularMetric_eq_pullback (u aS aV : ℂ) (b : Bool)
    (p : D4BMBackground.ExteriorPoint) :
    D4BMIngoingCoordinates.pullback (p.val 1 : ℂ)
        (D4BMLiteralCusp.perturbation (Complex.I*rate u b) u aS aV p.val) =
      regularMetric (rate u b) aS aV
        (D4BMFundamentalScalarMetric.envelope (rate u b) 1 p.val)
        (p.val 1) (p.val 3) (D4BMLiteralCusp.scalar u (D4BMMetricReconstruction.angularPoint p.val))
        (D4BMLiteralCusp.vector u 0 (D4BMMetricReconstruction.angularPoint p.val))
        (D4BMLiteralCusp.vector u 1 (D4BMMetricReconstruction.angularPoint p.val)) := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hp : (p.val 1 : ℂ)+1 ≠ 0 := by
    have h : p.val 1+1 ≠ 0 := by linarith [p.property.1]
    exact_mod_cast h
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  rw [D4BMFullLinearEquation.literal_perturbation_split]
  change D4BMIngoingCoordinates.pullback _
    (D4BMFundamentalMetric.perturbation _ (D4BMLiteralCusp.scalarQ u) aS 0 _ _ p.val +
      D4BMFundamentalMetric.perturbation _ (D4BMLiteralCusp.scalarQ u) 0 aV _ _ p.val) = _
  rw [← rate_parameter u b,
    D4BMFundamentalScalarMetric.reconstruction_eq (rate u b) aS _ _ p,
    D4BMVectorLinearEquation.reconstruction_eq (rate u b) aV _ _ _ p]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [D4BMIngoingCoordinates.pullback, D4BMIngoingCoordinates.jacobian,
    Matrix.mul_apply, Fin.sum_univ_succ, D4BMFundamentalScalarMetric.field,
    D4BMFundamentalScalarMetric.radialMatrix, D4BMFundamentalScalarMetric.envelope,
    D4BMVectorLinearEquation.field, D4BMVectorLinearEquation.timeBlock,
    D4BMVectorLinearEquation.radialBlock, regularMetric]
  all_goals field_simp [hr,hp,hf]
  all_goals try simp only [true_or]
  all_goals ring

/-- The regular field keeps the original ingoing coordinate change and physical clock. -/
theorem regularMetric_ingoing_source (u aS aV : ℂ) (b : Bool) (v : ℝ)
    (z : AngularPoint) (r : {r : ℝ // 1 < r}) :
    D4BMIngoingCoordinates.pullback (r : ℂ)
      (D4BMLiteralCusp.perturbation (Complex.I*rate u b) u aS aV
        (D4BMIngoingCoordinates.staticPoint (D4BMFundamentalMetricBoundary.staticRay v z r))) =
      regularMetric (rate u b) aS aV
        (D4BMIngoingCoordinates.compactEnvelope (rate u b) 1 v (r : ℂ)⁻¹)
        r (z.val 1) (D4BMLiteralCusp.scalar u z)
        (D4BMLiteralCusp.vector u 0 z) (D4BMLiteralCusp.vector u 1 z) := by
  let x := D4BMFundamentalMetricBoundary.staticRay v z r
  have hp : 1 < D4BMIngoingCoordinates.staticPoint x 1 ∧
      0 < D4BMIngoingCoordinates.staticPoint x 3 := by
    simpa [D4BMIngoingCoordinates.staticPoint, x, D4BMFundamentalMetricBoundary.staticRay]
      using And.intro r.property z.property
  have h := regularMetric_eq_pullback u aS aV b ⟨D4BMIngoingCoordinates.staticPoint x,hp⟩
  change D4BMIngoingCoordinates.pullback _ _ =
    regularMetric _ _ _ (D4BMFundamentalScalarMetric.envelope (rate u b) 1
      (D4BMIngoingCoordinates.staticPoint x)) _ _ _ _ _ at h
  rw [D4BMIngoingCoordinates.envelope_staticPoint (rate u b) 1 x r.property] at h
  have hz : ![z.val 0,z.val 1] = z.val := by
    ext k
    fin_cases k <;> rfl
  simpa [D4BMIngoingCoordinates.staticPoint, x, D4BMFundamentalMetricBoundary.staticRay,
    D4BMMetricReconstruction.angularPoint, hz] using h

def envelope (s : ℂ) (v : ℝ) : ℂ := Complex.exp (s*((v : ℂ)+Complex.log 2))

/-- The same original radial/time branch evaluated at the horizon. -/
def horizonMetric (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : Point) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  regularMetric (rate u b) aS aV (envelope (rate u b) v) 1 (z 1)
    (D4BMLiteralCusp.scalar u z) (D4BMLiteralCusp.vector u 0 z) (D4BMLiteralCusp.vector u 1 z)

/-- This is a genuine limit of the regular extension of the reconstructed tensor. -/
theorem horizonMetric_limit (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : Point) (i j : Fin 4) :
    Tendsto (fun r : ℂ => regularMetric (rate u b) aS aV
      (D4BMIngoingCoordinates.compactEnvelope (rate u b) 1 v r⁻¹) r (z 1)
      (D4BMLiteralCusp.scalar u z) (D4BMLiteralCusp.vector u 0 z)
      (D4BMLiteralCusp.vector u 1 z) i j) (𝓝 1) (𝓝 (horizonMetric u aS aV b v z i j)) := by
  have hI : ContinuousAt (fun r : ℂ => r⁻¹) 1 :=
    continuousAt_id.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hE : ContinuousAt (fun r : ℂ =>
      D4BMIngoingCoordinates.compactEnvelope (rate u b) 1 v r⁻¹) 1 := by
    have h := (D4BMIngoingCoordinates.compactEnvelope_contDiffAt (rate u b) 1 v 1
      (by norm_num [Complex.mem_slitPlane_iff]) 0).continuousAt
    exact (h.comp_of_eq hI (by simp))
  have he : ContinuousAt (fun r : ℂ => regularMetric (rate u b) aS aV
      (D4BMIngoingCoordinates.compactEnvelope (rate u b) 1 v r⁻¹) r (z 1)
      (D4BMLiteralCusp.scalar u z) (D4BMLiteralCusp.vector u 0 z)
      (D4BMLiteralCusp.vector u 1 z) i j) 1 := by
    fin_cases i <;> fin_cases j <;> simp only [regularMetric]
    all_goals fun_prop (disch := norm_num)
  simpa [horizonMetric, D4BMIngoingCoordinates.compactEnvelope, envelope,
    show (1 : ℂ)+1=2 by norm_num] using he.tendsto

/-- Actual exterior limit of every original metric component in the ingoing chart. -/
theorem original_metric_horizon (u aS aV : ℂ) (b : Bool) (v : ℝ)
    (z : AngularPoint) (i j : Fin 4) :
    Tendsto (fun r : ℝ => D4BMIngoingCoordinates.pullback (r : ℂ)
      (D4BMLiteralCusp.perturbation (Complex.I*rate u b) u aS aV
        (D4BMIngoingCoordinates.staticPoint (D4BMFundamentalMetricBoundary.staticRay v z r))) i j)
      (𝓝[Set.Ioi 1] 1) (𝓝 (horizonMetric u aS aV b v z i j)) := by
  have ht := (horizonMetric_limit u aS aV b v z i j).comp
    ((Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 1)))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j)
    (regularMetric_ingoing_source u aS aV b v z ⟨r,hr⟩).symm

private theorem envelope_deriv (s : ℂ) (v : ℝ) :
    HasDerivAt (envelope s) (s*envelope s v) v := by
  convert! (((Complex.ofRealCLM.hasDerivAt (x := v)).add_const
    (Complex.log 2)).const_mul s).cexp using 1
  simp [envelope, mul_comm]

/-- Separated displacement solving the original first null-surface equation. -/
def displacement (u aS : ℂ) (b : Bool) (v : ℝ) : Field :=
  fun z => (-rate u b*aS*envelope (rate u b) v/2)*D4BMLiteralCusp.scalar u z

private theorem displacement_deriv (u aS : ℂ) (b : Bool) (v : ℝ) (z : Point) :
    HasDerivAt (fun t => displacement u aS b t z)
      (rate u b*displacement u aS b v z) v := by
  convert! (((envelope_deriv (rate u b) v).const_mul (-rate u b*aS)).div_const 2).mul_const
    (D4BMLiteralCusp.scalar u z) using 1
  simp only [displacement]
  ring

/-- The first inverse-metric/null-normal contraction vanishes on this moved cut.
The coefficient 1 is the original background surface gravity. -/
theorem displacement_null_equation (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : Point) :
    2*displacement u aS b v z-horizonMetric u aS aV b v z 0 0-
      2*deriv (fun t => displacement u aS b t z) v = 0 := by
  rw [(displacement_deriv u aS b v z).deriv]
  simp [displacement, horizonMetric, regularMetric]
  ring

def angularIndex : Fin 2 → Fin 4 := ![2,3]

/-- Angular component of the displaced null generator, as a covector. -/
def angularShift (u aS aV : ℂ) (b : Bool) (v : ℝ) : Covector :=
  fun i z => rate u b*envelope (rate u b) v*
    (aS/2*ScalarTwoJet.coordDeriv i (D4BMLiteralCusp.scalar u) z+aV*D4BMLiteralCusp.vector u i z)

/-- The generator is obtained from the metric's original mixed component and graph normal. -/
theorem angularShift_eq (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : AngularPoint) (i : Fin 2) :
    angularShift u aS aV b v i z =
      -ScalarTwoJet.coordDeriv i (displacement u aS b v) z-
        horizonMetric u aS aV b v z 0 (angularIndex i) := by
  have hS := (D4BMLiteralCusp.scalar_contDiffAt u 1 z z.property).differentiableAt (by norm_num)
  have hd : ScalarTwoJet.coordDeriv i (displacement u aS b v) z =
      (-rate u b*aS*envelope (rate u b) v/2)*
        ScalarTwoJet.coordDeriv i (D4BMLiteralCusp.scalar u) z := by
    unfold ScalarTwoJet.coordDeriv displacement
    rw [fderiv_const_mul hS]
    rfl
  rw [hd]
  fin_cases i <;> simp [angularShift, angularIndex, horizonMetric, regularMetric] <;> ring

/-- Metric variation induced on the moved cut, with the radial displacement retained. -/
def cutMetric (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : Point) (i j : Fin 2) : ℂ :=
  2*displacement u aS b v z*metric z i j+
    horizonMetric u aS aV b v z (angularIndex i) (angularIndex j)

private theorem cutMetric_eq (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : Point) (i j : Fin 2) :
    cutMetric u aS aV b v z i j = aS*envelope (rate u b) v*
      D4BMLiteralCusp.scalarQ u/2*D4BMLiteralCusp.scalar u z*metric z i j := by
  rw [← rate_parameter u b]
  fin_cases i <;> fin_cases j
  all_goals simp [cutMetric, displacement, horizonMetric, regularMetric,
    angularIndex, metric, D4BMFundamentalScalarMetric.harmonicParameter]
  all_goals ring

private theorem cutMetric_deriv (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : Point) (i j : Fin 2) :
    deriv (fun t => cutMetric u aS aV b t z i j) v = rate u b*cutMetric u aS aV b v z i j := by
  simp_rw [cutMetric_eq]
  have hd := (((((envelope_deriv (rate u b) v).const_mul aS).mul_const
    (D4BMLiteralCusp.scalarQ u)).div_const 2).mul_const
    (D4BMLiteralCusp.scalar u z)).mul_const (metric z i j)
  rw [hd.deriv]
  ring

def hessian (u : ℂ) (z : Point) (i j : Fin 2) : ℂ :=
  covariant (fun k => ScalarTwoJet.coordDeriv k (D4BMLiteralCusp.scalar u)) i j z

def tracefreeHessian (u : ℂ) (z : Point) (i j : Fin 2) : ℂ :=
  hessian u z i j-scalarLaplacian (D4BMLiteralCusp.scalar u) z/2*metric z i j

def rotatedHessian (u : ℂ) (z : Point) (i j : Fin 2) : ℂ :=
  (covariant (D4BMLiteralCusp.vector u) i j z+covariant (D4BMLiteralCusp.vector u) j i z)/2

private theorem hessian_symm (u : ℂ) (z : AngularPoint) (i j : Fin 2) :
    hessian u z i j = hessian u z j i := by
  simp only [hessian, covariant_eq _ z z.property]
  fin_cases i <;> fin_cases j <;> simp [covariantFormula,
    coordDeriv_commute (D4BMLiteralCusp.scalar_contDiffAt u 2 z z.property) 0 1]

private theorem angularShift_covariant (u aS aV : ℂ) (b : Bool) (v : ℝ)
    (z : AngularPoint) (i j : Fin 2) :
    covariant (angularShift u aS aV b v) i j z = rate u b*envelope (rate u b) v*
      (aS/2*hessian u z i j+aV*covariant (D4BMLiteralCusp.vector u) i j z) := by
  have hG := (coordDeriv_hasFDerivAt (D4BMLiteralCusp.scalar_contDiffAt u 2 z z.property) j).differentiableAt
  have hV := (D4BMLiteralCusp.vector_contDiffAt u 1 z z.property j).differentiableAt (by norm_num)
  have hd : ScalarTwoJet.coordDeriv i (angularShift u aS aV b v j) z =
      rate u b*envelope (rate u b) v*
        (aS/2*ScalarTwoJet.coordDeriv i (ScalarTwoJet.coordDeriv j (D4BMLiteralCusp.scalar u)) z+
          aV*ScalarTwoJet.coordDeriv i (D4BMLiteralCusp.vector u j) z) := by
    have hd := ((hG.hasFDerivAt.const_mul (aS/2)).add
      (hV.hasFDerivAt.const_mul aV)).const_mul (rate u b*envelope (rate u b) v)
    have he := congrArg (fun L : Point →L[ℝ] ℂ => L (Pi.single i 1)) hd.fderiv
    convert! he using 1
  simp only [covariant, hd, angularShift, hessian, Fin.sum_univ_two]
  ring

/-- Half the first Lie derivative of the induced metric along the displaced generator. -/
def deformation (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : Point) (i j : Fin 2) : ℂ :=
  deriv (fun t => cutMetric u aS aV b t z i j) v/2+
    (covariant (angularShift u aS aV b v) i j z+
      covariant (angularShift u aS aV b v) j i z)/2

/-- The literal source equation removes expansion and retains both spin-two polarizations. -/
theorem deformation_eq (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : AngularPoint) (i j : Fin 2) :
    deformation u aS aV b v z i j = rate u b*envelope (rate u b) v*
      (aS/2*tracefreeHessian u z i j+aV*rotatedHessian u z i j) := by
  rw [deformation, cutMetric_deriv, cutMetric_eq,
    angularShift_covariant, angularShift_covariant, hessian_symm u z j i]
  simp only [tracefreeHessian, rotatedHessian, D4BMLiteralCusp.scalar_equation u z z.property]
  ring

def spinA (u : ℂ) (z : Point) : ℂ :=
  (ScalarTwoJet.coordDeriv 0 (ScalarTwoJet.coordDeriv 0 (D4BMLiteralCusp.scalar u)) z-
    ScalarTwoJet.coordDeriv 1 (ScalarTwoJet.coordDeriv 1 (D4BMLiteralCusp.scalar u)) z)/2-
    (z 1 : ℂ)⁻¹*ScalarTwoJet.coordDeriv 1 (D4BMLiteralCusp.scalar u) z

def spinB (u : ℂ) (z : Point) : ℂ :=
  ScalarTwoJet.coordDeriv 0 (ScalarTwoJet.coordDeriv 1 (D4BMLiteralCusp.scalar u)) z+
    (z 1 : ℂ)⁻¹*ScalarTwoJet.coordDeriv 0 (D4BMLiteralCusp.scalar u) z

private theorem tracefreeHessian_values (u : ℂ) (z : AngularPoint) :
    tracefreeHessian u z = !![spinA u z,spinB u z; spinB u z,-spinA u z] := by
  have hy : (z.val 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.property.ne'
  ext i j
  simp only [tracefreeHessian, hessian, covariant_eq _ z z.property,
    scalarLaplacian_eq _ z z.property]
  fin_cases i <;> fin_cases j
  all_goals simp [covariantFormula, metric, spinA, spinB,
    coordDeriv_commute (D4BMLiteralCusp.scalar_contDiffAt u 2 z z.property) 1 0]
  all_goals field_simp [hy]
  all_goals ring

private theorem partial_neg (i : Fin 2) (f : Field) (z : Point) :
    ScalarTwoJet.coordDeriv i (fun w => -f w) z = -ScalarTwoJet.coordDeriv i f z := by
  simp [ScalarTwoJet.coordDeriv]

private theorem rotatedHessian_values (u : ℂ) (z : AngularPoint) :
    rotatedHessian u z = !![spinB u z,-spinA u z; -spinA u z,-spinB u z] := by
  ext i j
  simp only [rotatedHessian, covariant_eq _ z z.property]
  fin_cases i <;> fin_cases j
  all_goals simp [covariantFormula, D4BMLiteralCusp.vector, coexact, spinA, spinB,
    partial_neg, coordDeriv_commute (D4BMLiteralCusp.scalar_contDiffAt u 2 z z.property) 1 0]
  all_goals ring

/-- Actual inverse-metric trace of the displaced-cut deformation vanishes. -/
theorem deformation_trace_zero (u aS aV : ℂ) (b : Bool) (v : ℝ) (z : AngularPoint) :
    (∑ i, ∑ j, (metric z)⁻¹ i j*deformation u aS aV b v z i j) = 0 := by
  simp_rw [deformation_eq u aS aV b v z, metric_inverse z z.property,
    tracefreeHessian_values u z, rotatedHessian_values u z]
  simp [Fin.sum_univ_two]
  ring

/-- Bilinear tensor contraction with both indices raised by the actual horizon metric. -/
def contraction (z : Point) (H K : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (metric z)⁻¹ i k*(metric z)⁻¹ j l*H i j*K k l

private theorem contraction_eq (z : AngularPoint) (H K : Matrix (Fin 2) (Fin 2) ℂ) :
    contraction z H K = (z.val 1 : ℂ)^(4 : ℕ)*
      (H 0 0*K 0 0+H 0 1*K 0 1+H 1 0*K 1 0+H 1 1*K 1 1) := by
  simp [contraction, metric_inverse z z.property, Fin.sum_univ_two]
  ring

/-- Distinct literal angular fields retain an antisymmetric mixed spin-two term. -/
theorem hessian_rotated_pairing (u w : ℂ) (z : AngularPoint) :
    contraction z (tracefreeHessian u z) (rotatedHessian w z) =
      2*(z.val 1 : ℂ)^(4 : ℕ)*(spinA u z*spinB w z-spinB u z*spinA w z) := by
  rw [contraction_eq, tracefreeHessian_values, rotatedHessian_values]
  simp
  ring

/-- Complete local pairing with independent source parameters and polarizations.
The mixed determinant may be discarded only after an actual source/reader identification. -/
theorem deformation_pairing_general (u w aS aV cS cV : ℂ) (b c : Bool)
    (v : ℝ) (z : AngularPoint) :
    contraction z (deformation u aS aV b v z) (deformation w cS cV c v z) =
      rate u b*rate w c*envelope (rate u b) v*envelope (rate w c) v*
        ((aS*cS/4+aV*cV)*contraction z (tracefreeHessian u z) (tracefreeHessian w z)+
          (aS*cV-aV*cS)/2*contraction z (tracefreeHessian u z) (rotatedHessian w z)) := by
  rw [contraction_eq, contraction_eq, contraction_eq]
  simp_rw [deformation_eq u aS aV b v z, deformation_eq w cS cV c v z,
    tracefreeHessian_values u z, tracefreeHessian_values w z,
    rotatedHessian_values u z, rotatedHessian_values w z]
  simp
  ring

/-- Both scalar and vector source polarizations survive in the exact horizon pairing.
The mixed angular contraction cancels; no complex square is declared positive. -/
theorem deformation_pairing (u aS aV cS cV : ℂ) (b c : Bool) (v : ℝ) (z : AngularPoint) :
    contraction z (deformation u aS aV b v z) (deformation u cS cV c v z) =
      rate u b*rate u c*envelope (rate u b) v*envelope (rate u c) v*
        (aS*cS/4+aV*cV)*contraction z (tracefreeHessian u z) (tracefreeHessian u z) := by
  rw [contraction_eq, contraction_eq]
  simp_rw [deformation_eq u aS aV b v z, deformation_eq u cS cV c v z,
    tracefreeHessian_values u z, rotatedHessian_values u z]
  simp
  ring

/-- Exact retained spin-two square, expressed in actual angular derivatives and metric weight. -/
theorem tracefreeHessian_square (u : ℂ) (z : AngularPoint) :
    contraction z (tracefreeHessian u z) (tracefreeHessian u z) =
      2*(z.val 1 : ℂ)^(4 : ℕ)*(spinA u z^(2 : ℕ)+spinB u z^(2 : ℕ)) := by
  rw [contraction_eq, tracefreeHessian_values]
  simp
  ring

end
end RHTower.D4BMMovingHorizon
