import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearEinsteinEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorLinearizedRicciJet

namespace RHTower.D4BMVectorLinearEquation
open GaloisForLFunctions.HTGeometry
open ScalarTwoJet D4BMMetricReconstruction D4BMFundamentalMaster
open D4BMScalarLinearEquation
open Filter Topology
noncomputable section

/-- Actual separated vector time block. -/
def timeBlock (s a : ℂ) (x : Fin 4 → ℝ) : ℂ :=
  (-s*D4BMFundamentalScalarMetric.envelope s a x)*(x 1 : ℂ)⁻¹

/-- Actual separated vector radial block. -/
def radialBlock (s a : ℂ) (x : Fin 4 → ℝ) : ℂ :=
  (-s*D4BMFundamentalScalarMetric.envelope s a x)*((x 1 : ℂ)^2-1)⁻¹

/-- Full symmetric vector perturbation, with both horizon covector entries. -/
def field (s a : ℂ) (V : D4BMHorizon.Covector) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let t := timeBlock s a x
  let r := radialBlock s a x
  let v := fun k => V k (angularPoint x)
  !![0,0,t*v 0,t*v 1; 0,0,r*v 0,r*v 1;
    t*v 0,r*v 0,0,0; t*v 1,r*v 1,0,0]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- The separated vector expression equals the original covariant KI reconstruction. -/
theorem reconstruction_eq (s a q : ℂ) (S : D4BMHorizon.Field)
    (V : D4BMHorizon.Covector) (p : D4BMBackground.ExteriorPoint) :
    D4BMFundamentalMetric.perturbation (Complex.I*s) q 0 a S V p.val =
      field s a V p.val := by
  have hrR : 0 < p.val 1 := lt_trans zero_lt_one p.property.1
  have hr : (p.val 1 : ℂ) ≠ 0 := by exact_mod_cast hrR.ne'
  have hf : (p.val 1 : ℂ)^2-1 ≠ 0 := by
    have h : (p.val 1)^2-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have hd := (master_hasDerivAt (Complex.I*s) (bmCoordinate p.val)
    (exterior_coordinate_domain p).1 (exterior_coordinate_domain p).2).deriv
  have hb : boundaryFactor (bmCoordinate p.val) = (p.val 1 : ℂ)⁻¹ :=
    D4BMFundamentalMetricBoundary.boundaryFactor_radius (p.val 1) hrR
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [D4BMFundamentalMetric.perturbation, D4BMFundamentalMetric.primitives,
    primitiveFields, covariantMetric, covariantMetricFromOrbits,
    D4BMFundamentalMetric.horizonFields, D4BMFundamentalMetric.horizonScale,
    d4KIScalarGaugeInvariantOrbitOfBMMaster, d4KIScalarMasslessTopologicalX,
    d4KIScalarMasslessTopologicalY, d4KIScalarMasslessTopologicalZtilde,
    d4KIVectorGaugeInvariantOrbitOfBMMaster, deriv_const_mul_field, hd]
  all_goals simp [D4BMFundamentalMaster.first, master, rate, hb, d4BMIngoingHorizonExponent,
    field, timeBlock, radialBlock, D4BMFundamentalScalarMetric.envelope, angularPoint]
  all_goals unfold bmCoordinate
  all_goals field_simp [hr,hf]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

private theorem flat_divergence_zero (V : D4BMHorizon.Covector)
    (hD : ∀ z, 0 < z 1 → D4BMHorizon.divergence V z = 0)
    (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    coordDeriv 0 (V 0) z + coordDeriv 1 (V 1) z = 0 := by
  have h := hD z hz
  rw [D4BMHorizon.divergence_eq V z hz] at h
  have hy : (z 1 : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hy)

private theorem flat_divergence_partial (V : D4BMHorizon.Covector)
    (hD : ∀ z, 0 < z 1 → D4BMHorizon.divergence V z = 0)
    (z : D4BMHorizon.Point) (hz : 0 < z 1)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) z) (k : Fin 2) :
    coordDeriv k (coordDeriv 0 (V 0)) z + coordDeriv k (coordDeriv 1 (V 1)) z = 0 := by
  have he : (fun w => coordDeriv 0 (V 0) w + coordDeriv 1 (V 1) w) =ᶠ[nhds z]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact flat_divergence_zero V hD w hw
  have hd : coordDeriv k (fun w => coordDeriv 0 (V 0) w + coordDeriv 1 (V 1) w) z = 0 := by
    change fderiv ℝ _ z (Pi.single k 1) = 0
    rw [he.fderiv_eq]
    simp
  have h0 := (D4BMHorizon.coordDeriv_hasFDerivAt (hV 0) 0).differentiableAt
  have h1 := (D4BMHorizon.coordDeriv_hasFDerivAt (hV 1) 1).differentiableAt
  simpa only [coordDeriv, fderiv_fun_add h0 h1, add_apply] using hd

/-- Actual full horizon covector jets, with divergence and rough equations retained. -/
theorem angular_jets (s : ℂ) (V : D4BMHorizon.Covector)
    (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → D4BMHorizon.divergence V z = 0)
    (hL : ∀ k, D4BMHorizon.roughLaplacian V k (angularPoint p.val) =
      ((s+1)*(s+2)-1)*V k (angularPoint p.val)) :
    (ofField (fun x => V 0 (angularPoint x)) p.val =
      angular0 s (p.val 3) (V 0 (angularPoint p.val))
        (coordDeriv 0 (V 0) (angularPoint p.val)) (coordDeriv 1 (V 0) (angularPoint p.val))
        (coordDeriv 0 (V 1) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 (V 0)) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 1 (V 0)) (angularPoint p.val))) ∧
    (ofField (fun x => V 1 (angularPoint x)) p.val =
      angular1 s (p.val 3) (V 1 (angularPoint p.val))
        (coordDeriv 0 (V 0) (angularPoint p.val)) (coordDeriv 0 (V 1) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 (V 0)) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 1 (V 0)) (angularPoint p.val))) := by
  let z := angularPoint p.val
  have hz : 0 < z 1 := p.property.2
  have hy : (p.val 3 : ℂ) ≠ 0 := by exact_mod_cast p.property.2.ne'
  have hd := flat_divergence_zero V hD z hz
  have hd0 := flat_divergence_partial V hD z hz hV 0
  have hd1 := flat_divergence_partial V hD z hz hV 1
  have hc (k : Fin 2) : coordDeriv 1 (coordDeriv 0 (V k)) z =
      coordDeriv 0 (coordDeriv 1 (V k)) z := D4BMHorizon.coordDeriv_commute (hV k) 1 0
  have hl0 := hL 0
  have hl1 := hL 1
  rw [D4BMHorizon.roughLaplacian_eq V z hz hV 0] at hl0
  rw [D4BMHorizon.roughLaplacian_eq V z hz hV 1] at hl1
  change (p.val 3 : ℂ)^2*(coordDeriv 0 (coordDeriv 0 (V 0)) z +
    coordDeriv 1 (coordDeriv 1 (V 0)) z)+2*(p.val 3 : ℂ)*
    (coordDeriv 1 (V 0) z-coordDeriv 0 (V 1) z)-V 0 z = _ at hl0
  change (p.val 3 : ℂ)^2*(coordDeriv 0 (coordDeriv 0 (V 1)) z +
    coordDeriv 1 (coordDeriv 1 (V 1)) z)+2*(p.val 3 : ℂ)*
    (coordDeriv 1 (V 1) z+coordDeriv 0 (V 0) z)-V 1 z = _ at hl1
  have hdy : coordDeriv 1 (V 1) z = -coordDeriv 0 (V 0) z := by linear_combination hd
  have hxy : coordDeriv 0 (coordDeriv 1 (V 1)) z =
      -coordDeriv 0 (coordDeriv 0 (V 0)) z := by linear_combination hd0
  have hyy : coordDeriv 1 (coordDeriv 1 (V 1)) z =
      -coordDeriv 0 (coordDeriv 1 (V 0)) z := by
    rw [hc 0] at hd1
    linear_combination hd1
  have hxx : coordDeriv 0 (coordDeriv 0 (V 1)) z =
      coordDeriv 0 (coordDeriv 1 (V 0)) z+(s+1)*(s+2)*V 1 z/(p.val 3 : ℂ)^2 := by
    rw [hdy,hyy] at hl1
    field_simp
    linear_combination hl1
  have hyy0 : coordDeriv 1 (coordDeriv 1 (V 0)) z =
      ((s+1)*(s+2)*V 0 z-2*(p.val 3 : ℂ)*(coordDeriv 1 (V 0) z-coordDeriv 0 (V 1) z)) /
        (p.val 3 : ℂ)^2 - coordDeriv 0 (coordDeriv 0 (V 0)) z := by
    field_simp
    linear_combination hl0
  rw [D4BMScalarLinearEquation.angular_lift_jet (V 0) p.val (hV 0),
    D4BMScalarLinearEquation.angular_lift_jet (V 1) p.val (hV 1)]
  change _ = angular0 _ _ _ _ _ _ _ _ ∧ _ = angular1 _ _ _ _ _ _ _
  simp only [angular0, angular1, ← show z = angularPoint p.val from rfl,
    hc, hdy, hxy, hyy, hxx, hyy0, and_self]

private theorem blocks_jets (s a : ℂ) (p : D4BMBackground.ExteriorPoint) :
    let R := coord (p.val 1) 1
    let F := (R.mul R).add (constant (-1))
    let B := (constant (-s)).mul (temporalRadial s (p.val 1)
      (D4BMFundamentalScalarMetric.envelope s a p.val))
    ofField (timeBlock s a) p.val = B.mul R.inv ∧
    ofField (radialBlock s a) p.val = B.mul F.inv := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^2-1 ≠ 0 := by
    have h : (p.val 1)^2-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hF : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)^2-1) p.val :=
    (hR.pow 2).sub contDiffAt_const
  have hB := D4BMFundamentalScalarMetric.envelope_contDiffAt s a p 2
  have hFJ : ofField (fun x : Fin 4 → ℝ => (x 1 : ℂ)^2-1) p.val =
      ((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1)) := by
    have he : (fun x : Fin 4 → ℝ => (x 1 : ℂ)^2-1) =
        fun x => (x 1 : ℂ)*(x 1 : ℂ)+(-1) := by funext x; ring
    rw [he, ofField_add (hR.mul hR) contDiffAt_const, ofField_mul hR hR,
      ofField_constant, D4BMFundamentalScalarMetric.coordinate_jet]
    rfl
  constructor
  · unfold timeBlock
    rw [ofField_mul (f := fun x => -s*D4BMFundamentalScalarMetric.envelope s a x)
      (g := fun x : Fin 4 → ℝ => (x 1 : ℂ)⁻¹) (contDiffAt_const.mul hB) (hR.inv hr),
      ofField_mul contDiffAt_const hB, ofField_constant, D4BMFundamentalScalarMetric.envelope_jet,
      ofField_inv hR hr, D4BMFundamentalScalarMetric.coordinate_jet]
    rfl
  · unfold radialBlock
    rw [ofField_mul (f := fun x => -s*D4BMFundamentalScalarMetric.envelope s a x)
      (g := fun x : Fin 4 → ℝ => ((x 1 : ℂ)^2-1)⁻¹) (contDiffAt_const.mul hB) (hF.inv hf),
      ofField_mul contDiffAt_const hB, ofField_constant, D4BMFundamentalScalarMetric.envelope_jet,
      ofField_inv hF hf, hFJ]
    rfl

private theorem blocks_contDiffAt (s a : ℂ) (p : D4BMBackground.ExteriorPoint) :
    ContDiffAt ℝ 2 (timeBlock s a) p.val ∧ ContDiffAt ℝ 2 (radialBlock s a) p.val := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^2-1 ≠ 0 := by
    have h : (p.val 1)^2-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hB := D4BMFundamentalScalarMetric.envelope_contDiffAt s a p 2
  exact ⟨(contDiffAt_const.mul hB).mul (hR.inv hr),
    (contDiffAt_const.mul hB).mul (((hR.pow 2).sub contDiffAt_const).inv hf)⟩

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) :
    CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,
    fun k l i j => (J i j).second k l⟩

/-- The solved vector jet is the actual complete jet of the reconstructed field. -/
theorem field_jet (s a : ℂ) (V : D4BMHorizon.Covector) (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → D4BMHorizon.divergence V z = 0)
    (hL : ∀ k, D4BMHorizon.roughLaplacian V k (angularPoint p.val) =
      ((s+1)*(s+2)-1)*V k (angularPoint p.val)) :
    ofMetricField (field s a V) p.val =
      vectorJet s (p.val 1) (p.val 3) (D4BMFundamentalScalarMetric.envelope s a p.val)
        (V 0 (angularPoint p.val)) (V 1 (angularPoint p.val))
        (coordDeriv 0 (V 0) (angularPoint p.val)) (coordDeriv 1 (V 0) (angularPoint p.val))
        (coordDeriv 0 (V 1) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 (V 0)) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 1 (V 0)) (angularPoint p.val)) := by
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift (k : Fin 2) : ContDiffAt ℝ 2 (fun x => V k (angularPoint x)) p.val := by
    simpa only [Function.comp_def] using (hV k).comp p.val hu.contDiffAt
  have hTJ := (blocks_jets s a p).1
  have hRJ := (blocks_jets s a p).2
  have hA := angular_jets s V p hV hD hL
  have ht0 := ofField_mul (f := timeBlock s a) (g := fun x => V 0 (angularPoint x))
    (blocks_contDiffAt s a p).1 (hLift 0)
  have ht1 := ofField_mul (f := timeBlock s a) (g := fun x => V 1 (angularPoint x))
    (blocks_contDiffAt s a p).1 (hLift 1)
  have hr0 := ofField_mul (f := radialBlock s a) (g := fun x => V 0 (angularPoint x))
    (blocks_contDiffAt s a p).2 (hLift 0)
  have hr1 := ofField_mul (f := radialBlock s a) (g := fun x => V 1 (angularPoint x))
    (blocks_contDiffAt s a p).2 (hLift 1)
  rw [hTJ,hA.1] at ht0
  rw [hTJ,hA.2] at ht1
  rw [hRJ,hA.1] at hr0
  rw [hRJ,hA.2] at hr1
  change assemble _ = assemble _
  congr 1
  funext i j
  fin_cases i <;> fin_cases j
  all_goals first | exact ofField_constant 0 p.val | exact ht0 | exact ht1 | exact hr0 | exact hr1

/-- Every actual vector field component has zero first cosmological residual. -/
theorem field_residual_zero (s a : ℂ) (V : D4BMHorizon.Covector) (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → D4BMHorizon.divergence V z = 0)
    (hL : ∀ k, D4BMHorizon.roughLaplacian V k (angularPoint p.val) =
      ((s+1)*(s+2)-1)*V k (angularPoint p.val)) (i j : Fin 4) :
    D4BMLinearizedEinsteinSource.residual p (ofMetricField (field s a V) p.val) i j = 0 := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hy : (p.val 3 : ℂ) ≠ 0 := by exact_mod_cast p.property.2.ne'
  have hf : (p.val 1 : ℂ)^2-1 ≠ 0 := by
    have h : (p.val 1)^2-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  rw [D4BMLinearizedEinsteinSource.residual, D4BMBackground.actualJet_eq, field_jet s a V p hV hD hL]
  exact D4BMVectorLinearEquation.cosmological_component _ _ _ _ _ _ _ _ _ _ _ hr hy hf i j

private theorem ofField_congr_germ {f g : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (h : f =ᶠ[nhds x] g) : ofField f x = ofField g x := by
  have hD : fderiv ℝ f =ᶠ[nhds x] fderiv ℝ g := h.fderiv
  have hd (k : Fin 4) : coordDeriv k f =ᶠ[nhds x] coordDeriv k g := by
    filter_upwards [hD] with y hy
    exact congrArg (fun L => L (Pi.single k 1)) hy
  ext i j
  · exact h.self_of_nhds
  · change fderiv ℝ f x (Pi.single i 1) = fderiv ℝ g x (Pi.single i 1)
    rw [h.fderiv_eq]
  · change fderiv ℝ (coordDeriv j f) x (Pi.single i 1) =
      fderiv ℝ (coordDeriv j g) x (Pi.single i 1)
    rw [(hd j).fderiv_eq]

private theorem reconstruction_jet (s a q : ℂ) (S : D4BMHorizon.Field)
    (V : D4BMHorizon.Covector) (p : D4BMBackground.ExteriorPoint) :
    ofMetricField (D4BMFundamentalMetric.perturbation (Complex.I*s) q 0 a S V) p.val =
      ofMetricField (field s a V) p.val := by
  change assemble _ = assemble _
  congr 1
  funext i j
  apply ofField_congr_germ
  have hO : IsOpen {x : Fin 4 → ℝ | 1 < x 1 ∧ 0 < x 3} :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (continuous_apply 3))
  filter_upwards [hO.mem_nhds p.property] with x hx
  exact congrArg (fun M => M i j) (reconstruction_eq s a q S V ⟨x,hx⟩)

/-- The original vector KI source has zero actual first amplitude derivative. -/
theorem reconstructed_source_first_zero (s a q : ℂ) (S : D4BMHorizon.Field)
    (V : D4BMHorizon.Covector) (p : D4BMBackground.ExteriorPoint)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → D4BMHorizon.divergence V z = 0)
    (hL : ∀ k, D4BMHorizon.roughLaplacian V k (angularPoint p.val) =
      ((s+1)*(s+2)-1)*V k (angularPoint p.val)) (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMFundamentalMetric.perturbation (Complex.I*s) q 0 a S V) i j) 0 = 0 := by
  rw [(D4BMLinearizedEinsteinSource.fundamental_source_hasDerivAt p (Complex.I*s)
    q 0 a S V hS hV i j).deriv,
    D4BMFundamentalMetric.fullJet_correct p (Complex.I*s) q 0 a S V hS hV,
    reconstruction_jet s a q S V p]
  exact field_residual_zero s a V p hV hD hL i j

private theorem literal_source_first_zero (s a u : ℂ) (p : D4BMBackground.ExteriorPoint)
    (hq : D4BMFundamentalScalarMetric.harmonicParameter s = D4BMLiteralCusp.scalarQ u)
    (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMLiteralCusp.perturbation (Complex.I*s) u 0 a) i j) 0 = 0 := by
  apply reconstructed_source_first_zero s a (D4BMLiteralCusp.scalarQ u)
    (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) p
    (D4BMLiteralCusp.scalar_contDiffAt u 2 _ p.property.2)
    (D4BMLiteralCusp.vector_contDiffAt u 2 _ p.property.2)
    (D4BMLiteralCusp.vector_divergence u)
  intro k
  rw [D4BMLiteralCusp.vector_equation u _ p.property.2 k, ← hq]
  unfold D4BMFundamentalScalarMetric.harmonicParameter d4HyperbolicHodgePairedVectorEigenvalue
  ring

/-- The complete literal coexact cusp vector satisfies every first-order Einstein
component at the fundamental plus frequency, with all angular premises discharged. -/
theorem literal_plus_source_first_zero (u a : ℂ) (p : D4BMBackground.ExteriorPoint)
    (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum u))
        u 0 a) i j) 0 = 0 := by
  have hf : d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum u) =
      Complex.I*(-u-3/2) := by
    simp only [d4BMCausalQNMPlus, d4BMCausalDecay, D4BMLiteralCusp.radialMomentum,
      Nat.cast_zero, mul_zero, zero_add]
    ring
  rw [hf]
  apply literal_source_first_zero
  unfold D4BMFundamentalScalarMetric.harmonicParameter D4BMLiteralCusp.scalarQ
  ring

/-- The complete literal coexact cusp vector satisfies every first-order Einstein
component at the fundamental minus frequency, with all angular premises discharged. -/
theorem literal_minus_source_first_zero (u a : ℂ) (p : D4BMBackground.ExteriorPoint)
    (i j : Fin 4) :
    deriv (D4BMActualMetricSource.source p
      (D4BMLiteralCusp.perturbation (d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum u))
        u 0 a) i j) 0 = 0 := by
  have hf : d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum u) =
      Complex.I*(u-3/2) := by
    simp only [d4BMCausalQNMMinus, d4BMCausalDecay, D4BMLiteralCusp.radialMomentum,
      Nat.cast_zero, mul_zero, zero_add]
    ring
  rw [hf]
  apply literal_source_first_zero
  unfold D4BMFundamentalScalarMetric.harmonicParameter D4BMLiteralCusp.scalarQ
  ring

end
end RHTower.D4BMVectorLinearEquation
