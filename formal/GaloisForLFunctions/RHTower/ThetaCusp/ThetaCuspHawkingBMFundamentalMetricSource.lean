import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalMonodromyMaster
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Physical fundamental BM master profiles

The fundamental profile is `z^(-i omega/2) * (1-z)^(1/2)`.
Its actual physical radial residual factors into the two literal fundamental
BM frequencies.  The ingoing normalization and Dirichlet limit are proved
separately from the equation.  These local radial facts do not assert causal
admissibility of a completed nonlinear source.
-/

open Complex Set Filter Topology
namespace RHTower.D4BMFundamentalMaster
noncomputable section

/-- The vanishing four-dimensional Dirichlet factor. -/
def boundaryFactor (z : ℂ) : ℂ := (1 - z) ^ (1 / 2 : ℂ)

/-- Full physical fundamental profile, including both spatial factors. -/
def master (omega z : ℂ) : ℂ :=
  D4BMPhysicalMaster.factor omega z * boundaryFactor z

/-- Logarithmic derivative of the full fundamental profile. -/
def rate (omega z : ℂ) : ℂ :=
  d4BMIngoingHorizonExponent omega * z⁻¹ - (1 / 2 : ℂ) * (1 - z)⁻¹

/-- Derivative of the logarithmic derivative, retaining the boundary factor. -/
def rateFirst (omega z : ℂ) : ℂ :=
  -d4BMIngoingHorizonExponent omega * z⁻¹ ^ 2 - (1 / 2 : ℂ) * (1 - z)⁻¹ ^ 2

/-- Exact first physical jet. -/
def first (omega z : ℂ) : ℂ := master omega z * rate omega z

/-- Exact second physical jet. -/
def second (omega z : ℂ) : ℂ := master omega z * (rate omega z ^ 2 + rateFirst omega z)

private theorem domain_open :
    IsOpen {z : ℂ | z ∈ Complex.slitPlane ∧ 1 - z ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.inter
    (Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id))

/-- Smoothness of the boundary factor on its natural logarithm chart. -/
theorem boundaryFactor_contDiffAt (z : ℂ) (hz : 1 - z ∈ Complex.slitPlane)
    (m : WithTop ℕ∞) : ContDiffAt ℂ m boundaryFactor z := by
  have he : boundaryFactor =ᶠ[nhds z]
      (fun w => Complex.exp (Complex.log (1 - w) * (1 / 2 : ℂ))) := by
    filter_upwards [(Complex.isOpen_slitPlane.preimage
      (continuous_const.sub continuous_id)).mem_nhds hz] with w hw
    exact Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw) _
  have hs : ContDiffAt ℂ m
      (fun w : ℂ => Complex.exp (Complex.log (1 - w) * (1 / 2 : ℂ))) z :=
    Complex.contDiff_exp.contDiffAt.comp z
      (((Complex.contDiffAt_log hz).comp z (contDiffAt_const.sub contDiffAt_id)).mul
        contDiffAt_const)
  exact hs.congr_of_eventuallyEq he

/-- Actual derivative of the vanishing boundary factor. -/
theorem boundaryFactor_hasDerivAt (z : ℂ) (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt boundaryFactor (-boundaryFactor z * (1 / 2 : ℂ) * (1 - z)⁻¹) z := by
  have h := ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).cpow_const
    (c := (1 / 2 : ℂ)) hz
  convert! h using 1
  dsimp [boundaryFactor]
  rw [Complex.cpow_sub _ _ (Complex.slitPlane_ne_zero hz), Complex.cpow_one]
  ring

/-- The physical fundamental profile is locally smooth to every order. -/
theorem master_contDiffAt (omega z : ℂ) (hz : z ∈ Complex.slitPlane)
    (h1 : 1 - z ∈ Complex.slitPlane) (m : WithTop ℕ∞) :
    ContDiffAt ℂ m (master omega) z :=
  (D4BMPhysicalMaster.factor_contDiffAt omega z hz m).mul
    (boundaryFactor_contDiffAt z h1 m)

/-- Actual first derivative, including both spatial-factor contributions. -/
theorem master_hasDerivAt (omega z : ℂ) (hz : z ∈ Complex.slitPlane)
    (h1 : 1 - z ∈ Complex.slitPlane) : HasDerivAt (master omega) (first omega z) z := by
  convert! (D4BMPhysicalMaster.factor_hasDerivAt omega z hz).mul
    (boundaryFactor_hasDerivAt z h1) using 1
  dsimp [first, master, rate]
  ring

private theorem rate_hasDerivAt (omega z : ℂ) (hz : z ≠ 0) (h1 : 1 - z ≠ 0) :
    HasDerivAt (rate omega) (rateFirst omega z) z := by
  have hi := (hasDerivAt_id z).inv hz
  have hj := ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).inv h1
  convert! (hi.const_mul (d4BMIngoingHorizonExponent omega)).sub
    (hj.const_mul (1 / 2 : ℂ)) using 1
  dsimp [rateFirst]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- Actual second derivative jet. -/
theorem first_hasDerivAt (omega z : ℂ) (hz : z ∈ Complex.slitPlane)
    (h1 : 1 - z ∈ Complex.slitPlane) : HasDerivAt (first omega) (second omega z) z := by
  convert! (master_hasDerivAt omega z hz h1).mul
    (rate_hasDerivAt omega z (Complex.slitPlane_ne_zero hz)
      (Complex.slitPlane_ne_zero h1)) using 1
  dsimp [first, second]
  ring

/-- The explicit second jet equals the actual iterated derivative. -/
theorem master_second_deriv (omega z : ℂ) (hz : z ∈ Complex.slitPlane)
    (h1 : 1 - z ∈ Complex.slitPlane) :
    deriv (deriv (master omega)) z = second omega z := by
  have he : deriv (master omega) =ᶠ[nhds z] first omega := by
    filter_upwards [domain_open.mem_nhds ⟨hz, h1⟩] with w hw
    exact (master_hasDerivAt omega w hw.1 hw.2).deriv
  rw [he.deriv_eq]
  exact (first_hasDerivAt omega z hz h1).deriv

/-- Fundamental radial dispersion is derived from the literal physical equation. -/
theorem radial_residual (omega chi z : ℂ) (hz : z ≠ 0) (h1 : 1 - z ≠ 0) :
    D4BMPhysicalMaster.radialJet omega chi z
      (master omega z) (first omega z) (second omega z) =
    ((omega - d4BMCausalQNMPlus 0 chi) * (omega - d4BMCausalQNMMinus 0 chi) / 4) *
      master omega z := by
  dsimp [D4BMPhysicalMaster.radialJet, first, second, rate, rateFirst,
    d4BMIngoingHorizonExponent, d4BMCausalQNMPlus, d4BMCausalQNMMinus, d4BMCausalDecay]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The profile has no interior zeros. -/
theorem master_ne_zero (omega z : ℂ) (h1 : 1 - z ≠ 0) : master omega z ≠ 0 := by
  apply mul_ne_zero (Complex.exp_ne_zero _)
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl h1)

/-- Exactly the two fundamental QNM frequencies solve the physical equation for this profile. -/
theorem radial_equation_iff (omega chi z : ℂ) (hz : z ∈ Complex.slitPlane)
    (h1 : 1 - z ∈ Complex.slitPlane) :
    D4BMPhysicalMaster.radialJet omega chi z (master omega z)
      (deriv (master omega) z) (deriv (deriv (master omega)) z) = 0 ↔
      omega = d4BMCausalQNMPlus 0 chi ∨ omega = d4BMCausalQNMMinus 0 chi := by
  rw [(master_hasDerivAt omega z hz h1).deriv, master_second_deriv omega z hz h1,
    radial_residual omega chi z (Complex.slitPlane_ne_zero hz) (Complex.slitPlane_ne_zero h1)]
  simp [mul_eq_zero, master_ne_zero omega z (Complex.slitPlane_ne_zero h1), sub_eq_zero]

/-- The full profile divided by its ingoing horizon factor is exactly the Dirichlet factor. -/
theorem master_div_ingoing_factor (omega z : ℂ) :
    master omega z / D4BMPhysicalMaster.factor omega z = boundaryFactor z := by
  dsimp [master]
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

/-- The incoming horizon normalization is exactly one. -/
theorem master_ingoing_normalization (omega : ℂ) :
    Tendsto (fun z : ℂ => master omega z / D4BMPhysicalMaster.factor omega z)
      (nhds 0) (nhds 1) := by
  have hc := (boundaryFactor_contDiffAt 0 (by simp [Complex.mem_slitPlane_iff]) 0).continuousAt
  simp_rw [master_div_ingoing_factor]
  have hv : boundaryFactor 0 = 1 := by norm_num [boundaryFactor]
  rw [← hv]
  exact hc.tendsto

/-- The boundary factor is continuous even at its vanishing Dirichlet endpoint. -/
theorem boundaryFactor_continuousAt_one : ContinuousAt boundaryFactor 1 := by
  have hc : ContinuousAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) (1 - 1 : ℂ) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by norm_num)) (by norm_num)
  exact hc.comp (continuousAt_const.sub continuousAt_id)

/-- The physical fundamental profile has the actual zero Dirichlet limit. -/
theorem master_dirichlet_limit (omega : ℂ) :
    Tendsto (master omega) (nhds 1) (nhds 0) := by
  have hc : ContinuousAt (master omega) 1 :=
    (D4BMPhysicalMaster.factor_contDiffAt omega 1
      (by simp [Complex.mem_slitPlane_iff]) 0).continuousAt.mul boundaryFactor_continuousAt_one
  have hv : master omega 1 = 0 := by norm_num [master, boundaryFactor]
  rw [← hv]
  exact hc.tendsto

/-- Its Fourier time dependence has the incoming horizon coordinate, not the outgoing one. -/
theorem master_ingoing_time_phase (omega : ℂ) (tau z : ℝ) (hz : 0 < z) :
    d4BMFourierTimePhase omega tau * master omega (z : ℂ) =
      Complex.exp (-Complex.I * omega * (d4BMIngoingHorizonCoordinate tau z : ℂ)) *
        boundaryFactor (z : ℂ) := by
  have h := d4BMFourierTimePhase_mul_ingoingHorizonLogPower omega tau z
  change _ * Complex.exp _ = _ at h
  dsimp [master, D4BMPhysicalMaster.factor]
  rw [← Complex.ofReal_log hz.le, ← mul_assoc, h]

/-- Both logarithm charts are valid at every static exterior point. -/
theorem exterior_coordinate_domain (p : D4BMBackground.ExteriorPoint) :
    D4BMMetricReconstruction.bmCoordinate p.val ∈ Complex.slitPlane ∧
      1 - D4BMMetricReconstruction.bmCoordinate p.val ∈ Complex.slitPlane := by
  refine ⟨(D4BMPhysicalMaster.exterior_coordinate_domain p).2, ?_⟩
  have he : 1 - D4BMMetricReconstruction.bmCoordinate p.val =
      (((p.val 1)⁻¹ ^ 2 : ℝ) : ℂ) := by
    simp [D4BMMetricReconstruction.bmCoordinate]
  rw [he]
  apply Complex.mem_slitPlane_iff.mpr
  left
  rw [Complex.ofReal_re]
  exact sq_pos_of_pos (inv_pos.mpr (lt_trans zero_lt_one p.property.1))

/-- The literal physical radial input is locally smooth at every exterior point. -/
theorem exterior_master_contDiffAt (omega : ℂ) (p : D4BMBackground.ExteriorPoint)
    (m : WithTop ℕ∞) :
    ContDiffAt ℂ m (master omega) (D4BMMetricReconstruction.bmCoordinate p.val) :=
  master_contDiffAt omega _ (exterior_coordinate_domain p).1 (exterior_coordinate_domain p).2 m

/-- Actual exterior radial equation for both source fundamental branches. -/
theorem exterior_fundamental_equations (chi : ℂ) (p : D4BMBackground.ExteriorPoint) :
    let z := D4BMMetricReconstruction.bmCoordinate p.val
    (D4BMPhysicalMaster.radialJet (d4BMCausalQNMPlus 0 chi) chi z
      (master (d4BMCausalQNMPlus 0 chi) z) (deriv (master (d4BMCausalQNMPlus 0 chi)) z)
      (deriv (deriv (master (d4BMCausalQNMPlus 0 chi))) z) = 0) ∧
    (D4BMPhysicalMaster.radialJet (d4BMCausalQNMMinus 0 chi) chi z
      (master (d4BMCausalQNMMinus 0 chi) z) (deriv (master (d4BMCausalQNMMinus 0 chi)) z)
      (deriv (deriv (master (d4BMCausalQNMMinus 0 chi))) z) = 0) := by
  constructor
  · exact (radial_equation_iff _ _ _ (exterior_coordinate_domain p).1
      (exterior_coordinate_domain p).2).mpr (Or.inl rfl)
  · exact (radial_equation_iff _ _ _ (exterior_coordinate_domain p).1
      (exterior_coordinate_domain p).2).mpr (Or.inr rfl)

end
end RHTower.D4BMFundamentalMaster

namespace RHTower.D4BMFundamentalMetric
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet
noncomputable section

/-- Literal upper-half-plane horizon scale in coordinates `(x,y)`. -/
def horizonScale (u : Fin 2 → ℝ) : ℂ := (u 1 : ℂ)⁻¹ ^ 2

/-- Scalar and vector profiles attached to the fixed hyperbolic horizon metric. -/
def horizonFields (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ) : HorizonFields where
  scalar := S
  vector := V
  metric00 := horizonScale
  metric01 := fun _ => 0
  metric11 := horizonScale

/-- The attached horizon metric agrees with the angular block of the proved BM background. -/
theorem horizonBlock_eq_background (S : (Fin 2 → ℝ) → ℂ)
    (V : Fin 2 → (Fin 2 → ℝ) → ℂ) (x : Fin 4 → ℝ) :
    (x 1 : ℂ) ^ 2 * (horizonFields S V).metric00 (angularPoint x) =
      metric (x 1) (x 3) 2 2 ∧
    (x 1 : ℂ) ^ 2 * (horizonFields S V).metric01 (angularPoint x) =
      metric (x 1) (x 3) 2 3 ∧
    (x 1 : ℂ) ^ 2 * (horizonFields S V).metric11 (angularPoint x) =
      metric (x 1) (x 3) 3 3 := by
  simp [horizonFields, horizonScale, angularPoint, metric]

/-- Horizon metric regularity is proved from its literal scale. -/
theorem horizonScale_contDiffAt (u : Fin 2 → ℝ) (hy : 0 < u 1)
    (m : WithTop ℕ∞) : ContDiffAt ℝ m horizonScale u := by
  have hc : ContDiffAt ℝ m (fun v : Fin 2 → ℝ => (v 1 : ℂ)) u :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hy' : (u 1 : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  exact (hc.inv hy').pow 2

/-- Complete primitive fields of a fundamental scalar/vector perturbation. -/
def primitives (omega aS aV : ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (V : Fin 2 → (Fin 2 → ℝ) → ℂ) : Primitive → (Fin 4 → ℝ) → ℂ :=
  primitiveFields omega (fun z => aS * D4BMFundamentalMaster.master omega z)
    (fun z => aV * D4BMFundamentalMaster.master omega z) (horizonFields S V)

private theorem radius_conditions (p : ExteriorPoint) :
    p.val 1 ≠ 0 ∧ (p.val 1 : ℂ) ≠ 0 ∧ (p.val 1 : ℂ) ^ 2 - 1 ≠ 0 := by
  have hr : p.val 1 ≠ 0 := ne_of_gt (lt_trans zero_lt_one p.property.1)
  have hf : p.val 1 ^ 2 - 1 ≠ 0 := by nlinarith [p.property.1]
  exact ⟨hr, by exact_mod_cast hr, by exact_mod_cast hf⟩

/-- Only the scalar/vector angular regularity remains explicit in the complete field recipe. -/
theorem primitives_contDiffAt (p : ExteriorPoint) (omega aS aV : ℂ)
    (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hV : ∀ i, ContDiffAt ℝ 2 (V i) (angularPoint p.val)) (b : Primitive) :
    ContDiffAt ℝ 2 (primitives omega aS aV S V b) p.val := by
  have hR := D4BMFundamentalMaster.exterior_master_contDiffAt omega p 3
  have hM := horizonScale_contDiffAt (angularPoint p.val) p.property.2 2
  exact primitiveFields_contDiffAt omega (radius_conditions p).1
    (contDiffAt_const.mul hR) (contDiffAt_const.mul hR) hS hV hM contDiffAt_const hM b

/-- The complete covariant perturbation from the physical fundamental profile. -/
def perturbation (omega kSq aS aV : ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (V : Fin 2 → (Fin 2 → ℝ) → ℂ) : MetricField :=
  fun x => covariantMetric omega kSq (fun b => primitives omega aS aV S V b x)

/-- Its explicit full metric jet, with actual radial, temporal and angular derivatives. -/
def fullJet (p : ExteriorPoint) (omega kSq aS aV : ℂ)
    (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  metricJet omega kSq (fun b => ScalarTwoJet.ofField (primitives omega aS aV S V b) p.val)

/-- The physical profile's full reconstructed jet agrees with actual coordinate derivatives. -/
theorem fullJet_correct (p : ExteriorPoint) (omega kSq aS aV : ℂ)
    (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hV : ∀ i, ContDiffAt ℝ 2 (V i) (angularPoint p.val)) :
    fullJet p omega kSq aS aV S V = ofMetricField (perturbation omega kSq aS aV S V) p.val :=
  metricJet_correct omega kSq (primitives_contDiffAt p omega aS aV S V hS hV)
    (radius_conditions p).2.1 (radius_conditions p).2.2

/-- Actual direct quadratic and cubic source coefficients with the physical radial profile
and fixed horizon geometry substituted. No independent radial regularity premise is needed. -/
theorem source_coefficients (p : ExteriorPoint) (omega kSq aS aV : ℂ)
    (S : (Fin 2 → ℝ) → ℂ) (V : Fin 2 → (Fin 2 → ℝ) → ℂ)
    (hS : ContDiffAt ℝ 2 S (angularPoint p.val))
    (hV : ∀ i, ContDiffAt ℝ 2 (V i) (angularPoint p.val)) (i j : Fin 4) :
    let h := perturbation omega kSq aS aV S V
    let u := toSpace (fullJet p omega kSq aS aV S V)
    (iteratedDeriv 2 (source p h i j) 0 / 2 = secondVariation (backgroundSpace p) i j u u / 2) ∧
    (iteratedDeriv 3 (source p h i j) 0 / 6 = thirdVariation (backgroundSpace p) i j u u u / 6) :=
  reconstructed_source_coefficients p omega kSq (primitives omega aS aV S V)
    (primitives_contDiffAt p omega aS aV S V hS hV)
    (radius_conditions p).2.1 (radius_conditions p).2.2 i j

end
end RHTower.D4BMFundamentalMetric
