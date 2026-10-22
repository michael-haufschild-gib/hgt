import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalMetricBoundary

namespace RHTower.D4BMFundamentalScalarMetric
open GaloisForLFunctions.HTGeometry
open D4BMMetricReconstruction D4BMFundamentalMaster
open Filter Topology
open scoped ContDiff
noncomputable section

/-- Scalar harmonic parameter forced by the fundamental frequency with time rate s. -/
def harmonicParameter (s : ℂ) : ℂ := -(s+1)*(s+2)

/-- The common actual temporal and radial factor in the fundamental scalar field. -/
def envelope (s a : ℂ) (x : Fin 4 → ℝ) : ℂ :=
  a * Complex.exp (s * (x 0 : ℂ)) * D4BMPhysicalMaster.factor (Complex.I*s) (bmCoordinate x)

/-- Explicit radial matrix obtained from the original scalar KI reconstruction. -/
def radialMatrix (s r y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let f := r^(2 : ℕ)-1
  let tt := s*(s-3)/2+s*(s+1)/(2*r^(2 : ℕ))
  let tr := -s*(r^(2 : ℕ)-s)/(r*f)
  let aa := (-r^(2 : ℕ)-s*(s+1)/2)*y⁻¹^(2 : ℕ)
  !![tt,tr,0,0; tr,tt/f^(2 : ℕ),0,0; 0,0,aa,0; 0,0,0,aa]

/-- A closed separated expression for the actual scalar perturbation. -/
def field (s a : ℂ) (S : (Fin 2 → ℝ) → ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (envelope s a x * S (angularPoint x)) • radialMatrix s (x 1) (x 3)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- The separated matrix equals the literal covariant reconstruction at the
fundamental dispersion; it is not an independently chosen metric ansatz. -/
theorem reconstruction_eq (s a : ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (V : Fin 2 → (Fin 2 → ℝ) → ℂ) (p : D4BMBackground.ExteriorPoint) :
    D4BMFundamentalMetric.perturbation (Complex.I*s) (harmonicParameter s) a 0 S V p.val =
      field s a S p.val := by
  have hrR : 0 < p.val 1 := lt_trans zero_lt_one p.property.1
  have hr : (p.val 1 : ℂ) ≠ 0 := by exact_mod_cast hrR.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have hd := (master_hasDerivAt (Complex.I*s) (bmCoordinate p.val)
    (exterior_coordinate_domain p).1 (exterior_coordinate_domain p).2).deriv
  have hb : boundaryFactor (bmCoordinate p.val) = (p.val 1 : ℂ)⁻¹ :=
    D4BMFundamentalMetricBoundary.boundaryFactor_radius (p.val 1) hrR
  have ht : -Complex.I*(Complex.I*s)*(p.val 0 : ℂ) = s*(p.val 0 : ℂ) := by
    ring_nf
    simp [Complex.I_sq]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [D4BMFundamentalMetric.perturbation, D4BMFundamentalMetric.primitives,
    primitiveFields, covariantMetric, covariantMetricFromOrbits,
    D4BMFundamentalMetric.horizonFields, D4BMFundamentalMetric.horizonScale,
    d4KIScalarGaugeInvariantOrbitOfBMMaster, d4KIScalarMasslessTopologicalX,
    d4KIScalarMasslessTopologicalY, d4KIScalarMasslessTopologicalZtilde,
    d4KIVectorGaugeInvariantOrbitOfBMMaster, deriv_const_mul_field, hd]
  all_goals simp [first, master, rate, hb, d4BMIngoingHorizonExponent, field, envelope,
    radialMatrix, harmonicParameter, angularPoint]
  all_goals unfold bmCoordinate
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

private theorem coordinate_contDiff (k : Fin 4) (m : WithTop ℕ∞) :
    ContDiff ℝ m (fun x : Fin 4 → ℝ => (x k : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)

/-- Every finite derivative of the literal common factor exists on the exterior. -/
theorem envelope_contDiffAt (s a : ℂ) (p : D4BMBackground.ExteriorPoint)
    (m : WithTop ℕ∞) : ContDiffAt ℝ m (envelope s a) p.val := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hz : ContDiffAt ℝ m bmCoordinate p.val :=
    contDiffAt_const.sub (((coordinate_contDiff 1 m).contDiffAt.inv hr).pow 2)
  have ht : ContDiffAt ℝ m (fun x : Fin 4 → ℝ => Complex.exp (s*(x 0 : ℂ))) p.val :=
    Complex.contDiff_exp.contDiffAt.comp p.val
      (contDiffAt_const.mul (coordinate_contDiff 0 m).contDiffAt)
  have hA := ((D4BMPhysicalMaster.factor_contDiffAt (Complex.I*s) (bmCoordinate p.val)
    (exterior_coordinate_domain p).1 m).restrict_scalars ℝ).comp p.val hz
  exact (contDiffAt_const.mul ht).mul hA

private theorem radialMatrix_contDiffAt (s : ℂ) (p : D4BMBackground.ExteriorPoint)
    (m : WithTop ℕ∞) (i j : Fin 4) :
    ContDiffAt ℝ m (fun x : Fin 4 → ℝ => radialMatrix s (x 1) (x 3) i j) p.val := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hy : (p.val 3 : ℂ) ≠ 0 := by exact_mod_cast p.property.2.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have hR := (coordinate_contDiff 1 m).contDiffAt (x := p.val)
  have hY := (coordinate_contDiff 3 m).contDiffAt (x := p.val)
  have hiR := hR.inv hr
  have hiY := hY.inv hy
  have hiF := ((hR.pow 2).sub contDiffAt_const).inv hf
  fin_cases i <;> fin_cases j <;>
    simp [radialMatrix, div_eq_mul_inv, mul_inv_rev, inv_pow]
  all_goals fun_prop (disch := simp_all)

/-- Actual scalar metric regularity follows from its literal radial factors and horizon field. -/
theorem field_contDiffAt (s a : ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (p : D4BMBackground.ExteriorPoint) (m : WithTop ℕ∞)
    (hS : ContDiffAt ℝ m S (angularPoint p.val)) (i j : Fin 4) :
    ContDiffAt ℝ m (fun x => field s a S x i j) p.val := by
  have hu : ContDiff ℝ m angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  exact ((envelope_contDiffAt s a p m).mul (hS.comp p.val hu.contDiffAt)).mul
    (radialMatrix_contDiffAt s p m i j)

/-- Coordinate jet of the actual real chart coordinate, with complex values. -/
def coordinateJet (v : ℂ) (i : Fin 4) : ScalarTwoJet (Fin 4) ℂ :=
  ⟨v, fun k => if k = i then 1 else 0, fun _ _ => 0⟩

/-- Every ordered derivative of a coordinate agrees with its elementary jet. -/
theorem coordinate_jet (x : Fin 4 → ℝ) (k : Fin 4) :
    ScalarTwoJet.ofField (fun z : Fin 4 → ℝ => (z k : ℂ)) x = coordinateJet (x k) k := by
  have hd (i : Fin 4) :
      ScalarTwoJet.coordDeriv i (fun z : Fin 4 → ℝ => (z k : ℂ)) =
        fun _ => if i = k then 1 else 0 := by
    funext z
    change fderiv ℝ (Complex.ofRealCLM.comp (ContinuousLinearMap.proj k)) z (Pi.single i 1) = _
    rw [ContinuousLinearMap.fderiv]
    by_cases hi : i = k
    · simp [hi]
    · simp [hi, Ne.symm hi]
  ext i j
  · rfl
  · exact congrFun (hd i) x
  · change ScalarTwoJet.coordDeriv i
      (ScalarTwoJet.coordDeriv j (fun z : Fin 4 → ℝ => (z k : ℂ))) x = 0
    rw [hd]
    simp [ScalarTwoJet.coordDeriv]

private def radialCoordinateJet (r : ℂ) : ScalarTwoJet (Fin 4) ℂ :=
  (ScalarTwoJet.constant 1).add (((coordinateJet r 1).inv.mul (coordinateJet r 1).inv).neg)

private theorem radialCoordinate_jet (p : D4BMBackground.ExteriorPoint) :
    ScalarTwoJet.ofField bmCoordinate p.val = radialCoordinateJet (p.val 1) := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hR := (coordinate_contDiff 1 2).contDiffAt (x := p.val)
  have hiR := hR.inv hr
  have hb : bmCoordinate = fun x : Fin 4 → ℝ => 1 + -((x 1 : ℂ)⁻¹*(x 1 : ℂ)⁻¹) := by
    funext x
    simp only [bmCoordinate, pow_two, sub_eq_add_neg]
  rw [hb, ScalarTwoJet.ofField_add
    (f := fun _ : Fin 4 → ℝ => (1 : ℂ))
    (g := fun x : Fin 4 → ℝ => -((x 1 : ℂ)⁻¹*(x 1 : ℂ)⁻¹))
    contDiffAt_const (hiR.mul hiR).neg,
    ScalarTwoJet.ofField_constant, ScalarTwoJet.ofField_neg,
    ScalarTwoJet.ofField_mul (f := fun x : Fin 4 → ℝ => (x 1 : ℂ)⁻¹)
      (g := fun x : Fin 4 → ℝ => (x 1 : ℂ)⁻¹) hiR hiR,
    ScalarTwoJet.ofField_inv (f := fun x : Fin 4 → ℝ => (x 1 : ℂ)) hR hr, coordinate_jet]
  rfl

private theorem log_second (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    deriv (deriv Complex.log) z = -(z⁻¹ ^ (2 : ℕ)) := by
  have he : deriv Complex.log =ᶠ[nhds z] fun w => w⁻¹ := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
    exact Complex.deriv_log hw
  rw [he.deriv_eq]
  simp

private theorem ofField_log {g : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hz : g x ∈ Complex.slitPlane) :
    ScalarTwoJet.ofField (fun y => Complex.log (g y)) x =
      ScalarTwoJet.compose (ScalarTwoJet.ofField g x) (Complex.log (g x))
        (g x)⁻¹ (-((g x)⁻¹ ^ (2 : ℕ))) := by
  rw [ScalarTwoJet.ofField_comp (Complex.contDiffAt_log hz) hg,
    Complex.deriv_log hz, log_second (g x) hz]

/-- The actual common factor is one exponential of its separated exponent. -/
theorem envelope_eq_exp (s a : ℂ) (x : Fin 4 → ℝ) :
    envelope s a x = a * Complex.exp
      (s*(x 0 : ℂ)+(s/2)*Complex.log (bmCoordinate x)) := by
  have hs : d4BMIngoingHorizonExponent (Complex.I*s) = s/2 := by
    unfold d4BMIngoingHorizonExponent
    ring_nf
    simp [Complex.I_sq]
    ring
  simp only [envelope, D4BMPhysicalMaster.factor, hs, mul_assoc, ← Complex.exp_add]

/-- Full temporal/radial jet, retaining its mixed derivative and radial rate derivative. -/
def envelopeJet (s r B : ℂ) : ScalarTwoJet (Fin 4) ℂ where
  value := B
  first := ![s*B, s*B/(r*(r^(2 : ℕ)-1)), 0, 0]
  second := !![s^(2 : ℕ)*B, s^(2 : ℕ)*B/(r*(r^(2 : ℕ)-1)), 0, 0;
    s^(2 : ℕ)*B/(r*(r^(2 : ℕ)-1)), B*(s^(2 : ℕ)-s*(3*r^(2 : ℕ)-1))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)), 0, 0;
    0, 0, 0, 0; 0, 0, 0, 0]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- The displayed temporal/radial jet is proved equal to actual coordinate derivatives. -/
theorem envelope_jet (s a : ℂ) (p : D4BMBackground.ExteriorPoint) :
    ScalarTwoJet.ofField (envelope s a) p.val =
      envelopeJet s (p.val 1) (envelope s a p.val) := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have hR := (coordinate_contDiff 1 2).contDiffAt (x := p.val)
  have hT := (coordinate_contDiff 0 2).contDiffAt (x := p.val)
  have hz : ContDiffAt ℝ 2 bmCoordinate p.val :=
    contDiffAt_const.sub ((hR.inv hr).pow 2)
  have hcut := (exterior_coordinate_domain p).1
  have hz0 : 1 - (p.val 1 : ℂ)⁻¹ ^ (2 : ℕ) ≠ 0 := Complex.slitPlane_ne_zero hcut
  have hlog : ContDiffAt ℝ 2 (fun x => Complex.log (bmCoordinate x)) p.val :=
    ((Complex.contDiffAt_log hcut).restrict_scalars ℝ).comp p.val hz
  let Q : (Fin 4 → ℝ) → ℂ := fun x => s*(x 0 : ℂ)+(s/2)*Complex.log (bmCoordinate x)
  have hQ : ContDiffAt ℝ 2 Q p.val :=
    (contDiffAt_const.mul hT).add (contDiffAt_const.mul hlog)
  have he : envelope s a = fun x => a*Complex.exp (Q x) := funext (envelope_eq_exp s a)
  have hExp : ContDiffAt ℝ 2 (fun x => Complex.exp (Q x)) p.val := by
    simpa only [Function.comp_def] using Complex.contDiff_exp.contDiffAt.comp p.val hQ
  rw [he, ScalarTwoJet.ofField_mul (f := fun _ => a) (g := fun x => Complex.exp (Q x))
    contDiffAt_const hExp, ScalarTwoJet.ofField_constant,
    ScalarTwoJet.ofField_comp Complex.contDiff_exp.contDiffAt hQ]
  simp only [Complex.deriv_exp]
  have hQJ : ScalarTwoJet.ofField Q p.val =
      ((ScalarTwoJet.constant s).mul (coordinateJet (p.val 0) 0)).add
        ((ScalarTwoJet.constant (s/2)).mul
          (ScalarTwoJet.compose (radialCoordinateJet (p.val 1))
            (Complex.log (bmCoordinate p.val)) (bmCoordinate p.val)⁻¹
              (-((bmCoordinate p.val)⁻¹ ^ (2 : ℕ))))) := by
    rw [show Q = fun x => s*(x 0 : ℂ)+(s/2)*Complex.log (bmCoordinate x) from rfl,
      ScalarTwoJet.ofField_add (contDiffAt_const.mul hT) (contDiffAt_const.mul hlog),
      ScalarTwoJet.ofField_mul contDiffAt_const hT,
      ScalarTwoJet.ofField_mul contDiffAt_const hlog,
      ScalarTwoJet.ofField_constant, ScalarTwoJet.ofField_constant, coordinate_jet,
      ofField_log hz hcut, radialCoordinate_jet]
  rw [hQJ]
  ext i j
  · rfl
  · fin_cases i <;>
      simp [envelopeJet, radialCoordinateJet, coordinateJet, ScalarTwoJet.compose,
        ScalarTwoJet.mul, ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv,
        ScalarTwoJet.constant, bmCoordinate]
    all_goals field_simp [hr, hf, hz0]
    all_goals ring
  · fin_cases i <;> fin_cases j <;>
      simp [envelopeJet, radialCoordinateJet, coordinateJet, ScalarTwoJet.compose,
        ScalarTwoJet.mul, ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv,
        ScalarTwoJet.constant, bmCoordinate]
    all_goals try simp only [← pow_two, ← sub_eq_add_neg]
    all_goals field_simp [hr, hf, hz0]
    all_goals ring

end
end RHTower.D4BMFundamentalScalarMetric
