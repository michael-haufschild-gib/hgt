import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCausalPotential
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeFieldMatchingNoGo

/-! # Polarization of the literal retarded causal source

The source amplitude enters every radial coefficient of the original causal problem as the single
factor `a²`.  Hence the retarded potential is exactly quadratic in the amplitude,
`U(a) = a² U(1)`, and its polarization is the symmetric two-leg field
`U[a, d] = a d U(1)`, with forcing `F[a, d] = a d F(1)`.  The two-leg field solves the original
forced wave equation on the physical null wedge, keeps the Dirichlet boundary value and the fixed
onset, and restricts on the diagonal to the original field and forcing. -/

open Set Filter Topology Complex

namespace RHTower.D4BMOriginalCausalPotential
open D4BMNativeResponse D4BMJointSource D4BMModularCore D4BMHorizon D4BMNativeFieldMatching

set_option autoImplicit false

/-! ### Every radial coefficient is `a²` times its unit-amplitude value -/

theorem sourceAmplitude_amplitude (s w a T : ℂ) (t : ℝ) :
    sourceAmplitude s w a T t = a ^ 2 * sourceAmplitude s w 1 T t := by
  simp only [sourceAmplitude]
  ring

theorem radialLift_amplitude (s w a T : ℂ) (t : ℝ) :
    radialLift s w a T t = a ^ 2 * radialLift s w 1 T t := by
  simp only [radialLift, sourceAmplitude_amplitude s w a]
  ring

theorem radialLiftFirst_amplitude (s w a T : ℂ) (t : ℝ) :
    radialLiftFirst s w a T t = a ^ 2 * radialLiftFirst s w 1 T t := by
  simp only [radialLiftFirst, sourceAmplitude_amplitude s w a]
  ring

theorem reducedCoefficient_amplitude (s w a T : ℂ) (t : ℝ) :
    reducedCoefficient s w a T t = a ^ 2 * reducedCoefficient s w 1 T t := by
  simp only [reducedCoefficient, sourceAmplitude_amplitude s w a]
  ring

theorem timeReducedCoefficient_amplitude (s a : ℂ) (τ t : ℝ) :
    timeReducedCoefficient s a τ t = a ^ 2 * timeReducedCoefficient s 1 τ t := by
  simp only [timeReducedCoefficient, reducedCoefficient_amplitude s 0 a,
    radialLiftFirst_amplitude s 0 a]
  ring

theorem oddSource_amplitude (s a : ℂ) (τ x : ℝ) :
    oddSource s a τ x = a ^ 2 * oddSource s 1 τ x := by
  simp only [oddSource, timeReducedCoefficient_amplitude s a]
  ring

theorem nullLift_amplitude (s a : ℂ) (p r : ℝ) :
    nullLift s a p r = a ^ 2 * nullLift s 1 p r := by
  simp only [nullLift, radialLift_amplitude s 0 a]
  ring

/-- The native causal response is quadratic in the amplitude: `a²` passes through both finite
null integrals of the native Riemann kernel against the odd source. -/
theorem fullNullResponse_amplitude (q : XiZeroCopy) (s a : ℂ) (p r X k : ℝ) :
    fullNullResponse q s a p r X k = a ^ 2 * fullNullResponse q s 1 p r X k := by
  rcases le_or_gt p 0 with hp | hp
  · rw [fullNullResponse_nonpositive q s a (Or.inl hp),
      fullNullResponse_nonpositive q s 1 (Or.inl hp), mul_zero]
  rcases le_or_gt r 0 with hr | hr
  · rw [fullNullResponse_nonpositive q s a (Or.inr hr),
      fullNullResponse_nonpositive q s 1 (Or.inr hr), mul_zero]
  rw [fullNullResponse_native q s a hp.le hr.le, fullNullResponse_native q s 1 hp.le hr.le]
  simp only [oddSource_amplitude s a, mul_left_comm _ (a ^ 2), intervalIntegral.integral_const_mul]

/-- **Quadratic retarded field.**  `U(q, br, a) = a² U(q, br, 1)` at every event. -/
theorem originalPotential_amplitude (q : XiZeroCopy) (br : Bool) (a : ℂ) (p r X k : ℝ) :
    originalPotential q br a p r X k = a ^ 2 * originalPotential q br 1 p r X k := by
  simp only [originalPotential, fullNullResponse_amplitude q _ a, nullLift_amplitude _ a]
  ring

/-! ### The two-leg source and field -/

/-- The two-leg causal source `F[a, d] = a d F(1)`. -/
noncomputable def twoLegForcing (q : XiZeroCopy) (br : Bool) (a d : ℂ) (τ t : ℝ) (z : Point) : ℂ :=
  a * d * timeOriginalForcing q br 1 τ t z

/-- The two-leg retarded field `U[a, d] = a d U(1)`. -/
noncomputable def twoLegPotential (q : XiZeroCopy) (br : Bool) (a d : ℂ) (p r X k : ℝ) : ℂ :=
  a * d * originalPotential q br 1 p r X k

/-- The two-leg source is the polarization of the quadratic original source. -/
theorem twoLegForcing_eq_polarization (q : XiZeroCopy) (br : Bool) (a d : ℂ) (τ t : ℝ)
    (z : Point) :
    twoLegForcing q br a d τ t z =
      (timeOriginalForcing q br (a + d) τ t z - timeOriginalForcing q br (a - d) τ t z) / 4 := by
  rw [twoLegForcing, timeOriginalForcing_quadratic q br (a + d),
    timeOriginalForcing_quadratic q br (a - d)]
  ring

/-- The two-leg field is the polarization of the quadratic retarded field. -/
theorem twoLegPotential_eq_polarization (q : XiZeroCopy) (br : Bool) (a d : ℂ) (p r X k : ℝ) :
    twoLegPotential q br a d p r X k =
      (originalPotential q br (a + d) p r X k - originalPotential q br (a - d) p r X k) / 4 := by
  rw [twoLegPotential, originalPotential_amplitude q br (a + d),
    originalPotential_amplitude q br (a - d)]
  ring

theorem twoLegForcing_symm (q : XiZeroCopy) (br : Bool) (a d : ℂ) :
    twoLegForcing q br a d = twoLegForcing q br d a := by
  funext τ t z
  simp only [twoLegForcing, mul_comm a d]

theorem twoLegPotential_symm (q : XiZeroCopy) (br : Bool) (a d : ℂ) :
    twoLegPotential q br a d = twoLegPotential q br d a := by
  funext p r X k
  simp only [twoLegPotential, mul_comm a d]

/-- On the diagonal the two-leg source is the original source. -/
theorem twoLegForcing_diag (q : XiZeroCopy) (br : Bool) (a : ℂ) :
    twoLegForcing q br a a = timeOriginalForcing q br a := by
  funext τ t z
  rw [twoLegForcing, timeOriginalForcing_quadratic q br a, sq]

/-- On the diagonal the two-leg field is the original retarded field. -/
theorem twoLegPotential_diag (q : XiZeroCopy) (br : Bool) (a : ℂ) :
    twoLegPotential q br a a = originalPotential q br a := by
  funext p r X k
  rw [twoLegPotential, originalPotential_amplitude q br a, sq]

private theorem angularLaplacian_smul (c : ℂ) (F : ℝ → ℝ → ℂ) (X k : ℝ) :
    angularLaplacian (fun x y => c * F x y) X k = c * angularLaplacian F X k := by
  simp only [angularLaplacian, deriv_const_mul_field']
  ring

/-- **Two-leg wave equation**: the two-leg field solves the original forced wave equation with
the two-leg source on the physical null wedge `0 < p ≤ r`. -/
theorem twoLegPotential_wave (q : XiZeroCopy) (br : Bool) (a d : ℂ) {p r : ℝ} (hp : 0 < p)
    (hpr : p ≤ r) (X k : ℝ) :
    4 * deriv (fun b => deriv (fun u => twoLegPotential q br a d u b X k) p) r -
      angularLaplacian (twoLegPotential q br a d p r) X k / (Real.cosh ((p - r) / 2) : ℂ) ^ 2 =
        twoLegForcing q br a d ((p + r) / 2) ((p - r) / 2) ![X, Real.exp k] := by
  have h := originalPotential_wave q br 1 hp hpr X k
  have hL : angularLaplacian (twoLegPotential q br a d p r) X k =
      a * d * angularLaplacian (originalPotential q br 1 p r) X k :=
    angularLaplacian_smul (a * d) (originalPotential q br 1 p r) X k
  simp only [twoLegPotential, deriv_const_mul_field'] at hL ⊢
  rw [hL, twoLegForcing, ← h]
  ring

/-- The two-leg field keeps the Dirichlet boundary value. -/
theorem twoLegPotential_boundary (q : XiZeroCopy) (br : Bool) (a d : ℂ) (p X k : ℝ) :
    twoLegPotential q br a d p p X k = 0 := by
  rw [twoLegPotential, originalPotential_boundary, mul_zero]

/-- The two-leg field vanishes before the fixed ingoing onset. -/
theorem twoLegPotential_before_onset (q : XiZeroCopy) (br : Bool) (a d : ℂ) {p r : ℝ}
    (hp : p ≤ 0) (X k : ℝ) : twoLegPotential q br a d p r X k = 0 := by
  rw [twoLegPotential, originalPotential_before_onset q br 1 hp, mul_zero]

end RHTower.D4BMOriginalCausalPotential
