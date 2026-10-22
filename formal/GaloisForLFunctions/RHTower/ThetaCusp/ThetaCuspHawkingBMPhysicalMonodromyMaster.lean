import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMActualAffineMetricSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonIncidence
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The physical BM master carried by the mixed Xi monodromy

The reduced Gauss solution `F` is dressed by `z^alpha`, with
`alpha = -i omega / 2`.  For both four-dimensional BM scalar and vector
sectors beta is zero.  The identities below retain derivatives of this
factor and prove the physical radial equation.  Horizon incidence is a
separate condition; solving this equation does not assert retardedness.
-/

open Complex Set
namespace RHTower.D4BMPhysicalMaster
noncomputable section

/-- Principal-branch realization of the BM horizon factor. -/
def factor (omega z : ℂ) : ℂ :=
  Complex.exp (d4BMIngoingHorizonExponent omega * Complex.log z)

/-- The literal mixed frequency of the Xi fibre. -/
abbrev frequency (n k : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMCausalPlusMinusFrequency n k (d4BMXiMixedHorizonAngularMomentum q)

/-- Physical master, including the factor removed in the Gauss equation. -/
def master (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  factor (frequency n k q) z * d4BMXiMixedHorizonExactMonodromyMode n k q z

/-- First jet with the horizon-factor derivative retained. -/
def first (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  factor (frequency n k q) z *
    (d4BMXiMixedHorizonExactMonodromyModeDerivative n k q z +
      d4BMIngoingHorizonExponent (frequency n k q) * z⁻¹ *
        d4BMXiMixedHorizonExactMonodromyMode n k q z)

/-- Second jet with both horizon-factor correction terms retained. -/
def second (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  let a := d4BMIngoingHorizonExponent (frequency n k q)
  factor (frequency n k q) z *
    (d4BMXiMixedHorizonExactMonodromyModeSecondDerivative n k q z +
      2 * a * z⁻¹ * d4BMXiMixedHorizonExactMonodromyModeDerivative n k q z +
      a * (a - 1) * z⁻¹ ^ (2 : ℕ) * d4BMXiMixedHorizonExactMonodromyMode n k q z)

/-- The physical four-dimensional BM radial differential expression, in `z`. -/
def radialJet (omega chi z v d dd : ℂ) : ℂ :=
  z * (1 - z) * dd + (1 - 3 * z / 2) * d +
    (omega ^ (2 : ℕ) / (4 * z) - (1 / 4 + chi ^ (2 : ℕ)) / 4) * v

private theorem reduced_hasDerivAt (n k : ℕ) (q : XiZeroCopy)
    (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMXiMixedHorizonExactMonodromyMode n k q)
      (d4BMXiMixedHorizonExactMonodromyModeDerivative n k q z) z :=
  (hasDerivAt_d4BMMixedHorizonRegularBranch n k _ z
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz).const_mul _

private theorem reduced_first_hasDerivAt (n k : ℕ) (q : XiZeroCopy)
    (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMXiMixedHorizonExactMonodromyModeDerivative n k q)
      (d4BMXiMixedHorizonExactMonodromyModeSecondDerivative n k q z) z :=
  (hasDerivAt_d4BMMixedHorizonRegularBranchDerivative n k _ z
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz).const_mul _

/-- The dressing factor is smooth away from the principal logarithm cut. -/
theorem factor_contDiffAt (omega z : ℂ) (hz : z ∈ Complex.slitPlane)
    (m : WithTop ℕ∞) : ContDiffAt ℂ m (factor omega) z := by
  exact Complex.contDiff_exp.contDiffAt.comp z
    (contDiffAt_const.mul (Complex.contDiffAt_log hz))

/-- Exact derivative of the nonconstant dressing factor. -/
theorem factor_hasDerivAt (omega z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (factor omega)
      (factor omega z * d4BMIngoingHorizonExponent omega * z⁻¹) z := by
  convert! ((Complex.hasDerivAt_log hz).const_mul
    (d4BMIngoingHorizonExponent omega)).cexp using 1
  simp [factor, mul_assoc]

/-- Actual first derivative of the dressed mixed mode. -/
theorem master_hasDerivAt (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) :
    HasDerivAt (master n k q) (first n k q z) z := by
  convert! (factor_hasDerivAt (frequency n k q) z hcut).mul
    (reduced_hasDerivAt n k q z hz) using 1
  dsimp [master, first]
  ring

/-- Actual derivative of the dressed first jet. -/
theorem first_hasDerivAt (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) :
    HasDerivAt (first n k q) (second n k q z) z := by
  have hi := (hasDerivAt_id z).inv (Complex.slitPlane_ne_zero hcut)
  have hp := (hi.const_mul (d4BMIngoingHorizonExponent (frequency n k q))).mul
    (reduced_hasDerivAt n k q z hz)
  have hd := (reduced_first_hasDerivAt n k q z hz).add hp
  convert! (factor_hasDerivAt (frequency n k q) z hcut).mul hd using 1
  dsimp [first, second]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The reduced Xi mode is locally smooth to every order inside its convergence disk. -/
theorem reduced_contDiffAt (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (m : WithTop ℕ∞) :
    ContDiffAt ℂ m (d4BMXiMixedHorizonExactMonodromyMode n k q) z := by
  let p := d4BMMixedHorizonRegularHypergeometricSeries n k
    (d4BMXiMixedHorizonAngularMomentum q)
  have hm : z ∈ Metric.eball 0 p.radius := by
    simp only [Metric.mem_eball, edist_zero_right]
    rw [d4BMMixedHorizonRegularHypergeometricSeries_radius_eq_one n k _
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)]
    exact hz
  have ha : ContDiffAt ℂ m p.sum z := (p.analyticOnNhd z hm).contDiffAt
  exact contDiffAt_const.mul ((contDiffAt_id.pow _).mul ha)

/-- Smoothness of the physical master needed by the full KI metric jet. -/
theorem master_contDiffAt (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) (m : WithTop ℕ∞) :
    ContDiffAt ℂ m (master n k q) z :=
  (factor_contDiffAt _ z hcut m).mul (reduced_contDiffAt n k q z hz m)

/-- Exact conjugation of the physical BM expression to its reduced Gauss expression. -/
theorem radialJet_dressing (omega chi z p v d dd : ℂ) (hz : z ≠ 0) :
    let a := d4BMIngoingHorizonExponent omega
    radialJet omega chi z (p * v) (p * (d + a * z⁻¹ * v))
      (p * (dd + 2 * a * z⁻¹ * d + a * (a - 1) * z⁻¹ ^ (2 : ℕ) * v)) =
    p * (z * (1 - z) * dd +
      (d4BMCausalRadialC omega -
        (d4BMCausalHypergeometricA omega chi +
          d4BMCausalHypergeometricB omega chi + 1) * z) * d -
      d4BMCausalHypergeometricA omega chi *
        d4BMCausalHypergeometricB omega chi * v) := by
  dsimp [radialJet, d4BMIngoingHorizonExponent, d4BMCausalRadialC,
    d4BMCausalHypergeometricA, d4BMCausalHypergeometricB,
    d4BMCausalRadialA, d4BMCausalRadialB]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The dressed Xi monodromy satisfies the physical BM radial equation. -/
theorem master_radialJet_eq_zero (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hz0 : z ≠ 0) :
    radialJet (frequency n k q) (d4BMXiMixedHorizonAngularMomentum q) z
      (master n k q z) (first n k q z) (second n k q z) = 0 := by
  unfold master first second
  rw [radialJet_dressing _ _ _ _ _ _ _ hz0]
  have h := d4BMXiMixedHorizonExactMonodromyMode_jet_eq_zero n k q z hz
  change _ * (z * (1 - z) * _ +
    (d4BMCausalRadialC _ -
      (d4BMMixedHorizonComplexA n k _ + d4BMMixedHorizonComplexB n k _ + 1) * z) *
        _ - d4BMMixedHorizonComplexA n k _ * d4BMMixedHorizonComplexB n k _ * _) = 0
  rw [h, mul_zero]

private theorem domain_open :
    IsOpen {z : ℂ | ‖z‖ₑ < 1 ∧ z ∈ Complex.slitPlane} := by
  exact (isOpen_lt continuous_enorm continuous_const).inter Complex.isOpen_slitPlane

/-- The displayed second jet equals the iterated actual complex derivative. -/
theorem master_second_deriv (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) :
    deriv (deriv (master n k q)) z = second n k q z := by
  have he : deriv (master n k q) =ᶠ[nhds z] first n k q := by
    filter_upwards [domain_open.mem_nhds ⟨hz, hcut⟩] with w hw
    exact (master_hasDerivAt n k q w hw.1 hw.2).deriv
  rw [he.deriv_eq]
  exact (first_hasDerivAt n k q z hz hcut).deriv

/-- The physical BM equation for actual derivatives, with no derivative-jet premise. -/
theorem master_radial_equation (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) :
    radialJet (frequency n k q) (d4BMXiMixedHorizonAngularMomentum q) z
      (master n k q z) (deriv (master n k q) z)
      (deriv (deriv (master n k q)) z) = 0 := by
  rw [(master_hasDerivAt n k q z hz hcut).deriv,
    master_second_deriv n k q z hz hcut]
  exact master_radialJet_eq_zero n k q z hz (Complex.slitPlane_ne_zero hcut)

/-- Every point of the static exterior gives an interior point of the physical radial chart. -/
theorem exterior_coordinate_domain (p : D4BMBackground.ExteriorPoint) :
    ‖D4BMMetricReconstruction.bmCoordinate p.val‖ₑ < 1 ∧
      D4BMMetricReconstruction.bmCoordinate p.val ∈ Complex.slitPlane := by
  have hr : 1 < p.val 1 := p.property.1
  have hi : 0 < (p.val 1)⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : (p.val 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hz0 : 0 < 1 - (p.val 1)⁻¹ ^ (2 : ℕ) := by nlinarith
  have hz1 : 1 - (p.val 1)⁻¹ ^ (2 : ℕ) < 1 := by nlinarith
  have he : D4BMMetricReconstruction.bmCoordinate p.val =
      ((1 - (p.val 1)⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp [D4BMMetricReconstruction.bmCoordinate]
  rw [he]
  exact ⟨enorm_ofReal_lt_one hz0 hz1,
    Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.ofReal_re]; exact hz0))⟩

/-- Unconditional smoothness of the literal dressed Xi master at every exterior point. -/
theorem exterior_master_contDiffAt (n k : ℕ) (q : XiZeroCopy)
    (p : D4BMBackground.ExteriorPoint) (m : WithTop ℕ∞) :
    ContDiffAt ℂ m (master n k q) (D4BMMetricReconstruction.bmCoordinate p.val) :=
  master_contDiffAt n k q _ (exterior_coordinate_domain p).1
    (exterior_coordinate_domain p).2 m

/-- Unconditional physical radial equation at each exterior point. -/
theorem exterior_master_equation (n k : ℕ) (q : XiZeroCopy)
    (p : D4BMBackground.ExteriorPoint) :
    let z := D4BMMetricReconstruction.bmCoordinate p.val
    radialJet (frequency n k q) (d4BMXiMixedHorizonAngularMomentum q) z
      (master n k q z) (deriv (master n k q) z)
      (deriv (deriv (master n k q)) z) = 0 :=
  master_radial_equation n k q _ (exterior_coordinate_domain p).1
    (exterior_coordinate_domain p).2

/-- Dressing the resonant regular reduced branch gives the outgoing horizon exponent. -/
theorem master_outgoing_factorization (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : z ≠ 0) :
    master n k q z =
      d4BMXiMixedHorizonComplexMonodromyJump n k q *
        Complex.exp (d4BMOutgoingHorizonExponent (frequency n k q) * Complex.log z) *
          d4BMMixedHorizonRegularHypergeometricFactor n k
            (d4BMXiMixedHorizonAngularMomentum q) z := by
  have he : d4BMIngoingHorizonExponent (frequency n k q) +
      ((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℂ) =
      d4BMOutgoingHorizonExponent (frequency n k q) := by
    have h := d4BMIngoingHorizonExponent_add_complementary_eq_outgoing (frequency n k q)
    rw [d4BMCausalRadialC_plusMinus_eq_negNat] at h
    convert h using 1
    push_cast
    dsimp [d4BMMixedHorizonFrobeniusOrder]
    push_cast
    ring
  have hp : z ^ (d4BMMixedHorizonFrobeniusOrder n k + 1) =
      Complex.exp (((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℂ) *
        Complex.log z) := by
    rw [Complex.exp_nat_mul, Complex.exp_log hz]
  unfold master factor d4BMXiMixedHorizonExactMonodromyMode d4BMMixedHorizonRegularBranch
  rw [hp]
  have hx : Complex.exp (d4BMIngoingHorizonExponent (frequency n k q) * Complex.log z) *
      Complex.exp (((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℂ) * Complex.log z) =
      Complex.exp (d4BMOutgoingHorizonExponent (frequency n k q) * Complex.log z) := by
    rw [← Complex.exp_add, ← add_mul, he]
  calc
    _ = d4BMXiMixedHorizonComplexMonodromyJump n k q *
        (Complex.exp (d4BMIngoingHorizonExponent (frequency n k q) * Complex.log z) *
          Complex.exp (((d4BMMixedHorizonFrobeniusOrder n k + 1 : ℕ) : ℂ) * Complex.log z)) *
        d4BMMixedHorizonRegularHypergeometricFactor n k
          (d4BMXiMixedHorizonAngularMomentum q) z := by ring
    _ = _ := by rw [hx]

/-- On the positive radial ray, the dressed mixed mode has the outgoing Fourier phase. -/
theorem master_outgoing_time_phase (n k : ℕ) (q : XiZeroCopy) (tau z : ℝ)
    (hz : 0 < z) :
    d4BMFourierTimePhase (frequency n k q) tau * master n k q (z : ℂ) =
      d4BMXiMixedHorizonComplexMonodromyJump n k q *
        Complex.exp (-Complex.I * frequency n k q *
          (d4BMOutgoingHorizonCoordinate tau z : ℂ)) *
        d4BMMixedHorizonRegularHypergeometricFactor n k
          (d4BMXiMixedHorizonAngularMomentum q) (z : ℂ) := by
  rw [master_outgoing_factorization n k q _ (by exact_mod_cast hz.ne'),
    ← Complex.ofReal_log hz.le]
  have h := d4BMFourierTimePhase_mul_outgoingHorizonLogPower (frequency n k q) tau z
  change _ * Complex.exp _ = _ at h
  linear_combination
    d4BMXiMixedHorizonComplexMonodromyJump n k q *
      d4BMMixedHorizonRegularHypergeometricFactor n k
        (d4BMXiMixedHorizonAngularMomentum q) (z : ℂ) * h

/-- The physical ODE's exact second-derivative reduction. -/
def onShellSecond (omega chi z v d : ℂ) : ℂ :=
  -((1 - 3 * z / 2) * d + (omega ^ (2 : ℕ) / (4 * z) - (1 / 4 + chi ^ (2 : ℕ)) / 4) * v) /
    (z * (1 - z))

/-- The differentiated physical ODE's exact third-derivative reduction. -/
def onShellThird (omega chi z v d : ℂ) : ℂ :=
  -((2 - 7 * z / 2) * onShellSecond omega chi z v d +
      (-3 / 2 + omega ^ (2 : ℕ) / (4 * z) - (1 / 4 + chi ^ (2 : ℕ)) / 4) * d -
      omega ^ (2 : ℕ) / (4 * z ^ (2 : ℕ)) * v) / (z * (1 - z))

private theorem domain_ne_one {z : ℂ} (hz : ‖z‖ₑ < 1) : z ≠ 1 := by
  intro he
  subst z
  simp at hz

/-- The physical equation reduces the second derivative to the value and first derivative. -/
theorem master_second_onShell (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) :
    deriv (deriv (master n k q)) z =
      onShellSecond (frequency n k q) (d4BMXiMixedHorizonAngularMomentum q) z
        (master n k q z) (deriv (master n k q) z) := by
  have h := master_radial_equation n k q z hz hcut
  have hA : z * (1 - z) ≠ 0 :=
    mul_ne_zero (Complex.slitPlane_ne_zero hcut) (sub_ne_zero.mpr (domain_ne_one hz).symm)
  apply (eq_div_iff hA).mpr
  dsimp [radialJet] at h
  linear_combination h

/-- Differentiating the actual physical equation retains its potential derivative term. -/
theorem master_differentiated_equation (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) :
    let omega := frequency n k q
    let chi := d4BMXiMixedHorizonAngularMomentum q
    z * (1 - z) * deriv (deriv (deriv (master n k q))) z +
      (2 - 7 * z / 2) * deriv (deriv (master n k q)) z +
      (-3 / 2 + omega ^ (2 : ℕ) / (4 * z) - (1 / 4 + chi ^ (2 : ℕ)) / 4) *
        deriv (master n k q) z - omega ^ (2 : ℕ) / (4 * z ^ (2 : ℕ)) * master n k q z = 0 := by
  let omega := frequency n k q
  let chi := d4BMXiMixedHorizonAngularMomentum q
  let F := master n k q
  have hs := master_contDiffAt n k q z hz hcut 3
  have h0 : HasDerivAt F (deriv F z) z := (hs.differentiableAt (by norm_num)).hasDerivAt
  have hs1 := hs.derivWithin (m := 2) (by norm_num)
  have h1 : HasDerivAt (deriv F) (deriv (deriv F) z) z :=
    (hs1.differentiableAt (by norm_num)).hasDerivAt
  have hs2 := hs1.derivWithin (m := 1) (by norm_num)
  have h2 : HasDerivAt (deriv (deriv F)) (deriv (deriv (deriv F)) z) z :=
    hs2.differentiableAt_one.hasDerivAt
  have hi := (hasDerivAt_id z).inv (Complex.slitPlane_ne_zero hcut)
  have hA := (hasDerivAt_id z).mul ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z))
  have hB := (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (3 / 2))
  have hC := (hi.const_mul (omega ^ (2 : ℕ) / 4)).sub_const ((1 / 4 + chi ^ (2 : ℕ)) / 4)
  have hd : HasDerivAt
      (fun w => radialJet omega chi w (F w) (deriv F w) (deriv (deriv F) w))
      (z * (1 - z) * deriv (deriv (deriv F)) z +
        (2 - 7 * z / 2) * deriv (deriv F) z +
        (-3 / 2 + omega ^ (2 : ℕ) / (4 * z) - (1 / 4 + chi ^ (2 : ℕ)) / 4) * deriv F z -
        omega ^ (2 : ℕ) / (4 * z ^ (2 : ℕ)) * F z) z := by
    convert! ((hA.mul h2).add (hB.mul h1)).add (hC.mul h0) using 1
    · funext w
      dsimp [radialJet]
      ring
    · dsimp
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  have he : (fun w => radialJet omega chi w (F w) (deriv F w) (deriv (deriv F) w))
      =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
    filter_upwards [domain_open.mem_nhds ⟨hz, hcut⟩] with w hw
    exact master_radial_equation n k q w hw.1 hw.2
  have hz' := (he.hasDerivAt_iff.mp hd).deriv
  simpa [omega, chi, F] using hz'.symm

/-- The full reconstruction's third master jet is fixed by the value and first derivative. -/
theorem master_third_onShell (n k : ℕ) (q : XiZeroCopy) (z : ℂ)
    (hz : ‖z‖ₑ < 1) (hcut : z ∈ Complex.slitPlane) :
    deriv (deriv (deriv (master n k q))) z =
      onShellThird (frequency n k q) (d4BMXiMixedHorizonAngularMomentum q) z
        (master n k q z) (deriv (master n k q) z) := by
  have h := master_differentiated_equation n k q z hz hcut
  dsimp only at h
  rw [master_second_onShell n k q z hz hcut] at h
  have hA : z * (1 - z) ≠ 0 :=
    mul_ne_zero (Complex.slitPlane_ne_zero hcut) (sub_ne_zero.mpr (domain_ne_one hz).symm)
  apply (eq_div_iff hA).mpr
  linear_combination h

/-- Both higher radial jets needed by full KI reconstruction are reduced on the exterior. -/
theorem exterior_master_higher_jets (n k : ℕ) (q : XiZeroCopy)
    (p : D4BMBackground.ExteriorPoint) :
    let z := D4BMMetricReconstruction.bmCoordinate p.val
    let omega := frequency n k q
    let chi := d4BMXiMixedHorizonAngularMomentum q
    deriv (deriv (master n k q)) z =
      onShellSecond omega chi z (master n k q z) (deriv (master n k q) z) ∧
    deriv (deriv (deriv (master n k q))) z =
      onShellThird omega chi z (master n k q z) (deriv (master n k q) z) :=
  ⟨master_second_onShell n k q _ (exterior_coordinate_domain p).1
      (exterior_coordinate_domain p).2,
    master_third_onShell n k q _ (exterior_coordinate_domain p).1
      (exterior_coordinate_domain p).2⟩

end
end RHTower.D4BMPhysicalMaster
