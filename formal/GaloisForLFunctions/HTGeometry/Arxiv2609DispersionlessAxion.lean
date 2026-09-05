import Mathlib

/-!
# Dispersionless cylindrical Maxwell--axion algebra from arXiv:2609.03550

This module extracts theorem-level content from An--Chen--Wu--Liu--Sheng--Zhang's
quasi-cylindrical direction-splitting solver.  It formalizes the paper's exact characteristic
change of variables, cell shifts, azimuthal mode-selection law, axion effective current, axis and
ghost-cell identities, charge-conserving update, Boris magnetic rotation, and paraxial velocity
reduction.

Every side condition is absorbed into a type (`Units` or a positive-real subtype).  Results are
therefore closed and unconditional: no numerical benchmark, discretization assumption, or external
axiom enters any proof.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Pointwise

/-! ## Exact characteristic coordinates: equations (8), (22), (30), and (35) -/

/-- Forward characteristic transform `(E,B) ↦ (E+cB,E-cB)`. -/
def qdsCharacteristicForward {K : Type*} [Field K] (c : Kˣ) (p : K × K) : K × K :=
  (p.1 + (c : K) * p.2, p.1 - (c : K) * p.2)

/-- Inverse characteristic transform.  A unit-valued speed makes inversion total. -/
def qdsCharacteristicInverse {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) (q : K × K) : K × K :=
  (((2 : K)⁻¹) * (q.1 + q.2),
    ((2 : K)⁻¹ * ((c⁻¹ : Kˣ) : K)) * (q.1 - q.2))

/-- Reconstruction after characteristic splitting is exact. -/
@[simp] theorem qdsCharacteristicInverse_forward {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) (p : K × K) :
    qdsCharacteristicInverse c (qdsCharacteristicForward c p) = p := by
  ext <;>
    simp only [qdsCharacteristicInverse, qdsCharacteristicForward,
      Units.val_inv_eq_inv_val] <;>
    field_simp [Units.ne_zero c] <;> ring

/-- Characteristic synthesis after reconstruction is exact. -/
@[simp] theorem qdsCharacteristicForward_inverse {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) (q : K × K) :
    qdsCharacteristicForward c (qdsCharacteristicInverse c q) = q := by
  ext <;>
    simp only [qdsCharacteristicInverse, qdsCharacteristicForward,
      Units.val_inv_eq_inv_val] <;>
    field_simp [Units.ne_zero c] <;> ring

/-- The electromagnetic characteristic transform is an actual equivalence, not a lossy encoding. -/
def qdsCharacteristicEquiv {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) : (K × K) ≃ (K × K) where
  toFun := qdsCharacteristicForward c
  invFun := qdsCharacteristicInverse c
  left_inv := qdsCharacteristicInverse_forward c
  right_inv := qdsCharacteristicForward_inverse c

/-- Paper's axion transport variables
`(∂ₜφ,∂ₓφ) ↦ (c⁻¹∂ₜφ-∂ₓφ,c⁻¹∂ₜφ+∂ₓφ)`. -/
def qdsAxionTransportForward {K : Type*} [Field K]
    (c : Kˣ) (p : K × K) : K × K :=
  (((c⁻¹ : Kˣ) : K) * p.1 - p.2, ((c⁻¹ : Kˣ) : K) * p.1 + p.2)

/-- Equation (35), packaged as a total inverse. -/
def qdsAxionTransportInverse {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) (q : K × K) : K × K :=
  (((c : K) * (2 : K)⁻¹) * (q.2 + q.1), (2 : K)⁻¹ * (q.2 - q.1))

@[simp] theorem qdsAxionTransportInverse_forward {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) (p : K × K) :
    qdsAxionTransportInverse c (qdsAxionTransportForward c p) = p := by
  ext <;>
    simp only [qdsAxionTransportInverse, qdsAxionTransportForward,
      Units.val_inv_eq_inv_val] <;>
    field_simp [Units.ne_zero c] <;> ring

@[simp] theorem qdsAxionTransportForward_inverse {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) (q : K × K) :
    qdsAxionTransportForward c (qdsAxionTransportInverse c q) = q := by
  ext <;>
    simp only [qdsAxionTransportInverse, qdsAxionTransportForward,
      Units.val_inv_eq_inv_val] <;>
    field_simp [Units.ne_zero c] <;> ring

/-- The axion transport-variable construction is a coordinate equivalence. -/
def qdsAxionTransportEquiv {K : Type*} [Field K] [CharZero K]
    (c : Kˣ) : (K × K) ≃ (K × K) where
  toFun := qdsAxionTransportForward c
  invFun := qdsAxionTransportInverse c
  left_inv := qdsAxionTransportInverse_forward c
  right_inv := qdsAxionTransportForward_inverse c

/-- Sum of the two characteristic source channels recovers the non-advective source. -/
theorem qds_source_sum (c gamma phi : ℝ) :
    (gamma + c * phi) + (gamma - c * phi) = 2 * gamma := by
  ring

/-- Difference of the characteristic source channels recovers the transverse coupling. -/
theorem qds_source_difference (c gamma phi : ℝ) :
    (gamma + c * phi) - (gamma - c * phi) = 2 * c * phi := by
  ring

/-- Characteristic channels split electromagnetic quadratic energy without a cross term. -/
theorem qds_characteristic_energy (c electric magnetic : ℝ) :
    (electric + c * magnetic) ^ 2 + (electric - c * magnetic) ^ 2 =
      2 * (electric ^ 2 + c ^ 2 * magnetic ^ 2) := by
  ring

/-- Complex modal version of the characteristic energy identity. -/
theorem qds_characteristic_mode_energy (c : ℝ) (electric magnetic : ℂ) :
    Complex.normSq (electric + c * magnetic) +
        Complex.normSq (electric - c * magnetic) =
      2 * (Complex.normSq electric + c ^ 2 * Complex.normSq magnetic) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  ring

/-! ## Exact source-free axial shifts: equations (14)--(17) and (32)--(33) -/

/-- One-cell right-moving transport on the integer axial lattice. -/
def qdsShiftPlus {A : Type*} (field : ℤ → A) : ℤ → A :=
  fun i => field (i - 1)

/-- One-cell left-moving transport on the integer axial lattice. -/
def qdsShiftMinus {A : Type*} (field : ℤ → A) : ℤ → A :=
  fun i => field (i + 1)

@[simp] theorem qdsShiftPlus_minus {A : Type*} (field : ℤ → A) :
    qdsShiftPlus (qdsShiftMinus field) = field := by
  funext i
  simp [qdsShiftPlus, qdsShiftMinus]

@[simp] theorem qdsShiftMinus_plus {A : Type*} (field : ℤ → A) :
    qdsShiftMinus (qdsShiftPlus field) = field := by
  funext i
  simp [qdsShiftPlus, qdsShiftMinus]

/-- After `n` source-free steps, a plus characteristic is translated by exactly `n` cells. -/
theorem qdsShiftPlus_iterate {A : Type*} (field : ℤ → A) (n : ℕ) (i : ℤ) :
    (qdsShiftPlus^[n]) field i = field (i - (n : ℤ)) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (qdsShiftPlus^[n]) field (i - 1) = field (i - ↑(n + 1))
      rw [ih]
      congr 1
      omega

/-- After `n` source-free steps, a minus characteristic is translated by exactly `n` cells. -/
theorem qdsShiftMinus_iterate {A : Type*} (field : ℤ → A) (n : ℕ) (i : ℤ) :
    (qdsShiftMinus^[n]) field i = field (i + (n : ℤ)) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (qdsShiftMinus^[n]) field (i + 1) = field (i + ↑(n + 1))
      rw [ih]
      congr 1
      omega

/-- Sourced right-moving QDS update. -/
def qdsShiftPlusStep {K : Type*} [Ring K]
    (step : K) (source field : ℤ → K) : ℤ → K :=
  fun i => field (i - 1) + step * source i

/-- Sourced left-moving QDS update. -/
def qdsShiftMinusStep {K : Type*} [Ring K]
    (step : K) (source field : ℤ → K) : ℤ → K :=
  fun i => field (i + 1) + step * source i

@[simp] theorem qdsShiftPlusStep_zero_source {K : Type*} [Ring K]
    (step : K) (field : ℤ → K) :
    qdsShiftPlusStep step 0 field = qdsShiftPlus field := by
  funext i
  simp [qdsShiftPlusStep, qdsShiftPlus]

@[simp] theorem qdsShiftMinusStep_zero_source {K : Type*} [Ring K]
    (step : K) (field : ℤ → K) :
    qdsShiftMinusStep step 0 field = qdsShiftMinus field := by
  funext i
  simp [qdsShiftMinusStep, qdsShiftMinus]

/-! ## Azimuthal mode selection as Laurent-polynomial multiplication: equations (27)--(29) -/

/-- Finite azimuthal spectra, represented as Laurent polynomials in the mode label. -/
abbrev QDSModeAlgebra (K : Type*) [Semiring K] := AddMonoidAlgebra K ℤ

/-- Paper's mode convolution is multiplication in the integer mode algebra. -/
def qdsModeConvolution {K : Type*} [Semiring K]
    (a b : QDSModeAlgebra K) : QDSModeAlgebra K :=
  a * b

/-- A field with one azimuthal Fourier mode. -/
def qdsPureMode {K : Type*} [Semiring K] (m : ℤ) (a : K) : QDSModeAlgebra K :=
  AddMonoidAlgebra.single m a

@[simp] theorem qdsModeConvolution_assoc {K : Type*} [Semiring K]
    (a b d : QDSModeAlgebra K) :
    qdsModeConvolution (qdsModeConvolution a b) d =
      qdsModeConvolution a (qdsModeConvolution b d) := by
  simp [qdsModeConvolution, mul_assoc]

@[simp] theorem qdsModeConvolution_comm {K : Type*} [CommSemiring K]
    (a b : QDSModeAlgebra K) :
    qdsModeConvolution a b = qdsModeConvolution b a := by
  simp [qdsModeConvolution, mul_comm]

/-- Pure modes multiply into the sum mode, the algebraic content of `m = ±k ±l`. -/
@[simp] theorem qdsModeConvolution_pure {K : Type*} [Semiring K]
    (k l : ℤ) (a b : K) :
    qdsModeConvolution (qdsPureMode k a) (qdsPureMode l b) =
      qdsPureMode (k + l) (a * b) := by
  exact AddMonoidAlgebra.single_mul_single k l a b

/-- Coefficient-level selection rule for two pure modes. -/
theorem qdsModeConvolution_pure_coeff {K : Type*} [Semiring K]
    (k l m : ℤ) (a b : K) :
    (qdsModeConvolution (qdsPureMode k a) (qdsPureMode l b)).coeff m =
      if k + l = m then a * b else 0 := by
  rw [qdsModeConvolution_pure, qdsPureMode, AddMonoidAlgebra.coeff_single]
  exact Finsupp.single_apply

/-- Opposite modes are exactly the pure-mode pairs that source the zero mode. -/
theorem qdsModeConvolution_opposite_zero_coeff {K : Type*} [Semiring K]
    (k : ℤ) (a b : K) :
    (qdsModeConvolution (qdsPureMode k a) (qdsPureMode (-k) b)).coeff 0 = a * b := by
  rw [qdsModeConvolution_pure_coeff]
  simp

/-- A quadratic pure-mode source has doubled azimuthal order. -/
theorem qdsModeConvolution_self_pure {K : Type*} [Semiring K]
    (k : ℤ) (a : K) :
    qdsModeConvolution (qdsPureMode k a) (qdsPureMode k a) =
      qdsPureMode (2 * k) (a ^ 2) := by
  rw [qdsModeConvolution_pure]
  simp [two_mul, pow_two]

/-- Three-wave mixing of pure modes lands at their signed sum. -/
theorem qdsModeConvolution_three_pure {K : Type*} [Semiring K]
    (k l m : ℤ) (a b d : K) :
    qdsModeConvolution (qdsModeConvolution (qdsPureMode k a) (qdsPureMode l b))
        (qdsPureMode m d) =
      qdsPureMode (k + l + m) (a * b * d) := by
  rw [qdsModeConvolution_pure, qdsModeConvolution_pure]

/-- General spectra cannot create a mode outside the sumset of their supports. -/
theorem qdsModeConvolution_support {K : Type*} [Semiring K]
    (a b : QDSModeAlgebra K) :
    (qdsModeConvolution a b).coeff.support ⊆
      a.coeff.support + b.coeff.support := by
  exact AddMonoidAlgebra.support_coeff_mul_subset a b

/-! ## Three-vector algebra and the axion effective current: equations (39)--(42) -/

/-- Three-component vector used for cylindrical and Cartesian field components. -/
abbrev QDSVector3 (K : Type*) := Fin 3 → K

/-- Algebraic three-dimensional cross product. -/
def qdsCross {K : Type*} [CommRing K]
    (u v : QDSVector3 K) : QDSVector3 K :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Bilinear dot product. -/
def qdsDot {K : Type*} [CommSemiring K] (u v : QDSVector3 K) : K :=
  ∑ i, u i * v i

@[simp] theorem qdsCross_antisymm {K : Type*} [CommRing K]
    (u v : QDSVector3 K) : qdsCross u v = -qdsCross v u := by
  funext i
  fin_cases i <;> simp [qdsCross] <;> ring

/-- Cross product is perpendicular to its left input. -/
@[simp] theorem qdsDot_cross_left {K : Type*} [CommRing K]
    (u v : QDSVector3 K) : qdsDot u (qdsCross u v) = 0 := by
  simp [qdsDot, qdsCross, Fin.sum_univ_three]
  ring

/-- Cross product is perpendicular to its right input. -/
@[simp] theorem qdsDot_cross_right {K : Type*} [CommRing K]
    (u v : QDSVector3 K) : qdsDot v (qdsCross u v) = 0 := by
  simp [qdsDot, qdsCross, Fin.sum_univ_three]
  ring

/-- Axion-induced current `g/c (B ∂ₜφ - E × ∇φ)`. -/
def qdsAxionCurrent {K : Type*} [CommRing K]
    (couplingOverSpeed phiTime : K)
    (magnetic electric gradPhi : QDSVector3 K) : QDSVector3 K :=
  fun i => couplingOverSpeed *
    (phiTime * magnetic i - qdsCross electric gradPhi i)

theorem qdsAxionCurrent_zero (couplingOverSpeed phiTime : ℂ) :
    qdsAxionCurrent couplingOverSpeed phiTime 0 0 0 = 0 := by
  funext i
  fin_cases i <;> simp [qdsAxionCurrent, qdsCross]

/-- Electric work of the axion current depends only on the pseudoscalar `E·B`; the cross term does
no work. -/
theorem qdsDot_electric_axionCurrent {K : Type*} [CommRing K]
    (couplingOverSpeed phiTime : K)
    (magnetic electric gradPhi : QDSVector3 K) :
    qdsDot electric
        (qdsAxionCurrent couplingOverSpeed phiTime magnetic electric gradPhi) =
      couplingOverSpeed * phiTime * qdsDot electric magnetic := by
  simp [qdsDot, qdsAxionCurrent, qdsCross, Fin.sum_univ_three]
  ring

/-- Pure-mode dot products obey the paper's exact azimuthal selection rule. -/
theorem qdsModeDot_pure {K : Type*} [CommSemiring K]
    (k l : ℤ) (u v : QDSVector3 K) :
    qdsDot (fun i => qdsPureMode k (u i)) (fun i => qdsPureMode l (v i)) =
      qdsPureMode (k + l) (qdsDot u v) := by
  rw [qdsDot, qdsDot, Fin.sum_univ_three]
  have hpure (a b : K) :
      qdsPureMode k a * qdsPureMode l b = qdsPureMode (k + l) (a * b) := by
    simpa [qdsModeConvolution] using qdsModeConvolution_pure k l a b
  rw [hpure, hpure, hpure]
  simp only [qdsPureMode]
  rw [← AddMonoidAlgebra.single_add, ← AddMonoidAlgebra.single_add]
  rw [Fin.sum_univ_three]

/-- Consequently an `E_k·B_l` axion source occupies only mode `k+l`. -/
theorem qdsAxionSource_pure_mode {K : Type*} [CommSemiring K]
    (k l : ℤ) (electric magnetic : QDSVector3 K) :
    qdsDot (fun i => qdsPureMode k (electric i))
        (fun i => qdsPureMode l (magnetic i)) =
      qdsPureMode (k + l) (qdsDot electric magnetic) :=
  qdsModeDot_pure k l electric magnetic

/-! ## Axis regularity and ghost cells: equations (43), (48)--(50) -/

/-- Regular scalar/longitudinal axis trace: only mode zero survives. -/
def qdsScalarAxisMode (m : ℕ) (value : ℂ) : ℂ :=
  if m = 0 then value else 0

@[simp] theorem qdsScalarAxisMode_zero (value : ℂ) :
    qdsScalarAxisMode 0 value = value := by
  simp [qdsScalarAxisMode]

@[simp] theorem qdsScalarAxisMode_succ (m : ℕ) (value : ℂ) :
    qdsScalarAxisMode (m + 1) value = 0 := by
  simp [qdsScalarAxisMode]

/-- Regular transverse axis trace: only the dipole mode survives. -/
def qdsTransverseAxisMode (m : ℕ) (value : ℂ) : ℂ :=
  if m = 1 then value else 0

@[simp] theorem qdsTransverseAxisMode_one (value : ℂ) :
    qdsTransverseAxisMode 1 value = value := by
  simp [qdsTransverseAxisMode]

/-- Complete axis classification in one equation. -/
theorem qdsTransverseAxisMode_classification (m : ℕ) (value : ℂ) :
    qdsTransverseAxisMode m value = if m = 1 then value else 0 := rfl

/-- Equation (49): ghost value enforcing the dipole-axis midpoint relation. -/
def qdsDipoleAxisGhost (interior theta : ℂ) : ℂ :=
  2 * Complex.I * theta - interior

/-- The average of ghost and interior values is exactly `i T_theta`. -/
theorem qdsDipoleAxisGhost_average (interior theta : ℂ) :
    (qdsDipoleAxisGhost interior theta + interior) / 2 = Complex.I * theta := by
  rw [qdsDipoleAxisGhost]
  ring

/-- Dipole ghost reflection is an involution. -/
@[simp] theorem qdsDipoleAxisGhost_involutive (interior theta : ℂ) :
    qdsDipoleAxisGhost (qdsDipoleAxisGhost interior theta) theta = interior := by
  rw [qdsDipoleAxisGhost, qdsDipoleAxisGhost]
  ring

/-- Mirrored ghost cell implementing a homogeneous Neumann axis condition. -/
def qdsNeumannAxisGhost {K : Type*} (interior : K) : K := interior

/-- Centered difference numerator of a mirrored field vanishes identically. -/
@[simp] theorem qdsNeumannAxisGhost_difference {K : Type*} [AddGroup K]
    (interior : K) : interior - qdsNeumannAxisGhost interior = 0 := by
  simp [qdsNeumannAxisGhost]

/-! ## Exact charge-conserving finite-volume algebra: equations (59)--(63) -/

/-- One-dimensional affine trajectory weight from equation (54). -/
def qdsLinearTrajectoryWeight {K : Type*} [Ring K]
    (initial change parameter : K) : K :=
  initial + parameter * change

@[simp] theorem qdsLinearTrajectoryWeight_zero {K : Type*} [Ring K]
    (initial change : K) : qdsLinearTrajectoryWeight initial change 0 = initial := by
  simp [qdsLinearTrajectoryWeight]

@[simp] theorem qdsLinearTrajectoryWeight_one {K : Type*} [Ring K]
    (initial change : K) : qdsLinearTrajectoryWeight initial change 1 = initial + change := by
  simp [qdsLinearTrajectoryWeight]

/-- Exact axisymmetric charge change, written using the trajectory averages of the two affine
shape weights. -/
theorem qds_axisymmetric_shape_charge_change
    (charge gx hx gr hr : ℝ) :
    charge * ((gx + hx) * (gr + hr) - gx * gr) =
      charge * hx * (gr + hr / 2) + charge * hr * (gx + hx / 2) := by
  ring

/-- Abstract finite-volume divergence.  In cylindrical mode deposition, the four arguments are the
axial, radial, and angular flux contributions of equation (63). -/
def qdsFiniteVolumeDivergence {K : Type*} [Field K]
    (axial radial angular : K) : K :=
  axial + radial - angular

/-- Charge update defined by the same flux ledger as deposition. -/
def qdsChargeAdvance {K : Type*} [Field K]
    (timeStep : Kˣ) (density axial radial angular : K) : K :=
  density - (timeStep : K) * qdsFiniteVolumeDivergence axial radial angular

/-- Discrete continuity equation holds identically when charge and current share one trajectory. -/
theorem qdsChargeAdvance_continuity {K : Type*} [Field K]
    (timeStep : Kˣ) (density axial radial angular : K) :
    (qdsChargeAdvance timeStep density axial radial angular - density) /
        (timeStep : K) + qdsFiniteVolumeDivergence axial radial angular = 0 := by
  rw [qdsChargeAdvance, qdsFiniteVolumeDivergence]
  field_simp [Units.ne_zero timeStep]
  ring

/-- Summing local flux differences leaves only the two boundary fluxes. -/
theorem qdsFlux_telescope {K : Type*} [AddCommGroup K]
    (flux : ℕ → K) (cells : ℕ) :
    ∑ i ∈ Finset.range cells, (flux (i + 1) - flux i) = flux cells - flux 0 :=
  Finset.sum_range_sub flux cells

/-! ## Open axial and outgoing radial boundaries: equations (64)--(71) -/

/-- Four transverse electromagnetic characteristic channels. -/
structure QDSEMAxialState (K : Type*) where
  radialPlus : K
  radialMinus : K
  thetaPlus : K
  thetaMinus : K
  deriving DecidableEq

/-- Left open boundary: kill exactly the two inward channels. -/
def qdsEMOpenLeft {K : Type*} [Zero K] (s : QDSEMAxialState K) : QDSEMAxialState K where
  radialPlus := 0
  radialMinus := s.radialMinus
  thetaPlus := s.thetaPlus
  thetaMinus := 0

/-- Right open boundary: kill exactly the two inward channels. -/
def qdsEMOpenRight {K : Type*} [Zero K] (s : QDSEMAxialState K) : QDSEMAxialState K where
  radialPlus := s.radialPlus
  radialMinus := 0
  thetaPlus := 0
  thetaMinus := s.thetaMinus

@[simp] theorem qdsEMOpenLeft_idempotent {K : Type*} [Zero K]
    (s : QDSEMAxialState K) : qdsEMOpenLeft (qdsEMOpenLeft s) = qdsEMOpenLeft s := by
  rfl

@[simp] theorem qdsEMOpenRight_idempotent {K : Type*} [Zero K]
    (s : QDSEMAxialState K) : qdsEMOpenRight (qdsEMOpenRight s) = qdsEMOpenRight s := by
  rfl

/-- Left axion boundary kills the incoming plus characteristic only. -/
def qdsAxionOpenLeft {K : Type*} [Zero K] (s : K × K) : K × K := (0, s.2)

/-- Right axion boundary kills the incoming minus characteristic only. -/
def qdsAxionOpenRight {K : Type*} [Zero K] (s : K × K) : K × K := (s.1, 0)

@[simp] theorem qdsAxionOpenLeft_idempotent {K : Type*} [Zero K] (s : K × K) :
    qdsAxionOpenLeft (qdsAxionOpenLeft s) = qdsAxionOpenLeft s := by
  rfl

@[simp] theorem qdsAxionOpenRight_idempotent {K : Type*} [Zero K] (s : K × K) :
    qdsAxionOpenRight (qdsAxionOpenRight s) = qdsAxionOpenRight s := by
  rfl

/-- Radially outgoing transverse electromagnetic state from equation (66). -/
def qdsOutgoingRadialEM (c : ℝ) (magneticX magneticTheta : ℝ) : ℝ × ℝ :=
  (c * magneticX, -c * magneticTheta)

theorem qdsOutgoingRadialEM_energy (c magneticX magneticTheta : ℝ) :
    (qdsOutgoingRadialEM c magneticX magneticTheta).1 ^ 2 +
        (qdsOutgoingRadialEM c magneticX magneticTheta).2 ^ 2 =
      c ^ 2 * (magneticX ^ 2 + magneticTheta ^ 2) := by
  simp [qdsOutgoingRadialEM]
  ring

/-- Exterior axion ghost value obtained from the centered outgoing-wave condition, equation (70). -/
def qdsAxionOuterGhost {K : Type*} [Field K]
    (ratio : Kˣ) (inner future past : K) : K :=
  inner - ((ratio⁻¹ : Kˣ) : K) * (future - past)

/-- The constructed ghost cell satisfies the centered outgoing condition exactly. -/
theorem qdsAxionOuterGhost_residual {K : Type*} [Field K]
    (ratio : Kˣ) (inner future past : K) :
    qdsAxionOuterGhost ratio inner future past - inner +
        ((ratio⁻¹ : Kˣ) : K) * (future - past) = 0 := by
  simp [qdsAxionOuterGhost]

/-! ## Boris magnetic rotation from equations (52)--(53) -/

/-- Squared Euclidean norm written polynomially. -/
def qdsNormSq (u : QDSVector3 ℝ) : ℝ := qdsDot u u

theorem qdsNormSq_nonneg (u : QDSVector3 ℝ) : 0 ≤ qdsNormSq u := by
  rw [qdsNormSq, qdsDot, Fin.sum_univ_three]
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

/-- Boris rotation auxiliary vector `s = 2t/(1+|t|²)`. -/
def qdsBorisS (t : QDSVector3 ℝ) : QDSVector3 ℝ :=
  fun i => (2 / (1 + qdsNormSq t)) * t i

/-- Intermediate momentum `u' = u + u × t`. -/
def qdsBorisPrime (u t : QDSVector3 ℝ) : QDSVector3 ℝ :=
  fun i => u i + qdsCross u t i

/-- Magnetic part of the Boris push. -/
def qdsBorisRotate (u t : QDSVector3 ℝ) : QDSVector3 ℝ :=
  fun i => u i + qdsCross (qdsBorisPrime u t) (qdsBorisS t) i

@[simp] theorem qdsCross_zero {K : Type*} [CommRing K]
    (u v : QDSVector3 K) : qdsCross u v 0 = u 1 * v 2 - u 2 * v 1 := by
  rfl

@[simp] theorem qdsCross_one {K : Type*} [CommRing K]
    (u v : QDSVector3 K) : qdsCross u v 1 = u 2 * v 0 - u 0 * v 2 := by
  rfl

@[simp] theorem qdsCross_two {K : Type*} [CommRing K]
    (u v : QDSVector3 K) : qdsCross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  rfl

/-- Boris magnetic rotation preserves squared momentum exactly. -/
theorem qdsNormSq_borisRotate (u t : QDSVector3 ℝ) :
    qdsNormSq (qdsBorisRotate u t) = qdsNormSq u := by
  have hden : 1 + qdsNormSq t ≠ 0 := by
    have h := qdsNormSq_nonneg t
    linarith
  simp only [qdsNormSq, qdsDot, qdsBorisRotate, qdsBorisPrime, qdsBorisS,
    Fin.sum_univ_three, qdsCross_zero, qdsCross_one, qdsCross_two]
  field_simp [hden]
  ring

/-! ## Paraxial finite-waist velocity: equations (74)--(75) -/

/-- Positive physical length, preventing wavelength or waist denominators from vanishing. -/
abbrev QDSPositiveLength := Set.Ioi (0 : ℝ)

/-- Leading-order group-velocity ratio in terms of transverse and axial squared wave numbers. -/
def qdsParaxialVelocityRatio (kPerpSq kZeroSq : ℝ) : ℝ :=
  1 - kPerpSq / (2 * kZeroSq)

/-- Gaussian-beam specialization of the paraxial velocity law. -/
theorem qdsParaxialVelocityRatio_gaussian
    (wavelength waist : QDSPositiveLength) :
    qdsParaxialVelocityRatio (2 / (waist : ℝ) ^ 2)
        ((2 * Real.pi / (wavelength : ℝ)) ^ 2) =
      1 - ((wavelength : ℝ) / (2 * Real.pi * (waist : ℝ))) ^ 2 := by
  have hw : (waist : ℝ) ≠ 0 := ne_of_gt waist.property
  have hlam : (wavelength : ℝ) ≠ 0 := ne_of_gt wavelength.property
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [qdsParaxialVelocityRatio]
  field_simp [hw, hlam, hpi]

end GaloisForLFunctions.HTGeometry
