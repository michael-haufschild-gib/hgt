import GaloisForLFunctions.HTGeometry.CayleyFockOrderSpaceConservation
import GaloisForLFunctions.RHTower.XiCayleyWardDynamicalVisibility

/-!
# Xi Cayley--Fock order-space conservation

Every strict-right upper zero of the completed Riemann xi function determines two intrinsic
Cayley--Fock coordinates:

* a positive order drift `d = |ρ - 1|⁻²`;
* a positive transverse exponent `κ = (2 Re ρ - 1)d`.

After weighting the corresponding coherent mode by its endpoint Ward source weight, every
factorially normalized jet channel is exactly a Poisson packet of mean `d x` and total exponential
mass `exp (κ x)`.  Passing to the adjacent-order exterior determinant removes the conjugate phase
without losing the packet: every channel is strictly negative and the complete order sum is the
same signed exponential instability.

Thus height, transverse displacement, source multiplicity, order drift, and instability are not
separate observables.  They are exact coordinates of one conserved order-space packet.
-/

open Complex Real
open scoped BigOperators
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Shift from the Li Cayley node to its coherent-exponential coordinate. -/
def xiCayleyFockShift (q : XiRightUpperZeroCopy) : ℂ :=
  (xiWardLiCayleyNode q)⁻¹ - 1

private theorem xiCayleyFock_rho_ne_zero (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ) ≠ 0 := by
  intro h
  exact xi_divisor_support_im_ne_zero q.1.1.1 (by simp [h])

private theorem xiCayleyFock_rho_ne_one (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ) ≠ 1 := by
  intro h
  exact xi_divisor_support_im_ne_zero q.1.1.1 (by simp [h])

/-- The coherent shift is exactly the inverse displacement from the reflection point `1`. -/
theorem xiCayleyFockShift_eq (q : XiRightUpperZeroCopy) :
    xiCayleyFockShift q = ((q.1.1.1 : ℂ) - 1)⁻¹ := by
  rw [xiCayleyFockShift, xiWardLiCayleyNode, wCoordinate]
  field_simp [xiCayleyFock_rho_ne_zero q, xiCayleyFock_rho_ne_one q]
  have hsub : (q.1.1.1 : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (xiCayleyFock_rho_ne_one q)
  field_simp [hsub]
  ring

/-- Order drift of one strict-right xi divisor copy. -/
def xiCayleyFockDrift (q : XiRightUpperZeroCopy) : ℝ :=
  HTGeometry.cayleyFockDrift (xiCayleyFockShift q)

/-- Transverse exponential instability of one strict-right xi divisor copy. -/
def xiCayleyFockExponent (q : XiRightUpperZeroCopy) : ℝ :=
  HTGeometry.cayleyFockExponent (xiCayleyFockShift q)

theorem xiCayleyFockDrift_eq (q : XiRightUpperZeroCopy) :
    xiCayleyFockDrift q =
      (Complex.normSq ((q.1.1.1 : ℂ) - 1))⁻¹ := by
  rw [xiCayleyFockDrift, xiCayleyFockShift_eq,
    HTGeometry.cayleyFockDrift_of_rho (xiCayleyFock_rho_ne_one q)]

theorem xiCayleyFockExponent_eq (q : XiRightUpperZeroCopy) :
    xiCayleyFockExponent q =
      (2 * (q.1.1.1 : ℂ).re - 1) * xiCayleyFockDrift q := by
  rw [xiCayleyFockExponent, xiCayleyFockDrift, xiCayleyFockShift_eq,
    HTGeometry.cayleyFockExponent_of_rho (xiCayleyFock_rho_ne_one q)]

theorem xiCayleyFockDrift_pos (q : XiRightUpperZeroCopy) :
    0 < xiCayleyFockDrift q := by
  rw [xiCayleyFockDrift, HTGeometry.cayleyFockDrift]
  rw [xiCayleyFockShift_eq]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr (inv_ne_zero
      (sub_ne_zero.mpr (xiCayleyFock_rho_ne_one q))))

/-- Strict-right displacement is exactly positive Cayley--Fock instability. -/
theorem xiCayleyFockExponent_pos (q : XiRightUpperZeroCopy) :
    0 < xiCayleyFockExponent q := by
  rw [xiCayleyFockExponent_eq]
  apply mul_pos
  · have h := xiRightCenteredZero_re_pos q.1
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at h
    simp only [Complex.sub_re] at h
    norm_num at h
    linarith
  · exact xiCayleyFockDrift_pos q

/-- Endpoint-Ward-weighted coherent jet of one strict-right xi divisor copy. -/
def xiCayleyWardCoherentJet
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) : ℂ :=
  HTGeometry.coherentExponentialJet
    (Real.sqrt (xiEndpointWardPairWeight q) : ℂ)
    (xiCayleyFockShift q) x r

/-- Exact source-weighted Poisson packet in derivative-order space. -/
theorem xiCayleyWardCoherentJet_poisson_conservation
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * ‖xiCayleyWardCoherentJet q x r‖ ^ (2 : ℕ) =
      xiEndpointWardPairWeight q *
        Real.exp (xiCayleyFockExponent q * x) *
          HTGeometry.poissonOrderWeight (xiCayleyFockDrift q * x) r := by
  rw [xiCayleyWardCoherentJet, xiCayleyFockExponent, xiCayleyFockDrift,
    HTGeometry.coherentExponentialJet_poisson_conservation]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]

/-- Adjacent-order exterior packet of the source-weighted conjugate mode pair. -/
def xiCayleyWardExteriorPacket
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) : ℂ :=
  HTGeometry.twoModeCoherentExterior
    (Real.sqrt (xiEndpointWardPairWeight q) : ℂ)
    (Real.sqrt (xiEndpointWardPairWeight q) : ℂ)
    (xiCayleyFockShift q)
    ((starRingEnd ℂ) (xiCayleyFockShift q)) x r

/-- Removing phase by the adjacent-order exterior determinant preserves the complete Poisson
packet and fixes its sign. -/
theorem neg_re_xiCayleyWardExteriorPacket_poisson_conservation
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    x ^ r / r.factorial * (-(xiCayleyWardExteriorPacket q x r).re) =
      4 * xiEndpointWardPairWeight q * (xiCayleyFockShift q).im ^ (2 : ℕ) *
        Real.exp (xiCayleyFockExponent q * x) *
          HTGeometry.poissonOrderWeight (xiCayleyFockDrift q * x) r := by
  rw [xiCayleyWardExteriorPacket, xiCayleyFockExponent, xiCayleyFockDrift,
    HTGeometry.neg_re_twoModeCoherentExterior_conj_poisson_conservation]
  rw [Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]

/-- Complete exterior order summation returns the exact signed exponential instability. -/
theorem tsum_xiCayleyWardExteriorPacket
    (q : XiRightUpperZeroCopy) (x : ℝ) :
    ∑' r : ℕ, ((x : ℂ) ^ r / r.factorial) *
        xiCayleyWardExteriorPacket q x r =
      ((xiEndpointWardPairWeight q : ℝ) : ℂ) *
        (xiCayleyFockShift q -
          (starRingEnd ℂ) (xiCayleyFockShift q)) ^ (2 : ℕ) *
        Complex.exp ((xiCayleyFockExponent q * x : ℝ) : ℂ) := by
  simp_rw [xiCayleyWardExteriorPacket]
  rw [xiCayleyFockExponent,
    HTGeometry.tsum_twoModeCoherentExterior_conj]
  rw [Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]

/-- Every individual exterior channel has strict negative orientation. -/
theorem xiCayleyWardExteriorPacket_re_neg
    (q : XiRightUpperZeroCopy) (x : ℝ) (r : ℕ) :
    (xiCayleyWardExteriorPacket q x r).re < 0 := by
  rw [xiCayleyWardExteriorPacket,
    HTGeometry.twoModeCoherentExterior_conj_eq]
  rw [show (xiCayleyFockShift q -
      (starRingEnd ℂ) (xiCayleyFockShift q)) ^ (2 : ℕ) =
      (((-4 * (xiCayleyFockShift q).im ^ (2 : ℕ) : ℝ) : ℂ)) by
    rw [Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  simp only [mul_zero, sub_zero]
  have him : (xiCayleyFockShift q).im ≠ 0 := by
    rw [xiCayleyFockShift_eq, Complex.inv_im]
    apply div_ne_zero
    · simp only [Complex.sub_im, Complex.one_im, sub_zero]
      exact neg_ne_zero.mpr (xi_divisor_support_im_ne_zero q.1.1.1)
    · exact ne_of_gt
        (Complex.normSq_pos.mpr
          (sub_ne_zero.mpr (xiCayleyFock_rho_ne_one q)))
  have hweight : 0 < Real.sqrt (xiEndpointWardPairWeight q) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt (xiEndpointWardPairWeight_pos q).le]
    exact xiEndpointWardPairWeight_pos q
  have hnorm : 0 < ‖xiCayleyFockShift q‖ ^ (2 * r) := by
    have hne : xiCayleyFockShift q ≠ 0 := by
      rw [xiCayleyFockShift_eq]
      exact inv_ne_zero
        (sub_ne_zero.mpr (xiCayleyFock_rho_ne_one q))
    positivity
  have hexp : 0 < Real.exp (2 * (xiCayleyFockShift q).re * x) :=
    Real.exp_pos _
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hweight (by
      nlinarith [sq_pos_of_ne_zero him]))
    (mul_pos hnorm hexp)

end

end RHTower
