import GaloisForLFunctions.RHTower.GammaSewnXiShiftTangentInnovation
import GaloisForLFunctions.RHTower.XiPhysicalEndpointLocalStiffness

/-!
# The Xi-shift endpoint tangent Hilbert kernel

The height synthesis of the completed `+2` Xi-shift source has an exact father/tangent split at
each prime.  This file constructs the missing cross-prime object: the square-root-density lift of
the centered height coordinate on the common valuation-depth axis.

Writing `a = p⁻¹`, its `e`-th coordinate is

`sqrt(1-a²) * a^(e+1) * ((1-a²)e-a²)`.

Its squared norm is the already proved `p⁻⁴`, but unlike that diagonal statement the common-depth
lift retains cross-prime correlation.  The full generating function and Gram kernel are

`a² sqrt(1-a²) (z-a)/(1-az)²`,

and

`a² b² sqrt((1-a²)(1-b²))
  * ((1+ab)²-2(a²+b²))/(1-ab)³`.

Thus the source-derived tangent is a rooted double-pole Hardy coordinate: its root is the inverse
prime and its pole is the prime itself.  After the forced `p²` normalization every prime vector
has norm one, and the resulting cross-prime kernel is contractive because its defect is literally
the squared Hilbert distance between the normalized all-depth source vectors.

No Xi zero, target response, RH-equivalent positivity assumption, selected valuation depth, or
ambient resolution lift is used.
-/

open Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem hasSum_nat_sq_mul_geometric
    {r : ℝ} (hr : ‖r‖ < 1) :
    HasSum (fun e : ℕ => (e : ℝ) ^ 2 * r ^ e)
      (r * (1 + r) / (1 - r) ^ 3) := by
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr
  have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr
  have hgeom := hasSum_geometric_of_norm_lt_one (K := ℝ) hr
  have hraw := ((hchoose.mul_left 2).sub (hlinear.mul_left 3)).sub
    (hgeom.mul_left 2)
  have hraw' : HasSum (fun e : ℕ => (e : ℝ) ^ 2 * r ^ e)
      (2 * (1 / (1 - r) ^ (2 + 1)) -
        3 * (r / (1 - r) ^ 2) - 2 * (1 - r)⁻¹) := by
    apply HasSum.congr_fun hraw
    intro e
    have hchooseTwo :
        (2 : ℝ) * ((((e + 2).choose 2 : ℕ) : ℝ)) - 3 * (e : ℝ) - 2 =
          (e : ℝ) ^ 2 := by
      have hd : 2 ∣ (e + 2) * (e + 1) := by
        simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
          (Nat.even_mul_succ_self (e + 1)).two_dvd
      have hn : 2 * (e + 2).choose 2 = (e + 2) * (e + 1) := by
        rw [Nat.choose_two_right]
        have hsub : e + 2 - 1 = e + 1 := by omega
        rw [hsub, Nat.mul_div_cancel' hd]
      have hncast : (2 : ℝ) * ((((e + 2).choose 2 : ℕ) : ℝ)) =
          (((e + 2) * (e + 1) : ℕ) : ℝ) := by
        exact_mod_cast hn
      rw [hncast]
      push_cast
      ring
    rw [← hchooseTwo]
    ring
  have hne : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linarith
    subst r
    norm_num at hr
  have hvalue :
      2 * (1 / (1 - r) ^ (2 + 1)) -
          3 * (r / (1 - r) ^ 2) - 2 * (1 - r)⁻¹ =
        r * (1 + r) / (1 - r) ^ 3 := by
    field_simp [hne]
    ring_nf
  rw [← hvalue]
  exact hraw'

/-- The actual centered height coordinate embedded by the square root of the Xi-shift depth law.
The inverse-prime parameter is source-forced by the completed `+2` shift. -/
def gammaSewnXiShiftEndpointTangentFeature
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  let a := ((p : ℝ)⁻¹)
  Real.sqrt (1 - a ^ 2) * a ^ (e + 1) *
    ((1 - a ^ 2) * (e : ℝ) - a ^ 2)

/-- The explicit feature is exactly the square-root-density lift of the centered physical-height
coordinate.  This identifies the new cross-prime carrier with the actual Xi-shift law. -/
theorem gammaSewnXiShiftEndpointTangentFeature_sq_eq
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnXiShiftEndpointTangentFeature p e ^ 2 =
      gammaSewnXiShiftJointDepthProbability 1 p e *
        (gammaSewnXiShiftEndpointHeightLift p e - (p : ℝ)⁻¹) ^ 2 := by
  let a := ((p : ℝ)⁻¹)
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have ha1 : a < 1 := by
    dsimp only [a]
    exact (inv_lt_one₀ (by positivity)).mpr hp
  have haSq : 0 ≤ 1 - a ^ 2 := by nlinarith [sq_lt_sq₀ ha0.le (by norm_num) |>.2 ha1]
  have hsqrt : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 :=
    Real.sq_sqrt haSq
  have haPow : (a ^ (e + 1)) ^ 2 = (a ^ 2) ^ e * a ^ 2 := by
    rw [pow_succ a e, mul_pow, ← mul_pow]
    ring
  rw [gammaSewnXiShiftJointDepthProbability,
    gammaSewnSynchronizedEulerDepthProbability,
    show (2 : ℝ) * 1 = 2 by norm_num,
    xiMobiusContinuousApertureDiskNode_two_eq_inv_sq]
  unfold gammaSewnXiShiftEndpointTangentFeature
    gammaSewnXiShiftEndpointHeightLift
  rw [xiMobiusContinuousApertureDiskNode_two_eq_inv_sq]
  change (Real.sqrt (1 - a ^ 2) * a ^ (e + 1) *
      ((1 - a ^ 2) * (e : ℝ) - a ^ 2)) ^ 2 =
    (1 - a ^ 2) * (a ^ 2) ^ e *
      ((1 - a ^ 2) * a * ((e : ℝ) + 1) - a) ^ 2
  calc
    (Real.sqrt (1 - a ^ 2) * a ^ (e + 1) *
        ((1 - a ^ 2) * (e : ℝ) - a ^ 2)) ^ 2 =
        Real.sqrt (1 - a ^ 2) ^ 2 * (a ^ (e + 1)) ^ 2 *
          ((1 - a ^ 2) * (e : ℝ) - a ^ 2) ^ 2 := by
            ring
    _ = Real.sqrt (1 - a ^ 2) ^ 2 * (a ^ 2) ^ e * a ^ 2 *
          ((1 - a ^ 2) * (e : ℝ) - a ^ 2) ^ 2 := by
            rw [haPow]
            ring
    _ = (1 - a ^ 2) * (a ^ 2) ^ e *
        ((1 - a ^ 2) * a * ((e : ℝ) + 1) - a) ^ 2 := by
          rw [hsqrt]
          ring

/-- The cross-prime all-depth tangent Gram kernel. -/
def gammaSewnXiShiftEndpointTangentKernel
    (p q : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    gammaSewnXiShiftEndpointTangentFeature p e *
      gammaSewnXiShiftEndpointTangentFeature q e

/-- Closed form of the cross-prime tangent kernel in inverse-prime coordinates. -/
def gammaSewnXiShiftEndpointTangentKernelClosed
    (p q : Nat.Primes) : ℝ :=
  let a := ((p : ℝ)⁻¹)
  let b := ((q : ℝ)⁻¹)
  a ^ 2 * b ^ 2 * Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) *
    ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / (1 - a * b) ^ 3

/-- Exact infinite cross-prime summation. -/
theorem hasSum_gammaSewnXiShiftEndpointTangentFeature_mul
    (p q : Nat.Primes) :
    HasSum
      (fun e : ℕ => gammaSewnXiShiftEndpointTangentFeature p e *
        gammaSewnXiShiftEndpointTangentFeature q e)
      (gammaSewnXiShiftEndpointTangentKernelClosed p q) := by
  let a := ((p : ℝ)⁻¹)
  let b := ((q : ℝ)⁻¹)
  let u := a * b
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hq : (1 : ℝ) < q := by exact_mod_cast q.2.one_lt
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have ha1 : a < 1 := by
    dsimp only [a]
    exact (inv_lt_one₀ (by positivity)).mpr hp
  have hb1 : b < 1 := by
    dsimp only [b]
    exact (inv_lt_one₀ (by positivity)).mpr hq
  have hu0 : 0 < u := mul_pos ha0 hb0
  have hu1 : u < 1 := mul_lt_one_of_nonneg_of_lt_one_left ha0.le ha1 hb1.le
  have hunorm : ‖u‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hu0]
    exact hu1
  have hzero := hasSum_geometric_of_norm_lt_one (K := ℝ) hunorm
  have hone := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hunorm
  have htwo := hasSum_nat_sq_mul_geometric hunorm
  let A := (1 - a ^ 2) * (1 - b ^ 2)
  let B := -((1 - a ^ 2) * b ^ 2 + (1 - b ^ 2) * a ^ 2)
  let C := a ^ 2 * b ^ 2
  let D := Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) * a * b
  have hpoly := ((htwo.mul_left A).add (hone.mul_left B)).add (hzero.mul_left C)
  have hscaled := hpoly.mul_left D
  have hscaled' : HasSum
      (fun e : ℕ => gammaSewnXiShiftEndpointTangentFeature p e *
        gammaSewnXiShiftEndpointTangentFeature q e)
      (D * (A * (u * (1 + u) / (1 - u) ^ 3) +
        B * (u / (1 - u) ^ 2) + C * (1 - u)⁻¹)) := by
    apply HasSum.congr_fun hscaled
    intro e
    change (Real.sqrt (1 - a ^ 2) * a ^ (e + 1) *
        ((1 - a ^ 2) * (e : ℝ) - a ^ 2)) *
      (Real.sqrt (1 - b ^ 2) * b ^ (e + 1) *
        ((1 - b ^ 2) * (e : ℝ) - b ^ 2)) =
      D * (A * ((e : ℝ) ^ 2 * u ^ e) +
        B * ((e : ℝ) * u ^ e) + C * u ^ e)
    rw [pow_succ, pow_succ]
    change _ = D * (A * ((e : ℝ) ^ 2 * (a * b) ^ e) +
      B * ((e : ℝ) * (a * b) ^ e) + C * (a * b) ^ e)
    rw [mul_pow]
    dsimp only [A, B, C, D]
    ring_nf
  have hvalue :
      gammaSewnXiShiftEndpointTangentKernelClosed p q =
        D * (A * (u * (1 + u) / (1 - u) ^ 3) +
          B * (u / (1 - u) ^ 2) + C * (1 - u)⁻¹) := by
    dsimp only [gammaSewnXiShiftEndpointTangentKernelClosed,
      u]
    have hden : 1 - a * b ≠ 0 := sub_ne_zero.mpr hu1.ne'
    have haSq : 0 ≤ 1 - a ^ 2 := by
      nlinarith [sq_lt_sq₀ ha0.le (by norm_num) |>.2 ha1]
    have hbSq : 0 ≤ 1 - b ^ 2 := by
      nlinarith [sq_lt_sq₀ hb0.le (by norm_num) |>.2 hb1]
    change a ^ 2 * b ^ 2 * Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) *
        ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / (1 - a * b) ^ 3 =
      D * (A * (u * (1 + u) / (1 - u) ^ 3) +
        B * (u / (1 - u) ^ 2) + C * (1 - u)⁻¹)
    rw [Real.sqrt_mul haSq]
    dsimp only [A, B, C, D, u]
    field_simp [hden]
    ring_nf
  rw [hvalue]
  exact hscaled'

theorem gammaSewnXiShiftEndpointTangentKernel_eq_closed
    (p q : Nat.Primes) :
    gammaSewnXiShiftEndpointTangentKernel p q =
      gammaSewnXiShiftEndpointTangentKernelClosed p q :=
  (hasSum_gammaSewnXiShiftEndpointTangentFeature_mul p q).tsum_eq

theorem gammaSewnXiShiftEndpointTangentKernel_symm
    (p q : Nat.Primes) :
    gammaSewnXiShiftEndpointTangentKernel p q =
      gammaSewnXiShiftEndpointTangentKernel q p := by
  unfold gammaSewnXiShiftEndpointTangentKernel
  apply tsum_congr
  intro e
  ring

/-- The diagonal of the new cross-prime kernel recovers the exact `p⁻⁴` tangent mass. -/
theorem gammaSewnXiShiftEndpointTangentKernel_self
    (p : Nat.Primes) :
    gammaSewnXiShiftEndpointTangentKernel p p = ((p : ℝ)⁻¹) ^ 4 := by
  rw [gammaSewnXiShiftEndpointTangentKernel]
  rw [← (hasSum_gammaSewnXiShiftDepthProbability_mul_endpointHeightLift_centered_sq_eq_inv_four
    p).tsum_eq]
  apply tsum_congr
  intro e
  simpa [pow_two] using
    gammaSewnXiShiftEndpointTangentFeature_sq_eq p e

/-- Prime parameters lie in the positive chamber of the exact cross kernel.  Thus centering does
not destroy cross-prime correlation: it removes only the father mode. -/
theorem gammaSewnXiShiftEndpointTangentKernel_pos
    (p q : Nat.Primes) :
    0 < gammaSewnXiShiftEndpointTangentKernel p q := by
  let a := ((p : ℝ)⁻¹)
  let b := ((q : ℝ)⁻¹)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.2.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast q.2.two_le
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have haHalf : a ≤ 1 / 2 := by
    dsimp only [a]
    rw [inv_eq_one_div, div_le_iff₀ hp0]
    nlinarith
  have hbHalf : b ≤ 1 / 2 := by
    dsimp only [b]
    rw [inv_eq_one_div, div_le_iff₀ hq0]
    nlinarith
  have haSq : a ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hbSq : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (b - 1 / 2)]
  have hroot : 0 < (1 - a ^ 2) * (1 - b ^ 2) := by nlinarith
  have habHalf' : a * b ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
    mul_le_mul haHalf hbHalf hb0.le (by norm_num)
  have habHalf : a * b ≤ 1 / 4 := by nlinarith
  have hnode : 0 < 1 - a * b := by nlinarith
  have hnumerator : 0 < (1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2) := by
    have hab : 0 < a * b := mul_pos ha0 hb0
    nlinarith [sq_pos_of_pos hab]
  rw [gammaSewnXiShiftEndpointTangentKernel_eq_closed]
  change 0 < a ^ 2 * b ^ 2 *
      Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) *
        ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / (1 - a * b) ^ 3
  exact div_pos (by positivity) (pow_pos hnode 3)

/-- The forced `p²` normalization of the endpoint tangent feature. -/
def gammaSewnXiShiftEndpointUnitTangentFeature
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  (p : ℝ) ^ 2 * gammaSewnXiShiftEndpointTangentFeature p e

/-- The normalized cross-prime tangent correlation kernel. -/
def gammaSewnXiShiftEndpointUnitTangentKernel
    (p q : Nat.Primes) : ℝ :=
  (p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
    gammaSewnXiShiftEndpointTangentKernel p q

theorem hasSum_gammaSewnXiShiftEndpointUnitTangentFeature_mul
    (p q : Nat.Primes) :
    HasSum
      (fun e : ℕ => gammaSewnXiShiftEndpointUnitTangentFeature p e *
        gammaSewnXiShiftEndpointUnitTangentFeature q e)
      (gammaSewnXiShiftEndpointUnitTangentKernel p q) := by
  have h := (hasSum_gammaSewnXiShiftEndpointTangentFeature_mul p q).mul_left
    ((p : ℝ) ^ 2 * (q : ℝ) ^ 2)
  have h' : HasSum
      (fun e : ℕ => gammaSewnXiShiftEndpointUnitTangentFeature p e *
        gammaSewnXiShiftEndpointUnitTangentFeature q e)
      ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
        gammaSewnXiShiftEndpointTangentKernelClosed p q) := by
    apply HasSum.congr_fun h
    intro e
    simp only [gammaSewnXiShiftEndpointUnitTangentFeature]
    ring_nf
  have hvalue :
      gammaSewnXiShiftEndpointUnitTangentKernel p q =
        (p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
          gammaSewnXiShiftEndpointTangentKernelClosed p q := by
    rw [gammaSewnXiShiftEndpointUnitTangentKernel,
      gammaSewnXiShiftEndpointTangentKernel_eq_closed]
  rw [hvalue]
  exact h'

/-- Every normalized prime tangent has unit all-depth mass. -/
theorem gammaSewnXiShiftEndpointUnitTangentKernel_self
    (p : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentKernel p p = 1 := by
  rw [gammaSewnXiShiftEndpointUnitTangentKernel,
    gammaSewnXiShiftEndpointTangentKernel_self]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hp]

/-- Squared Hilbert distance between two normalized all-depth endpoint tangents. -/
def gammaSewnXiShiftEndpointUnitTangentDistanceSq
    (p q : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    (gammaSewnXiShiftEndpointUnitTangentFeature p e -
      gammaSewnXiShiftEndpointUnitTangentFeature q e) ^ 2

/-- The correlation defect is exactly half the squared all-depth tangent distance. -/
theorem gammaSewnXiShiftEndpointUnitTangentDistanceSq_eq
    (p q : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentDistanceSq p q =
      2 * (1 - gammaSewnXiShiftEndpointUnitTangentKernel p q) := by
  have hpp := hasSum_gammaSewnXiShiftEndpointUnitTangentFeature_mul p p
  have hqq := hasSum_gammaSewnXiShiftEndpointUnitTangentFeature_mul q q
  have hpq := hasSum_gammaSewnXiShiftEndpointUnitTangentFeature_mul p q
  have hsum := (hpp.add hqq).sub (hpq.mul_left 2)
  have htarget :
      gammaSewnXiShiftEndpointUnitTangentKernel p p +
          gammaSewnXiShiftEndpointUnitTangentKernel q q -
            2 * gammaSewnXiShiftEndpointUnitTangentKernel p q =
        2 * (1 - gammaSewnXiShiftEndpointUnitTangentKernel p q) := by
    rw [gammaSewnXiShiftEndpointUnitTangentKernel_self,
      gammaSewnXiShiftEndpointUnitTangentKernel_self]
    ring
  unfold gammaSewnXiShiftEndpointUnitTangentDistanceSq
  rw [← htarget]
  have hsum' : HasSum
      (fun e : ℕ =>
        (gammaSewnXiShiftEndpointUnitTangentFeature p e -
          gammaSewnXiShiftEndpointUnitTangentFeature q e) ^ 2)
      (gammaSewnXiShiftEndpointUnitTangentKernel p p +
        gammaSewnXiShiftEndpointUnitTangentKernel q q -
          2 * gammaSewnXiShiftEndpointUnitTangentKernel p q) := by
    apply hsum.congr
    intro e
    ring_nf
  exact hsum'.tsum_eq

/-- The actual cross-prime tangent correlation is contractive without an assumed colligation. -/
theorem gammaSewnXiShiftEndpointUnitTangentKernel_le_one
    (p q : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentKernel p q ≤ 1 := by
  have hnonneg : 0 ≤ gammaSewnXiShiftEndpointUnitTangentDistanceSq p q := by
    unfold gammaSewnXiShiftEndpointUnitTangentDistanceSq
    exact tsum_nonneg fun e => sq_nonneg _
  rw [gammaSewnXiShiftEndpointUnitTangentDistanceSq_eq] at hnonneg
  linarith

theorem gammaSewnXiShiftEndpointUnitTangentKernel_pos
    (p q : Nat.Primes) :
    0 < gammaSewnXiShiftEndpointUnitTangentKernel p q := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hq : (0 : ℝ) < q := by exact_mod_cast q.2.pos
  unfold gammaSewnXiShiftEndpointUnitTangentKernel
  exact mul_pos (mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos hq))
    (gammaSewnXiShiftEndpointTangentKernel_pos p q)

/-! ## The exact compound-order obstruction

The source tangent kernel is a second-compound producer.  A full three-node response determinant
also contains a connected third-compound term, which a rooted scalar times a second compound does
not remove.  The following source specialization isolates that term exactly.
-/

/-- Determinant of a symmetric three-node matrix with common diagonal `d`. -/
def constantDiagonalThreePointDet (d xy xz yz : ℝ) : ℝ :=
  d ^ 3 + 2 * xy * xz * yz - d * (xy ^ 2 + xz ^ 2 + yz ^ 2)

/-- Quadratic second-compound expression of three tangent edges. -/
def rootedTangentSecondCompound (xy xz yz : ℝ) : ℝ :=
  2 * (xy * xz + xy * yz + xz * yz) - (xy ^ 2 + xz ^ 2 + yz ^ 2)

/-- A rank-one root converts the tangent second compound only into the rooted part of the
three-node determinant; the pure tangent third compound survives exactly. -/
theorem constantDiagonalThreePointDet_root_add_tangent
    (d xy xz yz : ℝ) :
    constantDiagonalThreePointDet d (d + xy) (d + xz) (d + yz) =
      d * rootedTangentSecondCompound xy xz yz + 2 * xy * xz * yz := by
  unfold constantDiagonalThreePointDet rootedTangentSecondCompound
  ring

/-- The actual completed endpoint determinant on three prime nodes. -/
def xiPhysicalEndpointCompletedThreePrimeDet
    (p q r : Nat.Primes) : ℝ :=
  constantDiagonalThreePointDet
    (xiPhysicalEndpointCompletedKernel 0).re
    (xiPhysicalEndpointCompletedPrimeRatioRealKernel p q)
    (xiPhysicalEndpointCompletedPrimeRatioRealKernel p r)
    (xiPhysicalEndpointCompletedPrimeRatioRealKernel q r)

/-- **Exact source compound split.**  The completed three-prime determinant is rooted stiffness
times the tangent second compound plus the pure tangent third compound. -/
theorem xiPhysicalEndpointCompletedThreePrimeDet_eq_rootedSecond_add_tangentThird
    (p q r : Nat.Primes) :
    xiPhysicalEndpointCompletedThreePrimeDet p q r =
      (xiPhysicalEndpointCompletedKernel 0).re *
        rootedTangentSecondCompound
          (xiPhysicalEndpointTangentPrimeRatioRealKernel p q)
          (xiPhysicalEndpointTangentPrimeRatioRealKernel p r)
          (xiPhysicalEndpointTangentPrimeRatioRealKernel q r) +
      2 * xiPhysicalEndpointTangentPrimeRatioRealKernel p q *
        xiPhysicalEndpointTangentPrimeRatioRealKernel p r *
          xiPhysicalEndpointTangentPrimeRatioRealKernel q r := by
  rw [xiPhysicalEndpointCompletedThreePrimeDet]
  have hpq : xiPhysicalEndpointCompletedPrimeRatioRealKernel p q =
      (xiPhysicalEndpointCompletedKernel 0).re +
        xiPhysicalEndpointTangentPrimeRatioRealKernel p q := by
    unfold xiPhysicalEndpointTangentPrimeRatioRealKernel
    ring
  have hpr : xiPhysicalEndpointCompletedPrimeRatioRealKernel p r =
      (xiPhysicalEndpointCompletedKernel 0).re +
        xiPhysicalEndpointTangentPrimeRatioRealKernel p r := by
    unfold xiPhysicalEndpointTangentPrimeRatioRealKernel
    ring
  have hqr : xiPhysicalEndpointCompletedPrimeRatioRealKernel q r =
      (xiPhysicalEndpointCompletedKernel 0).re +
        xiPhysicalEndpointTangentPrimeRatioRealKernel q r := by
    unfold xiPhysicalEndpointTangentPrimeRatioRealKernel
    ring
  rw [hpq, hpr, hqr]
  exact constantDiagonalThreePointDet_root_add_tangent _ _ _ _

/-- Therefore an exact identification of the full three-node determinant with only the rooted
second compound is possible exactly when at least one tangent edge vanishes. -/
theorem xiPhysicalEndpointCompletedThreePrimeDet_eq_rootedSecond_iff
    (p q r : Nat.Primes) :
    xiPhysicalEndpointCompletedThreePrimeDet p q r =
        (xiPhysicalEndpointCompletedKernel 0).re *
          rootedTangentSecondCompound
            (xiPhysicalEndpointTangentPrimeRatioRealKernel p q)
            (xiPhysicalEndpointTangentPrimeRatioRealKernel p r)
            (xiPhysicalEndpointTangentPrimeRatioRealKernel q r) ↔
      xiPhysicalEndpointTangentPrimeRatioRealKernel p q *
        xiPhysicalEndpointTangentPrimeRatioRealKernel p r *
          xiPhysicalEndpointTangentPrimeRatioRealKernel q r = 0 := by
  rw [xiPhysicalEndpointCompletedThreePrimeDet_eq_rootedSecond_add_tangentThird]
  constructor <;> intro h
  · linarith
  · nlinarith [h]

/-- The tangent generating function on the shared depth coordinate. -/
def gammaSewnXiShiftEndpointTangentGeneratingFunction
    (p : Nat.Primes) (z : ℝ) : ℝ :=
  ∑' e : ℕ, gammaSewnXiShiftEndpointTangentFeature p e * z ^ e

/-- **Rooted double-pole law.**  The all-depth tangent has its source root at the inverse prime and
its only rational pole at the prime, with multiplicity two. -/
theorem gammaSewnXiShiftEndpointTangentGeneratingFunction_eq
    (p : Nat.Primes) {z : ℝ}
    (hz : ‖((p : ℝ)⁻¹) * z‖ < 1) :
    gammaSewnXiShiftEndpointTangentGeneratingFunction p z =
      ((p : ℝ)⁻¹) ^ 2 * Real.sqrt (1 - ((p : ℝ)⁻¹) ^ 2) *
        (z - (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹ * z) ^ 2 := by
  let a := ((p : ℝ)⁻¹)
  let u := a * z
  have hzero := hasSum_geometric_of_norm_lt_one (K := ℝ) hz
  have hone := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hz
  have hsum := ((hone.mul_left (1 - a ^ 2)).sub
    (hzero.mul_left (a ^ 2))).mul_left (Real.sqrt (1 - a ^ 2) * a)
  unfold gammaSewnXiShiftEndpointTangentGeneratingFunction
  have hden : 1 - a * z ≠ 0 := by
    intro h
    have hu : a * z = 1 := by linarith
    rw [hu] at hz
    norm_num at hz
  have hsum' : HasSum
      (fun e : ℕ => gammaSewnXiShiftEndpointTangentFeature p e * z ^ e)
      (Real.sqrt (1 - a ^ 2) * a *
        ((1 - a ^ 2) * (u / (1 - u) ^ 2) - a ^ 2 * (1 - u)⁻¹)) := by
    apply HasSum.congr_fun hsum
    intro e
    change (Real.sqrt (1 - a ^ 2) * a ^ (e + 1) *
        ((1 - a ^ 2) * (e : ℝ) - a ^ 2)) * z ^ e =
      Real.sqrt (1 - a ^ 2) * a *
        ((1 - a ^ 2) * ((e : ℝ) * u ^ e) - a ^ 2 * u ^ e)
    rw [pow_succ]
    change _ = Real.sqrt (1 - a ^ 2) * a *
      ((1 - a ^ 2) * ((e : ℝ) * (a * z) ^ e) - a ^ 2 * (a * z) ^ e)
    rw [mul_pow]
    ring_nf
  rw [hsum'.tsum_eq]
  change Real.sqrt (1 - a ^ 2) * a *
      ((1 - a ^ 2) * (a * z / (1 - a * z) ^ 2) -
        a ^ 2 * (1 - a * z)⁻¹) =
    a ^ 2 * Real.sqrt (1 - a ^ 2) * (z - a) / (1 - a * z) ^ 2
  field_simp [hden]
  ring

/-- The inverse prime is an actual root of the complete tangent depth transform.  It is not an
auxiliary cancellation imposed after forming the Gram. -/
theorem gammaSewnXiShiftEndpointTangentGeneratingFunction_inversePrime
    (p : Nat.Primes) :
    gammaSewnXiShiftEndpointTangentGeneratingFunction p ((p : ℝ)⁻¹) = 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have ha0 : 0 < (p : ℝ)⁻¹ := by positivity
  have ha1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp
  have hz : ‖((p : ℝ)⁻¹) * (p : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos ha0 ha0)]
    nlinarith [sq_lt_sq₀ ha0.le (by norm_num) |>.2 ha1]
  rw [gammaSewnXiShiftEndpointTangentGeneratingFunction_eq p hz]
  simp

end

end RHTower
