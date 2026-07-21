import GaloisForLFunctions.RHTower.GammaSewnXiShiftTangentHilbertKernel

/-!
# The Xi-shift tangent exterior cube

The normalized completed `+2` Xi-shift tangent at prime `p` already has a strict third exterior
coordinate in its first three valuation depths.  Writing `a = p⁻¹`, these coordinates are

`-a sqrt(1-a²)`, `(1-2a²)sqrt(1-a²)`, and `a(2-3a²)sqrt(1-a²)`.

For three distinct primes, their determinant is a generalized Vandermonde factor times positive
source weights.  This is a literal source theorem: it uses no Xi zero, target response, RH
criterion, selected deep valuation, inverse-resolution lift, or post-hoc Gram realization.

The theorem does not identify this source exterior cube with the pure third-compound term of the
completed three-node response.  That coefficientwise response intertwiner remains open.
-/

open scoped Matrix

namespace RHTower

noncomputable section

/-- First-three-coordinate model for three normalized Xi-shift tangents, in inverse-prime
coordinates `a`, `b`, and `c`. -/
def xiShiftTangentExteriorFrame (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-a * Real.sqrt (1 - a ^ 2), -b * Real.sqrt (1 - b ^ 2),
      -c * Real.sqrt (1 - c ^ 2);
    (1 - 2 * a ^ 2) * Real.sqrt (1 - a ^ 2),
      (1 - 2 * b ^ 2) * Real.sqrt (1 - b ^ 2),
      (1 - 2 * c ^ 2) * Real.sqrt (1 - c ^ 2);
    a * (2 - 3 * a ^ 2) * Real.sqrt (1 - a ^ 2),
      b * (2 - 3 * b ^ 2) * Real.sqrt (1 - b ^ 2),
      c * (2 - 3 * c ^ 2) * Real.sqrt (1 - c ^ 2)]

/-- Exact generalized-Vandermonde factorization of the abstract exterior frame. -/
theorem xiShiftTangentExteriorFrame_det_eq (a b c : ℝ) :
    (xiShiftTangentExteriorFrame a b c).det =
      -3 * Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) *
        Real.sqrt (1 - c ^ 2) *
        (b - a) * (c - a) * (c - b) * (a + b + c + 2 * a * b * c) := by
  simp [xiShiftTangentExteriorFrame, Matrix.det_fin_three]
  ring

/-- Squared exterior-volume formula once the three source weights are nonnegative. -/
theorem xiShiftTangentExteriorFrame_det_sq_eq (a b c : ℝ)
    (ha : 0 ≤ 1 - a ^ 2) (hb : 0 ≤ 1 - b ^ 2) (hc : 0 ≤ 1 - c ^ 2) :
    (xiShiftTangentExteriorFrame a b c).det ^ 2 =
      9 * (1 - a ^ 2) * (1 - b ^ 2) * (1 - c ^ 2) *
        (b - a) ^ 2 * (c - a) ^ 2 * (c - b) ^ 2 *
        (a + b + c + 2 * a * b * c) ^ 2 := by
  rw [xiShiftTangentExteriorFrame_det_eq]
  calc
    (-3 * Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) *
          Real.sqrt (1 - c ^ 2) *
          (b - a) * (c - a) * (c - b) *
          (a + b + c + 2 * a * b * c)) ^ 2 =
        9 * Real.sqrt (1 - a ^ 2) ^ 2 * Real.sqrt (1 - b ^ 2) ^ 2 *
          Real.sqrt (1 - c ^ 2) ^ 2 *
          (b - a) ^ 2 * (c - a) ^ 2 * (c - b) ^ 2 *
          (a + b + c + 2 * a * b * c) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc]

/-- Depth-zero coordinate of the actual normalized Xi-shift tangent. -/
theorem gammaSewnXiShiftEndpointUnitTangentFeature_zero (p : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentFeature p 0 =
      -((p : ℝ)⁻¹) * Real.sqrt (1 - ((p : ℝ)⁻¹) ^ 2) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  unfold gammaSewnXiShiftEndpointUnitTangentFeature
    gammaSewnXiShiftEndpointTangentFeature
  dsimp
  norm_num
  field_simp [hp]

/-- Depth-one coordinate of the actual normalized Xi-shift tangent. -/
theorem gammaSewnXiShiftEndpointUnitTangentFeature_one (p : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentFeature p 1 =
      (1 - 2 * ((p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (1 - ((p : ℝ)⁻¹) ^ 2) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  unfold gammaSewnXiShiftEndpointUnitTangentFeature
    gammaSewnXiShiftEndpointTangentFeature
  dsimp
  norm_num
  field_simp [hp]
  ring

/-- Depth-two coordinate of the actual normalized Xi-shift tangent. -/
theorem gammaSewnXiShiftEndpointUnitTangentFeature_two (p : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentFeature p 2 =
      (p : ℝ)⁻¹ * (2 - 3 * ((p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (1 - ((p : ℝ)⁻¹) ^ 2) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  unfold gammaSewnXiShiftEndpointUnitTangentFeature
    gammaSewnXiShiftEndpointTangentFeature
  dsimp
  norm_num
  field_simp [hp]
  ring

/-- The literal first-three-depth frame of three normalized source tangents. -/
def gammaSewnXiShiftEndpointUnitTangentFrame (p q r : Nat.Primes) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![gammaSewnXiShiftEndpointUnitTangentFeature p 0,
      gammaSewnXiShiftEndpointUnitTangentFeature q 0,
      gammaSewnXiShiftEndpointUnitTangentFeature r 0;
    gammaSewnXiShiftEndpointUnitTangentFeature p 1,
      gammaSewnXiShiftEndpointUnitTangentFeature q 1,
      gammaSewnXiShiftEndpointUnitTangentFeature r 1;
    gammaSewnXiShiftEndpointUnitTangentFeature p 2,
      gammaSewnXiShiftEndpointUnitTangentFeature q 2,
      gammaSewnXiShiftEndpointUnitTangentFeature r 2]

/-- The actual source frame is the abstract inverse-prime frame. -/
theorem gammaSewnXiShiftEndpointUnitTangentFrame_eq (p q r : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentFrame p q r =
      xiShiftTangentExteriorFrame ((p : ℝ)⁻¹) ((q : ℝ)⁻¹) ((r : ℝ)⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaSewnXiShiftEndpointUnitTangentFrame, xiShiftTangentExteriorFrame,
      gammaSewnXiShiftEndpointUnitTangentFeature_zero,
      gammaSewnXiShiftEndpointUnitTangentFeature_one,
      gammaSewnXiShiftEndpointUnitTangentFeature_two]

/-- Exact determinant formula for the actual three-prime source frame. -/
theorem gammaSewnXiShiftEndpointUnitTangentFrame_det_eq (p q r : Nat.Primes) :
    (gammaSewnXiShiftEndpointUnitTangentFrame p q r).det =
      -3 * Real.sqrt (1 - ((p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (1 - ((q : ℝ)⁻¹) ^ 2) *
        Real.sqrt (1 - ((r : ℝ)⁻¹) ^ 2) *
        ((q : ℝ)⁻¹ - (p : ℝ)⁻¹) *
        ((r : ℝ)⁻¹ - (p : ℝ)⁻¹) *
        ((r : ℝ)⁻¹ - (q : ℝ)⁻¹) *
        ((p : ℝ)⁻¹ + (q : ℝ)⁻¹ + (r : ℝ)⁻¹ +
          2 * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ * (r : ℝ)⁻¹) := by
  rw [gammaSewnXiShiftEndpointUnitTangentFrame_eq]
  exact xiShiftTangentExteriorFrame_det_eq _ _ _

private theorem invPrime_unit_sub_sq_pos (p : Nat.Primes) :
    0 < 1 - ((p : ℝ)⁻¹) ^ 2 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have ha0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast p.2.pos)
  have ha1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp
  nlinarith [sq_lt_sq₀ ha0.le (by norm_num) |>.2 ha1]

private theorem invPrime_ne_invPrime {p q : Nat.Primes} (hpq : p ≠ q) :
    (p : ℝ)⁻¹ ≠ (q : ℝ)⁻¹ := by
  have hpqNat : (p : ℕ) ≠ (q : ℕ) := by
    intro h
    exact hpq (Subtype.ext h)
  have hpqReal : (p : ℝ) ≠ (q : ℝ) := by exact_mod_cast hpqNat
  intro h
  exact hpqReal (inv_injective h)

/-- Exact squared exterior-volume formula for the actual three-prime source frame. -/
theorem gammaSewnXiShiftEndpointUnitTangentFrame_det_sq_eq (p q r : Nat.Primes) :
    (gammaSewnXiShiftEndpointUnitTangentFrame p q r).det ^ 2 =
      9 * (1 - ((p : ℝ)⁻¹) ^ 2) * (1 - ((q : ℝ)⁻¹) ^ 2) *
        (1 - ((r : ℝ)⁻¹) ^ 2) *
        ((q : ℝ)⁻¹ - (p : ℝ)⁻¹) ^ 2 *
        ((r : ℝ)⁻¹ - (p : ℝ)⁻¹) ^ 2 *
        ((r : ℝ)⁻¹ - (q : ℝ)⁻¹) ^ 2 *
        ((p : ℝ)⁻¹ + (q : ℝ)⁻¹ + (r : ℝ)⁻¹ +
          2 * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ * (r : ℝ)⁻¹) ^ 2 := by
  rw [gammaSewnXiShiftEndpointUnitTangentFrame_eq]
  exact xiShiftTangentExteriorFrame_det_sq_eq _ _ _
    (invPrime_unit_sub_sq_pos p).le
    (invPrime_unit_sub_sq_pos q).le
    (invPrime_unit_sub_sq_pos r).le

/-- Pairwise distinct primes have a strictly positive Xi-shift tangent exterior cube. -/
theorem gammaSewnXiShiftEndpointUnitTangentFrame_det_sq_pos
    (p q r : Nat.Primes) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    0 < (gammaSewnXiShiftEndpointUnitTangentFrame p q r).det ^ 2 := by
  have hp := invPrime_unit_sub_sq_pos p
  have hq := invPrime_unit_sub_sq_pos q
  have hr := invPrime_unit_sub_sq_pos r
  have hp0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast p.2.pos)
  have hq0 : 0 < (q : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast q.2.pos)
  have hr0 : 0 < (r : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast r.2.pos)
  have hqp : (q : ℝ)⁻¹ - (p : ℝ)⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (invPrime_ne_invPrime hpq).symm
  have hrp : (r : ℝ)⁻¹ - (p : ℝ)⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (invPrime_ne_invPrime hpr).symm
  have hrq : (r : ℝ)⁻¹ - (q : ℝ)⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (invPrime_ne_invPrime hqr).symm
  rw [gammaSewnXiShiftEndpointUnitTangentFrame_det_sq_eq]
  positivity

end

end RHTower
