import GaloisForLFunctions.HTGeometry.KerrNewmanBoyerLindquistLocalSmoothness
import GaloisForLFunctions.HTGeometry.KerrNewmanHorizonAlgebra

/-!
# Algebraic global structure of Kerr--Newman--Bertotti--Robinson spacetime

This module formalizes the denominator-cleared identities behind arXiv:2608.28265,
*Global structure of Kerr-Newman-BR spacetime*.  It covers the Schwarzschild--BR reciprocal
chart, the generic rotating radial and reciprocal potentials, the conformal seam, the ring
singularity carrier, branch matching, Kruskal-type coordinates, and arctangent compactification.

All results are unconditional algebraic or smoothness statements.  They do not assert geodesic
maximality, solve the Einstein--Maxwell equations, or identify a unique global gluing.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped ContDiff

/-! ## Schwarzschild--BR potentials and horizon -/

/-- Angular coefficient `P_y` in the reciprocal Schwarzschild--BR chart. -/
def schwarzschildBRPolarFactor (mass magnetic polarX : ℝ) : ℝ :=
  (1 - polarX ^ 2) * (1 + magnetic ^ 2 * mass ^ 2 * polarX ^ 2)

/-- Positive radial dressing factor `I` in the Schwarzschild--BR chart. -/
def schwarzschildBRRadialWeight (mass magnetic radius : ℝ) : ℝ :=
  (1 - magnetic ^ 2 * mass * radius) ^ 2 + magnetic ^ 2 * radius ^ 2

/-- Denominator-cleared Schwarzschild--BR radial lapse numerator. -/
def schwarzschildBRClearedLapse (mass magnetic radius : ℝ) : ℝ :=
  schwarzschildBRRadialWeight mass magnetic radius *
    ((1 + magnetic ^ 2 * mass ^ 2) * radius - 2 * mass)

/-- Unique algebraic Schwarzschild--BR horizon radius. -/
def schwarzschildBRHorizonRadius (mass magnetic : ℝ) : ℝ :=
  2 * mass / (1 + magnetic ^ 2 * mass ^ 2)

/-- Reciprocal radial weight `I_y`. -/
def schwarzschildBRReciprocalWeight (mass magnetic reciprocalRadius : ℝ) : ℝ :=
  (reciprocalRadius - magnetic ^ 2 * mass) ^ 2 + magnetic ^ 2

/-- Reciprocal radial lapse `Q_y`. -/
def schwarzschildBRReciprocalLapse (mass magnetic reciprocalRadius : ℝ) : ℝ :=
  schwarzschildBRReciprocalWeight mass magnetic reciprocalRadius *
    ((1 + magnetic ^ 2 * mass ^ 2) - 2 * mass * reciprocalRadius)

/-- Reciprocal conformal factor squared `Omega_y^2`. -/
def schwarzschildBRReciprocalConformalSq
    (mass magnetic polarX reciprocalRadius : ℝ) : ℝ :=
  schwarzschildBRReciprocalWeight mass magnetic reciprocalRadius -
    magnetic ^ 2 * ((1 + magnetic ^ 2 * mass ^ 2) - 2 * mass * reciprocalRadius) *
      polarX ^ 2

/-- Denominator-cleared Weyl-flatness factor in reciprocal coordinates. -/
def schwarzschildBRReciprocalWeylFactor
    (mass magnetic polarX reciprocalRadius : ℝ) : ℝ :=
  reciprocalRadius - magnetic ^ 2 * mass * (1 - polarX ^ 2)

theorem schwarzschildBRRadialWeight_eq_sum_sq
    (mass magnetic radius : ℝ) :
    schwarzschildBRRadialWeight mass magnetic radius =
      (1 - magnetic ^ 2 * mass * radius) ^ 2 + (magnetic * radius) ^ 2 := by
  simp only [schwarzschildBRRadialWeight]
  ring

/-- The magnetic dressing never creates an additional radial zero. -/
theorem schwarzschildBRRadialWeight_pos (mass magnetic radius : ℝ) :
    0 < schwarzschildBRRadialWeight mass magnetic radius := by
  rw [schwarzschildBRRadialWeight_eq_sum_sq]
  by_cases hB : magnetic = 0
  · simp [hB]
  by_cases hr : radius = 0
  · simp [hr]
  have hBr : magnetic * radius ≠ 0 := mul_ne_zero hB hr
  have hs : 0 < (magnetic * radius) ^ 2 := sq_pos_of_ne_zero hBr
  nlinarith [sq_nonneg (1 - magnetic ^ 2 * mass * radius)]

/-- Zeros of the dressed lapse are exactly zeros of its linear horizon factor. -/
theorem schwarzschildBRClearedLapse_eq_zero_iff (mass magnetic radius : ℝ) :
    schwarzschildBRClearedLapse mass magnetic radius = 0 ↔
      (1 + magnetic ^ 2 * mass ^ 2) * radius - 2 * mass = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hI | hlinear
    · exact False.elim ((ne_of_gt (schwarzschildBRRadialWeight_pos mass magnetic radius)) hI)
    · exact hlinear
  · intro h
    simp [schwarzschildBRClearedLapse, h]

theorem schwarzschildBRHorizonCoefficient_pos (mass magnetic : ℝ) :
    0 < 1 + magnetic ^ 2 * mass ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg magnetic) (sq_nonneg mass)]

/-- Exact horizon classification, valid also at zero mass and zero magnetic field. -/
theorem schwarzschildBRClearedLapse_eq_zero_iff_horizon (mass magnetic radius : ℝ) :
    schwarzschildBRClearedLapse mass magnetic radius = 0 ↔
      radius = schwarzschildBRHorizonRadius mass magnetic := by
  rw [schwarzschildBRClearedLapse_eq_zero_iff]
  have hne : 1 + magnetic ^ 2 * mass ^ 2 ≠ 0 :=
    ne_of_gt (schwarzschildBRHorizonCoefficient_pos mass magnetic)
  unfold schwarzschildBRHorizonRadius
  rw [eq_div_iff hne]
  constructor <;> intro h <;> nlinarith

theorem schwarzschildBRHorizonRadius_zeroField (mass : ℝ) :
    schwarzschildBRHorizonRadius mass 0 = 2 * mass := by
  simp [schwarzschildBRHorizonRadius]

/-- Reciprocal substitution clears the radial denominator exactly away from the chart seam. -/
theorem schwarzschildBRRadialWeight_reciprocalClearing
    (mass magnetic : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ 2 * schwarzschildBRRadialWeight mass magnetic y.1⁻¹ =
      schwarzschildBRReciprocalWeight mass magnetic y.1 := by
  unfold schwarzschildBRRadialWeight schwarzschildBRReciprocalWeight
  field_simp [y.2]

theorem schwarzschildBRReciprocalWeight_eq_zero_iff
    (mass magnetic reciprocalRadius : ℝ) :
    schwarzschildBRReciprocalWeight mass magnetic reciprocalRadius = 0 ↔
      magnetic = 0 ∧ reciprocalRadius = 0 := by
  unfold schwarzschildBRReciprocalWeight
  constructor
  · intro h
    have hBsq : magnetic ^ 2 = 0 := by
      nlinarith [sq_nonneg (reciprocalRadius - magnetic ^ 2 * mass), sq_nonneg magnetic]
    have hfirst : (reciprocalRadius - magnetic ^ 2 * mass) ^ 2 = 0 := by
      nlinarith [sq_nonneg (reciprocalRadius - magnetic ^ 2 * mass), sq_nonneg magnetic]
    have hB : magnetic = 0 := sq_eq_zero_iff.mp hBsq
    exact ⟨hB, by simpa [hB] using sq_eq_zero_iff.mp hfirst⟩
  · rintro ⟨hB, hy⟩
    simp [hB, hy]

/-- Reciprocal clearing exposes one exceptional seam zero in addition to the horizon factor. -/
theorem schwarzschildBRReciprocalLapse_eq_zero_iff
    (mass magnetic reciprocalRadius : ℝ) :
    schwarzschildBRReciprocalLapse mass magnetic reciprocalRadius = 0 ↔
      (magnetic = 0 ∧ reciprocalRadius = 0) ∨
        (1 + magnetic ^ 2 * mass ^ 2) - 2 * mass * reciprocalRadius = 0 := by
  unfold schwarzschildBRReciprocalLapse
  rw [mul_eq_zero, schwarzschildBRReciprocalWeight_eq_zero_iff]

/-- The reciprocal conformal factor has an exact nonnegative decomposition on the polar strip. -/
theorem schwarzschildBRReciprocalConformalSq_completeSquare
    (mass magnetic polarX reciprocalRadius : ℝ) :
    schwarzschildBRReciprocalConformalSq mass magnetic polarX reciprocalRadius =
      (reciprocalRadius - magnetic ^ 2 * mass * (1 - polarX ^ 2)) ^ 2 +
        magnetic ^ 2 * (1 - polarX ^ 2) *
          (1 + magnetic ^ 2 * mass ^ 2 * polarX ^ 2) := by
  simp only [schwarzschildBRReciprocalConformalSq, schwarzschildBRReciprocalWeight]
  ring

theorem schwarzschildBRReciprocalConformalSq_nonneg
    (mass magnetic reciprocalRadius : ℝ) (polarX : Set.Icc (-1 : ℝ) 1) :
    0 ≤ schwarzschildBRReciprocalConformalSq mass magnetic polarX.1 reciprocalRadius := by
  rw [schwarzschildBRReciprocalConformalSq_completeSquare]
  have hx : 0 ≤ 1 - polarX.1 ^ 2 := by nlinarith [polarX.2.1, polarX.2.2]
  have hlast : 0 ≤ 1 + magnetic ^ 2 * mass ^ 2 * polarX.1 ^ 2 := by positivity
  positivity

/-- Exact conformal zero law before resolving the polar-axis factor. -/
theorem schwarzschildBRReciprocalConformalSq_eq_zero_iff
    (mass magnetic reciprocalRadius : ℝ) (polarX : Set.Icc (-1 : ℝ) 1) :
    schwarzschildBRReciprocalConformalSq mass magnetic polarX.1 reciprocalRadius = 0 ↔
      reciprocalRadius = magnetic ^ 2 * mass * (1 - polarX.1 ^ 2) ∧
        magnetic ^ 2 * (1 - polarX.1 ^ 2) = 0 := by
  rw [schwarzschildBRReciprocalConformalSq_completeSquare]
  have hx : 0 ≤ 1 - polarX.1 ^ 2 := by nlinarith [polarX.2.1, polarX.2.2]
  have hv : 0 < 1 + magnetic ^ 2 * mass ^ 2 * polarX.1 ^ 2 := by positivity
  have hu : 0 ≤ magnetic ^ 2 * (1 - polarX.1 ^ 2) := mul_nonneg (sq_nonneg _) hx
  constructor
  · intro h
    have hsquare :
        (reciprocalRadius - magnetic ^ 2 * mass * (1 - polarX.1 ^ 2)) ^ 2 = 0 := by
      nlinarith [mul_nonneg hu hv.le]
    have hproduct :
        magnetic ^ 2 * (1 - polarX.1 ^ 2) *
          (1 + magnetic ^ 2 * mass ^ 2 * polarX.1 ^ 2) = 0 := by
      nlinarith [sq_nonneg
        (reciprocalRadius - magnetic ^ 2 * mass * (1 - polarX.1 ^ 2))]
    have hbase : magnetic ^ 2 * (1 - polarX.1 ^ 2) = 0 := by
      rcases mul_eq_zero.mp hproduct with hzero | hfalse
      · exact hzero
      · exact False.elim ((ne_of_gt hv) hfalse)
    have hy : reciprocalRadius = magnetic ^ 2 * mass * (1 - polarX.1 ^ 2) := by
      nlinarith [hsquare]
    exact ⟨hy, hbase⟩
  · rintro ⟨hy, hbase⟩
    calc
      (reciprocalRadius - magnetic ^ 2 * mass * (1 - polarX.1 ^ 2)) ^ 2 +
          magnetic ^ 2 * (1 - polarX.1 ^ 2) *
            (1 + magnetic ^ 2 * mass ^ 2 * polarX.1 ^ 2) =
        0 ^ 2 + (magnetic ^ 2 * (1 - polarX.1 ^ 2)) *
          (1 + magnetic ^ 2 * mass ^ 2 * polarX.1 ^ 2) := by rw [hy]; ring
      _ = 0 := by rw [hbase]; ring

theorem magneticSq_mul_one_sub_sq_eq_zero_iff
    (magnetic polarX : ℝ) :
    magnetic ^ 2 * (1 - polarX ^ 2) = 0 ↔
      magnetic = 0 ∨ polarX = -1 ∨ polarX = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hB | hx
    · exact Or.inl ((sq_eq_zero_iff).mp hB)
    · right
      have hfactor : (1 - polarX) * (1 + polarX) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hright | hleft
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  · rintro (hB | hx | hx)
    · simp [hB]
    · simp [hx]
    · simp [hx]

theorem one_sub_polarSq_eq_zero_iff (polarX : ℝ) :
    1 - polarX ^ 2 = 0 ↔ polarX = -1 ∨ polarX = 1 := by
  have hfactor : 1 - polarX ^ 2 = (1 - polarX) * (1 + polarX) := by ring
  rw [hfactor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · right; linarith
    · left; linarith

/-- The angular Schwarzschild--BR coefficient degenerates only on the two polar axes. -/
theorem schwarzschildBRPolarFactor_eq_zero_iff
    (mass magnetic polarX : ℝ) :
    schwarzschildBRPolarFactor mass magnetic polarX = 0 ↔
      polarX = -1 ∨ polarX = 1 := by
  unfold schwarzschildBRPolarFactor
  have hpos : 0 < 1 + magnetic ^ 2 * mass ^ 2 * polarX ^ 2 := by positivity
  rw [mul_eq_zero, one_sub_polarSq_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim ((ne_of_gt hpos) h)
  · intro h
    exact Or.inl h

/-- Full Schwarzschild--BR conformal zero locus on the physical polar interval. -/
theorem schwarzschildBRReciprocalConformalSq_zero_classification
    (mass magnetic reciprocalRadius : ℝ) (polarX : Set.Icc (-1 : ℝ) 1) :
    schwarzschildBRReciprocalConformalSq mass magnetic polarX.1 reciprocalRadius = 0 ↔
      (magnetic = 0 ∧ reciprocalRadius = 0) ∨
      (polarX.1 = -1 ∧ reciprocalRadius = 0) ∨
      (polarX.1 = 1 ∧ reciprocalRadius = 0) := by
  rw [schwarzschildBRReciprocalConformalSq_eq_zero_iff,
    magneticSq_mul_one_sub_sq_eq_zero_iff]
  constructor
  · rintro ⟨hy, hB | hx | hx⟩
    · exact Or.inl ⟨hB, by simpa [hB] using hy⟩
    · exact Or.inr <| Or.inl ⟨hx, by simpa [hx] using hy⟩
    · exact Or.inr <| Or.inr ⟨hx, by simpa [hx] using hy⟩
  · rintro (⟨hB, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact ⟨by simp [hB, hy], Or.inl hB⟩
    · exact ⟨by simp [hx, hy], Or.inr <| Or.inl hx⟩
    · exact ⟨by simp [hx, hy], Or.inr <| Or.inr hx⟩

theorem schwarzschildBRReciprocalConformalSq_seam
    (mass magnetic polarX : ℝ) :
    schwarzschildBRReciprocalConformalSq mass magnetic polarX 0 =
      magnetic ^ 2 * (1 - polarX ^ 2) *
        (1 + magnetic ^ 2 * mass ^ 2) := by
  rw [schwarzschildBRReciprocalConformalSq_completeSquare]
  ring

theorem schwarzschildBRReciprocalWeylFactor_eq_zero_iff
    (mass magnetic polarX reciprocalRadius : ℝ) :
    schwarzschildBRReciprocalWeylFactor mass magnetic polarX reciprocalRadius = 0 ↔
      reciprocalRadius = magnetic ^ 2 * mass * (1 - polarX ^ 2) := by
  unfold schwarzschildBRReciprocalWeylFactor
  constructor <;> intro h <;> linarith

/-- Every reciprocal Schwarzschild--BR coefficient displayed in the paper is smooth through `y=0`. -/
theorem contDiff_schwarzschildBRReciprocalPotentials (mass magnetic polarX : ℝ) :
    ContDiff ℝ ∞ (fun y => schwarzschildBRReciprocalWeight mass magnetic y) ∧
    ContDiff ℝ ∞ (fun y => schwarzschildBRReciprocalLapse mass magnetic y) ∧
    ContDiff ℝ ∞ (fun y => schwarzschildBRReciprocalConformalSq mass magnetic polarX y) ∧
    ContDiff ℝ ∞ (fun y => schwarzschildBRReciprocalWeylFactor mass magnetic polarX y) := by
  simp only [schwarzschildBRReciprocalWeight, schwarzschildBRReciprocalLapse,
    schwarzschildBRReciprocalConformalSq, schwarzschildBRReciprocalWeylFactor]
  constructor
  · fun_prop
  constructor
  · fun_prop
  constructor <;> fun_prop

/-! ## Generic Kerr--Newman--BR reciprocal chart -/

/-- Generic rotating radial dressing factor `I`. -/
def kerrNewmanBRRadialWeight (twist magnetic radius : ℝ) : ℝ :=
  (1 + twist * magnetic * radius) ^ 2 + magnetic ^ 2 * radius ^ 2

/-- Coefficient of `r^2` in the paper's generalized radial polynomial. -/
def kerrNewmanBRRadialCoefficient (spin charge twist : ℝ) : ℝ :=
  1 + twist ^ 2 - charge ^ 2 / spin ^ 2

/-- Generalized Kerr--Newman--BR horizon polynomial `Delta`. -/
def kerrNewmanBRDelta (mass spin charge twist radius : ℝ) : ℝ :=
  (1 + twist ^ 2) * spin ^ 2 - 2 * mass * radius +
    kerrNewmanBRRadialCoefficient spin charge twist * radius ^ 2

/-- Dressed radial function `Q = I Delta`. -/
def kerrNewmanBRQ (mass spin charge twist magnetic radius : ℝ) : ℝ :=
  kerrNewmanBRRadialWeight twist magnetic radius *
    kerrNewmanBRDelta mass spin charge twist radius

/-- Ring-singularity carrier `rho^2` in `x = cos(theta)` coordinates. -/
def kerrNewmanBRRhoSq (spin radius polarX : ℝ) : ℝ :=
  radius ^ 2 + spin ^ 2 * polarX ^ 2

/-- Reciprocal extension of `y^2 I(1/y)`. -/
def kerrNewmanBRReciprocalWeight (twist magnetic reciprocalRadius : ℝ) : ℝ :=
  (reciprocalRadius + twist * magnetic) ^ 2 + magnetic ^ 2

/-- Reciprocal extension of `y^2 Delta(1/y)`. -/
def kerrNewmanBRReciprocalDelta
    (mass spin charge twist reciprocalRadius : ℝ) : ℝ :=
  (1 + twist ^ 2) * spin ^ 2 * reciprocalRadius ^ 2 -
    2 * mass * reciprocalRadius + kerrNewmanBRRadialCoefficient spin charge twist

/-- Reciprocal conformal potential `y^2 Omega^2(1/y)`. -/
def kerrNewmanBRReciprocalConformalSq
    (mass spin charge twist magnetic polarX reciprocalRadius : ℝ) : ℝ :=
  kerrNewmanBRReciprocalWeight twist magnetic reciprocalRadius -
    magnetic ^ 2 *
      kerrNewmanBRReciprocalDelta mass spin charge twist reciprocalRadius * polarX ^ 2

/-- Reciprocal extension of the dressed radial function. -/
def kerrNewmanBRReciprocalQ
    (mass spin charge twist magnetic reciprocalRadius : ℝ) : ℝ :=
  kerrNewmanBRReciprocalWeight twist magnetic reciprocalRadius *
    kerrNewmanBRReciprocalDelta mass spin charge twist reciprocalRadius

/-- Reciprocal ring carrier `y^2 rho^2(1/y)`. -/
def kerrNewmanBRReciprocalRhoSq (spin polarX reciprocalRadius : ℝ) : ℝ :=
  1 + spin ^ 2 * polarX ^ 2 * reciprocalRadius ^ 2

theorem kerrNewmanBRRadialWeight_eq_sum_sq (twist magnetic radius : ℝ) :
    kerrNewmanBRRadialWeight twist magnetic radius =
      (1 + twist * magnetic * radius) ^ 2 + (magnetic * radius) ^ 2 := by
  simp only [kerrNewmanBRRadialWeight]
  ring

/-- Generic BR radial dressing is strictly positive for every real parameter tuple. -/
theorem kerrNewmanBRRadialWeight_pos (twist magnetic radius : ℝ) :
    0 < kerrNewmanBRRadialWeight twist magnetic radius := by
  rw [kerrNewmanBRRadialWeight_eq_sum_sq]
  by_cases hB : magnetic = 0
  · simp [hB]
  by_cases hr : radius = 0
  · simp [hr]
  have hBr : magnetic * radius ≠ 0 := mul_ne_zero hB hr
  have hs : 0 < (magnetic * radius) ^ 2 := sq_pos_of_ne_zero hBr
  nlinarith [sq_nonneg (1 + twist * magnetic * radius)]

/-- The magnetic dressing changes no algebraic horizon: `Q=0` exactly when `Delta=0`. -/
theorem kerrNewmanBRQ_eq_zero_iff (mass spin charge twist magnetic radius : ℝ) :
    kerrNewmanBRQ mass spin charge twist magnetic radius = 0 ↔
      kerrNewmanBRDelta mass spin charge twist radius = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hI | hDelta
    · exact False.elim ((ne_of_gt (kerrNewmanBRRadialWeight_pos twist magnetic radius)) hI)
    · exact hDelta
  · intro h
    simp [kerrNewmanBRQ, h]

/-- Denominator-cleared complete-square identity for the generalized horizon polynomial. -/
theorem kerrNewmanBRDelta_completeSquare_cleared
    (mass spin charge twist radius : ℝ) :
    kerrNewmanBRRadialCoefficient spin charge twist *
        kerrNewmanBRDelta mass spin charge twist radius =
      (kerrNewmanBRRadialCoefficient spin charge twist * radius - mass) ^ 2 -
        (mass ^ 2 - kerrNewmanBRRadialCoefficient spin charge twist *
          (1 + twist ^ 2) * spin ^ 2) := by
  simp only [kerrNewmanBRDelta]
  ring

theorem kerrNewmanBRDelta_cleared_eq_zero_iff
    (mass spin charge twist radius : ℝ) :
    kerrNewmanBRRadialCoefficient spin charge twist *
        kerrNewmanBRDelta mass spin charge twist radius = 0 ↔
      (kerrNewmanBRRadialCoefficient spin charge twist * radius - mass) ^ 2 =
        mass ^ 2 - kerrNewmanBRRadialCoefficient spin charge twist *
          (1 + twist ^ 2) * spin ^ 2 := by
  rw [kerrNewmanBRDelta_completeSquare_cleared]
  exact sub_eq_zero

theorem kerrNewmanBRRhoSq_eq_zero_iff (spin radius polarX : ℝ) :
    kerrNewmanBRRhoSq spin radius polarX = 0 ↔
      radius = 0 ∧ spin * polarX = 0 := by
  rw [show kerrNewmanBRRhoSq spin radius polarX = radius ^ 2 + (spin * polarX) ^ 2 by
    simp [kerrNewmanBRRhoSq]; ring]
  constructor
  · intro h
    have hr : radius ^ 2 = 0 := by nlinarith [sq_nonneg radius, sq_nonneg (spin * polarX)]
    have hx : (spin * polarX) ^ 2 = 0 := by
      nlinarith [sq_nonneg radius, sq_nonneg (spin * polarX)]
    exact ⟨(sq_eq_zero_iff.mp hr), (sq_eq_zero_iff.mp hx)⟩
  · rintro ⟨hr, hx⟩
    simp [hr, hx]

theorem kerrNewmanBRRhoSq_ring_classification (spin radius polarX : ℝ) :
    kerrNewmanBRRhoSq spin radius polarX = 0 ↔
      radius = 0 ∧ (spin = 0 ∨ polarX = 0) := by
  rw [kerrNewmanBRRhoSq_eq_zero_iff, mul_eq_zero]

/-- Reciprocal radius removes the apparent ring carrier at infinity: its extension is at least one. -/
theorem kerrNewmanBRReciprocalRhoSq_ge_one (spin polarX reciprocalRadius : ℝ) :
    1 ≤ kerrNewmanBRReciprocalRhoSq spin polarX reciprocalRadius := by
  simp only [kerrNewmanBRReciprocalRhoSq]
  nlinarith [sq_nonneg (spin * polarX * reciprocalRadius)]

theorem kerrNewmanBRReciprocalRhoSq_pos (spin polarX reciprocalRadius : ℝ) :
    0 < kerrNewmanBRReciprocalRhoSq spin polarX reciprocalRadius :=
  lt_of_lt_of_le zero_lt_one (kerrNewmanBRReciprocalRhoSq_ge_one spin polarX reciprocalRadius)

theorem kerrNewmanBRReciprocalWeight_eq_zero_iff
    (twist magnetic reciprocalRadius : ℝ) :
    kerrNewmanBRReciprocalWeight twist magnetic reciprocalRadius = 0 ↔
      magnetic = 0 ∧ reciprocalRadius = 0 := by
  unfold kerrNewmanBRReciprocalWeight
  constructor
  · intro h
    have hBsq : magnetic ^ 2 = 0 := by
      nlinarith [sq_nonneg (reciprocalRadius + twist * magnetic), sq_nonneg magnetic]
    have hfirst : (reciprocalRadius + twist * magnetic) ^ 2 = 0 := by
      nlinarith [sq_nonneg (reciprocalRadius + twist * magnetic), sq_nonneg magnetic]
    have hB : magnetic = 0 := sq_eq_zero_iff.mp hBsq
    exact ⟨hB, by simpa [hB] using sq_eq_zero_iff.mp hfirst⟩
  · rintro ⟨hB, hy⟩
    simp [hB, hy]

theorem kerrNewmanBRReciprocalWeight_seam (twist magnetic : ℝ) :
    kerrNewmanBRReciprocalWeight twist magnetic 0 =
      magnetic ^ 2 * (1 + twist ^ 2) := by
  simp [kerrNewmanBRReciprocalWeight]
  ring

theorem kerrNewmanBRReciprocalQ_eq_zero_iff
    (mass spin charge twist magnetic reciprocalRadius : ℝ) :
    kerrNewmanBRReciprocalQ mass spin charge twist magnetic reciprocalRadius = 0 ↔
      (magnetic = 0 ∧ reciprocalRadius = 0) ∨
        kerrNewmanBRReciprocalDelta mass spin charge twist reciprocalRadius = 0 := by
  unfold kerrNewmanBRReciprocalQ
  rw [mul_eq_zero, kerrNewmanBRReciprocalWeight_eq_zero_iff]

theorem kerrNewmanBRReciprocalConformalSq_equator
    (mass spin charge twist magnetic reciprocalRadius : ℝ) :
    kerrNewmanBRReciprocalConformalSq
      mass spin charge twist magnetic 0 reciprocalRadius =
        kerrNewmanBRReciprocalWeight twist magnetic reciprocalRadius := by
  simp [kerrNewmanBRReciprocalConformalSq]

theorem kerrNewmanBRReciprocalConformalSq_equator_eq_zero_iff
    (mass spin charge twist magnetic reciprocalRadius : ℝ) :
    kerrNewmanBRReciprocalConformalSq
      mass spin charge twist magnetic 0 reciprocalRadius = 0 ↔
        magnetic = 0 ∧ reciprocalRadius = 0 := by
  rw [kerrNewmanBRReciprocalConformalSq_equator,
    kerrNewmanBRReciprocalWeight_eq_zero_iff]

/-- Exact generic conformal factor on the reciprocal seam. -/
theorem kerrNewmanBRReciprocalConformalSq_seam
    (mass spin charge twist magnetic polarX : ℝ) :
    kerrNewmanBRReciprocalConformalSq
        mass spin charge twist magnetic polarX 0 =
      magnetic ^ 2 *
        ((1 + twist ^ 2) * (1 - polarX ^ 2) +
          (charge ^ 2 / spin ^ 2) * polarX ^ 2) := by
  simp [kerrNewmanBRReciprocalConformalSq, kerrNewmanBRReciprocalWeight,
    kerrNewmanBRReciprocalDelta, kerrNewmanBRRadialCoefficient]
  ring

theorem kerrNewmanBRReciprocalConformalSq_polarSeam
    (mass spin charge twist magnetic : ℝ) :
    kerrNewmanBRReciprocalConformalSq
        mass spin charge twist magnetic 1 0 =
      magnetic ^ 2 * (charge ^ 2 / spin ^ 2) := by
  rw [kerrNewmanBRReciprocalConformalSq_seam]
  ring

theorem kerrNewmanBRRadialWeight_reciprocalClearing
    (twist magnetic : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ 2 * kerrNewmanBRRadialWeight twist magnetic y.1⁻¹ =
      kerrNewmanBRReciprocalWeight twist magnetic y.1 := by
  unfold kerrNewmanBRRadialWeight kerrNewmanBRReciprocalWeight
  field_simp [y.2]

theorem kerrNewmanBRDelta_reciprocalClearing
    (mass spin charge twist : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ 2 * kerrNewmanBRDelta mass spin charge twist y.1⁻¹ =
      kerrNewmanBRReciprocalDelta mass spin charge twist y.1 := by
  unfold kerrNewmanBRDelta kerrNewmanBRReciprocalDelta
  field_simp [y.2]

theorem kerrNewmanBRConformal_reciprocalClearing
    (mass spin charge twist magnetic polarX : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ 2 *
        (kerrNewmanBRRadialWeight twist magnetic y.1⁻¹ -
          magnetic ^ 2 * kerrNewmanBRDelta mass spin charge twist y.1⁻¹ * polarX ^ 2) =
      kerrNewmanBRReciprocalConformalSq
        mass spin charge twist magnetic polarX y.1 := by
  rw [mul_sub, kerrNewmanBRRadialWeight_reciprocalClearing]
  rw [show y.1 ^ 2 *
      (magnetic ^ 2 * kerrNewmanBRDelta mass spin charge twist y.1⁻¹ * polarX ^ 2) =
      magnetic ^ 2 *
        (y.1 ^ 2 * kerrNewmanBRDelta mass spin charge twist y.1⁻¹) * polarX ^ 2 by ring]
  rw [kerrNewmanBRDelta_reciprocalClearing]
  rfl

theorem kerrNewmanBRRhoSq_reciprocalClearing
    (spin polarX : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ 2 * kerrNewmanBRRhoSq spin y.1⁻¹ polarX =
      kerrNewmanBRReciprocalRhoSq spin polarX y.1 := by
  unfold kerrNewmanBRRhoSq kerrNewmanBRReciprocalRhoSq
  field_simp [y.2]

/-- All generic reciprocal potentials are smooth through the seam `y=0`. -/
theorem contDiff_kerrNewmanBRReciprocalPotentials
    (mass spin charge twist magnetic polarX : ℝ) :
    ContDiff ℝ ∞ (fun y => kerrNewmanBRReciprocalWeight twist magnetic y) ∧
    ContDiff ℝ ∞ (fun y => kerrNewmanBRReciprocalDelta mass spin charge twist y) ∧
    ContDiff ℝ ∞ (fun y =>
      kerrNewmanBRReciprocalConformalSq mass spin charge twist magnetic polarX y) ∧
    ContDiff ℝ ∞ (fun y => kerrNewmanBRReciprocalRhoSq spin polarX y) := by
  simp only [kerrNewmanBRReciprocalWeight, kerrNewmanBRReciprocalDelta,
    kerrNewmanBRReciprocalConformalSq, kerrNewmanBRReciprocalRhoSq,
    kerrNewmanBRRadialCoefficient]
  constructor
  · fun_prop
  constructor
  · fun_prop
  constructor <;> fun_prop

/-! ## Existing Kerr--Newman corpus bridges -/

theorem kerrNewmanBRRhoSq_eq_kerrNewmanSigma (spin radius polar : ℝ) :
    kerrNewmanBRRhoSq spin radius (Real.cos polar) =
      kerrNewmanSigma spin radius polar := by
  rfl

theorem kerrNewmanBRDelta_untwistedUncharged_eq_kerrDelta
    (mass spin radius : ℝ) :
    kerrNewmanBRDelta mass spin 0 0 radius =
      kerrNewmanDelta mass spin 0 radius := by
  simp [kerrNewmanBRDelta, kerrNewmanBRRadialCoefficient, kerrNewmanDelta]
  ring

theorem kerrNewmanBRQ_zeroField_untwistedUncharged_eq_kerrDelta
    (mass spin radius : ℝ) :
    kerrNewmanBRQ mass spin 0 0 0 radius =
      kerrNewmanDelta mass spin 0 radius := by
  simp [kerrNewmanBRQ, kerrNewmanBRRadialWeight,
    kerrNewmanBRDelta_untwistedUncharged_eq_kerrDelta]

theorem kerrNewmanBRDelta_untwistedUncharged_completeSquare
    (mass spin radius : ℝ) :
    kerrNewmanBRDelta mass spin 0 0 radius =
      (radius - mass) ^ 2 - (mass ^ 2 - spin ^ 2) := by
  rw [kerrNewmanBRDelta_untwistedUncharged_eq_kerrDelta,
    kerrNewmanDelta_completeSquare]
  ring

theorem schwarzschildBRRadialWeight_eq_genericSpecialization
    (mass magnetic radius : ℝ) :
    schwarzschildBRRadialWeight mass magnetic radius =
      kerrNewmanBRRadialWeight (-magnetic * mass) magnetic radius := by
  simp [schwarzschildBRRadialWeight, kerrNewmanBRRadialWeight]
  ring

/-! ## Branch matching and compactified Kruskal coordinates -/

/-- Integration constant required to match positive and negative radial branches. -/
def kerrNewmanBRTortoiseNegativeConstant
    (openCoefficient positiveConstant : ℝ) : ℝ :=
  openCoefficient * Real.pi + positiveConstant

theorem kerrNewmanBRTortoiseNegativeConstant_sub_positive
    (openCoefficient positiveConstant : ℝ) :
    kerrNewmanBRTortoiseNegativeConstant openCoefficient positiveConstant -
      positiveConstant = openCoefficient * Real.pi := by
  simp [kerrNewmanBRTortoiseNegativeConstant]

/-- Kruskal-like spatial coordinate used for either radial branch. -/
def kerrNewmanBRKruskalU
    (time tortoise horizonScale orientation : ℝ) : ℝ :=
  (Real.exp ((time + tortoise) / (2 * horizonScale)) -
    orientation * Real.exp (-(time - tortoise) / (2 * horizonScale))) / 2

/-- Kruskal-like temporal coordinate used for either radial branch. -/
def kerrNewmanBRKruskalV
    (time tortoise horizonScale orientation : ℝ) : ℝ :=
  (Real.exp ((time + tortoise) / (2 * horizonScale)) +
    orientation * Real.exp (-(time - tortoise) / (2 * horizonScale))) / 2

theorem kerrNewmanBRKruskalV_add_U
    (time tortoise horizonScale orientation : ℝ) :
    kerrNewmanBRKruskalV time tortoise horizonScale orientation +
      kerrNewmanBRKruskalU time tortoise horizonScale orientation =
        Real.exp ((time + tortoise) / (2 * horizonScale)) := by
  simp [kerrNewmanBRKruskalU, kerrNewmanBRKruskalV]
  ring

theorem kerrNewmanBRKruskalV_sub_U
    (time tortoise horizonScale orientation : ℝ) :
    kerrNewmanBRKruskalV time tortoise horizonScale orientation -
      kerrNewmanBRKruskalU time tortoise horizonScale orientation =
        orientation * Real.exp (-(time - tortoise) / (2 * horizonScale)) := by
  simp [kerrNewmanBRKruskalU, kerrNewmanBRKruskalV]
  ring

theorem kerrNewmanBRKruskalV_add_U_pos
    (time tortoise horizonScale orientation : ℝ) :
    0 < kerrNewmanBRKruskalV time tortoise horizonScale orientation +
      kerrNewmanBRKruskalU time tortoise horizonScale orientation := by
  rw [kerrNewmanBRKruskalV_add_U]
  exact Real.exp_pos _

/-- Hyperbolic product invariant of the Kruskal-like chart. -/
theorem kerrNewmanBRKruskalV_sq_sub_U_sq
    (time tortoise horizonScale orientation : ℝ) :
    kerrNewmanBRKruskalV time tortoise horizonScale orientation ^ 2 -
      kerrNewmanBRKruskalU time tortoise horizonScale orientation ^ 2 =
        orientation * Real.exp (tortoise / horizonScale) := by
  rw [sq_sub_sq, kerrNewmanBRKruskalV_sub_U, kerrNewmanBRKruskalV_add_U]
  calc
    Real.exp ((time + tortoise) / (2 * horizonScale)) *
        (orientation * Real.exp (-(time - tortoise) / (2 * horizonScale))) =
      orientation *
        (Real.exp ((time + tortoise) / (2 * horizonScale)) *
          Real.exp (-(time - tortoise) / (2 * horizonScale))) := by ring
    _ = orientation * Real.exp
        ((time + tortoise) / (2 * horizonScale) +
          (-(time - tortoise) / (2 * horizonScale))) := by rw [Real.exp_add]
    _ = orientation * Real.exp (tortoise / horizonScale) := by
      congr 2
      ring

theorem kerrNewmanBRKruskalV_sq_sub_U_sq_eq_zero_iff
    (time tortoise horizonScale orientation : ℝ) :
    kerrNewmanBRKruskalV time tortoise horizonScale orientation ^ 2 -
      kerrNewmanBRKruskalU time tortoise horizonScale orientation ^ 2 = 0 ↔
        orientation = 0 := by
  rw [kerrNewmanBRKruskalV_sq_sub_U_sq, mul_eq_zero]
  exact or_iff_left (Real.exp_ne_zero _)

/-- Compactified time coordinate. -/
def kerrNewmanBRCompactEta (U V : ℝ) : ℝ :=
  Real.arctan (V + U) + Real.arctan (V - U)

/-- Compactified radial coordinate. -/
def kerrNewmanBRCompactChi (U V : ℝ) : ℝ :=
  Real.arctan (V + U) - Real.arctan (V - U)

theorem kerrNewmanBRCompactEta_add_Chi (U V : ℝ) :
    kerrNewmanBRCompactEta U V + kerrNewmanBRCompactChi U V =
      2 * Real.arctan (V + U) := by
  simp [kerrNewmanBRCompactEta, kerrNewmanBRCompactChi]
  ring

theorem kerrNewmanBRCompactEta_sub_Chi (U V : ℝ) :
    kerrNewmanBRCompactEta U V - kerrNewmanBRCompactChi U V =
      2 * Real.arctan (V - U) := by
  simp [kerrNewmanBRCompactEta, kerrNewmanBRCompactChi]
  ring

theorem kerrNewmanBRCompact_tan_half_add (U V : ℝ) :
    Real.tan ((kerrNewmanBRCompactEta U V + kerrNewmanBRCompactChi U V) / 2) =
      V + U := by
  rw [kerrNewmanBRCompactEta_add_Chi]
  rw [show 2 * Real.arctan (V + U) / 2 = Real.arctan (V + U) by ring]
  exact Real.tan_arctan (V + U)

theorem kerrNewmanBRCompact_tan_half_sub (U V : ℝ) :
    Real.tan ((kerrNewmanBRCompactEta U V - kerrNewmanBRCompactChi U V) / 2) =
      V - U := by
  rw [kerrNewmanBRCompactEta_sub_Chi]
  rw [show 2 * Real.arctan (V - U) / 2 = Real.arctan (V - U) by ring]
  exact Real.tan_arctan (V - U)

theorem kerrNewmanBRCompact_recover_U (U V : ℝ) :
    (Real.tan ((kerrNewmanBRCompactEta U V + kerrNewmanBRCompactChi U V) / 2) -
      Real.tan ((kerrNewmanBRCompactEta U V - kerrNewmanBRCompactChi U V) / 2)) / 2 = U := by
  rw [kerrNewmanBRCompact_tan_half_add, kerrNewmanBRCompact_tan_half_sub]
  ring

theorem kerrNewmanBRCompact_recover_V (U V : ℝ) :
    (Real.tan ((kerrNewmanBRCompactEta U V + kerrNewmanBRCompactChi U V) / 2) +
      Real.tan ((kerrNewmanBRCompactEta U V - kerrNewmanBRCompactChi U V) / 2)) / 2 = V := by
  rw [kerrNewmanBRCompact_tan_half_add, kerrNewmanBRCompact_tan_half_sub]
  ring

/-- Carter--Penrose null combinations lie in the open compact interval `(-pi, pi)`. -/
theorem kerrNewmanBRCompact_nullBounds (U V : ℝ) :
    -Real.pi < kerrNewmanBRCompactEta U V + kerrNewmanBRCompactChi U V ∧
      kerrNewmanBRCompactEta U V + kerrNewmanBRCompactChi U V < Real.pi ∧
      -Real.pi < kerrNewmanBRCompactEta U V - kerrNewmanBRCompactChi U V ∧
      kerrNewmanBRCompactEta U V - kerrNewmanBRCompactChi U V < Real.pi := by
  rw [kerrNewmanBRCompactEta_add_Chi, kerrNewmanBRCompactEta_sub_Chi]
  have hpa := Real.arctan_lt_pi_div_two (V + U)
  have hna := Real.neg_pi_div_two_lt_arctan (V + U)
  have hps := Real.arctan_lt_pi_div_two (V - U)
  have hns := Real.neg_pi_div_two_lt_arctan (V - U)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Radial patch reflection preserves compactified time. -/
theorem kerrNewmanBRCompactEta_reflectRadius (U V : ℝ) :
    kerrNewmanBRCompactEta (-U) V = kerrNewmanBRCompactEta U V := by
  unfold kerrNewmanBRCompactEta
  rw [show V + -U = V - U by ring, show V - -U = V + U by ring]
  ac_rfl

/-- Radial patch reflection reverses compactified radius. -/
theorem kerrNewmanBRCompactChi_reflectRadius (U V : ℝ) :
    kerrNewmanBRCompactChi (-U) V = -kerrNewmanBRCompactChi U V := by
  unfold kerrNewmanBRCompactChi
  rw [show V + -U = V - U by ring, show V - -U = V + U by ring]
  ring

end

end GaloisForLFunctions.HTGeometry
