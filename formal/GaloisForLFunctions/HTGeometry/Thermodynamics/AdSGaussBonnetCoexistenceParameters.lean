import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetBoundary
import GaloisForLFunctions.HTGeometry.CPVThermalRadiation

/-!
# Constructive parameters for the full coexistence surface

The ratio of the two radii lies in `(0,1)`. Their squared large radius
interpolates between the neutral and Einstein edges. The resulting
coupling, charge and temperature are physical without any assumed
coexistence or sign conditions.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def coexistenceN (k : ℝ) : ℝ := k ^ 2 + 3 * k + 1
def coexistenceD (k : ℝ) : ℝ := k ^ 4 + 3 * k ^ 3 + 7 * k ^ 2 + 3 * k + 1
def coexistenceJ (k : ℝ) : ℝ := k ^ 2 + 4 * k + 1
def coexistenceK (k : ℝ) : ℝ := k ^ 2 + k + 1

theorem coexistence_polynomials_pos (τ : ℝ) :
    0 < coexistenceN (CPV.thermalRatio τ) ∧ 0 < coexistenceD (CPV.thermalRatio τ) ∧
      0 < coexistenceJ (CPV.thermalRatio τ) ∧ 0 < coexistenceK (CPV.thermalRatio τ) := by
  have hk := CPV.thermalRatio_pos τ
  unfold coexistenceN coexistenceD coexistenceJ coexistenceK
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem coexistence_spread (k : ℝ) :
    coexistenceN k * coexistenceJ k - coexistenceD k = k * (4 * k ^ 2 + 7 * k + 4) := by
  unfold coexistenceN coexistenceJ coexistenceD
  ring

def coexistenceSquare (τ θ : ℝ) : ℝ :=
  (1 - Real.sin θ ^ 2) / coexistenceJ (CPV.thermalRatio τ) +
    Real.sin θ ^ 2 * coexistenceN (CPV.thermalRatio τ) / coexistenceD (CPV.thermalRatio τ)

theorem coexistenceSquare_lower_gap (τ θ : ℝ) :
    coexistenceSquare τ θ - 1 / coexistenceJ (CPV.thermalRatio τ) =
      Real.sin θ ^ 2 * (coexistenceN (CPV.thermalRatio τ) * coexistenceJ (CPV.thermalRatio τ) -
        coexistenceD (CPV.thermalRatio τ)) /
      (coexistenceJ (CPV.thermalRatio τ) * coexistenceD (CPV.thermalRatio τ)) := by
  unfold coexistenceSquare
  have hp := coexistence_polynomials_pos τ
  field_simp [hp.2.1.ne', hp.2.2.1.ne']
  ring

theorem coexistenceSquare_upper_gap (τ θ : ℝ) :
    coexistenceN (CPV.thermalRatio τ) / coexistenceD (CPV.thermalRatio τ) - coexistenceSquare τ θ =
      (1 - Real.sin θ ^ 2) *
        (coexistenceN (CPV.thermalRatio τ) * coexistenceJ (CPV.thermalRatio τ) -
          coexistenceD (CPV.thermalRatio τ)) /
        (coexistenceJ (CPV.thermalRatio τ) * coexistenceD (CPV.thermalRatio τ)) := by
  unfold coexistenceSquare
  have hp := coexistence_polynomials_pos τ
  field_simp [hp.2.1.ne', hp.2.2.1.ne']
  ring

theorem coexistenceSquare_bounds (τ θ : ℝ) :
    1 / coexistenceJ (CPV.thermalRatio τ) ≤ coexistenceSquare τ θ ∧
      coexistenceSquare τ θ ≤ coexistenceN (CPV.thermalRatio τ) / coexistenceD (CPV.thermalRatio τ) := by
  have hp := coexistence_polynomials_pos τ
  have hD := hp.2.1
  have hJ := hp.2.2.1
  have hk := CPV.thermalRatio_pos τ
  have hw : 0 ≤ 1 - Real.sin θ ^ 2 := by
    nlinarith only [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  constructor
  · apply sub_nonneg.mp
    rw [coexistenceSquare_lower_gap, coexistence_spread]
    positivity
  · apply sub_nonneg.mp
    rw [coexistenceSquare_upper_gap, coexistence_spread]
    positivity

theorem coexistenceSquare_pos (τ θ : ℝ) : 0 < coexistenceSquare τ θ :=
  (div_pos (by norm_num) (coexistence_polynomials_pos τ).2.2.1).trans_le
    (coexistenceSquare_bounds τ θ).1

def coexistenceRadius (τ θ : ℝ) : ℝ := Real.sqrt (coexistenceSquare τ θ)

theorem coexistenceRadius_pos (τ θ : ℝ) : 0 < coexistenceRadius τ θ :=
  Real.sqrt_pos.mpr (coexistenceSquare_pos τ θ)

theorem coexistenceRadius_sq (τ θ : ℝ) : coexistenceRadius τ θ ^ 2 = coexistenceSquare τ θ :=
  Real.sq_sqrt (coexistenceSquare_pos τ θ).le

def coexistenceSum (τ θ : ℝ) : ℝ := (CPV.thermalRatio τ + 1) * coexistenceRadius τ θ
def coexistenceProduct (τ θ : ℝ) : ℝ := CPV.thermalRatio τ * coexistenceRadius τ θ ^ 2
def coexistenceCoupling (τ θ : ℝ) : ℝ :=
  coexistenceRadius τ θ ^ 2 *
    (coexistenceN (CPV.thermalRatio τ) - coexistenceD (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2) /
    (6 * (3 * coexistenceK (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 + 1))

theorem coexistenceSum_pos (τ θ : ℝ) : 0 < coexistenceSum τ θ := by
  unfold coexistenceSum
  have hk := CPV.thermalRatio_pos τ
  have hr := coexistenceRadius_pos τ θ
  positivity

theorem coexistenceProduct_pos (τ θ : ℝ) : 0 < coexistenceProduct τ θ := by
  unfold coexistenceProduct
  have hk := CPV.thermalRatio_pos τ
  have hr := coexistenceRadius_pos τ θ
  positivity

theorem coexistenceCoupling_nonneg (τ θ : ℝ) : 0 ≤ coexistenceCoupling τ θ := by
  have hp := coexistence_polynomials_pos τ
  have hK := hp.2.2.2
  have hu := (coexistenceSquare_bounds τ θ).2
  have hm := mul_le_mul_of_nonneg_left hu hp.2.1.le
  have hc : coexistenceD (CPV.thermalRatio τ) *
      (coexistenceN (CPV.thermalRatio τ) / coexistenceD (CPV.thermalRatio τ)) =
      coexistenceN (CPV.thermalRatio τ) := by field_simp [hp.2.1.ne']
  rw [hc, ← coexistenceRadius_sq] at hm
  unfold coexistenceCoupling
  have hn : 0 ≤ coexistenceN (CPV.thermalRatio τ) -
      coexistenceD (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 := sub_nonneg.mpr hm
  positivity

/-- The charge changes sign exactly at the neutral-radius edge. -/
theorem coexistenceProduct_sub_six_coupling (τ θ : ℝ) :
    coexistenceProduct τ θ - 6 * coexistenceCoupling τ θ =
      coexistenceRadius τ θ ^ 2 * (CPV.thermalRatio τ + 1) ^ 2 *
        (coexistenceJ (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 - 1) /
        (3 * coexistenceK (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 + 1) := by
  have hp := (coexistence_polynomials_pos τ).2.2.2
  have hd : 3 * coexistenceK (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 + 1 ≠ 0 := by positivity
  unfold coexistenceProduct coexistenceCoupling
  field_simp [hd]
  unfold coexistenceN coexistenceD coexistenceJ coexistenceK
  ring

theorem coexistence_lower_radius_nonneg (τ θ : ℝ) :
    0 ≤ coexistenceJ (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 - 1 := by
  have hp := coexistence_polynomials_pos τ
  have hl := (coexistenceSquare_bounds τ θ).1
  have hm := mul_le_mul_of_nonneg_left hl hp.2.2.1.le
  have hc : coexistenceJ (CPV.thermalRatio τ) * (1 / coexistenceJ (CPV.thermalRatio τ)) = 1 := by
    field_simp [hp.2.2.1.ne']
  rw [hc, ← coexistenceRadius_sq] at hm
  exact sub_nonneg.mpr hm

theorem coexistenceProduct_sub_six_coupling_nonneg (τ θ : ℝ) :
    0 ≤ coexistenceProduct τ θ - 6 * coexistenceCoupling τ θ := by
  have hK := (coexistence_polynomials_pos τ).2.2.2
  have hn := coexistence_lower_radius_nonneg τ θ
  rw [coexistenceProduct_sub_six_coupling]
  positivity

/-- Every split-radius coexistence coupling lies strictly below the neutral critical threshold. -/
theorem coexistenceCoupling_lt_threshold (τ θ : ℝ) : coexistenceCoupling τ θ < 1 / 36 := by
  have hp := coexistence_polynomials_pos τ
  have hk := CPV.thermalRatio_pos τ
  have hJ := hp.2.2.1
  have hD := hp.2.1
  have hK := hp.2.2.2
  have hpoly : coexistenceD (CPV.thermalRatio τ) - CPV.thermalRatio τ * coexistenceJ (CPV.thermalRatio τ) =
      CPV.thermalRatio τ ^ 4 + 2 * CPV.thermalRatio τ ^ 3 + 3 * CPV.thermalRatio τ ^ 2 +
        2 * CPV.thermalRatio τ + 1 := by
    unfold coexistenceD coexistenceJ
    ring
  have hpolypos : 0 < coexistenceD (CPV.thermalRatio τ) - CPV.thermalRatio τ * coexistenceJ (CPV.thermalRatio τ) := by
    rw [hpoly]
    positivity
  have hm := mul_le_mul_of_nonneg_left (coexistenceSquare_bounds τ θ).1 hD.le
  rw [← coexistenceRadius_sq] at hm
  have hratio : coexistenceD (CPV.thermalRatio τ) * (1 / coexistenceJ (CPV.thermalRatio τ)) -
      CPV.thermalRatio τ =
        (coexistenceD (CPV.thermalRatio τ) - CPV.thermalRatio τ * coexistenceJ (CPV.thermalRatio τ)) /
          coexistenceJ (CPV.thermalRatio τ) := by field_simp [hJ.ne']
  have hprod : 0 < coexistenceD (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 - CPV.thermalRatio τ := by
    have hpos := div_pos hpolypos hJ
    rw [← hratio] at hpos
    linarith only [hm, hpos]
  have hden : 3 * coexistenceK (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 + 1 ≠ 0 := by positivity
  have hgap : CPV.thermalRatio τ / (6 * coexistenceJ (CPV.thermalRatio τ)) - coexistenceCoupling τ θ =
      (coexistenceJ (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 - 1) *
        (coexistenceD (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 - CPV.thermalRatio τ) /
        (6 * coexistenceJ (CPV.thermalRatio τ) *
          (3 * coexistenceK (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 + 1)) := by
    unfold coexistenceCoupling
    field_simp [hJ.ne', hden]
    unfold coexistenceN coexistenceD coexistenceJ coexistenceK
    ring
  have hupper : coexistenceCoupling τ θ ≤ CPV.thermalRatio τ / (6 * coexistenceJ (CPV.thermalRatio τ)) := by
    apply sub_nonneg.mp
    rw [hgap]
    have hl := coexistence_lower_radius_nonneg τ θ
    positivity
  have hthreshold : 1 / 36 - CPV.thermalRatio τ / (6 * coexistenceJ (CPV.thermalRatio τ)) =
      (1 - CPV.thermalRatio τ) ^ 2 / (36 * coexistenceJ (CPV.thermalRatio τ)) := by
    field_simp [hJ.ne']
    unfold coexistenceJ
    ring
  have hsplit := sub_pos.mpr (CPV.thermalRatio_lt_one τ)
  have hstrict : 0 < (1 - CPV.thermalRatio τ) ^ 2 / (36 * coexistenceJ (CPV.thermalRatio τ)) := by positivity
  linarith only [hupper, hthreshold, hstrict]

def coexistenceDenominator (τ θ : ℝ) : ℝ :=
  coexistenceSum τ θ ^ 2 + coexistenceProduct τ θ - 6 * coexistenceCoupling τ θ

theorem coexistenceDenominator_pos (τ θ : ℝ) : 0 < coexistenceDenominator τ θ := by
  have hs : 0 < coexistenceSum τ θ ^ 2 := by
    have h := coexistenceSum_pos τ θ
    positivity
  have hp := coexistenceProduct_sub_six_coupling_nonneg τ θ
  unfold coexistenceDenominator
  linarith only [hs, hp]

def coexistenceConstant (τ θ : ℝ) : ℝ :=
  coexistenceProduct τ θ * (coexistenceProduct τ θ - 6 * coexistenceCoupling τ θ) /
    coexistenceDenominator τ θ
def coexistenceLinear (τ θ : ℝ) : ℝ :=
  2 * coexistenceSum τ θ * (coexistenceProduct τ θ - 6 * coexistenceCoupling τ θ) /
    coexistenceDenominator τ θ
def coexistenceTemperature (τ θ : ℝ) : ℝ :=
  3 * (2 * coexistenceSum τ θ - coexistenceLinear τ θ) / (4 * Real.pi)
def coexistenceCharge (τ θ : ℝ) : ℝ :=
  Real.sqrt (3 * coexistenceProduct τ θ ^ 2 * coexistenceConstant τ θ)
def coexistenceMinimum (τ θ : ℝ) : ℝ :=
  3 * coexistenceCoupling τ θ - 3 *
    (coexistenceConstant τ θ * (coexistenceSum τ θ ^ 2 + 2 * coexistenceProduct τ θ) -
      2 * coexistenceSum τ θ * coexistenceProduct τ θ * coexistenceLinear τ θ + coexistenceProduct τ θ ^ 2)

theorem coexistenceConstant_nonneg (τ θ : ℝ) : 0 ≤ coexistenceConstant τ θ :=
  div_nonneg (mul_nonneg (coexistenceProduct_pos τ θ).le
    (coexistenceProduct_sub_six_coupling_nonneg τ θ)) (coexistenceDenominator_pos τ θ).le

theorem coexistenceLinear_nonneg (τ θ : ℝ) : 0 ≤ coexistenceLinear τ θ :=
  div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (coexistenceSum_pos τ θ).le)
    (coexistenceProduct_sub_six_coupling_nonneg τ θ)) (coexistenceDenominator_pos τ θ).le

theorem coexistenceTemperature_pos (τ θ : ℝ) : 0 < coexistenceTemperature τ θ := by
  have hgap : 2 * coexistenceSum τ θ - coexistenceLinear τ θ =
      2 * coexistenceSum τ θ ^ 3 / coexistenceDenominator τ θ := by
    unfold coexistenceLinear
    field_simp [(coexistenceDenominator_pos τ θ).ne']
    unfold coexistenceDenominator
    ring
  unfold coexistenceTemperature
  rw [hgap]
  have hs := coexistenceSum_pos τ θ
  have hd := coexistenceDenominator_pos τ θ
  positivity

theorem coexistenceCharge_sq (τ θ : ℝ) :
    coexistenceCharge τ θ ^ 2 = 3 * coexistenceProduct τ θ ^ 2 * coexistenceConstant τ θ := by
  unfold coexistenceCharge
  apply Real.sq_sqrt
  have hc := coexistenceConstant_nonneg τ θ
  positivity

#print axioms coexistenceSquare_bounds
#print axioms coexistenceCoupling_nonneg
#print axioms coexistenceCoupling_lt_threshold
#print axioms coexistenceTemperature_pos
#print axioms coexistenceCharge_sq

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
