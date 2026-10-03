import GaloisForLFunctions.RHTower.ThetaTailSchurAxisExtension

/-! The joint-center compensation is the actual normalized Schur Hessian sign. -/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.ThetaJoint
open ThetaConfluent ThetaCoordinate

local notation "k" => thetaCuspFullSource
local notation "k₁" => deriv thetaCuspFullSource
local notation "k₂" => deriv (deriv thetaCuspFullSource)
local notation "q" => thetaCuspLogCurvature 0

private theorem k_hasDerivAt (x : ℝ) : HasDerivAt k (k₁ x) x :=
  thetaCuspSchwartzReal.hasDerivAt x
private theorem k₁_hasDerivAt (x : ℝ) : HasDerivAt k₁ (k₂ x) x :=
  (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).hasDerivAt x
private theorem k₁_zero : k₁ 0 = 0 := by
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) ⟨0,rfl⟩

private theorem k_cont : Continuous k := thetaCuspSchwartzReal.continuous
private theorem k₁_cont : Continuous k₁ :=
  (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
private theorem k₂_cont : Continuous k₂ :=
  (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal)).continuous

def normalizedSchur (x y : ℝ) : ℝ := dividedSchur x y/(k x*k y)
def normalizedSchurRight (x y : ℝ) : ℝ :=
  (dividedSchurRight x y*k y-dividedSchur x y*k₁ y)/(k x*k y^2)
def normalizedSchurRightTwice (x y : ℝ) : ℝ :=
  (dividedSchurRightTwice x y*k y^2-2*dividedSchurRight x y*k y*k₁ y-
    dividedSchur x y*k y*k₂ y+2*dividedSchur x y*k₁ y^2)/(k x*k y^3)
def normalizedSchurRightLeft (x y : ℝ) : ℝ :=
  (dividedSchurBoth x y*k x*k y-dividedSchurLeft x y*k x*k₁ y-
    dividedSchurRight x y*k₁ x*k y+dividedSchur x y*k₁ x*k₁ y)/(k x^2*k y^2)

theorem normalizedSchur_continuous :
    Continuous fun p : ℝ × ℝ => normalizedSchur p.1 p.2 :=
  dividedSchur_continuous.div ((k_cont.comp continuous_fst).mul (k_cont.comp continuous_snd))
    (fun p => mul_ne_zero (thetaCuspFullSource_pos_all p.1).ne'
      (thetaCuspFullSource_pos_all p.2).ne')

theorem normalizedSchurRight_continuous :
    Continuous fun p : ℝ × ℝ => normalizedSchurRight p.1 p.2 := by
  exact ((dividedSchurRight_continuous.mul (k_cont.comp continuous_snd)).sub
    (dividedSchur_continuous.mul (k₁_cont.comp continuous_snd))).div
      ((k_cont.comp continuous_fst).mul ((k_cont.comp continuous_snd).pow 2))
      (fun p => mul_ne_zero (thetaCuspFullSource_pos_all p.1).ne'
        (pow_ne_zero 2 (thetaCuspFullSource_pos_all p.2).ne'))

theorem normalizedSchurRightTwice_continuous :
    Continuous fun p : ℝ × ℝ => normalizedSchurRightTwice p.1 p.2 := by
  exact ((((dividedSchurRightTwice_continuous.mul ((k_cont.comp continuous_snd).pow 2)).sub
    (((dividedSchurRight_continuous.const_mul 2).mul (k_cont.comp continuous_snd)).mul
      (k₁_cont.comp continuous_snd))).sub
        ((dividedSchur_continuous.mul (k_cont.comp continuous_snd)).mul
          (k₂_cont.comp continuous_snd))).add
            ((dividedSchur_continuous.const_mul 2).mul ((k₁_cont.comp continuous_snd).pow 2))).div
              ((k_cont.comp continuous_fst).mul ((k_cont.comp continuous_snd).pow 3))
              (fun p => mul_ne_zero (thetaCuspFullSource_pos_all p.1).ne'
                (pow_ne_zero 3 (thetaCuspFullSource_pos_all p.2).ne'))

theorem normalizedSchurRightLeft_continuous :
    Continuous fun p : ℝ × ℝ => normalizedSchurRightLeft p.1 p.2 := by
  exact (((((dividedSchurBoth_continuous.mul (k_cont.comp continuous_fst)).mul
    (k_cont.comp continuous_snd)).sub
      ((dividedSchurLeft_continuous.mul (k_cont.comp continuous_fst)).mul
        (k₁_cont.comp continuous_snd))).sub
          ((dividedSchurRight_continuous.mul (k₁_cont.comp continuous_fst)).mul
            (k_cont.comp continuous_snd))).add
              ((dividedSchur_continuous.mul (k₁_cont.comp continuous_fst)).mul
                (k₁_cont.comp continuous_snd))).div
                  (((k_cont.comp continuous_fst).pow 2).mul ((k_cont.comp continuous_snd).pow 2))
                  (fun p => mul_ne_zero (pow_ne_zero 2 (thetaCuspFullSource_pos_all p.1).ne')
                    (pow_ne_zero 2 (thetaCuspFullSource_pos_all p.2).ne'))

theorem normalizedSchur_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (normalizedSchur x) (normalizedSchurRight x y) y := by
  have hn := mul_ne_zero (thetaCuspFullSource_pos_all x).ne' (thetaCuspFullSource_pos_all y).ne'
  convert! (dividedSchur_hasDerivAt_right x y).div ((k_hasDerivAt y).const_mul (k x)) hn using 1
  simp only [normalizedSchurRight]
  field_simp [(thetaCuspFullSource_pos_all x).ne', (thetaCuspFullSource_pos_all y).ne']
  ring

theorem normalizedSchurRight_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (normalizedSchurRight x) (normalizedSchurRightTwice x y) y := by
  have hnum : HasDerivAt
      (fun y => dividedSchurRight x y*k y-dividedSchur x y*k₁ y)
      (dividedSchurRightTwice x y*k y-dividedSchur x y*k₂ y) y := by
    convert! ((dividedSchurRight_hasDerivAt_right x y).mul (k_hasDerivAt y)).sub
      ((dividedSchur_hasDerivAt_right x y).mul (k₁_hasDerivAt y)) using 1
    ring
  have hden := ((k_hasDerivAt y).pow 2).const_mul (k x)
  convert! hnum.div hden
    (mul_ne_zero (thetaCuspFullSource_pos_all x).ne'
      (pow_ne_zero 2 (thetaCuspFullSource_pos_all y).ne')) using 1
  simp only [normalizedSchurRightTwice]
  field_simp [(thetaCuspFullSource_pos_all x).ne', (thetaCuspFullSource_pos_all y).ne']
  ring

theorem normalizedSchurRight_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => normalizedSchurRight x y) (normalizedSchurRightLeft x y) x := by
  have hnum := ((dividedSchurRight_hasDerivAt_left x y).mul_const (k y)).sub
    ((dividedSchur_hasDerivAt_left x y).mul_const (k₁ y))
  convert! hnum.div ((k_hasDerivAt x).mul_const (k y^2))
    (mul_ne_zero (thetaCuspFullSource_pos_all x).ne'
      (pow_ne_zero 2 (thetaCuspFullSource_pos_all y).ne')) using 1
  simp only [normalizedSchurRightLeft]
  field_simp [(thetaCuspFullSource_pos_all x).ne', (thetaCuspFullSource_pos_all y).ne']
  ring

theorem normalizedSchurRight_origin : normalizedSchurRight 0 0 = 0 := by
  simp [normalizedSchurRight, dividedSchurRight_origin, k₁_zero]

theorem normalizedSchurRightTwice_origin : normalizedSchurRightTwice 0 0 =
    -2*coordinateEnergy/(3*k 0^2) := by
  simp only [normalizedSchurRightTwice, dividedSchurRightTwice_origin,
    dividedSchurRight_origin, dividedSchur_origin, k₁_zero, source_second_center,
    coordinateEnergy, centerEntry]
  field_simp [(thetaCuspFullSource_pos_all 0).ne']
  ring

/-- The compensation certificate is the exact diagonal-direction Hessian, including the
inverse-Gram contribution. -/
theorem normalizedSchurHessian_sum_origin :
    normalizedSchurRightLeft 0 0+normalizedSchurRightTwice 0 0 =
      -jointCoordinateCompensation/k 0^2 := by
  rw [normalizedSchurRightTwice_origin]
  simp only [normalizedSchurRightLeft, dividedSchurBoth_origin, dividedSchurLeft_origin,
    dividedSchurRight_origin, dividedSchur_origin, k₁_zero, coordinateEnergy,
    jointCoordinateCompensation]
  field_simp [(thetaCuspFullSource_pos_all 0).ne', centerMass_pos.ne']
  ring

theorem normalizedSchurRightTwice_origin_neg : normalizedSchurRightTwice 0 0 < 0 := by
  rw [normalizedSchurRightTwice_origin]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) coordinateEnergy_pos)
    (mul_pos (by norm_num) (sq_pos_of_pos (thetaCuspFullSource_pos_all 0)))

theorem normalizedSchurHessian_sum_origin_neg :
    normalizedSchurRightLeft 0 0+normalizedSchurRightTwice 0 0 < 0 := by
  rw [normalizedSchurHessian_sum_origin]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos jointCoordinateCompensation_pos)
    (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))

theorem eventually_normalizedSchurHessian_neg :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), normalizedSchurRightTwice p.1 p.2 < 0 ∧
      normalizedSchurRightLeft p.1 p.2+normalizedSchurRightTwice p.1 p.2 < 0 := by
  exact ((normalizedSchurRightTwice_continuous.continuousAt.eventually
    (isOpen_Iio.mem_nhds normalizedSchurRightTwice_origin_neg))).and
      (((normalizedSchurRightLeft_continuous.add normalizedSchurRightTwice_continuous).
        continuousAt.eventually (isOpen_Iio.mem_nhds normalizedSchurHessian_sum_origin_neg)))

end RHTower.ThetaJoint
