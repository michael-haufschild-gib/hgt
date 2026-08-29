import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualMaassModeJet

/-!
# Actual signed Whittaker first-jet weld on the exterior cusp

Corpus conjecture C-A.9t2b2a isolates the least analytic input needed to weld the
literal Poincare Maass legs to the canonical signed Whittaker words.  On the
Stokes top edge `Y >= 1`, the corpus arithmetic packet already pays the
summable rate `exp (-(N+1)/2)`.  The arbitrary-order Schlaefli envelope makes
that same rate uniform on the full height neighborhood `(1/2, 2Y)`.

This module uses that common majorant to differentiate the actual signed
square-root Whittaker tail vertically.  Horizontal and mixed differentiation
then cost only fixed powers of the Fourier index.  The pure vertical second
jet will be recovered downstream from the already-proved Poincare eigen-
equation, so no redundant second-radial-jet majorant is assumed.

RH chain:

signed exterior first-jet weld -> actual/canonical raise-lower weld -> literal
truncated Green/Stokes -> full cusp current -> balanced BM `++-` coefficient ->
negative BM leg -> left-QNM -> HC94 -> RH.
-/

open Complex Real Filter Set Topology

namespace RHTower
noncomputable section

/-- Uniform Bessel constant on every exterior-cusp differentiation neighborhood. -/
def d4BMSignedWhittakerLocalBesselConstant (mu : ℂ) : ℝ :=
  Real.exp (‖mu‖ ^ 2) * Real.sqrt (4 * Real.pi)

lemma d4BMSignedWhittakerLocalBesselConstant_nonneg (mu : ℂ) :
    0 ≤ d4BMSignedWhittakerLocalBesselConstant mu := by
  unfold d4BMSignedWhittakerLocalBesselConstant
  positivity

/-- On `(1/2,2Y)`, every signed Whittaker Bessel carrier has the common
`exp (-(N+1)/2)` envelope needed by the existing arithmetic packet. -/
theorem d4BM_norm_modifiedBesselKOrder_signed_local_le
    (Y : {y : ℝ // 1 ≤ y}) {q : ℝ}
    (hq : q ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)))
    (N : ℕ) (mu : ℂ) :
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (2 * Real.pi * ((N : ℝ) + 1) * q) mu‖ ≤
      d4BMSignedWhittakerLocalBesselConstant mu *
        Real.exp (-(((N : ℝ) + 1) / 2)) := by
  have hq0 : 0 < q := by linarith [hq.1]
  let s : {x : ℝ // 0 < x} :=
    ⟨2 * Real.pi * ((N : ℝ) + 1) * q, by positivity⟩
  have hnOne : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hhalf_le_s : ((N : ℝ) + 1) / 2 ≤ (s : ℝ) := by
    dsimp [s]
    have hqhalf : (1 / 2 : ℝ) ≤ q := hq.1.le
    have hnnonneg : 0 ≤ (N : ℝ) + 1 := by positivity
    have hnq : ((N : ℝ) + 1) / 2 ≤ ((N : ℝ) + 1) * q := by
      nlinarith [mul_le_mul_of_nonneg_left hqhalf hnnonneg]
    have hscale : ((N : ℝ) + 1) * q ≤
        2 * Real.pi * ((N : ℝ) + 1) * q := by
      have hnonneg : 0 ≤ ((N : ℝ) + 1) * q := by positivity
      nlinarith [mul_le_mul_of_nonneg_right htwoPi hnonneg]
    exact hnq.trans hscale
  have hsHalf : (1 / 2 : ℝ) ≤ (s : ℝ) :=
    (by nlinarith [hnOne] : (1 / 2 : ℝ) ≤ ((N : ℝ) + 1) / 2).trans hhalf_le_s
  have horder : ‖mu‖ ^ 2 / (2 * (s : ℝ)) ≤ ‖mu‖ ^ 2 := by
    have hden : (1 : ℝ) ≤ 2 * (s : ℝ) := by nlinarith
    calc
      ‖mu‖ ^ 2 / (2 * (s : ℝ)) ≤ ‖mu‖ ^ 2 / 1 := by
        exact div_le_div_of_nonneg_left (sq_nonneg ‖mu‖) (by positivity) hden
      _ = ‖mu‖ ^ 2 := by ring
  have hsqrt : Real.sqrt (2 * Real.pi / (s : ℝ)) ≤
      Real.sqrt (4 * Real.pi) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ s.2]
    nlinarith [Real.pi_pos]
  have hexp : Real.exp (-(s : ℝ)) ≤
      Real.exp (-(((N : ℝ) + 1) / 2)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hhalf_le_s)
  have henv := d4BM_norm_modifiedBesselKOrder_le s mu
  calc
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (2 * Real.pi * ((N : ℝ) + 1) * q) mu‖
        ≤ Real.exp (-(s : ℝ)) *
            Real.exp (‖mu‖ ^ 2 / (2 * (s : ℝ))) *
              Real.sqrt (2 * Real.pi / (s : ℝ)) := by
          simpa [s] using henv
    _ ≤ Real.exp (-(((N : ℝ) + 1) / 2)) *
          Real.exp (‖mu‖ ^ 2) * Real.sqrt (4 * Real.pi) := by
          gcongr
    _ = d4BMSignedWhittakerLocalBesselConstant mu *
          Real.exp (-(((N : ℝ) + 1) / 2)) := by
          unfold d4BMSignedWhittakerLocalBesselConstant
          ring

/-- Existing arithmetic admission, exposed in the exact zero-height-degree form
needed by local Whittaker differentiation. -/
theorem summable_d4BMCompletedEisensteinCoefficientIndexExpHalf
    (u : ℂ) (indexDegree : ℕ) :
    Summable (fun N : ℕ =>
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ indexDegree‖ *
        Real.exp (-(((N : ℝ) + 1) / 2))) := by
  simpa using
    d4BM_completedEisensteinPolynomialWhittakerCoefficient_weightedSummable
      u indexDegree 0

/-- Uniform first-radial-jet constant on `(1/2,2Y)`. -/
def d4BMSignedWhittakerLocalFirstJetConstant
    (Y : {y : ℝ // 1 ≤ y}) (nu : ℂ) : ℝ :=
  d4BMSignedWhittakerLocalBesselConstant nu +
    Real.sqrt (2 * (Y : ℝ)) * Real.pi *
      (d4BMSignedWhittakerLocalBesselConstant (nu + 1) +
        d4BMSignedWhittakerLocalBesselConstant (nu - 1))

lemma d4BMSignedWhittakerLocalFirstJetConstant_nonneg
    (Y : {y : ℝ // 1 ≤ y}) (nu : ℂ) :
    0 ≤ d4BMSignedWhittakerLocalFirstJetConstant Y nu := by
  unfold d4BMSignedWhittakerLocalFirstJetConstant
  exact add_nonneg
    (d4BMSignedWhittakerLocalBesselConstant_nonneg nu)
    (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)
      (add_nonneg
        (d4BMSignedWhittakerLocalBesselConstant_nonneg (nu + 1))
        (d4BMSignedWhittakerLocalBesselConstant_nonneg (nu - 1))))

/-- The genuine first radial jet has one index-linear locally uniform
majorant on every exterior cusp neighborhood. -/
theorem norm_d4BMWhittakerP0FirstJet_signed_local_le
    (Y : {y : ℝ // 1 ≤ y}) {q : ℝ}
    (hq : q ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)))
    (N : ℕ) (nu : ℂ) :
    ‖d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu q‖ ≤
      d4BMSignedWhittakerLocalFirstJetConstant Y nu *
        ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) + 1) / 2)) := by
  have hq0 : 0 < q := by linarith [hq.1]
  have hnOne : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  let eN : ℝ := Real.exp (-(((N : ℝ) + 1) / 2))
  let C0 := d4BMSignedWhittakerLocalBesselConstant nu
  let Cp := d4BMSignedWhittakerLocalBesselConstant (nu + 1)
  let Cm := d4BMSignedWhittakerLocalBesselConstant (nu - 1)
  have hK0 :
      ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((d4BMPositiveFourierScale N : ℝ) * q) nu‖ ≤ C0 * eN := by
    simpa [d4BMPositiveFourierScale, C0, eN] using
      d4BM_norm_modifiedBesselKOrder_signed_local_le Y hq N nu
  have hKp :
      ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((d4BMPositiveFourierScale N : ℝ) * q) (nu + 1)‖ ≤ Cp * eN := by
    simpa [d4BMPositiveFourierScale, Cp, eN] using
      d4BM_norm_modifiedBesselKOrder_signed_local_le Y hq N (nu + 1)
  have hKm :
      ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((d4BMPositiveFourierScale N : ℝ) * q) (nu - 1)‖ ≤ Cm * eN := by
    simpa [d4BMPositiveFourierScale, Cm, eN] using
      d4BM_norm_modifiedBesselKOrder_signed_local_le Y hq N (nu - 1)
  have hsqrtLower : (1 / 2 : ℝ) ≤ Real.sqrt q := by
    have hsqrtSq := Real.sq_sqrt hq0.le
    have hsqrt0 := Real.sqrt_nonneg q
    nlinarith [hq.1]
  have hinv : ‖(((1 / (2 * Real.sqrt q) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1 / (2 * Real.sqrt q) : ℝ))]
    rw [div_le_one (by positivity : 0 < 2 * Real.sqrt q)]
    nlinarith
  have hsqrtUpper : Real.sqrt q ≤ Real.sqrt (2 * (Y : ℝ)) := by
    exact Real.sqrt_le_sqrt hq.2.le
  have hsqrtNorm : ‖(Real.sqrt q : ℂ)‖ = Real.sqrt q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg q)]
  have hscaleNorm : ‖(d4BMPositiveFourierScale N : ℂ)‖ =
      2 * Real.pi * ((N : ℝ) + 1) := by
    rw [show (d4BMPositiveFourierScale N : ℂ) =
        ((2 * Real.pi * ((N : ℝ) + 1) : ℝ) : ℂ) by
      rfl, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hhalfNorm : ‖(-(1 / 2 : ℂ))‖ = (1 / 2 : ℝ) := by norm_num
  have hsumK :
      ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((d4BMPositiveFourierScale N : ℝ) * q) (nu + 1) +
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((d4BMPositiveFourierScale N : ℝ) * q) (nu - 1)‖ ≤
        (Cp + Cm) * eN := by
    calc
      _ ≤ ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
              ((d4BMPositiveFourierScale N : ℝ) * q) (nu + 1)‖ +
            ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
              ((d4BMPositiveFourierScale N : ℝ) * q) (nu - 1)‖ := norm_add_le _ _
      _ ≤ Cp * eN + Cm * eN := add_le_add hKp hKm
      _ = (Cp + Cm) * eN := by ring
  have hfirst :
      ‖d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu q‖ ≤
        C0 * eN +
          (Real.sqrt (2 * (Y : ℝ)) *
            (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2)) *
              ((Cp + Cm) * eN) := by
    unfold d4BMWhittakerP0FirstJet
    calc
      _ ≤ (‖((1 / (2 * Real.sqrt q) : ℝ) : ℂ) *
              GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
                ((d4BMPositiveFourierScale N : ℝ) * q) nu‖) +
            (‖(Real.sqrt q : ℂ) * (d4BMPositiveFourierScale N : ℂ) *
              (-(1 / 2 : ℂ)) *
                (GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
                    ((d4BMPositiveFourierScale N : ℝ) * q) (nu + 1) +
                  GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
                    ((d4BMPositiveFourierScale N : ℝ) * q) (nu - 1))‖) :=
          norm_add_le _ _
      _ ≤ C0 * eN +
            (Real.sqrt (2 * (Y : ℝ)) *
              (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2)) *
                ((Cp + Cm) * eN) := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul,
            hsqrtNorm, hscaleNorm, hhalfNorm]
          apply add_le_add
          · calc
              ‖(((1 / (2 * Real.sqrt q) : ℝ) : ℂ))‖ *
                    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
                      ((d4BMPositiveFourierScale N : ℝ) * q) nu‖
                  ≤ 1 * (C0 * eN) := by
                    exact mul_le_mul hinv hK0 (norm_nonneg _) zero_le_one
              _ = C0 * eN := by ring
          · gcongr
  calc
    ‖d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu q‖
        ≤ C0 * eN +
          (Real.sqrt (2 * (Y : ℝ)) *
            (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2)) *
              ((Cp + Cm) * eN) := hfirst
    _ ≤ C0 * ((N : ℝ) + 1) * eN +
          (Real.sqrt (2 * (Y : ℝ)) * Real.pi * (Cp + Cm)) *
            ((N : ℝ) + 1) * eN := by
          have hC0 : 0 ≤ C0 := d4BMSignedWhittakerLocalBesselConstant_nonneg nu
          have heN : 0 ≤ eN := Real.exp_nonneg _
          apply add_le_add
          · apply mul_le_mul_of_nonneg_right _ heN
            calc
              C0 = C0 * 1 := by ring
              _ ≤ C0 * ((N : ℝ) + 1) :=
                mul_le_mul_of_nonneg_left hnOne hC0
          · convert le_rfl using 1 <;> ring
    _ = d4BMSignedWhittakerLocalFirstJetConstant Y nu *
          ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) + 1) / 2)) := by
          simp only [d4BMSignedWhittakerLocalFirstJetConstant, C0, Cp, Cm, eN]
          ring

/-- Uniform value-level constant on an exterior cusp neighborhood. -/
def d4BMSignedWhittakerLocalValueConstant
    (Y : {y : ℝ // 1 ≤ y}) (nu : ℂ) : ℝ :=
  Real.sqrt (2 * (Y : ℝ)) * d4BMSignedWhittakerLocalBesselConstant nu

lemma d4BMSignedWhittakerLocalValueConstant_nonneg
    (Y : {y : ℝ // 1 ≤ y}) (nu : ℂ) :
    0 ≤ d4BMSignedWhittakerLocalValueConstant Y nu := by
  unfold d4BMSignedWhittakerLocalValueConstant
  exact mul_nonneg (Real.sqrt_nonneg _)
    (d4BMSignedWhittakerLocalBesselConstant_nonneg nu)

/-- The Whittaker value itself has a degree-zero common majorant. -/
theorem norm_d4BMWhittakerP0_signed_local_le
    (Y : {y : ℝ // 1 ≤ y}) {q : ℝ}
    (hq : q ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)))
    (N : ℕ) (nu : ℂ) :
    ‖d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu q‖ ≤
      d4BMSignedWhittakerLocalValueConstant Y nu *
        Real.exp (-(((N : ℝ) + 1) / 2)) := by
  have hq0 : 0 < q := by linarith [hq.1]
  have hK := d4BM_norm_modifiedBesselKOrder_signed_local_le Y hq N nu
  have hK' :
      ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((d4BMPositiveFourierScale N : ℝ) * q) nu‖ ≤
        d4BMSignedWhittakerLocalBesselConstant nu *
          Real.exp (-(((N : ℝ) + 1) / 2)) := by
    simpa [d4BMPositiveFourierScale] using hK
  unfold d4BMWhittakerP0 d4BMSignedWhittakerLocalValueConstant
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg q)]
  calc
    Real.sqrt q *
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((d4BMPositiveFourierScale N : ℝ) * q) nu‖
        ≤ Real.sqrt (2 * (Y : ℝ)) *
            ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
              ((d4BMPositiveFourierScale N : ℝ) * q) nu‖ := by
          gcongr
          exact hq.2.le
    _ ≤ Real.sqrt (2 * (Y : ℝ)) *
          (d4BMSignedWhittakerLocalBesselConstant nu *
            Real.exp (-(((N : ℝ) + 1) / 2))) := by
          exact mul_le_mul_of_nonneg_left hK' (Real.sqrt_nonneg _)
    _ = (Real.sqrt (2 * (Y : ℝ)) *
          d4BMSignedWhittakerLocalBesselConstant nu) *
            Real.exp (-(((N : ℝ) + 1) / 2)) := by ring

/-- Arithmetic coefficient times one signed Whittaker mode. -/
def d4BMCompletedEisensteinWeightedSignedWhittakerMode
    (u : ℂ) (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
    d4BMSignedWhittakerMode negative N nu x Y

/-- Arithmetic coefficient times the genuine vertical first jet of one signed mode. -/
def d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
    (u : ℂ) (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
    d4BMSignedWhittakerModeVerticalFirstJet negative N nu x Y

/-- Norm of the signed horizontal logarithmic derivative. -/
theorem norm_d4BMSignedFourierRate (negative : Bool) (N : ℕ) :
    ‖d4BMSignedFourierRate negative N‖ =
      2 * Real.pi * ((N : ℝ) + 1) := by
  unfold d4BMSignedFourierRate
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
  change ‖(d4BMFourierSign negative : ℂ)‖ *
      ‖((2 * Real.pi * ((N : ℝ) + 1) : ℝ) : ℂ)‖ =
    2 * Real.pi * ((N : ℝ) + 1)
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hscale : 0 < 2 * Real.pi * ((N : ℝ) + 1) := by positivity
  rw [abs_of_pos hscale]
  cases negative <;> simp [d4BMFourierSign]

/-- Existing signed square-root tail equals the coefficientwise actual mode sum. -/
theorem d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_weightedMode_tsum
    (u nu : ℂ) (negative : Bool) (x Y : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail
        u nu negative x 0 0 Y =
      ∑' N : ℕ,
        d4BMCompletedEisensteinWeightedSignedWhittakerMode
          u negative N nu x Y := by
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerTail
  apply tsum_congr
  intro N
  simp only [pow_zero, mul_one]
  unfold d4BMCompletedEisensteinWeightedSignedWhittakerMode
    d4BMSignedWhittakerMode d4BMWhittakerP0 d4BMPositiveFourierScale
  ring

/-- Canonical signed tail's actual vertical first jet. -/
def d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
    (u nu : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u negative N nu x Y

/-- Arithmetic coefficient times the genuine horizontal first jet. -/
def d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
    (u : ℂ) (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
    d4BMSignedWhittakerModeHorizontalFirstJet negative N nu x Y

/-- Arithmetic coefficient times the genuine horizontal second jet. -/
def d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
    (u : ℂ) (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
    d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y

/-- Arithmetic coefficient times the genuine mixed second jet. -/
def d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
    (u : ℂ) (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
    d4BMSignedWhittakerModeMixedSecondJet negative N nu x Y

/-- Canonical signed tail's actual horizontal first jet. -/
def d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
    (u nu : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u negative N nu x Y

/-- Canonical signed tail's actual horizontal second jet. -/
def d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalSecondJetTail
    (u nu : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u negative N nu x Y

/-- Canonical signed tail's actual mixed second jet. -/
def d4BMCompletedEisensteinSignedSqrtWhittakerMixedSecondJetTail
    (u nu : ℂ) (negative : Bool) (x Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
      u negative N nu x Y

/-- The canonical signed square-root Whittaker tail is genuinely vertically
differentiable on every exterior cusp edge, with derivative equal to the
coefficientwise actual first jet. -/
theorem hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_vertical
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (d4BMCompletedEisensteinSignedSqrtWhittakerTail
        u nu negative x 0 0)
      (d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
        u nu negative x Y) (Y : ℝ) := by
  let t : Set ℝ := Ioo (1 / 2 : ℝ) (2 * (Y : ℝ))
  let g : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerMode
      u negative N nu x q
  let g' : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u negative N nu x q
  let M : ℕ → ℝ := fun N =>
    d4BMSignedWhittakerLocalFirstJetConstant Y nu *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ 1‖ *
        Real.exp (-(((N : ℝ) + 1) / 2)))
  let M0 : ℕ → ℝ := fun N =>
    d4BMSignedWhittakerLocalValueConstant Y nu *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ 0‖ *
        Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 1).mul_left
      (d4BMSignedWhittakerLocalFirstJetConstant Y nu)
  have hM0 : Summable M0 :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 0).mul_left
      (d4BMSignedWhittakerLocalValueConstant Y nu)
  have hderiv : ∀ N, ∀ q ∈ t, HasDerivAt (g N) (g' N q) q := by
    intro N q hq
    have h := (hasDerivAt_d4BMSignedWhittakerMode_vertical
      negative N nu x ⟨q, by dsimp [t] at hq; linarith [hq.1]⟩).const_mul
        (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩)
    simpa [g, g', d4BMCompletedEisensteinWeightedSignedWhittakerMode,
      d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet] using h
  have hbound : ∀ N, ∀ q ∈ t, ‖g' N q‖ ≤ M N := by
    intro N q hq
    have hfirst := norm_d4BMWhittakerP0FirstJet_signed_local_le
      Y (by simpa [t] using hq) N nu
    rw [show g' N q =
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (d4BMCompletedEisensteinFourierPhase negative N x *
            d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu q) by
      rfl, norm_mul, norm_mul,
      d4BM_norm_completedEisensteinFourierPhase, one_mul]
    calc
      _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          (d4BMSignedWhittakerLocalFirstJetConstant Y nu *
            ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) + 1) / 2))) := by
            gcongr
      _ = M N := by
            have hnNorm : ‖(((N + 1 : ℕ) : ℂ))‖ = (N : ℝ) + 1 := by
              rw [Complex.norm_natCast]
              norm_num [Real.norm_eq_abs, abs_of_nonneg]
            simp only [M, pow_one, norm_mul, hnNorm]
            ring
  have hYmem : (Y : ℝ) ∈ t := by
    dsimp only [t]
    constructor <;> linarith [Y.2]
  have hbase : Summable fun N => g N (Y : ℝ) := by
    apply Summable.of_norm_bounded hM0
    intro N
    have hvalue := norm_d4BMWhittakerP0_signed_local_le
      Y hYmem N nu
    rw [show g N (Y : ℝ) =
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (d4BMCompletedEisensteinFourierPhase negative N x *
            d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y) by
      rfl, norm_mul, norm_mul,
      d4BM_norm_completedEisensteinFourierPhase, one_mul]
    calc
      _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          (d4BMSignedWhittakerLocalValueConstant Y nu *
            Real.exp (-(((N : ℝ) + 1) / 2))) := by gcongr
      _ = M0 N := by simp [M0]; ring
  have hsum := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo
    isPreconnected_Ioo hderiv hbound hYmem hbase hYmem
  have hfun :
      d4BMCompletedEisensteinSignedSqrtWhittakerTail
          u nu negative x 0 0 =
        (fun q : ℝ => ∑' N : ℕ, g N q) := by
    funext q
    unfold d4BMCompletedEisensteinSignedSqrtWhittakerTail
    apply tsum_congr
    intro N
    simp only [pow_zero, mul_one]
    unfold g d4BMCompletedEisensteinWeightedSignedWhittakerMode
      d4BMSignedWhittakerMode d4BMWhittakerP0 d4BMPositiveFourierScale
    ring
  have hder :
      d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
          u nu negative x Y =
        ∑' N : ℕ, g' N Y := by
    unfold d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
    apply tsum_congr
    intro N
    rfl
  rw [hfun, hder]
  exact hsum

/-- The canonical signed tail is genuinely horizontally differentiable on
every exterior cusp edge. -/
theorem hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_horizontal
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (fun q : ℝ => d4BMCompletedEisensteinSignedSqrtWhittakerTail
        u nu negative q 0 0 Y)
      (d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
        u nu negative x Y) x := by
  let g : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerMode
      u negative N nu q Y
  let g' : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u negative N nu q Y
  let C := d4BMSignedWhittakerLocalValueConstant Y nu
  let M : ℕ → ℝ := fun N =>
    (2 * Real.pi * C) *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ 1‖ *
        Real.exp (-(((N : ℝ) + 1) / 2)))
  let M0 : ℕ → ℝ := fun N =>
    C *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ 0‖ *
        Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 1).mul_left
      (2 * Real.pi * C)
  have hM0 : Summable M0 :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 0).mul_left C
  have hYmem : (Y : ℝ) ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)) := by
    constructor <;> linarith [Y.2]
  have hvalue (N : ℕ) := norm_d4BMWhittakerP0_signed_local_le Y hYmem N nu
  have hderiv : ∀ N, ∀ q ∈ (Set.univ : Set ℝ),
      HasDerivAt (g N) (g' N q) q := by
    intro N q _hq
    have h := (hasDerivAt_d4BMSignedWhittakerMode_horizontal
      negative N nu q Y).const_mul
        (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩)
    simpa [g, g', d4BMCompletedEisensteinWeightedSignedWhittakerMode,
      d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet] using h
  have hbound : ∀ N, ∀ q ∈ (Set.univ : Set ℝ), ‖g' N q‖ ≤ M N := by
    intro N q _hq
    rw [show g' N q =
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (d4BMSignedFourierRate negative N *
            (d4BMCompletedEisensteinFourierPhase negative N q *
              d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y)) by rfl,
      norm_mul, norm_mul, norm_mul, norm_d4BMSignedFourierRate,
      d4BM_norm_completedEisensteinFourierPhase, one_mul]
    calc
      _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          (2 * Real.pi * ((N : ℝ) + 1)) *
            (C * Real.exp (-(((N : ℝ) + 1) / 2))) := by
              have hvalueN :
                  ‖d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y‖ ≤
                    C * Real.exp (-(((N : ℝ) + 1) / 2)) := by
                simpa only [C] using hvalue N
              have hcoeffNonneg :
                  0 ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient
                    u ⟨N + 1, by omega⟩‖ := norm_nonneg _
              have hscaleNonneg :
                  0 ≤ 2 * Real.pi * ((N : ℝ) + 1) :=
                mul_nonneg
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
                  (add_nonneg (Nat.cast_nonneg N) zero_le_one)
              simpa only [mul_assoc] using
                (mul_le_mul_of_nonneg_left hvalueN
                  (mul_nonneg hcoeffNonneg hscaleNonneg))
      _ = M N := by
            have hnNorm : ‖(((N + 1 : ℕ) : ℂ))‖ = (N : ℝ) + 1 := by
              rw [Complex.norm_natCast]
              norm_num [Real.norm_eq_abs, abs_of_nonneg]
            simp only [M, pow_one, norm_mul, hnNorm]
            ring
  have hbase : Summable fun N => g N x := by
    apply Summable.of_norm_bounded hM0
    intro N
    rw [show g N x =
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (d4BMCompletedEisensteinFourierPhase negative N x *
            d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y) by rfl,
      norm_mul, norm_mul, d4BM_norm_completedEisensteinFourierPhase, one_mul]
    calc
      _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          (C * Real.exp (-(((N : ℝ) + 1) / 2))) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            simpa only [C] using hvalue N
      _ = M0 N := by simp [M0, C]; ring
  have hsum := hasDerivAt_tsum_of_isPreconnected hM isOpen_univ
    isPreconnected_univ hderiv hbound (Set.mem_univ x) hbase (Set.mem_univ x)
  have hfun :
      (fun q : ℝ => d4BMCompletedEisensteinSignedSqrtWhittakerTail
        u nu negative q 0 0 Y) =
      (fun q : ℝ => ∑' N : ℕ, g N q) := by
    funext q
    exact d4BMCompletedEisensteinSignedSqrtWhittakerTail_eq_weightedMode_tsum
      u nu negative q Y
  have hder :
      d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
          u nu negative x Y =
        ∑' N : ℕ, g' N x := by
    unfold d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
    apply tsum_congr
    intro N
    rfl
  rw [hfun, hder]
  exact hsum

theorem summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    Summable (fun N : ℕ =>
      d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
        u negative N nu x Y) := by
  let C := d4BMSignedWhittakerLocalFirstJetConstant Y nu
  let M : ℕ → ℝ := fun N =>
    C * (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ 1‖ * Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 1).mul_left C
  apply Summable.of_norm_bounded hM
  intro N
  have hYmem : (Y : ℝ) ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)) := by
    constructor <;> linarith [Y.2]
  have hfirst := norm_d4BMWhittakerP0FirstJet_signed_local_le Y hYmem N nu
  rw [show d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
        u negative N nu x Y =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMCompletedEisensteinFourierPhase negative N x *
          d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu Y) by rfl,
    norm_mul, norm_mul, d4BM_norm_completedEisensteinFourierPhase, one_mul]
  calc
    _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
        (C * ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) + 1) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa only [C] using hfirst
    _ = M N := by
          have hnNorm : ‖(((N + 1 : ℕ) : ℂ))‖ = (N : ℝ) + 1 := by
            rw [Complex.norm_natCast]
            norm_num [Real.norm_eq_abs, abs_of_nonneg]
          simp only [M, pow_one, norm_mul, hnNorm]
          ring

theorem summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    Summable (fun N : ℕ =>
      d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
        u negative N nu x Y) := by
  let C := d4BMSignedWhittakerLocalValueConstant Y nu
  let M : ℕ → ℝ := fun N =>
    (2 * Real.pi * C) *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        ((N + 1 : ℕ) : ℂ) ^ 1‖ * Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 1).mul_left
      (2 * Real.pi * C)
  apply Summable.of_norm_bounded hM
  intro N
  have hYmem : (Y : ℝ) ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)) := by
    constructor <;> linarith [Y.2]
  have hvalue := norm_d4BMWhittakerP0_signed_local_le Y hYmem N nu
  rw [show d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
        u negative N nu x Y =
      d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        (d4BMSignedFourierRate negative N *
          (d4BMCompletedEisensteinFourierPhase negative N x *
            d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y)) by rfl,
    norm_mul, norm_mul, norm_mul, norm_d4BMSignedFourierRate,
    d4BM_norm_completedEisensteinFourierPhase, one_mul]
  calc
    _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
        (2 * Real.pi * ((N : ℝ) + 1)) *
          (C * Real.exp (-(((N : ℝ) + 1) / 2))) := by
            have hvalue' :
                ‖d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y‖ ≤
                  C * Real.exp (-(((N : ℝ) + 1) / 2)) := by
              simpa only [C] using hvalue
            have hnonneg :
                0 ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient
                    u ⟨N + 1, by omega⟩‖ *
                  (2 * Real.pi * ((N : ℝ) + 1)) := by positivity
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hvalue' hnonneg
    _ = M N := by
          have hnNorm : ‖(((N + 1 : ℕ) : ℂ))‖ = (N : ℝ) + 1 := by
            rw [Complex.norm_natCast]
            norm_num [Real.norm_eq_abs, abs_of_nonneg]
          simp only [M, pow_one, norm_mul, hnNorm]
          ring

/-- Horizontal differentiation of the canonical vertical first-jet tail gives
the actual mixed second jet. -/
theorem hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail_horizontal
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (fun q : ℝ =>
        d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
          u nu negative q Y)
      (d4BMCompletedEisensteinSignedSqrtWhittakerMixedSecondJetTail
        u nu negative x Y) x := by
  let g : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u negative N nu q Y
  let g' : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet
      u negative N nu q Y
  let C := d4BMSignedWhittakerLocalFirstJetConstant Y nu
  let M : ℕ → ℝ := fun N =>
    (2 * Real.pi * C) *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ 2‖ *
        Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 2).mul_left
      (2 * Real.pi * C)
  have hYmem : (Y : ℝ) ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)) := by
    constructor <;> linarith [Y.2]
  have hfirst (N : ℕ) :=
    norm_d4BMWhittakerP0FirstJet_signed_local_le Y hYmem N nu
  have hderiv : ∀ N, ∀ q ∈ (Set.univ : Set ℝ),
      HasDerivAt (g N) (g' N q) q := by
    intro N q _hq
    have h := (hasDerivAt_d4BMSignedWhittakerModeVerticalFirstJet_horizontal
      negative N nu q Y).const_mul
        (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩)
    simpa [g, g', d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet,
      d4BMCompletedEisensteinWeightedSignedWhittakerMixedSecondJet] using h
  have hbound : ∀ N, ∀ q ∈ (Set.univ : Set ℝ), ‖g' N q‖ ≤ M N := by
    intro N q _hq
    rw [show g' N q =
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (d4BMSignedFourierRate negative N *
            (d4BMCompletedEisensteinFourierPhase negative N q *
              d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu Y)) by rfl,
      norm_mul, norm_mul, norm_mul, norm_d4BMSignedFourierRate,
      d4BM_norm_completedEisensteinFourierPhase, one_mul]
    calc
      _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          (2 * Real.pi * ((N : ℝ) + 1)) *
            (C * ((N : ℝ) + 1) * Real.exp (-(((N : ℝ) + 1) / 2))) := by
              have hfirst' :
                  ‖d4BMWhittakerP0FirstJet
                      (d4BMPositiveFourierScale N) nu Y‖ ≤
                    C * ((N : ℝ) + 1) *
                      Real.exp (-(((N : ℝ) + 1) / 2)) := by
                simpa only [C] using hfirst N
              have hnonneg :
                  0 ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient
                      u ⟨N + 1, by omega⟩‖ *
                    (2 * Real.pi * ((N : ℝ) + 1)) := by positivity
              simpa only [mul_assoc] using
                mul_le_mul_of_nonneg_left hfirst' hnonneg
      _ = M N := by
            have hnNorm : ‖(((N + 1 : ℕ) : ℂ))‖ = (N : ℝ) + 1 := by
              rw [Complex.norm_natCast]
              norm_num [Real.norm_eq_abs, abs_of_nonneg]
            simp only [M, norm_mul, norm_pow, hnNorm]
            ring
  have hbase :=
    summable_d4BMCompletedEisensteinWeightedSignedWhittakerVerticalFirstJet
      u nu negative x Y
  have hsum := hasDerivAt_tsum_of_isPreconnected hM isOpen_univ
    isPreconnected_univ hderiv hbound (Set.mem_univ x) hbase (Set.mem_univ x)
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerVerticalFirstJetTail
    d4BMCompletedEisensteinSignedSqrtWhittakerMixedSecondJetTail
  simpa only [g, g'] using hsum

/-- A second horizontal differentiation of the canonical signed tail is
justified by the same degree-two arithmetic admission. -/
theorem hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail_horizontal
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    HasDerivAt
      (fun q : ℝ =>
        d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
          u nu negative q Y)
      (d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalSecondJetTail
        u nu negative x Y) x := by
  let g : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u negative N nu q Y
  let g' : ℕ → ℝ → ℂ := fun N q =>
    d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet
      u negative N nu q Y
  let C := d4BMSignedWhittakerLocalValueConstant Y nu
  let M : ℕ → ℝ := fun N =>
    ((2 * Real.pi) ^ 2 * C) *
      (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ 2‖ *
        Real.exp (-(((N : ℝ) + 1) / 2)))
  have hM : Summable M :=
    (summable_d4BMCompletedEisensteinCoefficientIndexExpHalf u 2).mul_left
      ((2 * Real.pi) ^ 2 * C)
  have hYmem : (Y : ℝ) ∈ Ioo (1 / 2 : ℝ) (2 * (Y : ℝ)) := by
    constructor <;> linarith [Y.2]
  have hvalue (N : ℕ) := norm_d4BMWhittakerP0_signed_local_le Y hYmem N nu
  have hderiv : ∀ N, ∀ q ∈ (Set.univ : Set ℝ),
      HasDerivAt (g N) (g' N q) q := by
    intro N q _hq
    have h := (hasDerivAt_d4BMSignedWhittakerModeHorizontalFirstJet_horizontal
      negative N nu q Y).const_mul
        (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩)
    simpa [g, g', d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet,
      d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalSecondJet] using h
  have hbound : ∀ N, ∀ q ∈ (Set.univ : Set ℝ), ‖g' N q‖ ≤ M N := by
    intro N q _hq
    rw [show g' N q =
        d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (d4BMSignedFourierRate negative N ^ 2 *
            (d4BMCompletedEisensteinFourierPhase negative N q *
              d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y)) by rfl,
      norm_mul, norm_mul, norm_pow, norm_mul, norm_d4BMSignedFourierRate,
      d4BM_norm_completedEisensteinFourierPhase, one_mul]
    calc
      _ ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 *
            (C * Real.exp (-(((N : ℝ) + 1) / 2))) := by
              have hvalue' :
                  ‖d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y‖ ≤
                    C * Real.exp (-(((N : ℝ) + 1) / 2)) := by
                simpa only [C] using hvalue N
              have hnonneg :
                  0 ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient
                      u ⟨N + 1, by omega⟩‖ *
                    (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 := by positivity
              simpa only [mul_assoc] using
                mul_le_mul_of_nonneg_left hvalue' hnonneg
      _ = M N := by
            have hnNorm : ‖(((N + 1 : ℕ) : ℂ))‖ = (N : ℝ) + 1 := by
              rw [Complex.norm_natCast]
              norm_num [Real.norm_eq_abs, abs_of_nonneg]
            simp only [M, norm_mul, norm_pow, hnNorm]
            ring
  have hbase :=
    summable_d4BMCompletedEisensteinWeightedSignedWhittakerHorizontalFirstJet
      u nu negative x Y
  have hsum := hasDerivAt_tsum_of_isPreconnected hM isOpen_univ
    isPreconnected_univ hderiv hbound (Set.mem_univ x) hbase (Set.mem_univ x)
  unfold d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalFirstJetTail
    d4BMCompletedEisensteinSignedSqrtWhittakerHorizontalSecondJetTail
  simpa only [g, g'] using hsum

end
end RHTower
