import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelInteriorFirstZero
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyDivisorLift

/-!
# LI completed-Abel two-scale radial generating law

This module closes the full-divisor/full-mode transform behind route LI-CAB5.
For a positive interior squared mass `v` and a uniform generating parameter
`0 < s < 1/5`, the complete adjacent-current series is exactly a divided
difference of the first radial response of the shifted Xi moment tower at two
reciprocal scales.  Absolute product summability makes the divisor/mode
interchange unconditional.
-/

open Polynomial Real Filter Topology Set MeasureTheory Complex
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem hasSum_natSucc_mul_geometric
    {r : ℂ} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℂ) + 1) * r ^ n) ((1 - r)⁻¹ ^ (2 : ℕ)) := by
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hg := hasSum_geometric_of_norm_lt_one hr
  have h := hn.add hg
  have hne : 1 - r ≠ 0 := by
    intro hz
    have hr1 : r = 1 := (sub_eq_zero.mp hz).symm
    rw [hr1] at hr
    norm_num at hr
  have heq : r / (1 - r) ^ (2 : ℕ) + (1 - r)⁻¹ = (1 - r)⁻¹ ^ (2 : ℕ) := by
    field_simp [hne]
    ring
  rw [heq] at h
  simpa only [add_mul, one_mul] using h

private theorem norm_add_I_mul_div_sub_I_mul_le_three
    {a : ℝ} {α : ℂ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2)
    (hα : 4 < ‖α‖) :
    ‖((a : ℂ) + I * α) / ((a : ℂ) - I * α)‖ ≤ 3 := by
  have hIa : ‖I * α‖ = ‖α‖ := by simp
  have haC : ‖(a : ℂ)‖ = a := by simp [abs_of_nonneg ha0]
  have hnum : ‖(a : ℂ) + I * α‖ ≤ a + ‖α‖ := by
    calc
      ‖(a : ℂ) + I * α‖ ≤ ‖(a : ℂ)‖ + ‖I * α‖ := norm_add_le _ _
      _ = a + ‖α‖ := by rw [haC, hIa]
  have hden : ‖α‖ - a ≤ ‖(a : ℂ) - I * α‖ := by
    calc
      ‖α‖ - a = ‖I * α‖ - ‖(a : ℂ)‖ := by rw [hIa, haC]
      _ ≤ ‖I * α - (a : ℂ)‖ := norm_sub_norm_le _ _
      _ = ‖(a : ℂ) - I * α‖ := norm_sub_rev _ _
  have hdenpos : 0 < ‖(a : ℂ) - I * α‖ := by nlinarith
  rw [norm_div, div_le_iff₀ hdenpos]
  nlinarith

private theorem norm_xiHardEdgeCayleyPhase_le_three
    {v : ℝ} (_hv0 : 0 ≤ v) (hv4 : v ≤ 1 / 4) (q : XiZeroCopy) :
    ‖xiHardEdgeCayleyPhase (Real.sqrt v : ℂ) (xiSpectralPoint q)‖ ≤ 3 := by
  have hsqrt : Real.sqrt v ≤ 1 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  exact norm_add_I_mul_div_sub_I_mul_le_three (Real.sqrt_nonneg v) hsqrt
    (four_lt_norm_xiSpectralPoint q)

private theorem norm_xiHardEdgeCayleyPhase_inv_le_three
    {v : ℝ} (_hv0 : 0 ≤ v) (hv4 : v ≤ 1 / 4) (q : XiZeroCopy) :
    ‖(xiHardEdgeCayleyPhase (Real.sqrt v : ℂ) (xiSpectralPoint q))⁻¹‖ ≤ 3 := by
  have hsqrt : Real.sqrt v ≤ 1 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have h := norm_add_I_mul_div_sub_I_mul_le_three
    (α := -xiSpectralPoint q) (Real.sqrt_nonneg v) hsqrt
      (by simpa using four_lt_norm_xiSpectralPoint q)
  simpa only [xiHardEdgeCayleyPhase, inv_div, mul_neg, sub_eq_add_neg,
    neg_neg] using h

private theorem sqrt_add_I_mul_xiSpectralPoint_ne_zero
    {v : ℝ} (hv0 : 0 ≤ v) (q : XiZeroCopy) :
    (Real.sqrt v : ℂ) + I * xiSpectralPoint q ≠ 0 := by
  have hden : (v : ℂ) + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := by
    simpa [xiSquaredNode] using ofReal_add_xiSquaredNode_ne_zero hv0 q
  have hprod :
      ((Real.sqrt v : ℂ) + I * xiSpectralPoint q) *
        ((Real.sqrt v : ℂ) - I * xiSpectralPoint q) =
          (v : ℂ) + xiSpectralPoint q ^ (2 : ℕ) := by
    have hsqC : (Real.sqrt v : ℂ) ^ (2 : ℕ) = (v : ℂ) := by
      exact_mod_cast Real.sq_sqrt hv0
    rw [show I * xiSpectralPoint q = xiSpectralPoint q * I by ring]
    ring_nf
    rw [I_sq, hsqC]
    ring
  exact (mul_ne_zero_iff.mp (hprod.symm ▸ hden)).1

private theorem sqrt_sub_I_mul_xiSpectralPoint_ne_zero
    {v : ℝ} (hv0 : 0 ≤ v) (q : XiZeroCopy) :
    (Real.sqrt v : ℂ) - I * xiSpectralPoint q ≠ 0 := by
  have hden : (v : ℂ) + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := by
    simpa [xiSquaredNode] using ofReal_add_xiSquaredNode_ne_zero hv0 q
  have hprod :
      ((Real.sqrt v : ℂ) + I * xiSpectralPoint q) *
        ((Real.sqrt v : ℂ) - I * xiSpectralPoint q) =
          (v : ℂ) + xiSpectralPoint q ^ (2 : ℕ) := by
    have hsqC : (Real.sqrt v : ℂ) ^ (2 : ℕ) = (v : ℂ) := by
      exact_mod_cast Real.sq_sqrt hv0
    rw [show I * xiSpectralPoint q = xiSpectralPoint q * I by ring]
    ring_nf
    rw [I_sq, hsqC]
    ring
  exact (mul_ne_zero_iff.mp (hprod.symm ▸ hden)).2

/-- Phase-side closed form of one all-mode adjacent-current row. -/
private def liEvenCrossPhaseGeneratingAtom
    (v s : ℝ) (q : XiZeroCopy) : ℂ :=
  let u := xiHardEdgeCayleyPhase (Real.sqrt v : ℂ) (xiSpectralPoint q)
  let t : ℂ := (s : ℂ) ^ (2 : ℕ)
  (1 / (16 * (v : ℂ))) *
    (u * (u ^ (2 : ℕ) - 1) * (1 - t * u ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) +
      u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1) * (1 - t * u⁻¹ ^ (2 : ℕ))⁻¹ ^ (2 : ℕ))

private theorem hasSum_liEvenCrossSquareMassAdjacentFlux_mul_sq
    {v s : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (hs : 0 < s) (hs5 : s < 1 / 5) (q : XiZeroCopy) :
    HasSum (fun n : ℕ =>
      liEvenCrossSquareMassAdjacentFlux v n q * (((s : ℂ) ^ (2 : ℕ)) ^ n))
      (liEvenCrossPhaseGeneratingAtom v s q) := by
  let u : ℂ := xiHardEdgeCayleyPhase (Real.sqrt v : ℂ) (xiSpectralPoint q)
  let t : ℂ := (s : ℂ) ^ (2 : ℕ)
  have hu : ‖u‖ ≤ 3 := norm_xiHardEdgeCayleyPhase_le_three hv.le hv4 q
  have hui : ‖u⁻¹‖ ≤ 3 := norm_xiHardEdgeCayleyPhase_inv_le_three hv.le hv4 q
  have ht : ‖t‖ = s ^ (2 : ℕ) := by
    simp [t, abs_of_pos hs]
  have htu : ‖t * u ^ (2 : ℕ)‖ < 1 := by
    have hu2 : ‖u‖ ^ (2 : ℕ) ≤ 3 ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg u) hu 2
    have hs2 : s ^ (2 : ℕ) < (1 / 5 : ℝ) ^ (2 : ℕ) := by nlinarith
    calc
      ‖t * u ^ (2 : ℕ)‖ = s ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) := by
        simp [t, norm_pow, abs_of_pos hs]
      _ ≤ s ^ (2 : ℕ) * 3 ^ (2 : ℕ) := by gcongr
      _ < 1 := by nlinarith [sq_nonneg s]
  have htui : ‖t * u⁻¹ ^ (2 : ℕ)‖ < 1 := by
    have hu2 : ‖u⁻¹‖ ^ (2 : ℕ) ≤ 3 ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg u⁻¹) hui 2
    have hs2 : s ^ (2 : ℕ) < (1 / 5 : ℝ) ^ (2 : ℕ) := by nlinarith
    calc
      ‖t * u⁻¹ ^ (2 : ℕ)‖ = s ^ (2 : ℕ) * ‖u⁻¹‖ ^ (2 : ℕ) := by
        simp [t, norm_pow, abs_of_pos hs]
      _ ≤ s ^ (2 : ℕ) * 3 ^ (2 : ℕ) := by gcongr
      _ < 1 := by nlinarith [sq_nonneg s]
  have hsumU := hasSum_natSucc_mul_geometric htu
  have hsumUi := hasSum_natSucc_mul_geometric htui
  let cU : ℂ := (1 / (16 * (v : ℂ))) * u * (u ^ (2 : ℕ) - 1)
  let cUi : ℂ := (1 / (16 * (v : ℂ))) * u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1)
  have hsum := (hsumU.mul_left cU).add (hsumUi.mul_left cUi)
  have hplus := sqrt_add_I_mul_xiSpectralPoint_ne_zero hv.le q
  have hminus := sqrt_sub_I_mul_xiSpectralPoint_ne_zero hv.le q
  have hsqrt : Real.sqrt v ^ (2 : ℕ) = v := Real.sq_sqrt hv.le
  have hcoord :
      liEvenCrossCayleyAtSquareMass v q =
        xiHardEdgeCayleyCoordinate (Real.sqrt v : ℂ) (xiSpectralPoint q) := by
    rw [liEvenCrossCayleyAtSquareMass,
      xiHardEdgeCayleyCoordinate_xiSpectralPoint]
    rw [hsqrt]
  have hu_def :
      ((Real.sqrt v : ℂ) + I * xiSpectralPoint q) /
          ((Real.sqrt v : ℂ) - I * xiSpectralPoint q) = u := by
    rfl
  have hui_def :
      ((Real.sqrt v : ℂ) - I * xiSpectralPoint q) /
          ((Real.sqrt v : ℂ) + I * xiSpectralPoint q) = u⁻¹ := by
    dsimp only [u, xiHardEdgeCayleyPhase]
    exact (inv_div _ _).symm
  have hu0 : u ≠ 0 := by
    dsimp only [u, xiHardEdgeCayleyPhase]
    exact div_ne_zero hplus hminus
  have hterm (n : ℕ) :
      liEvenCrossSquareMassAdjacentFlux v n q * t ^ n =
        cU * (((n : ℂ) + 1) * (t * u ^ (2 : ℕ)) ^ n) +
          cUi * (((n : ℂ) + 1) * (t * u⁻¹ ^ (2 : ℕ)) ^ n) := by
    rw [liEvenCrossSquareMassAdjacentFlux, hcoord]
    rw [show 2 * ((n : ℤ) + 1) + 1 = ((2 * n + 3 : ℕ) : ℤ) by omega,
      show 2 * ((n : ℤ) + 1) - 1 = ((2 * n + 1 : ℕ) : ℤ) by omega]
    simp only [evalRealPolynomial, Polynomial.Chebyshev.map_T]
    rw [chebyshevT_eval_xiHardEdgeCayleyCoordinate hplus hminus,
      chebyshevT_eval_xiHardEdgeCayleyCoordinate hplus hminus,
      hu_def, hui_def]
    dsimp only [cU, cUi]
    rw [mul_pow]
    have hp3 : u ^ (2 * n + 3) = u ^ (3 : ℕ) * (u ^ (2 : ℕ)) ^ n := by
      rw [show 2 * n + 3 = 3 + 2 * n by omega, pow_add, pow_mul]
    have hp1 : u ^ (2 * n + 1) = u * (u ^ (2 : ℕ)) ^ n := by
      rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add, pow_mul]
      simp
    have hip3 : u⁻¹ ^ (2 * n + 3) = u⁻¹ ^ (3 : ℕ) * (u⁻¹ ^ (2 : ℕ)) ^ n := by
      rw [show 2 * n + 3 = 3 + 2 * n by omega, pow_add, pow_mul]
    have hip1 : u⁻¹ ^ (2 * n + 1) = u⁻¹ * (u⁻¹ ^ (2 : ℕ)) ^ n := by
      rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add, pow_mul]
      simp
    rw [hp3, hp1, hip3, hip1]
    field_simp [hv.ne', hu0]
    ring
  have hsum' := HasSum.congr_fun hsum (fun n => hterm n)
  have hout :
      cU * (1 - t * u ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) + cUi * (1 - t * u⁻¹ ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) =
        liEvenCrossPhaseGeneratingAtom v s q := by
    dsimp only [u, t, cU, cUi, liEvenCrossPhaseGeneratingAtom]
    ring
  rw [hout] at hsum'
  simpa only [t] using hsum'

/-- Reciprocal scale above the current mass. -/
def liEvenCrossReciprocalScaleUp (v s : ℝ) : ℝ :=
  v * ((1 + s) / (1 - s)) ^ (2 : ℕ)

/-- Reciprocal scale below the current mass. -/
def liEvenCrossReciprocalScaleDown (v s : ℝ) : ℝ :=
  v * ((1 - s) / (1 + s)) ^ (2 : ℕ)

/-- Rational squared-node form of one complete all-mode row. -/
def liEvenCrossTwoScaleRationalAtom (v s : ℝ) (q : XiZeroCopy) : ℂ :=
  -2 * (1 + (s : ℂ) ^ (2 : ℕ)) / (1 - (s : ℂ) ^ (2 : ℕ)) ^ (3 : ℕ) *
    (xiSquaredNode q * ((v : ℂ) ^ (2 : ℕ) - xiSquaredNode q ^ (2 : ℕ)) /
      ((xiSquaredNode q + (liEvenCrossReciprocalScaleUp v s : ℂ)) ^ (2 : ℕ) *
        (xiSquaredNode q + (liEvenCrossReciprocalScaleDown v s : ℂ)) ^ (2 : ℕ)))

/-- Resolvent-side form before factorization into reciprocal scales. -/
private def liEvenCrossResolventGeneratingAtom (v s : ℝ) (q : XiZeroCopy) : ℂ :=
  -2 * xiShiftedReciprocalSquare v q *
      (1 - (v : ℂ) * xiShiftedReciprocalSquare v q) *
      (2 * ((v : ℂ) * xiShiftedReciprocalSquare v q) - 1) *
      (1 - (s : ℂ) ^ (4 : ℕ)) /
    ((1 - (s : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) +
      16 * (s : ℂ) ^ (2 : ℕ) * ((v : ℂ) * xiShiftedReciprocalSquare v q) *
        (1 - (v : ℂ) * xiShiftedReciprocalSquare v q)) ^ (2 : ℕ)

private theorem add_inv_sq_eq_common_inv_sq
    {p q A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) :
    p * A⁻¹ ^ (2 : ℕ) + q * B⁻¹ ^ (2 : ℕ) =
      (p * B ^ (2 : ℕ) + q * A ^ (2 : ℕ)) * (A * B)⁻¹ ^ (2 : ℕ) := by
  field_simp [hA, hB]

private theorem phaseAdjacent_eq_resolvent_algebra
    {u t x : ℂ} (hu : u ≠ 0)
    (hdu : 1 - t * u ^ (2 : ℕ) ≠ 0) (hdui : 1 - t * u⁻¹ ^ (2 : ℕ) ≠ 0)
    (hx : x = (2 + u + u⁻¹) / 4) :
    (1 / 16) *
        (u * (u ^ (2 : ℕ) - 1) * (1 - t * u ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) +
          u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1) * (1 - t * u⁻¹ ^ (2 : ℕ))⁻¹ ^ (2 : ℕ)) =
      -2 * x * (1 - x) * (2 * x - 1) * (1 - t ^ (2 : ℕ)) /
        ((1 - t) ^ (2 : ℕ) + 16 * t * x * (1 - x)) ^ (2 : ℕ) := by
  have hc : 2 * x - 1 = (u + u⁻¹) / 2 := by
    rw [hx]
    field_simp [hu]
    ring
  have hD :
      (1 - t) ^ (2 : ℕ) + 16 * t * x * (1 - x) =
        (1 - t * u ^ (2 : ℕ)) * (1 - t * u⁻¹ ^ (2 : ℕ)) := by
    rw [hx]
    field_simp [hu]
    ring
  let A := 1 - t * u ^ (2 : ℕ)
  let B := 1 - t * u⁻¹ ^ (2 : ℕ)
  have hcommon := add_inv_sq_eq_common_inv_sq
    (p := u * (u ^ (2 : ℕ) - 1)) (q := u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1)) hdu hdui
  have hpoly :
      (1 / 16) *
          (u * (u ^ (2 : ℕ) - 1) * B ^ (2 : ℕ) +
            u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1) * A ^ (2 : ℕ)) =
        -2 * x * (1 - x) * (2 * x - 1) * (1 - t ^ (2 : ℕ)) := by
    dsimp only [A, B]
    rw [hx]
    field_simp [hu]
    ring
  calc
    (1 / 16) *
        (u * (u ^ (2 : ℕ) - 1) * (1 - t * u ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) +
          u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1) * (1 - t * u⁻¹ ^ (2 : ℕ))⁻¹ ^ (2 : ℕ)) =
      (1 / 16) *
        (u * (u ^ (2 : ℕ) - 1) * B ^ (2 : ℕ) +
          u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1) * A ^ (2 : ℕ)) * (A * B)⁻¹ ^ (2 : ℕ) := by
        rw [hcommon]
        ring
    _ = (-2 * x * (1 - x) * (2 * x - 1) * (1 - t ^ (2 : ℕ))) *
        (A * B)⁻¹ ^ (2 : ℕ) := by rw [hpoly]
    _ = -2 * x * (1 - x) * (2 * x - 1) * (1 - t ^ (2 : ℕ)) /
        ((1 - t) ^ (2 : ℕ) + 16 * t * x * (1 - x)) ^ (2 : ℕ) := by
      rw [hD]
      simp only [div_eq_mul_inv, inv_pow, mul_pow]
      dsimp only [A, B]
      rw [show (u ^ (2 : ℕ))⁻¹ = u⁻¹ ^ (2 : ℕ) by rw [inv_pow]]

private theorem liEvenCrossPhaseGeneratingAtom_eq_resolventAtom
    {v s : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (hs : 0 < s) (hs5 : s < 1 / 5) (q : XiZeroCopy) :
    liEvenCrossPhaseGeneratingAtom v s q =
      liEvenCrossResolventGeneratingAtom v s q := by
  let a : ℂ := Real.sqrt v
  let α : ℂ := xiSpectralPoint q
  let u : ℂ := xiHardEdgeCayleyPhase a α
  let t : ℂ := (s : ℂ) ^ (2 : ℕ)
  let r : ℂ := xiShiftedReciprocalSquare v q
  let x : ℂ := (v : ℂ) * r
  have hplus : a + I * α ≠ 0 := sqrt_add_I_mul_xiSpectralPoint_ne_zero hv.le q
  have hminus : a - I * α ≠ 0 := sqrt_sub_I_mul_xiSpectralPoint_ne_zero hv.le q
  have hu0 : u ≠ 0 := by
    dsimp only [u, xiHardEdgeCayleyPhase]
    exact div_ne_zero hplus hminus
  have hu : ‖u‖ ≤ 3 := norm_xiHardEdgeCayleyPhase_le_three hv.le hv4 q
  have hui : ‖u⁻¹‖ ≤ 3 := norm_xiHardEdgeCayleyPhase_inv_le_three hv.le hv4 q
  have htu : ‖t * u ^ (2 : ℕ)‖ < 1 := by
    have hu2 : ‖u‖ ^ (2 : ℕ) ≤ 3 ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg u) hu 2
    have hs2 : s ^ (2 : ℕ) < (1 / 5 : ℝ) ^ (2 : ℕ) := by nlinarith
    calc
      ‖t * u ^ (2 : ℕ)‖ = s ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) := by simp [t, norm_pow, abs_of_pos hs]
      _ ≤ s ^ (2 : ℕ) * 3 ^ (2 : ℕ) := by gcongr
      _ < 1 := by nlinarith [sq_nonneg s]
  have htui : ‖t * u⁻¹ ^ (2 : ℕ)‖ < 1 := by
    have hu2 : ‖u⁻¹‖ ^ (2 : ℕ) ≤ 3 ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg u⁻¹) hui 2
    have hs2 : s ^ (2 : ℕ) < (1 / 5 : ℝ) ^ (2 : ℕ) := by nlinarith
    calc
      ‖t * u⁻¹ ^ (2 : ℕ)‖ = s ^ (2 : ℕ) * ‖u⁻¹‖ ^ (2 : ℕ) := by simp [t, norm_pow, abs_of_pos hs]
      _ ≤ s ^ (2 : ℕ) * 3 ^ (2 : ℕ) := by gcongr
      _ < 1 := by nlinarith [sq_nonneg s]
  have hdu : 1 - t * u ^ (2 : ℕ) ≠ 0 := by
    intro h
    have : t * u ^ (2 : ℕ) = 1 := (sub_eq_zero.mp h).symm
    rw [this] at htu
    norm_num at htu
  have hdui : 1 - t * u⁻¹ ^ (2 : ℕ) ≠ 0 := by
    intro h
    have : t * u⁻¹ ^ (2 : ℕ) = 1 := (sub_eq_zero.mp h).symm
    rw [this] at htui
    norm_num at htui
  have hsqrt : Real.sqrt v ^ (2 : ℕ) = v := Real.sq_sqrt hv.le
  have hcoord :
      liEvenCrossCayleyAtSquareMass v q =
        xiHardEdgeCayleyCoordinate a α := by
    dsimp only [a, α]
    rw [liEvenCrossCayleyAtSquareMass,
      xiHardEdgeCayleyCoordinate_xiSpectralPoint, hsqrt]
  have hphase := chebyshevT_eval_xiHardEdgeCayleyCoordinate hplus hminus 1
  have hui_eq : (a - I * α) / (a + I * α) = u⁻¹ := by
    dsimp only [u, xiHardEdgeCayleyPhase]
    exact (inv_div _ _).symm
  have hc : 2 * x - 1 = (u + u⁻¹) / 2 := by
    have hphase' : xiHardEdgeCayleyCoordinate a α = u / 2 + u⁻¹ / 2 := by
      rw [show ((1 : ℕ) : ℤ) = 1 by norm_num,
        Polynomial.Chebyshev.T_one] at hphase
      simp only [Polynomial.eval_X, pow_one] at hphase
      rw [hui_eq] at hphase
      simpa only [u, xiHardEdgeCayleyPhase] using hphase
    dsimp only [x, r]
    rw [show 2 * ((v : ℂ) * xiShiftedReciprocalSquare v q) - 1 =
        liEvenCrossCayleyAtSquareMass v q by
      simp only [liEvenCrossCayleyAtSquareMass]
      push_cast
      ring]
    rw [hcoord, hphase']
    ring
  have hx : x = (2 + u + u⁻¹) / 4 := by
    apply (eq_div_iff (by norm_num : (4 : ℂ) ≠ 0)).2
    linear_combination 2 * hc
  have halg := phaseAdjacent_eq_resolvent_algebra hu0 hdu hdui hx
  calc
    liEvenCrossPhaseGeneratingAtom v s q =
        (v : ℂ)⁻¹ *
          ((1 / 16) *
            (u * (u ^ (2 : ℕ) - 1) * (1 - t * u ^ (2 : ℕ))⁻¹ ^ (2 : ℕ) +
              u⁻¹ * (u⁻¹ ^ (2 : ℕ) - 1) * (1 - t * u⁻¹ ^ (2 : ℕ))⁻¹ ^ (2 : ℕ))) := by
      dsimp only [liEvenCrossPhaseGeneratingAtom, u, t, a, α]
      have hvC : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv.ne'
      field_simp [hvC]
    _ = (v : ℂ)⁻¹ *
        (-2 * x * (1 - x) * (2 * x - 1) * (1 - t ^ (2 : ℕ)) /
          ((1 - t) ^ (2 : ℕ) + 16 * t * x * (1 - x)) ^ (2 : ℕ)) := by rw [halg]
    _ = liEvenCrossResolventGeneratingAtom v s q := by
      dsimp only [liEvenCrossResolventGeneratingAtom, x, r, t]
      have hvC : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv.ne'
      field_simp [hvC]

private theorem resolventTwoScaleFactor_algebra
    {v b A B t : ℂ}
    (hvb : v + b ≠ 0) (hbA : b + A ≠ 0) (hbB : b + B ≠ 0)
    (ht : 1 - t ≠ 0) :
    -2 * (v + b)⁻¹ * (1 - v / (v + b)) *
          (2 * (v / (v + b)) - 1) * (1 - t ^ (2 : ℕ)) /
        (((1 - t) ^ (2 : ℕ) * (b + A) * (b + B) / (v + b) ^ (2 : ℕ)) ^ (2 : ℕ)) =
      -2 * (1 + t) / (1 - t) ^ (3 : ℕ) *
        (b * (v ^ (2 : ℕ) - b ^ (2 : ℕ)) / ((b + A) ^ (2 : ℕ) * (b + B) ^ (2 : ℕ))) := by
  field_simp [hvb, hbA, hbB, ht]
  ring

private theorem liEvenCrossResolventGeneratingAtom_eq_rationalAtom
    {v s : ℝ} (hv : 0 < v) (hs : 0 < s) (hs5 : s < 1 / 5)
    (q : XiZeroCopy) :
    liEvenCrossResolventGeneratingAtom v s q =
      liEvenCrossTwoScaleRationalAtom v s q := by
  let b : ℂ := xiSquaredNode q
  let A : ℂ := liEvenCrossReciprocalScaleUp v s
  let B : ℂ := liEvenCrossReciprocalScaleDown v s
  let t : ℂ := (s : ℂ) ^ (2 : ℕ)
  have hsm : (1 - s : ℝ) ≠ 0 := by nlinarith
  have hsp : (1 + s : ℝ) ≠ 0 := by nlinarith
  have hsmC : (1 - (s : ℂ)) ≠ 0 := by exact_mod_cast hsm
  have hspC : (1 + (s : ℂ)) ≠ 0 := by exact_mod_cast hsp
  have ht1 : (1 - t : ℂ) ≠ 0 := by
    dsimp only [t]
    norm_cast
    nlinarith [sq_nonneg s]
  have hApos : 0 < liEvenCrossReciprocalScaleUp v s := by
    rw [liEvenCrossReciprocalScaleUp]
    have hsmpos : 0 < 1 - s := by nlinarith
    have hsppos : 0 < 1 + s := by nlinarith
    positivity
  have hBpos : 0 < liEvenCrossReciprocalScaleDown v s := by
    rw [liEvenCrossReciprocalScaleDown]
    have hsmpos : 0 < 1 - s := by nlinarith
    have hsppos : 0 < 1 + s := by nlinarith
    positivity
  have hvb : (v : ℂ) + b ≠ 0 := by
    simpa only [b] using ofReal_add_xiSquaredNode_ne_zero hv.le q
  have hbA : b + A ≠ 0 := by
    simpa only [b, A, add_comm] using ofReal_add_xiSquaredNode_ne_zero hApos.le q
  have hbB : b + B ≠ 0 := by
    simpa only [b, B, add_comm] using ofReal_add_xiSquaredNode_ne_zero hBpos.le q
  have hr : xiShiftedReciprocalSquare v q = ((v : ℂ) + b)⁻¹ := by
    simpa only [b] using xiShiftedReciprocalSquare_eq_inv hv.le q
  have hfactor :
      (1 - t) ^ (2 : ℕ) + 16 * t * ((v : ℂ) / ((v : ℂ) + b)) *
          (1 - (v : ℂ) / ((v : ℂ) + b)) =
        (1 - t) ^ (2 : ℕ) * (b + A) * (b + B) / ((v : ℂ) + b) ^ (2 : ℕ) := by
    dsimp only [t, A, B, liEvenCrossReciprocalScaleUp,
      liEvenCrossReciprocalScaleDown]
    push_cast
    field_simp [hsmC, hspC, hvb]
    ring
  have halg := resolventTwoScaleFactor_algebra hvb hbA hbB ht1
  calc
    liEvenCrossResolventGeneratingAtom v s q =
        -2 * ((v : ℂ) + b)⁻¹ *
            (1 - (v : ℂ) / ((v : ℂ) + b)) *
            (2 * ((v : ℂ) / ((v : ℂ) + b)) - 1) * (1 - t ^ (2 : ℕ)) /
          (((1 - t) ^ (2 : ℕ) * (b + A) * (b + B) /
            ((v : ℂ) + b) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
      rw [liEvenCrossResolventGeneratingAtom, hr]
      rw [show (v : ℂ) * ((v : ℂ) + b)⁻¹ =
          (v : ℂ) / ((v : ℂ) + b) by ring]
      rw [hfactor]
      dsimp only [t]
      ring
    _ = -2 * (1 + t) / (1 - t) ^ (3 : ℕ) *
        (b * ((v : ℂ) ^ (2 : ℕ) - b ^ (2 : ℕ)) /
          ((b + A) ^ (2 : ℕ) * (b + B) ^ (2 : ℕ))) := halg
    _ = liEvenCrossTwoScaleRationalAtom v s q := by
      dsimp only [liEvenCrossTwoScaleRationalAtom, b, A, B, t]

private theorem norm_eval_chebyshevU_complex_le_five_pow
    {z : ℂ} (hz : ‖z‖ ≤ 2) (n : ℕ) :
    ‖(Polynomial.Chebyshev.U ℂ (n : ℤ)).eval z‖ ≤ (5 : ℝ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [show ((1 : ℕ) : ℤ) = 1 by norm_num,
        Polynomial.Chebyshev.U_one]
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
        norm_mul]
      norm_num
      nlinarith [norm_nonneg z]
  | more n h0 h1 =>
      have h1' :
          ‖(Polynomial.Chebyshev.U ℂ ((n : ℤ) + 1)).eval z‖ ≤
            (5 : ℝ) ^ (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using h1
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X]
      calc
        ‖2 * z * (Polynomial.Chebyshev.U ℂ ((n : ℤ) + 1)).eval z -
            (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval z‖ ≤
          ‖2 * z * (Polynomial.Chebyshev.U ℂ ((n : ℤ) + 1)).eval z‖ +
            ‖(Polynomial.Chebyshev.U ℂ (n : ℤ)).eval z‖ := norm_sub_le _ _
        _ = 2 * ‖z‖ *
              ‖(Polynomial.Chebyshev.U ℂ ((n : ℤ) + 1)).eval z‖ +
            ‖(Polynomial.Chebyshev.U ℂ (n : ℤ)).eval z‖ := by
              simp only [norm_mul]
              norm_num
        _ ≤ 2 * 2 * (5 : ℝ) ^ (n + 1) + (5 : ℝ) ^ n := by gcongr
        _ ≤ (5 : ℝ) ^ (n + 2) := by
          rw [show (5 : ℝ) ^ (n + 2) = 25 * 5 ^ n by
            rw [show n + 2 = n + 1 + 1 by omega, pow_succ, pow_succ]; ring,
            show (5 : ℝ) ^ (n + 1) = 5 * 5 ^ n by rw [pow_succ]; ring]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) n]

private theorem norm_liEvenCrossSquareMassAdjacentFlux_le
    {v : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (n : ℕ) (q : XiZeroCopy) :
    ‖liEvenCrossSquareMassAdjacentFlux v n q‖ ≤
      10 * ((n : ℝ) + 1) * 25 ^ n * ‖xiZeroCopyReciprocalSquare q‖ := by
  let r := xiShiftedReciprocalSquare v q
  let x : ℂ := (v : ℂ) * r
  let z : ℂ := 2 * x - 1
  have hr : ‖r‖ ≤ ‖xiZeroCopyReciprocalSquare q‖ :=
    norm_xiShiftedReciprocalSquare_le hv.le q
  have hraw : ‖xiZeroCopyReciprocalSquare q‖ < 2 / 41 :=
    norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q
  have hx : ‖x‖ ≤ 1 / 82 := by
    calc
      ‖x‖ = v * ‖r‖ := by simp [x, abs_of_pos hv]
      _ ≤ v * ‖xiZeroCopyReciprocalSquare q‖ := by gcongr
      _ ≤ (1 / 4 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ := by gcongr
      _ ≤ 1 / 82 := by nlinarith [norm_nonneg (xiZeroCopyReciprocalSquare q)]
  have hz : ‖z‖ ≤ 2 := by
    calc
      ‖z‖ = ‖2 * x - 1‖ := rfl
      _ ≤ ‖2 * x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_mul]
        norm_num
        nlinarith
  have hU := norm_eval_chebyshevU_complex_le_five_pow hz (2 * n + 1)
  have hEval :
      evalRealPolynomial (liEvenCrossUnitFluxQuotient n) x =
        -((n : ℂ) + 1) * (1 - x) *
          (Polynomial.Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval z := by
    have hC :
        evalRealPolynomial (-((n : Polynomial ℝ) + 1)) x =
          -((n : ℂ) + 1) := by
      simp [evalRealPolynomial]
    have hlin : evalRealPolynomial (1 - X : Polynomial ℝ) x = 1 - x := by
      simp [evalRealPolynomial]
    have hcomp :
        evalRealPolynomial
            ((Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).comp
              liEvenCrossUnitAffine) x =
          (Polynomial.Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval z := by
      rw [evalRealPolynomial_comp_apply]
      simp [liEvenCrossUnitAffine, evalRealPolynomial, z]
    rw [liEvenCrossUnitFluxQuotient_eq_oddChebyshev]
    rw [evalRealPolynomial_mul, evalRealPolynomial_mul, hC, hlin, hcomp]
  rw [liEvenCrossSquareMassAdjacentFlux_eq_unitFluxQuotient hv n q]
  change ‖r * evalRealPolynomial (liEvenCrossUnitFluxQuotient n) x‖ ≤ _
  rw [norm_mul, hEval, norm_mul, norm_mul]
  have hone : ‖1 - x‖ ≤ 2 := by
    calc
      ‖1 - x‖ ≤ ‖(1 : ℂ)‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num; nlinarith
  have hpow : (5 : ℝ) ^ (2 * n + 1) = 5 * 25 ^ n := by
    rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add, pow_mul]
    norm_num
  rw [hpow] at hU
  have hcast : ‖-((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [norm_neg]
    convert norm_natCast (α := ℂ) (n + 1) using 1 <;> norm_num
  rw [hcast]
  calc
    ‖r‖ * (((n : ℝ) + 1) * ‖1 - x‖ *
        ‖(Polynomial.Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval z‖) ≤
      ‖xiZeroCopyReciprocalSquare q‖ * (((n : ℝ) + 1) * ‖1 - x‖ *
        ‖(Polynomial.Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval z‖) := by
          gcongr
    _ ≤ ‖xiZeroCopyReciprocalSquare q‖ * (((n : ℝ) + 1) * 2 *
        ‖(Polynomial.Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval z‖) := by
          gcongr
    _ ≤ ‖xiZeroCopyReciprocalSquare q‖ * (((n : ℝ) + 1) * 2 *
        (5 * 25 ^ n)) := by gcongr
    _ = 10 * ((n : ℝ) + 1) * 25 ^ n *
        ‖xiZeroCopyReciprocalSquare q‖ := by ring

private theorem summable_liEvenCrossGeneratingFlux_prod
    {v s : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (hs : 0 < s) (hs5 : s < 1 / 5) :
    Summable (fun p : XiZeroCopy × ℕ =>
      liEvenCrossSquareMassAdjacentFlux v p.2 p.1 * (((s : ℂ) ^ (2 : ℕ)) ^ p.2)) := by
  let ratio : ℝ := 25 * s ^ (2 : ℕ)
  have hratio0 : 0 ≤ ratio := by positivity
  have hratio1 : ratio < 1 := by
    dsimp only [ratio]
    nlinarith [sq_nonneg s]
  have hratioNorm : ‖ratio‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hratio0]; exact hratio1
  have hn := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hratioNorm
  have hg : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_norm_lt_one hratioNorm
  have hw0 : Summable (fun n : ℕ => ((n : ℝ) + 1) * ratio ^ n) := by
    have h := hn.add hg
    simpa only [pow_one, add_mul, one_mul] using h
  have hw : Summable (fun n : ℕ => 10 * ((n : ℝ) + 1) * ratio ^ n) := by
    simpa only [mul_assoc] using hw0.mul_left 10
  have hbase := summable_norm_xiZeroCopyReciprocalSquare
  refine Summable.of_norm_bounded
    (g := fun p : XiZeroCopy × ℕ =>
      ‖xiZeroCopyReciprocalSquare p.1‖ *
        (10 * ((p.2 : ℝ) + 1) * ratio ^ p.2)) ?_ ?_
  · exact hbase.mul_of_nonneg hw (fun q => norm_nonneg _)
      (fun n => mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (pow_nonneg hratio0 n))
  · intro p
    rw [norm_mul, norm_pow]
    have hflux := norm_liEvenCrossSquareMassAdjacentFlux_le hv hv4 p.2 p.1
    have hsNorm : ‖(s : ℂ)‖ ^ (2 : ℕ) = s ^ (2 : ℕ) := by simp [abs_of_pos hs]
    calc
      ‖liEvenCrossSquareMassAdjacentFlux v p.2 p.1‖ *
          ‖(s : ℂ) ^ (2 : ℕ)‖ ^ p.2 ≤
        (10 * ((p.2 : ℝ) + 1) * 25 ^ p.2 *
          ‖xiZeroCopyReciprocalSquare p.1‖) * (s ^ (2 : ℕ)) ^ p.2 := by
            rw [norm_pow, hsNorm]
            gcongr
      _ = ‖xiZeroCopyReciprocalSquare p.1‖ *
          (10 * ((p.2 : ℝ) + 1) * ratio ^ p.2) := by
            dsimp only [ratio]
            rw [mul_pow]
            ring

/-- The complete divisor-by-mode adjacent-current series may be interchanged, and every
mode row collapses to its two-scale squared-node atom.  This is the absolute-convergence
step needed before the Li current can be reduced to shifted source data. -/
theorem liEvenCrossSquareMassAdjacentFlux_generating_eq_twoScaleAtom_tsum
    {v s : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (hs : 0 < s) (hs5 : s < 1 / 5) :
    (∑' n : ℕ, (∑' q : XiZeroCopy,
        liEvenCrossSquareMassAdjacentFlux v n q) * (((s : ℂ) ^ (2 : ℕ)) ^ n)) =
      ∑' q : XiZeroCopy, liEvenCrossTwoScaleRationalAtom v s q := by
  let F : XiZeroCopy → ℕ → ℂ := fun q n =>
    liEvenCrossSquareMassAdjacentFlux v n q * (((s : ℂ) ^ (2 : ℕ)) ^ n)
  have hprod : Summable (fun p : XiZeroCopy × ℕ => F p.1 p.2) := by
    simpa only [F] using summable_liEvenCrossGeneratingFlux_prod hv hv4 hs hs5
  have hinner (q : XiZeroCopy) :
      (∑' n : ℕ, F q n) = liEvenCrossTwoScaleRationalAtom v s q := by
    calc
      (∑' n : ℕ, F q n) = liEvenCrossPhaseGeneratingAtom v s q :=
        (hasSum_liEvenCrossSquareMassAdjacentFlux_mul_sq hv hv4 hs hs5 q).tsum_eq
      _ = liEvenCrossResolventGeneratingAtom v s q :=
        liEvenCrossPhaseGeneratingAtom_eq_resolventAtom hv hv4 hs hs5 q
      _ = liEvenCrossTwoScaleRationalAtom v s q :=
        liEvenCrossResolventGeneratingAtom_eq_rationalAtom hv hs hs5 q
  calc
    (∑' n : ℕ, (∑' q : XiZeroCopy,
        liEvenCrossSquareMassAdjacentFlux v n q) * (((s : ℂ) ^ (2 : ℕ)) ^ n)) =
        ∑' n : ℕ, ∑' q : XiZeroCopy, F q n := by
      apply tsum_congr
      intro n
      rw [tsum_mul_right]
    _ = ∑' q : XiZeroCopy, ∑' n : ℕ, F q n := hprod.tsum_comm
    _ = ∑' q : XiZeroCopy, liEvenCrossTwoScaleRationalAtom v s q :=
      tsum_congr hinner

/-- Radial first-response combination of the first two shifted Xi divisor moments. -/
def liEvenCrossComplexRadialDilationResponse (y : ℝ) : ℂ :=
  (y : ℂ) *
    (xiShiftedReciprocalMoment y 0 -
      (y : ℂ) * xiShiftedReciprocalMoment y 1)

/-- Real radial first-response combination.  Shifted Xi moments are real on the
nonnegative base ray, so this is the real form used by the Li current. -/
def liEvenCrossRadialDilationResponse (y : ℝ) : ℝ :=
  y *
    ((xiShiftedReciprocalMoment y 0).re -
      y * (xiShiftedReciprocalMoment y 1).re)

/-- Exact first-response identity for the complete squared Xi divisor. -/
theorem tsum_xiSquaredNode_div_add_shift_sq_eq_shiftedMoment_response
    {y : ℝ} (hy : 0 ≤ y) :
    (∑' q : XiZeroCopy,
        xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ)) =
      xiShiftedReciprocalMoment y 0 -
        (y : ℂ) * xiShiftedReciprocalMoment y 1 := by
  have h0 := summable_xiShiftedReciprocalSquare_pow hy 0
  have h1 := summable_xiShiftedReciprocalSquare_pow hy 1
  have h0' : Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q) := by
    simpa using h0
  have h1' : Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q ^ (2 : ℕ)) := by
    simpa using h1
  have hatom (q : XiZeroCopy) :
      xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ) =
        xiShiftedReciprocalSquare y q -
          (y : ℂ) * xiShiftedReciprocalSquare y q ^ (2 : ℕ) := by
    have hne : (y : ℂ) + xiSquaredNode q ≠ 0 :=
      ofReal_add_xiSquaredNode_ne_zero hy q
    rw [xiShiftedReciprocalSquare_eq_inv hy q]
    calc
      xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ) =
          xiSquaredNode q / ((y : ℂ) + xiSquaredNode q) ^ (2 : ℕ) := by
            rw [add_comm (xiSquaredNode q) (y : ℂ)]
      _ = ((y : ℂ) + xiSquaredNode q)⁻¹ -
          (y : ℂ) * ((y : ℂ) + xiSquaredNode q)⁻¹ ^ (2 : ℕ) := by
            field_simp [hne]
            ring
  calc
    (∑' q : XiZeroCopy,
        xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ)) =
      ∑' q : XiZeroCopy,
        (xiShiftedReciprocalSquare y q -
          (y : ℂ) * xiShiftedReciprocalSquare y q ^ (2 : ℕ)) := tsum_congr hatom
    _ = (∑' q : XiZeroCopy, xiShiftedReciprocalSquare y q) -
        ∑' q : XiZeroCopy, (y : ℂ) * xiShiftedReciprocalSquare y q ^ (2 : ℕ) := by
      rw [h0'.tsum_sub (h1'.mul_left (y : ℂ))]
    _ = xiShiftedReciprocalMoment y 0 -
        (y : ℂ) * xiShiftedReciprocalMoment y 1 := by
      rw [tsum_mul_left]
      simp [xiShiftedReciprocalMoment]

theorem summable_xiSquaredNode_div_add_shift_sq
    {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun q : XiZeroCopy =>
      xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ)) := by
  have h0 : Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q) := by
    simpa using summable_xiShiftedReciprocalSquare_pow hy 0
  have h1 : Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q ^ (2 : ℕ)) := by
    simpa using summable_xiShiftedReciprocalSquare_pow hy 1
  refine (h0.sub (h1.mul_left (y : ℂ))).congr fun q => ?_
  have hne : (y : ℂ) + xiSquaredNode q ≠ 0 :=
    ofReal_add_xiSquaredNode_ne_zero hy q
  rw [xiShiftedReciprocalSquare_eq_inv hy q]
  calc
    ((y : ℂ) + xiSquaredNode q)⁻¹ -
        (y : ℂ) * ((y : ℂ) + xiSquaredNode q)⁻¹ ^ (2 : ℕ) =
      xiSquaredNode q / ((y : ℂ) + xiSquaredNode q) ^ (2 : ℕ) := by
        field_simp [hne]
        ring
    _ = xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ) := by
      rw [add_comm (y : ℂ) (xiSquaredNode q)]

private theorem twoScaleRationalAtom_partialFraction
    {v b A B t : ℂ} (hAB : A * B = v ^ (2 : ℕ))
    (hABne : A - B ≠ 0) (hbA : b + A ≠ 0) (hbB : b + B ≠ 0) :
    -2 * (1 + t) / (1 - t) ^ (3 : ℕ) *
        (b * (v ^ (2 : ℕ) - b ^ (2 : ℕ)) / ((b + A) ^ (2 : ℕ) * (b + B) ^ (2 : ℕ))) =
      (2 * (1 + t) / (1 - t) ^ (3 : ℕ)) *
        ((A * (b / (b + A) ^ (2 : ℕ)) - B * (b / (b + B) ^ (2 : ℕ))) /
          (A - B)) := by
  have hinner :
      b * (v ^ (2 : ℕ) - b ^ (2 : ℕ)) / ((b + A) ^ (2 : ℕ) * (b + B) ^ (2 : ℕ)) =
        (B * (b / (b + B) ^ (2 : ℕ)) - A * (b / (b + A) ^ (2 : ℕ))) /
          (A - B) := by
    rw [← hAB]
    field_simp [hABne, hbA, hbB]
    ring
  rw [hinner]
  ring

private theorem liEvenCrossTwoScaleRationalAtom_eq_responseAtom
    {v s : ℝ} (hv : 0 < v) (hs : 0 < s) (hs5 : s < 1 / 5)
    (q : XiZeroCopy) :
    liEvenCrossTwoScaleRationalAtom v s q =
      (2 * (1 + (s : ℂ) ^ (2 : ℕ)) / (1 - (s : ℂ) ^ (2 : ℕ)) ^ (3 : ℕ)) *
        (((liEvenCrossReciprocalScaleUp v s : ℂ) *
              (xiSquaredNode q /
                (xiSquaredNode q + (liEvenCrossReciprocalScaleUp v s : ℂ)) ^ (2 : ℕ)) -
            (liEvenCrossReciprocalScaleDown v s : ℂ) *
              (xiSquaredNode q /
                (xiSquaredNode q + (liEvenCrossReciprocalScaleDown v s : ℂ)) ^ (2 : ℕ))) /
          ((liEvenCrossReciprocalScaleUp v s : ℂ) -
            (liEvenCrossReciprocalScaleDown v s : ℂ))) := by
  let A : ℝ := liEvenCrossReciprocalScaleUp v s
  let B : ℝ := liEvenCrossReciprocalScaleDown v s
  have hsm : (1 - s : ℝ) ≠ 0 := by nlinarith
  have hsp : (1 + s : ℝ) ≠ 0 := by nlinarith
  have hApos : 0 < A := by
    dsimp only [A, liEvenCrossReciprocalScaleUp]
    positivity
  have hBpos : 0 < B := by
    dsimp only [B, liEvenCrossReciprocalScaleDown]
    have hsm : 0 < 1 - s := by nlinarith
    have hsp : 0 < 1 + s := by nlinarith
    positivity
  have hABreal : A * B = v ^ (2 : ℕ) := by
    dsimp only [A, B, liEvenCrossReciprocalScaleUp,
      liEvenCrossReciprocalScaleDown]
    field_simp [hsm, hsp]
  have hdiff : A - B ≠ 0 := by
    intro h
    have hEq : A = B := sub_eq_zero.mp h
    dsimp only [A, B, liEvenCrossReciprocalScaleUp,
      liEvenCrossReciprocalScaleDown] at hEq
    field_simp [hsm, hsp, hv.ne'] at hEq
    nlinarith [sq_nonneg s]
  have hABC : (A : ℂ) * (B : ℂ) = (v : ℂ) ^ (2 : ℕ) := by exact_mod_cast hABreal
  have hdiffC : (A : ℂ) - (B : ℂ) ≠ 0 := by exact_mod_cast hdiff
  have hbA : xiSquaredNode q + (A : ℂ) ≠ 0 := by
    simpa only [add_comm] using ofReal_add_xiSquaredNode_ne_zero hApos.le q
  have hbB : xiSquaredNode q + (B : ℂ) ≠ 0 := by
    simpa only [add_comm] using ofReal_add_xiSquaredNode_ne_zero hBpos.le q
  have halg := twoScaleRationalAtom_partialFraction
    (v := (v : ℂ)) (b := xiSquaredNode q) (A := (A : ℂ)) (B := (B : ℂ))
    (t := (s : ℂ) ^ (2 : ℕ)) hABC hdiffC hbA hbB
  simpa only [liEvenCrossTwoScaleRationalAtom, A, B] using
    halg

/-- The complete two-scale atom sum is exactly a divided difference of the radial
shifted-moment response.  No zero truncation or mode truncation occurs. -/
theorem tsum_liEvenCrossTwoScaleRationalAtom_eq_radialResponse_divDiff
    {v s : ℝ} (hv : 0 < v) (hs : 0 < s) (hs5 : s < 1 / 5) :
    (∑' q : XiZeroCopy, liEvenCrossTwoScaleRationalAtom v s q) =
      (2 * (1 + (s : ℂ) ^ (2 : ℕ)) / (1 - (s : ℂ) ^ (2 : ℕ)) ^ (3 : ℕ)) *
        ((liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleUp v s) -
            liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleDown v s)) /
          ((liEvenCrossReciprocalScaleUp v s : ℂ) -
            (liEvenCrossReciprocalScaleDown v s : ℂ))) := by
  let A : ℝ := liEvenCrossReciprocalScaleUp v s
  let B : ℝ := liEvenCrossReciprocalScaleDown v s
  let C : ℂ := 2 * (1 + (s : ℂ) ^ (2 : ℕ)) / (1 - (s : ℂ) ^ (2 : ℕ)) ^ (3 : ℕ)
  let f : ℝ → XiZeroCopy → ℂ := fun y q =>
    xiSquaredNode q / (xiSquaredNode q + (y : ℂ)) ^ (2 : ℕ)
  have hApos : 0 < A := by
    dsimp only [A, liEvenCrossReciprocalScaleUp]
    have hsm : 0 < 1 - s := by nlinarith
    positivity
  have hBpos : 0 < B := by
    dsimp only [B, liEvenCrossReciprocalScaleDown]
    have hsm : 0 < 1 - s := by nlinarith
    have hsp : 0 < 1 + s := by nlinarith
    positivity
  have hA : Summable (f A) := by
    simpa only [f] using summable_xiSquaredNode_div_add_shift_sq hApos.le
  have hB : Summable (f B) := by
    simpa only [f] using summable_xiSquaredNode_div_add_shift_sq hBpos.le
  have hAtom (q : XiZeroCopy) :
      liEvenCrossTwoScaleRationalAtom v s q =
        C * (((A : ℂ) * f A q - (B : ℂ) * f B q) / ((A : ℂ) - (B : ℂ))) := by
    simpa only [A, B, C, f] using
      liEvenCrossTwoScaleRationalAtom_eq_responseAtom hv hs hs5 q
  calc
    (∑' q : XiZeroCopy, liEvenCrossTwoScaleRationalAtom v s q) =
        ∑' q : XiZeroCopy,
          C * (((A : ℂ) * f A q - (B : ℂ) * f B q) /
            ((A : ℂ) - (B : ℂ))) := tsum_congr hAtom
    _ = C * (((A : ℂ) * (∑' q : XiZeroCopy, f A q) -
          (B : ℂ) * (∑' q : XiZeroCopy, f B q)) /
        ((A : ℂ) - (B : ℂ))) := by
      rw [show (fun q : XiZeroCopy =>
          C * (((A : ℂ) * f A q - (B : ℂ) * f B q) /
            ((A : ℂ) - (B : ℂ)))) =
          fun q : XiZeroCopy =>
            (C / ((A : ℂ) - (B : ℂ))) *
              ((A : ℂ) * f A q - (B : ℂ) * f B q) by
        funext q
        ring]
      rw [tsum_mul_left,
        (hA.mul_left (A : ℂ)).tsum_sub (hB.mul_left (B : ℂ)),
        tsum_mul_left, tsum_mul_left]
      ring
    _ = C *
        ((liEvenCrossComplexRadialDilationResponse A -
            liEvenCrossComplexRadialDilationResponse B) /
          ((A : ℂ) - (B : ℂ))) := by
      rw [show (∑' q : XiZeroCopy, f A q) =
          xiShiftedReciprocalMoment A 0 -
            (A : ℂ) * xiShiftedReciprocalMoment A 1 by
        simpa only [f] using
          tsum_xiSquaredNode_div_add_shift_sq_eq_shiftedMoment_response hApos.le,
        show (∑' q : XiZeroCopy, f B q) =
          xiShiftedReciprocalMoment B 0 -
            (B : ℂ) * xiShiftedReciprocalMoment B 1 by
        simpa only [f] using
          tsum_xiSquaredNode_div_add_shift_sq_eq_shiftedMoment_response hBpos.le]
      simp only [liEvenCrossComplexRadialDilationResponse]
    _ = (2 * (1 + (s : ℂ) ^ (2 : ℕ)) / (1 - (s : ℂ) ^ (2 : ℕ)) ^ (3 : ℕ)) *
        ((liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleUp v s) -
            liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleDown v s)) /
          ((liEvenCrossReciprocalScaleUp v s : ℂ) -
            (liEvenCrossReciprocalScaleDown v s : ℂ))) := by
      rfl

theorem liEvenCrossComplexRadialDilationResponse_eq_ofReal
    {y : ℝ} (hy : 0 ≤ y) :
    liEvenCrossComplexRadialDilationResponse y =
      (liEvenCrossRadialDilationResponse y : ℂ) := by
  have h0 := xiShiftedReciprocalMoment_im_eq_zero hy 0
  have h1 := xiShiftedReciprocalMoment_im_eq_zero hy 1
  apply Complex.ext
  · simp [liEvenCrossComplexRadialDilationResponse,
      liEvenCrossRadialDilationResponse, mul_re]
  · simp [liEvenCrossComplexRadialDilationResponse,
      liEvenCrossRadialDilationResponse, mul_im, h0, h1]

/-- Absolute convergence of the completed adjacent-current generating rows. -/
theorem summable_liEvenCrossSquareMassAdjacentFlux_generating_rows
    {v s : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (hs : 0 < s) (hs5 : s < 1 / 5) :
    Summable (fun n : ℕ =>
      (∑' q : XiZeroCopy, liEvenCrossSquareMassAdjacentFlux v n q) *
        (((s : ℂ) ^ (2 : ℕ)) ^ n)) := by
  let F : XiZeroCopy → ℕ → ℂ := fun q n =>
    liEvenCrossSquareMassAdjacentFlux v n q * (((s : ℂ) ^ (2 : ℕ)) ^ n)
  have hprod : Summable (fun p : XiZeroCopy × ℕ => F p.1 p.2) := by
    simpa only [F] using summable_liEvenCrossGeneratingFlux_prod hv hv4 hs hs5
  have hswap : Summable (fun p : ℕ × XiZeroCopy => F p.2 p.1) := by
    apply (hprod.comp_injective (Equiv.prodComm ℕ XiZeroCopy).injective).congr
    rintro ⟨n, q⟩
    rfl
  have hrows : Summable (fun n : ℕ => ∑' q : XiZeroCopy, F q n) := hswap.prod
  apply hrows.congr
  intro n
  rw [tsum_mul_right]

/-- **LI two-scale radial generating law.**  The full infinite Xi divisor and the
full adjacent-mode tower reduce to one divided difference of the first radial
shifted-moment response. -/
theorem liEvenCrossSquareMassAdjacentFlux_generating_eq_radialResponse_divDiff
    {v s : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (hs : 0 < s) (hs5 : s < 1 / 5) :
    (∑' n : ℕ, (∑' q : XiZeroCopy,
        liEvenCrossSquareMassAdjacentFlux v n q) * (((s : ℂ) ^ (2 : ℕ)) ^ n)) =
      (2 * (1 + (s : ℂ) ^ (2 : ℕ)) / (1 - (s : ℂ) ^ (2 : ℕ)) ^ (3 : ℕ)) *
        ((liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleUp v s) -
            liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleDown v s)) /
          ((liEvenCrossReciprocalScaleUp v s : ℂ) -
            (liEvenCrossReciprocalScaleDown v s : ℂ))) := by
  rw [liEvenCrossSquareMassAdjacentFlux_generating_eq_twoScaleAtom_tsum
      hv hv4 hs hs5,
    tsum_liEvenCrossTwoScaleRationalAtom_eq_radialResponse_divDiff hv hs hs5]

/-- **Real LI source law.**  Every coefficient of the completed adjacent-current
tower is encoded at once by the two radial scales.  Consequently the remaining
LI sign problem is a source-level divided-difference orientation problem. -/
theorem liEvenCrossSquareMassAdjacentCurrent_generating_eq_radialResponse_divDiff
    {v s : ℝ} (hv : 0 < v) (hv4 : v ≤ 1 / 4)
    (hs : 0 < s) (hs5 : s < 1 / 5) :
    (∑' n : ℕ,
        liEvenCrossSquareMassAdjacentCurrent v n * (s ^ (2 : ℕ)) ^ n) =
      (2 * (1 + s ^ (2 : ℕ)) / (1 - s ^ (2 : ℕ)) ^ (3 : ℕ)) *
        ((liEvenCrossRadialDilationResponse
              (liEvenCrossReciprocalScaleUp v s) -
            liEvenCrossRadialDilationResponse
              (liEvenCrossReciprocalScaleDown v s)) /
          (liEvenCrossReciprocalScaleUp v s -
            liEvenCrossReciprocalScaleDown v s)) := by
  let row : ℕ → ℂ := fun n =>
    (∑' q : XiZeroCopy, liEvenCrossSquareMassAdjacentFlux v n q) *
      (((s : ℂ) ^ (2 : ℕ)) ^ n)
  have hrow : Summable row := by
    simpa only [row] using
      summable_liEvenCrossSquareMassAdjacentFlux_generating_rows hv hv4 hs hs5
  have hterm (n : ℕ) :
      liEvenCrossSquareMassAdjacentCurrent v n * (s ^ (2 : ℕ)) ^ n = (row n).re := by
    rw [liEvenCrossSquareMassAdjacentCurrent_eq_re_tsum hv n]
    dsimp only [row]
    rw [mul_re]
    have hre : ((((s : ℂ) ^ (2 : ℕ)) ^ n).re) = (s ^ (2 : ℕ)) ^ n := by
      norm_cast
    have him : ((((s : ℂ) ^ (2 : ℕ)) ^ n).im) = 0 := by
      norm_cast
    rw [hre, him]
    ring
  have hcomplex :=
    liEvenCrossSquareMassAdjacentFlux_generating_eq_radialResponse_divDiff
      hv hv4 hs hs5
  have hApos : 0 < liEvenCrossReciprocalScaleUp v s := by
    rw [liEvenCrossReciprocalScaleUp]
    have hsm : 0 < 1 - s := by nlinarith
    positivity
  have hBpos : 0 < liEvenCrossReciprocalScaleDown v s := by
    rw [liEvenCrossReciprocalScaleDown]
    have hsm : 0 < 1 - s := by nlinarith
    have hsp : 0 < 1 + s := by nlinarith
    positivity
  calc
    (∑' n : ℕ,
        liEvenCrossSquareMassAdjacentCurrent v n * (s ^ (2 : ℕ)) ^ n) =
      ∑' n : ℕ, (row n).re := tsum_congr hterm
    _ = (∑' n : ℕ, row n).re := by
      rw [Complex.re_tsum hrow]
    _ = ((2 * (1 + (s : ℂ) ^ (2 : ℕ)) / (1 - (s : ℂ) ^ (2 : ℕ)) ^ (3 : ℕ)) *
        ((liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleUp v s) -
            liEvenCrossComplexRadialDilationResponse
              (liEvenCrossReciprocalScaleDown v s)) /
          ((liEvenCrossReciprocalScaleUp v s : ℂ) -
            (liEvenCrossReciprocalScaleDown v s : ℂ)))).re := by
      exact congrArg Complex.re hcomplex
    _ = (2 * (1 + s ^ (2 : ℕ)) / (1 - s ^ (2 : ℕ)) ^ (3 : ℕ)) *
        ((liEvenCrossRadialDilationResponse
              (liEvenCrossReciprocalScaleUp v s) -
            liEvenCrossRadialDilationResponse
              (liEvenCrossReciprocalScaleDown v s)) /
          (liEvenCrossReciprocalScaleUp v s -
            liEvenCrossReciprocalScaleDown v s)) := by
      rw [liEvenCrossComplexRadialDilationResponse_eq_ofReal hApos.le,
        liEvenCrossComplexRadialDilationResponse_eq_ofReal hBpos.le]
      norm_cast

end
end RHTower
