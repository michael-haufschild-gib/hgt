import GaloisForLFunctions.RHTower.PrimeArchThetaLikelihoodOrderedTailTransfer
import GaloisForLFunctions.RHTower.PrimeArchThetaTwoChannelVirialRayleighRitz

/-!
# Likelihood single-loss Stein and Rayleigh--Ritz certificates

The theta higher-tail likelihood order removes one copy of the first-atom enclosure factor from
the completed-source moment transfer.  This module carries that improvement backward through the
quadratic Stein, two-channel Robertson, Rayleigh--Ritz, and polarized virial interfaces.

The reusable scaled certificates use a target multiplier `κ`; Robertson requires the energy
coefficient `κ - 9`.  Specializing to `κ = 14 * (3005 / 2997)` gives the likelihood single-loss
interfaces, replacing the older squared enclosure multiplier.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-! ## Scaled quadratic and two-channel certificates -/

/-- Quadratic Stein certificate for an arbitrary target moment multiplier `κ`. -/
def ThetaCuspFirstRadialQuadraticSteinScaledEnergyCertificate (κ : ℝ) : Prop :=
  (κ - 9) * thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
        thetaCuspFirstRadialQuadraticSteinEnergy ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialQuadraticSteinCoupling ^ 2

/-- Curvature-form quadratic certificate at the same target multiplier. -/
def ThetaCuspFirstRadialQuadraticVirialScaledEnergyCertificate (κ : ℝ) : Prop :=
  (κ - 9) * thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
        thetaCuspFirstRadialQuadraticVirialEnergy ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialQuadraticSteinCoupling ^ 2

/-- Stein and virial scaled certificates are identical. -/
theorem quadraticSteinScaledEnergyCertificate_iff_virialScaledEnergyCertificate
    (κ : ℝ) :
    ThetaCuspFirstRadialQuadraticSteinScaledEnergyCertificate κ ↔
      ThetaCuspFirstRadialQuadraticVirialScaledEnergyCertificate κ := by
  rw [ThetaCuspFirstRadialQuadraticSteinScaledEnergyCertificate,
    ThetaCuspFirstRadialQuadraticVirialScaledEnergyCertificate,
    thetaCuspFirstRadialQuadraticSteinEnergy_eq_virialEnergy]

/-- Variational two-channel certificate for an arbitrary target multiplier `κ`. -/
def ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate (κ : ℝ) : Prop :=
  ∃ a b : ℝ,
    0 < thetaCuspFirstRadialTwoChannelSteinEnergy a b ∧
    (κ - 9) * thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialTwoChannelSteinEnergy a b ≤
      9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling a b ^ 2

/-- The fixed quadratic field `(1,-1/2)` embeds every scaled quadratic certificate into the
two-channel family. -/
theorem twoChannelSteinScaledEnergyCertificate_of_quadratic
    {κ : ℝ} (hcert : ThetaCuspFirstRadialQuadraticSteinScaledEnergyCertificate κ) :
    ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate κ := by
  refine ⟨1, -1 / 2, ?_, ?_⟩
  · rw [thetaCuspFirstRadialTwoChannelSteinEnergy]
    convert thetaCuspFirstRadialQuadraticSteinEnergy_pos using 1
    rw [thetaCuspFirstRadialQuadraticSteinEnergy]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [thetaCuspFirstRadialTwoChannelSteinScore_one_negHalf]
  · have hcoupling : thetaCuspFirstRadialTwoChannelSteinCoupling 1 (-1 / 2) =
        thetaCuspFirstRadialQuadraticSteinCoupling := by
      rw [thetaCuspFirstRadialTwoChannelSteinCoupling,
        thetaCuspFirstRadialQuadraticSteinCoupling]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    have henergy : thetaCuspFirstRadialTwoChannelSteinEnergy 1 (-1 / 2) =
        thetaCuspFirstRadialQuadraticSteinEnergy := by
      rw [thetaCuspFirstRadialTwoChannelSteinEnergy,
        thetaCuspFirstRadialQuadraticSteinEnergy]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [thetaCuspFirstRadialTwoChannelSteinScore_one_negHalf]
    simpa only [ThetaCuspFirstRadialQuadraticSteinScaledEnergyCertificate,
      henergy, hcoupling] using hcert

/-- Robertson converts a scaled two-channel energy certificate into the corresponding first-atom
moment inequality. -/
theorem thetaCusp_firstRadial_upper_of_twoChannelSteinScaledEnergyCertificate
    {κ : ℝ} (hcert : ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate κ) :
    κ * thetaCuspBornWittenRadialRawMoment 1 1 1 ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 := by
  rcases hcert with ⟨a, b, hE, hcert⟩
  let J0 := thetaCuspBornWittenRadialPowerMoment 0 1 1
  let J1 := thetaCuspBornWittenRadialPowerMoment 2 1 1
  let J2 := thetaCuspBornWittenRadialPowerMoment 4 1 1
  let C := thetaCuspFirstRadialTwoChannelSteinCoupling a b
  let E := thetaCuspFirstRadialTwoChannelSteinEnergy a b
  let c := κ - 9
  have hJ0 : 0 < J0 := thetaCuspFirstRadialPowerMoment_zero_pos
  have hunc := thetaCuspFirstRadialTwoChannelSteinRobertson a b
  have huncFactor : J0 * (J0 * C ^ 2) ≤
      J0 * ((J0 * J2 - J1 ^ 2) * E) := by
    dsimp [J0, J1, J2, C, E] at hunc ⊢
    convert hunc using 1 <;> ring
  have hunc' : J0 * C ^ 2 ≤ (J0 * J2 - J1 ^ 2) * E :=
    (mul_le_mul_iff_of_pos_left hJ0).mp huncFactor
  have hEnergy' : c * J1 ^ 2 * E ≤ 9 * J0 * C ^ 2 := by
    simpa only [ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate,
      c, J0, J1, C, E] using hcert
  have hchain : c * J1 ^ 2 * E ≤ 9 * ((J0 * J2 - J1 ^ 2) * E) := by
    calc
      c * J1 ^ 2 * E ≤ 9 * (J0 * C ^ 2) := by
        simpa only [mul_assoc] using hEnergy'
      _ ≤ 9 * ((J0 * J2 - J1 ^ 2) * E) :=
        mul_le_mul_of_nonneg_left hunc' (by norm_num : (0 : ℝ) ≤ 9)
  have hcore : c * J1 ^ 2 ≤ 9 * (J0 * J2 - J1 ^ 2) := by
    have hfactor : E * (c * J1 ^ 2) ≤
        E * (9 * (J0 * J2 - J1 ^ 2)) := by
      convert hchain using 1 <;> ring
    exact (mul_le_mul_iff_of_pos_left hE).mp hfactor
  rw [← thetaCuspBornWittenRadialPowerMoment_even 0 1 1,
    ← thetaCuspBornWittenRadialPowerMoment_even 1 1 1,
    ← thetaCuspBornWittenRadialPowerMoment_even 2 1 1]
  dsimp [J0, J1, J2, c] at hcore
  norm_num only [Nat.reduceMul] at hcore ⊢
  nlinarith

/-! ## Scaled Rayleigh--Ritz elimination -/

/-- Explicit two-channel Rayleigh--Ritz certificate at target multiplier `κ`. -/
def ThetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate (κ : ℝ) : Prop :=
  (κ - 9) * thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
        thetaCuspFirstRadialTwoChannelSteinEnergyDet ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialTwoChannelSteinAdjugateResponse

/-- Adjugate optimization eliminates the two generator coefficients for every target
multiplier. -/
theorem thetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate_iff
    (κ : ℝ) :
    ThetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate κ ↔
      ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate κ := by
  constructor
  · intro hcert
    let A := thetaCuspFirstRadialTwoChannelSteinEnergy 1 0
    let B := thetaCuspFirstRadialTwoChannelSteinCrossEnergy
    let D := thetaCuspFirstRadialTwoChannelSteinEnergy 0 1
    let c₁ := thetaCuspFirstRadialTwoChannelSteinCoupling 1 0
    let c₂ := thetaCuspFirstRadialTwoChannelSteinCoupling 0 1
    let scale := (κ - 9) *
      thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2
    let L := 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1
    have hdet : 0 < A * D - B ^ 2 := by
      simpa only [A, B, D] using thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos
    have hresponse : 0 < D * c₁ ^ 2 - 2 * B * c₁ * c₂ + A * c₂ ^ 2 := by
      simpa only [thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
        A, B, D, c₁, c₂] using
          thetaCuspFirstRadialTwoChannelSteinAdjugateResponse_pos
    have hmatrix : scale * (A * D - B ^ 2) ≤
        L * (D * c₁ ^ 2 - 2 * B * c₁ * c₂ + A * c₂ ^ 2) := by
      simpa only [ThetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate,
        thetaCuspFirstRadialTwoChannelSteinEnergyDet,
        thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
        scale, L, A, B, D, c₁, c₂] using hcert
    rcases HTGeometry.exists_positive_twoChannelRayleighWitness_of_adjugate
      A B D c₁ c₂ scale L hdet hresponse hmatrix with ⟨a, b, hE, hineq⟩
    refine ⟨a, b, ?_, ?_⟩
    · rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic]
      simpa only [A, B, D, mul_comm, mul_left_comm, mul_assoc] using hE
    · rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic,
        thetaCuspFirstRadialTwoChannelSteinCoupling_eq_basis]
      simpa only [scale, L, A, B, D, c₁, c₂, mul_comm, mul_left_comm,
        mul_assoc] using hineq
  · rintro ⟨a, b, henergy, hineq⟩
    let A := thetaCuspFirstRadialTwoChannelSteinEnergy 1 0
    let B := thetaCuspFirstRadialTwoChannelSteinCrossEnergy
    let D := thetaCuspFirstRadialTwoChannelSteinEnergy 0 1
    let c₁ := thetaCuspFirstRadialTwoChannelSteinCoupling 1 0
    let c₂ := thetaCuspFirstRadialTwoChannelSteinCoupling 0 1
    let scale := (κ - 9) *
      thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2
    let L := 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1
    have hdet : 0 < A * D - B ^ 2 := by
      simpa only [A, B, D] using
        thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos
    have hL : 0 ≤ L := by
      have hM0 : 0 < thetaCuspBornWittenRadialPowerMoment 0 1 1 :=
        thetaCuspFirstRadialPowerMoment_zero_pos
      dsimp only [L]
      positivity
    have hE : 0 < A * a ^ 2 + 2 * B * a * b + D * b ^ 2 := by
      rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic] at henergy
      simpa only [A, B, D, mul_comm, mul_left_comm, mul_assoc] using henergy
    have hineq' : scale * (A * a ^ 2 + 2 * B * a * b + D * b ^ 2) ≤
        L * (a * c₁ + b * c₂) ^ 2 := by
      rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic,
        thetaCuspFirstRadialTwoChannelSteinCoupling_eq_basis] at hineq
      simpa only [scale, L, A, B, D, c₁, c₂, mul_comm, mul_left_comm,
        mul_assoc] using hineq
    have hmatrix :=
      HTGeometry.twoChannelRayleighMatrixCertificate_of_positiveWitness
        A B D c₁ c₂ scale L a b hdet hL hE hineq'
    simpa only [ThetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate,
      thetaCuspFirstRadialTwoChannelSteinEnergyDet,
      thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
      scale, L, A, B, D, c₁, c₂] using hmatrix

/-- Polarized virial Rayleigh--Ritz certificate at target multiplier `κ`. -/
def ThetaCuspFirstRadialTwoChannelVirialRayleighRitzScaledCertificate (κ : ℝ) : Prop :=
  (κ - 9) * thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
        thetaCuspFirstRadialTwoChannelVirialEnergyDet ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialTwoChannelVirialAdjugateResponse

/-- Polarized hypervirial replacement is exact for every target multiplier. -/
theorem thetaCuspFirstRadialTwoChannelVirialRayleighRitzScaledCertificate_iff
    (κ : ℝ) :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzScaledCertificate κ ↔
      ThetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate κ := by
  simp only [ThetaCuspFirstRadialTwoChannelVirialRayleighRitzScaledCertificate,
    ThetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate,
    thetaCuspFirstRadialTwoChannelVirialEnergyDet_eq,
    thetaCuspFirstRadialTwoChannelVirialAdjugateResponse_eq]

/-! ## Likelihood single-loss specialization -/

/-- Quadratic Stein certificate with the one-factor likelihood enclosure loss. -/
def ThetaCuspFirstRadialQuadraticSteinSingleLossEnergyCertificate : Prop :=
  ThetaCuspFirstRadialQuadraticSteinScaledEnergyCertificate
    (14 * (3005 / 2997 : ℝ))

/-- Quadratic virial certificate with the one-factor likelihood enclosure loss. -/
def ThetaCuspFirstRadialQuadraticVirialSingleLossEnergyCertificate : Prop :=
  ThetaCuspFirstRadialQuadraticVirialScaledEnergyCertificate
    (14 * (3005 / 2997 : ℝ))

/-- Variational two-channel certificate with the one-factor likelihood enclosure loss. -/
def ThetaCuspFirstRadialTwoChannelSteinSingleLossEnergyCertificate : Prop :=
  ThetaCuspFirstRadialTwoChannelSteinScaledEnergyCertificate
    (14 * (3005 / 2997 : ℝ))

/-- Rayleigh--Ritz determinant certificate with the one-factor likelihood enclosure loss. -/
def ThetaCuspFirstRadialTwoChannelRayleighRitzSingleLossCertificate : Prop :=
  ThetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate
    (14 * (3005 / 2997 : ℝ))

/-- Polarized virial determinant certificate with the one-factor likelihood enclosure loss. -/
def ThetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate : Prop :=
  ThetaCuspFirstRadialTwoChannelVirialRayleighRitzScaledCertificate
    (14 * (3005 / 2997 : ℝ))

/-- The older squared-loss quadratic certificate implies the likelihood single-loss
certificate. -/
theorem quadraticSteinSingleLossEnergyCertificate_of_squaredLoss
    (hcert : ThetaCuspFirstRadialQuadraticSteinEnergyCertificate) :
    ThetaCuspFirstRadialQuadraticSteinSingleLossEnergyCertificate := by
  rw [ThetaCuspFirstRadialQuadraticSteinEnergyCertificate] at hcert
  change
    (14 * (3005 / 2997 : ℝ) - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialQuadraticSteinEnergy ≤
      9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialQuadraticSteinCoupling ^ 2
  have hfactor : 0 ≤
      thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
        thetaCuspFirstRadialQuadraticSteinEnergy :=
    mul_nonneg (sq_nonneg _) thetaCuspFirstRadialQuadraticSteinEnergy_pos.le
  have hcoeff :
      14 * (3005 / 2997 : ℝ) - 9 ≤
        14 * (3005 / 2997 : ℝ) ^ 2 - 9 := by
    norm_num
  calc
    (14 * (3005 / 2997 : ℝ) - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialQuadraticSteinEnergy =
        (14 * (3005 / 2997 : ℝ) - 9) *
          (thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialQuadraticSteinEnergy) := by ring
    _ ≤ (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
          (thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialQuadraticSteinEnergy) :=
      mul_le_mul_of_nonneg_right hcoeff hfactor
    _ = (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialQuadraticSteinEnergy := by ring
    _ ≤ 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspFirstRadialQuadraticSteinCoupling ^ 2 := hcert

/-- Stein and virial single-loss quadratic certificates coincide. -/
theorem quadraticSteinSingleLossEnergyCertificate_iff_virial :
    ThetaCuspFirstRadialQuadraticSteinSingleLossEnergyCertificate ↔
      ThetaCuspFirstRadialQuadraticVirialSingleLossEnergyCertificate :=
  quadraticSteinScaledEnergyCertificate_iff_virialScaledEnergyCertificate _

/-- The fixed quadratic single-loss certificate embeds into the variational two-channel
single-loss certificate. -/
theorem twoChannelSteinSingleLossEnergyCertificate_of_quadratic
    (hcert : ThetaCuspFirstRadialQuadraticSteinSingleLossEnergyCertificate) :
    ThetaCuspFirstRadialTwoChannelSteinSingleLossEnergyCertificate :=
  twoChannelSteinScaledEnergyCertificate_of_quadratic hcert

/-- Single-loss Rayleigh--Ritz elimination is exact. -/
theorem thetaCuspFirstRadialTwoChannelRayleighRitzSingleLossCertificate_iff :
    ThetaCuspFirstRadialTwoChannelRayleighRitzSingleLossCertificate ↔
      ThetaCuspFirstRadialTwoChannelSteinSingleLossEnergyCertificate :=
  thetaCuspFirstRadialTwoChannelRayleighRitzScaledCertificate_iff _

/-- Single-loss polarized virial replacement is exact. -/
theorem thetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate_iff :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate ↔
      ThetaCuspFirstRadialTwoChannelRayleighRitzSingleLossCertificate :=
  thetaCuspFirstRadialTwoChannelVirialRayleighRitzScaledCertificate_iff _

/-- A two-channel single-loss certificate supplies the precise first-atom inequality needed by
the likelihood-order transfer. -/
theorem thetaCusp_firstRadial_upper_of_twoChannelSteinSingleLossEnergyCertificate
    (hcert : ThetaCuspFirstRadialTwoChannelSteinSingleLossEnergyCertificate) :
    14 * (3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1 ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 :=
  thetaCusp_firstRadial_upper_of_twoChannelSteinScaledEnergyCertificate hcert

/-- A quadratic single-loss certificate supplies the same likelihood-order input. -/
theorem thetaCusp_firstRadial_upper_of_quadraticSteinSingleLossEnergyCertificate
    (hcert : ThetaCuspFirstRadialQuadraticSteinSingleLossEnergyCertificate) :
    14 * (3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1 ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 :=
  thetaCusp_firstRadial_upper_of_twoChannelSteinSingleLossEnergyCertificate
    (twoChannelSteinSingleLossEnergyCertificate_of_quadratic hcert)

/-- The common `2π` radial normalization cancels from the likelihood single-loss upper
first-atom inequality. -/
theorem thetaCusp_firstAtom_upper_singleLoss_of_radial
    (hupper :
      14 * (3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 1 1 1 ^ 2 ≤
        9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
          thetaCuspBornWittenRadialRawMoment 2 1 1) :
    14 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1 ^ 2 ≤
      9 * thetaCuspAtomRawEvenMoment 1 1 *
        thetaCuspAtomRawEvenMoment 3 1 := by
  rw [show thetaCuspAtomRawEvenMoment 1 1 =
        2 * Real.pi * thetaCuspBornWittenRadialRawMoment 0 1 1 by
      simpa using thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 0 1 1,
    show thetaCuspAtomRawEvenMoment 2 1 =
        2 * Real.pi * thetaCuspBornWittenRadialRawMoment 1 1 1 by
      simpa using thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 1 1 1,
    show thetaCuspAtomRawEvenMoment 3 1 =
        2 * Real.pi * thetaCuspBornWittenRadialRawMoment 2 1 1 by
      simpa using thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 2 1 1]
  have hscale : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hupper hscale
  nlinarith

/-- The same common radial normalization cancels from the relaxed first-atom inequality. -/
theorem thetaCusp_firstAtom_relaxed_singleLoss_of_radial
    (hrelaxed :
      16 * (3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    16 * (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1 *
        thetaCuspAtomRawEvenMoment 2 1 ≤
      45 * thetaCuspAtomRawEvenMoment 1 1 ^ 2 := by
  rw [show thetaCuspAtomRawEvenMoment 0 1 =
        2 * Real.pi * thetaCuspBornWittenRadialRawMoment 0 0 1 by
      simpa using thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 0 0 1,
    show thetaCuspAtomRawEvenMoment 1 1 =
        2 * Real.pi * thetaCuspBornWittenRadialRawMoment 1 0 1 by
      simpa using thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 1 0 1,
    show thetaCuspAtomRawEvenMoment 2 1 =
        2 * Real.pi * thetaCuspBornWittenRadialRawMoment 2 0 1 by
      simpa using thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 2 0 1]
  have hscale : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hrelaxed hscale
  nlinarith

/-- The single-loss two-channel certificate and matching relaxed first-atom inequality discharge
every completed-source linear Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelSteinSingleLoss
    (hcert : ThetaCuspFirstRadialTwoChannelSteinSingleLossEnergyCertificate)
    (hrelaxed :
      16 * (3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_first_atom_singleLoss
    (thetaCusp_firstAtom_upper_singleLoss_of_radial
      (thetaCusp_firstRadial_upper_of_twoChannelSteinSingleLossEnergyCertificate hcert))
    (thetaCusp_firstAtom_relaxed_singleLoss_of_radial hrelaxed)

/-- The polarized virial single-loss certificate, matching relaxed first-atom inequality, and
degree-two source tail imply RH. -/
theorem riemannHypothesis_of_twoChannelVirialRayleighRitzSingleLoss_of_primeArchDegreeTwoTail
    (hcert : ThetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate)
    (hrelaxed :
      16 * (3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1 *
          thetaCuspBornWittenRadialRawMoment 2 0 1 ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_first_atom_singleLoss_of_primeArchDegreeTwoTail
  · apply thetaCusp_firstAtom_upper_singleLoss_of_radial
    exact thetaCusp_firstRadial_upper_of_twoChannelSteinSingleLossEnergyCertificate
      (thetaCuspFirstRadialTwoChannelRayleighRitzSingleLossCertificate_iff.1
        (thetaCuspFirstRadialTwoChannelVirialRayleighRitzSingleLossCertificate_iff.1
          hcert))
  · exact thetaCusp_firstAtom_relaxed_singleLoss_of_radial hrelaxed
  · exact htail

end

end RHTower
