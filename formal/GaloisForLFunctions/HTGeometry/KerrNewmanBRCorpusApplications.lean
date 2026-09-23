import GaloisForLFunctions.HTGeometry.KerrNewmanBRGlobalStructure
import GaloisForLFunctions.HTGeometry.KerrNewmanStationaryLimitAlgebra
import GaloisForLFunctions.HTGeometry.PostselectedQubitRationalDynamics
import GaloisForLFunctions.HTGeometry.VaidyaEvaporationFZZHorizonScale

/-!
# Corpus applications of the Kerr--Newman--BR reciprocal-chart algebra

The reciprocal-clearing, horizon-factorization, seam-reflection, and compactification identities
from `KerrNewmanBRGlobalStructure` are applied here to pre-existing Kerr--Newman, Belinski--Zakharov,
Vaidya, and projective rational-dynamics objects.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped ContDiff

/-! ## Standard Kerr--Newman reciprocal extensions -/

/-- Polynomial extension of `y^(2 : ℕ) Sigma(1/y, theta)`. -/
def kerrNewmanReciprocalSigma (spin polar reciprocalRadius : ℝ) : ℝ :=
  1 + spin ^ (2 : ℕ) * Real.cos polar ^ (2 : ℕ) * reciprocalRadius ^ (2 : ℕ)

/-- Polynomial extension of `y^(2 : ℕ) Delta(1/y)`. -/
def kerrNewmanReciprocalDelta (mass spin charge reciprocalRadius : ℝ) : ℝ :=
  1 - 2 * mass * reciprocalRadius +
    (spin ^ (2 : ℕ) + charge ^ (2 : ℕ)) * reciprocalRadius ^ (2 : ℕ)

/-- Polynomial extension of the denominator-cleared stationary-limit numerator. -/
def kerrNewmanReciprocalStationaryLimit
    (mass spin charge polar reciprocalRadius : ℝ) : ℝ :=
  1 - 2 * mass * reciprocalRadius +
    (charge ^ (2 : ℕ) + spin ^ (2 : ℕ) * Real.cos polar ^ (2 : ℕ)) * reciprocalRadius ^ (2 : ℕ)

theorem kerrNewmanSigma_reciprocalClearing
    (spin polar : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ (2 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar =
      kerrNewmanReciprocalSigma spin polar y.1 := by
  unfold kerrNewmanSigma kerrNewmanReciprocalSigma
  field_simp [y.2]

theorem kerrNewmanDelta_reciprocalClearing
    (mass spin charge : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ (2 : ℕ) * kerrNewmanDelta mass spin charge y.1⁻¹ =
      kerrNewmanReciprocalDelta mass spin charge y.1 := by
  unfold kerrNewmanDelta kerrNewmanReciprocalDelta
  field_simp [y.2]
  ring

theorem kerrNewmanStationaryLimit_reciprocalClearing
    (mass spin charge polar : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ (2 : ℕ) *
        kerrNewmanStationaryLimitPolynomial mass spin charge y.1⁻¹ polar =
      kerrNewmanReciprocalStationaryLimit mass spin charge polar y.1 := by
  rw [kerrNewmanStationaryLimitPolynomial_completeSquare]
  unfold kerrNewmanReciprocalStationaryLimit
  field_simp [y.2]
  ring

theorem kerrNewmanReciprocalSigma_seam (spin polar : ℝ) :
    kerrNewmanReciprocalSigma spin polar 0 = 1 := by
  simp [kerrNewmanReciprocalSigma]

theorem kerrNewmanReciprocalDelta_seam (mass spin charge : ℝ) :
    kerrNewmanReciprocalDelta mass spin charge 0 = 1 := by
  simp [kerrNewmanReciprocalDelta]

theorem kerrNewmanReciprocalStationaryLimit_seam
    (mass spin charge polar : ℝ) :
    kerrNewmanReciprocalStationaryLimit mass spin charge polar 0 = 1 := by
  simp [kerrNewmanReciprocalStationaryLimit]

theorem kerrNewmanReciprocalSigma_ge_one (spin polar reciprocalRadius : ℝ) :
    1 ≤ kerrNewmanReciprocalSigma spin polar reciprocalRadius := by
  unfold kerrNewmanReciprocalSigma
  rw [show spin ^ (2 : ℕ) * Real.cos polar ^ (2 : ℕ) * reciprocalRadius ^ (2 : ℕ) =
    (spin * Real.cos polar * reciprocalRadius) ^ (2 : ℕ) by ring]
  nlinarith [sq_nonneg (spin * Real.cos polar * reciprocalRadius)]

/-- The standard Kerr--Newman reciprocal chart is regular at infinity at scalar-potential level. -/
theorem contDiff_kerrNewmanReciprocalPotentials (mass spin charge polar : ℝ) :
    ContDiff ℝ ∞ (fun y => kerrNewmanReciprocalSigma spin polar y) ∧
    ContDiff ℝ ∞ (fun y => kerrNewmanReciprocalDelta mass spin charge y) ∧
    ContDiff ℝ ∞ (fun y =>
      kerrNewmanReciprocalStationaryLimit mass spin charge polar y) := by
  simp only [kerrNewmanReciprocalSigma, kerrNewmanReciprocalDelta,
    kerrNewmanReciprocalStationaryLimit]
  constructor
  · fun_prop
  constructor <;> fun_prop

/-- Reciprocal horizon discriminant in denominator-cleared complete-square form. -/
theorem kerrNewmanReciprocalDelta_completeSquare_cleared
    (mass spin charge reciprocalRadius : ℝ) :
    (spin ^ (2 : ℕ) + charge ^ (2 : ℕ)) *
        kerrNewmanReciprocalDelta mass spin charge reciprocalRadius =
      ((spin ^ (2 : ℕ) + charge ^ (2 : ℕ)) * reciprocalRadius - mass) ^ (2 : ℕ) +
        (spin ^ (2 : ℕ) + charge ^ (2 : ℕ)) - mass ^ (2 : ℕ) := by
  unfold kerrNewmanReciprocalDelta
  ring

/-- Reciprocal stationary-limit discriminant, including angular rotation term. -/
theorem kerrNewmanReciprocalStationaryLimit_completeSquare_cleared
    (mass spin charge polar reciprocalRadius : ℝ) :
    (charge ^ (2 : ℕ) + spin ^ (2 : ℕ) * Real.cos polar ^ (2 : ℕ)) *
        kerrNewmanReciprocalStationaryLimit mass spin charge polar reciprocalRadius =
      ((charge ^ (2 : ℕ) + spin ^ (2 : ℕ) * Real.cos polar ^ (2 : ℕ)) * reciprocalRadius - mass) ^ (2 : ℕ) +
        (charge ^ (2 : ℕ) + spin ^ (2 : ℕ) * Real.cos polar ^ (2 : ℕ)) - mass ^ (2 : ℕ) := by
  unfold kerrNewmanReciprocalStationaryLimit
  ring

/-- Existing horizon zero locus transports exactly into the reciprocal chart. -/
theorem kerrNewmanDelta_reciprocal_zero_iff
    (mass spin charge : ℝ) (y : {z : ℝ // z ≠ 0}) :
    kerrNewmanDelta mass spin charge y.1⁻¹ = 0 ↔
      kerrNewmanReciprocalDelta mass spin charge y.1 = 0 := by
  have hclear := kerrNewmanDelta_reciprocalClearing mass spin charge y
  constructor
  · intro h
    simpa [h] using hclear.symm
  · intro h
    have hySq : y.1 ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 y.2
    apply (mul_eq_zero.mp ?_).resolve_left hySq
    rw [hclear, h]

/-- Existing stationary-limit zero locus transports exactly into the reciprocal chart. -/
theorem kerrNewmanStationaryLimit_reciprocal_zero_iff
    (mass spin charge polar : ℝ) (y : {z : ℝ // z ≠ 0}) :
    kerrNewmanStationaryLimitPolynomial mass spin charge y.1⁻¹ polar = 0 ↔
      kerrNewmanReciprocalStationaryLimit mass spin charge polar y.1 = 0 := by
  have hclear := kerrNewmanStationaryLimit_reciprocalClearing mass spin charge polar y
  constructor
  · intro h
    simpa [h] using hclear.symm
  · intro h
    have hySq : y.1 ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 y.2
    apply (mul_eq_zero.mp ?_).resolve_left hySq
    rw [hclear, h]

/-! ## Metric and BZ determinant applications -/

/-- Reciprocal extension of the stationary Killing coefficient after its existing clearing. -/
theorem kerrNewmanKillingBlock_tt_reciprocalCleared
    (mass spin charge polar : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ (4 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
        kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar 0 0 =
      -kerrNewmanReciprocalSigma spin polar y.1 *
        kerrNewmanReciprocalStationaryLimit mass spin charge polar y.1 := by
  rw [show y.1 ^ (4 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
      kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar 0 0 =
      y.1 ^ (4 : ℕ) *
        (kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
          kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar 0 0) by ring]
  rw [kerrNewmanKillingBlock_tt_cleared_stationaryLimitPolynomial]
  have hSigma := kerrNewmanSigma_reciprocalClearing spin polar y
  have hStationary :=
    kerrNewmanStationaryLimit_reciprocalClearing mass spin charge polar y
  calc
    y.1 ^ (4 : ℕ) *
        (-kerrNewmanSigma spin y.1⁻¹ polar *
          kerrNewmanStationaryLimitPolynomial mass spin charge y.1⁻¹ polar) =
      -(y.1 ^ (2 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar) *
        (y.1 ^ (2 : ℕ) *
          kerrNewmanStationaryLimitPolynomial mass spin charge y.1⁻¹ polar) := by ring
    _ = _ := by rw [hSigma, hStationary]

/-- Reciprocal polynomial form of the undressed Killing-block determinant law. -/
theorem kerrNewmanKillingBlock_det_reciprocalCleared
    (mass spin charge polar : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ (6 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
        (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar).det =
      -kerrNewmanReciprocalDelta mass spin charge y.1 * Real.sin polar ^ (2 : ℕ) *
        kerrNewmanReciprocalSigma spin polar y.1 ^ (2 : ℕ) := by
  rw [show y.1 ^ (6 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
      (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar).det =
      y.1 ^ (6 : ℕ) *
        (kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
          (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar).det) by ring]
  rw [kerrNewmanKillingBlock_det_cleared]
  have hSigma := kerrNewmanSigma_reciprocalClearing spin polar y
  have hDelta := kerrNewmanDelta_reciprocalClearing mass spin charge y
  calc
    y.1 ^ (6 : ℕ) *
        (-kerrNewmanDelta mass spin charge y.1⁻¹ * Real.sin polar ^ (2 : ℕ) *
          kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ)) =
      -(y.1 ^ (2 : ℕ) * kerrNewmanDelta mass spin charge y.1⁻¹) * Real.sin polar ^ (2 : ℕ) *
        (y.1 ^ (2 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar) ^ (2 : ℕ) := by ring
    _ = _ := by rw [hDelta, hSigma]

/-- Constant unipotent BZ dressing preserves the same reciprocal horizon carrier. -/
theorem belinskiZakharovDressedKerrNewmanKillingBlock_det_reciprocalCleared
    (parameter mass spin charge polar : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ (6 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
        (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
          (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar)).det =
      -kerrNewmanReciprocalDelta mass spin charge y.1 * Real.sin polar ^ (2 : ℕ) *
        kerrNewmanReciprocalSigma spin polar y.1 ^ (2 : ℕ) := by
  rw [show y.1 ^ (6 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
      (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
        (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar)).det =
      y.1 ^ (6 : ℕ) *
        (kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
          (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
            (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar)).det) by ring]
  rw [belinskiZakharovDressedKerrNewmanKillingBlock_det_cleared]
  have hSigma := kerrNewmanSigma_reciprocalClearing spin polar y
  have hDelta := kerrNewmanDelta_reciprocalClearing mass spin charge y
  calc
    y.1 ^ (6 : ℕ) *
        (-kerrNewmanDelta mass spin charge y.1⁻¹ * Real.sin polar ^ (2 : ℕ) *
          kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ)) =
      -(y.1 ^ (2 : ℕ) * kerrNewmanDelta mass spin charge y.1⁻¹) * Real.sin polar ^ (2 : ℕ) *
        (y.1 ^ (2 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar) ^ (2 : ℕ) := by ring
    _ = _ := by rw [hDelta, hSigma]

/-- One-pole spectral BZ dressing preserves the same reciprocal horizon carrier. -/
theorem belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_det_reciprocalCleared
    (spectral pole residue mass spin charge polar : ℝ) (y : {z : ℝ // z ≠ 0}) :
    y.1 ^ (6 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
        (belinskiZakharovDressing
          (belinskiZakharovOnePoleDressing spectral pole residue)
          (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar)).det =
      -kerrNewmanReciprocalDelta mass spin charge y.1 * Real.sin polar ^ (2 : ℕ) *
        kerrNewmanReciprocalSigma spin polar y.1 ^ (2 : ℕ) := by
  rw [show y.1 ^ (6 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
      (belinskiZakharovDressing
        (belinskiZakharovOnePoleDressing spectral pole residue)
        (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar)).det =
      y.1 ^ (6 : ℕ) *
        (kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ) *
          (belinskiZakharovDressing
            (belinskiZakharovOnePoleDressing spectral pole residue)
            (kerrNewmanKillingBlock mass spin charge y.1⁻¹ polar)).det) by ring]
  rw [belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_det_cleared]
  have hSigma := kerrNewmanSigma_reciprocalClearing spin polar y
  have hDelta := kerrNewmanDelta_reciprocalClearing mass spin charge y
  calc
    y.1 ^ (6 : ℕ) *
        (-kerrNewmanDelta mass spin charge y.1⁻¹ * Real.sin polar ^ (2 : ℕ) *
          kerrNewmanSigma spin y.1⁻¹ polar ^ (2 : ℕ)) =
      -(y.1 ^ (2 : ℕ) * kerrNewmanDelta mass spin charge y.1⁻¹) * Real.sin polar ^ (2 : ℕ) *
        (y.1 ^ (2 : ℕ) * kerrNewmanSigma spin y.1⁻¹ polar) ^ (2 : ℕ) := by ring
    _ = _ := by rw [hDelta, hSigma]

/-! ## Vaidya horizon factorization -/

/-- Denominator-cleared Vaidya horizon polynomial. -/
def vaidyaClearedHorizonPolynomial (evaporation radius : ℝ) : ℝ :=
  radius - 1 - 4 * evaporation * radius ^ (2 : ℕ)

theorem vaidyaConformalHorizonFunction_clearing
    (evaporation : ℝ) (radius : {x : ℝ // x ≠ 0}) :
    radius.1 * vaidyaConformalHorizonFunction evaporation radius.1 =
      vaidyaClearedHorizonPolynomial evaporation radius.1 := by
  unfold vaidyaConformalHorizonFunction vaidyaClearedHorizonPolynomial
  field_simp [radius.2]

/-- Polynomial in horizon-ratio coordinates after clearing `(1+q)^(2 : ℕ)`. -/
def vaidyaHorizonRatioPolynomial (q radius : ℝ) : ℝ :=
  q * radius ^ (2 : ℕ) - (1 + q) ^ (2 : ℕ) * radius + (1 + q) ^ (2 : ℕ)

/-- Exact event/outer-horizon factorization, with all degenerate ratio branches retained. -/
theorem vaidyaHorizonRatioPolynomial_factor (q radius : ℝ) :
    vaidyaHorizonRatioPolynomial q radius =
      (radius - (1 + q)) * (q * radius - (1 + q)) := by
  unfold vaidyaHorizonRatioPolynomial
  ring

theorem vaidyaHorizonRatioPolynomial_eq_zero_iff (q radius : ℝ) :
    vaidyaHorizonRatioPolynomial q radius = 0 ↔
      radius = 1 + q ∨ q * radius = 1 + q := by
  rw [vaidyaHorizonRatioPolynomial_factor, mul_eq_zero]
  constructor
  · rintro (h | h) <;> [left; right] <;> linarith
  · rintro (h | h) <;> [left; right] <;> linarith

/-- Existing Vaidya function is exactly the factorized polynomial on its honest chart. -/
theorem vaidyaConformalHorizonFunction_ratioPolynomial
    (q : {u : ℝ // 1 + u ≠ 0}) (radius : {x : ℝ // x ≠ 0}) :
    (1 + q.1) ^ (2 : ℕ) * radius.1 *
        vaidyaConformalHorizonFunction
          (vaidyaMassRateOfHorizonRatio q.1) radius.1 =
      -vaidyaHorizonRatioPolynomial q.1 radius.1 := by
  rw [mul_assoc, vaidyaConformalHorizonFunction_clearing]
  unfold vaidyaClearedHorizonPolynomial vaidyaMassRateOfHorizonRatio
    vaidyaHorizonRatioPolynomial
  have hqSq : (1 + q.1) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 q.2
  have hden : 4 * (1 + q.1) ^ (2 : ℕ) ≠ 0 := mul_ne_zero (by norm_num) hqSq
  field_simp [hden]
  have hcancel : (1 + q.1) ^ (2 : ℕ) *
      (q.1 * radius.1 ^ (2 : ℕ) / (1 + q.1) ^ (2 : ℕ)) = q.1 * radius.1 ^ (2 : ℕ) :=
    mul_div_cancel₀ _ hqSq
  calc
    (1 + q.1) ^ (2 : ℕ) *
        (radius.1 - 1 - q.1 * radius.1 ^ (2 : ℕ) / (1 + q.1) ^ (2 : ℕ)) =
      (1 + q.1) ^ (2 : ℕ) * (radius.1 - 1) - q.1 * radius.1 ^ (2 : ℕ) := by
        rw [mul_sub, hcancel]
    _ = -(radius.1 * (q.1 * radius.1 - (1 + q.1) ^ (2 : ℕ)) +
        (1 + q.1) ^ (2 : ℕ)) := by ring

/-! ## Reciprocal infinity in projective rational dynamics -/

/-- Paper-style positive/negative reciprocal patch reflection for the qubit infinity germ. -/
theorem postselectedQubit_infinityLocalDisplacement_reflect (w : ℚ) :
    (1 + (-w) ^ (2 : ℕ)) + ((-w) ^ (2 : ℕ) - 1) =
      (1 + w ^ (2 : ℕ)) + (w ^ (2 : ℕ) - 1) := by
  rw [postselectedQubit_infinityLocalDisplacementNumerator,
    postselectedQubit_infinityLocalDisplacementNumerator]
  ring

theorem postselectedQubit_infinityLocalDisplacement_eq_zero_iff (w : ℚ) :
    (1 + w ^ (2 : ℕ)) + (w ^ (2 : ℕ) - 1) = 0 ↔ w = 0 := by
  rw [postselectedQubit_infinityLocalDisplacementNumerator]
  constructor
  · intro h
    have : w ^ (2 : ℕ) = 0 := by linarith
    exact sq_eq_zero_iff.mp this
  · intro h
    simp [h]

end

end GaloisForLFunctions.HTGeometry
