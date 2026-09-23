import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-!
# Inverse-response Ward mechanics

An invertible formed law couples all of its logarithmic intervention currents.  For two
derivations `D₁,D₂`, an inverse pair `M * E = 1`, and currents `Θᵢ = M * Dᵢ E`, the mixed response
identity is

`D₁ Θ₂ + Θ₁ * Θ₂ = M * D₁ (D₂ E)`.

It reconstructs mixed source acceleration.  If that acceleration vanishes, the fused product is
a total derivative, so every additive reporter annihilating `D₁` kills it.  All statements below
are unconditional algebraic theorems; no arithmetic selection premise is imported.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The logarithmic response current formed by an inverse `M` and an intervention derivation. -/
def inverseResponseCurrent (D : Derivation R A A) (M E : A) : A :=
  M * D E

/-- Differentiating an inverse formation couples the inverse response to its logarithmic current. -/
theorem derivation_inverse_eq_neg_mul_inverseResponseCurrent
    (D : Derivation R A A) {M E : A} (hME : M * E = 1) :
    D M = -M * inverseResponseCurrent D M E := by
  have hproduct : D M * E + M * D E = 0 := by
    calc
      D M * E + M * D E = D (M * E) := by
        calc
          D M * E + M * D E = M * D E + E * D M := by ring
          _ = D (M * E) := (D.leibniz M E).symm
      _ = D 1 := by rw [hME]
      _ = 0 := Derivation.map_one_eq_zero D
  have hEM : E * M = 1 := by simpa [mul_comm] using hME
  rw [inverseResponseCurrent]
  calc
    D M = D M * (E * M) := by rw [hEM, mul_one]
    _ = (D M * E + M * D E) * M - (M * D E) * M := by ring
    _ = -M * (M * D E) := by rw [hproduct]; ring

/-- Equivalent square form of the inverse derivative. -/
theorem derivation_inverse_eq_neg_sq_mul
    (D : Derivation R A A) {M E : A} (hME : M * E = 1) :
    D M = -(M ^ (2 : ℕ)) * D E := by
  rw [derivation_inverse_eq_neg_mul_inverseResponseCurrent D hME,
    inverseResponseCurrent]
  ring

/-- **Mixed inverse-response Riccati law.**  No commutation of the two derivations is required. -/
theorem mixed_inverseResponseCurrent_riccati
    (D₁ D₂ : Derivation R A A) {M E : A} (hME : M * E = 1) :
    D₁ (inverseResponseCurrent D₂ M E) +
        inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E =
      M * D₁ (D₂ E) := by
  rw [inverseResponseCurrent, Derivation.leibniz,
    derivation_inverse_eq_neg_sq_mul D₁ hME]
  simp only [inverseResponseCurrent]
  ring

/-- The two formed currents reconstruct the mixed source acceleration exactly. -/
theorem mixed_sourceAcceleration_reconstruction
    (D₁ D₂ : Derivation R A A) {M E : A} (hME : M * E = 1) :
    D₁ (D₂ E) =
      E * (D₁ (inverseResponseCurrent D₂ M E) +
        inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E) := by
  rw [mixed_inverseResponseCurrent_riccati D₁ D₂ hME]
  have hEM : E * M = 1 := by simpa [mul_comm] using hME
  rw [← mul_assoc, hEM, one_mul]

/-- The diagonal shadow is the ordinary inverse-response Riccati equation. -/
theorem inverseResponseCurrent_riccati
    (D : Derivation R A A) {M E : A} (hME : M * E = 1) :
    D (inverseResponseCurrent D M E) + inverseResponseCurrent D M E ^ (2 : ℕ) =
      M * D (D E) := by
  simpa [pow_two] using mixed_inverseResponseCurrent_riccati D D hME

/-- Mixed-affine source response makes the fused current product an exact derivative. -/
theorem inverseResponseCurrent_mul_eq_neg_derivation_of_mixed_affine
    (D₁ D₂ : Derivation R A A) {M E : A} (hME : M * E = 1)
    (haffine : D₁ (D₂ E) = 0) :
    inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E =
      -D₁ (inverseResponseCurrent D₂ M E) := by
  have h := mixed_inverseResponseCurrent_riccati D₁ D₂ hME
  rw [haffine, mul_zero] at h
  calc
    inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E =
        (D₁ (inverseResponseCurrent D₂ M E) +
          inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E) -
            D₁ (inverseResponseCurrent D₂ M E) := by ring
    _ = -D₁ (inverseResponseCurrent D₂ M E) := by rw [h]; ring

/-- **Ward conservation.**  A reporter annihilating total `D₁`-responses kills the fused product. -/
theorem inverseResponseCurrent_ward_conservation
    {B : Type*} [AddCommGroup B] (D₁ D₂ : Derivation R A A) {M E : A}
    (hME : M * E = 1) (haffine : D₁ (D₂ E) = 0) (τ : A →+ B)
    (hτ : ∀ x : A, τ (D₁ x) = 0) :
    τ (inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E) = 0 := by
  rw [inverseResponseCurrent_mul_eq_neg_derivation_of_mixed_affine D₁ D₂ hME haffine,
    map_neg, hτ, neg_zero]

/-- **Anomalous Ward balance.**  A nonconservative reporter reads the fused product as source
acceleration minus its boundary anomaly. -/
theorem inverseResponseCurrent_anomalous_ward_balance
    {B : Type*} [AddCommGroup B] (D₁ D₂ : Derivation R A A) {M E : A}
    (hME : M * E = 1) (τ β : A →+ B)
    (hτD : ∀ x : A, τ (D₁ x) = β x) :
    τ (inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E) =
      τ (M * D₁ (D₂ E)) - β (inverseResponseCurrent D₂ M E) := by
  have h := congrArg τ (mixed_inverseResponseCurrent_riccati D₁ D₂ hME)
  rw [map_add, hτD] at h
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using h

/-- Under mixed affinity, all surviving fused response is the negative boundary anomaly. -/
theorem inverseResponseCurrent_anomalous_ward_of_mixed_affine
    {B : Type*} [AddCommGroup B] (D₁ D₂ : Derivation R A A) {M E : A}
    (hME : M * E = 1) (haffine : D₁ (D₂ E) = 0) (τ β : A →+ B)
    (hτD : ∀ x : A, τ (D₁ x) = β x) :
    τ (inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E) =
      -β (inverseResponseCurrent D₂ M E) := by
  rw [inverseResponseCurrent_anomalous_ward_balance D₁ D₂ hME τ β hτD,
    haffine, mul_zero, map_zero, zero_sub]

/-- A strict linear Ward reporter is blind on every nonzero derivation eigengrade. -/
theorem conservativeReporter_eq_zero_on_nonzero_eigenweight
    {K C : Type*} [Field K] [CommRing C] [Algebra K C]
    (D : Derivation K C C) (τ : C →ₗ[K] K) (hτ : ∀ x : C, τ (D x) = 0)
    {x : C} {w : K} (hw : w ≠ 0) (hx : D x = w • x) :
    τ x = 0 := by
  have h := hτ x
  rw [hx, LinearMap.map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hw

/-- A faithful square reporter turns diagonal Ward conservation into exact current selection. -/
theorem inverseResponseCurrent_eq_zero_of_faithful_squareReporter
    {B : Type*} [AddCommGroup B] (D : Derivation R A A) {M E : A}
    (hME : M * E = 1) (haffine : D (D E) = 0) (τ : A →+ B)
    (hτ : ∀ x : A, τ (D x) = 0)
    (hfaithful : ∀ x : A, τ (x ^ (2 : ℕ)) = 0 → x = 0) :
    inverseResponseCurrent D M E = 0 := by
  apply hfaithful
  simpa [pow_two] using
    inverseResponseCurrent_ward_conservation D D hME haffine τ hτ

/-- One capstone packages inverse response, mixed reconstruction, and Ward conservation. -/
theorem inverseResponseWardMechanics_capstone
    {B : Type*} [AddCommGroup B] (D₁ D₂ : Derivation R A A) {M E : A}
    (hME : M * E = 1) (haffine : D₁ (D₂ E) = 0) (τ : A →+ B)
    (hτ : ∀ x : A, τ (D₁ x) = 0) :
    D₁ (D₂ E) =
        E * (D₁ (inverseResponseCurrent D₂ M E) +
          inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E) ∧
      inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E =
        -D₁ (inverseResponseCurrent D₂ M E) ∧
      τ (inverseResponseCurrent D₁ M E * inverseResponseCurrent D₂ M E) = 0 := by
  exact ⟨mixed_sourceAcceleration_reconstruction D₁ D₂ hME,
    inverseResponseCurrent_mul_eq_neg_derivation_of_mixed_affine D₁ D₂ hME haffine,
    inverseResponseCurrent_ward_conservation D₁ D₂ hME haffine τ hτ⟩

end GaloisForLFunctions.HTGeometry
