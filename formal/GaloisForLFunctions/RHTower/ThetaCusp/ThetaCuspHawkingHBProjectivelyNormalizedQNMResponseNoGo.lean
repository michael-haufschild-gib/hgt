import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBAdjointQNMComplexBilinearPositivityNoGo

/-!
# Projectively normalized QNM response is nonselective for HB

The surviving HB off-diagonal proposal uses a complex-bilinear source/QNM projection rather than
a forbidden diagonal positive form.  Physical QNM excitation, however, is normalized: source-mode
overlap is divided by the bilinear mode norm and the resulting coefficient multiplies the mode.

For an arbitrary complex-bilinear form `B`, source `s`, and mode `m`, define

`c(s,m) = B(s,m) / B(m,m)`,  `R(s,m) = c(s,m) m`.

Under a nonzero mode rescaling `m -> z m`, the numerator has weight `z`, the denominator weight
`z²`, and the coefficient weight `z⁻¹`.  Thus the returned field `R` is exactly invariant.  This
reciprocal phase lock is automatic algebra, not a dynamical sign.

More strongly, the one-dimensional multiplication pairing with source equal to an arbitrary
target and mode `1` realizes every complex returned field, with nonzero mode norm and full
projective invariance.  It therefore realizes every canonical HB full-cokernel orbit, including
tilted fibres, without any arithmetic premise.

Consequently existence and projective covariance of a normalized off-diagonal QNM response cannot
be the RH-bearing step in

`normalized QNM response` -> `fixed Peierls orientation` -> `causal-cut extinction` -> `RH`.

The positive survivor is source-semantic: derive the literal Einstein--Teukolsky bilinear form,
source, causal contour/domain, and opposite Ward sign.  QNM normalization itself contributes no
selection.

`[PROVED HERE] [LEAN-PROVED] [HB ROUTE-CLASS KILL] [PROJECTIVE QNM NORMALIZATION]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Bilinearly normalized source-to-QNM excitation coefficient. -/
def d4HBAdjointQNMNormalizedExcitationCoefficient
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (source mode : X) : ℂ :=
  B source mode / B mode mode

/-- Physical returned field obtained by multiplying the normalized coefficient by its QNM. -/
def d4HBAdjointQNMNormalizedReturnedField
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (source mode : X) : X :=
  d4HBAdjointQNMNormalizedExcitationCoefficient B source mode • mode

/-- Mode rescaling gives the normalized excitation coefficient inverse weight. -/
theorem d4HBAdjointQNMNormalizedExcitationCoefficient_mode_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (source mode : X)
    {z : ℂ} (hz : z ≠ 0) (hnorm : B mode mode ≠ 0) :
    d4HBAdjointQNMNormalizedExcitationCoefficient B source (z • mode) =
      z⁻¹ * d4HBAdjointQNMNormalizedExcitationCoefficient B source mode := by
  simp only [d4HBAdjointQNMNormalizedExcitationCoefficient,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp [hz, hnorm]

/-- The normalized returned QNM field is exactly invariant under every nonzero mode rescaling. -/
theorem d4HBAdjointQNMNormalizedReturnedField_mode_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (source mode : X)
    {z : ℂ} (hz : z ≠ 0) (hnorm : B mode mode ≠ 0) :
    d4HBAdjointQNMNormalizedReturnedField B source (z • mode) =
      d4HBAdjointQNMNormalizedReturnedField B source mode := by
  rw [d4HBAdjointQNMNormalizedReturnedField,
    d4HBAdjointQNMNormalizedExcitationCoefficient_mode_smul B source mode hz hnorm,
    d4HBAdjointQNMNormalizedReturnedField]
  simp only [smul_smul]
  have hzunit : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  rw [show (z⁻¹ * d4HBAdjointQNMNormalizedExcitationCoefficient B source mode) * z =
      d4HBAdjointQNMNormalizedExcitationCoefficient B source mode by
    calc
      (z⁻¹ * d4HBAdjointQNMNormalizedExcitationCoefficient B source mode) * z =
          (z⁻¹ * z) * d4HBAdjointQNMNormalizedExcitationCoefficient B source mode := by ring
      _ = d4HBAdjointQNMNormalizedExcitationCoefficient B source mode := by
        rw [hzunit, one_mul]]

/-- One-dimensional nondegenerate complex-bilinear model used for universal target realization. -/
def d4HBComplexMultiplicationBilinear : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun x y : ℂ => x * y)
    (by intro x y z; ring)
    (by intro c x y; ring)
    (by intro x y z; ring)
    (by intro c x y; ring)

/-- A complex target has a nondegenerate normalized QNM realization which is invariant under every
nonzero change of mode representative. -/
def D4HBProjectivelyNormalizedQNMResponseRealizes (value : ℂ) : Prop :=
  ∃ (B : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) (source mode : ℂ),
    B mode mode ≠ 0 ∧
      d4HBAdjointQNMNormalizedReturnedField B source mode = value ∧
      ∀ z : ℂ, z ≠ 0 →
        d4HBAdjointQNMNormalizedReturnedField B source (z • mode) = value

/-- Universal target fitting: projectively normalized QNM response realizes every complex value. -/
theorem d4HBProjectivelyNormalizedQNMResponseRealizes (value : ℂ) :
    D4HBProjectivelyNormalizedQNMResponseRealizes value := by
  refine ⟨d4HBComplexMultiplicationBilinear, value, 1, ?_, ?_, ?_⟩
  · simp [d4HBComplexMultiplicationBilinear]
  · simp [d4HBAdjointQNMNormalizedReturnedField,
      d4HBAdjointQNMNormalizedExcitationCoefficient,
      d4HBComplexMultiplicationBilinear]
  · intro z hz
    rw [d4HBAdjointQNMNormalizedReturnedField_mode_smul
      d4HBComplexMultiplicationBilinear value 1 hz]
    · simp [d4HBAdjointQNMNormalizedReturnedField,
        d4HBAdjointQNMNormalizedExcitationCoefficient,
        d4HBComplexMultiplicationBilinear]
    · simp [d4HBComplexMultiplicationBilinear]

/-- Projectively normalized QNM realization of one canonical HB full-cokernel orbit value. -/
def D4HBProjectivelyNormalizedFullCokernelQNMResponseAt
    (n : ℕ) (q : XiZeroCopy) : Prop :=
  D4HBProjectivelyNormalizedQNMResponseRealizes
    (hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q)

/-- Every HB orbit, on or off the critical wall, has the normalized projective realization. -/
theorem d4HBProjectivelyNormalizedFullCokernelQNMResponseAt
    (n : ℕ) (q : XiZeroCopy) :
    D4HBProjectivelyNormalizedFullCokernelQNMResponseAt n q := by
  exact d4HBProjectivelyNormalizedQNMResponseRealizes _

/-- Closed route class: normalized projective QNM response existence is universally target-fitted
and therefore cannot provide HB's missing physical orientation. -/
def D4HBProjectivelyNormalizedQNMResponseExistenceRouteKilled : Prop :=
  (∀ value : ℂ, D4HBProjectivelyNormalizedQNMResponseRealizes value) ∧
    ∀ (n : ℕ) (q : XiZeroCopy),
      D4HBProjectivelyNormalizedFullCokernelQNMResponseAt n q

/-- Premise-free certificate killing projectively normalized QNM response existence as an HB
producer. -/
theorem d4HBProjectivelyNormalizedQNMResponseExistenceRouteKilled :
    D4HBProjectivelyNormalizedQNMResponseExistenceRouteKilled := by
  exact ⟨d4HBProjectivelyNormalizedQNMResponseRealizes,
    d4HBProjectivelyNormalizedFullCokernelQNMResponseAt⟩

end

end RHTower
