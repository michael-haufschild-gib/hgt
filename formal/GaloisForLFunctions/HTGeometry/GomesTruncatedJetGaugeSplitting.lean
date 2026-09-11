import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeCharacter
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetNilpotentPart

/-!
# Every actual gauge symmetry splits into scalar and unipotent factors

The character kernel is exactly the literal unipotent subgroup. Removing the
scalar is a group homomorphism, and it gives a direct product decomposition of
the entire gauge group for every phase and finite jet horizon.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The character kernel inside the actual matrix gauge group. -/
def gomesTruncatedJetUnipotentGroup (n : ℕ) (z : ℂ) :
    Subgroup (gomesTruncatedJetGaugeGroup n z) := (gomesTruncatedJetGaugeCharacter n z).ker

/-- The character kernel consists exactly of matrices satisfying the literal unipotence equation. -/
theorem gomesTruncatedJetUnipotentGroup_mem_iff (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    u ∈ gomesTruncatedJetUnipotentGroup n z ↔ (u.val.val - 1) ^ (n + 1) = 0 := by
  rw [gomesTruncatedJetUnipotentGroup, MonoidHom.mem_ker,
    gomesTruncatedJetJointAlgebra_unipotent_iff n z ⟨u.val.val, u.property⟩]
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

/-- Removing the observed scalar is a homomorphism onto the unipotent factor. -/
def gomesTruncatedJetUnipotentPart (n : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z →* gomesTruncatedJetUnipotentGroup n z where
  toFun u := ⟨(gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u))⁻¹ * u, by
    change gomesTruncatedJetGaugeCharacter n z _ = 1
    rw [map_mul, map_inv, gomesTruncatedJetGaugeCharacter_scalarSection, inv_mul_cancel]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    change (gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z (u * v)))⁻¹ *
      (u * v) = ((gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u))⁻¹ * u) *
        ((gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z v))⁻¹ * v)
    rw [map_mul, map_mul, mul_inv_rev]
    rw [mul_comm ((gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z v))⁻¹)
      ((gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u))⁻¹)]
    exact mul_mul_mul_comm _ _ _ _

/-- The unipotent factor has the exact scalar-normalization formula in the gauge group. -/
theorem gomesTruncatedJetUnipotentPart_val (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    (gomesTruncatedJetUnipotentPart n z u).val =
      (gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u))⁻¹ * u := rfl

/-- The entire actual gauge group is the direct product of nonzero scalars and its unipotent subgroup. -/
def gomesTruncatedJetGaugeSplitting (n : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z ≃* ℂˣ × gomesTruncatedJetUnipotentGroup n z where
  toFun u := (gomesTruncatedJetGaugeCharacter n z u, gomesTruncatedJetUnipotentPart n z u)
  invFun v := gomesTruncatedJetScalarSection n z v.1 * v.2.val
  left_inv u := by
    change gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u) *
      ((gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u))⁻¹ * u) = u
    exact mul_inv_cancel_left _ _
  right_inv v := by
    have hv : gomesTruncatedJetGaugeCharacter n z v.2.val = 1 := v.2.property
    apply Prod.ext
    · change gomesTruncatedJetGaugeCharacter n z (gomesTruncatedJetScalarSection n z v.1 * v.2.val) = v.1
      rw [map_mul, gomesTruncatedJetGaugeCharacter_scalarSection, hv, mul_one]
    · apply Subtype.ext
      change (gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z
        (gomesTruncatedJetScalarSection n z v.1 * v.2.val)))⁻¹ *
        (gomesTruncatedJetScalarSection n z v.1 * v.2.val) = v.2.val
      rw [map_mul, gomesTruncatedJetGaugeCharacter_scalarSection, hv, mul_one, inv_mul_cancel_left]
  map_mul' u v := by
    apply Prod.ext
    · exact map_mul _ u v
    · exact map_mul _ u v

/-- The direct-product scalar coordinate is the literal matrix character. -/
theorem gomesTruncatedJetGaugeSplitting_fst (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    (gomesTruncatedJetGaugeSplitting n z u).1 = gomesTruncatedJetGaugeCharacter n z u := rfl

/-- Recombining arbitrary scalar and unipotent factors recovers an actual gauge symmetry. -/
theorem gomesTruncatedJetGaugeSplitting_symm (n : ℕ) (z : ℂ) (c : ℂˣ)
    (v : gomesTruncatedJetUnipotentGroup n z) :
    (gomesTruncatedJetGaugeSplitting n z).symm (c, v) =
      gomesTruncatedJetScalarSection n z c * v.val := rfl

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
