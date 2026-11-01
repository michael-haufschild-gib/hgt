import GaloisForLFunctions.HeckeKreinToeplitz.Index.OneNegativeDirection
import GaloisForLFunctions.HeckeKreinToeplitz.Index.PositiveCoefficients
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Positive coefficients perpendicular to a nonpositive eigenline

Pairing against a common eigenvector transforms by the reflected character.
Its kernel is invariant and positive whenever the eigenvector is nonzero
and nonpositive. Every orbit coefficient in that hyperplane is therefore
a positive-definite group kernel.
-/

noncomputable section
set_option autoImplicit false
open Complex Module
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The linear functional obtained by pairing against a fixed vector. -/
def pairingLinear (w : H × ℂ) : (H × ℂ) →ₗ[ℂ] ℂ where
  toFun := pairing w
  map_add' := pairing_add_right w
  map_smul' c v := pairing_smul_right c w v

/-- Eigencharacters act contragrediently on the associated pairing functional. -/
theorem pairing_action_right (ρ : G →* End ℂ (H × ℂ))
    (hρ : ∀ g u v, pairing (ρ g u) (ρ g v) = pairing u v)
    (χ : G →* ℂ) {w : H × ℂ} (hw : ∀ g, ρ g w = χ g • w)
    (g : G) (v : H × ℂ) :
    pairing w (ρ g v) = reflectChar χ g * pairing w v := by
  have he := hρ g (ρ g⁻¹ w) v
  have hcancel : ρ g (ρ g⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hcancel, hw g⁻¹, pairing_smul_left] at he
  exact he

/-- Coefficients in the positive hyperplane of a common eigenvector are positive definite. -/
theorem isPosDefCoefficient_of_nonpositive_eigenvector
    (ρ : G →* End ℂ (H × ℂ))
    (hρ : ∀ g u v, pairing (ρ g u) (ρ g v) = pairing u v)
    (χ : G →* ℂ) {w : H × ℂ} (hw : ∀ g, ρ g w = χ g • w)
    (hw0 : w ≠ 0) (hwq : (pairing w w).re ≤ 0)
    {r : H × ℂ} (hr : pairing w r = 0) :
    IsPosDefKernel (fun g => pairing r (ρ g r)) := by
  let W : Submodule ℂ (H × ℂ) := (pairingLinear w).ker
  have hinvariant (g : G) (v : W) : ρ g (v : H × ℂ) ∈ W := by
    change pairing w (ρ g (v : H × ℂ)) = 0
    rw [pairing_action_right ρ hρ χ hw]
    have hv : pairing w (v : H × ℂ) = 0 := v.property
    rw [hv, mul_zero]
  let σ : G →* End ℂ W :=
    { toFun := fun g =>
        { toFun := fun v => ⟨ρ g v.val, hinvariant g v⟩
          map_add' := fun u v => Subtype.ext ((ρ g).map_add u.val v.val)
          map_smul' := fun c v => Subtype.ext ((ρ g).map_smul c v.val) }
      map_one' := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        change ρ 1 v.val = v.val
        rw [map_one, Module.End.one_apply]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg (fun f : End ℂ (H × ℂ) => f v.val) (map_mul ρ g h) }
  have hform : IsHermitianForm (fun u v : W => pairing v.val u.val) :=
    { add_left := fun u v q => pairing_add_right q.val u.val v.val
      smul_left := fun c u v => pairing_smul_right c v.val u.val
      symm := fun u v => (pairing_conj_symm u.val v.val).symm }
  have hpos (u : W) : 0 ≤ (pairing u.val u.val).re :=
    nonneg_of_orthogonal_nonpositive hw0 hwq u.property
  exact isPosDefKernel_of_invariantHermitianForm σ hform hpos
    (fun g u v => hρ g v.val u.val) ⟨r, hr⟩

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
