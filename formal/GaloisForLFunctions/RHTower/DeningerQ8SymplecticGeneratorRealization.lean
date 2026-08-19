import GaloisForLFunctions.RHTower.DeningerArithmeticQuaternionicTransitionNoReal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic

/-!
# The standard symplectic generator realization of `Q₈`

This is the finite representation-theoretic portion of the quaternion-field
input in Deninger's Theorem 2.13.  The two explicitly realized transition
generators satisfy the quaternion presentation and preserve a nondegenerate
alternating complex bilinear form.  Consequently they are the standard
two-dimensional symplectic `Q₈` generator realization.

It deliberately stops before the arithmetic assertion that a *number field*
has this Galois group and that its Artin root number is `-1`: those are
separate published arithmetic inputs, not consequences of the finite matrix
calculation.
-/

namespace RHTower

noncomputable section

/-- The standard alternating form on the two-dimensional transition carrier. -/
def deningerQ8TransitionSymplectic : LinearMap.BilinForm ℂ (ℂ × ℂ) :=
  LinearMap.mk₂ ℂ (fun p q => p.1 * q.2 - p.2 * q.1)
    (fun p p' q => by
      rcases p with ⟨p₁, p₂⟩
      rcases p' with ⟨p'₁, p'₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp
      ring)
    (fun c p q => by
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp [smul_eq_mul]
      ring)
    (fun p q q' => by
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      rcases q' with ⟨q'₁, q'₂⟩
      simp
      ring)
    (fun c p q => by
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp [smul_eq_mul]
      ring)

@[simp]
theorem deningerQ8TransitionSymplectic_apply (p q : ℂ × ℂ) :
    deningerQ8TransitionSymplectic p q = p.1 * q.2 - p.2 * q.1 := rfl

/-- The standard form is alternating. -/
theorem deningerQ8TransitionSymplectic_isAlt :
    deningerQ8TransitionSymplectic.IsAlt := by
  intro p
  rcases p with ⟨x, y⟩
  simp [deningerQ8TransitionSymplectic_apply]
  ring

/-- The standard form is nondegenerate. -/
theorem deningerQ8TransitionSymplectic_nondegenerate :
    deningerQ8TransitionSymplectic.Nondegenerate := by
  refine deningerQ8TransitionSymplectic_isAlt.isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro p hp
  apply Prod.ext
  · have h := hp (0, 1)
    simpa [deningerQ8TransitionSymplectic_apply] using h
  · have h := hp (1, 0)
    have : -p.2 = 0 := by
      simpa [deningerQ8TransitionSymplectic_apply] using h
    simpa using neg_eq_zero.mp this

/-- First `Q₈` generator preserves the symplectic form. -/
theorem deningerQuaternionTransitionI_preserves_symplectic (p q : ℂ × ℂ) :
    deningerQ8TransitionSymplectic (deningerQuaternionTransitionI p)
      (deningerQuaternionTransitionI q) = deningerQ8TransitionSymplectic p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  simp [deningerQuaternionTransitionI, deningerQ8TransitionSymplectic_apply]
  calc
    -(Complex.I * x * (Complex.I * v)) + Complex.I * y * (Complex.I * u) =
        -(Complex.I * Complex.I) * x * v + (Complex.I * Complex.I) * y * u := by ring
    _ = x * v - y * u := by rw [Complex.I_mul_I]; ring

/-- Second `Q₈` generator preserves the symplectic form. -/
theorem deningerQuaternionTransitionK_preserves_symplectic (p q : ℂ × ℂ) :
    deningerQ8TransitionSymplectic (deningerQuaternionTransitionK p)
      (deningerQuaternionTransitionK q) = deningerQ8TransitionSymplectic p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  simp [deningerQuaternionTransitionK, deningerQ8TransitionSymplectic_apply]
  ring

/-- The two explicit transition generators are a symplectic realization of the
quaternion presentation: both square to the same central involution and they
anticommute. -/
theorem deningerQ8TransitionGeneratorRelations (p : ℂ × ℂ) :
    deningerQuaternionTransitionI (deningerQuaternionTransitionI p) = -p ∧
      deningerQuaternionTransitionK (deningerQuaternionTransitionK p) = -p ∧
      deningerQuaternionTransitionI (deningerQuaternionTransitionK p) =
        -deningerQuaternionTransitionK (deningerQuaternionTransitionI p) :=
  ⟨deningerQuaternionTransitionI_sq p, deningerQuaternionTransitionK_sq p,
    deningerQuaternionTransitionI_anticommutes_K p⟩

end

end RHTower
