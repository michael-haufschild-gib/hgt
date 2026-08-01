import GaloisForLFunctions.HTGeometry.TailScalingAutomorphism
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The scalings as a group action

The scalings compose by multiplying their scalars, so they give a homomorphism from the units of the
constants to the automorphisms of the polynomial ring in the parameters.  Restricted to the `n`-th
roots of unity it is faithful and fixes every tail coefficient.

This is the group of deck transformations of the Kummer covering: it acts trivially on the
coefficient field and simply transitively on the choices of the first parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

theorem varScaleHom_one : varScaleHom K n 1 = AlgHom.id K (MvPolynomial (Fin n) K) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [varScaleHom_X, one_pow, map_one, one_mul]
  rfl

theorem varScaleHom_comp (ζ η : K) :
    (varScaleHom K n ζ).comp (varScaleHom K n η) = varScaleHom K n (ζ * η) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, varScaleHom_X, map_mul, varScaleHom_X, varScaleHom_C, ← mul_assoc,
    ← map_mul, ← mul_pow, mul_comm η ζ, varScaleHom_X]

theorem varScaleHom_mul_apply (ζ η : K) (p : MvPolynomial (Fin n) K) :
    varScaleHom K n ζ (varScaleHom K n η p) = varScaleHom K n (ζ * η) p := by
  have h := varScaleHom_comp (K := K) (n := n) ζ η
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) h

/-- The scaling attached to a unit of the constants. -/
noncomputable def varScaleUnit (K : Type*) [Field K] (n : ℕ) (u : Kˣ) :
    MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K :=
  varScale K n (Units.ne_zero u)

theorem varScaleUnit_apply (u : Kˣ) (p : MvPolynomial (Fin n) K) :
    varScaleUnit K n u p = varScaleHom K n ((u : K)) p := rfl

/-- **The scalings form a group of automorphisms.** -/
noncomputable def varScaleAut (K : Type*) [Field K] (n : ℕ) :
    Kˣ →* RingAut (MvPolynomial (Fin n) K) where
  toFun u := (varScaleUnit K n u).toRingEquiv
  map_one' := by
    refine RingEquiv.ext fun p => ?_
    have h : varScaleUnit K n 1 p = varScaleHom K n ((1 : Kˣ) : K) p := rfl
    rw [show ((1 : Kˣ) : K) = 1 from rfl] at h
    have h1 : varScaleHom K n (1 : K) p = p := by
      rw [show varScaleHom K n (1 : K) p = (varScaleHom K n (1 : K)) p from rfl,
        varScaleHom_one]
      rfl
    exact h.trans h1
  map_mul' u v := by
    refine RingEquiv.ext fun p => ?_
    show varScaleHom K n ((u * v : Kˣ) : K) p = varScaleHom K n ((u : K)) (varScaleHom K n ((v : K)) p)
    rw [varScaleHom_mul_apply, Units.val_mul]

theorem varScaleAut_apply (u : Kˣ) (p : MvPolynomial (Fin n) K) :
    varScaleAut K n u p = varScaleHom K n ((u : K)) p := rfl

/-! ## The roots of unity as deck transformations

The polynomial ring already carries a scalar action of the units of the constants, so the scalings
are not packaged as a second action on the same type; they are recorded as a homomorphism into the
automorphism group, which is what the fixed-field theorem consumes. -/

/-- The deck transformations: the scalings attached to the `n`-th roots of unity. -/
noncomputable def rootsOfUnityScale (K : Type*) [Field K] (n : ℕ) :
    rootsOfUnity n K →* RingAut (MvPolynomial (Fin n) K) :=
  (varScaleAut K n).comp (rootsOfUnity n K).subtype

theorem rootsOfUnityScale_apply (u : rootsOfUnity n K) (p : MvPolynomial (Fin n) K) :
    rootsOfUnityScale K n u p = varScaleHom K n (((u : Kˣ) : K)) p := rfl

theorem rootsOfUnity_pow_eq_one (u : rootsOfUnity n K) : (((u : Kˣ)) : K) ^ n = 1 := by
  have h1 : ((u : Kˣ)) ^ n = 1 := by
    have h := u.2
    rwa [mem_rootsOfUnity] at h
  calc (((u : Kˣ)) : K) ^ n = (((u : Kˣ) ^ n : Kˣ) : K) := by rw [Units.val_pow_eq_pow_val]
    _ = 1 := by rw [h1, Units.val_one]

/-- **The deck transformations fix every tail coefficient.** -/
theorem rootsOfUnityScale_tailCoeff (u : rootsOfUnity n K) (j : Fin n) :
    rootsOfUnityScale K n u (tailCoeff K n j) = tailCoeff K n j := by
  rw [rootsOfUnityScale_apply]
  exact varScaleHom_tailCoeff_of_pow_eq_one (rootsOfUnity_pow_eq_one u) j

/-- **The deck transformations move the first parameter.** -/
theorem rootsOfUnityScale_X_zero (u : rootsOfUnity n K) {j : Fin n} (hj : (j : ℕ) = 0) :
    rootsOfUnityScale K n u (MvPolynomial.X j) =
      MvPolynomial.C (((u : Kˣ) : K)) * MvPolynomial.X j := by
  rw [rootsOfUnityScale_apply, varScaleHom_X_zero hj]

/-- **Distinct roots of unity give distinct deck transformations.** -/
theorem rootsOfUnityScale_injective [NeZero n] :
    Function.Injective (rootsOfUnityScale K n) := by
  intro u v h
  have h0 := congrArg (fun f : RingAut (MvPolynomial (Fin n) K) =>
    f (MvPolynomial.X (0 : Fin n))) h
  rw [rootsOfUnityScale_X_zero u rfl, rootsOfUnityScale_X_zero v rfl] at h0
  have hX : (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) K) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  have hC := mul_right_cancel₀ hX h0
  exact Subtype.ext (Units.ext (MvPolynomial.C_injective (Fin n) K hC))

end GaloisForLFunctions.HTGeometry
