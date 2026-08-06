import GaloisForLFunctions.HTGeometry.ReflectionRatFuncTransport

/-!
# Differential algebraicity is stable under reflection

The corpus transports differential algebraicity along an automorphism of the meromorphic field that
covers an automorphism of the coordinate field **and commutes with the jets**.  The reflection
covers such an automorphism but only *anti*-commutes: each derivation contributes a sign, so

```text
jet n (reflect x) = (-1)^n · reflect (jet n x).
```

Algebraic independence does not see that, because `(-1)^n` is a unit of the base field: rescaling
each generator of a family by a unit is the invertible substitution `X_p |-> (-1)^{p.2} X_p` on the
polynomial ring.  This file builds that substitution, proves it is an involution, and runs the
transport with the sign carried through.

The conclusion is that the differentially algebraic sector is reflection stable, which is what lets
the Barnes ladder — which holds modulo that sector — be moved across the reflection to the multiple
sine.
-/

open Filter Topology Set Function Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra

/-! ### The sign substitution -/

/-- The alternating unit attached to a jet index. -/
def jetSign (p : Unit × ℕ) : RatFunc ℂ := (-1) ^ p.2

theorem jetSign_mul_self (p : Unit × ℕ) : jetSign p * jetSign p = 1 := by
  unfold jetSign
  rw [← pow_add]
  rcases Nat.even_or_odd (p.2 + p.2) with h | h
  · exact h.neg_one_pow
  · exact absurd h (by simp)

/-- Rescaling every jet variable by its alternating unit. -/
def jetSignSub :
    MvPolynomial (Unit × ℕ) (RatFunc ℂ) →ₐ[RatFunc ℂ]
      MvPolynomial (Unit × ℕ) (RatFunc ℂ) :=
  MvPolynomial.aeval fun p =>
    algebraMap (RatFunc ℂ) (MvPolynomial (Unit × ℕ) (RatFunc ℂ)) (jetSign p) *
      MvPolynomial.X p

@[simp] theorem jetSignSub_X (p : Unit × ℕ) :
    jetSignSub (MvPolynomial.X p) =
      algebraMap (RatFunc ℂ) (MvPolynomial (Unit × ℕ) (RatFunc ℂ)) (jetSign p) *
        MvPolynomial.X p := by
  unfold jetSignSub
  rw [MvPolynomial.aeval_X]

/-- The sign substitution is an involution. -/
theorem jetSignSub_jetSignSub (R : MvPolynomial (Unit × ℕ) (RatFunc ℂ)) :
    jetSignSub (jetSignSub R) = R := by
  have hcomp : jetSignSub.comp jetSignSub = AlgHom.id (RatFunc ℂ) _ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, jetSignSub_X, map_mul, jetSignSub.commutes,
      jetSignSub_X, AlgHom.id_apply, ← mul_assoc, ← map_mul, jetSign_mul_self,
      map_one, one_mul]
  exact congrArg (fun f : MvPolynomial (Unit × ℕ) (RatFunc ℂ) →ₐ[RatFunc ℂ]
    MvPolynomial (Unit × ℕ) (RatFunc ℂ) => f R) hcomp

theorem jetSignSub_injective : Function.Injective jetSignSub := by
  intro P Q h
  have hP := jetSignSub_jetSignSub P
  have hQ := jetSignSub_jetSignSub Q
  rw [← hP, ← hQ, h]

/-- Evaluating after the sign substitution rescales the evaluation family. -/
theorem aeval_jetSignSub {A : Type*} [CommRing A] [Algebra (RatFunc ℂ) A]
    (f : Unit × ℕ → A) (R : MvPolynomial (Unit × ℕ) (RatFunc ℂ)) :
    MvPolynomial.aeval f (jetSignSub R) =
      MvPolynomial.aeval (fun p => algebraMap (RatFunc ℂ) A (jetSign p) * f p) R := by
  have hcomp : (MvPolynomial.aeval f).comp jetSignSub =
      MvPolynomial.aeval (fun p => algebraMap (RatFunc ℂ) A (jetSign p) * f p) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, jetSignSub_X, map_mul, AlgHom.commutes,
      MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  exact congrArg (fun g : MvPolynomial (Unit × ℕ) (RatFunc ℂ) →ₐ[RatFunc ℂ] A => g R) hcomp

/-! ### The signed transport -/

/-- **Differential algebraicity transports along an automorphism whose jets commute up to the
alternating unit of the base.** -/
theorem differentialAlgebraicOver_of_signed_transport
    {sigma : meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ)}
    {rho : RatFunc ℂ ≃+* RatFunc ℂ}
    (hjet : ∀ (n : ℕ) (y : meroField (Set.univ : Set ℂ)),
      differentialJet n (sigma y) =
        algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) ((-1 : RatFunc ℂ) ^ n) *
          sigma (differentialJet n y))
    (hbase : ∀ r : RatFunc ℂ,
      sigma (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r)
        = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (rho r))
    {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (sigma x) := by
  classical
  intro hindep
  refine hx ?_
  refine (algebraicIndependent_iff_injective_aeval).mpr fun P Q hPQ => ?_
  -- the sigma-image of an evaluation, read on the reindexed and rescaled polynomial
  have hval : ∀ R : MvPolynomial (Unit × ℕ) (RatFunc ℂ),
      sigma ((MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 x) R)
        = (MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 (sigma x))
          (jetSignSub (MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) R)) := by
    intro R
    have hleft := MvPolynomial.eval₂_comp_left
      (sigma : meroField (Set.univ : Set ℂ) →+* meroField (Set.univ : Set ℂ))
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
      (fun p : Unit × ℕ => differentialJet p.2 x) R
    have hcomp :
        (sigma : meroField (Set.univ : Set ℂ) →+* meroField (Set.univ : Set ℂ)).comp
          (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
          = (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).comp
            (rho : RatFunc ℂ →+* RatFunc ℂ) := by
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply]
      exact hbase r
    have hstep :
        sigma ((MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 x) R)
          = MvPolynomial.eval₂
              ((sigma : meroField (Set.univ : Set ℂ) →+*
                meroField (Set.univ : Set ℂ)).comp
                (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))))
              (fun p : Unit × ℕ => sigma (differentialJet p.2 x)) R := by
      simpa [MvPolynomial.aeval_def, Function.comp_def] using hleft
    have hrescale :
        (MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 (sigma x))
            (jetSignSub (MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) R))
          = (MvPolynomial.aeval fun p : Unit × ℕ => sigma (differentialJet p.2 x))
            (MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) R) := by
      rw [aeval_jetSignSub]
      have hfam : (fun p : Unit × ℕ =>
          algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (jetSign p) *
            differentialJet p.2 (sigma x))
          = fun p : Unit × ℕ => sigma (differentialJet p.2 x) := by
       funext p
       rw [hjet p.2 x]
       have hsq :
           algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (jetSign p) *
               algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
                 ((-1 : RatFunc ℂ) ^ p.2) = 1 := by
         rw [← map_mul]
         have hone : jetSign p * (-1 : RatFunc ℂ) ^ p.2 = 1 := jetSign_mul_self p
         rw [hone, map_one]
       calc
         algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (jetSign p) *
             (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
               ((-1 : RatFunc ℂ) ^ p.2) * sigma (differentialJet p.2 x))
             = (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (jetSign p) *
                 algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
                   ((-1 : RatFunc ℂ) ^ p.2)) * sigma (differentialJet p.2 x) := by
               ring
         _ = sigma (differentialJet p.2 x) := by rw [hsq, one_mul]
      rw [hfam]
    rw [hstep, hcomp, ← MvPolynomial.eval₂_map, hrescale]
    rfl
  have hmap :
      jetSignSub (MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) P)
        = jetSignSub (MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) Q) := by
    have h1 := hval P
    have h2 := hval Q
    rw [hPQ] at h1
    rw [h1] at h2
    have hindep' : AlgebraicIndependent (RatFunc ℂ)
        (fun p : Unit × ℕ => differentialJet p.2 (sigma x)) := hindep
    exact (algebraicIndependent_iff_injective_aeval).mp hindep' h2
  have hmap' : MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) P
      = MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) Q :=
    jetSignSub_injective hmap
  exact MvPolynomial.map_injective _ rho.injective hmap'

/-! ### The reflection case -/

/-- **Differential algebraicity is stable under reflection.** -/
theorem differentialAlgebraicOver_complexReflectionMeroEquiv (c : ℂ)
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (complexReflectionMeroEquiv c x) := by
  refine differentialAlgebraicOver_of_signed_transport (rho := ratReflectEquivBy c)
    (fun n y => ?_) (fun r => ?_) hx
  · rw [differentialJet_complexReflectionMeroEquiv c n y]
    congr 1
    rw [map_pow, map_neg, map_one]
  · exact complexReflectionMeroEquiv_ratfuncToMero c r

/-- **The differentially algebraic sector is reflection stable.** -/
theorem daSector_complexReflectionMeroEquiv (c : ℂ)
    {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ daSector) :
    complexReflectionMeroEquiv c x ∈ daSector :=
  differentialAlgebraicOver_complexReflectionMeroEquiv c hx

end

end GaloisForLFunctions.HTGeometry
