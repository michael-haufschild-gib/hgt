import GaloisForLFunctions.HTGeometry.BoundedBelowRangeProjection
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Analytic.Constructions

/-!
# The derivative of the closed-range projection at the base point

For a differentiable family `t ↦ M_t` of bounded operators with `M_0 = 1`, the Gram operator
`A_t = Q M_t* M_t Q + (1 - Q)` satisfies `A_0 = 1`, so the projection

`P_t = M_t Q A_t⁻¹ Q M_t*`

is differentiable at `0` and

`P'_0 = (1 - Q) X Q + Q X* (1 - Q)`,   `X = M'_0`.

In particular the second fundamental form of the family is `(1 - Q) P'_0 Q = (1 - Q) X Q`.
-/

open ContinuousLinearMap

namespace HTGeometry

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The adjoint as a continuous real-linear map of the operator algebra. -/
noncomputable def adjointRealCLM : (H →L[ℂ] H) →L[ℝ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add _ A B
      map_smul' := fun r A => by
        have hsmul : (r : ℝ) • A = ((r : ℂ)) • A :=
          (IsScalarTower.algebraMap_smul ℂ r A).symm
        have hadj : ContinuousLinearMap.adjoint (((r : ℂ)) • A)
            = (starRingEnd ℂ ((r : ℂ))) • ContinuousLinearMap.adjoint A :=
          map_smulₛₗ ContinuousLinearMap.adjoint _ _
        have hconj : (starRingEnd ℂ ((r : ℂ))) = ((r : ℂ)) := Complex.conj_ofReal r
        simp only [hsmul, hadj, hconj, RingHom.id_apply]
        exact (IsScalarTower.algebraMap_smul ℂ r (ContinuousLinearMap.adjoint A)) }
    1 (fun A => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact le_of_eq (LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint A))

@[simp] theorem adjointRealCLM_apply (A : H →L[ℂ] H) :
    adjointRealCLM A = ContinuousLinearMap.adjoint A := rfl

/-- Differentiating the adjoint of a differentiable operator family. -/
theorem hasDerivAt_adjoint {f : ℝ → (H →L[ℂ] H)} {X : H →L[ℂ] H} {t : ℝ}
    (hf : HasDerivAt f X t) :
    HasDerivAt (fun s => ContinuousLinearMap.adjoint (f s)) (ContinuousLinearMap.adjoint X) t := by
  have h := HasFDerivAt.comp_hasDerivAt t (ContinuousLinearMap.hasFDerivAt
    (adjointRealCLM (H := H))) hf
  simpa [Function.comp_def] using h

variable {Q : H →L[ℂ] H}

/-- At an identity base point the Gram operator is the identity. -/
theorem rangeProjectionGram_one (hQ2 : IsIdempotentElem Q) :
    rangeProjectionGram Q (1 : H →L[ℂ] H) = 1 := by
  have h : Q * Q = Q := hQ2
  have h1 : Q * (1 : H →L[ℂ] H) * (1 : H →L[ℂ] H) * Q = Q := by rw [mul_one, mul_one]; exact h
  rw [rangeProjectionGram, ContinuousLinearMap.adjoint_one, h1]
  abel

/-- Derivative of the Gram operator of a family through the identity. -/
theorem hasDerivAt_rangeProjectionGram {f : ℝ → (H →L[ℂ] H)} {X : H →L[ℂ] H}
    (hf : HasDerivAt f X 0) (hf0 : f 0 = 1) :
    HasDerivAt (fun t => rangeProjectionGram Q (f t))
      (Q * (ContinuousLinearMap.adjoint X + X) * Q) 0 := by
  have hg : HasDerivAt (fun s => ContinuousLinearMap.adjoint (f s))
      (ContinuousLinearMap.adjoint X) 0 := hasDerivAt_adjoint hf
  have hprod : HasDerivAt (fun t => ContinuousLinearMap.adjoint (f t) * f t)
      (ContinuousLinearMap.adjoint X + X) 0 := by
    have h := hg.mul hf
    simp only [Pi.mul_def] at h
    rw [hf0, ContinuousLinearMap.adjoint_one, mul_one, one_mul] at h
    exact h
  have hmid : HasDerivAt (fun t => Q * (ContinuousLinearMap.adjoint (f t) * f t) * Q)
      (Q * (ContinuousLinearMap.adjoint X + X) * Q) 0 :=
    (hprod.const_mul Q).mul_const Q
  have hfun : (fun t => rangeProjectionGram Q (f t))
      = fun t => Q * (ContinuousLinearMap.adjoint (f t) * f t) * Q + (1 - Q) := by
    funext t
    rw [rangeProjectionGram]
    noncomm_ring
  rw [hfun]
  exact hmid.add_const (1 - Q)

/-- **The projection derivative at the base point.**  `P'_0 = (1 - Q) X Q + Q X* (1 - Q)`. -/
theorem hasDerivAt_rangeProjection {f : ℝ → (H →L[ℂ] H)} {X : H →L[ℂ] H}
    (hQ2 : IsIdempotentElem Q) (hf : HasDerivAt f X 0) (hf0 : f 0 = 1) :
    HasDerivAt (fun t => rangeProjection Q (f t))
      ((1 - Q) * X * Q + Q * (ContinuousLinearMap.adjoint X) * (1 - Q)) 0 := by
  have hQQ : Q * Q = Q := hQ2
  have hg : HasDerivAt (fun s => ContinuousLinearMap.adjoint (f s))
      (ContinuousLinearMap.adjoint X) 0 := hasDerivAt_adjoint hf
  have hA := hasDerivAt_rangeProjectionGram (Q := Q) hf hf0
  have hA0 : rangeProjectionGram Q (f 0) = 1 := by
    rw [hf0]; exact rangeProjectionGram_one hQ2
  have hv1 : f 0 * Q = Q := by rw [hf0, one_mul]
  have hv2 : Ring.inverse (rangeProjectionGram Q (f 0)) = 1 := by rw [hA0, Ring.inverse_one]
  have hv3 : Q * ContinuousLinearMap.adjoint (f 0) = Q := by
    rw [hf0, ContinuousLinearMap.adjoint_one, mul_one]
  have hinv : HasDerivAt (fun t => Ring.inverse (rangeProjectionGram Q (f t)))
      (-(Q * (ContinuousLinearMap.adjoint X + X) * Q)) 0 := by
    have hunit : rangeProjectionGram Q (f 0) = ((1 : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) := by
      rw [hA0]; rfl
    have hd := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (H →L[ℂ] H)ˣ)
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq 0 hd hA hunit.symm
    simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply] using hcomp
  have hfQ : HasDerivAt (fun t => f t * Q) (X * Q) 0 := hf.mul_const Q
  have hQg : HasDerivAt (fun t => Q * ContinuousLinearMap.adjoint (f t))
      (Q * ContinuousLinearMap.adjoint X) 0 := hg.const_mul Q
  have hstep1 : HasDerivAt
      (fun t => (f t * Q) * Ring.inverse (rangeProjectionGram Q (f t)))
      (X * Q - Q * (ContinuousLinearMap.adjoint X + X) * Q) 0 := by
    have h := hfQ.mul hinv
    simp only [Pi.mul_def] at h
    rw [hv1, hv2, mul_one] at h
    have hfix : Q * -(Q * (ContinuousLinearMap.adjoint X + X) * Q)
        = -(Q * (ContinuousLinearMap.adjoint X + X) * Q) := by
      rw [mul_neg, ← mul_assoc, ← mul_assoc, hQQ]
    rw [hfix] at h
    rw [sub_eq_add_neg]
    exact h
  have hstep2 : HasDerivAt
      (fun t => ((f t * Q) * Ring.inverse (rangeProjectionGram Q (f t))) *
        (Q * ContinuousLinearMap.adjoint (f t)))
      ((1 - Q) * X * Q + Q * (ContinuousLinearMap.adjoint X) * (1 - Q)) 0 := by
    have h := hstep1.mul hQg
    simp only [Pi.mul_def] at h
    rw [hv1, hv2, mul_one, hv3] at h
    have halg : (X * Q - Q * (ContinuousLinearMap.adjoint X + X) * Q) * Q +
        Q * (Q * ContinuousLinearMap.adjoint X)
        = (1 - Q) * X * Q + Q * (ContinuousLinearMap.adjoint X) * (1 - Q) := by
      have e1 : (X * Q - Q * (ContinuousLinearMap.adjoint X + X) * Q) * Q
          = X * (Q * Q) - Q * (ContinuousLinearMap.adjoint X + X) * (Q * Q) := by noncomm_ring
      rw [e1, hQQ, ← mul_assoc Q Q, hQQ]
      noncomm_ring
    rw [halg] at h
    exact h
  have hfun : (fun t => rangeProjection Q (f t))
      = fun t => ((f t * Q) * Ring.inverse (rangeProjectionGram Q (f t))) *
        (Q * ContinuousLinearMap.adjoint (f t)) := by
    funext t
    rw [rangeProjection]
    noncomm_ring
  rw [hfun]
  exact hstep2

end

end HTGeometry
