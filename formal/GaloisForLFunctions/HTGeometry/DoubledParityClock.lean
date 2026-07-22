import GaloisForLFunctions.HTGeometry.FiniteInvolutiveClockQuantumFisherDephasing
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Doubled parity clocks

A self-adjoint involution on a Hilbert space induces a swap clock on its Hilbert direct square.
An observable with opposite signs in the two sectors is odd under this clock whenever it commutes
with the original involution.  The resulting clock commutator is the anticommutator block of the
original observable and involution.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private def doubledPair (f g : WithLp 2 (E × E) →L[𝕜] E) :
    WithLp 2 (E × E) →L[𝕜] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E E).symm.toContinuousLinearMap.comp
    (f.prod g)

@[simp] private theorem doubledPair_fst (f g : WithLp 2 (E × E) →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (doubledPair f g x).fst = f x := rfl

@[simp] private theorem doubledPair_snd (f g : WithLp 2 (E × E) →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (doubledPair f g x).snd = g x := rfl

/-- The swap clock `(x,y) ↦ (Jy,Jx)` on the Hilbert direct square. -/
def doubledParityClock (J : E →L[𝕜] E) :
    WithLp 2 (E × E) →L[𝕜] WithLp 2 (E × E) :=
  doubledPair (J.comp (WithLp.sndL 2 𝕜 E E))
    (J.comp (WithLp.fstL 2 𝕜 E E))

@[simp] theorem doubledParityClock_fst (J : E →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (doubledParityClock J x).fst = J x.snd := rfl

@[simp] theorem doubledParityClock_snd (J : E →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (doubledParityClock J x).snd = J x.fst := rfl

/-- The sector-odd block observable `(x,y) ↦ (Ax,-Ay)`. -/
def doubledOddObservable (A : E →L[𝕜] E) :
    WithLp 2 (E × E) →L[𝕜] WithLp 2 (E × E) :=
  doubledPair (A.comp (WithLp.fstL 2 𝕜 E E))
    ((-A).comp (WithLp.sndL 2 𝕜 E E))

@[simp] theorem doubledOddObservable_fst (A : E →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (doubledOddObservable A x).fst = A x.fst := rfl

@[simp] theorem doubledOddObservable_snd (A : E →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (doubledOddObservable A x).snd = -A x.snd := rfl

omit [NormedAddCommGroup E] in
private theorem withLp_ext {x y : WithLp 2 (E × E)}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  apply (WithLp.equiv 2 (E × E)).injective
  exact Prod.ext hfst hsnd

/-- An involutive parity gives an involutive doubled swap clock. -/
theorem doubledParityClock_sq (J : E →L[𝕜] E) (hJ : J ^ 2 = 1) :
    doubledParityClock J ^ 2 = 1 := by
  ext x
  apply withLp_ext
  · change J (J x.fst) = x.fst
    rw [← ContinuousLinearMap.mul_apply, ← pow_two, hJ,
      ContinuousLinearMap.one_apply]
  · change J (J x.snd) = x.snd
    rw [← ContinuousLinearMap.mul_apply, ← pow_two, hJ,
      ContinuousLinearMap.one_apply]

/-- A self-adjoint parity gives a self-adjoint doubled clock. -/
theorem doubledParityClock_isSelfAdjoint (J : E →L[𝕜] E)
    [CompleteSpace E] (hJ : IsSelfAdjoint J) :
    IsSelfAdjoint (doubledParityClock J) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  change inner 𝕜 (J x.snd) y.fst + inner 𝕜 (J x.fst) y.snd =
    inner 𝕜 x.fst (J y.snd) + inner 𝕜 x.snd (J y.fst)
  have h1 : inner 𝕜 (J x.snd) y.fst = inner 𝕜 x.snd (J y.fst) :=
    hJ.isSymmetric x.snd y.fst
  have h2 : inner 𝕜 (J x.fst) y.snd = inner 𝕜 x.fst (J y.snd) :=
    hJ.isSymmetric x.fst y.snd
  rw [h1, h2]
  ring

/-- A self-adjoint observable gives a self-adjoint sector-odd doubled observable. -/
theorem doubledOddObservable_isSelfAdjoint (A : E →L[𝕜] E)
    [CompleteSpace E] (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (doubledOddObservable A) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  change inner 𝕜 (A x.fst) y.fst + inner 𝕜 (-A x.snd) y.snd =
    inner 𝕜 x.fst (A y.fst) + inner 𝕜 x.snd (-A y.snd)
  rw [inner_neg_left, inner_neg_right]
  have h1 : inner 𝕜 (A x.fst) y.fst = inner 𝕜 x.fst (A y.fst) :=
    hA.isSymmetric x.fst y.fst
  have h2 : inner 𝕜 (A x.snd) y.snd = inner 𝕜 x.snd (A y.snd) :=
    hA.isSymmetric x.snd y.snd
  rw [h1, h2]

/-- The doubled clock obtained from a self-adjoint involution is unitary. -/
theorem doubledParityClock_adjoint_mul (J : E →L[𝕜] E)
    [CompleteSpace E] (hJself : IsSelfAdjoint J) (hJsq : J ^ 2 = 1) :
    (doubledParityClock J).adjoint * doubledParityClock J = 1 := by
  rw [← ContinuousLinearMap.star_eq_adjoint,
    (doubledParityClock_isSelfAdjoint J hJself).star_eq,
    ← pow_two, doubledParityClock_sq J hJsq]

/-- The unnormalized parity-paired vector `(psi,J psi)`. -/
def doubledParityPair (J : E →L[𝕜] E) (ψ : E) : WithLp 2 (E × E) :=
  WithLp.toLp 2 (ψ, J ψ)

@[simp] theorem doubledParityPair_fst (J : E →L[𝕜] E) (ψ : E) :
    (doubledParityPair J ψ).fst = ψ := rfl

@[simp] theorem doubledParityPair_snd (J : E →L[𝕜] E) (ψ : E) :
    (doubledParityPair J ψ).snd = J ψ := rfl

/-- The parity-paired vector is fixed by the doubled clock. -/
theorem doubledParityClock_fixed_pair (J : E →L[𝕜] E)
    (hJsq : J ^ 2 = 1) (ψ : E) :
    doubledParityClock J (doubledParityPair J ψ) = doubledParityPair J ψ := by
  apply withLp_ext
  · change J (J ψ) = ψ
    rw [← ContinuousLinearMap.mul_apply, ← pow_two, hJsq,
      ContinuousLinearMap.one_apply]
  · rfl

/-- If `J` and `A` commute, the doubled observable applied to the paired vector lies in the
clock-odd sector. -/
theorem doubledParityClock_odd_pair (J A : E →L[𝕜] E)
    (hJsq : J ^ 2 = 1) (hcomm : J * A = A * J) (ψ : E) :
    doubledParityClock J (doubledOddObservable A (doubledParityPair J ψ)) =
      -doubledOddObservable A (doubledParityPair J ψ) := by
  apply withLp_ext
  · change J (-A (J ψ)) = -(A ψ)
    rw [map_neg, ← ContinuousLinearMap.mul_apply, hcomm,
      ContinuousLinearMap.mul_apply]
    have hJJ : J (J ψ) = ψ := by
      have h := congrArg (fun T : E →L[𝕜] E => T ψ) hJsq
      simpa only [pow_two, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.one_apply] using h
    rw [hJJ]
  · change J (A ψ) = -(-A (J ψ))
    rw [neg_neg]
    rw [← ContinuousLinearMap.mul_apply, hcomm,
      ContinuousLinearMap.mul_apply]

/-- The clock commutator is twice the odd observable on the paired state. -/
theorem doubledParityClock_commutator_pair (J A : E →L[𝕜] E)
    (hJsq : J ^ 2 = 1) (hcomm : J * A = A * J) (ψ : E) :
    ((doubledOddObservable A * doubledParityClock J -
      doubledParityClock J * doubledOddObservable A) :
        WithLp 2 (E × E) →L[𝕜] WithLp 2 (E × E))
        (doubledParityPair J ψ) =
      (2 : 𝕜) • doubledOddObservable A (doubledParityPair J ψ) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, doubledParityClock_fixed_pair J hJsq,
    doubledParityClock_odd_pair J A hJsq hcomm]
  module

/-- The unit-normalized doubled parity pair. -/
def doubledParitySource (J : E →L[𝕜] E) (ψ : E) : WithLp 2 (E × E) :=
  (((Real.sqrt 2 : ℝ) : 𝕜)⁻¹) • doubledParityPair J ψ

/-- Squared norm of the normalized doubled source. -/
theorem norm_doubledParitySource_sq (J : E →L[𝕜] E) (ψ : E)
    (hJnorm : ‖J ψ‖ = ‖ψ‖) :
    ‖doubledParitySource J ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [doubledParitySource, norm_smul, mul_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  simp only [doubledParityPair_fst, doubledParityPair_snd, hJnorm]
  rw [norm_inv, RCLike.norm_ofReal,
    abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

/-- A normalized source and an isometric parity give a normalized doubled source. -/
theorem norm_doubledParitySource (J : E →L[𝕜] E) (ψ : E)
    (hJnorm : ‖J ψ‖ = ‖ψ‖) (hψnorm : ‖ψ‖ = 1) :
    ‖doubledParitySource J ψ‖ = 1 := by
  have hsquare := norm_doubledParitySource_sq J ψ hJnorm
  rw [hψnorm, one_pow] at hsquare
  nlinarith [norm_nonneg (doubledParitySource J ψ)]

/-- The normalized doubled source is fixed by its clock. -/
theorem doubledParityClock_fixed_source (J : E →L[𝕜] E)
    (hJsq : J ^ 2 = 1) (ψ : E) :
    doubledParityClock J (doubledParitySource J ψ) =
      doubledParitySource J ψ := by
  rw [doubledParitySource, map_smul, doubledParityClock_fixed_pair J hJsq]

/-- The odd observable applied to the normalized source lies in the clock-odd sector. -/
theorem doubledParityClock_odd_source (J A : E →L[𝕜] E)
    (hJsq : J ^ 2 = 1) (hcomm : J * A = A * J) (ψ : E) :
    doubledParityClock J
        (doubledOddObservable A (doubledParitySource J ψ)) =
      -doubledOddObservable A (doubledParitySource J ψ) := by
  rw [doubledParitySource, map_smul, map_smul,
    doubledParityClock_odd_pair J A hJsq hcomm, smul_neg]

/-- The doubled clock commutator is twice the odd observable on the normalized source. -/
theorem doubledParityClock_commutator_source (J A : E →L[𝕜] E)
    (hJsq : J ^ 2 = 1) (hcomm : J * A = A * J) (ψ : E) :
    ((doubledOddObservable A * doubledParityClock J -
      doubledParityClock J * doubledOddObservable A) :
        WithLp 2 (E × E) →L[𝕜] WithLp 2 (E × E))
        (doubledParitySource J ψ) =
      (2 : 𝕜) • doubledOddObservable A (doubledParitySource J ψ) := by
  rw [doubledParitySource, map_smul, map_smul,
    doubledParityClock_commutator_pair J A hJsq hcomm,
    smul_smul, smul_smul, mul_comm]

/-- The upper block of the doubled clock commutator is the anticommutator `AJ + JA`. -/
theorem doubledOddObservable_commutator_fst (J A : E →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (((doubledOddObservable A * doubledParityClock J -
      doubledParityClock J * doubledOddObservable A) :
        WithLp 2 (E × E) →L[𝕜] WithLp 2 (E × E)) x).fst =
      ((A * J + J * A) : E →L[𝕜] E) x.snd := by
  change A (J x.snd) - J (-A x.snd) =
    A (J x.snd) + J (A x.snd)
  rw [map_neg]
  module

/-- The lower block of the doubled clock commutator is minus the anticommutator `AJ + JA`. -/
theorem doubledOddObservable_commutator_snd (J A : E →L[𝕜] E)
    (x : WithLp 2 (E × E)) :
    (((doubledOddObservable A * doubledParityClock J -
      doubledParityClock J * doubledOddObservable A) :
        WithLp 2 (E × E) →L[𝕜] WithLp 2 (E × E)) x).snd =
      -((A * J + J * A) : E →L[𝕜] E) x.fst := by
  change -A (J x.fst) - J (A x.fst) =
    -(A (J x.fst) + J (A x.fst))
  module

/-- Under commutation and parity isometry, the doubled odd-observable energy equals the original
observable energy. -/
theorem norm_doubledOddObservable_source_sq (J A : E →L[𝕜] E)
    (hJnorm : ∀ x, ‖J x‖ = ‖x‖) (hcomm : J * A = A * J) (ψ : E) :
    ‖doubledOddObservable A (doubledParitySource J ψ)‖ ^ 2 =
      ‖A ψ‖ ^ 2 := by
  have hAJ : A (J ψ) = J (A ψ) := by
    have h := congrArg (fun T : E →L[𝕜] E => T ψ) hcomm.symm
    simpa only [ContinuousLinearMap.mul_apply] using h
  rw [doubledParitySource, map_smul, norm_smul, mul_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  simp only [doubledOddObservable_fst, doubledOddObservable_snd, norm_neg,
    doubledParityPair_fst, doubledParityPair_snd, hAJ, hJnorm]
  rw [norm_inv, RCLike.norm_ofReal,
    abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

/-- The QFI erased by the doubled parity clock is exactly four times the odd-observable energy;
no self-adjointness of the observable is required. -/
theorem doubledParityClock_erasedQFI_eq_four_mul_oddNormSq
    [CompleteSpace E] (J A : E →L[𝕜] E)
    (hJself : IsSelfAdjoint J) (hJsq : J ^ 2 = 1)
    (hJnorm : ∀ x, ‖J x‖ = ‖x‖)
    (hcomm : J * A = A * J) {ψ : E} (hψnorm : ‖ψ‖ = 1) :
    pureStateQuantumFisherValue (‖doubledParitySource J ψ‖ ^ 2)
        (‖inner 𝕜 (doubledParitySource J ψ)
          ((1 - finiteCyclicGaugeAverage (doubledParityClock J) 2)
            (doubledOddObservable A (doubledParitySource J ψ)))‖)
        (‖(1 - finiteCyclicGaugeAverage (doubledParityClock J) 2)
          (doubledOddObservable A (doubledParitySource J ψ))‖ ^ 2) =
      4 * ‖doubledOddObservable A (doubledParitySource J ψ)‖ ^ 2 := by
  rw [finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq
    (doubledParityClock J) (doubledOddObservable A)
    (doubledParityClock_adjoint_mul J hJself hJsq)
    (doubledParityClock_sq J hJsq)
    (norm_doubledParitySource J ψ (hJnorm ψ) hψnorm)
    (doubledParityClock_fixed_source J hJsq ψ),
    doubledParityClock_commutator_source J A hJsq hcomm]
  rw [norm_smul]
  have htwo : ‖(2 : 𝕜)‖ = 2 := by norm_num
  rw [htwo]
  ring

end

end HTGeometry
