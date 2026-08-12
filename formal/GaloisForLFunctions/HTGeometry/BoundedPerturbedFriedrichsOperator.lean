import GaloisForLFunctions.HTGeometry.FriedrichsFormOperator
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Friedrichs realization of a boundedly perturbed compact form embedding

Let `J : V → H` be a compact, injective, dense form embedding and let `B` be a bounded
self-adjoint operator on `H`.  The signed form

`q(u,v) = ⟪u,v⟫ + ⟪B (J u), J v⟫`

is closed and lower bounded.  This file constructs its representing operator without assuming a
closed-form theorem or Kato--Rellich.  We first add the explicit scalar
`c = ‖B‖ + 1`.  On `V`, the shifted form is represented by the coercive bounded operator

`R = 1 + J† B J + c J† J`.

The covariance `C = J R⁻¹ J†` is compact, injective, self-adjoint, and has dense range.  Its graph
inverse represents `q + c⟪J·,J·⟫`; subtracting `c` on the same graph domain therefore represents
the original signed form.  The subtraction is a bounded self-adjoint perturbation, and `-c` is an
explicit compact-resolvent point of the resulting operator.
-/

open Module Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A bounded self-adjoint shift of a densely defined self-adjoint operator is self-adjoint. -/
theorem boundedShift_isSelfAdjoint
    (T : H →ₗ.[ℂ] H) (B : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (boundedShift T B) := by
  let S := boundedShift T B
  have hTdense : Dense (T.domain : Set H) := hT.dense_domain
  have hSdense : Dense (S.domain : Set H) := by
    simpa only [S, boundedShift_domain] using hTdense
  have hBsymm : ∀ x y : H, inner ℂ (B x) y = inner ℂ x (B y) := by
    intro x y
    rw [← B.adjoint_inner_right, hB.adjoint_eq]
  have hTadj : T.adjoint = T := hT
  have hTformal : T.IsFormalAdjoint T := by
    have hle : T ≤ T.adjoint := le_of_eq hTadj.symm
    intro x y
    let xAdj : T.adjoint.domain := ⟨(x : H), hle.1 x.property⟩
    have hxApply : T x = T.adjoint xAdj := hle.2 rfl
    rw [hxApply]
    exact LinearPMap.adjoint_isFormalAdjoint hTdense xAdj y
  have hSformal : S.IsFormalAdjoint S := by
    intro x y
    change inner ℂ (T x + B (x : H)) (y : H) =
      inner ℂ (x : H) (T y + B (y : H))
    rw [inner_add_left, inner_add_right, hBsymm]
    exact congrArg₂ (· + ·) (hTformal x y) rfl
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      let yAdj : S.adjoint.domain := ⟨y, hy⟩
      let w : H := S.adjoint yAdj
      have hyTadj : y ∈ T.adjoint.domain := by
        apply LinearPMap.mem_adjoint_domain_of_exists
        refine ⟨w - B y, ?_⟩
        intro x
        let xS : S.domain := ⟨(x : H), by simpa only [S, boundedShift_domain] using x.property⟩
        have hAdj := LinearPMap.adjoint_isFormalAdjoint hSdense yAdj xS
        change inner ℂ (w - B y) (x : H) = inner ℂ y (T x)
        rw [inner_sub_left, hBsymm]
        change inner ℂ w (x : H) - inner ℂ y (B (x : H)) = inner ℂ y (T x)
        rw [show inner ℂ w (x : H) = inner ℂ y (S xS) by simpa only [w] using hAdj]
        change inner ℂ y (T x + B (x : H)) - inner ℂ y (B (x : H)) = inner ℂ y (T x)
        rw [inner_add_right, add_sub_cancel_right]
      have hyT : y ∈ T.domain := by
        simpa only [hTadj] using hyTadj
      simpa only [S, boundedShift_domain] using hyT
    · intro y z hyz
      let yAdj : S.adjoint.domain := y
      let w : H := S.adjoint yAdj
      have hyTadj : (y : H) ∈ T.adjoint.domain := by
        apply LinearPMap.mem_adjoint_domain_of_exists
        refine ⟨w - B (y : H), ?_⟩
        intro x
        let xS : S.domain := ⟨(x : H), by simpa only [S, boundedShift_domain] using x.property⟩
        have hAdj := LinearPMap.adjoint_isFormalAdjoint hSdense yAdj xS
        change inner ℂ (w - B (y : H)) (x : H) = inner ℂ (y : H) (T x)
        rw [inner_sub_left, hBsymm]
        change inner ℂ w (x : H) - inner ℂ (y : H) (B (x : H)) =
          inner ℂ (y : H) (T x)
        rw [show inner ℂ w (x : H) = inner ℂ (y : H) (S xS) by
          simpa only [w] using hAdj]
        change inner ℂ (y : H) (T x + B (x : H)) -
          inner ℂ (y : H) (B (x : H)) = inner ℂ (y : H) (T x)
        rw [inner_add_right, add_sub_cancel_right]
      have hyT : (y : H) ∈ T.domain := by simpa only [hTadj] using hyTadj
      let yT : T.domain := ⟨(y : H), hyT⟩
      have hAdjApply : S.adjoint yAdj = T yT + B (y : H) := by
        apply LinearPMap.adjoint_apply_eq hSdense
        intro x
        let xT : T.domain := ⟨(x : H), by
          simpa only [S, boundedShift_domain] using x.property⟩
        change inner ℂ (T yT + B (y : H)) (x : H) = inner ℂ (y : H) (S x)
        rw [inner_add_left, hBsymm]
        change inner ℂ (T yT) (xT : H) + inner ℂ (y : H) (B (x : H)) =
          inner ℂ (y : H) (T xT + B (x : H))
        rw [hTformal yT xT, inner_add_right]
      rw [hAdjApply]
      change T yT + B (y : H) =
        T ⟨(z : H), by simpa only [S, boundedShift_domain] using z.property⟩ + B (z : H)
      have hzy : (z : H) = (y : H) := hyz.symm
      have hzT :
          (⟨(z : H), by simpa only [S, boundedShift_domain] using z.property⟩ : T.domain) =
            yT := Subtype.ext hzy
      rw [hzT, hzy]
  · exact hSformal.le_adjoint hSdense

/-- Scalar used to make the boundedly perturbed form strictly coercive. -/
def boundedPerturbedFormShift (B : H →L[ℂ] H) : ℝ :=
  ‖B‖ + 1

theorem boundedPerturbedFormShift_pos (B : H →L[ℂ] H) :
    0 < boundedPerturbedFormShift B := by
  unfold boundedPerturbedFormShift
  positivity

/-- Riesz operator of the explicitly shifted form on the original form domain. -/
def boundedPerturbedFormRiesz (J : V →L[ℂ] H) (B : H →L[ℂ] H) : V →L[ℂ] V :=
  1 + J.adjoint ∘L B ∘L J +
    ((boundedPerturbedFormShift B : ℂ) • (J.adjoint ∘L J))

theorem boundedPerturbedFormRiesz_apply (J : V →L[ℂ] H) (B : H →L[ℂ] H)
    (u : V) :
    boundedPerturbedFormRiesz J B u =
      u + J.adjoint (B (J u)) +
        (boundedPerturbedFormShift B : ℂ) • J.adjoint (J u) := by
  rfl

theorem boundedPerturbedFormRiesz_isSelfAdjoint
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (boundedPerturbedFormRiesz J B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  have hBpair : inner ℂ (B (J u)) (J v) = inner ℂ (J u) (B (J v)) := by
    rw [← B.adjoint_inner_right, hB.adjoint_eq]
  change inner ℂ (boundedPerturbedFormRiesz J B u) v =
    inner ℂ u (boundedPerturbedFormRiesz J B v)
  rw [boundedPerturbedFormRiesz_apply, boundedPerturbedFormRiesz_apply,
    inner_add_left, inner_add_left, inner_add_right, inner_add_right,
    inner_smul_left, inner_smul_right,
    J.adjoint_inner_left, J.adjoint_inner_right,
    J.adjoint_inner_left, J.adjoint_inner_right]
  rw [hBpair]
  simp [boundedPerturbedFormShift]

/-- Exact coercivity: the shifted form controls the original form-domain norm with constant one. -/
theorem boundedPerturbedFormRiesz_coercive
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (u : V) :
    ‖u‖ ^ 2 ≤ (inner ℂ (boundedPerturbedFormRiesz J B u) u).re := by
  have hBnorm :
      |(inner ℂ (B (J u)) (J u)).re| ≤ ‖B‖ * ‖J u‖ ^ 2 := by
    calc
      |(inner ℂ (B (J u)) (J u)).re| ≤ ‖inner ℂ (B (J u)) (J u)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖B (J u)‖ * ‖J u‖ := norm_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖J u‖) * ‖J u‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm (J u)) (norm_nonneg _)
      _ = ‖B‖ * ‖J u‖ ^ 2 := by ring
  have hBbelow :
      -(‖B‖ * ‖J u‖ ^ 2) ≤ (inner ℂ (B (J u)) (J u)).re :=
    (neg_le_neg hBnorm).trans (neg_abs_le _)
  have hexpand :
      (inner ℂ (boundedPerturbedFormRiesz J B u) u).re =
        ‖u‖ ^ 2 + (inner ℂ (B (J u)) (J u)).re +
          boundedPerturbedFormShift B * ‖J u‖ ^ 2 := by
    rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
      inner_smul_left, inner_self_eq_norm_sq_to_K,
      J.adjoint_inner_left, J.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K]
    simp [boundedPerturbedFormShift]
    norm_cast
  rw [hexpand]
  have hJu : 0 ≤ ‖J u‖ ^ 2 := sq_nonneg _
  have hBu : 0 ≤ ‖B‖ := norm_nonneg _
  unfold boundedPerturbedFormShift
  nlinarith

theorem boundedPerturbedFormRiesz_norm_lower
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (u : V) :
    ‖u‖ ≤ ‖boundedPerturbedFormRiesz J B u‖ := by
  by_cases hu : u = 0
  · simp [hu]
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hcoer := boundedPerturbedFormRiesz_coercive J B u
  have hre : (inner ℂ (boundedPerturbedFormRiesz J B u) u).re ≤
      ‖boundedPerturbedFormRiesz J B u‖ * ‖u‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hmul : ‖u‖ * ‖u‖ ≤ ‖boundedPerturbedFormRiesz J B u‖ * ‖u‖ := by
    nlinarith [hcoer, hre]
  exact le_of_mul_le_mul_right hmul hpos

theorem boundedPerturbedFormRiesz_injective
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) :
    Function.Injective (boundedPerturbedFormRiesz J B) := by
  intro u v huv
  have hzero : boundedPerturbedFormRiesz J B (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hnorm := boundedPerturbedFormRiesz_norm_lower J B (u - v)
  rw [hzero, norm_zero] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

theorem boundedPerturbedFormRiesz_isClosed_range
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) :
    IsClosed ((boundedPerturbedFormRiesz J B).range : Set V) := by
  have hanti : AntilipschitzWith 1 (boundedPerturbedFormRiesz J B) :=
    ContinuousLinearMap.antilipschitz_of_bound _
      (by simpa using fun u => boundedPerturbedFormRiesz_norm_lower J B u)
  exact hanti.isClosed_range (boundedPerturbedFormRiesz J B).uniformContinuous

theorem boundedPerturbedFormRiesz_dense_range
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    Dense ((boundedPerturbedFormRiesz J B).range : Set V) := by
  let R := boundedPerturbedFormRiesz J B
  have hRself : IsSelfAdjoint R := boundedPerturbedFormRiesz_isSelfAdjoint J B hB
  have hRinj : Function.Injective R := boundedPerturbedFormRiesz_injective J B
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  rw [R.orthogonal_range, hRself.adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr hRinj

theorem boundedPerturbedFormRiesz_surjective
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    Function.Surjective (boundedPerturbedFormRiesz J B) := by
  have hclosed := boundedPerturbedFormRiesz_isClosed_range J B
  have hdense := boundedPerturbedFormRiesz_dense_range J B hB
  intro y
  have hyClosure : y ∈ closure
      ((boundedPerturbedFormRiesz J B).range : Set V) := hdense y
  have hyRange : y ∈ (boundedPerturbedFormRiesz J B).range := by
    rwa [hclosed.closure_eq] at hyClosure
  exact hyRange

/-- Continuous inverse of the shifted form Riesz operator. -/
def boundedPerturbedFormRieszEquiv
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) : V ≃L[ℂ] V :=
  ContinuousLinearEquiv.ofBijective (boundedPerturbedFormRiesz J B)
    (LinearMap.ker_eq_bot.mpr (boundedPerturbedFormRiesz_injective J B))
    (LinearMap.range_eq_top.mpr (boundedPerturbedFormRiesz_surjective J B hB))

/-- Inverse shifted-form Riesz operator. -/
def boundedPerturbedFormRieszInv
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) : V →L[ℂ] V :=
  (boundedPerturbedFormRieszEquiv J B hB).symm.toContinuousLinearMap

theorem boundedPerturbedFormRieszInv_isSelfAdjoint
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (boundedPerturbedFormRieszInv J B hB) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  let u := boundedPerturbedFormRieszInv J B hB x
  let v := boundedPerturbedFormRieszInv J B hB y
  have hx : boundedPerturbedFormRiesz J B u = x :=
    (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply x
  have hy : boundedPerturbedFormRiesz J B v = y :=
    (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply y
  have hRself := boundedPerturbedFormRiesz_isSelfAdjoint J B hB
  change inner ℂ u y = inner ℂ x v
  rw [← hx, ← hy]
  exact hRself.isSymmetric u v |>.symm

/-- Compact covariance of the shifted perturbed form. -/
def boundedPerturbedFormCovariance
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) : H →L[ℂ] H :=
  J ∘L boundedPerturbedFormRieszInv J B hB ∘L J.adjoint

theorem boundedPerturbedFormCovariance_isSelfAdjoint
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (boundedPerturbedFormCovariance J B hB) := by
  exact (boundedPerturbedFormRieszInv_isSelfAdjoint J B hB).conj_adjoint J

theorem boundedPerturbedFormCovariance_injective
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    Function.Injective (boundedPerturbedFormCovariance J B hB) := by
  have hJadj : Function.Injective J.adjoint :=
    continuousLinearMap_adjoint_injective_of_dense_range J hDense
  intro x y hxy
  apply hJadj
  apply (boundedPerturbedFormRieszEquiv J B hB).symm.injective
  apply hJinj
  exact hxy

theorem boundedPerturbedFormCovariance_dense_range
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    Dense ((boundedPerturbedFormCovariance J B hB).range : Set H) := by
  let C := boundedPerturbedFormCovariance J B hB
  have hCself : IsSelfAdjoint C := boundedPerturbedFormCovariance_isSelfAdjoint J B hB
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B hB hJinj hDense
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  rw [C.orthogonal_range, hCself.adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr hCinj

theorem boundedPerturbedFormCovariance_isCompact
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJcompact : IsCompactOperator J) :
    IsCompactOperator (boundedPerturbedFormCovariance J B hB) := by
  exact hJcompact.comp_clm
    (boundedPerturbedFormRieszInv J B hB ∘L J.adjoint)

/-- Self-adjoint operator representing the original, unshifted perturbed form. -/
def boundedPerturbedFriedrichsOperator
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) : H →ₗ.[ℂ] H :=
  boundedShift
    (closedDenseInverse (boundedPerturbedFormCovariance J B hB))
    (-((boundedPerturbedFormShift B : ℂ) • ContinuousLinearMap.id ℂ H))

@[simp] theorem boundedPerturbedFriedrichsOperator_domain
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    (boundedPerturbedFriedrichsOperator J B hB).domain =
      (closedDenseInverse (boundedPerturbedFormCovariance J B hB)).domain := rfl

theorem boundedPerturbedFriedrichsOperator_apply
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (x : (boundedPerturbedFriedrichsOperator J B hB).domain) :
    boundedPerturbedFriedrichsOperator J B hB x =
      closedDenseInverse (boundedPerturbedFormCovariance J B hB)
        ⟨(x : H), by
          simpa only [boundedPerturbedFriedrichsOperator_domain] using x.property⟩ -
      (boundedPerturbedFormShift B : ℂ) • (x : H) := by
  change boundedShift
      (closedDenseInverse (boundedPerturbedFormCovariance J B hB))
      (-((boundedPerturbedFormShift B : ℂ) • ContinuousLinearMap.id ℂ H)) x = _
  rw [boundedShift_apply]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [sub_eq_add_neg]
  congr 2

theorem boundedPerturbedFriedrichsOperator_isSelfAdjoint
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    IsSelfAdjoint (boundedPerturbedFriedrichsOperator J B hB) := by
  apply boundedShift_isSelfAdjoint
  · exact closedDenseInverse_isSelfAdjoint _
      (boundedPerturbedFormCovariance_injective J B hB hJinj hDense)
      (boundedPerturbedFormCovariance_dense_range J B hB hJinj hDense)
      (boundedPerturbedFormCovariance_isSelfAdjoint J B hB)
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℂ (-((boundedPerturbedFormShift B : ℂ) • x)) y =
      inner ℂ x (-((boundedPerturbedFormShift B : ℂ) • y))
    rw [inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right]
    simp [boundedPerturbedFormShift]

theorem boundedPerturbedFriedrichsOperator_hasCompactResolventAt_negShift
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (hJcompact : IsCompactOperator J) :
    LinearPMap.HasCompactResolventAt
      (boundedPerturbedFriedrichsOperator J B hB)
      (-(boundedPerturbedFormShift B : ℂ)) := by
  let C := boundedPerturbedFormCovariance J B hB
  let A := closedDenseInverse C
  refine ⟨C, boundedPerturbedFormCovariance_isCompact J B hB hJcompact, ?_, ?_⟩
  · refine ⟨fun x => (closedDenseInverse_apply_C C
        (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) x).1, ?_⟩
    intro x
    rw [boundedPerturbedFriedrichsOperator_apply]
    change A ⟨C x, _⟩ - (boundedPerturbedFormShift B : ℂ) • C x -
      (-(boundedPerturbedFormShift B : ℂ)) • C x = x
    rw [(closedDenseInverse_apply_C C
      (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) x).2]
    module
  · intro x
    rw [boundedPerturbedFriedrichsOperator_apply]
    change C (A ⟨(x : H), _⟩ - (boundedPerturbedFormShift B : ℂ) • (x : H) -
      (-(boundedPerturbedFormShift B : ℂ)) • (x : H)) = (x : H)
    have hxAdom : (x : H) ∈ A.domain := by
      simpa only [A, boundedPerturbedFriedrichsOperator_domain] using x.property
    let xA : A.domain := ⟨(x : H), hxAdom⟩
    have hxRange : (x : H) ∈ C.range := by
      simpa only [A, closedDenseInverse_domain] using hxAdom
    rcases hxRange with ⟨y, hy⟩
    have hAy : A xA = y := by
      have happ := (closedDenseInverse_apply_C C
        (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) y).2
      have heq : xA = ⟨C y, (closedDenseInverse_apply_C C
        (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) y).1⟩ :=
          Subtype.ext hy.symm
      exact (congrArg A heq).trans happ
    change C (A xA - (boundedPerturbedFormShift B : ℂ) • (x : H) -
      (-(boundedPerturbedFormShift B : ℂ)) • (x : H)) = (x : H)
    rw [hAy]
    have hcancel : y - (boundedPerturbedFormShift B : ℂ) • (x : H) -
        (-(boundedPerturbedFormShift B : ℂ)) • (x : H) = y := by module
    rw [hcancel]
    exact hy

/-- Exact first-representation identity for the unshifted signed form. -/
theorem boundedPerturbedFriedrichsOperator_represents_form
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (y : H) (v : V) :
    let C := boundedPerturbedFormCovariance J B hB
    let x : (boundedPerturbedFriedrichsOperator J B hB).domain :=
      ⟨C y, by
        change C y ∈ (closedDenseInverse C).domain
        exact (closedDenseInverse_apply_C C
          (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) y).1⟩
    let u := boundedPerturbedFormRieszInv J B hB (J.adjoint y)
    (x : H) = J u ∧
      inner ℂ (boundedPerturbedFriedrichsOperator J B hB x) (J v) =
        inner ℂ u v + inner ℂ (B (J u)) (J v) := by
  dsimp only
  let C := boundedPerturbedFormCovariance J B hB
  let A := closedDenseInverse C
  let u := boundedPerturbedFormRieszInv J B hB (J.adjoint y)
  have hCu : C y = J u := rfl
  have hAy : A ⟨C y, (closedDenseInverse_apply_C C
      (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) y).1⟩ = y :=
    (closedDenseInverse_apply_C C
      (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) y).2
  have hRu : boundedPerturbedFormRiesz J B u = J.adjoint y :=
    (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply (J.adjoint y)
  refine ⟨hCu, ?_⟩
  rw [boundedPerturbedFriedrichsOperator_apply]
  change inner ℂ (A ⟨C y, _⟩ -
      (boundedPerturbedFormShift B : ℂ) • C y) (J v) = _
  rw [hAy, hCu, inner_sub_left, inner_smul_left]
  have hform : inner ℂ y (J v) =
      inner ℂ u v + inner ℂ (B (J u)) (J v) +
        (boundedPerturbedFormShift B : ℂ) * inner ℂ (J u) (J v) := by
    rw [← J.adjoint_inner_left]
    rw [← hRu]
    rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
      inner_smul_left, J.adjoint_inner_left, J.adjoint_inner_left]
    simp [boundedPerturbedFormShift]
  rw [hform]
  change _ = inner ℂ u v + inner ℂ (B (J u)) (J v)
  simp [boundedPerturbedFormShift]

end

end GaloisForLFunctions.HTGeometry
