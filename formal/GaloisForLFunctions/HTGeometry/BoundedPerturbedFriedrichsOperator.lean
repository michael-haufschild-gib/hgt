import GaloisForLFunctions.HTGeometry.FriedrichsFormOperator
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import Mathlib.Analysis.InnerProductSpace.StarOrder

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

/-- The inverse shifted-form Riesz operator is positive. -/
theorem boundedPerturbedFormRieszInv_isPositive
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    ContinuousLinearMap.IsPositive (boundedPerturbedFormRieszInv J B hB) := by
  refine ⟨(boundedPerturbedFormRieszInv_isSelfAdjoint J B hB).isSymmetric, ?_⟩
  intro x
  let u := boundedPerturbedFormRieszInv J B hB x
  have hx : boundedPerturbedFormRiesz J B u = x :=
    (boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply x
  have hsymm := (boundedPerturbedFormRiesz_isSelfAdjoint J B hB).isSymmetric u u
  change 0 ≤ (inner ℂ (boundedPerturbedFormRieszInv J B hB x) x).re
  change 0 ≤ (inner ℂ u x).re
  rw [← hx]
  calc
    0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    _ ≤ (inner ℂ (boundedPerturbedFormRiesz J B u) u).re :=
      boundedPerturbedFormRiesz_coercive J B u
    _ = (inner ℂ u (boundedPerturbedFormRiesz J B u)).re :=
      congrArg Complex.re hsymm

/-- Compact covariance of the shifted perturbed form. -/
def boundedPerturbedFormCovariance
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) : H →L[ℂ] H :=
  J ∘L boundedPerturbedFormRieszInv J B hB ∘L J.adjoint

theorem boundedPerturbedFormCovariance_isSelfAdjoint
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (boundedPerturbedFormCovariance J B hB) := by
  exact (boundedPerturbedFormRieszInv_isSelfAdjoint J B hB).conj_adjoint J

/-- The shifted covariance is positive. -/
theorem boundedPerturbedFormCovariance_isPositive
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    ContinuousLinearMap.IsPositive (boundedPerturbedFormCovariance J B hB) := by
  exact (boundedPerturbedFormRieszInv_isPositive J B hB).conj_adjoint J

/-- A positive operator squared is bounded by its norm times itself. -/
theorem positiveOperator_sq_le_norm_smul
    (C : H →L[ℂ] H) (hC : ContinuousLinearMap.IsPositive C) :
    C * C ≤ ((‖C‖ : ℂ) • C) := by
  have hnonneg : 0 ≤ C := (ContinuousLinearMap.nonneg_iff_isPositive C).2 hC
  have hle := (IsSelfAdjoint.of_nonneg hnonneg).le_algebraMap_norm_self
  have hconj := star_left_conjugate_le_conjugate hle (CFC.sqrt C)
  have hsnonneg : 0 ≤ CFC.sqrt C := CFC.sqrt_nonneg C
  have hsstar : star (CFC.sqrt C) = CFC.sqrt C :=
    (IsSelfAdjoint.of_nonneg hsnonneg).star_eq
  have hsquare : CFC.sqrt C * CFC.sqrt C = C :=
    CFC.sqrt_mul_sqrt_self C
  rw [hsstar] at hconj
  calc
    C * C = (CFC.sqrt C * CFC.sqrt C) *
        (CFC.sqrt C * CFC.sqrt C) := congrArg₂ (· * ·) hsquare.symm hsquare.symm
    _ = CFC.sqrt C * (CFC.sqrt C * CFC.sqrt C) * CFC.sqrt C := by
      simp only [mul_assoc]
    _ = CFC.sqrt C * C * CFC.sqrt C :=
      congrArg (fun T => CFC.sqrt C * T * CFC.sqrt C) hsquare
    _ ≤ CFC.sqrt C * algebraMap ℝ (H →L[ℂ] H) ‖C‖ * CFC.sqrt C := hconj
    _ = ((‖C‖ : ℂ) • C) := by
      rw [Algebra.algebraMap_eq_smul_one]
      calc
        CFC.sqrt C * (‖C‖ • (1 : H →L[ℂ] H)) * CFC.sqrt C =
            (‖C‖ : ℂ) • (CFC.sqrt C * CFC.sqrt C) := by
          ext x
          simp
        _ = (‖C‖ : ℂ) • C := by rw [hsquare]

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

/-- The graph inverse is a left inverse on its full graph domain. -/
theorem closedDenseInverse_C_apply
    (C : H →L[ℂ] H) (hC : Function.Injective C)
    (x : (closedDenseInverse C).domain) :
    C (closedDenseInverse C x) = (x : H) := by
  have hxRange : (x : H) ∈ C.range := by
    simpa only [closedDenseInverse_domain] using x.property
  rcases hxRange with ⟨y, hy⟩
  have happ := (closedDenseInverse_apply_C C hC y).2
  let Cy : (closedDenseInverse C).domain :=
    ⟨C y, (closedDenseInverse_apply_C C hC y).1⟩
  have heq : x = Cy := Subtype.ext hy.symm
  have happly : closedDenseInverse C x = y := by
    rw [heq]
    exact happ
  rw [happly]
  exact hy

/-- Rayleigh lower bound for the graph inverse of a positive injective covariance. -/
theorem closedDenseInverse_re_inner_lower
    [Nontrivial H] (C : H →L[ℂ] H)
    (hCinj : Function.Injective C) (hCpos : ContinuousLinearMap.IsPositive C)
    (x : (closedDenseInverse C).domain) :
    ‖C‖⁻¹ * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ (closedDenseInverse C x) (x : H)).re := by
  have hCne : C ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := exists_ne (0 : H)
    apply hz
    apply hCinj
    simp [hzero]
  have hmu : 0 < ‖C‖ := (norm_pos_iff (E := H →L[ℂ] H)).mpr hCne
  let y : H := closedDenseInverse C x
  have hCy : C y = (x : H) := closedDenseInverse_C_apply C hCinj x
  have horder : C * C ≤ ((‖C‖ : ℂ) • C) :=
    positiveOperator_sq_le_norm_smul C hCpos
  have hdiff : ContinuousLinearMap.IsPositive (((‖C‖ : ℂ) • C) - C * C) :=
    (ContinuousLinearMap.le_def _ _).mp horder
  have hnonneg := hdiff.re_inner_nonneg_left y
  have hCsymm := hCpos.inner_left_eq_inner_right
  have hineq : ‖(x : H)‖ ^ 2 ≤
      ‖C‖ * (inner ℂ y (x : H)).re := by
    change 0 ≤ (inner ℂ
      ((‖C‖ : ℂ) • C y - C (C y)) y).re at hnonneg
    rw [inner_sub_left, Complex.sub_re, inner_smul_left] at hnonneg
    have hfirst : (inner ℂ (C y) y).re = (inner ℂ y (C y)).re := by
      exact congrArg Complex.re (hCsymm y y)
    have hsecond : (inner ℂ (C (C y)) y).re = ‖C y‖ ^ 2 := by
      rw [hCsymm (C y) y, inner_self_eq_norm_sq_to_K]
      norm_cast
    have hscalar :
        ((starRingEnd ℂ) (‖C‖ : ℂ) * inner ℂ (C y) y).re =
          ‖C‖ * (inner ℂ (C y) y).re := by
      norm_num [Complex.mul_re]
    rw [hscalar, hfirst, hsecond, hCy] at hnonneg
    linarith
  exact (inv_mul_le_iff₀ hmu).2 hineq

/-- A compact positive injective covariance has a nonzero eigenvector at its operator norm. -/
theorem boundedPerturbedFormCovariance_exists_norm_eigenvector
    [Nontrivial H]
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (hJcompact : IsCompactOperator J) :
    ∃ x : H, x ≠ 0 ∧
      boundedPerturbedFormCovariance J B hB x =
        ((‖boundedPerturbedFormCovariance J B hB‖ : ℝ) : ℂ) • x := by
  let C := boundedPerturbedFormCovariance J B hB
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B hB hJinj hDense
  have hCne : C ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    apply hx
    apply hCinj
    simp [hzero]
  have hnorm : ‖C‖ ≠ 0 := norm_ne_zero_iff.mpr hCne
  have hpositive : ContinuousLinearMap.IsPositive C :=
    boundedPerturbedFormCovariance_isPositive J B hB
  have hnonneg : 0 ≤ C := (ContinuousLinearMap.nonneg_iff_isPositive C).2 hpositive
  have hspecReal : ‖C‖ ∈ spectrum ℝ C :=
    CStarAlgebra.norm_mem_spectrum_of_nonneg hnonneg
  have hspecComplex : ((‖C‖ : ℝ) : ℂ) ∈ spectrum ℂ C :=
    spectrum.algebraMap_mem ℂ hspecReal
  have hmu : ((‖C‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hnorm
  have heigen : Module.End.HasEigenvalue (C : Module.End ℂ H) ((‖C‖ : ℝ) : ℂ) :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum
      (boundedPerturbedFormCovariance_isCompact J B hB hJcompact) hmu).2 hspecComplex
  obtain ⟨x, hxmem, hxne⟩ := heigen.exists_hasEigenvector
  exact ⟨x, hxne, Module.End.mem_eigenspace_iff.mp hxmem⟩

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

/-- The covariance-norm value is a quadratic-form lower bound on the full operator domain. -/
theorem boundedPerturbedFriedrichsOperator_ground_mul_norm_sq_le
    [Nontrivial H]
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (x : (boundedPerturbedFriedrichsOperator J B hB).domain) :
    (‖boundedPerturbedFormCovariance J B hB‖⁻¹ -
          boundedPerturbedFormShift B) * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ (boundedPerturbedFriedrichsOperator J B hB x) (x : H)).re := by
  let x0 : (closedDenseInverse
      (boundedPerturbedFormCovariance J B hB)).domain :=
    ⟨(x : H), by
      simpa only [boundedPerturbedFriedrichsOperator_domain] using x.property⟩
  have hCinj : Function.Injective (boundedPerturbedFormCovariance J B hB) :=
    boundedPerturbedFormCovariance_injective J B hB hJinj hDense
  have hCpos : ContinuousLinearMap.IsPositive
      (boundedPerturbedFormCovariance J B hB) :=
    boundedPerturbedFormCovariance_isPositive J B hB
  have hlower := closedDenseInverse_re_inner_lower
    (boundedPerturbedFormCovariance J B hB) hCinj hCpos x0
  rw [boundedPerturbedFriedrichsOperator_apply]
  change
    (‖boundedPerturbedFormCovariance J B hB‖⁻¹ -
          boundedPerturbedFormShift B) * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ
        (closedDenseInverse (boundedPerturbedFormCovariance J B hB) x0 -
          (boundedPerturbedFormShift B : ℂ) • (x : H))
        (x : H)).re
  rw [inner_sub_left, Complex.sub_re, inner_smul_left]
  have hscalar :
      ((starRingEnd ℂ) (boundedPerturbedFormShift B : ℂ) *
          inner ℂ (x : H) (x : H)).re =
        boundedPerturbedFormShift B * ‖(x : H)‖ ^ 2 := by
    calc
      _ = ((starRingEnd ℂ) (boundedPerturbedFormShift B : ℂ) *
          (‖(x : H)‖ : ℂ) ^ 2).re := by
            rw [inner_self_eq_norm_sq_to_K]
            rfl
      _ = boundedPerturbedFormShift B * ‖(x : H)‖ ^ 2 := by
        exact (by
          intro s r
          have hsre : ((starRingEnd ℂ) (s : ℂ)).re = s := by norm_num
          have hsim : ((starRingEnd ℂ) (s : ℂ)).im = 0 := by norm_num
          have hpre : ((r : ℂ) ^ 2).re = r ^ 2 := by
            rw [pow_two, Complex.mul_re]
            norm_num
            ring
          have hpim : ((r : ℂ) ^ 2).im = 0 := by
            rw [pow_two, Complex.mul_im]
            norm_num
          rw [Complex.mul_re, hsre, hsim, hpre, hpim]
          ring : ∀ s r : ℝ,
            (((starRingEnd ℂ) (s : ℂ)) * (r : ℂ) ^ 2).re = s * r ^ 2)
          (boundedPerturbedFormShift B) ‖(x : H)‖
  rw [hscalar]
  change ‖boundedPerturbedFormCovariance J B hB‖⁻¹ * ‖(x : H)‖ ^ 2 ≤ _ at hlower
  nlinarith

/-- The covariance-norm eigenvalue is below every real eigenvalue of the represented operator. -/
theorem boundedPerturbedFriedrichsOperator_ground_le_eigenvalue
    [Nontrivial H]
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    {lam : ℝ} (x : (boundedPerturbedFriedrichsOperator J B hB).domain)
    (hxne : (x : H) ≠ 0)
    (hx : boundedPerturbedFriedrichsOperator J B hB x = (lam : ℂ) • (x : H)) :
    ‖boundedPerturbedFormCovariance J B hB‖⁻¹ - boundedPerturbedFormShift B ≤ lam := by
  let C := boundedPerturbedFormCovariance J B hB
  let A0 := closedDenseInverse C
  let r : ℝ := lam + boundedPerturbedFormShift B
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B hB hJinj hDense
  have hCne : C ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := exists_ne (0 : H)
    apply hz
    apply hCinj
    simp [hzero]
  have hmu : 0 < ‖C‖ :=
    (norm_pos_iff (E := H →L[ℂ] H)).mpr hCne
  let x0 : A0.domain := ⟨(x : H), by
    simpa only [A0, boundedPerturbedFriedrichsOperator_domain] using x.property⟩
  have hA0 : A0 x0 = (r : ℂ) • (x : H) := by
    have hxapply := boundedPerturbedFriedrichsOperator_apply J B hB x
    rw [hx] at hxapply
    change (lam : ℂ) • (x : H) = A0 x0 -
      (boundedPerturbedFormShift B : ℂ) • (x : H) at hxapply
    change A0 x0 = ((lam + boundedPerturbedFormShift B : ℝ) : ℂ) • (x : H)
    push_cast
    rw [add_smul, hxapply]
    exact (sub_add_cancel _ _).symm
  have hCA0 : C (A0 x0) = (x : H) :=
    closedDenseInverse_C_apply C hCinj x0
  have hrCx : (r : ℂ) • C (x : H) = (x : H) := by
    rw [← map_smul, ← hA0]
    exact hCA0
  have hrne : (r : ℂ) ≠ 0 := by
    intro hrzero
    rw [hrzero, zero_smul] at hrCx
    exact hxne hrCx.symm
  have hCx : C (x : H) = ((r : ℂ)⁻¹) • (x : H) := by
    calc
      C (x : H) = (1 : ℂ) • C (x : H) := (one_smul ℂ _).symm
      _ = ((r : ℂ)⁻¹ * (r : ℂ)) • C (x : H) := by rw [inv_mul_cancel₀ hrne]
      _ = ((r : ℂ)⁻¹) • ((r : ℂ) • C (x : H)) := by rw [smul_smul]
      _ = ((r : ℂ)⁻¹) • (x : H) := by rw [hrCx]
  have hrneReal : r ≠ 0 := by exact_mod_cast hrne
  have hCpos := boundedPerturbedFormCovariance_isPositive J B hB
  have hquad : 0 ≤ (r⁻¹) * ‖(x : H)‖ ^ 2 := by
    have h := hCpos.re_inner_nonneg_left (x : H)
    rw [hCx, inner_smul_left, inner_self_eq_norm_sq_to_K] at h
    norm_num [Complex.mul_re, pow_two] at h
    simpa [pow_two] using h
  have hxnorm : 0 < ‖(x : H)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hxne)
  have hrInvPos : 0 < r⁻¹ := by
    have hrInvNe : r⁻¹ ≠ 0 := inv_ne_zero hrneReal
    by_contra hnot
    have hle : r⁻¹ ≤ 0 := le_of_not_gt hnot
    have hlt : r⁻¹ < 0 := lt_of_le_of_ne hle hrInvNe
    exact (not_lt_of_ge hquad) (mul_neg_of_neg_of_pos hlt hxnorm)
  have hrpos : 0 < r := inv_pos.mp hrInvPos
  have hop := C.le_opNorm (x : H)
  rw [hCx, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos hrpos] at hop
  have hInvLe : r⁻¹ ≤ ‖C‖ := by
    exact le_of_mul_le_mul_right hop (norm_pos_iff.mpr hxne)
  have hfloor : ‖C‖⁻¹ ≤ r := by
    simpa using (inv_le_inv₀ hmu hrInvPos).2 hInvLe
  change ‖C‖⁻¹ - boundedPerturbedFormShift B ≤ lam
  dsimp only [r] at hfloor
  linarith

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

/-- Exact Friedrichs-extension theorem for a boundedly perturbed form.  A core operator whose
vectors lift continuously to the form domain and whose graph realizes the unshifted signed form
is extended by the represented self-adjoint operator. -/
theorem boundedPerturbedFriedrichsOperator_extends_core
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (T : H →ₗ.[ℂ] H) (coreLift : T.domain →ₗ[ℂ] V)
    (hsection : ∀ x : T.domain, J (coreLift x) = (x : H))
    (hform : ∀ (x : T.domain) (v : V),
      inner ℂ (coreLift x) v + inner ℂ (B (x : H)) (J v) =
        inner ℂ (T x) (J v)) :
    T ≤ boundedPerturbedFriedrichsOperator J B hB := by
  let R := boundedPerturbedFormRiesz J B
  let Rinv := boundedPerturbedFormRieszInv J B hB
  let C := boundedPerturbedFormCovariance J B hB
  let A0 := closedDenseInverse C
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B hB hJinj hDense
  have hRinvR : ∀ u : V, Rinv (R u) = u := fun u =>
    (boundedPerturbedFormRieszEquiv J B hB).symm_apply_apply u
  have hR : ∀ x : T.domain,
      R (coreLift x) =
        J.adjoint (T x + (boundedPerturbedFormShift B : ℂ) • (x : H)) := by
    intro x
    apply ext_inner_right ℂ
    intro v
    rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
      inner_smul_left, J.adjoint_inner_left, J.adjoint_inner_left,
      J.adjoint_inner_left, hsection]
    rw [inner_add_left, inner_smul_left]
    rw [← hform x v]
  have hC : ∀ x : T.domain,
      C (T x + (boundedPerturbedFormShift B : ℂ) • (x : H)) = (x : H) := by
    intro x
    change J (Rinv (J.adjoint
      (T x + (boundedPerturbedFormShift B : ℂ) • (x : H)))) = (x : H)
    rw [← hR x, hRinvR, hsection]
  refine ⟨?_, ?_⟩
  · intro x hx
    let xd : T.domain := ⟨x, hx⟩
    change x ∈ A0.domain
    rw [closedDenseInverse_domain]
    exact ⟨T xd + (boundedPerturbedFormShift B : ℂ) • x, hC xd⟩
  · intro x y hxy
    let xd : T.domain := x
    have hxA0 : (x : H) ∈ A0.domain := by
      rw [closedDenseInverse_domain]
      exact ⟨T xd + (boundedPerturbedFormShift B : ℂ) • (x : H), hC xd⟩
    have hA0 : A0 ⟨(x : H), hxA0⟩ =
        T xd + (boundedPerturbedFormShift B : ℂ) • (x : H) := by
      let z := T xd + (boundedPerturbedFormShift B : ℂ) • (x : H)
      have happ := (closedDenseInverse_apply_C C hCinj z).2
      have heq : (⟨(x : H), hxA0⟩ : A0.domain) =
          ⟨C z, (closedDenseInverse_apply_C C hCinj z).1⟩ :=
        Subtype.ext (hC xd).symm
      exact (congrArg A0 heq).trans happ
    have hyEq : (y : H) = (x : H) := hxy.symm
    rw [boundedPerturbedFriedrichsOperator_apply]
    change T xd = A0 ⟨(y : H), _⟩ -
      (boundedPerturbedFormShift B : ℂ) • (y : H)
    have heqDom : (⟨(y : H), by
          simpa only [A0, boundedPerturbedFriedrichsOperator_domain] using y.property⟩ : A0.domain) =
        ⟨(x : H), hxA0⟩ := Subtype.ext hyEq
    rw [heqDom, hA0, hyEq]
    module

/-- A form vector whose sesquilinear functional has an `H`-representative belongs to the
represented operator domain, and the represented operator takes exactly that value. -/
theorem boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (u : V) (y : H)
    (hform : ∀ v : V,
      inner ℂ u v + inner ℂ (B (J u)) (J v) = inner ℂ y (J v)) :
    ∃ hmem : J u ∈ (boundedPerturbedFriedrichsOperator J B hB).domain,
      boundedPerturbedFriedrichsOperator J B hB ⟨J u, hmem⟩ = y := by
  let R := boundedPerturbedFormRiesz J B
  let Rinv := boundedPerturbedFormRieszInv J B hB
  let C := boundedPerturbedFormCovariance J B hB
  let A0 := closedDenseInverse C
  let z : H := y + (boundedPerturbedFormShift B : ℂ) • J u
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B hB hJinj hDense
  have hRinvR : Rinv (R u) = u :=
    (boundedPerturbedFormRieszEquiv J B hB).symm_apply_apply u
  have hR : R u = J.adjoint z := by
    apply ext_inner_right ℂ
    intro v
    rw [boundedPerturbedFormRiesz_apply, inner_add_left, inner_add_left,
      inner_smul_left, J.adjoint_inner_left, J.adjoint_inner_left,
      J.adjoint_inner_left]
    rw [hform v, inner_add_left, inner_smul_left]
  have hC : C z = J u := by
    change J (Rinv (J.adjoint z)) = J u
    rw [← hR, hRinvR]
  have hmem0 : J u ∈ A0.domain := by
    rw [closedDenseInverse_domain]
    exact ⟨z, hC⟩
  have hA0 : A0 ⟨J u, hmem0⟩ = z := by
    have happ := (closedDenseInverse_apply_C C hCinj z).2
    have heq : (⟨J u, hmem0⟩ : A0.domain) =
        ⟨C z, (closedDenseInverse_apply_C C hCinj z).1⟩ :=
      Subtype.ext hC.symm
    exact (congrArg A0 heq).trans happ
  have hmem : J u ∈ (boundedPerturbedFriedrichsOperator J B hB).domain := by
    simpa only [A0, boundedPerturbedFriedrichsOperator_domain] using hmem0
  refine ⟨hmem, ?_⟩
  rw [boundedPerturbedFriedrichsOperator_apply]
  change A0 ⟨J u, _⟩ - (boundedPerturbedFormShift B : ℂ) • J u = y
  have heqDom : (⟨J u, by
      simpa only [A0, boundedPerturbedFriedrichsOperator_domain] using hmem⟩ : A0.domain) =
      ⟨J u, hmem0⟩ := rfl
  rw [heqDom, hA0]
  dsimp only [z]
  module


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

/-- Injectivity of an embedding makes the adjoint range dense. -/
theorem continuousLinearMap_adjoint_dense_range_of_injective
    (J : V →L[ℂ] H) (hJinj : Function.Injective J) :
    DenseRange J.adjoint := by
  change Dense ((J.adjoint.range : Submodule ℂ V) : Set V)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  rw [J.adjoint.orthogonal_range, ContinuousLinearMap.adjoint_adjoint]
  exact LinearMap.ker_eq_bot.mpr hJinj

/-- The form vectors represented by the graph domain form a dense core. -/
theorem boundedPerturbedRepresentationCore_denseRange
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) :
    DenseRange
      (boundedPerturbedFormRieszInv J B hB ∘L J.adjoint) := by
  have hAdj : DenseRange J.adjoint :=
    continuousLinearMap_adjoint_dense_range_of_injective J hJinj
  have hInv : DenseRange (boundedPerturbedFormRieszInv J B hB) :=
    (boundedPerturbedFormRieszEquiv J B hB).symm.surjective.denseRange
  exact hInv.comp hAdj (boundedPerturbedFormRieszInv J B hB).continuous

/-- The covariance-norm value is the lower Rayleigh floor on the entire closed form domain. -/
theorem boundedPerturbedForm_ground_mul_norm_sq_le
    [Nontrivial H]
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (u : V) :
    (‖boundedPerturbedFormCovariance J B hB‖⁻¹ -
          boundedPerturbedFormShift B) * ‖J u‖ ^ 2 ≤
      (inner ℂ u u + inner ℂ (B (J u)) (J u)).re := by
  let L : H →L[ℂ] V := boundedPerturbedFormRieszInv J B hB ∘L J.adjoint
  let P : V → Prop := fun v =>
    (‖boundedPerturbedFormCovariance J B hB‖⁻¹ -
          boundedPerturbedFormShift B) * ‖J v‖ ^ 2 ≤
      (inner ℂ v v + inner ℂ (B (J v)) (J v)).re
  apply DenseRange.induction_on (p := P)
    (boundedPerturbedRepresentationCore_denseRange J B hB hJinj) u
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro y
    let C := boundedPerturbedFormCovariance J B hB
    let x : (boundedPerturbedFriedrichsOperator J B hB).domain :=
      ⟨C y, by
        change C y ∈ (closedDenseInverse C).domain
        exact (closedDenseInverse_apply_C C
          (boundedPerturbedFormCovariance_injective J B hB hJinj hDense) y).1⟩
    let v := boundedPerturbedFormRieszInv J B hB (J.adjoint y)
    have hrep := boundedPerturbedFriedrichsOperator_represents_form
      J B hB hJinj hDense y v
    dsimp only at hrep
    have hxv : (x : H) = J v := hrep.1
    have hform : inner ℂ (boundedPerturbedFriedrichsOperator J B hB x) (J v) =
        inner ℂ v v + inner ℂ (B (J v)) (J v) := hrep.2
    have hlower := boundedPerturbedFriedrichsOperator_ground_mul_norm_sq_le
      J B hB hJinj hDense x
    change P (L y)
    change
      (‖boundedPerturbedFormCovariance J B hB‖⁻¹ -
            boundedPerturbedFormShift B) * ‖J v‖ ^ 2 ≤
        (inner ℂ v v + inner ℂ (B (J v)) (J v)).re
    rw [← hform, ← hxv]
    exact hlower

end

end GaloisForLFunctions.HTGeometry
