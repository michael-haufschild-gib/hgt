import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse

/-!
# Friedrichs operators from dense form embeddings

Let `V` be a complete form domain and let `J : V → H` be its continuous, injective, dense
embedding into the ambient Hilbert space.  The bounded covariance `C = J J†` is positive,
injective, self-adjoint, and has dense range.  Its closed graph inverse is therefore the positive
self-adjoint operator associated with the form inner product on `V`.

This is the first-representation/Friedrichs construction needed by Suzuki's restricted-Weil
operator.  It is implemented as a literal `LinearPMap`, not as an operator-valued premise.  If the
form embedding is compact, zero is a compact resolvent point.  The final theorem proves that every
core operator satisfying the exact form identity is extended by the constructed operator.
-/

open Module Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Bounded covariance associated with a continuous form-domain embedding. -/
def formEmbeddingCovariance (J : V →L[ℂ] H) : H →L[ℂ] H :=
  J.comp J.adjoint

/-- Positive operator associated with a form-domain embedding, constructed as the closed graph
inverse of its bounded covariance. -/
def friedrichsFormOperator (J : V →L[ℂ] H) : H →ₗ.[ℂ] H :=
  closedDenseInverse (formEmbeddingCovariance J)

theorem formEmbeddingCovariance_isSelfAdjoint (J : V →L[ℂ] H) :
    IsSelfAdjoint (formEmbeddingCovariance J) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [formEmbeddingCovariance, ContinuousLinearMap.adjoint_comp]

theorem formEmbeddingCovariance_injective (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    Function.Injective (formEmbeddingCovariance J) := by
  have hJadj : Function.Injective J.adjoint :=
    continuousLinearMap_adjoint_injective_of_dense_range J hDense
  intro x y hxy
  apply hJadj
  apply hJinj
  exact hxy

theorem formEmbeddingCovariance_dense_range (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    Dense ((formEmbeddingCovariance J).range : Set H) := by
  let C := formEmbeddingCovariance J
  have hCself : IsSelfAdjoint C := formEmbeddingCovariance_isSelfAdjoint J
  have hCinj : Function.Injective C := formEmbeddingCovariance_injective J hJinj hDense
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  rw [C.orthogonal_range, hCself.adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr hCinj

theorem friedrichsFormOperator_isClosed (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    (friedrichsFormOperator J).IsClosed :=
  closedDenseInverse_isClosed _ (formEmbeddingCovariance_injective J hJinj hDense)

theorem friedrichsFormOperator_dense_domain (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    Dense ((friedrichsFormOperator J).domain : Set H) :=
  closedDenseInverse_dense_domain _ (formEmbeddingCovariance_dense_range J hJinj hDense)

theorem friedrichsFormOperator_isSelfAdjoint (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) :
    IsSelfAdjoint (friedrichsFormOperator J) :=
  closedDenseInverse_isSelfAdjoint _
    (formEmbeddingCovariance_injective J hJinj hDense)
    (formEmbeddingCovariance_dense_range J hJinj hDense)
    (formEmbeddingCovariance_isSelfAdjoint J)

theorem friedrichsFormOperator_apply_covariance (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) (y : H) :
    formEmbeddingCovariance J y ∈ (friedrichsFormOperator J).domain ∧
      friedrichsFormOperator J
        ⟨formEmbeddingCovariance J y, by
          rw [friedrichsFormOperator, closedDenseInverse_domain]
          exact ⟨y, rfl⟩⟩ = y := by
  exact closedDenseInverse_apply_C _ (formEmbeddingCovariance_injective J hJinj hDense) y

/-- First representation identity: the graph inverse represents the form inner product. -/
theorem friedrichsFormOperator_represents_form (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H)) (y : H) (v : V) :
    inner ℂ (J.adjoint y) v =
      inner ℂ
        (friedrichsFormOperator J
          ⟨formEmbeddingCovariance J y,
            (friedrichsFormOperator_apply_covariance J hJinj hDense y).1⟩)
        (J v) := by
  rw [(friedrichsFormOperator_apply_covariance J hJinj hDense y).2]
  exact J.adjoint_inner_left v y

/-- The associated form operator is nonnegative on its literal graph domain. -/
theorem friedrichsFormOperator_re_inner_nonneg (J : V →L[ℂ] H)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (x : (friedrichsFormOperator J).domain) :
    0 ≤ (inner ℂ (friedrichsFormOperator J x) (x : H)).re := by
  have hxRange : (x : H) ∈ (formEmbeddingCovariance J).range := by
    simpa [friedrichsFormOperator, closedDenseInverse_domain] using x.property
  rcases hxRange with ⟨y, hy⟩
  have hAx : friedrichsFormOperator J x = y := by
    have happ := (friedrichsFormOperator_apply_covariance J hJinj hDense y).2
    have heq : x =
        ⟨formEmbeddingCovariance J y,
          (friedrichsFormOperator_apply_covariance J hJinj hDense y).1⟩ :=
      Subtype.ext hy.symm
    exact (congrArg (friedrichsFormOperator J) heq).trans happ
  rw [hAx]
  rw [show (x : H) = formEmbeddingCovariance J y from hy.symm]
  change 0 ≤ (inner ℂ y (J (J.adjoint y))).re
  rw [← J.adjoint_inner_left]
  rw [inner_self_eq_norm_sq_to_K]
  have hsq : 0 ≤ ‖J.adjoint y‖ ^ (2 : ℕ) := sq_nonneg _
  exact_mod_cast hsq

theorem formEmbeddingCovariance_isCompact (J : V →L[ℂ] H)
    (hJ : IsCompactOperator J) :
    IsCompactOperator (formEmbeddingCovariance J) := by
  change IsCompactOperator (fun x => J (J.adjoint x))
  exact hJ.comp_clm J.adjoint

theorem friedrichsFormOperator_hasCompactResolventAt_zero
    (J : V →L[ℂ] H) (hJinj : Function.Injective J)
    (hDense : Dense (J.range : Set H)) (hJ : IsCompactOperator J) :
    LinearPMap.HasCompactResolventAt (friedrichsFormOperator J) 0 :=
  closedDenseInverse_hasCompactResolventAt_zero _
    (formEmbeddingCovariance_injective J hJinj hDense)
    (formEmbeddingCovariance_isCompact J hJ)

/-- Exact Friedrichs extension theorem.  A core operator whose graph embeds into `V` and whose
pairing is the `V` inner product is extended by the associated self-adjoint form operator. -/
theorem friedrichsFormOperator_extends_core
    (J : V →L[ℂ] H) (hJinj : Function.Injective J)
    (hDense : Dense (J.range : Set H))
    (B : H →ₗ.[ℂ] H) (coreLift : B.domain →L[ℂ] V)
    (hsection : ∀ x : B.domain, J (coreLift x) = (x : H))
    (hform : ∀ (x : B.domain) (v : V),
      inner ℂ (coreLift x) v = inner ℂ (B x) (J v)) :
    B ≤ friedrichsFormOperator J := by
  refine ⟨?_, ?_⟩
  · intro x hx
    let xd : B.domain := ⟨x, hx⟩
    have hadj : J.adjoint (B xd) = coreLift xd := by
      apply ext_inner_right ℂ
      intro v
      rw [J.adjoint_inner_left]
      exact (hform xd v).symm
    rw [friedrichsFormOperator, closedDenseInverse_domain]
    refine ⟨B xd, ?_⟩
    change J (J.adjoint (B xd)) = x
    rw [hadj, hsection]
  · intro x y hxy
    let xd : B.domain := x
    have hadj : J.adjoint (B xd) = coreLift xd := by
      apply ext_inner_right ℂ
      intro v
      rw [J.adjoint_inner_left]
      exact (hform xd v).symm
    have hcov : formEmbeddingCovariance J (B xd) = (x : H) := by
      change J (J.adjoint (B xd)) = (x : H)
      rw [hadj, hsection]
    have happ := (friedrichsFormOperator_apply_covariance J hJinj hDense (B xd)).2
    have heq : y =
        ⟨formEmbeddingCovariance J (B xd),
          (friedrichsFormOperator_apply_covariance J hJinj hDense (B xd)).1⟩ :=
      Subtype.ext (hxy.symm.trans hcov.symm)
    exact ((congrArg (friedrichsFormOperator J) heq).trans happ).symm

end

end GaloisForLFunctions.HTGeometry
