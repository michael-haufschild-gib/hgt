/-
# Infinite semimetric symmetrization

For a bounded self-adjoint semimetric `T` on an arbitrary real Hilbert space, a symmetric support
inverse consists of a support projection `P` and a generalized inverse `G`.  No finite-dimensional
or finite-rank condition occurs.

The universal symmetrizer

`S_T(D) = (1/2) • (P D P + G D† T)`

is supported, kills `ker T`, is self-adjoint for the `T`-metric, and is an idempotent retraction
onto all supported `T`-self-adjoint operators.  This is the arbitrary-rank infinite-dimensional
law underlying sparse boundary-channel corrections.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

noncomputable section

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Algebraic support-inverse data for a bounded self-adjoint semimetric.  Closed-range
self-adjoint operators carry this package via their Moore--Penrose inverse and range projection. -/
@[ext]
structure SymmetricSupportInverse (T : E →L[ℝ] E) where
  /-- Generalized inverse on the support. -/
  inverse : E →L[ℝ] E
  /-- Orthogonal support projection. -/
  support : E →L[ℝ] E
  selfAdjoint_metric : IsSelfAdjoint T
  selfAdjoint_inverse : IsSelfAdjoint inverse
  selfAdjoint_support : IsSelfAdjoint support
  support_idempotent : support * support = support
  metric_mul_inverse : T * inverse = support
  inverse_mul_metric : inverse * T = support
  metric_mul_support : T * support = T
  support_mul_metric : support * T = T
  support_mul_inverse : support * inverse = inverse

/-- **Unconditional algebraic support--range equivalence.**  Every bounded operator on an
arbitrary real Hilbert space restricts to a linear equivalence from the orthogonal complement of
its kernel onto its algebraic range.  No closed-range premise occurs; discontinuity of the inverse
is precisely what remains possible. -/
noncomputable def algebraicSupportRangeEquiv (T : E →L[ℝ] E) :
    T.kerᗮ ≃ₗ[ℝ] T.range := by
  let K : Submodule ℝ E := T.ker
  let S : Submodule ℝ E := Kᗮ
  letI : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  letI : K.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace K
  letI : CompleteSpace S := (Submodule.isClosed_orthogonal K).completeSpace_coe
  letI : S.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace S
  let f : S →ₗ[ℝ] T.range :=
    (T.toLinearMap.domRestrict S).codRestrict T.range (fun x => ⟨x, rfl⟩)
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hzker : (x : E) - y ∈ K := by
      change T ((x : E) - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hzS : (x : E) - y ∈ S := S.sub_mem x.property y.property
    have hzbot : (x : E) - y ∈ K ⊓ S := ⟨hzker, hzS⟩
    have : (x : E) - y ∈ (⊥ : Submodule ℝ E) :=
      (K.orthogonal_disjoint.le_bot) hzbot
    exact sub_eq_zero.mp (by simpa using this)
  have hTPapply : ∀ x : E, T (S.starProjection x) = T x := by
    intro x
    have hdiffSorth : x - S.starProjection x ∈ Sᗮ :=
      Submodule.sub_starProjection_mem_orthogonal x
    have hSK : Sᗮ = K := by
      change Kᗮᗮ = K
      exact Submodule.orthogonal_orthogonal K
    have hdiffK : x - S.starProjection x ∈ K := by simpa [hSK] using hdiffSorth
    change T (S.starProjection x) = T x
    have hz : T (x - S.starProjection x) = 0 := hdiffK
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm
  have hfsurj : Function.Surjective f := by
    intro y
    rcases y.property with ⟨x, hx⟩
    let sx : S := S.orthogonalProjection x
    refine ⟨sx, Subtype.ext ?_⟩
    change T (S.starProjection x) = y
    rw [hTPapply]
    exact hx
  exact LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩

/-- The algebraic support--range equivalence is the original operator on the support. -/
theorem algebraicSupportRangeEquiv_apply
    (T : E →L[ℝ] E) (x : T.kerᗮ) :
    ((algebraicSupportRangeEquiv T x : T.range) : E) = T x := by
  rfl

/-- Its inverse is an exact right inverse on the algebraic range, whether or not that range is
closed. -/
theorem algebraicSupportRangeEquiv_symm_rightInverse
    (T : E →L[ℝ] E) (y : T.range) :
    T ((algebraicSupportRangeEquiv T).symm y) = y := by
  have h := (algebraicSupportRangeEquiv T).apply_symm_apply y
  exact congrArg Subtype.val h

/-- Its inverse chooses the unique preimage orthogonal to the kernel. -/
theorem algebraicSupportRangeEquiv_symm_leftInverse
    (T : E →L[ℝ] E) (x : T.kerᗮ) :
    (algebraicSupportRangeEquiv T).symm
        ⟨T x, ⟨x, rfl⟩⟩ = x :=
  (algebraicSupportRangeEquiv T).symm_apply_apply x

/-- Universal infinite-dimensional semimetric symmetrization. -/
def infiniteSemimetricSymmetrization
    (T : E →L[ℝ] E) (data : SymmetricSupportInverse T)
    (D : E →L[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) •
    (data.support * D * data.support + data.inverse * star D * T)

/-- **Universal metric-adjoint law.**  Symmetrization removes an arbitrary bounded clock defect;
the defect can have infinite rank. -/
theorem infiniteSemimetricSymmetrization_metricAdjoint
    (T : E →L[ℝ] E) (data : SymmetricSupportInverse T) (D : E →L[ℝ] E) :
    T * infiniteSemimetricSymmetrization T data D =
      star (infiniteSemimetricSymmetrization T data D) * T := by
  simp only [infiniteSemimetricSymmetrization, mul_smul_comm, star_smul,
    star_add, star_mul, star_star, data.selfAdjoint_metric.star_eq,
    data.selfAdjoint_inverse.star_eq, data.selfAdjoint_support.star_eq,
    star_trivial, smul_mul_assoc]
  congr 1
  have hleft :
      T * (data.support * D * data.support + data.inverse * star D * T) =
        T * D * data.support + data.support * star D * T := by
    calc
      T * (data.support * D * data.support + data.inverse * star D * T) =
          T * data.support * D * data.support +
            T * data.inverse * star D * T := by noncomm_ring
      _ = T * D * data.support + data.support * star D * T := by
        rw [data.metric_mul_support, data.metric_mul_inverse]
  have hright :
      (data.support * (star D * data.support) + T * (D * data.inverse)) * T =
        data.support * star D * T + T * D * data.support := by
    calc
      (data.support * (star D * data.support) + T * (D * data.inverse)) * T =
          data.support * star D * data.support * T +
            T * D * data.inverse * T := by noncomm_ring
      _ = data.support * star D * T + T * D * data.support := by
        rw [mul_assoc (data.support * star D) data.support T,
          data.support_mul_metric, mul_assoc (T * D) data.inverse T,
          data.inverse_mul_metric]
  rw [hleft, hright]
  abel

/-- Symmetrization is supported on both sides. -/
theorem infiniteSemimetricSymmetrization_support
    (T : E →L[ℝ] E) (data : SymmetricSupportInverse T) (D : E →L[ℝ] E) :
    data.support * infiniteSemimetricSymmetrization T data D =
        infiniteSemimetricSymmetrization T data D ∧
      infiniteSemimetricSymmetrization T data D * data.support =
        infiniteSemimetricSymmetrization T data D := by
  constructor
  · rw [infiniteSemimetricSymmetrization]
    simp only [mul_smul_comm]
    congr 1
    calc
      data.support *
          (data.support * D * data.support + data.inverse * star D * T) =
          data.support * data.support * D * data.support +
            data.support * data.inverse * star D * T := by noncomm_ring
      _ = data.support * D * data.support + data.inverse * star D * T := by
        rw [data.support_idempotent, data.support_mul_inverse]
  · rw [infiniteSemimetricSymmetrization]
    simp only [smul_mul_assoc]
    congr 1
    noncomm_ring [data.support_idempotent, data.metric_mul_support]

/-- The universal symmetrizer annihilates the entire radical of `T`. -/
theorem infiniteSemimetricSymmetrization_apply_eq_zero_of_mem_ker
    (T : E →L[ℝ] E) (data : SymmetricSupportInverse T)
    (D : E →L[ℝ] E) (x : E) (hx : T x = 0) :
    infiniteSemimetricSymmetrization T data D x = 0 := by
  have hPx : data.support x = 0 := by
    have h := congrArg (fun A : E →L[ℝ] E => A x) data.inverse_mul_metric
    simpa [ContinuousLinearMap.mul_apply, hx] using h.symm
  have hsupp := (infiniteSemimetricSymmetrization_support T data D).2
  have h := congrArg (fun A : E →L[ℝ] E => A x) hsupp.symm
  simpa [ContinuousLinearMap.mul_apply, hPx] using h

/-- Supported metric-adjoint operators are fixed by the universal symmetrizer. -/
theorem infiniteSemimetricSymmetrization_fixed
    (T : E →L[ℝ] E) (data : SymmetricSupportInverse T) (D : E →L[ℝ] E)
    (hPD : data.support * D = D) (hDP : D * data.support = D)
    (hmetric : T * D = star D * T) :
    infiniteSemimetricSymmetrization T data D = D := by
  rw [infiniteSemimetricSymmetrization]
  rw [hPD, hDP, mul_assoc data.inverse (star D) T, ← hmetric,
    ← mul_assoc, data.inverse_mul_metric, hPD]
  module

/-- **Idempotent retraction law.**  Applying the universal symmetrizer twice changes nothing. -/
theorem infiniteSemimetricSymmetrization_idempotent
    (T : E →L[ℝ] E) (data : SymmetricSupportInverse T) (D : E →L[ℝ] E) :
    infiniteSemimetricSymmetrization T data
        (infiniteSemimetricSymmetrization T data D) =
      infiniteSemimetricSymmetrization T data D := by
  have hsupp := infiniteSemimetricSymmetrization_support T data D
  have hmetric := infiniteSemimetricSymmetrization_metricAdjoint T data D
  exact infiniteSemimetricSymmetrization_fixed T data
    (infiniteSemimetricSymmetrization T data D) hsupp.1 hsupp.2 hmetric

/-- Fixed points of the symmetrizer are exactly the supported metric-adjoint operators. -/
theorem infiniteSemimetricSymmetrization_fixed_iff
    (T : E →L[ℝ] E) (data : SymmetricSupportInverse T) (D : E →L[ℝ] E) :
    infiniteSemimetricSymmetrization T data D = D ↔
      data.support * D = D ∧ D * data.support = D ∧
        T * D = star D * T := by
  constructor
  · intro hfixed
    have hsupp := infiniteSemimetricSymmetrization_support T data D
    have hmetric := infiniteSemimetricSymmetrization_metricAdjoint T data D
    simpa [hfixed] using And.intro hsupp.1 (And.intro hsupp.2 hmetric)
  · rintro ⟨hPD, hDP, hmetric⟩
    exact infiniteSemimetricSymmetrization_fixed T data D hPD hDP hmetric

/-- Every bounded self-adjoint operator with closed range has symmetric support-inverse data.
The construction restricts `T` to the orthogonal complement of its kernel, uses the bounded
inverse theorem there, and extends the inverse by zero across the kernel. -/
theorem exists_symmetricSupportInverse_of_isClosed_range
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hclosed : IsClosed (T.range : Set E)) :
    Nonempty (SymmetricSupportInverse T) := by
  let K : Submodule ℝ E := T.ker
  let S : Submodule ℝ E := Kᗮ
  letI : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  letI : K.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace K
  letI : CompleteSpace S := (Submodule.isClosed_orthogonal K).completeSpace_coe
  letI : S.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace S
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  letI : T.range.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace T.range
  have hrange : T.range = S := by
    calc
      T.range = T.rangeᗮᗮ := (Submodule.orthogonal_orthogonal T.range).symm
      _ = T.kerᗮ := congrArg (fun U : Submodule ℝ E => Uᗮ)
        (ContinuousLinearMap.IsStarNormal.orthogonal_range hT.isStarNormal)
      _ = S := rfl
  have hmaps : ∀ x : S, T x ∈ S := by
    intro x
    exact hrange.le ⟨x, rfl⟩
  let f : S →L[ℝ] S := (T.domRestrict S).codRestrict S hmaps
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hzker : (x : E) - y ∈ K := by
      change T ((x : E) - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hzS : (x : E) - y ∈ S := S.sub_mem x.property y.property
    have hzbot : (x : E) - y ∈ K ⊓ S := ⟨hzker, hzS⟩
    have : (x : E) - y ∈ (⊥ : Submodule ℝ E) := by
      exact (K.orthogonal_disjoint.le_bot) hzbot
    exact sub_eq_zero.mp (by simpa using this)
  have hTPapply : ∀ x : E, T (S.starProjection x) = T x := by
    intro x
    have hdiffSorth : x - S.starProjection x ∈ Sᗮ :=
      Submodule.sub_starProjection_mem_orthogonal x
    have hSK : Sᗮ = K := by
      change Kᗮᗮ = K
      exact Submodule.orthogonal_orthogonal K
    have hdiffK : x - S.starProjection x ∈ K := by simpa [hSK] using hdiffSorth
    change T (S.starProjection x) = T x
    have hz : T (x - S.starProjection x) = 0 := hdiffK
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm
  have hfsurj : Function.Surjective f := by
    intro y
    have hyRange : (y : E) ∈ T.range := hrange.ge y.property
    rcases hyRange with ⟨x, hx⟩
    let sx : S := S.orthogonalProjection x
    refine ⟨sx, Subtype.ext ?_⟩
    change T (S.starProjection x) = y
    rw [hTPapply]
    exact hx
  have hfker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr hfinj
  have hfrange : f.range = ⊤ := LinearMap.range_eq_top.mpr hfsurj
  let e : S ≃L[ℝ] S := ContinuousLinearEquiv.ofBijective f hfker hfrange
  let P : E →L[ℝ] E := S.starProjection
  let G : E →L[ℝ] E :=
    S.subtypeL ∘L e.symm.toContinuousLinearMap ∘L S.orthogonalProjection
  have hPself : IsSelfAdjoint P := by
    dsimp [P]
    exact isSelfAdjoint_starProjection S
  have hP2 : P * P = P := by
    dsimp [P]
    exact S.isIdempotentElem_starProjection
  have hTG : T * G = P := by
    ext x
    change T (e.symm (S.orthogonalProjection x)) = S.starProjection x
    have he := e.apply_symm_apply (S.orthogonalProjection x)
    exact congrArg Subtype.val he
  have hPT : P * T = T := by
    ext x
    change S.starProjection (T x) = T x
    apply Submodule.starProjection_eq_self_iff.mpr
    exact hrange.le ⟨x, rfl⟩
  have hTP : T * P = T := by
    ext x
    exact hTPapply x
  have hPG : P * G = G := by
    ext x
    change S.starProjection ((e.symm (S.orthogonalProjection x) : S) : E) =
      ((e.symm (S.orthogonalProjection x) : S) : E)
    exact Submodule.starProjection_mem_subspace_eq_self _
  have hGself : IsSelfAdjoint G := by
    apply LinearMap.IsSymmetric.isSelfAdjoint
    intro x y
    have hPGx : P (G x) = G x := by
      have h := congrArg (fun A : E →L[ℝ] E => A x) hPG
      simpa [ContinuousLinearMap.mul_apply] using h
    have hPGy : P (G y) = G y := by
      have h := congrArg (fun A : E →L[ℝ] E => A y) hPG
      simpa [ContinuousLinearMap.mul_apply] using h
    have hTGx : T (G x) = P x := by
      have h := congrArg (fun A : E →L[ℝ] E => A x) hTG
      simpa [ContinuousLinearMap.mul_apply] using h
    have hTGy : T (G y) = P y := by
      have h := congrArg (fun A : E →L[ℝ] E => A y) hTG
      simpa [ContinuousLinearMap.mul_apply] using h
    calc
      inner ℝ (G x) y = inner ℝ (P (G x)) y := by rw [hPGx]
      _ = inner ℝ (G x) (P y) := hPself.isSymmetric (G x) y
      _ = inner ℝ (G x) (T (G y)) := by rw [hTGy]
      _ = inner ℝ (T (G x)) (G y) := (hT.isSymmetric (G x) (G y)).symm
      _ = inner ℝ (P x) (G y) := by rw [hTGx]
      _ = inner ℝ x (P (G y)) := hPself.isSymmetric x (G y)
      _ = inner ℝ x (G y) := by rw [hPGy]
  have hGT : G * T = P := by
    have h := congrArg star hTG
    simpa [star_mul, hT.star_eq, hGself.star_eq, hPself.star_eq] using h
  exact ⟨{
    inverse := G
    support := P
    selfAdjoint_metric := hT
    selfAdjoint_inverse := hGself
    selfAdjoint_support := hPself
    support_idempotent := hP2
    metric_mul_inverse := hTG
    inverse_mul_metric := hGT
    metric_mul_support := hTP
    support_mul_metric := hPT
    support_mul_inverse := hPG
  }⟩

/-- **Sharp infinite closed-range boundary.**  A bounded self-adjoint semimetric has bounded
symmetric support-inverse data exactly when its range is closed.  Thus closed range is not a
technical premise hidden in the universal symmetrizer; it is the exact existence boundary. -/
theorem isClosed_range_iff_nonempty_symmetricSupportInverse
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) :
    IsClosed (T.range : Set E) ↔ Nonempty (SymmetricSupportInverse T) := by
  constructor
  · exact exists_symmetricSupportInverse_of_isClosed_range T hT
  · rintro ⟨data⟩
    have hrange : T.range = data.support.range := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        refine ⟨T x, ?_⟩
        have h := congrArg (fun A : E →L[ℝ] E => A x) data.support_mul_metric
        simpa [ContinuousLinearMap.mul_apply] using h
      · rintro y ⟨x, rfl⟩
        refine ⟨data.inverse x, ?_⟩
        have h := congrArg (fun A : E →L[ℝ] E => A x) data.metric_mul_inverse
        simpa [ContinuousLinearMap.mul_apply] using h
    rw [hrange]
    exact ContinuousLinearMap.IsIdempotentElem.isClosed_range data.support_idempotent

/-- The support projection in symmetric support-inverse data is unique. -/
theorem symmetricSupportInverse_support_unique
    (T : E →L[ℝ] E) (first second : SymmetricSupportInverse T) :
    first.support = second.support := by
  have hfirstSecond : first.support * second.support = second.support := by
    calc
      first.support * second.support =
          first.support * (T * second.inverse) := by rw [second.metric_mul_inverse]
      _ = (first.support * T) * second.inverse := by rw [mul_assoc]
      _ = T * second.inverse := by rw [first.support_mul_metric]
      _ = second.support := second.metric_mul_inverse
  have hsecondFirst : second.support * first.support = first.support := by
    calc
      second.support * first.support =
          second.support * (T * first.inverse) := by rw [first.metric_mul_inverse]
      _ = (second.support * T) * first.inverse := by rw [mul_assoc]
      _ = T * first.inverse := by rw [second.support_mul_metric]
      _ = first.support := first.metric_mul_inverse
  have hstar := congrArg star hfirstSecond
  have hreverse : second.support * first.support = second.support := by
    simpa [star_mul, first.selfAdjoint_support.star_eq,
      second.selfAdjoint_support.star_eq] using hstar
  calc
    first.support = second.support * first.support := hsecondFirst.symm
    _ = second.support := hreverse

/-- The generalized inverse in symmetric support-inverse data is unique. -/
theorem symmetricSupportInverse_inverse_unique
    (T : E →L[ℝ] E) (first second : SymmetricSupportInverse T) :
    first.inverse = second.inverse := by
  have hfirstRight : first.inverse * first.support = first.inverse := by
    have h := congrArg star first.support_mul_inverse
    simpa [star_mul, first.selfAdjoint_support.star_eq,
      first.selfAdjoint_inverse.star_eq] using h
  calc
    first.inverse = first.inverse * first.support := hfirstRight.symm
    _ = first.inverse * second.support := by
      rw [symmetricSupportInverse_support_unique T first second]
    _ = first.inverse * (T * second.inverse) := by rw [second.metric_mul_inverse]
    _ = (first.inverse * T) * second.inverse := by rw [mul_assoc]
    _ = first.support * second.inverse := by rw [first.inverse_mul_metric]
    _ = second.support * second.inverse := by
      rw [symmetricSupportInverse_support_unique T first second]
    _ = second.inverse := second.support_mul_inverse

/-- Symmetric support-inverse data, when it exists, is canonical. -/
theorem symmetricSupportInverse_unique
    (T : E →L[ℝ] E) (first second : SymmetricSupportInverse T) : first = second := by
  apply SymmetricSupportInverse.ext
  · exact symmetricSupportInverse_inverse_unique T first second
  · exact symmetricSupportInverse_support_unique T first second

/-- Canonicality as a typeclass-free subsingleton law. -/
instance symmetricSupportInverse_subsingleton (T : E →L[ℝ] E) :
    Subsingleton (SymmetricSupportInverse T) :=
  ⟨symmetricSupportInverse_unique T⟩

/-- Nonclosed range is exactly the obstruction to bounded symmetric support inversion. -/
theorem no_symmetricSupportInverse_of_not_isClosed_range
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hnot : ¬ IsClosed (T.range : Set E)) :
    IsEmpty (SymmetricSupportInverse T) :=
  ⟨fun data => hnot ((isClosed_range_iff_nonempty_symmetricSupportInverse T hT).2 ⟨data⟩)⟩

end RHTower
