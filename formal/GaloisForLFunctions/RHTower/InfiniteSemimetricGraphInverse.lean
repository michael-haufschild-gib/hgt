/-
# Infinite graph-domain semimetric symmetrization

Every bounded operator `T` on a real Hilbert space has a canonical closed, possibly unbounded,
support inverse.  Its exact domain is `range T`; it returns the unique preimage in `(ker T)ᗮ`.
Thus nonclosed range does not destroy inversion: it forces inversion out of the bounded category
and into a closed partially defined operator.

For bounded self-adjoint `T` and arbitrary bounded `D`, the incidence domain

`{x | D† T x ∈ range T}`

supports a canonical graph symmetrizer.  It annihilates the radical and is symmetric for the
`T`-metric.  This is the arbitrary-rank graph-domain extension of the bounded closed-range law.
-/
import GaloisForLFunctions.RHTower.InfiniteSemimetricSymmetrization
import Mathlib.Analysis.InnerProductSpace.LinearPMap

noncomputable section

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restriction of a bounded operator to the orthogonal complement of its kernel. -/
def supportRestriction (T : E →L[ℝ] E) : E →ₗ.[ℝ] E :=
  T.toLinearMap.toPMap T.kerᗮ

/-- Canonical partially defined support inverse. -/
def closedSupportInverse (T : E →L[ℝ] E) : E →ₗ.[ℝ] E :=
  (supportRestriction T).inverse

theorem supportRestriction_toFun_ker_eq_bot (T : E →L[ℝ] E) :
    LinearMap.ker (supportRestriction T).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨x, hxS⟩ hx
  apply Subtype.ext
  change x = 0
  have hxK : x ∈ T.ker := by
    change T x = 0
    exact hx
  have hxbot : x ∈ T.ker ⊓ T.kerᗮ := ⟨hxK, hxS⟩
  have : x ∈ (⊥ : Submodule ℝ E) := T.ker.orthogonal_disjoint.le_bot hxbot
  simpa using this

def supportRestrictionGraphDefect (T : E →L[ℝ] E) : (E × E) →L[ℝ] E :=
  T.comp (ContinuousLinearMap.fst ℝ E E) - ContinuousLinearMap.snd ℝ E E

theorem supportRestriction_graph_eq (T : E →L[ℝ] E) :
    (supportRestriction T).graph =
      T.kerᗮ.comap (ContinuousLinearMap.fst ℝ E E).toLinearMap ⊓
        (supportRestrictionGraphDefect T).ker := by
  ext p
  constructor
  · intro hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨x, hxp, hxout⟩
    constructor
    · change p.1 ∈ T.kerᗮ
      rw [← hxp]
      exact x.property
    · change T p.1 - p.2 = 0
      rw [← hxp, ← hxout]
      simp [supportRestriction]
  · rintro ⟨hpS, hpD⟩
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨p.1, hpS⟩, rfl, ?_⟩
    change T p.1 = p.2
    change T p.1 - p.2 = 0 at hpD
    exact sub_eq_zero.mp hpD

theorem supportRestriction_isClosed (T : E →L[ℝ] E) :
    (supportRestriction T).IsClosed := by
  rw [LinearPMap.IsClosed, supportRestriction_graph_eq]
  apply IsClosed.inter
  · exact (Submodule.isClosed_orthogonal T.ker).preimage
      (ContinuousLinearMap.fst ℝ E E).continuous
  · exact (supportRestrictionGraphDefect T).isClosed_ker

theorem closedSupportInverse_isClosed (T : E →L[ℝ] E) :
    (closedSupportInverse T).IsClosed := by
  exact (LinearPMap.inverse_closed_iff (supportRestriction_toFun_ker_eq_bot T)).2
    (supportRestriction_isClosed T)

variable [CompleteSpace E]

theorem closedSupportInverse_domain (T : E →L[ℝ] E) :
    (closedSupportInverse T).domain = T.range := by
  rw [closedSupportInverse, LinearPMap.inverse_domain]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    let S : Submodule ℝ E := T.kerᗮ
    letI : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
    letI : T.ker.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace T.ker
    letI : CompleteSpace S := (Submodule.isClosed_orthogonal T.ker).completeSpace_coe
    letI : S.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace S
    let sx : S := S.orthogonalProjection x
    refine ⟨sx, ?_⟩
    change T (S.starProjection x) = T x
    have hdiff : x - S.starProjection x ∈ T.ker := by
      have horth := Submodule.sub_starProjection_mem_orthogonal x (K := S)
      have hSK : Sᗮ = T.ker := by
        change T.kerᗮᗮ = T.ker
        exact Submodule.orthogonal_orthogonal T.ker
      simpa [hSK] using horth
    have hz : T (x - S.starProjection x) = 0 := hdiff
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm

theorem not_isClosed_closedSupportInverse_domain_of_not_isClosed_range
    (T : E →L[ℝ] E) (hnot : ¬ IsClosed (T.range : Set E)) :
    ¬ IsClosed ((closedSupportInverse T).domain : Set E) := by
  simpa [closedSupportInverse_domain] using hnot

theorem dense_closedSupportInverse_domain_iff_dense_range (T : E →L[ℝ] E) :
    Dense ((closedSupportInverse T).domain : Set E) ↔ Dense (T.range : Set E) := by
  rw [closedSupportInverse_domain]

omit [CompleteSpace E] in
theorem closedSupportInverse_rightInverse
    (T : E →L[ℝ] E) (y : (closedSupportInverse T).domain) :
    T (closedSupportInverse T y) = y := by
  change T ((supportRestriction T).inverse y) = y
  have hyrange : (y : E) ∈ LinearMap.range (supportRestriction T).toFun := by
    rw [← LinearPMap.inverse_domain]
    exact y.property
  rcases hyrange with ⟨x, hx⟩
  have hinv : (supportRestriction T).inverse y = x :=
    LinearPMap.inverse_apply_eq (supportRestriction_toFun_ker_eq_bot T) hx
  rw [hinv]
  simpa [supportRestriction] using! hx

theorem closedSupportInverse_apply_eq_algebraicSupportRangeEquiv_symm
    (T : E →L[ℝ] E) (y : (closedSupportInverse T).domain) :
    closedSupportInverse T y =
      (algebraicSupportRangeEquiv T).symm
        ⟨y, by simpa [closedSupportInverse_domain] using y.property⟩ := by
  change (supportRestriction T).inverse y = _
  apply LinearPMap.inverse_apply_eq (supportRestriction_toFun_ker_eq_bot T)
  change T ((algebraicSupportRangeEquiv T).symm
    ⟨y, by simpa [closedSupportInverse_domain] using y.property⟩) = y
  exact algebraicSupportRangeEquiv_symm_rightInverse T
    ⟨y, by simpa [closedSupportInverse_domain] using y.property⟩

/-- Orthogonal projection onto the support `(ker T)ᗮ`. -/
def kernelSupportProjection (T : E →L[ℝ] E) : E →L[ℝ] E := by
  let K : Submodule ℝ E := T.ker
  let S : Submodule ℝ E := Kᗮ
  letI : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  letI : K.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace K
  letI : CompleteSpace S := (Submodule.isClosed_orthogonal K).completeSpace_coe
  letI : S.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace S
  exact S.starProjection

theorem kernelSupportProjection_isSelfAdjoint (T : E →L[ℝ] E) :
    IsSelfAdjoint (kernelSupportProjection T) := by
  dsimp [kernelSupportProjection]
  exact isSelfAdjoint_starProjection T.kerᗮ

theorem kernelSupportProjection_idempotent (T : E →L[ℝ] E) :
    kernelSupportProjection T * kernelSupportProjection T = kernelSupportProjection T := by
  dsimp [kernelSupportProjection]
  exact T.kerᗮ.isIdempotentElem_starProjection

theorem kernelSupportProjection_apply_mem (T : E →L[ℝ] E) (x : E) :
    kernelSupportProjection T x ∈ T.kerᗮ := by
  dsimp [kernelSupportProjection]
  exact Submodule.starProjection_apply_mem _ _

theorem kernelSupportProjection_apply_eq_self_of_mem
    (T : E →L[ℝ] E) (x : E) (hx : x ∈ T.kerᗮ) :
    kernelSupportProjection T x = x := by
  dsimp [kernelSupportProjection]
  exact Submodule.starProjection_eq_self_iff.mpr hx

theorem kernelSupportProjection_apply_eq_zero_of_mem_ker
    (T : E →L[ℝ] E) (x : E) (hx : T x = 0) :
    kernelSupportProjection T x = 0 := by
  have hxK : x ∈ T.ker := hx
  have hxorth : x ∈ (T.kerᗮ)ᗮ := by
    simpa using hxK
  dsimp [kernelSupportProjection]
  exact (Submodule.starProjection_apply_eq_zero_iff (K := T.kerᗮ)).2 hxorth

theorem metric_mul_kernelSupportProjection (T : E →L[ℝ] E) :
    T * kernelSupportProjection T = T := by
  ext x
  change T (kernelSupportProjection T x) = T x
  let S : Submodule ℝ E := T.kerᗮ
  have hdiff : x - kernelSupportProjection T x ∈ T.ker := by
    have horth : x - kernelSupportProjection T x ∈ Sᗮ := by
      dsimp [kernelSupportProjection]
      exact Submodule.sub_starProjection_mem_orthogonal x
    have hSK : Sᗮ = T.ker := by
      change T.kerᗮᗮ = T.ker
      exact Submodule.orthogonal_orthogonal T.ker
    simpa [hSK] using horth
  have hz : T (x - kernelSupportProjection T x) = 0 := hdiff
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

theorem kernelSupportProjection_mul_metric
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) :
    kernelSupportProjection T * T = T := by
  have h := congrArg star (metric_mul_kernelSupportProjection T)
  simpa [star_mul, hT.star_eq, (kernelSupportProjection_isSelfAdjoint T).star_eq] using h

theorem range_le_kernel_orthogonal
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) : T.range ≤ T.kerᗮ := by
  intro y hy
  have hyy : y ∈ T.rangeᗮᗮ := T.range.le_orthogonal_orthogonal hy
  have hrangeOrth : T.rangeᗮ = T.ker :=
    ContinuousLinearMap.IsStarNormal.orthogonal_range hT.isStarNormal
  simpa [hrangeOrth] using hyy

theorem closedSupportInverse_metric_apply
    (T : E →L[ℝ] E) (x : E) :
    closedSupportInverse T
      ⟨T x, by
        rw [closedSupportInverse_domain]
        exact ⟨x, rfl⟩⟩ = kernelSupportProjection T x := by
  change (supportRestriction T).inverse _ = kernelSupportProjection T x
  let px : (supportRestriction T).domain :=
    ⟨kernelSupportProjection T x, kernelSupportProjection_apply_mem T x⟩
  have hxy : supportRestriction T px = T x := by
    change T (kernelSupportProjection T x) = T x
    have h := congrArg (fun A : E →L[ℝ] E => A x)
      (metric_mul_kernelSupportProjection T)
    simpa [mul_apply_eq_comp] using h
  exact LinearPMap.inverse_apply_eq (supportRestriction_toFun_ker_eq_bot T) hxy

theorem closedSupportInverse_formalSymmetric
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) :
    (closedSupportInverse T).IsFormalAdjoint (closedSupportInverse T) := by
  intro x y
  rw [closedSupportInverse_apply_eq_algebraicSupportRangeEquiv_symm,
    closedSupportInverse_apply_eq_algebraicSupportRangeEquiv_symm]
  let xi : T.kerᗮ := (algebraicSupportRangeEquiv T).symm
    ⟨x, by simpa [closedSupportInverse_domain] using x.property⟩
  let yi : T.kerᗮ := (algebraicSupportRangeEquiv T).symm
    ⟨y, by simpa [closedSupportInverse_domain] using y.property⟩
  have hx : T xi = x := algebraicSupportRangeEquiv_symm_rightInverse T
    ⟨x, by simpa [closedSupportInverse_domain] using x.property⟩
  have hy : T yi = y := algebraicSupportRangeEquiv_symm_rightInverse T
    ⟨y, by simpa [closedSupportInverse_domain] using y.property⟩
  change inner ℝ (xi : E) (y : E) = inner ℝ (x : E) (yi : E)
  rw [← hy, ← hx]
  exact (hT.isSymmetric xi yi).symm

def graphSemimetricIncidenceDomain
    (T D : E →L[ℝ] E) : Submodule ℝ E :=
  T.range.comap (star D * T).toLinearMap

def graphSemimetricInverseTerm
    (T D : E →L[ℝ] E) : E →ₗ.[ℝ] E :=
  (closedSupportInverse T).comp
    ((star D * T).toLinearMap.toPMap (graphSemimetricIncidenceDomain T D))
    (fun x => by
      rw [closedSupportInverse_domain]
      exact x.property)

def graphSemimetricSymmetrization
    (T D : E →L[ℝ] E) : E →ₗ.[ℝ] E :=
  (1 / 2 : ℝ) •
    ((kernelSupportProjection T * D * kernelSupportProjection T).toLinearMap +ᵥ
      graphSemimetricInverseTerm T D)

theorem graphSemimetricSymmetrization_domain (T D : E →L[ℝ] E) :
    (graphSemimetricSymmetrization T D).domain =
      graphSemimetricIncidenceDomain T D := by
  rfl

theorem mem_graphSemimetricSymmetrization_domain_iff (T D : E →L[ℝ] E) (x : E) :
    x ∈ (graphSemimetricSymmetrization T D).domain ↔ star D (T x) ∈ T.range := by
  rfl

theorem graphSemimetricInverseTerm_apply
    (T D : E →L[ℝ] E) (x : (graphSemimetricInverseTerm T D).domain) :
    graphSemimetricInverseTerm T D x =
      closedSupportInverse T
        ⟨star D (T x), by
          rw [closedSupportInverse_domain]
          exact x.property⟩ := by
  rfl

theorem graphSemimetricSymmetrization_apply
    (T D : E →L[ℝ] E) (x : (graphSemimetricSymmetrization T D).domain) :
    graphSemimetricSymmetrization T D x =
      (1 / 2 : ℝ) •
        (kernelSupportProjection T (D (kernelSupportProjection T x)) +
          closedSupportInverse T
            ⟨star D (T x), by
              rw [closedSupportInverse_domain]
              exact x.property⟩) := by
  rfl

theorem metric_graphSemimetricSymmetrization_apply
    (T D : E →L[ℝ] E)
    (x : (graphSemimetricSymmetrization T D).domain) :
    T (graphSemimetricSymmetrization T D x) =
      (1 / 2 : ℝ) • (T (D (kernelSupportProjection T x)) + star D (T x)) := by
  rw [graphSemimetricSymmetrization_apply, map_smul, map_add]
  have hP : T (kernelSupportProjection T (D (kernelSupportProjection T x))) =
      T (D (kernelSupportProjection T x)) := by
    have h := congrArg (fun A : E →L[ℝ] E => A (D (kernelSupportProjection T x)))
      (metric_mul_kernelSupportProjection T)
    simpa [mul_apply_eq_comp] using h
  have hG : T (closedSupportInverse T
      ⟨star D (T x), by
        rw [closedSupportInverse_domain]
        exact x.property⟩) = star D (T x) :=
    closedSupportInverse_rightInverse T _
  rw [hP, hG]

theorem graphSemimetricSymmetrization_mem_domain_of_mem_ker
    (T D : E →L[ℝ] E) (x : E) (hx : T x = 0) :
    x ∈ (graphSemimetricSymmetrization T D).domain := by
  rw [mem_graphSemimetricSymmetrization_domain_iff, hx, map_zero]
  exact Submodule.zero_mem _

theorem graphSemimetricSymmetrization_apply_eq_zero_of_mem_ker
    (T D : E →L[ℝ] E) (x : E) (hx : T x = 0) :
    graphSemimetricSymmetrization T D
      ⟨x, graphSemimetricSymmetrization_mem_domain_of_mem_ker T D x hx⟩ = 0 := by
  let z : (graphSemimetricSymmetrization T D).domain :=
    ⟨x, graphSemimetricSymmetrization_mem_domain_of_mem_ker T D x hx⟩
  change graphSemimetricSymmetrization T D z = 0
  rw [graphSemimetricSymmetrization_apply]
  have hP : kernelSupportProjection T (z : E) = 0 := by
    exact kernelSupportProjection_apply_eq_zero_of_mem_ker T x hx
  have hinc : star D (T (z : E)) = 0 := by simp [z, hx]
  have hG : ∀ (hz : star D (T (z : E)) ∈ (closedSupportInverse T).domain),
      closedSupportInverse T ⟨star D (T (z : E)), hz⟩ = 0 := by
    intro hz
    have heq : (⟨star D (T (z : E)), hz⟩ : (closedSupportInverse T).domain) = 0 := by
      apply Subtype.ext
      exact hinc
    rw [heq]
    exact LinearPMap.map_zero _
  rw [hP, map_zero, hG, add_zero]
  simp

theorem graphSemimetricSymmetrization_metricSymmetric
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) (D : E →L[ℝ] E)
    (x y : (graphSemimetricSymmetrization T D).domain) :
    inner ℝ (T (graphSemimetricSymmetrization T D x)) (y : E) =
      inner ℝ (T (x : E)) (graphSemimetricSymmetrization T D y) := by
  have hL1 : inner ℝ (T (D (kernelSupportProjection T x))) (y : E) =
      inner ℝ (D (kernelSupportProjection T x)) (T y) :=
    hT.isSymmetric _ _
  have hL2 : inner ℝ (star D (T x)) (y : E) = inner ℝ (T x) (D y) := by
    simpa using! ContinuousLinearMap.adjoint_inner_left D (y : E) (T x)
  have hPTx : kernelSupportProjection T (T x) = T x := by
    have hmul := congrArg (fun A : E →L[ℝ] E => A (x : E))
      (kernelSupportProjection_mul_metric T hT)
    simpa [mul_apply_eq_comp] using hmul
  have hR1 : inner ℝ (T x)
      (kernelSupportProjection T (D (kernelSupportProjection T y))) =
      inner ℝ (T x) (D (kernelSupportProjection T y)) := by
    calc
      inner ℝ (T x) (kernelSupportProjection T (D (kernelSupportProjection T y))) =
          inner ℝ (kernelSupportProjection T (T x))
            (D (kernelSupportProjection T y)) :=
        ((kernelSupportProjection_isSelfAdjoint T).isSymmetric _ _).symm
      _ = inner ℝ (T x) (D (kernelSupportProjection T y)) := by rw [hPTx]
  let tx : (closedSupportInverse T).domain :=
    ⟨T x, by
      rw [closedSupportInverse_domain]
      exact ⟨x, rfl⟩⟩
  let zy : (closedSupportInverse T).domain :=
    ⟨star D (T y), by
      rw [closedSupportInverse_domain]
      exact y.property⟩
  have hR2 : inner ℝ (T x) (closedSupportInverse T zy) =
      inner ℝ (D (kernelSupportProjection T x)) (T y) := by
    calc
      inner ℝ (T x) (closedSupportInverse T zy) =
          inner ℝ (closedSupportInverse T tx) (star D (T y)) := by
        exact (closedSupportInverse_formalSymmetric T hT tx zy).symm
      _ = inner ℝ (kernelSupportProjection T x) (star D (T y)) := by
        rw [closedSupportInverse_metric_apply]
      _ = inner ℝ (D (kernelSupportProjection T x)) (T y) := by
        simpa using! ContinuousLinearMap.adjoint_inner_right D
          (kernelSupportProjection T x) (T y)
  have hincX : inner ℝ (T x) (D y) =
      inner ℝ (T x) (D (kernelSupportProjection T y)) := by
    have hzRange : star D (T x) ∈ T.range := x.property
    have hzSupport : star D (T x) ∈ T.kerᗮ := range_le_kernel_orthogonal T hT hzRange
    have hPz : kernelSupportProjection T (star D (T x)) = star D (T x) :=
      kernelSupportProjection_apply_eq_self_of_mem T _ hzSupport
    calc
      inner ℝ (T x) (D y) = inner ℝ (star D (T x)) (y : E) := by
        symm
        simpa using! ContinuousLinearMap.adjoint_inner_left D (y : E) (T x)
      _ = inner ℝ (kernelSupportProjection T (star D (T x))) (y : E) := by rw [hPz]
      _ = inner ℝ (star D (T x)) (kernelSupportProjection T y) :=
        (kernelSupportProjection_isSelfAdjoint T).isSymmetric _ _
      _ = inner ℝ (T x) (D (kernelSupportProjection T y)) := by
        simpa using! ContinuousLinearMap.adjoint_inner_left D
          (kernelSupportProjection T y) (T x)
  rw [metric_graphSemimetricSymmetrization_apply,
    graphSemimetricSymmetrization_apply]
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    conj_trivial]
  rw [hL1, hL2, hR1, hR2, hincX]
  abel_nf

end RHTower
