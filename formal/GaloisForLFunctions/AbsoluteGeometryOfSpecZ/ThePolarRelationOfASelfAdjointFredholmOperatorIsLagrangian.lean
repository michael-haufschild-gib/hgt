import GaloisForLFunctions.HTGeometry.BoundedFredholmStability

/-!
# The polar relation of a self-adjoint Fredholm operator is Lagrangian

Let `T` be a bounded self-adjoint operator on a Hilbert space `H` with `1 − T` compact, and let
`d : H → V` be a continuous linear map to a finite-dimensional inner product space: the charges
of a vector. The **polar relation** of `T` and `d` is

  `L = {(x, y) ∈ V × V : there is ξ with d ξ = x and T ξ = d† y}`   (`polarRelation`):

the vectors that `T` maps into the range of `d†`, read through their charges and their forcing.

* `L` is isotropic for the form `ω((x, y), (x', y')) = ⟨y, x'⟩ − ⟨x, y'⟩` on `V × V`
  (`polarRelation_isotropic`): `⟨y, x'⟩ = ⟨T ξ, ξ'⟩ = ⟨ξ, T ξ'⟩ = ⟨x, y'⟩`.
* `dim L = dim V` (`finrank_polarRelation`): the second projection of `L` is the orthogonal
  complement of the charges `d(ker T)` of the null space, because the range of `T` is the
  orthogonal complement of its kernel; the kernel of the projection is `d(ker T)`.

So `L` is a Lagrangian subspace of `V × V`. Its intersection with `V × 0` is `d(ker T) × 0`
(`mem_polarRelation_zero_right`): the null vectors of `T`, seen through their charges. A null
vector without charge is not seen, and
`dim ker T = dim d(ker T) + dim (ker T ∩ ker d)` (`finrank_ker_eq_charged_add_neutral`).

Its intersection with `0 × V` comes from the vectors without charge that `T` maps to a forcing
(`mem_polarRelation_zero_left`), and a vector is a forcing exactly when it is orthogonal to the
vectors without charge (`exists_eq_adjoint_iff`): these are the null vectors of the form of `T`
restricted to the kernel of `d`.
-/

open Module
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HTGeometry

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A self-adjoint operator is symmetric. -/
theorem inner_apply_eq_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (x y : H) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h := ContinuousLinearMap.adjoint_inner_right T x y
  rw [hT.adjoint_eq] at h
  exact h.symm

/-- **The range of a self-adjoint operator `1 − compact` is the orthogonal complement of its
kernel.** -/
theorem exists_apply_eq_of_mem_orthogonal_ker {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (hK : IsCompactOperator (1 - T : H →L[ℂ] H)) {η : H}
    (hη : η ∈ (LinearMap.ker (T : H →ₗ[ℂ] H))ᗮ) : ∃ ξ, T ξ = η := by
  have hC : IsCompactOperator (-(1 - T) : H →L[ℂ] H) := hK.neg
  have hF : IsFredholmOp T := by
    have h := isFredholmOp_one_add_compact hC
    rwa [show (1 : H →L[ℂ] H) + -(1 - T) = T by abel] at h
  haveI := hF.hasOrthogonalProjection_range
  have h1 : (LinearMap.range (T : H →ₗ[ℂ] H))ᗮ = LinearMap.ker (T : H →ₗ[ℂ] H) := by
    ext v
    rw [Submodule.mem_orthogonal]
    constructor
    · intro h
      have h0 : ⟪T (T v), v⟫_ℂ = 0 := h (T (T v)) ⟨T v, rfl⟩
      rw [inner_apply_eq_of_isSelfAdjoint hT] at h0
      exact inner_self_eq_zero.mp h0
    · rintro hv u ⟨ξ, rfl⟩
      have hv0 : T v = 0 := hv
      show ⟪T ξ, v⟫_ℂ = 0
      rw [inner_apply_eq_of_isSelfAdjoint hT, hv0, inner_zero_right]
  have h2 : η ∈ (LinearMap.range (T : H →ₗ[ℂ] H))ᗮᗮ := by
    rw [h1]
    exact hη
  rw [Submodule.orthogonal_orthogonal] at h2
  obtain ⟨ξ, hξ⟩ := h2
  exact ⟨ξ, hξ⟩

/-- **The polar relation** of an operator `T` and a charge map `d`: the pairs (charges, forcing)
of the vectors that `T` maps into the range of `d†`. -/
def polarRelation (T : H →L[ℂ] H) (d : H →L[ℂ] V) : Submodule ℂ (V × V) where
  carrier := {p | ∃ ξ, d ξ = p.1 ∧ T ξ = ContinuousLinearMap.adjoint d p.2}
  add_mem' := by
    rintro p q ⟨ξ, h1, h2⟩ ⟨ξ', h1', h2'⟩
    exact ⟨ξ + ξ', by rw [map_add, h1, h1', Prod.fst_add],
      by rw [map_add, h2, h2', Prod.snd_add, map_add]⟩
  zero_mem' := ⟨0, by rw [map_zero, Prod.fst_zero], by rw [map_zero, Prod.snd_zero, map_zero]⟩
  smul_mem' := by
    rintro c p ⟨ξ, h1, h2⟩
    exact ⟨c • ξ, by rw [map_smul, h1, Prod.smul_fst], by rw [map_smul, h2, Prod.smul_snd, map_smul]⟩

variable {T : H →L[ℂ] H} {d : H →L[ℂ] V}

theorem mem_polarRelation {p : V × V} :
    p ∈ polarRelation T d ↔ ∃ ξ, d ξ = p.1 ∧ T ξ = ContinuousLinearMap.adjoint d p.2 :=
  Iff.rfl

/-- **The polar relation is isotropic** for `ω((x, y), (x', y')) = ⟨y, x'⟩ − ⟨x, y'⟩`. -/
theorem polarRelation_isotropic (hT : IsSelfAdjoint T) {p q : V × V}
    (hp : p ∈ polarRelation T d) (hq : q ∈ polarRelation T d) :
    ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ := by
  obtain ⟨ξ, h1, h2⟩ := hp
  obtain ⟨ξ', h1', h2'⟩ := hq
  calc ⟪p.2, q.1⟫_ℂ = ⟪p.2, d ξ'⟫_ℂ := by rw [h1']
    _ = ⟪ContinuousLinearMap.adjoint d p.2, ξ'⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left d ξ' p.2).symm
    _ = ⟪T ξ, ξ'⟫_ℂ := by rw [h2]
    _ = ⟪ξ, T ξ'⟫_ℂ := inner_apply_eq_of_isSelfAdjoint hT ξ ξ'
    _ = ⟪ξ, ContinuousLinearMap.adjoint d q.2⟫_ℂ := by rw [h2']
    _ = ⟪d ξ, q.2⟫_ℂ := ContinuousLinearMap.adjoint_inner_right d ξ q.2
    _ = ⟪p.1, q.2⟫_ℂ := by rw [h1]

/-- **The crossing with `V × 0`**: the charges of the null vectors. -/
theorem mem_polarRelation_zero_right {x : V} :
    (x, (0 : V)) ∈ polarRelation T d ↔ ∃ ξ, T ξ = 0 ∧ d ξ = x := by
  constructor
  · rintro ⟨ξ, h1, h2⟩
    exact ⟨ξ, by rw [h2]; exact map_zero _, h1⟩
  · rintro ⟨ξ, h1, h2⟩
    exact ⟨ξ, h2, by rw [h1]; exact (map_zero _).symm⟩

/-- **The crossing with `0 × V`**: the vectors without charge that `T` maps to a forcing. -/
theorem mem_polarRelation_zero_left {y : V} :
    ((0 : V), y) ∈ polarRelation T d ↔ ∃ ξ, d ξ = 0 ∧ T ξ = ContinuousLinearMap.adjoint d y :=
  Iff.rfl

/-- **The forcings are the vectors orthogonal to the vectors without charge**: the range of `d†`
is the orthogonal complement of the kernel of `d`. -/
theorem exists_eq_adjoint_iff [FiniteDimensional ℂ V] (η : H) :
    (∃ y, η = ContinuousLinearMap.adjoint d y) ↔ ∀ v, d v = 0 → ⟪η, v⟫_ℂ = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ v hv
    rw [ContinuousLinearMap.adjoint_inner_left, hv, inner_zero_right]
  · intro h
    have hmem : η ∈ (LinearMap.range (ContinuousLinearMap.adjoint d : V →ₗ[ℂ] H))ᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro v hv
      have hdv : d v = 0 := by
        have h0 : ⟪d v, d v⟫_ℂ = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_left]
          exact (Submodule.mem_orthogonal _ _).mp hv _ ⟨d v, rfl⟩
        exact inner_self_eq_zero.mp h0
      rw [← inner_conj_symm, h v hdv, map_zero]
    rw [Submodule.orthogonal_orthogonal] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy.symm⟩

/-- **The polar relation is half-dimensional**: with isotropy, a Lagrangian subspace of
`V × V`. -/
theorem finrank_polarRelation [FiniteDimensional ℂ V] (hT : IsSelfAdjoint T)
    (hK : IsCompactOperator (1 - T : H →L[ℂ] H)) :
    finrank ℂ (polarRelation T d) = finrank ℂ V := by
  -- the charges of the null space
  have hM : ∀ k : H, T k = 0 → d k ∈ (LinearMap.ker (T : H →ₗ[ℂ] H)).map (d : H →ₗ[ℂ] V) :=
    fun k hk => ⟨k, hk, rfl⟩
  -- the second projection of the relation
  have hrange : LinearMap.range ((LinearMap.snd ℂ V V).comp (polarRelation T d).subtype) =
      ((LinearMap.ker (T : H →ₗ[ℂ] H)).map (d : H →ₗ[ℂ] V))ᗮ := by
    ext y
    constructor
    · rintro ⟨⟨p, ξ, h1, h2⟩, rfl⟩
      rw [Submodule.mem_orthogonal]
      rintro m ⟨k, hk, rfl⟩
      have hk0 : T k = 0 := hk
      show ⟪d k, p.2⟫_ℂ = 0
      rw [← ContinuousLinearMap.adjoint_inner_right, ← h2,
        ← inner_apply_eq_of_isSelfAdjoint hT, hk0, inner_zero_left]
    · intro hy
      have hperp : ContinuousLinearMap.adjoint d y ∈ (LinearMap.ker (T : H →ₗ[ℂ] H))ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro k hk
        rw [ContinuousLinearMap.adjoint_inner_right]
        exact (Submodule.mem_orthogonal _ _).mp hy (d k) (hM k hk)
      obtain ⟨ξ, hξ⟩ := exists_apply_eq_of_mem_orthogonal_ker hT hK hperp
      exact ⟨⟨(d ξ, y), ξ, rfl, hξ⟩, rfl⟩
  -- the kernel of the projection, through the first coordinate
  have hinj : Function.Injective ((LinearMap.fst ℂ V V).comp ((polarRelation T d).subtype.comp
      (LinearMap.ker ((LinearMap.snd ℂ V V).comp (polarRelation T d).subtype)).subtype)) := by
    refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    have h2 : (z.1.1 : V × V).2 = 0 := z.2
    exact Subtype.ext (Subtype.ext (Prod.ext hz h2))
  have hrange' : LinearMap.range ((LinearMap.fst ℂ V V).comp ((polarRelation T d).subtype.comp
      (LinearMap.ker ((LinearMap.snd ℂ V V).comp (polarRelation T d).subtype)).subtype)) =
      (LinearMap.ker (T : H →ₗ[ℂ] H)).map (d : H →ₗ[ℂ] V) := by
    ext x
    constructor
    · rintro ⟨⟨⟨p, ξ, h1, h2⟩, hz⟩, rfl⟩
      have hp2 : p.2 = 0 := hz
      refine ⟨ξ, ?_, h1⟩
      show T ξ = 0
      rw [h2, hp2, map_zero]
    · rintro ⟨k, hk, rfl⟩
      have hk0 : T k = 0 := hk
      exact ⟨⟨⟨(d k, 0), k, rfl, by
        show T k = ContinuousLinearMap.adjoint d 0
        rw [map_zero, hk0]⟩, rfl⟩, rfl⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.snd ℂ V V).comp (polarRelation T d).subtype)
  have h2 := LinearMap.finrank_range_of_inj hinj
  have h3 := Submodule.finrank_add_finrank_orthogonal
    ((LinearMap.ker (T : H →ₗ[ℂ] H)).map (d : H →ₗ[ℂ] V))
  rw [hrange] at h1
  rw [hrange'] at h2
  omega

omit [CompleteSpace H] [CompleteSpace V] in
/-- **The null space splits into its charged and its neutral part.** -/
theorem finrank_ker_eq_charged_add_neutral
    [FiniteDimensional ℂ (LinearMap.ker (T : H →ₗ[ℂ] H))] :
    finrank ℂ (LinearMap.ker (T : H →ₗ[ℂ] H)) =
      finrank ℂ ((LinearMap.ker (T : H →ₗ[ℂ] H)).map (d : H →ₗ[ℂ] V)) +
        finrank ℂ (LinearMap.ker ((d : H →ₗ[ℂ] V).domRestrict
          (LinearMap.ker (T : H →ₗ[ℂ] H)))) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((d : H →ₗ[ℂ] V).domRestrict (LinearMap.ker (T : H →ₗ[ℂ] H)))
  have hr : LinearMap.range ((d : H →ₗ[ℂ] V).domRestrict (LinearMap.ker (T : H →ₗ[ℂ] H))) =
      (LinearMap.ker (T : H →ₗ[ℂ] H)).map (d : H →ₗ[ℂ] V) := by
    ext x
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [hr] at h
  exact h.symm

omit [CompleteSpace H] [CompleteSpace V] in
/-- The crossing of the polar relation with `V × 0` has at most the dimension of `V`. -/
theorem finrank_map_ker_le [FiniteDimensional ℂ V] :
    finrank ℂ ((LinearMap.ker (T : H →ₗ[ℂ] H)).map (d : H →ₗ[ℂ] V)) ≤ finrank ℂ V :=
  Submodule.finrank_le _

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
