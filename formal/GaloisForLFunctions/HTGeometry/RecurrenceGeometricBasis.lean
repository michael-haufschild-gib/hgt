import Mathlib

/-!
# A recurrence with distinct characteristic roots has a geometric basis

If the characteristic polynomial of a linear recurrence has as many distinct roots as its order,
every solution is a combination of the corresponding geometric sequences: the geometric solutions
are independent by Vandermonde and there are as many of them as the dimension of the solution space.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {K : Type*} [Field K]

/-- The geometric combinations attached to a family of ratios. -/
def geomCombination {t : ℕ} (lam : Fin t → K) (c : Fin t → K) : ℕ → K :=
  fun n => ∑ k, c k * lam k ^ n

theorem geomCombination_eq_zero_iff {t : ℕ} {lam : Fin t → K} (hinj : Function.Injective lam)
    {c : Fin t → K} (h : ∀ n, geomCombination lam c n = 0) : c = 0 := by
  classical
  have hdet : (Matrix.vandermonde lam).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff).2 hinj
  have hmul : (Matrix.vandermonde lam)ᵀ *ᵥ c = 0 := by
    funext n
    have hn := h (n : ℕ)
    simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.vandermonde, Matrix.of_apply,
      Pi.zero_apply, dotProduct]
    rw [← hn, geomCombination]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine Matrix.eq_zero_of_mulVec_eq_zero ?_ hmul
  rwa [Matrix.det_transpose]

/-- The linear map sending coefficients to the corresponding geometric combination. -/
def geomMap {t : ℕ} (lam : Fin t → K) : (Fin t → K) →ₗ[K] (ℕ → K) where
  toFun c := geomCombination lam c
  map_add' c d := by
    funext n
    simp only [geomCombination, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  map_smul' a c := by
    funext n
    simp only [geomCombination, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem geomMap_injective {t : ℕ} {lam : Fin t → K} (hinj : Function.Injective lam) :
    Function.Injective (geomMap lam) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).2 fun c hc => ?_
  refine geomCombination_eq_zero_iff hinj fun n => ?_
  have := congrFun (LinearMap.mem_ker.1 hc) n
  simpa [geomMap] using this

/-- **Every solution of a recurrence with a full set of distinct characteristic roots is a
combination of geometric sequences.** -/
theorem exists_geomCombination_of_distinct_roots (E : LinearRecurrence K)
    (lam : Fin E.order → K) (hinj : Function.Injective lam)
    (hroot : ∀ k, E.charPoly.IsRoot (lam k))
    {u : ℕ → K} (hu : E.IsSolution u) :
    ∃ c : Fin E.order → K, ∀ n, u n = geomCombination lam c n := by
  classical
  have hmem : ∀ c : Fin E.order → K, geomMap lam c ∈ E.solSpace := by
    intro c
    have hgeom : ∀ k, (fun n => lam k ^ n) ∈ E.solSpace := fun k =>
      (E.is_sol_iff_mem_solSpace _).1 ((E.geom_sol_iff_root_charPoly (lam k)).2 (hroot k))
    have hrw : geomMap lam c = ∑ k, c k • (fun n => lam k ^ n : ℕ → K) := by
      funext n
      simp only [geomMap, geomCombination, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    rw [hrw]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hgeom k)
  set Φ : (Fin E.order → K) →ₗ[K] E.solSpace :=
    { toFun := fun c => ⟨geomMap lam c, hmem c⟩
      map_add' := fun c d => by
        refine Subtype.ext ?_
        simp
      map_smul' := fun a c => by
        refine Subtype.ext ?_
        simp } with hΦ
  haveI : FiniteDimensional K E.solSpace :=
    Module.Finite.equiv E.toInit.symm
  have hΦinj : Function.Injective Φ := by
    intro c d hcd
    refine geomMap_injective hinj ?_
    exact congrArg Subtype.val hcd
  have hrank : Module.finrank K E.solSpace = E.order := by
    rw [E.toInit.finrank_eq]
    simp
  have hsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hΦinj
    rw [hrank]
    simp
  obtain ⟨c, hc⟩ := hsurj ⟨u, (E.is_sol_iff_mem_solSpace u).1 hu⟩
  refine ⟨c, fun n => ?_⟩
  have hval := congrArg Subtype.val hc
  exact (congrFun hval n).symm

end GaloisForLFunctions.HTGeometry
