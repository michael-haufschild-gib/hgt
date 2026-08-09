import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.IncompatDerived

/-!
# Arbitrary derived pullback of the source orientation line

Let `A` be a commutative `R`-algebra and let `u = algebraMap R A q` be the image of the monodromy
parameter.  Tensoring the free resolution `R --(q-1)--> R` with `A` gives the two-term complex
`A --(u-1)--> A`, so the derived pullback of the source orientation line `Q_src ≅ R ⧸ (q-1)` has

* `torOnePullbackIso` — first derived group `Tor₁(R ⧸ (q-1), A) ≅ Ann_A(u-1)`;
* `tensorPullbackEquiv` — zeroth group `(R ⧸ (q-1)) ⊗_R A ≅ A ⧸ (u-1)`;
* `isZero_torPullback_add_two` — nothing above degree one.

At a field point both groups are the field when `u = 1` and vanish otherwise:

* `ker_smul_field_eq_bot`, `ker_smul_field_eq_top`,
* `span_sub_one_eq_top`, `span_sub_one_eq_bot`,
* `derivedPullback_nontrivial_iff` — the derived pullback is nonzero exactly at the identity point.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory Limits Opposite TensorProduct

universe u

section KerSmulTransport

variable {R : Type u} [CommRing R] {M M' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] (t : R)

theorem map_ker_smul_id (e : M ≃ₗ[R] M') :
    Submodule.map (e : M →ₗ[R] M') (LinearMap.ker (t • LinearMap.id : M →ₗ[R] M))
      = LinearMap.ker (t • LinearMap.id : M' →ₗ[R] M') := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_smul, hx, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    have := congrArg e.symm hy
    rw [map_smul, map_zero] at this
    exact this

/-- Multiplication by `t` commutes with any isomorphism, so its kernels correspond. -/
noncomputable def kerSmulEquiv (e : M ≃ₗ[R] M') :
    ↥(LinearMap.ker (t • LinearMap.id : M →ₗ[R] M)) ≃ₗ[R]
      ↥(LinearMap.ker (t • LinearMap.id : M' →ₗ[R] M')) :=
  (e.submoduleMap _).trans (LinearEquiv.ofEq _ _ (map_ker_smul_id t e))

end KerSmulTransport

section Pullback

variable {R : Type u} [CommRing R] {q : R} (A : Type u) [CommRing A] [Algebra R A]

/-- On an `R`-algebra, multiplication by `q - 1` is multiplication by `u - 1`. -/
theorem mem_ker_smul_algebra_iff (a : A) :
    a ∈ LinearMap.ker ((q - 1) • LinearMap.id : A →ₗ[R] A)
      ↔ (algebraMap R A q - 1) * a = 0 := by
  rw [LinearMap.mem_ker]
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  rw [Algebra.smul_def, map_sub, map_one]

theorem smul_ideal_eq_span :
    (Ideal.span {q - 1} : Ideal R) • (⊤ : Submodule R A)
      = (Ideal.span {algebraMap R A q - 1} : Ideal A).restrictScalars R := by
  apply le_antisymm
  · refine Submodule.smul_le.2 fun r hr a _ => ?_
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.1 hr
    rw [Submodule.restrictScalars_mem, Algebra.smul_def, map_mul, map_sub, map_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hx
    have hsm : (q - 1) • a = (algebraMap R A q - 1) * a := by
      rw [Algebra.smul_def, map_sub, map_one]
    rw [← hsm]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/-- **Theorem 8A.1 (8A.2), degree zero.**  `(R ⧸ (q-1)) ⊗_R A ≅ A ⧸ (u-1)`. -/
noncomputable def tensorPullbackEquiv :
    ((R ⧸ (Ideal.span {q - 1} : Ideal R)) ⊗[R] A) ≃ₗ[R]
      (A ⧸ (Ideal.span {algebraMap R A q - 1} : Ideal A).restrictScalars R) :=
  (quotTensorEquivQuotSMul A (Ideal.span {q - 1})).trans
    (Submodule.quotEquivOfEq _ _ (smul_ideal_eq_span A))

variable (hreg : IsSMulRegular R (q - 1))
include hreg

/-- **Theorem 8A.1 (8A.2), degree minus one.**  `Tor₁(R ⧸ (q-1), A) ≅ Ann_A(u-1)`. -/
noncomputable def torOnePullbackIso :
    (((Tor' (ModuleCat.{u} R) 1).obj
        (ModuleCat.of R (R ⧸ (Ideal.span {q - 1} : Ideal R)))).obj (ModuleCat.of R A))
      ≅ ModuleCat.of R ↥(LinearMap.ker ((q - 1) • LinearMap.id : A →ₗ[R] A)) :=
  torOneSmulIso (range_smul_id_eq_span (q - 1)) hreg (ModuleCat.of R A) ≪≫
    (kerSmulEquiv (q - 1) (TensorProduct.lid R A)).toModuleIso

/-- **Theorem 8A.1, higher vanishing.**  The derived pullback is concentrated in degrees `-1` and
`0`. -/
theorem isZero_torPullback_add_two (n : ℕ) :
    IsZero ((((Tor' (ModuleCat.{u} R) (n + 2)).obj
      (ModuleCat.of R (R ⧸ (Ideal.span {q - 1} : Ideal R)))).obj (ModuleCat.of R A))) :=
  isZero_torSmul_add_two (range_smul_id_eq_span (q - 1)) hreg (ModuleCat.of R A) n

end Pullback

section FieldPoint

variable {R : Type u} [CommRing R] {q : R} (K : Type u) [Field K] [Algebra R K]

/-- Away from the identity point the derived fibre of the source line vanishes in degree `-1`. -/
theorem ker_smul_field_eq_bot (h : algebraMap R K q ≠ 1) :
    LinearMap.ker ((q - 1) • LinearMap.id : K →ₗ[R] K) = ⊥ := by
  refine eq_bot_iff.2 fun a ha => ?_
  rw [mem_ker_smul_algebra_iff] at ha
  rcases mul_eq_zero.1 ha with h0 | h0
  · exact absurd (by linear_combination h0) h
  · exact h0

/-- At the identity point the derived fibre of the source line is the whole residue field. -/
theorem ker_smul_field_eq_top (h : algebraMap R K q = 1) :
    LinearMap.ker ((q - 1) • LinearMap.id : K →ₗ[R] K) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  rw [mem_ker_smul_algebra_iff, h, sub_self, zero_mul]

/-- Away from the identity point the ordinary fibre of the source line vanishes. -/
theorem span_sub_one_eq_top (h : algebraMap R K q ≠ 1) :
    (Ideal.span {algebraMap R K q - 1} : Ideal K) = ⊤ :=
  Ideal.span_singleton_eq_top.2 (Ne.isUnit (sub_ne_zero.2 h))

/-- At the identity point the ordinary fibre of the source line is the whole residue field. -/
theorem span_sub_one_eq_bot (h : algebraMap R K q = 1) :
    (Ideal.span {algebraMap R K q - 1} : Ideal K) = ⊥ := by
  rw [h, sub_self, Ideal.span_singleton_eq_bot]

/-- **Theorem 8A.1, field points.**  The derived pullback of the source orientation line is
nonzero exactly at the identity point of the monodromy line. -/
theorem derivedPullback_nontrivial_iff :
    LinearMap.ker ((q - 1) • LinearMap.id : K →ₗ[R] K) ≠ ⊥ ↔ algebraMap R K q = 1 := by
  constructor
  · intro hne
    by_contra h
    exact hne (ker_smul_field_eq_bot K h)
  · intro h
    rw [ker_smul_field_eq_top K h]
    intro hc
    have h1 : (1 : K) ∈ (⊤ : Submodule R K) := Submodule.mem_top
    rw [hc, Submodule.mem_bot] at h1
    exact one_ne_zero h1

end FieldPoint

end GaloisForLFunctions.HTGeometry.DerivedSelection
