import Mathlib

/-!
# Fredholm theory for unbounded operators

`LinearPMap` carries no kernel, range, or index in mathlib.  This module supplies them, together
with the criterion that identifies an index `-1` operator: injective, with range exactly the kernel
of one nonzero continuous functional.

* `LinearPMap.kernel`, `LinearPMap.rangeSubmodule` — the two invariant subspaces.
* `LinearPMap.IsFredholm` — finite-dimensional kernel, closed range, finite-dimensional cokernel.
* `LinearPMap.index` — the difference of those two dimensions.
* `LinearPMap.index_eq_neg_one_of_injective_of_range_eq_ker` — the criterion.
-/

open Module

namespace LinearPMap

variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The kernel of a partially defined linear map, as a subspace of the ambient source. -/
def kernel (T : E →ₗ.[𝕜] F) : Submodule 𝕜 E :=
  Submodule.map T.domain.subtype (LinearMap.ker T.toFun)

/-- The range of a partially defined linear map. -/
def rangeSubmodule (T : E →ₗ.[𝕜] F) : Submodule 𝕜 F :=
  LinearMap.range T.toFun

theorem mem_kernel_iff {T : E →ₗ.[𝕜] F} {x : E} :
    x ∈ T.kernel ↔ ∃ h : x ∈ T.domain, T ⟨x, h⟩ = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem mem_rangeSubmodule_iff {T : E →ₗ.[𝕜] F} {y : F} :
    y ∈ T.rangeSubmodule ↔ ∃ x : T.domain, T x = y :=
  Iff.rfl

theorem kernel_eq_bot_iff {T : E →ₗ.[𝕜] F} :
    T.kernel = ⊥ ↔ ∀ x : T.domain, T x = 0 → (x : E) = 0 := by
  rw [Submodule.eq_bot_iff]
  constructor
  · intro h x hx
    exact h _ (mem_kernel_iff.mpr ⟨x.2, by simpa using hx⟩)
  · intro h x hx
    obtain ⟨hmem, hzero⟩ := mem_kernel_iff.mp hx
    exact h ⟨x, hmem⟩ hzero

section Topology

variable [TopologicalSpace F]

/-- A partially defined operator is Fredholm when its kernel is finite-dimensional, its range is
closed, and its cokernel is finite-dimensional. -/
structure IsFredholm (T : E →ₗ.[𝕜] F) : Prop where
  finiteDimensional_kernel : FiniteDimensional 𝕜 T.kernel
  isClosed_range : _root_.IsClosed (T.rangeSubmodule : Set F)
  finiteDimensional_cokernel : FiniteDimensional 𝕜 (F ⧸ T.rangeSubmodule)

end Topology

/-- The Fredholm index: kernel dimension minus cokernel dimension. -/
noncomputable def index (T : E →ₗ.[𝕜] F) : ℤ :=
  (finrank 𝕜 T.kernel : ℤ) - (finrank 𝕜 (F ⧸ T.rangeSubmodule) : ℤ)

theorem index_eq (T : E →ₗ.[𝕜] F) :
    T.index = (finrank 𝕜 T.kernel : ℤ) - (finrank 𝕜 (F ⧸ T.rangeSubmodule) : ℤ) := rfl

/-- **The cokernel of a hyperplane range is one-dimensional.**  If the range is exactly the kernel
of a surjective scalar functional, the quotient is a line. -/
theorem finrank_quotient_eq_one_of_eq_ker {T : E →ₗ.[𝕜] F} {φ : F →ₗ[𝕜] 𝕜}
    (hφ : Function.Surjective φ) (hrange : T.rangeSubmodule = LinearMap.ker φ) :
    finrank 𝕜 (F ⧸ T.rangeSubmodule) = 1 := by
  rw [hrange]
  have e : (F ⧸ LinearMap.ker φ) ≃ₗ[𝕜] 𝕜 := φ.quotKerEquivOfSurjective hφ
  rw [e.finrank_eq, finrank_self]

/-- **The index `-1` criterion.**  An injective partially defined operator whose range is exactly
the kernel of a surjective scalar functional has index `-1`. -/
theorem index_eq_neg_one_of_injective_of_range_eq_ker {T : E →ₗ.[𝕜] F} {φ : F →ₗ[𝕜] 𝕜}
    (hker : T.kernel = ⊥) (hφ : Function.Surjective φ)
    (hrange : T.rangeSubmodule = LinearMap.ker φ) :
    T.index = -1 := by
  rw [index_eq, hker, finrank_quotient_eq_one_of_eq_ker hφ hrange]
  simp

/-- **The Fredholm property from a hyperplane range.**  Injectivity, a continuous functional and the
range identification give the whole package. -/
theorem isFredholm_of_injective_of_range_eq_ker [TopologicalSpace 𝕜] [TopologicalSpace F]
    [T1Space 𝕜] {T : E →ₗ.[𝕜] F} {φ : F →ₗ[𝕜] 𝕜} (hcont : Continuous φ)
    (hker : T.kernel = ⊥) (hφ : Function.Surjective φ)
    (hrange : T.rangeSubmodule = LinearMap.ker φ) :
    T.IsFredholm where
  finiteDimensional_kernel := by
    rw [hker]
    infer_instance
  isClosed_range := by
    rw [hrange]
    have hset : ((LinearMap.ker φ : Submodule 𝕜 F) : Set F) = φ ⁻¹' {0} := rfl
    rw [hset]
    exact (isClosed_singleton (x := (0 : 𝕜))).preimage hcont
  finiteDimensional_cokernel :=
    ((Submodule.quotEquivOfEq _ _ hrange).trans
      (φ.quotKerEquivOfSurjective hφ)).symm.finiteDimensional

end LinearPMap
