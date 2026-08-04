import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Range duality for an injective self-adjoint operator

For a bounded self-adjoint injective operator `D` on a Hilbert space, membership of `g` in the range
of `D` is equivalent to a boundary-observability inequality:

```text
g in range D   <->   exists C, |<g, h>| <= C ‖D h‖ for all h,
```

and when `g = D x` the least admissible constant is exactly `‖x‖`.  The range need not be closed; the
observability constant is precisely the information that the unbounded preimage carries.

* `ObservableBy`, `observableBy_of_mem_range`, `mem_range_of_observableBy`,
  `observableBy_iff_mem_range` — equations `(1)`–`(5)`.  The hard direction goes through the linear
  equivalence `H ≃ range D` supplied by injectivity, Hahn–Banach extension, and Riesz representation;
  no closedness or compactness of `D` is used.
* `norm_le_of_observable_bound`, `observable_bound_norm` — the norm identity: `‖x‖` is admissible and
  every admissible constant dominates it.  The lower bound is where density of the range enters, via
  the corpus lemma `denseRange_of_isSelfAdjoint_of_injective`.
* `setOf_observableBy_eq_range` — the admissible set is a submodule, which is the abstract form of the
  statement that the admissible trace space is linear.
* `inner_sandwich_adjoint` — the sandwich identity `<Q R P f, h> = <f, P R Q h>` for self-adjoint
  factors, which is what turns an exterior forcing into an interior pairing.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The observability predicate: the pairing against `g` is controlled by `‖D h‖`. -/
def ObservableBy (D : H →L[𝕜] H) (g : H) : Prop :=
  ∃ C : ℝ, ∀ h : H, ‖(inner 𝕜 g h : 𝕜)‖ ≤ C * ‖D h‖

/-! ## The easy direction -/

theorem inner_isSelfAdjoint_left {D : H →L[𝕜] H} (hsa : IsSelfAdjoint D) (x y : H) :
    (inner 𝕜 (D x) y : 𝕜) = inner 𝕜 x (D y) := by
  have hD : ContinuousLinearMap.adjoint D = D := hsa
  have hkey := ContinuousLinearMap.adjoint_inner_left D y x
  rw [hD] at hkey
  exact hkey

/-- **Equation (3).**  A preimage supplies its own norm as an observability constant. -/
theorem observableBy_of_mem_range {D : H →L[𝕜] H} (hsa : IsSelfAdjoint D) (x : H) :
    ObservableBy D (D x) := by
  refine ⟨‖x‖, fun h => ?_⟩
  rw [inner_isSelfAdjoint_left hsa]
  exact norm_inner_le_norm x (D h)

/-! ## The hard direction -/

/-- **Equations (4)–(5).**  An observable vector lies in the range.  The functional
`D h ↦ <g, h>` is well defined by injectivity, bounded by the observability constant, extended by
Hahn–Banach and represented by Riesz. -/
theorem mem_range_of_observableBy {D : H →L[𝕜] H} (hsa : IsSelfAdjoint D)
    (hinj : Function.Injective D) {g : H} (hg : ObservableBy D g) :
    ∃ x : H, g = D x := by
  obtain ⟨C, hC⟩ := hg
  -- the linear equivalence with the (possibly nonclosed) range
  set e : H ≃ₗ[𝕜] LinearMap.range (D : H →ₗ[𝕜] H) :=
    LinearEquiv.ofInjective (D : H →ₗ[𝕜] H) hinj with he
  have heval : ∀ y : LinearMap.range (D : H →ₗ[𝕜] H), D (e.symm y) = (y : H) := by
    intro y
    have := e.apply_symm_apply y
    exact congrArg (fun z : LinearMap.range (D : H →ₗ[𝕜] H) => (z : H)) this
  -- the functional on the range
  set φ₀ : LinearMap.range (D : H →ₗ[𝕜] H) →ₗ[𝕜] 𝕜 :=
    { toFun := fun y => inner 𝕜 g (e.symm y)
      map_add' := by
        intro y z
        rw [map_add, inner_add_right]
      map_smul' := by
        intro c y
        rw [map_smul, inner_smul_right]
        rfl } with hφ₀
  have hbound : ∀ y : LinearMap.range (D : H →ₗ[𝕜] H), ‖φ₀ y‖ ≤ C * ‖y‖ := by
    intro y
    have h1 : ‖(inner 𝕜 g (e.symm y) : 𝕜)‖ ≤ C * ‖D (e.symm y)‖ := hC (e.symm y)
    rw [heval y] at h1
    exact h1
  set φ : LinearMap.range (D : H →ₗ[𝕜] H) →L[𝕜] 𝕜 := φ₀.mkContinuous C hbound with hφ
  obtain ⟨ψ, hψ, -⟩ := exists_extension_norm_eq (LinearMap.range (D : H →ₗ[𝕜] H)) φ
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm ψ, ?_⟩
  have hrep : ∀ y : H, (inner 𝕜 ((InnerProductSpace.toDual 𝕜 H).symm ψ) y : 𝕜) = ψ y := by
    intro y
    have := (InnerProductSpace.toDual 𝕜 H).apply_symm_apply ψ
    exact congrArg (fun L : StrongDual 𝕜 H => L y) this
  refine ext_inner_right 𝕜 fun h => ?_
  have hmem : (D h) ∈ LinearMap.range (D : H →ₗ[𝕜] H) := ⟨h, rfl⟩
  have hφval : φ ⟨D h, hmem⟩ = (inner 𝕜 g h : 𝕜) := by
    have hsymm : e.symm ⟨D h, hmem⟩ = h := by
      have : e h = ⟨D h, hmem⟩ := rfl
      rw [← this, e.symm_apply_apply]
    rw [hφ, LinearMap.mkContinuous_apply, hφ₀]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [hsymm]
  have hψval : ψ (D h) = (inner 𝕜 g h : 𝕜) := by
    rw [← hφval]
    exact hψ ⟨D h, hmem⟩
  rw [inner_isSelfAdjoint_left hsa, hrep, hψval]

/-- **Equations (1)–(2).**  The dual characterisation of the range. -/
theorem observableBy_iff_mem_range {D : H →L[𝕜] H} (hsa : IsSelfAdjoint D)
    (hinj : Function.Injective D) (g : H) :
    ObservableBy D g ↔ ∃ x : H, g = D x := by
  refine ⟨mem_range_of_observableBy hsa hinj, ?_⟩
  rintro ⟨x, rfl⟩
  exact observableBy_of_mem_range hsa x

/-- The admissible set is exactly the range, hence a submodule.  This is the abstract content of the
statement that the admissible characteristic trace space is linear. -/
theorem setOf_observableBy_eq_range {D : H →L[𝕜] H} (hsa : IsSelfAdjoint D)
    (hinj : Function.Injective D) :
    {g : H | ObservableBy D g} = (LinearMap.range (D : H →ₗ[𝕜] H) : Set H) := by
  ext g
  rw [Set.mem_setOf_eq, observableBy_iff_mem_range hsa hinj]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩

/-! ## The norm identity -/

/-- **Equation (10), lower half.**  Every observability constant for `D x` dominates `‖x‖`.  Density
of the range is exactly what upgrades the inequality from the range to the whole space. -/
theorem norm_le_of_observable_bound {D : H →L[𝕜] H} (hsa : IsSelfAdjoint D)
    (hinj : Function.Injective D) {x : H} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ h : H, ‖(inner 𝕜 (D x) h : 𝕜)‖ ≤ C * ‖D h‖) : ‖x‖ ≤ C := by
  have hclosed : IsClosed {y : H | ‖(inner 𝕜 x y : 𝕜)‖ ≤ C * ‖y‖} := by
    refine isClosed_le ?_ ?_ <;> fun_prop
  have hsub : Set.range (D : H → H) ⊆ {y : H | ‖(inner 𝕜 x y : 𝕜)‖ ≤ C * ‖y‖} := by
    rintro y ⟨w, rfl⟩
    have h1 := h w
    rw [inner_isSelfAdjoint_left hsa] at h1
    exact h1
  have hdense := denseRange_of_isSelfAdjoint_of_injective hsa hinj
  have hall : ∀ y : H, ‖(inner 𝕜 x y : 𝕜)‖ ≤ C * ‖y‖ := by
    intro y
    have hmem : y ∈ closure (Set.range (D : H → H)) := by
      rw [hdense.closure_range]
      exact Set.mem_univ y
    exact (hclosed.closure_subset_iff.mpr hsub) hmem
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · rw [← hx]
    exact hC
  · have hself := hall x
    have hre : RCLike.re (inner 𝕜 x x : 𝕜) ≤ ‖(inner 𝕜 x x : 𝕜)‖ := RCLike.re_le_norm _
    rw [inner_self_eq_norm_mul_norm] at hre
    exact le_of_mul_le_mul_right (by linarith [hself, hre]) hx

/-- **Equation (10).**  `‖x‖` is admissible, and it is the least admissible constant. -/
theorem observable_bound_norm {D : H →L[𝕜] H} (hsa : IsSelfAdjoint D)
    (hinj : Function.Injective D) (x : H) :
    (∀ h : H, ‖(inner 𝕜 (D x) h : 𝕜)‖ ≤ ‖x‖ * ‖D h‖)
      ∧ ∀ C : ℝ, 0 ≤ C → (∀ h : H, ‖(inner 𝕜 (D x) h : 𝕜)‖ ≤ C * ‖D h‖) → ‖x‖ ≤ C := by
  refine ⟨fun h => ?_, fun C hC hbd => norm_le_of_observable_bound hsa hinj hC hbd⟩
  rw [inner_isSelfAdjoint_left hsa]
  exact norm_inner_le_norm x (D h)

/-! ## The sandwich identity -/

/-- **Equation (11).**  A self-adjoint sandwich moves across the pairing in reversed order.  This is
what turns the exterior forcing `-1_E R 1_I f` into the interior pairing `-<f, 1_I R 1_E h>`. -/
theorem inner_sandwich_adjoint {P Q R : H →L[𝕜] H} (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hR : IsSelfAdjoint R) (f h : H) :
    (inner 𝕜 (Q (R (P f))) h : 𝕜) = inner 𝕜 f (P (R (Q h))) := by
  rw [inner_isSelfAdjoint_left hQ, inner_isSelfAdjoint_left hR, inner_isSelfAdjoint_left hP]

end GaloisForLFunctions.HTGeometry

end
