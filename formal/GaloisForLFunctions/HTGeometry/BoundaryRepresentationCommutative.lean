import GaloisForLFunctions.HTGeometry.PureStatesContinuousFunctions

/-!
# Boundary representations in the commutative model

Arveson calls a representation a *boundary representation* when its restriction to the system has a
unique extension.  In the commutative model the irreducible representations are the point
evaluations, so the question becomes: for which `x` is `δₓ` the only state of `C(X, ℂ)` agreeing
with `δₓ` on `S`?

The answer is the Choquet boundary, and both directions are consequences of the extreme-state
description of `C(X, ℂ)`:

* if `δₓ` extends uniquely, lift a convex decomposition of `δₓ|S` through the restriction map — the
  lift decomposes `δₓ` itself, which is extreme, so the decomposition was trivial;
* if `δₓ|S` is extreme, the fibre of the restriction map over it is an *extreme subset* of the
  state body, so its own extreme points are extreme states, hence point evaluations agreeing with
  `x` on `S`, hence `x` itself; Krein–Milman then collapses the fibre to a point.

Separation of points is used only for the second direction, and no other hypothesis on `S` appears.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Restriction of a functional on `C(X, ℂ)` to a subsystem. -/
def resMap (S : Submodule ℂ C(X, ℂ)) (Φ : ↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ) : ↥S → ℂ :=
  fun s => Φ ⟨(s : C(X, ℂ)), Submodule.mem_top⟩

omit [CompactSpace X] [T2Space X] in
@[simp]
theorem resMap_evalPoint (S : Submodule ℂ C(X, ℂ)) (y : X) :
    resMap S (evalPoint (⊤ : Submodule ℂ C(X, ℂ)) y) = evalPoint S y := rfl

omit [CompactSpace X] [T2Space X] in
theorem continuous_resMap (S : Submodule ℂ C(X, ℂ)) : Continuous (resMap S) :=
  continuous_pi fun _ => continuous_apply _

omit [CompactSpace X] [T2Space X] in
theorem isLinear_resMap (S : Submodule ℂ C(X, ℂ)) : IsLinearMap ℝ (resMap S) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

omit [T2Space X] in
/-- The restriction map carries the state body of `C(X, ℂ)` onto the state body of `S`. -/
theorem image_stateBody (S : Submodule ℂ C(X, ℂ)) :
    resMap S '' stateBody (⊤ : Submodule ℂ C(X, ℂ)) = stateBody S := by
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.image_subset_iff.mpr ?_
    refine stateBody_subset_of_isClosed_convex
      (IsClosed.preimage (continuous_resMap S) (isCompact_stateBody S).isClosed) ?_ ?_
    · exact (convex_stateBody S).is_linear_preimage (isLinear_resMap S)
    · intro y
      simpa using range_evalPoint_subset_stateBody S ⟨y, rfl⟩
  · refine closure_minimal (convexHull_min ?_ ?_) ?_
    · rintro _ ⟨y, rfl⟩
      exact ⟨evalPoint (⊤ : Submodule ℂ C(X, ℂ)) y,
        range_evalPoint_subset_stateBody _ ⟨y, rfl⟩, rfl⟩
    · exact (convex_stateBody _).is_linear_image (isLinear_resMap S)
    · exact ((isCompact_stateBody _).image (continuous_resMap S)).isClosed

/-- The states of `C(X, ℂ)` restricting to the evaluation at `x` on `S`. -/
def extensionFibre (S : Submodule ℂ C(X, ℂ)) (x : X) : Set (↥(⊤ : Submodule ℂ C(X, ℂ)) → ℂ) :=
  {Φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ)) | resMap S Φ = evalPoint S x}

omit [CompactSpace X] [T2Space X] in
theorem evalPoint_mem_extensionFibre (S : Submodule ℂ C(X, ℂ)) (x : X) :
    evalPoint (⊤ : Submodule ℂ C(X, ℂ)) x ∈ extensionFibre S x :=
  ⟨range_evalPoint_subset_stateBody _ ⟨x, rfl⟩, rfl⟩

omit [CompactSpace X] [T2Space X] in
theorem convex_extensionFibre (S : Submodule ℂ C(X, ℂ)) (x : X) :
    Convex ℝ (extensionFibre S x) := by
  intro Φ hΦ Ψ hΨ a b ha hb hab
  refine ⟨(convex_stateBody _) hΦ.1 hΨ.1 ha hb hab, ?_⟩
  have h1 : resMap S (a • Φ + b • Ψ) = a • resMap S Φ + b • resMap S Ψ := by
    rw [(isLinear_resMap S).1, (isLinear_resMap S).2, (isLinear_resMap S).2]
  rw [h1, hΦ.2, hΨ.2]
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  rw [← add_mul, ← Complex.ofReal_add, hab, Complex.ofReal_one, one_mul]

omit [T2Space X] in
theorem isCompact_extensionFibre (S : Submodule ℂ C(X, ℂ)) (x : X) :
    IsCompact (extensionFibre S x) := by
  refine (isCompact_stateBody _).of_isClosed_subset ?_ fun _ h => h.1
  refine IsClosed.inter (isCompact_stateBody _).isClosed ?_
  exact isClosed_eq (continuous_resMap S) continuous_const

omit [T2Space X] in
/-- **The fibre is an extreme subset** whenever the evaluation is extreme on `S`. -/
theorem isExtreme_extensionFibre {S : Submodule ℂ C(X, ℂ)} {x : X}
    (hx : evalPoint S x ∈ (stateBody S).extremePoints ℝ) :
    IsExtreme ℝ (stateBody (⊤ : Submodule ℂ C(X, ℂ))) (extensionFibre S x) where
  subset := fun _ h => h.1
  left_mem_of_mem_openSegment := by
    rintro Φ hΦ Ψ hΨ Θ hΘ ⟨a, b, ha, hb, hab, hcomb⟩
    refine ⟨hΦ, ?_⟩
    have hres : resMap S Θ = a • resMap S Φ + b • resMap S Ψ := by
      rw [← hcomb, (isLinear_resMap S).1, (isLinear_resMap S).2, (isLinear_resMap S).2]
    have hseg : evalPoint S x ∈ openSegment ℝ (resMap S Φ) (resMap S Ψ) :=
      ⟨a, b, ha, hb, hab, by rw [← hres, hΘ.2]⟩
    have himΦ : resMap S Φ ∈ stateBody S := by
      rw [← image_stateBody S]
      exact ⟨Φ, hΦ, rfl⟩
    have himΨ : resMap S Ψ ∈ stateBody S := by
      rw [← image_stateBody S]
      exact ⟨Ψ, hΨ, rfl⟩
    exact hx.2 himΦ himΨ hseg

/-- **Boundary representations are the Choquet boundary.**  A point evaluation extends uniquely
from `S` to `C(X, ℂ)` exactly when the point lies in the Choquet boundary. -/
theorem mem_choquetBoundary_iff_uniqueExtension {S : Submodule ℂ C(X, ℂ)}
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y) (x : X) :
    x ∈ choquetBoundary S ↔
      ∀ Φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ)),
        (∀ s : C(X, ℂ), s ∈ S → topEval Φ s = s x) →
          Φ = evalPoint (⊤ : Submodule ℂ C(X, ℂ)) x := by
  constructor
  · -- the Choquet boundary gives uniqueness, via Krein–Milman on the fibre
    intro hx Φ hΦ hres
    have hfib : Φ ∈ extensionFibre S x := by
      refine ⟨hΦ, ?_⟩
      funext s
      exact hres (s : C(X, ℂ)) s.2
    have hext : IsExtreme ℝ (stateBody (⊤ : Submodule ℂ C(X, ℂ))) (extensionFibre S x) :=
      isExtreme_extensionFibre hx
    have hsingle : (extensionFibre S x).extremePoints ℝ
        ⊆ {evalPoint (⊤ : Submodule ℂ C(X, ℂ)) x} := by
      intro Ψ hΨ
      have hΨtop : Ψ ∈ (stateBody (⊤ : Submodule ℂ C(X, ℂ))).extremePoints ℝ :=
        hext.extremePoints_subset_extremePoints hΨ
      rw [extremePoints_stateBody_top] at hΨtop
      obtain ⟨y, rfl⟩ := hΨtop
      have hy : resMap S (evalPoint (⊤ : Submodule ℂ C(X, ℂ)) y) = evalPoint S x := hΨ.1.2
      rw [resMap_evalPoint] at hy
      by_cases hxy : y = x
      · rw [hxy]; rfl
      · obtain ⟨s, hs, hne⟩ := hsep y x hxy
        exact absurd (congrFun hy ⟨s, hs⟩) hne
    have hcollapse := closure_convexHull_extremePoints (isCompact_extensionFibre S x)
      (convex_extensionFibre S x)
    have hsub : extensionFibre S x ⊆ {evalPoint (⊤ : Submodule ℂ C(X, ℂ)) x} := by
      rw [← hcollapse]
      refine closure_minimal (convexHull_min hsingle (convex_singleton _)) isClosed_singleton
    exact hsub hfib
  · -- uniqueness gives extremality, by lifting a decomposition
    intro huniq
    refine ⟨range_evalPoint_subset_stateBody S ⟨x, rfl⟩, ?_⟩
    rintro φ hφ ψ hψ ⟨a, b, ha, hb, hab, hcomb⟩
    obtain ⟨Φ, hΦ, rfl⟩ : ∃ Φ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ)), resMap S Φ = φ := by
      rw [← image_stateBody S] at hφ
      obtain ⟨Φ, hΦ, hΦeq⟩ := hφ
      exact ⟨Φ, hΦ, hΦeq⟩
    obtain ⟨Ψ, hΨ, rfl⟩ : ∃ Ψ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ)), resMap S Ψ = ψ := by
      rw [← image_stateBody S] at hψ
      obtain ⟨Ψ, hΨ, hΨeq⟩ := hψ
      exact ⟨Ψ, hΨ, hΨeq⟩
    have hmix : a • Φ + b • Ψ ∈ stateBody (⊤ : Submodule ℂ C(X, ℂ)) :=
      (convex_stateBody _) hΦ hΨ ha.le hb.le hab
    have hmixres : ∀ s : C(X, ℂ), s ∈ S → topEval (a • Φ + b • Ψ) s = s x := by
      intro s hs
      have h1 : resMap S (a • Φ + b • Ψ) = a • resMap S Φ + b • resMap S Ψ := by
        rw [(isLinear_resMap S).1, (isLinear_resMap S).2, (isLinear_resMap S).2]
      have h2 := congrFun (h1.trans hcomb) ⟨s, hs⟩
      simpa [topEval, resMap] using h2
    have hmixeq := huniq _ hmix hmixres
    have hextop : evalPoint (⊤ : Submodule ℂ C(X, ℂ)) x
        ∈ (stateBody (⊤ : Submodule ℂ C(X, ℂ))).extremePoints ℝ :=
      evalPoint_mem_extremePoints_top x
    have hΦeq : Φ = evalPoint (⊤ : Submodule ℂ C(X, ℂ)) x :=
      hextop.2 hΦ hΨ ⟨a, b, ha, hb, hab, hmixeq⟩
    rw [hΦeq, resMap_evalPoint]

end ShilovLocal

end GaloisForLFunctions.HTGeometry
