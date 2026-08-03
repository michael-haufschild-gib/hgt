import GaloisForLFunctions.HTGeometry.SourcePointedObservationNetworkLaw

/-!
# Source-pointed exact descent law

An observation network has three logically independent requirements.  Conservativity gives
uniqueness of a source lift.  Exactness gives existence of a lift for every admissible compatible
datum.  A positive lower modulus gives stable recovery after completion.

This module packages all three requirements.  The central theorem says that source-pointed exact
descent is equivalent to unique gluing of every admissible compatible observation.  Thus a route
can fail only through source ambiguity, a compatibility class outside the observed range, or loss
of the quantitative lower modulus.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R E F G : Type*}
variable [CommRing R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup G] [Module R G]

/-- Exact descent relative to an actual source sector and an admissible observation sector.
Conservativity supplies uniqueness; equality of the observed source range with the compatible
admissible sector supplies existence. -/
def IsSourcePointedExactDescent
    (observe : E →ₗ[R] F) (compatibility : F →ₗ[R] G)
    (source : Submodule R E) (admissible : Submodule R F) : Prop :=
  IsConservativeOn observe source ∧
    source.map observe = admissible ⊓ LinearMap.ker compatibility

/-- Every admissible compatible datum has one and only one lift in the selected source sector. -/
theorem IsSourcePointedExactDescent.existsUnique_lift
    {observe : E →ₗ[R] F} {compatibility : F →ₗ[R] G}
    {source : Submodule R E} {admissible : Submodule R F}
    (h : IsSourcePointedExactDescent observe compatibility source admissible)
    {y : F} (hyA : y ∈ admissible) (hycompat : compatibility y = 0) :
    ∃! x : E, x ∈ source ∧ observe x = y := by
  have hy : y ∈ admissible ⊓ LinearMap.ker compatibility := ⟨hyA, hycompat⟩
  rw [← h.2] at hy
  rcases hy with ⟨x, hxsource, hxobs⟩
  refine ⟨x, ⟨hxsource, hxobs⟩, ?_⟩
  intro z hz
  have hsource : z - x ∈ source := source.sub_mem hz.1 hxsource
  have hkernel : z - x ∈ LinearMap.ker observe := by
    change observe (z - x) = 0
    rw [map_sub, hz.2, hxobs, sub_self]
  have hconservative := h.1
  rw [IsConservativeOn, Submodule.disjoint_def] at hconservative
  exact sub_eq_zero.mp (hconservative (z - x) hsource hkernel)

/-- **Source-pointed exact descent law.**  Exact descent is equivalent to the observation complex
containing the delivered source range and every admissible compatible datum having a unique source
lift. -/
theorem isSourcePointedExactDescent_iff_unique_compatible_lift
    (observe : E →ₗ[R] F) (compatibility : F →ₗ[R] G)
    (source : Submodule R E) (admissible : Submodule R F) :
    IsSourcePointedExactDescent observe compatibility source admissible ↔
      source.map observe ≤ admissible ⊓ LinearMap.ker compatibility ∧
      ∀ y, y ∈ admissible → compatibility y = 0 →
        ∃! x : E, x ∈ source ∧ observe x = y := by
  constructor
  · intro h
    exact ⟨h.2.le, fun _ hyA hycompat => h.existsUnique_lift hyA hycompat⟩
  · rintro ⟨hmap, hlift⟩
    constructor
    · rw [IsConservativeOn, Submodule.disjoint_def]
      intro x hxsource hxkernel
      have hzero := hlift 0 admissible.zero_mem (map_zero compatibility)
      exact hzero.unique ⟨hxsource, hxkernel⟩
        ⟨source.zero_mem, map_zero observe⟩
    · apply le_antisymm hmap
      intro y hy
      obtain ⟨x, hx, _⟩ := hlift y hy.1 hy.2
      exact ⟨x, hx.1, hx.2⟩

/-- Intrinsic form: a datum is admissible and compatible exactly when it has a unique source lift. -/
theorem IsSourcePointedExactDescent.compatible_iff_existsUnique_lift
    {observe : E →ₗ[R] F} {compatibility : F →ₗ[R] G}
    {source : Submodule R E} {admissible : Submodule R F}
    (h : IsSourcePointedExactDescent observe compatibility source admissible)
    (y : F) :
    (y ∈ admissible ∧ compatibility y = 0) ↔
      ∃! x : E, x ∈ source ∧ observe x = y := by
  constructor
  · rintro ⟨hyA, hycompat⟩
    exact h.existsUnique_lift hyA hycompat
  · rintro ⟨x, hx, _⟩
    have hy : y ∈ source.map observe := ⟨x, hx.1, hx.2⟩
    rw [h.2] at hy
    exact ⟨hy.1, hy.2⟩

/-! ## Stable descent -/

variable {K E₁ F₁ G₁ : Type*}
variable [NormedField K]
variable [NormedAddCommGroup E₁] [NormedSpace K E₁]
variable [NormedAddCommGroup F₁] [NormedSpace K F₁]
variable [AddCommGroup G₁] [Module K G₁]

/-- Stable exact descent adds a positive source-sector lower modulus to algebraic exact descent. -/
def IsStableSourcePointedExactDescent
    (observe : E₁ →ₗ[K] F₁) (compatibility : F₁ →ₗ[K] G₁)
    (source : Submodule K E₁) (admissible : Submodule K F₁) : Prop :=
  IsSourcePointedExactDescent observe compatibility source admissible ∧
    IsUniformlyConservativeOn observe source

/-- Stable exact descent gives unique compatible lifts with one common quantitative recovery
bound. -/
theorem IsStableSourcePointedExactDescent.existsUnique_lift_with_bound
    {observe : E₁ →ₗ[K] F₁} {compatibility : F₁ →ₗ[K] G₁}
    {source : Submodule K E₁} {admissible : Submodule K F₁}
    (h : IsStableSourcePointedExactDescent observe compatibility source admissible) :
    ∃ c : ℝ, 0 < c ∧ ∀ y, y ∈ admissible → compatibility y = 0 →
      ∃! x : E₁, x ∈ source ∧ observe x = y ∧ c * ‖x‖ ≤ ‖y‖ := by
  obtain ⟨c, hc, hbound⟩ := h.2
  refine ⟨c, hc, ?_⟩
  intro y hyA hycompat
  obtain ⟨x, hx, hxunique⟩ := h.1.existsUnique_lift hyA hycompat
  refine ⟨x, ⟨hx.1, hx.2, ?_⟩, ?_⟩
  · simpa [hx.2] using hbound x hx.1
  · intro z hz
    exact hxunique z ⟨hz.1, hz.2.1⟩

/-! ## Source-pointed conservative factorization -/

/-- A comparison need not identify two entire completed ranges in order to force one target point
to vanish.  It is enough that the comparison lands that point in a conservative source sector,
intertwines it into the zero observation fibre, and reflects zero on that point. -/
theorem eq_zero_of_sourcePointed_conservativeFactorization
    {X E₂ F₂ : Type*} [Zero X]
    [AddCommGroup E₂] [Module R E₂]
    [AddCommGroup F₂] [Module R F₂]
    (observe : E₂ →ₗ[R] F₂) (source : Submodule R E₂)
    (compare : X → E₂) {x : X}
    (hconservative : IsConservativeOn observe source)
    (hsource : compare x ∈ source)
    (hzero : observe (compare x) = 0)
    (hreflect : compare x = 0 → x = 0) :
    x = 0 := by
  apply hreflect
  rw [IsConservativeOn, Submodule.disjoint_def] at hconservative
  apply hconservative (compare x) hsource
  exact hzero

/-- Several source geometries need not be globally identified with one
another.  If each comparison lands the distinguished point in a conservative
zero fibre and their complete comparison record reflects zero, then the
point vanishes.  Individual comparisons may have nontrivial kernels; only
their intersection at the source point must be trivial. -/
theorem eq_zero_of_sourcePointed_parallelConservativeFactorizations
    {J X : Type*} [Zero X]
    {E₂ F₂ : J → Type*}
    [∀ j, AddCommGroup (E₂ j)] [∀ j, Module R (E₂ j)]
    [∀ j, AddCommGroup (F₂ j)] [∀ j, Module R (F₂ j)]
    (observe : ∀ j, E₂ j →ₗ[R] F₂ j)
    (source : ∀ j, Submodule R (E₂ j))
    (compare : ∀ j, X → E₂ j) {x : X}
    (hconservative : ∀ j, IsConservativeOn (observe j) (source j))
    (hsource : ∀ j, compare j x ∈ source j)
    (hzero : ∀ j, observe j (compare j x) = 0)
    (hreflect : (∀ j, compare j x = 0) → x = 0) :
    x = 0 := by
  apply hreflect
  intro j
  have hj := hconservative j
  rw [IsConservativeOn, Submodule.disjoint_def] at hj
  exact hj (compare j x) (hsource j) (hzero j)

end

end GaloisForLFunctions.HTGeometry
