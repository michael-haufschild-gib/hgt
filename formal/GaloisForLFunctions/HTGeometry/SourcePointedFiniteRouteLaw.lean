import GaloisForLFunctions.HTGeometry.SourcePointedConservativityChainLaw

/-!
# The finite serial route law

The two-stage chain law says a composite is conservative on a source sector exactly when the first
stage is conservative there and the second is conservative on the propagated sector.  Iterating it
along a finite route gives the audit statement: a serial route is conservative on its initial source
sector exactly when every one of its edges is conservative on the sector propagated to that edge.

Quantitatively, uniform lower bounds multiply: a route whose `i`-th edge has source-relative lower
bound `c i` has lower bound `∏ c i` on the whole route.  So a route can be injective at every finite
stage while its inverse conditioning degrades, and the audit is the first edge whose kernel meets the
propagated sector.

* `routeComp`, `routeSector` : the composite of the first `m` edges and the sector propagated to
  stage `m`.
* `isConservativeOn_routeComp_iff` : the finite serial route law.
* `norm_routeComp_lower` : uniform lower bounds multiply along the route.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Algebraic

variable {R : Type*} [CommRing R] {M : ℕ → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The composite of the first `m` edges of a serial route. -/
def routeComp (T : ∀ i, M i →ₗ[R] M (i + 1)) : ∀ m : ℕ, M 0 →ₗ[R] M m
  | 0 => LinearMap.id
  | m + 1 => (T m).comp (routeComp T m)

@[simp]
theorem routeComp_zero (T : ∀ i, M i →ₗ[R] M (i + 1)) :
    routeComp T 0 = LinearMap.id := rfl

@[simp]
theorem routeComp_succ (T : ∀ i, M i →ₗ[R] M (i + 1)) (m : ℕ) :
    routeComp T (m + 1) = (T m).comp (routeComp T m) := rfl

/-- The source sector propagated to stage `m` of the route. -/
def routeSector (T : ∀ i, M i →ₗ[R] M (i + 1)) (S : Submodule R (M 0)) :
    ∀ m : ℕ, Submodule R (M m)
  | 0 => S
  | m + 1 => (routeSector T S m).map (T m)

@[simp]
theorem routeSector_zero (T : ∀ i, M i →ₗ[R] M (i + 1)) (S : Submodule R (M 0)) :
    routeSector T S 0 = S := rfl

@[simp]
theorem routeSector_succ (T : ∀ i, M i →ₗ[R] M (i + 1)) (S : Submodule R (M 0)) (m : ℕ) :
    routeSector T S (m + 1) = (routeSector T S m).map (T m) := rfl

/-- **Propagating the sector is mapping it along the composite.** -/
theorem routeSector_eq_map (T : ∀ i, M i →ₗ[R] M (i + 1)) (S : Submodule R (M 0)) :
    ∀ m : ℕ, routeSector T S m = S.map (routeComp T m)
  | 0 => by rw [routeSector_zero, routeComp_zero, Submodule.map_id]
  | m + 1 => by
    rw [routeSector_succ, routeComp_succ, Submodule.map_comp, routeSector_eq_map T S m]

/-- The identity loses no information on any sector. -/
theorem isConservativeOn_id (S : Submodule R (M 0)) :
    IsConservativeOn (LinearMap.id : M 0 →ₗ[R] M 0) S := by
  simp only [IsConservativeOn, LinearMap.ker_id]
  exact disjoint_bot_right

/-- **The finite serial route law.**  A route is conservative on its initial source sector exactly
when every edge is conservative on the sector propagated to that edge.  So a serial route has a
unique logical audit: propagate the actual source sector and find the first edge whose kernel meets
it; no later reader can restore what that edge destroyed. -/
theorem isConservativeOn_routeComp_iff (T : ∀ i, M i →ₗ[R] M (i + 1))
    (S : Submodule R (M 0)) :
    ∀ m : ℕ, IsConservativeOn (routeComp T m) S ↔
      ∀ i, i < m → IsConservativeOn (T i) (routeSector T S i)
  | 0 => by
    constructor
    · intro _ i hi
      exact absurd hi (Nat.not_lt_zero i)
    · intro _
      rw [routeComp_zero]
      exact isConservativeOn_id S
  | m + 1 => by
    rw [routeComp_succ, isConservativeOn_comp_iff, ← routeSector_eq_map,
      isConservativeOn_routeComp_iff T S m]
    constructor
    · rintro ⟨hlt, hm⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact hlt i h
      · subst h
        exact hm
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h m (Nat.lt_succ_self m)⟩

/-- **Failure at one edge is failure of the route.**  Once an edge kills a source vector, no
continuation restores it. -/
theorem not_isConservativeOn_routeComp_of_edge (T : ∀ i, M i →ₗ[R] M (i + 1))
    (S : Submodule R (M 0)) {m i : ℕ} (hi : i < m)
    (hfail : ¬ IsConservativeOn (T i) (routeSector T S i)) :
    ¬ IsConservativeOn (routeComp T m) S := by
  intro h
  exact hfail ((isConservativeOn_routeComp_iff T S m).1 h i hi)

end Algebraic

section Quantitative

variable {K : Type*} [NormedField K] {M : ℕ → Type*}
  [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace K (M i)]

/-- **Uniform lower bounds multiply along a route.**  A route whose `i`-th edge is bounded below by
`c i` on the propagated sector is bounded below by the product of the `c i` on the source sector.
Every finite stage may be injective while the product tends to zero, which is exactly the failure of
stable separation along a cofinal family. -/
theorem norm_routeComp_lower (T : ∀ i, M i →ₗ[K] M (i + 1)) (S : Submodule K (M 0))
    (c : ℕ → ℝ) (hbound : ∀ i, ∀ x ∈ routeSector T S i, c i * ‖x‖ ≤ ‖T i x‖)
    (hc : ∀ i, 0 ≤ c i) :
    ∀ (m : ℕ), ∀ x ∈ S, (∏ i ∈ Finset.range m, c i) * ‖x‖ ≤ ‖routeComp T m x‖
  | 0, x, _ => by
    rw [Finset.prod_range_zero, one_mul, routeComp_zero]
    exact le_of_eq rfl
  | m + 1, x, hx => by
    have hprev := norm_routeComp_lower T S c hbound hc m x hx
    have hmem : routeComp T m x ∈ routeSector T S m := by
      rw [routeSector_eq_map]
      exact ⟨x, hx, rfl⟩
    have hstep := hbound m (routeComp T m x) hmem
    have hcm : 0 ≤ c m := hc m
    calc (∏ i ∈ Finset.range (m + 1), c i) * ‖x‖
        = c m * ((∏ i ∈ Finset.range m, c i) * ‖x‖) := by
          rw [Finset.prod_range_succ]
          ring
      _ ≤ c m * ‖routeComp T m x‖ := mul_le_mul_of_nonneg_left hprev hcm
      _ ≤ ‖T m (routeComp T m x)‖ := hstep
      _ = ‖routeComp T (m + 1) x‖ := rfl

/-- **The route is uniformly conservative when every edge is**, with a positive product bound. -/
theorem isUniformlyConservativeOn_routeComp (T : ∀ i, M i →ₗ[K] M (i + 1))
    (S : Submodule K (M 0)) (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hbound : ∀ i, ∀ x ∈ routeSector T S i, c i * ‖x‖ ≤ ‖T i x‖) (m : ℕ) :
    IsUniformlyConservativeOn (routeComp T m) S :=
  ⟨∏ i ∈ Finset.range m, c i, Finset.prod_pos fun i _ => hc i,
    norm_routeComp_lower T S c hbound (fun i => le_of_lt (hc i)) m⟩

end Quantitative

end

end GaloisForLFunctions.HTGeometry
