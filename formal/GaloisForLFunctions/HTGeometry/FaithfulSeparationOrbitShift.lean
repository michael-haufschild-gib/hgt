import GaloisForLFunctions.HTGeometry.FacetOrbitShift
import GaloisForLFunctions.HTGeometry.TranscendentalPowerIndependence

/-!
# The compressed facet-orbit shift of a faithful facet separation

A faithful facet separation in dimension `d` supplies vectors `a_v` and facet forms `ℓ_A` whose
complete numerical content is the value matrix

```
x_{A,v} = ℓ_A (a_v),      x_{A,v} = 0 ↔ v ∉ A,
```

with `{x_{A,v} : v ∈ A}` rationally independent for every facet `A`.  Restricting the compressed
system to an affine line in the direction of a form-generic vector turns the structural translate
`T^n Y_A` into the single scalar shift

```
γ_A + ∑_{v ∈ A} n_v x_{A,v},
```

so the whole compressed realization is controlled by one scalar shift palette.  Unlike the
universal one-coordinate-per-facet palette, this one is *not* injective on the full lattice: a
translation attached to a vertex outside `A` does not move `Y_A`.  It is injective exactly on the
facet slice, which is where the Laurent operator rows live.

Separation across facets costs one real parameter: taking `γ_A = t · tag(A)` for a single `t`
outside an explicit countable collision set already makes distinct facet families disjoint.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- Numerical content of a faithful facet separation: the facet-form values on the separation
vectors.  The zero pattern is the exact facet complement and the nonzero values of each facet are
rationally independent. -/
structure FacetSeparationValues (α : Type*) (facets : Finset (Finset α)) where
  /-- `value F v = ℓ_F (a_v)`. -/
  value : facets → α → ℂ
  /-- Condition 2: the zero set of a facet form is exactly the facet complement. -/
  zero_iff : ∀ (F : facets) (v : α), value F v = 0 ↔ v ∉ F.1
  /-- Condition 3: distinct Laurent monomials inside a facet induce distinct translates. -/
  facet_independent : ∀ F : facets, LinearIndependent ℚ (fun v : F.1 => value F v)

namespace FacetSeparationValues

variable {α : Type*} [Fintype α] {facets : Finset (Finset α)}

/-- The value matrix produced by faithful separation data in an arbitrary complex vector space. -/
def ofSeparation {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a : α → E) (ℓ : facets → (E →ₗ[ℂ] ℂ))
    (hzero : ∀ (F : facets) (v : α), ℓ F (a v) = 0 ↔ v ∉ F.1)
    (hindep : ∀ F : facets, LinearIndependent ℚ (fun v : F.1 => ℓ F (a v))) :
    FacetSeparationValues α facets where
  value F v := ℓ F (a v)
  zero_iff := hzero
  facet_independent := hindep

/-- **Every finite facet family has faithful separation values.**  Distinct transcendental powers
placed at the facet-incident vertices realize the exact facet-complement zero pattern with
rationally independent facet values. -/
def ofTranscendental [DecidableEq α] (facets : Finset (Finset α)) {τ : ℂ}
    (hτ : Transcendental ℚ τ) : FacetSeparationValues α facets where
  value F v := if v ∈ F.1 then τ ^ ((Fintype.equivFin α v : ℕ)) else 0
  zero_iff F v := by
    have hτne : τ ≠ 0 := fun h => hτ (h.symm ▸ isAlgebraic_zero)
    by_cases hv : v ∈ F.1
    · simp [hv, pow_ne_zero _ hτne]
    · simp [hv]
  facet_independent F := by
    have hfam : (fun v : F.1 => if v.1 ∈ F.1 then
          τ ^ ((Fintype.equivFin α v.1 : ℕ)) else 0) =
        fun v : F.1 => τ ^ ((Fintype.equivFin α v.1 : ℕ)) := by
      funext v
      simp [v.2]
    rw [hfam]
    refine transcendental_pow_comp_linearIndependent hτ ?_
    intro x y hxy
    exact Subtype.ext ((Fintype.equivFin α).injective (Fin.ext hxy))

/-- Structural orbit shift of one facet: the compressed translate parameter. -/
def orbitSum (S : FacetSeparationValues α facets) (F : facets) (n : α → ℤ) : ℂ :=
  ∑ v, (n v : ℂ) * S.value F v

/-- Vertices outside a facet do not contribute to that facet's orbit shift. -/
theorem orbitSum_eq_sum_facet (S : FacetSeparationValues α facets)
    (F : facets) (n : α → ℤ) :
    S.orbitSum F n = ∑ v ∈ F.1, (n v : ℂ) * S.value F v := by
  classical
  refine (Finset.sum_subset (Finset.subset_univ F.1) ?_).symm
  intro v _ hv
  rw [(S.zero_iff F v).2 hv, mul_zero]

/-- **Within one facet the orbit shift separates the slice.**  Rational independence of the facet
values makes distinct integer exponent vectors supported in the facet give distinct shifts. -/
theorem orbitSum_injOn_slice (S : FacetSeparationValues α facets)
    (F : facets) {n m : α → ℤ}
    (hn : ∀ v, v ∉ F.1 → n v = 0) (hm : ∀ v, v ∉ F.1 → m v = 0)
    (h : S.orbitSum F n = S.orbitSum F m) : n = m := by
  classical
  have hsum : ∑ v : F.1, ((n v.1 - m v.1 : ℤ) : ℚ) • S.value F v.1 = 0 := by
    have hfacet : ∑ v ∈ F.1, ((n v : ℂ) - (m v : ℂ)) * S.value F v = 0 := by
      rw [Finset.sum_congr rfl fun v _ => sub_mul (n v : ℂ) (m v : ℂ) (S.value F v),
        Finset.sum_sub_distrib, ← orbitSum_eq_sum_facet, ← orbitSum_eq_sum_facet, h, sub_self]
    rw [← Finset.sum_coe_sort F.1
      (fun v => ((n v : ℂ) - (m v : ℂ)) * S.value F v)] at hfacet
    rw [← hfacet]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Rat.smul_def]
    push_cast
    ring
  have hzero := Fintype.linearIndependent_iff.1 (S.facet_independent F)
    (fun v => ((n v.1 - m v.1 : ℤ) : ℚ)) hsum
  funext v
  by_cases hv : v ∈ F.1
  · have := hzero ⟨v, hv⟩
    have hint : (n v - m v : ℤ) = 0 := by exact_mod_cast this
    omega
  · rw [hn v hv, hm v hv]

/-- Compressed facet-orbit shift palette with a single cross-facet separation parameter. -/
def orbitShift (S : FacetSeparationValues α facets) (t : ℂ) :
    facets × (α → ℤ) → ℂ :=
  fun q => t * (facetTag facets q.1 : ℂ) + S.orbitSum q.1 q.2

/-- The facet slice: exponent vectors supported inside their own facet.  This is exactly the index
set carried by the Laurent operator rows. -/
def FacetSlice (α : Type*) (facets : Finset (Finset α)) :
    Set (facets × (α → ℤ)) :=
  {q | ∀ v, v ∉ q.1.1 → q.2 v = 0}

/-- Cross-facet collisions of the compressed palette, as a countable set of forbidden separation
parameters. -/
def collisionSet (S : FacetSeparationValues α facets) : Set ℂ :=
  Set.range fun p : (facets × facets) × ((α → ℤ) × (α → ℤ)) =>
    (S.orbitSum p.1.2 p.2.2 - S.orbitSum p.1.1 p.2.1) /
      ((facetTag facets p.1.1 : ℂ) - (facetTag facets p.1.2 : ℂ))

theorem collisionSet_countable (S : FacetSeparationValues α facets) :
    (S.collisionSet).Countable :=
  Set.countable_range _

/-- **Compressed palette separation.**  Outside a countable set of parameters the compressed
facet-orbit shift is injective on the facet slice. -/
theorem orbitShift_injOn (S : FacetSeparationValues α facets) {t : ℂ}
    (ht : t ∉ S.collisionSet) :
    Set.InjOn (S.orbitShift t) (FacetSlice α facets) := by
  classical
  rintro ⟨F, n⟩ hFn ⟨G, m⟩ hGm h
  have hFG : F = G := by
    by_contra hne
    have htag : (facetTag facets F : ℂ) ≠ (facetTag facets G : ℂ) := by
      intro hc
      exact hne (facetTag_injective facets (by exact_mod_cast hc))
    refine ht ⟨((F, G), (n, m)), ?_⟩
    have hsub : (facetTag facets F : ℂ) - (facetTag facets G : ℂ) ≠ 0 :=
      sub_ne_zero.2 htag
    have h' : t * (facetTag facets F : ℂ) + S.orbitSum F n =
        t * (facetTag facets G : ℂ) + S.orbitSum G m := h
    show (S.orbitSum G m - S.orbitSum F n) /
      ((facetTag facets F : ℂ) - (facetTag facets G : ℂ)) = t
    rw [div_eq_iff hsub]
    linear_combination -h'
  subst hFG
  have hsum : S.orbitSum F n = S.orbitSum F m := by
    have h' : t * (facetTag facets F : ℂ) + S.orbitSum F n =
        t * (facetTag facets F : ℂ) + S.orbitSum F m := h
    exact add_left_cancel h'
  have hnm : n = m :=
    S.orbitSum_injOn_slice F (fun v hv => hFn v hv) (fun v hv => hGm v hv) hsum
  rw [hnm]

/-- A separation parameter outside the countable collision set always exists. -/
theorem exists_separation_parameter (S : FacetSeparationValues α facets) :
    ∃ t : ℂ, t ∉ S.collisionSet := by
  by_contra h
  push Not at h
  exact not_countable_complex (by
    have : S.collisionSet = (Set.univ : Set ℂ) :=
      Set.eq_univ_of_forall fun t => h t
    exact this ▸ S.collisionSet_countable)

end FacetSeparationValues

end

end GaloisForLFunctions.HTGeometry
