import GaloisForLFunctions.HTGeometry.TopologicalSingularChains
import GaloisForLFunctions.HTGeometry.SubdivisionSupport
import Mathlib.Algebra.BigOperators.Field

/-!
# Pushing affine chains forward to singular chains

An affine simplex with vertices in the standard `n`-simplex determines a singular simplex of any
space `X` once a singular `n`-simplex `σ` of `X` is fixed: send a point of the standard `k`-simplex
to its affine combination of the vertices and then apply `σ`.

To make this assignment total — defined for *every* tuple of points of the ambient space, not only
for those inside the simplex — the affine combination is followed by a continuous retraction of the
ambient space onto the standard simplex, obtained by taking positive parts and renormalising with a
defect term that keeps the denominator at least one.  On tuples of points of the simplex the
retraction is the identity, so nothing is changed there, while totality makes the assignment a
map of chain complexes with no side conditions:

  `∂ (σ_* c) = σ_* (∂ c)`.

This is the bridge along which barycentric subdivision is transported from affine chains to
singular chains.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

universe v

variable {n : ℕ}

/-! ### A continuous retraction of the ambient space onto the standard simplex -/

/-- The total mass of the positive part of a point. -/
noncomputable def clampSum (y : Fin (n + 1) → ℝ) : ℝ := ∑ j, max (y j) 0

/-- The amount by which the positive part falls short of total mass one. -/
noncomputable def clampDefect (y : Fin (n + 1) → ℝ) : ℝ := max 0 (1 - clampSum y)

/-- The normalising denominator of the retraction; it is never smaller than one. -/
noncomputable def clampDen (y : Fin (n + 1) → ℝ) : ℝ := clampSum y + clampDefect y

/-- The unnormalised barycentric coordinates of the retraction. -/
noncomputable def clampNum (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  max (y i) 0 + clampDefect y / ((n : ℝ) + 1)

theorem clampDefect_nonneg (y : Fin (n + 1) → ℝ) : 0 ≤ clampDefect y := le_max_left _ _

theorem one_le_clampDen (y : Fin (n + 1) → ℝ) : 1 ≤ clampDen y := by
  have h : 1 - clampSum y ≤ clampDefect y := le_max_right _ _
  simp only [clampDen]
  linarith

theorem clampDen_pos (y : Fin (n + 1) → ℝ) : 0 < clampDen y :=
  lt_of_lt_of_le zero_lt_one (one_le_clampDen y)

theorem clampNum_nonneg (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : 0 ≤ clampNum y i := by
  have h1 : (0 : ℝ) ≤ max (y i) 0 := le_max_right _ _
  have h3 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : 0 ≤ clampDefect y / ((n : ℝ) + 1) := div_nonneg (clampDefect_nonneg y) h3.le
  simp only [clampNum]
  linarith

theorem sum_clampNum (y : Fin (n + 1) → ℝ) : ∑ i, clampNum y i = clampDen y := by
  have h1 : ∑ _i : Fin (n + 1), clampDefect y / ((n : ℝ) + 1) = clampDefect y := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  simp only [clampNum]
  rw [Finset.sum_add_distrib, h1]
  rfl

/-- The retraction of the ambient space onto the standard simplex. -/
noncomputable def simplexRetr (y : Fin (n + 1) → ℝ) : topSimplex n :=
  ⟨fun i => clampNum y i / clampDen y, by
    refine ⟨fun i => div_nonneg (clampNum_nonneg y i) (clampDen_pos y).le, ?_⟩
    rw [← Finset.sum_div, sum_clampNum, div_self (clampDen_pos y).ne']⟩

theorem continuous_clampSum : Continuous (clampSum : (Fin (n + 1) → ℝ) → ℝ) :=
  continuous_finsetSum _ fun j _ => (continuous_apply j).max continuous_const

theorem continuous_clampDefect : Continuous (clampDefect : (Fin (n + 1) → ℝ) → ℝ) :=
  continuous_const.max (continuous_const.sub continuous_clampSum)

theorem continuous_clampDen : Continuous (clampDen : (Fin (n + 1) → ℝ) → ℝ) :=
  continuous_clampSum.add continuous_clampDefect

theorem continuous_simplexRetr : Continuous (simplexRetr : (Fin (n + 1) → ℝ) → topSimplex n) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i => ?_
  exact Continuous.div
    (((continuous_apply i).max continuous_const).add (continuous_clampDefect.div_const _))
    continuous_clampDen fun y => (clampDen_pos y).ne'

/-- On the simplex itself the retraction is the identity. -/
theorem simplexRetr_coe (x : topSimplex n) : simplexRetr (x : Fin (n + 1) → ℝ) = x := by
  have hmax : ∀ i, max ((x : Fin (n + 1) → ℝ) i) 0 = (x : Fin (n + 1) → ℝ) i :=
    fun i => max_eq_left (stdSimplex.zero_le x i)
  have hsum : clampSum (x : Fin (n + 1) → ℝ) = 1 := by
    simp only [clampSum, hmax]
    exact stdSimplex.sum_eq_one x
  have hdef : clampDefect (x : Fin (n + 1) → ℝ) = 0 := by
    simp only [clampDefect, hsum, sub_self, max_self]
  have hden : clampDen (x : Fin (n + 1) → ℝ) = 1 := by
    simp only [clampDen, hsum, hdef, add_zero]
  refine Subtype.ext (funext fun i => ?_)
  show clampNum (x : Fin (n + 1) → ℝ) i / clampDen (x : Fin (n + 1) → ℝ) = _
  rw [hden, div_one, clampNum, hdef, hmax i, zero_div, add_zero]
  rfl

/-- The retraction as a continuous map. -/
noncomputable def simplexRetrMap : C(Fin (n + 1) → ℝ, topSimplex n) :=
  ⟨simplexRetr, continuous_simplexRetr⟩

/-! ### Affine simplices -/

/-- The affine map of the standard `k`-simplex determined by a tuple of `k + 1` points. -/
noncomputable def affComb {k : ℕ} (v : Fin (k + 1) → (Fin (n + 1) → ℝ)) :
    C(topSimplex k, Fin (n + 1) → ℝ) :=
  ⟨fun x => ∑ i, (x i) • v i, by
    refine continuous_finsetSum _ fun i _ => ?_
    exact Continuous.smul ((continuous_apply i).comp continuous_subtype_val) continuous_const⟩

theorem affComb_apply {k : ℕ} (v : Fin (k + 1) → (Fin (n + 1) → ℝ)) (x : topSimplex k) :
    affComb v x = ∑ i, (x i) • v i := rfl

/-- Precomposing an affine simplex with a face map reindexes its vertices. -/
theorem affComb_comp_topMap {k m : ℕ} (v : Fin (m + 1) → (Fin (n + 1) → ℝ))
    (f : Fin (k + 1) → Fin (m + 1)) :
    (affComb v).comp (topMap f) = affComb (v ∘ f) := by
  classical
  refine ContinuousMap.ext fun x => ?_
  show ∑ l, ((topMap f x) l) • v l = ∑ i, (x i) • v (f i)
  have h : ∀ l : Fin (m + 1), ((topMap f x) l) • v l
      = ∑ i ∈ Finset.univ.filter (fun i => f i = l), (x i) • v (f i) := by
    intro l
    rw [topMap_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl fun l _ => h l]
  exact Finset.sum_fiberwise Finset.univ f (fun i => (x i) • v (f i))

/-- An affine combination of points of the simplex stays in the simplex. -/
theorem affComb_mem {k : ℕ} (v : Fin (k + 1) → (Fin (n + 1) → ℝ))
    (hv : ∀ i, v i ∈ stdSimplex ℝ (Fin (n + 1))) (x : topSimplex k) :
    affComb v x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  rw [affComb_apply]
  refine (convex_stdSimplex ℝ (Fin (n + 1))).sum_mem (fun i _ => stdSimplex.zero_le x i) ?_
    (fun i _ => hv i)
  exact stdSimplex.sum_eq_one x

/-! ### The induced map of chain complexes -/

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- The singular simplex obtained from an affine simplex of the ambient space by retracting to the
standard simplex and applying a fixed singular simplex. -/
noncomputable def affSing {k : ℕ} (σ : C(topSimplex n, X))
    (v : Fin (k + 1) → (Fin (n + 1) → ℝ)) : C(topSimplex k, X) :=
  σ.comp (simplexRetrMap.comp (affComb v))

theorem affSing_apply {k : ℕ} (σ : C(topSimplex n, X)) (v : Fin (k + 1) → (Fin (n + 1) → ℝ))
    (x : topSimplex k) : affSing σ v x = σ (simplexRetr (affComb v x)) := rfl

/-- For vertices inside the simplex the retraction does nothing. -/
theorem affSing_apply_of_mem {k : ℕ} (σ : C(topSimplex n, X))
    (v : Fin (k + 1) → (Fin (n + 1) → ℝ)) (hv : ∀ i, v i ∈ stdSimplex ℝ (Fin (n + 1)))
    (x : topSimplex k) : affSing σ v x = σ ⟨affComb v x, affComb_mem v hv x⟩ := by
  rw [affSing_apply]
  congr 1
  exact simplexRetr_coe ⟨affComb v x, affComb_mem v hv x⟩

theorem affSing_comp {k m : ℕ} (σ : C(topSimplex n, X)) (v : Fin (m + 1) → (Fin (n + 1) → ℝ))
    (f : Fin (k + 1) → Fin (m + 1)) :
    (affSing σ v).comp (topMap f) = affSing σ (v ∘ f) := by
  rw [affSing, affSing, ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
    affComb_comp_topMap]

/-- The map from affine chains of the ambient space to singular chains of `X` induced by a singular
simplex. -/
noncomputable def affToSing {k : ℕ} (σ : C(topSimplex n, X)) :
    ((Fin (k + 1) → (Fin (n + 1) → ℝ)) →₀ R) →ₗ[R] (C(topSimplex k, X) →₀ R) :=
  Finsupp.lmapDomain R R (affSing σ)

theorem affToSing_single {k : ℕ} (σ : C(topSimplex n, X))
    (v : Fin (k + 1) → (Fin (n + 1) → ℝ)) (r : R) :
    affToSing R σ (Finsupp.single v r) = Finsupp.single (affSing σ v) r :=
  Finsupp.mapDomain_single

/-- **The pushforward of affine chains along a singular simplex is a chain map.** -/
theorem singBd_comp_affToSing {k : ℕ} (σ : C(topSimplex n, X)) :
    (singBd R X k).comp (affToSing R (k := k + 1) σ)
      = (affToSing R (k := k) σ).comp (affBd R (Fin (n + 1) → ℝ) k) := by
  refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [affToSing_single, singBd_single, affBd_single, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [affToSing_single, affSing_comp]

theorem singBd_affToSing {k : ℕ} (σ : C(topSimplex n, X))
    (c : (Fin (k + 2) → (Fin (n + 1) → ℝ)) →₀ R) :
    singBd R X k (affToSing R σ c) = affToSing R σ (affBd R (Fin (n + 1) → ℝ) k c) := by
  have := singBd_comp_affToSing R (X := X) (k := k) σ
  exact congrArg (fun L : ((Fin (k + 2) → (Fin (n + 1) → ℝ)) →₀ R) →ₗ[R]
    (C(topSimplex k, X) →₀ R) => L c) this

end GaloisForLFunctions.HTGeometry
