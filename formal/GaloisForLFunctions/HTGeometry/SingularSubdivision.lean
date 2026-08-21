import GaloisForLFunctions.HTGeometry.AffineToSingular
import GaloisForLFunctions.HTGeometry.AffineNaturality

/-!
# Barycentric subdivision of singular chains

The affine subdivision of the standard simplex is transported to an arbitrary singular simplex by
pushing it forward along that simplex.  Because the affine subdivision and its chain homotopy are
natural in the ambient space, and because the faces of the standard simplex are the images of the
standard simplex of one dimension lower under linear maps of the ambient space, the transported
operators commute with the faces.  Hence:

* `singBd_singSd` : subdivision is a chain map on singular chains;
* `singBd_singT`  : subdivision is chain homotopic to the identity.

Both statements are exact transcriptions of the corresponding affine identities; no new geometry
enters, only the naturality of the affine operators and the fact that the retraction used to define
the pushforward is the identity on chains whose vertices lie in the simplex.
-/

namespace GaloisForLFunctions.HTGeometry

universe v

/-! ### The ambient linear extension of a map of vertex sets -/

/-- The linear map of ambient spaces extending the map of simplices induced by a map of vertex
sets. -/
noncomputable def ambMap {m k : ℕ} (f : Fin (m + 1) → Fin (k + 1)) :
    (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ) :=
  FunOnFinite.linearMap ℝ ℝ f

theorem coe_topMap {m k : ℕ} (f : Fin (m + 1) → Fin (k + 1)) (x : topSimplex m) :
    ((topMap f x : topSimplex k) : Fin (k + 1) → ℝ) = ambMap f (x : Fin (m + 1) → ℝ) :=
  stdSimplex.map_coe f x

theorem ambMap_single {m k : ℕ} (f : Fin (m + 1) → Fin (k + 1)) (j : Fin (m + 1)) :
    ambMap f (Pi.single j (1 : ℝ)) = Pi.single (f j) 1 := by
  simp [ambMap]

/-- The vertices of the standard simplex, as points of the ambient space. -/
noncomputable def stdVerts (n : ℕ) : Fin (n + 1) → (Fin (n + 1) → ℝ) := fun i => Pi.single i 1

theorem stdVerts_mem (n : ℕ) (i : Fin (n + 1)) : stdVerts n i ∈ stdSimplex ℝ (Fin (n + 1)) :=
  (stdSimplex.vertex (S := ℝ) i).2

theorem ambMap_comp_stdVerts {m k : ℕ} (f : Fin (m + 1) → Fin (k + 1)) :
    (ambMap f : (Fin (m + 1) → ℝ) → (Fin (k + 1) → ℝ)) ∘ stdVerts m = stdVerts k ∘ f :=
  funext fun j => ambMap_single f j

theorem affComb_stdVerts {k : ℕ} (x : topSimplex k) :
    affComb (stdVerts k) x = (x : Fin (k + 1) → ℝ) := by
  rw [affComb_apply]
  funext l
  rw [Finset.sum_apply]
  simp [stdVerts, Pi.single_apply, mul_ite, Finset.sum_ite_eq]

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

theorem affSing_stdVerts {k : ℕ} (σ : C(topSimplex k, X)) : affSing σ (stdVerts k) = σ := by
  refine ContinuousMap.ext fun x => ?_
  rw [affSing_apply, affComb_stdVerts, simplexRetr_coe]

/-- The affine chain given by the standard simplex itself. -/
noncomputable def idAff (n : ℕ) : ((Fin (n + 1) → (Fin (n + 1) → ℝ)) →₀ R) :=
  Finsupp.single (stdVerts n) 1

theorem verticesIn_idAff {n : ℕ} : VerticesIn R (stdSimplex ℝ (Fin (n + 1))) (idAff R n) := by
  intro w hw i
  have hw' : w = stdVerts n := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
  subst hw'
  exact stdVerts_mem n i

theorem affToSing_idAff {k : ℕ} (σ : C(topSimplex k, X)) :
    affToSing R σ (idAff R k) = Finsupp.single σ (1 : R) := by
  rw [idAff, affToSing_single, affSing_stdVerts]

theorem affPush_idAff {k : ℕ} (i : Fin (k + 2)) :
    affPush R (ambMap (Fin.succAbove i)) k (idAff R k)
      = Finsupp.single (stdVerts (k + 1) ∘ i.succAbove) (1 : R) := by
  rw [idAff, affPush_single, ambMap_comp_stdVerts]

/-! ### Naturality of the pushforward -/

/-- On tuples inside the simplex the pushforward is natural in the vertex map. -/
theorem affSing_ambMap {j m k : ℕ} (σ : C(topSimplex k, X)) (f : Fin (m + 1) → Fin (k + 1))
    (w : Fin (j + 1) → (Fin (m + 1) → ℝ)) (hw : ∀ i, w i ∈ stdSimplex ℝ (Fin (m + 1))) :
    affSing σ ((ambMap f : (Fin (m + 1) → ℝ) → (Fin (k + 1) → ℝ)) ∘ w)
      = affSing (σ.comp (topMap f)) w := by
  refine ContinuousMap.ext fun x => ?_
  have hy : affComb w x ∈ stdSimplex ℝ (Fin (m + 1)) := affComb_mem w hw x
  have h1 : affComb ((ambMap f : (Fin (m + 1) → ℝ) → (Fin (k + 1) → ℝ)) ∘ w) x
      = ambMap f (affComb w x) := by
    rw [affComb_apply, affComb_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul (ambMap f) _ _).symm
  have h2 : simplexRetr (affComb w x) = (⟨affComb w x, hy⟩ : topSimplex m) :=
    simplexRetr_coe ⟨affComb w x, hy⟩
  have h3 : ambMap f (affComb w x)
      = ((topMap f (⟨affComb w x, hy⟩ : topSimplex m) : topSimplex k) : Fin (k + 1) → ℝ) :=
    (coe_topMap f ⟨affComb w x, hy⟩).symm
  rw [affSing_apply, affSing_apply, h1, h3, simplexRetr_coe, ContinuousMap.comp_apply, h2]

theorem affToSing_affPush {j m k : ℕ} (σ : C(topSimplex k, X)) (f : Fin (m + 1) → Fin (k + 1))
    (c : (Fin (j + 1) → (Fin (m + 1) → ℝ)) →₀ R)
    (hc : VerticesIn R (stdSimplex ℝ (Fin (m + 1))) c) :
    affToSing R σ (affPush R (ambMap f) j c) = affToSing R (σ.comp (topMap f)) c := by
  classical
  show Finsupp.mapDomain (affSing σ)
      (Finsupp.mapDomain (fun v => (ambMap f : (Fin (m + 1) → ℝ) → (Fin (k + 1) → ℝ)) ∘ v) c)
    = Finsupp.mapDomain (affSing (σ.comp (topMap f))) c
  rw [← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun w hw => ?_
  exact affSing_ambMap σ f w fun i => hc w hw i

/-! ### Subdivision of singular chains -/

/-- Barycentric subdivision of singular chains. -/
noncomputable def singSd (k : ℕ) : (C(topSimplex k, X) →₀ R) →ₗ[R] (C(topSimplex k, X) →₀ R) :=
  Finsupp.linearCombination R
    (fun σ : C(topSimplex k, X) => affToSing R σ (affSd R (Fin (k + 1) → ℝ) k (idAff R k)))

theorem singSd_single {k : ℕ} (σ : C(topSimplex k, X)) (r : R) :
    singSd R (X := X) k (Finsupp.single σ r)
      = r • affToSing R σ (affSd R (Fin (k + 1) → ℝ) k (idAff R k)) :=
  Finsupp.linearCombination_single _ _ _

/-- The chain homotopy from the subdivision to the identity, on singular chains. -/
noncomputable def singT (k : ℕ) :
    (C(topSimplex k, X) →₀ R) →ₗ[R] (C(topSimplex (k + 1), X) →₀ R) :=
  Finsupp.linearCombination R
    (fun σ : C(topSimplex k, X) => affToSing R σ (affT R (Fin (k + 1) → ℝ) k (idAff R k)))

theorem singT_single {k : ℕ} (σ : C(topSimplex k, X)) (r : R) :
    singT R (X := X) k (Finsupp.single σ r)
      = r • affToSing R σ (affT R (Fin (k + 1) → ℝ) k (idAff R k)) :=
  Finsupp.linearCombination_single _ _ _

/-- **Subdivision is a chain map on singular chains.** -/
theorem singBd_singSd {k : ℕ} (c : C(topSimplex (k + 1), X) →₀ R) :
    singBd R X k (singSd R (k + 1) c) = singSd R k (singBd R X k c) := by
  have hmap : (singBd R X k).comp (singSd R (X := X) (k + 1))
      = (singSd R (X := X) k).comp (singBd R X k) := by
    refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
    show singBd R X k (singSd R (k + 1) (Finsupp.single σ (1 : R)))
        = singSd R k (singBd R X k (Finsupp.single σ (1 : R)))
    have key : ∀ i : Fin (k + 2),
        singSd R (X := X) k (Finsupp.single (σ.comp (topMap i.succAbove)) ((-1 : R) ^ (i : ℕ)))
          = affToSing R σ (affSd R (Fin (k + 2) → ℝ) k
              (Finsupp.single (stdVerts (k + 1) ∘ i.succAbove) ((-1 : R) ^ (i : ℕ)))) := by
      intro i
      rw [singSd_single, ← affToSing_affPush R σ (Fin.succAbove i) _
          (verticesIn_affSd R (convex_stdSimplex ℝ (Fin (k + 1))) (verticesIn_idAff R)),
        affPush_affSd, affPush_idAff, ← map_smul, ← map_smul, Finsupp.smul_single,
        smul_eq_mul, mul_one]
    have hL : singBd R X k (singSd R (k + 1) (Finsupp.single σ (1 : R)))
        = ∑ i : Fin (k + 2), affToSing R σ (affSd R (Fin (k + 2) → ℝ) k
            (Finsupp.single (stdVerts (k + 1) ∘ i.succAbove) ((-1 : R) ^ (i : ℕ)))) := by
      rw [singSd_single, one_smul, singBd_affToSing, affBd_affSd, idAff, affBd_single,
        map_sum, map_sum]
    have hR : singSd R k (singBd R X k (Finsupp.single σ (1 : R)))
        = ∑ i : Fin (k + 2), affToSing R σ (affSd R (Fin (k + 2) → ℝ) k
            (Finsupp.single (stdVerts (k + 1) ∘ i.succAbove) ((-1 : R) ^ (i : ℕ)))) := by
      rw [singBd_single, map_sum]
      exact Finset.sum_congr rfl fun i _ => key i
    rw [hL, hR]
  exact LinearMap.congr_fun hmap c

/-- **Subdivision is chain homotopic to the identity on singular chains.** -/
theorem singBd_singT {k : ℕ} (c : C(topSimplex (k + 1), X) →₀ R) :
    singBd R X (k + 1) (singT R (k + 1) c) + singT R k (singBd R X k c)
      = singSd R (k + 1) c - c := by
  have hmap : ((singBd R X (k + 1)).comp (singT R (X := X) (k + 1)))
      + ((singT R (X := X) k).comp (singBd R X k))
      = (singSd R (X := X) (k + 1)) - LinearMap.id := by
    refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
    show singBd R X (k + 1) (singT R (k + 1) (Finsupp.single σ (1 : R)))
        + singT R k (singBd R X k (Finsupp.single σ (1 : R)))
      = singSd R (k + 1) (Finsupp.single σ (1 : R)) - Finsupp.single σ (1 : R)
    have key : ∀ i : Fin (k + 2),
        singT R (X := X) k (Finsupp.single (σ.comp (topMap i.succAbove)) ((-1 : R) ^ (i : ℕ)))
          = affToSing R σ (affT R (Fin (k + 2) → ℝ) k
              (Finsupp.single (stdVerts (k + 1) ∘ i.succAbove) ((-1 : R) ^ (i : ℕ)))) := by
      intro i
      rw [singT_single, ← affToSing_affPush R σ (Fin.succAbove i) _
          (verticesIn_affT R (convex_stdSimplex ℝ (Fin (k + 1))) k (verticesIn_idAff R)),
        affPush_affT, affPush_idAff, ← map_smul, ← map_smul, Finsupp.smul_single,
        smul_eq_mul, mul_one]
    have hL : singBd R X (k + 1) (singT R (k + 1) (Finsupp.single σ (1 : R)))
        = affToSing R σ (affBd R (Fin (k + 2) → ℝ) (k + 1)
            (affT R (Fin (k + 2) → ℝ) (k + 1) (idAff R (k + 1)))) := by
      rw [singT_single, one_smul, singBd_affToSing]
    have hR : singT R k (singBd R X k (Finsupp.single σ (1 : R)))
        = affToSing R σ (affT R (Fin (k + 2) → ℝ) k
            (affBd R (Fin (k + 2) → ℝ) k (idAff R (k + 1)))) := by
      rw [singBd_single, map_sum, Finset.sum_congr rfl fun i _ => key i, ← map_sum, ← map_sum,
        idAff, affBd_single]
    rw [hL, hR, ← map_add, affBd_affT, map_sub, singSd_single, one_smul, affToSing_idAff]
  have := LinearMap.congr_fun hmap c
  simpa using this

end GaloisForLFunctions.HTGeometry
