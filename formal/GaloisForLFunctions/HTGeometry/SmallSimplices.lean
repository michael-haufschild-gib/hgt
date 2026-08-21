import GaloisForLFunctions.HTGeometry.SingularSubdivision

/-!
# The small simplices theorem

Iterating the barycentric subdivision of a singular simplex produces simplices of arbitrarily small
image.  Two ingredients combine.

First, the subdivision of a singular simplex is again a pushforward of an affine chain along the
*same* simplex: an affine simplex of the standard simplex determines a linear map of the ambient
space, and the pushforward is natural for it, so the `N`-fold subdivision of `σ` is `σ` applied to
the `N`-fold affine subdivision of the standard simplex.

Second, the affine subdivision shrinks diameters geometrically, so after enough iterations every
affine simplex occurring is smaller than a Lebesgue number of the open cover pulled back along `σ`.
-/

open Finset Metric

namespace GaloisForLFunctions.HTGeometry

universe v

/-! ### The linear extension of an affine simplex -/

/-- The linear map of ambient spaces extending an affine simplex. -/
noncomputable def ambComb {j m : ℕ} (w : Fin (j + 1) → (Fin (m + 1) → ℝ)) :
    (Fin (j + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun y := ∑ i, y i • w i
  map_add' a b := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' r a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact (Finset.smul_sum).symm

theorem ambComb_apply {j m : ℕ} (w : Fin (j + 1) → (Fin (m + 1) → ℝ)) (y : Fin (j + 1) → ℝ) :
    ambComb w y = ∑ i, y i • w i := rfl

theorem ambComb_comp_stdVerts {j m : ℕ} (w : Fin (j + 1) → (Fin (m + 1) → ℝ)) :
    (ambComb w : (Fin (j + 1) → ℝ) → (Fin (m + 1) → ℝ)) ∘ stdVerts j = w := by
  funext i
  show ∑ a, (stdVerts j i) a • w a = w i
  simp [stdVerts, Pi.single_apply, ite_smul, Finset.sum_ite_eq']

/-- Every point of an affine simplex is within the diameter of each of its vertices. -/
theorem norm_affComb_sub_vertex_le {j m : ℕ} {w : Fin (j + 1) → (Fin (m + 1) → ℝ)} {D : ℝ}
    (h : ∀ a b, ‖w a - w b‖ ≤ D) (x : topSimplex j) (i : Fin (j + 1)) :
    ‖affComb w x - w i‖ ≤ D := by
  have hrepr : affComb w x - w i = ∑ a, (x a) • (w a - w i) := by
    have h1 : ∑ a, (x a) • (w a - w i) = (∑ a, (x a) • w a) - (∑ a, x a) • w i := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => smul_sub _ _ _
    rw [h1, stdSimplex.sum_eq_one x, one_smul, affComb_apply]
  rw [hrepr]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ a ∈ (Finset.univ : Finset (Fin (j + 1))),
      ‖(x a) • (w a - w i)‖ ≤ x a * D := by
    intro a _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (stdSimplex.zero_le x a)]
    exact mul_le_mul_of_nonneg_left (h a i) (stdSimplex.zero_le x a)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, stdSimplex.sum_eq_one x, one_mul]

/-! ### Subdivision iterated on a singular simplex -/

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- Pushing forward along an affine simplex of the standard simplex is the same as pushing forward
along the singular simplex it determines. -/
theorem affSing_ambComb {j m k : ℕ} (σ : C(topSimplex k, X))
    (w : Fin (m + 1) → (Fin (k + 1) → ℝ)) (u : Fin (j + 1) → (Fin (m + 1) → ℝ))
    (hu : ∀ i, u i ∈ stdSimplex ℝ (Fin (m + 1))) :
    affSing σ ((ambComb w : (Fin (m + 1) → ℝ) → (Fin (k + 1) → ℝ)) ∘ u)
      = affSing (affSing σ w) u := by
  refine ContinuousMap.ext fun x => ?_
  have hy : affComb u x ∈ stdSimplex ℝ (Fin (m + 1)) := affComb_mem u hu x
  have h1 : affComb ((ambComb w : (Fin (m + 1) → ℝ) → (Fin (k + 1) → ℝ)) ∘ u) x
      = ambComb w (affComb u x) := by
    rw [affComb_apply, affComb_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul (ambComb w) _ _).symm
  have h2 : simplexRetr (affComb u x) = (⟨affComb u x, hy⟩ : topSimplex m) :=
    simplexRetr_coe ⟨affComb u x, hy⟩
  rw [affSing_apply, affSing_apply, h1, h2]
  rfl

theorem affToSing_ambComb {j m k : ℕ} (σ : C(topSimplex k, X))
    (w : Fin (m + 1) → (Fin (k + 1) → ℝ)) (c : (Fin (j + 1) → (Fin (m + 1) → ℝ)) →₀ R)
    (hc : VerticesIn R (stdSimplex ℝ (Fin (m + 1))) c) :
    affToSing R σ (affPush R (ambComb w) j c) = affToSing R (affSing σ w) c := by
  classical
  show Finsupp.mapDomain (affSing σ)
      (Finsupp.mapDomain
        (fun u => (ambComb w : (Fin (m + 1) → ℝ) → (Fin (k + 1) → ℝ)) ∘ u) c)
    = Finsupp.mapDomain (affSing (affSing σ w)) c
  rw [← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun u hu => ?_
  exact affSing_ambComb σ w u fun i => hc u hu i

/-- **Subdivision of a pushforward is the pushforward of the subdivision.** -/
theorem singSd_affToSing {k : ℕ} (σ : C(topSimplex k, X))
    (c : (Fin (k + 1) → (Fin (k + 1) → ℝ)) →₀ R) :
    singSd R k (affToSing R σ c) = affToSing R σ (affSd R (Fin (k + 1) → ℝ) k c) := by
  classical
  have key : ∀ w ∈ c.support,
      affToSing R (affSing σ w) (affSd R (Fin (k + 1) → ℝ) k (idAff R k))
        = affToSing R σ (affSd R (Fin (k + 1) → ℝ) k (Finsupp.single w (1 : R))) := by
    intro w _
    rw [← affToSing_ambComb R σ w _
        (verticesIn_affSd R (convex_stdSimplex ℝ (Fin (k + 1))) (verticesIn_idAff R)),
      affPush_affSd, idAff, affPush_single, ambComb_comp_stdVerts]
  have hLHS : singSd R k (affToSing R σ c)
      = ∑ w ∈ c.support,
          (c w) • affToSing R (affSing σ w) (affSd R (Fin (k + 1) → ℝ) k (idAff R k)) := by
    show singSd R k (Finsupp.mapDomain (affSing σ) c) = _
    rw [Finsupp.mapDomain, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun w _ => singSd_single R _ _
  have hRHS : affToSing R σ (affSd R (Fin (k + 1) → ℝ) k c)
      = ∑ w ∈ c.support,
          (c w) • affToSing R σ (affSd R (Fin (k + 1) → ℝ) k (Finsupp.single w (1 : R))) := by
    conv_lhs => rw [← Finsupp.sum_single c, Finsupp.sum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hsplit : Finsupp.single w (c w) = (c w) • Finsupp.single w (1 : R) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsplit, map_smul, map_smul]
  rw [hLHS, hRHS]
  exact Finset.sum_congr rfl fun w hw => by rw [key w hw]

theorem diamLe_idAff {k : ℕ} : DiamLe R (1 : ℝ) (idAff R k) := by
  intro w hw i j
  have hw' : w = stdVerts k := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
  subst hw'
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro l
  have hbd : ∀ a : Fin (k + 1), (0 : ℝ) ≤ (Pi.single a (1 : ℝ) : Fin (k + 1) → ℝ) l
      ∧ (Pi.single a (1 : ℝ) : Fin (k + 1) → ℝ) l ≤ 1 := by
    intro a
    rw [Pi.single_apply]
    split <;> norm_num
  have hi := hbd i
  have hj := hbd j
  simp only [stdVerts, Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_sub_le_iff]
  constructor
  · linarith [hi.1, hi.2, hj.1, hj.2]
  · linarith [hi.1, hi.2, hj.1, hj.2]

theorem verticesIn_sdIter {k N : ℕ} :
    VerticesIn R (stdSimplex ℝ (Fin (k + 1))) (sdIter R k N (idAff R k)) :=
  (sdIter_mesh R (convex_stdSimplex ℝ (Fin (k + 1))) (verticesIn_idAff R) (diamLe_idAff R) N).1

theorem diamLe_sdIter {k N : ℕ} :
    DiamLe R ((((k : ℝ) / ((k : ℝ) + 1)) ^ N) * 1) (sdIter R k N (idAff R k)) :=
  (sdIter_mesh R (convex_stdSimplex ℝ (Fin (k + 1))) (verticesIn_idAff R) (diamLe_idAff R) N).2

/-- **The `N`-fold subdivision of a singular simplex is the pushforward of the `N`-fold affine
subdivision of the standard simplex.** -/
theorem singSd_iterate {k : ℕ} (σ : C(topSimplex k, X)) (N : ℕ) :
    (singSd R (X := X) k)^[N] (Finsupp.single σ (1 : R))
      = affToSing R σ (sdIter R k N (idAff R k)) := by
  induction N with
  | zero =>
    rw [Function.iterate_zero_apply, sdIter_zero, affToSing_idAff]
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, sdIter_succ,
      singSd_affToSing R σ _]

/-! ### Smallness -/

/-- **The small simplices theorem.**  For every open cover and every singular simplex there is an
iterated barycentric subdivision all of whose simplices have image inside a member of the cover. -/
theorem exists_iterate_small (𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U)
    (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰) {k : ℕ} (σ : C(topSimplex k, X)) :
    ∃ N : ℕ, ∀ τ ∈ ((singSd R (X := X) k)^[N] (Finsupp.single σ (1 : R))).support,
      ∃ U ∈ 𝒰, Set.range τ ⊆ U := by
  classical
  have hFc : Continuous (fun y : Fin (k + 1) → ℝ => σ (simplexRetr y)) :=
    σ.continuous.comp continuous_simplexRetr
  have hopen' : ∀ U : {U : Set X // U ∈ 𝒰},
      IsOpen ((fun y : Fin (k + 1) → ℝ => σ (simplexRetr y)) ⁻¹' (U : Set X)) :=
    fun U => IsOpen.preimage hFc (hopen U U.2)
  have hsub : stdSimplex ℝ (Fin (k + 1))
      ⊆ ⋃ U : {U : Set X // U ∈ 𝒰},
        (fun y : Fin (k + 1) → ℝ => σ (simplexRetr y)) ⁻¹' (U : Set X) := by
    intro y _
    obtain ⟨U, hU, hyU⟩ := hcover (Set.mem_univ (σ (simplexRetr y)))
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hyU⟩
  obtain ⟨δ, hδ, hlb⟩ := lebesgue_number_lemma_of_metric
    (isCompact_stdSimplex ℝ (Fin (k + 1))) hopen' hsub
  have hratio : ((k : ℝ) / ((k : ℝ) + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hratio0 : (0 : ℝ) ≤ (k : ℝ) / ((k : ℝ) + 1) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ hratio
  refine ⟨N, fun τ hτ => ?_⟩
  rw [singSd_iterate R σ N] at hτ
  obtain ⟨w, hw, hτw⟩ := support_linear_apply_subset R (affToSing R σ) _ hτ
  rw [affToSing_single] at hτw
  have hτeq : τ = affSing σ w := Finset.mem_singleton.mp (Finsupp.support_single_subset hτw)
  have hvert : ∀ i, w i ∈ stdSimplex ℝ (Fin (k + 1)) := fun i => verticesIn_sdIter R w hw i
  have hdiam : ∀ a b, ‖w a - w b‖ ≤ (((k : ℝ) / ((k : ℝ) + 1)) ^ N) * 1 :=
    fun a b => diamLe_sdIter R w hw a b
  obtain ⟨U, hU⟩ := hlb (w 0) (hvert 0)
  refine ⟨(U : Set X), U.2, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hball : affComb w x ∈ ball (w 0) δ := by
    rw [mem_ball, dist_eq_norm]
    calc ‖affComb w x - w 0‖ ≤ (((k : ℝ) / ((k : ℝ) + 1)) ^ N) * 1 :=
          norm_affComb_sub_vertex_le hdiam x 0
      _ < δ := by rw [mul_one]; exact hN
  have := hU hball
  rw [hτeq, affSing_apply]
  exact this

end GaloisForLFunctions.HTGeometry
