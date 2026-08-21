import GaloisForLFunctions.HTGeometry.HomotopyEquivHomology
import Mathlib.Topology.Connected.PathConnected

/-!
# The augmentation and the zeroth homology

The augmentation sends a `0`-chain to the sum of its coefficients; it kills boundaries because the
two faces of a `1`-simplex carry opposite signs.  Conversely, on a path-connected space a `0`-chain
with vanishing total coefficient is a boundary: a path between two points is a `1`-simplex whose
boundary is the difference of the two constant `0`-simplices, so subtracting a multiple of a fixed
basepoint expresses the chain as a boundary.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- The augmentation of the singular chains. -/
noncomputable def singAug : (C(topSimplex 0, X) →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun _ => (1 : R))

theorem singAug_single (σ : C(topSimplex 0, X)) (r : R) :
    singAug R (Finsupp.single σ r) = r := by
  rw [singAug, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

theorem singAug_singBd (c : C(topSimplex 1, X) →₀ R) :
    singAug R (singBd R X 0 c) = 0 := by
  have hmap : (singAug R (X := X)).comp (singBd R X 0) = 0 := by
    refine Finsupp.lhom_ext' fun σ => LinearMap.ext_ring ?_
    show singAug R (singBd R X 0 (Finsupp.single σ (1 : R))) = 0
    rw [singBd_single, map_sum]
    rw [Finset.sum_congr rfl fun (i : Fin 2) _ =>
      singAug_single R (σ.comp (topMap (Fin.succAbove i))) ((-1 : R) ^ (i : ℕ))]
    rw [Fin.sum_univ_two]
    norm_num
  have := LinearMap.congr_fun hmap c
  simpa using this

/-! ### Paths as one-simplices -/

theorem topMap_of_zero {m : ℕ} (f : Fin 1 → Fin (m + 1)) (y : topSimplex 0) :
    topMap f y = stdSimplex.vertex (f 0) := by
  haveI : Unique (topSimplex 0) := inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))
  have hy : y = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
  rw [hy]
  exact stdSimplex.map_vertex (S := ℝ) f 0

/-- The coordinate map from the topological `1`-simplex to the unit interval. -/
noncomputable def edgeParam : C(topSimplex 1, unitInterval) :=
  ⟨fun x => ⟨x 1, Set.mem_Icc.mpr ⟨stdSimplex.zero_le x 1, stdSimplex.le_one x 1⟩⟩,
    Continuous.subtype_mk (((continuous_apply 1).comp continuous_subtype_val)) _⟩

theorem edgeParam_vertex (j : Fin 2) :
    (edgeParam (stdSimplex.vertex j) : ℝ) = if j = 1 then 1 else 0 := by
  show (Pi.single j (1 : ℝ) : Fin 2 → ℝ) 1 = _
  rw [Pi.single_apply]
  by_cases h : j = 1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun heq => h heq.symm)]

/-- The singular `1`-simplex determined by a path. -/
noncomputable def pathSimplex {a b : X} (p : Path a b) : C(topSimplex 1, X) :=
  p.toContinuousMap.comp edgeParam

theorem succAbove_zero_zero : Fin.succAbove (0 : Fin 2) (0 : Fin 1) = 1 := rfl

theorem succAbove_one_zero : Fin.succAbove (1 : Fin 2) (0 : Fin 1) = 0 := rfl

theorem pathSimplex_face_zero {a b : X} (p : Path a b) :
    (pathSimplex p).comp (topMap (Fin.succAbove (0 : Fin 2))) = constSimplex b 0 := by
  refine ContinuousMap.ext fun y => ?_
  show p (edgeParam (topMap (Fin.succAbove (0 : Fin 2)) y)) = b
  rw [topMap_of_zero, succAbove_zero_zero]
  have h1 : edgeParam (stdSimplex.vertex (1 : Fin 2)) = 1 := by
    refine Subtype.ext ?_
    rw [edgeParam_vertex]
    simp
  rw [h1]
  exact p.target

theorem pathSimplex_face_one {a b : X} (p : Path a b) :
    (pathSimplex p).comp (topMap (Fin.succAbove (1 : Fin 2))) = constSimplex a 0 := by
  refine ContinuousMap.ext fun y => ?_
  show p (edgeParam (topMap (Fin.succAbove (1 : Fin 2)) y)) = a
  rw [topMap_of_zero, succAbove_one_zero]
  have h1 : edgeParam (stdSimplex.vertex (0 : Fin 2)) = 0 := by
    refine Subtype.ext ?_
    rw [edgeParam_vertex]
    simp
  rw [h1]
  exact p.source

theorem singBd_pathSimplex {a b : X} (p : Path a b) :
    singBd R X 0 (Finsupp.single (pathSimplex p) (1 : R))
      = Finsupp.single (constSimplex b 0) (1 : R) - Finsupp.single (constSimplex a 0) (1 : R) := by
  rw [singBd_single, Fin.sum_univ_two, pathSimplex_face_zero, pathSimplex_face_one]
  norm_num
  abel

theorem single_sum_eq {α : Type*} (a : α) {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, Finsupp.single a (f i)) = Finsupp.single a (∑ i ∈ s, f i) := by
  classical
  refine Finsupp.ext fun b => ?_
  rw [Finset.sum_apply']
  by_cases h : b = a
  · subst h
    simp
  · simp [Finsupp.single_eq_of_ne h]

theorem singAug_eq_sum (c : C(topSimplex 0, X) →₀ R) :
    singAug R c = ∑ σ ∈ c.support, c σ := by
  rw [singAug, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun σ _ => by rw [smul_eq_mul, mul_one]

/-- **On a path-connected space a `0`-chain of total coefficient zero is a boundary.** -/
theorem exists_singBd_eq_of_singAug_eq_zero [PathConnectedSpace X]
    (c : C(topSimplex 0, X) →₀ R) (hc : singAug R c = 0) :
    ∃ d : C(topSimplex 1, X) →₀ R, singBd R X 0 d = c := by
  classical
  haveI : Unique (topSimplex 0) := inferInstanceAs (Unique (stdSimplex ℝ (Fin 1)))
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hconst : ∀ σ : C(topSimplex 0, X), constSimplex (σ default) 0 = σ := fun σ =>
    ContinuousMap.ext fun y => by rw [Subsingleton.elim y default]; rfl
  refine ⟨∑ σ ∈ c.support, c σ •
    Finsupp.single (pathSimplex (PathConnectedSpace.somePath x₀ (σ default))) (1 : R), ?_⟩
  rw [map_sum]
  have hterm : ∀ σ ∈ c.support,
      singBd R X 0 (c σ •
          Finsupp.single (pathSimplex (PathConnectedSpace.somePath x₀ (σ default))) (1 : R))
        = Finsupp.single σ (c σ) - Finsupp.single (constSimplex x₀ 0) (c σ) := by
    intro σ _
    rw [map_smul, singBd_pathSimplex, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.smul_single, smul_eq_mul, mul_one, hconst σ]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, single_sum_eq, ← singAug_eq_sum, hc,
    Finsupp.single_zero, sub_zero]
  exact (Finsupp.sum_single c)

/-- **The boundaries in degree zero are exactly the chains of total coefficient zero.** -/
theorem range_singBd_zero_eq_ker_singAug [PathConnectedSpace X] :
    LinearMap.range (singBd R X 0) = LinearMap.ker (singAug R (X := X)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨d, rfl⟩
    exact singAug_singBd R d
  · intro c hc
    obtain ⟨d, hd⟩ := exists_singBd_eq_of_singAug_eq_zero R c hc
    exact ⟨d, hd⟩

end GaloisForLFunctions.HTGeometry
