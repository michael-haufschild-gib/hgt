import GaloisForLFunctions.HTGeometry.ArithmeticTemporalRankInstability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Baire.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Topology and measure of the rational-rank strata

A packet of `n` real coordinates fails to have maximal rational rank exactly when it satisfies one
nonzero rational linear relation.  The relation loci form a countable family of proper closed
hyperplanes, so every non-maximal stratum is meagre and Lebesgue null, while the maximal stratum is
residual and conull.  Density of the rank-one stratum nevertheless leaves the maximal stratum with
empty interior: typicality by category and by measure does not make maximal rational rank open.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- The real linear functional attached to a rational coefficient packet. -/
def ratFunctional (c : Fin n → ℚ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun ω := ∑ i, (c i : ℝ) * ω i
  map_add' ω ω' := by
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' a ω := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem ratFunctional_apply (c : Fin n → ℚ) (ω : Fin n → ℝ) :
    ratFunctional c ω = ∑ i, (c i : ℝ) * ω i := rfl

/-- The rational hyperplane cut out by a rational coefficient packet. -/
def ratHyperplane (c : Fin n → ℚ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (ratFunctional c)

@[simp] theorem mem_ratHyperplane {c : Fin n → ℚ} {ω : Fin n → ℝ} :
    ω ∈ ratHyperplane c ↔ ∑ i, (c i : ℝ) * ω i = 0 := Iff.rfl

/-- A nonzero rational packet cuts out a proper hyperplane. -/
theorem ratHyperplane_ne_top {c : Fin n → ℚ} (hc : c ≠ 0) : ratHyperplane c ≠ ⊤ := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext hcon)
  intro htop
  have hmem : (Pi.single i₀ (1 : ℝ)) ∈ ratHyperplane c := by
    rw [htop]; trivial
  rw [mem_ratHyperplane] at hmem
  rw [Finset.sum_eq_single i₀] at hmem
  · simp only [Pi.single_eq_same, mul_one] at hmem
    exact hi₀ (by exact_mod_cast hmem)
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hcon
    exact absurd (Finset.mem_univ i₀) hcon

theorem isClosed_ratHyperplane (c : Fin n → ℚ) :
    IsClosed (ratHyperplane c : Set (Fin n → ℝ)) :=
  Submodule.closed_of_finiteDimensional _

theorem interior_ratHyperplane_eq_empty {c : Fin n → ℚ} (hc : c ≠ 0) :
    interior (ratHyperplane c : Set (Fin n → ℝ)) = ∅ := by
  by_contra hcon
  exact ratHyperplane_ne_top hc
    (Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.mpr hcon))

theorem isNowhereDense_ratHyperplane {c : Fin n → ℚ} (hc : c ≠ 0) :
    IsNowhereDense (ratHyperplane c : Set (Fin n → ℝ)) := by
  show interior (closure (ratHyperplane c : Set (Fin n → ℝ))) = ∅
  rw [(isClosed_ratHyperplane c).closure_eq]
  exact interior_ratHyperplane_eq_empty hc

theorem volume_ratHyperplane_eq_zero {c : Fin n → ℚ} (hc : c ≠ 0) :
    volume (ratHyperplane c : Set (Fin n → ℝ)) = 0 :=
  Measure.addHaar_submodule volume _ (ratHyperplane_ne_top hc)

/-- Maximal rational rank is exactly rational linear independence of the packet. -/
theorem rationalCoordinateRank_eq_iff_linearIndependent (ω : Fin n → ℝ) :
    rationalCoordinateRank ω = n ↔ LinearIndependent ℚ ω := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- A packet of non-maximal rational rank satisfies a nonzero rational linear relation. -/
theorem exists_ratHyperplane_of_rank_ne {ω : Fin n → ℝ}
    (hne : rationalCoordinateRank ω ≠ n) :
    ∃ c : Fin n → ℚ, c ≠ 0 ∧ ω ∈ ratHyperplane c := by
  have hnli : ¬ LinearIndependent ℚ ω := by
    intro hli
    exact hne ((rationalCoordinateRank_eq_iff_linearIndependent ω).mpr hli)
  obtain ⟨g, hsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hnli
  refine ⟨g, ?_, ?_⟩
  · intro hzero
    exact hi₀ (by rw [hzero]; rfl)
  · rw [mem_ratHyperplane]
    simpa only [Rat.smul_def] using hsum

/-- The non-maximal rational-rank locus is covered by the countable family of nonzero rational
hyperplanes. -/
theorem subMaximalRank_subset_iUnion :
    {ω : Fin n → ℝ | rationalCoordinateRank ω ≠ n} ⊆
      ⋃ c : {c : Fin n → ℚ // c ≠ 0}, (ratHyperplane c.1 : Set (Fin n → ℝ)) := by
  intro ω hω
  obtain ⟨c, hc, hmem⟩ := exists_ratHyperplane_of_rank_ne hω
  exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hmem⟩

/-- The non-maximal rational-rank locus is meagre. -/
theorem isMeagre_subMaximalRank :
    IsMeagre {ω : Fin n → ℝ | rationalCoordinateRank ω ≠ n} :=
  IsMeagre.mono subMaximalRank_subset_iUnion
    (isMeagre_iUnion fun c => (isNowhereDense_ratHyperplane c.2).isMeagre)

/-- The non-maximal rational-rank locus is Lebesgue null. -/
theorem volume_subMaximalRank_eq_zero :
    volume {ω : Fin n → ℝ | rationalCoordinateRank ω ≠ n} = 0 :=
  measure_mono_null subMaximalRank_subset_iUnion
    (measure_iUnion_null fun c => volume_ratHyperplane_eq_zero c.2)

/-- Every stratum of rank below the maximum is meagre. -/
theorem isMeagre_exactRationalRank {k : ℕ} (hk : k ≠ n) :
    IsMeagre {ω : Fin n → ℝ | rationalCoordinateRank ω = k} :=
  IsMeagre.mono (fun ω hω => by
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω]
    exact hk) isMeagre_subMaximalRank

/-- Every stratum of rank below the maximum is Lebesgue null. -/
theorem volume_exactRationalRank_eq_zero {k : ℕ} (hk : k ≠ n) :
    volume {ω : Fin n → ℝ | rationalCoordinateRank ω = k} = 0 :=
  measure_mono_null (fun ω hω => by
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω]
    exact hk) volume_subMaximalRank_eq_zero

/-- The maximal rational-rank locus is residual. -/
theorem residual_maximalRationalRank :
    {ω : Fin n → ℝ | rationalCoordinateRank ω = n} ∈ residual (Fin n → ℝ) := by
  have hcompl : {ω : Fin n → ℝ | rationalCoordinateRank ω = n}ᶜ =
      {ω : Fin n → ℝ | rationalCoordinateRank ω ≠ n} := rfl
  have := isMeagre_subMaximalRank (n := n)
  rwa [IsMeagre, ← hcompl, compl_compl] at this

/-- The maximal rational-rank locus is conull. -/
theorem volume_compl_maximalRationalRank_eq_zero :
    volume {ω : Fin n → ℝ | rationalCoordinateRank ω = n}ᶜ = 0 :=
  volume_subMaximalRank_eq_zero

/-- From two coordinates onward the maximal rational-rank locus has empty interior: the rank-one
locus is dense and disjoint from it. -/
theorem interior_maximalRationalRank_eq_empty (hn : 2 ≤ n) :
    interior {ω : Fin n → ℝ | rationalCoordinateRank ω = n} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  refine Dense.mono ?_ (dense_exactRationalRank (n := n) (k := 1) one_pos (by omega))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hω]
  omega

/-- **Rational-rank stratum dichotomy.**  Maximal rational rank is simultaneously residual, conull
and nowhere locally constant; every lower stratum is dense, meagre and null. -/
theorem rationalRank_stratum_dichotomy (hn : 2 ≤ n) :
    ({ω : Fin n → ℝ | rationalCoordinateRank ω = n} ∈ residual (Fin n → ℝ)) ∧
      volume {ω : Fin n → ℝ | rationalCoordinateRank ω = n}ᶜ = 0 ∧
      interior {ω : Fin n → ℝ | rationalCoordinateRank ω = n} = ∅ ∧
      ∀ k : ℕ, 0 < k → k ≤ n → k ≠ n →
        Dense {ω : Fin n → ℝ | rationalCoordinateRank ω = k} ∧
          IsMeagre {ω : Fin n → ℝ | rationalCoordinateRank ω = k} ∧
          volume {ω : Fin n → ℝ | rationalCoordinateRank ω = k} = 0 :=
  ⟨residual_maximalRationalRank, volume_compl_maximalRationalRank_eq_zero,
    interior_maximalRationalRank_eq_empty hn,
    fun _ hk hkn hkne =>
      ⟨dense_exactRationalRank hk hkn, isMeagre_exactRationalRank hkne,
        volume_exactRationalRank_eq_zero hkne⟩⟩

end

end GaloisForLFunctions.HTGeometry
