import Mathlib.Combinatorics.Configuration
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import GaloisForLFunctions.HTGeometry.IncidenceDesignBound
import GaloisForLFunctions.HTGeometry.IncidenceWeightedComplex

/-!
# Spectral gap for a finite projective plane

The rank-two spherical building over a finite field is its projective plane.  This module
instantiates the generic `2`-design incidence bound with that plane: its point-line graph has
spectral gap `1 - √q / (q + 1)`, where `q` is the cardinality of the field.

The proof uses Mathlib's projective-plane construction and cardinality theorem.  No spectrum is
postulated and no finite-field computation is evaluated.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset
open scoped LinearAlgebra.Projectivization

noncomputable section

variable {P L : Type*} [Membership P L]

local instance : DecidableEq P := Classical.decEq _
local instance : DecidableEq L := Classical.decEq _
local instance finiteProjectivizationFintype (K : Type*) [Field K] [Fintype K] :
    Fintype (ℙ K (Fin 3 → K)) := Fintype.ofFinite _

/-- Point-line incidence, viewed as a real-valued matrix. -/
noncomputable def projectiveIncidence : P → L → ℝ := by
  classical
  exact fun p l => if p ∈ l then 1 else 0

theorem projectiveIncidence_nonneg (p : P) (l : L) :
    0 ≤ projectiveIncidence (P := P) (L := L) p l := by
  simp only [projectiveIncidence]
  split_ifs <;> norm_num

/-- The point-to-line weight in the empty link of the incidence weighted complex is precisely the
projective-incidence matrix entry. This connects the rank-two spectral calculation to Garland's
weighted-complex interface. -/
theorem projectiveIncidence_linkGraph_empty_w_inl_inr [Fintype P] [Fintype L] (p : P) (l : L) :
    ((incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅).w (Sum.inl p) (Sum.inr l)
      = projectiveIncidence (P := P) (L := L) p l := by
  simpa only [projectiveIncidence] using incidenceWeightedComplex_linkGraph_empty_w_inl_inr p l

/-- The reverse point-line weight in the empty link has the same projective-incidence value. -/
theorem projectiveIncidence_linkGraph_empty_w_inr_inl [Fintype P] [Fintype L] (p : P) (l : L) :
    ((incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅).w (Sum.inr l) (Sum.inl p)
      = projectiveIncidence (P := P) (L := L) p l := by
  simpa only [projectiveIncidence] using incidenceWeightedComplex_linkGraph_empty_w_inr_inl p l

/-- The empty link of the projective-plane incidence complex is its full bipartite incidence graph. -/
theorem projectiveIncidence_linkGraph_empty_eq_incidenceGraph [Fintype P] [Fintype L] :
    (incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅ =
      incidenceGraph (projectiveIncidence (P := P) (L := L))
        (projectiveIncidence_nonneg (P := P) (L := L)) := by
  rw [incidenceWeightedComplex_linkGraph_empty_eq_incidenceGraph]
  ext u v
  cases u <;> cases v <;> simp [incidenceGraph, incW, projectiveIncidence]

theorem projectiveIncidence_row_sum [Fintype L] (p : P) :
    ∑ l, projectiveIncidence (P := P) (L := L) p l = (Configuration.lineCount L p : ℝ) := by
  classical
  change (∑ l : L, if p ∈ l then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype]
  simp [Configuration.lineCount, Nat.card_eq_fintype_card]

theorem projectiveIncidence_col_sum [Fintype P] (l : L) :
    ∑ p, projectiveIncidence (P := P) (L := L) p l = (Configuration.pointCount P l : ℝ) := by
  classical
  change (∑ p : P, if p ∈ l then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype]
  simp [Configuration.pointCount, Nat.card_eq_fintype_card]

/-- The point-line incidence matrix of any finite projective plane is a symmetric `2`-design. -/
theorem projectiveIncidence_design [Fintype P] [Fintype L] [Configuration.ProjectivePlane P L]
    (p p' : P) :
    (∑ l, projectiveIncidence (P := P) (L := L) p l
      * projectiveIncidence (P := P) (L := L) p' l)
      = if p = p' then (Configuration.ProjectivePlane.order P L : ℝ) + 1 else 1 := by
  classical
  by_cases hpp : p = p'
  · subst p'
    have hsq : ∀ l : L, projectiveIncidence (P := P) (L := L) p l
        * projectiveIncidence (P := P) (L := L) p l
        = projectiveIncidence (P := P) (L := L) p l := by
      intro l
      simp [projectiveIncidence]
    rw [if_pos rfl, Finset.sum_congr rfl fun l _ => hsq l, projectiveIncidence_row_sum,
      Configuration.ProjectivePlane.lineCount_eq]
    norm_num
  · obtain ⟨l₀, hl₀, huniq⟩ :=
      Configuration.HasLines.existsUnique_line (P := P) (L := L) p p' hpp
    have hterm : ∀ l : L, projectiveIncidence (P := P) (L := L) p l
        * projectiveIncidence (P := P) (L := L) p' l = if l = l₀ then 1 else 0 := by
      intro l
      by_cases hl : l = l₀
      · subst l
        simp [projectiveIncidence, hl₀]
      · have hboth : ¬(p ∈ l ∧ p' ∈ l) := fun hboth => hl (huniq l hboth)
        by_cases hp : p ∈ l
        · have hp' : p' ∉ l := fun hp' => hboth ⟨hp, hp'⟩
          simp [projectiveIncidence, hp, hp', hl]
        · simp [projectiveIncidence, hp, hl]
    rw [if_neg hpp]
    simp_rw [hterm]
    simp

/-- The point-line graph of any finite projective plane has its design spectral gap. -/
theorem projectivePlane_incidenceGraph_hasSpectralGap
    [Fintype P] [Fintype L] [Configuration.ProjectivePlane P L] :
    (incidenceGraph (projectiveIncidence (P := P) (L := L))
      (projectiveIncidence_nonneg (P := P) (L := L))).HasSpectralGap
      (1 - Real.sqrt (((Configuration.ProjectivePlane.order P L : ℝ) + 1) - 1)
        / ((Configuration.ProjectivePlane.order P L : ℝ) + 1)) := by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ :=
    Configuration.ProjectivePlane.exists_config (P := P) (L := L)
  letI : Nonempty P := ⟨p₁⟩
  apply incidenceGraph_hasSpectralGap (projectiveIncidence (P := P) (L := L))
    (projectiveIncidence_nonneg (P := P) (L := L))
    ((Configuration.ProjectivePlane.order P L : ℝ) + 1) 1
  · positivity
  · have hq : (0 : ℝ) ≤ (Configuration.ProjectivePlane.order P L : ℝ) := Nat.cast_nonneg _
    linarith
  · exact Configuration.ProjectivePlane.card_points_eq_card_lines P L
  · intro p
    rw [projectiveIncidence_row_sum, Configuration.ProjectivePlane.lineCount_eq]
    norm_num
  · intro l
    rw [projectiveIncidence_col_sum, Configuration.ProjectivePlane.pointCount_eq]
    norm_num
  · intro p p'
    exact projectiveIncidence_design (P := P) (L := L) p p'

/-- Garland's empty-link graph for a finite projective plane has the projective-plane design gap. -/
theorem projectivePlane_incidenceWeightedComplex_linkGraph_empty_hasSpectralGap
    [Fintype P] [Fintype L] [Configuration.ProjectivePlane P L] :
    ((incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅).HasSpectralGap
      (1 - Real.sqrt (((Configuration.ProjectivePlane.order P L : ℝ) + 1) - 1)
        / ((Configuration.ProjectivePlane.order P L : ℝ) + 1)) := by
  rw [projectiveIncidence_linkGraph_empty_eq_incidenceGraph]
  exact projectivePlane_incidenceGraph_hasSpectralGap (P := P) (L := L)

theorem finiteField_projectivePlane_card {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    Nat.card (ℙ K (Fin 3 → K)) = Nat.card K ^ 2 + Nat.card K + 1 := by
  rw [Projectivization.card_of_finrank K (Fin 3 → K) (Module.finrank_fin_fun K)]
  norm_num [Finset.sum_range_succ]
  omega

theorem nat_sq_add_injective {a b : ℕ} (h : a ^ 2 + a = b ^ 2 + b) : a = b := by
  apply le_antisymm
  · by_contra hab
    have hba : b < a := Nat.lt_of_not_ge hab
    have hsq : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hba (by omega)
    omega
  · by_contra hba
    have hab : a < b := Nat.lt_of_not_ge hba
    have hsq : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by omega)
    omega

/-- The order of the projective plane over a finite field is its field cardinality. -/
theorem finiteField_projectivePlane_order {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    Configuration.ProjectivePlane.order (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) = Nat.card K := by
  letI : Fintype (ℙ K (Fin 3 → K)) := Fintype.ofFinite _
  apply nat_sq_add_injective
  have hplane := Configuration.ProjectivePlane.card_points
    (P := ℙ K (Fin 3 → K)) (L := ℙ K (Fin 3 → K))
  rw [← Nat.card_eq_fintype_card] at hplane
  rw [finiteField_projectivePlane_card] at hplane
  omega

/-- The rank-two spherical building over a finite field of cardinality `q` has gap
`1 - √q / (q + 1)`. -/
theorem finiteField_projectivePlane_incidenceGraph_hasSpectralGap
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    (incidenceGraph
      (projectiveIncidence (P := ℙ K (Fin 3 → K)) (L := ℙ K (Fin 3 → K)))
      (projectiveIncidence_nonneg (P := ℙ K (Fin 3 → K)) (L := ℙ K (Fin 3 → K)))).HasSpectralGap
      (1 - Real.sqrt (Nat.card K : ℝ) / ((Nat.card K : ℝ) + 1)) := by
  simpa only [finiteField_projectivePlane_order, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right] using
    projectivePlane_incidenceGraph_hasSpectralGap
      (P := ℙ K (Fin 3 → K)) (L := ℙ K (Fin 3 → K))

/-- The rank-two spherical-building gap in the `WeightedComplex` link interface. -/
theorem finiteField_projectivePlane_incidenceWeightedComplex_linkGraph_empty_hasSpectralGap
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    WeightedGraph.HasSpectralGap
      ((incidenceWeightedComplex (P := ℙ K (Fin 3 → K)) (L := ℙ K (Fin 3 → K))).linkGraph ∅)
      (1 - Real.sqrt (Nat.card K : ℝ) / ((Nat.card K : ℝ) + 1)) := by
  rw [projectiveIncidence_linkGraph_empty_eq_incidenceGraph]
  exact finiteField_projectivePlane_incidenceGraph_hasSpectralGap

/-- For `q ≥ 7`, the rank-two spherical-building gap is strictly above Garland's `2 / 3`
threshold. -/
theorem finiteField_projectivePlane_gap_gt_two_thirds
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (hK : 7 ≤ Nat.card K) :
    (2 : ℝ) / 3 < 1 - Real.sqrt (Nat.card K : ℝ) / ((Nat.card K : ℝ) + 1) := by
  have hq : (7 : ℝ) ≤ (Nat.card K : ℝ) := by exact_mod_cast hK
  have hq0 : 0 ≤ (Nat.card K : ℝ) := by linarith
  have hq1 : 0 < (Nat.card K : ℝ) + 1 := by linarith
  have hsqrt : Real.sqrt (Nat.card K : ℝ) ^ 2 = (Nat.card K : ℝ) := Real.sq_sqrt hq0
  have hsq : (3 * Real.sqrt (Nat.card K : ℝ)) ^ 2 < ((Nat.card K : ℝ) + 1) ^ 2 := by
    nlinarith
  have hroot : 3 * Real.sqrt (Nat.card K : ℝ) < (Nat.card K : ℝ) + 1 :=
    (sq_lt_sq₀ (by positivity) (by linarith)).mp hsq
  have hfrac : Real.sqrt (Nat.card K : ℝ) / ((Nat.card K : ℝ) + 1) < (1 : ℝ) / 3 :=
    (div_lt_iff₀ hq1).2 (by nlinarith)
  nlinarith

end

end GaloisForLFunctions.HTGeometry
