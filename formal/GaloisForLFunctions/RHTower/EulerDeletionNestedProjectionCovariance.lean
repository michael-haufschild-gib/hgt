import GaloisForLFunctions.RHTower.EulerDeletionWeightedResidueProjection

/-!
# Nested-history covariance of the Euler-deletion drift

The chronological residue histories are nested.  Consequently, each cross-time covariance of
conditional residue predictors reduces exactly to an earlier predictor paired with the raw later
residue.  The resulting triangular covariance is the literal multi-prime quantity that must be
controlled; no periodic averaging, absolute value, or one-prime replacement occurs here.
-/

noncomputable section
set_option autoImplicit false

open Finset MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

/-- Orthogonal increment from one chronological history space to the next. -/
def historyLayer (i : ℕ) : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure :=
  (historySpace (i + 1)).starProjection - (historySpace i).starProjection

/-- A history layer kills every vector already measurable at its lower clock. -/
theorem historyLayer_apply_eq_zero_of_mem (i : ℕ) (v : Lp ℝ 2 cellMeasure)
    (hv : v ∈ historySpace i) :
    historyLayer i v = 0 := by
  change (historySpace (i + 1)).starProjection v -
    (historySpace i).starProjection v = 0
  have hvnext : v ∈ historySpace (i + 1) := historySpace_mono (by omega) hv
  rw [Submodule.starProjection_eq_self_iff.mpr hvnext,
    Submodule.starProjection_eq_self_iff.mpr hv, sub_self]

/-- A history layer passes unchanged through any later chronological projection. -/
theorem historyLayer_apply_starProjection_eq (i n : ℕ) (hin : i + 1 ≤ n)
    (v : Lp ℝ 2 cellMeasure) :
    historyLayer i ((historySpace n).starProjection v) = historyLayer i v := by
  change (historySpace (i + 1)).starProjection ((historySpace n).starProjection v) -
      (historySpace i).starProjection ((historySpace n).starProjection v) =
    (historySpace (i + 1)).starProjection v - (historySpace i).starProjection v
  have hnext : (historySpace (i + 1)).starProjection
      ((historySpace n).starProjection v) =
      (historySpace (i + 1)).starProjection v := by
    exact congrArg (fun f : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure => f v)
      (Submodule.starProjection_comp_starProjection_of_le (historySpace_mono hin))
  have hnow : (historySpace i).starProjection ((historySpace n).starProjection v) =
      (historySpace i).starProjection v := by
    exact congrArg (fun f : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure => f v)
      (Submodule.starProjection_comp_starProjection_of_le
        (historySpace_mono (Nat.le_trans (by omega) hin)))
  rw [hnext, hnow]

/-- Every history layer of the final drift is a reverse complete Möbius tail.  Earlier predictors
are annihilated and every later predictor reduces to its raw residue on that layer.  This retains
all simultaneous prime insertions in the tail. -/
theorem historyLayer_predictableDrift_eq_reverse_tail (l N : ℕ) :
    historyLayer l (predictableDrift N) =
      ∑ i ∈ range N, if l < i then
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
          historyLayer l (residueVec (i + 1)) else 0 := by
  unfold predictableDrift
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  by_cases hli : l < i
  · rw [if_pos hli, historyLayer_apply_starProjection_eq l i
      (Nat.succ_le_iff.mpr hli)]
  · rw [if_neg hli]
    have hil : i ≤ l := Nat.le_of_not_gt hli
    rw [historyLayer_apply_eq_zero_of_mem l
      ((historySpace i).starProjection (residueVec (i + 1)))
      (historySpace_mono hil (Submodule.starProjection_apply_mem _ _)), smul_zero]

/-- One chronological projection step is Pythagorean: the newly exposed history layer carries
exactly the difference of the two nested projections. -/
theorem history_projection_succ_norm_sq_eq_add_layer (i : ℕ)
    (v : Lp ℝ 2 cellMeasure) :
    ‖(historySpace (i + 1)).starProjection v‖ ^ 2 =
      ‖(historySpace i).starProjection v‖ ^ 2 + ‖historyLayer i v‖ ^ 2 := by
  have hcomp : (historySpace i).starProjection
      ((historySpace (i + 1)).starProjection v) =
      (historySpace i).starProjection v := by
    exact congrArg (fun f : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure => f v)
      (Submodule.starProjection_comp_starProjection_of_le (historySpace_mono (by omega)))
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection
    ((historySpace (i + 1)).starProjection v) (historySpace i)
  rw [Submodule.starProjection_orthogonal_val, hcomp] at hpyth
  change ‖(historySpace (i + 1)).starProjection v‖ ^ 2 =
    ‖(historySpace i).starProjection v‖ ^ 2 +
      ‖(historySpace (i + 1)).starProjection v - (historySpace i).starProjection v‖ ^ 2
  exact hpyth

/-- Projection onto a terminal chronological history decomposes into its base history and every
intermediate orthogonal layer. -/
theorem history_projection_norm_sq_eq_layer_sum (N : ℕ)
    (v : Lp ℝ 2 cellMeasure) :
    ‖(historySpace N).starProjection v‖ ^ 2 =
      ‖(historySpace 0).starProjection v‖ ^ 2 +
        ∑ i ∈ range N, ‖historyLayer i v‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      ‖(historySpace (N + 1)).starProjection v‖ ^ 2 =
          ‖(historySpace N).starProjection v‖ ^ 2 + ‖historyLayer N v‖ ^ 2 :=
        history_projection_succ_norm_sq_eq_add_layer N v
      _ = _ := by rw [ih, Finset.sum_range_succ]; ring

/-- Exact layer energy of the complete predictable drift. -/
theorem predictableDrift_norm_sq_eq_historyLayer_sum (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ i ∈ range N, ‖historyLayer i (predictableDrift N)‖ ^ 2 := by
  calc
    ‖predictableDrift N‖ ^ 2 =
        ‖(historySpace N).starProjection (predictableDrift N)‖ ^ 2 := by
      rw [Submodule.starProjection_eq_self_iff.mpr (predictableDrift_mem_historySpace N)]
    _ = _ := history_projection_norm_sq_eq_layer_sum N (predictableDrift N)

/-- Full EDQ layer decomposition.  The covariance energy is exactly the base-history mass plus
the positive sum of squared reverse tails, each retaining all later signed Möbius insertions. -/
theorem predictableDrift_norm_sq_eq_reverse_tail_layer_energy (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ l ∈ range N, ‖∑ i ∈ range N, if l < i then
          ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
            historyLayer l (residueVec (i + 1)) else 0‖ ^ 2 := by
  calc
    ‖predictableDrift N‖ ^ 2 =
        ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
          ∑ l ∈ range N, ‖historyLayer l (predictableDrift N)‖ ^ 2 :=
      predictableDrift_norm_sq_eq_historyLayer_sum N
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      rw [historyLayer_predictableDrift_eq_reverse_tail]

/-- For nested chronological histories, the cross covariance of two projected residues is the
pairing of the earlier projection with the raw later residue. -/
theorem nested_projected_residue_inner_eq_raw (i j : ℕ) (hij : i ≤ j) :
    inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
      ((historySpace j).starProjection (residueVec (j + 1))) =
      inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
        (residueVec (j + 1)) := by
  have hmem : (historySpace i).starProjection (residueVec (i + 1)) ∈ historySpace j :=
    historySpace_mono hij (Submodule.starProjection_apply_mem _ _)
  calc
    inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
        ((historySpace j).starProjection (residueVec (j + 1))) =
        inner ℝ ((historySpace j).starProjection
          ((historySpace i).starProjection (residueVec (i + 1))))
          (residueVec (j + 1)) :=
      (Submodule.inner_starProjection_left_eq_right (historySpace j)
        ((historySpace i).starProjection (residueVec (i + 1)))
        (residueVec (j + 1))).symm
    _ = _ := by rw [Submodule.starProjection_eq_self_iff.mpr hmem]

/-- Inserting the next chronological residue adds precisely its signed predictor to the drift. -/
theorem predictableDrift_succ (N : ℕ) :
    predictableDrift (N + 1) = predictableDrift N +
      ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) •
        (historySpace N).starProjection (residueVec (N + 1)) := by
  unfold predictableDrift
  rw [Finset.sum_range_succ]

/-- At every non-prime stage the Möbius-weighted predictor is exactly the raw residue.  This
retains every squarefree composite insertion; a vanishing Möbius coefficient covers the remaining
composites. -/
theorem signed_predictor_eq_raw_of_not_prime (n : ℕ) (hn : ¬ (n + 1).Prime) :
    ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) •
      (historySpace n).starProjection (residueVec (n + 1)) =
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) • residueVec (n + 1) := by
  have hzero := signedInnovation_eq_zero_of_not_prime n hn
  rw [signedInnovation, innovation, smul_sub, sub_eq_zero] at hzero
  exact hzero.symm

/-- A non-prime chronological insertion therefore changes the drift by its literal Möbius
residue, with no conditional approximation. -/
theorem predictableDrift_succ_eq_raw_of_not_prime (N : ℕ) (hN : ¬ (N + 1).Prime) :
    predictableDrift (N + 1) = predictableDrift N +
      ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) • residueVec (N + 1) := by
  rw [predictableDrift_succ, signed_predictor_eq_raw_of_not_prime N hN]

/-- The cross covariance of the accumulated drift and the next predictor is an exact triangular
sum over all earlier histories, with the later residue left unprojected. -/
theorem predictableDrift_cross_eq_earlier_raw_residue_sum (N : ℕ) :
    inner ℝ (predictableDrift N)
      ((historySpace N).starProjection (residueVec (N + 1))) =
      ∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
        inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
          (residueVec (N + 1)) := by
  unfold predictableDrift
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_left, nested_projected_residue_inner_eq_raw i N
    (Nat.le_of_lt (mem_range.mp hi))]
  simp

/-- Exact chronological drift-energy increment.  Its middle term is the complete signed
triangular multi-prime covariance, now expressed using raw later residues. -/
theorem predictableDrift_energy_succ_eq_nested_residue_covariance (N : ℕ) :
    ‖predictableDrift (N + 1)‖ ^ 2 = ‖predictableDrift N‖ ^ 2 +
      2 * ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) *
        (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
            (residueVec (N + 1))) +
      ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) ^ 2 *
        ‖(historySpace N).starProjection (residueVec (N + 1))‖ ^ 2 := by
  rw [predictableDrift_succ, norm_add_sq (𝕜 := ℝ), inner_smul_right,
    predictableDrift_cross_eq_earlier_raw_residue_sum, norm_smul, Real.norm_eq_abs]
  simp only [RCLike.re_to_real]
  rw [mul_pow, sq_abs]
  ring

end RHTower.DeletionResidueMartingale
