import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Compactness.Compact

/-!
# Positive Hilbert-cube embeddings in finite constraint fibers

This module formalizes the topological and Banach-space core of the finite-frame aperture in the
cofinal Cholesky paper.  A uniformly bounded biorthogonal sequence of constraint-kernel directions
produces an affine, closed topological embedding of the signed Hilbert cube.  Geometric weighting
makes the series uniformly convergent, and every point of the embedded cube satisfies exactly the
same finite continuous-linear constraints as the base point.

The later measure module must construct the biorthogonal kernel directions from disjoint positive
blocks of an atomless parameter law and prove positivity of the resulting weights.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set
open scoped Topology

noncomputable section

/-- The signed Hilbert cube `[-1,1]^ℕ` with its product topology. -/
abbrev SignedHilbertCube := ∀ _n : ℕ, Set.Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Geometric coefficient used in the positive aperture series. -/
noncomputable def hilbertCubeWeight (delta : ℝ) (n : ℕ) : ℝ :=
  delta / 2 / 2 ^ n

/-- Geometrically weighted Hilbert-cube series in a Banach space. -/
noncomputable def positiveHilbertCubeMap (delta : ℝ) (v : ℕ → E)
    (t : SignedHilbertCube) : E :=
  ∑' n : ℕ, (hilbertCubeWeight delta n * (t n : ℝ)) • v n

theorem hilbertCubeWeight_summable (delta : ℝ) :
    Summable (hilbertCubeWeight delta) := by
  simpa [hilbertCubeWeight] using summable_geometric_two' delta

lemma signedHilbertCube_abs_le_one (t : SignedHilbertCube) (n : ℕ) :
    |(t n : ℝ)| ≤ 1 := by
  rcases (t n).2 with ⟨hl, hr⟩
  rw [abs_le]
  exact ⟨hl, hr⟩

omit [CompleteSpace E] in
/-- Every summand is bounded by its geometric majorant. -/
lemma positiveHilbertCube_term_norm_le
    {delta : ℝ} (hdelta : 0 ≤ delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1)
    (t : SignedHilbertCube) (n : ℕ) :
    ‖(hilbertCubeWeight delta n * (t n : ℝ)) • v n‖ ≤ hilbertCubeWeight delta n := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have hw : 0 ≤ hilbertCubeWeight delta n := by
    dsimp [hilbertCubeWeight]
    positivity
  rw [abs_of_nonneg hw]
  have ht := signedHilbertCube_abs_le_one t n
  have hvn := hv n
  have hwa : hilbertCubeWeight delta n * |(t n : ℝ)| ≤ hilbertCubeWeight delta n := by
    simpa using mul_le_mul_of_nonneg_left ht hw
  have hwanonneg : 0 ≤ hilbertCubeWeight delta n * |(t n : ℝ)| :=
    mul_nonneg hw (abs_nonneg _)
  calc
    hilbertCubeWeight delta n * |(t n : ℝ)| * ‖v n‖ ≤
        hilbertCubeWeight delta n * |(t n : ℝ)| * 1 :=
      mul_le_mul_of_nonneg_left hvn hwanonneg
    _ ≤ hilbertCubeWeight delta n * 1 := mul_le_mul_of_nonneg_right hwa zero_le_one
    _ = hilbertCubeWeight delta n := mul_one _

theorem summable_positiveHilbertCube_terms
    {delta : ℝ} (hdelta : 0 ≤ delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1)
    (t : SignedHilbertCube) :
    Summable (fun n : ℕ => (hilbertCubeWeight delta n * (t n : ℝ)) • v n) :=
  (hilbertCubeWeight_summable delta).of_norm_bounded
    (positiveHilbertCube_term_norm_le hdelta hv t)

omit [CompleteSpace E] in
/-- The whole perturbation has norm at most `delta`. -/
theorem norm_positiveHilbertCubeMap_le
    {delta : ℝ} (hdelta : 0 ≤ delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1)
    (t : SignedHilbertCube) :
    ‖positiveHilbertCubeMap delta v t‖ ≤ delta := by
  let f : ℕ → E := fun n => (hilbertCubeWeight delta n * (t n : ℝ)) • v n
  have hbound : ∀ n, ‖f n‖ ≤ hilbertCubeWeight delta n :=
    positiveHilbertCube_term_norm_le hdelta hv t
  have hnormsumm : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hilbertCubeWeight_summable delta)
  calc
    ‖positiveHilbertCubeMap delta v t‖ = ‖∑' n, f n‖ := rfl
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hnormsumm
    _ ≤ ∑' n, hilbertCubeWeight delta n :=
      hnormsumm.tsum_le_tsum hbound (hilbertCubeWeight_summable delta)
    _ = delta := tsum_geometric_two' delta

/-- The geometrically weighted Hilbert-cube series is continuous for the product topology. -/
theorem continuous_positiveHilbertCubeMap
    {delta : ℝ} (hdelta : 0 ≤ delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1) :
    Continuous (positiveHilbertCubeMap delta v) := by
  apply continuous_tsum
  · intro n
    fun_prop
  · exact hilbertCubeWeight_summable delta
  · intro n t
    exact positiveHilbertCube_term_norm_le hdelta hv t n

/-- A biorthogonal decoder makes the Hilbert-cube series injective. -/
theorem positiveHilbertCubeMap_injective
    {delta : ℝ} (hdelta : 0 < delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1)
    (ell : ℕ → E →L[ℝ] ℝ)
    (hbio : ∀ n m, ell n (v m) = if n = m then 1 else 0) :
    Function.Injective (positiveHilbertCubeMap delta v) := by
  intro s t hst
  funext n
  apply Subtype.ext
  have hsummS := summable_positiveHilbertCube_terms hdelta.le hv s
  have hsummT := summable_positiveHilbertCube_terms hdelta.le hv t
  have hell := congrArg (ell n) hst
  simp only [positiveHilbertCubeMap] at hell
  rw [(ell n).map_tsum hsummS, (ell n).map_tsum hsummT] at hell
  simp_rw [map_smul, hbio, smul_eq_mul] at hell
  rw [tsum_eq_single n, tsum_eq_single n] at hell
  · simp only [if_pos, mul_one] at hell
    have hw : hilbertCubeWeight delta n ≠ 0 := by
      dsimp [hilbertCubeWeight]
      positivity
    exact mul_left_cancel₀ hw hell
  · intro m hmn
    simp [Ne.symm hmn]
  · intro m hmn
    simp [Ne.symm hmn]

/-- The unshifted series is a closed topological embedding of the Hilbert cube. -/
theorem positiveHilbertCubeMap_isClosedEmbedding
    {delta : ℝ} (hdelta : 0 < delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1)
    (ell : ℕ → E →L[ℝ] ℝ)
    (hbio : ∀ n m, ell n (v m) = if n = m then 1 else 0) :
    Topology.IsClosedEmbedding (positiveHilbertCubeMap delta v) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_positiveHilbertCubeMap hdelta.le hv
  · exact positiveHilbertCubeMap_injective hdelta hv ell hbio
  · exact (continuous_positiveHilbertCubeMap hdelta.le hv).isClosedMap

/-- Affine Hilbert-cube aperture centered at `base`. -/
noncomputable def affinePositiveHilbertCubeMap (base : E) (delta : ℝ) (v : ℕ → E)
    (t : SignedHilbertCube) : E :=
  base + positiveHilbertCubeMap delta v t

theorem continuous_affinePositiveHilbertCubeMap
    (base : E) {delta : ℝ} (hdelta : 0 ≤ delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1) :
    Continuous (affinePositiveHilbertCubeMap base delta v) :=
  continuous_const.add (continuous_positiveHilbertCubeMap hdelta hv)

theorem affinePositiveHilbertCubeMap_injective
    (base : E) {delta : ℝ} (hdelta : 0 < delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1)
    (ell : ℕ → E →L[ℝ] ℝ)
    (hbio : ∀ n m, ell n (v m) = if n = m then 1 else 0) :
    Function.Injective (affinePositiveHilbertCubeMap base delta v) := by
  intro s t h
  apply positiveHilbertCubeMap_injective hdelta hv ell hbio
  exact add_left_cancel h

/-- Every point in the affine cube has exactly the same finite continuous-linear constraints as
the base point when all directions lie in the constraint kernel. -/
theorem affinePositiveHilbertCubeMap_constraint_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (base : E) {delta : ℝ} (hdelta : 0 ≤ delta)
    {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1) (hvker : ∀ n, T (v n) = 0)
    (t : SignedHilbertCube) :
    T (affinePositiveHilbertCubeMap base delta v t) = T base := by
  rw [affinePositiveHilbertCubeMap, map_add]
  have hsumm := summable_positiveHilbertCube_terms hdelta hv t
  rw [positiveHilbertCubeMap, T.map_tsum hsumm]
  simp only [map_smul, hvker, smul_zero, tsum_zero, add_zero]

/-- The affine aperture is a closed topological embedding. -/
theorem affinePositiveHilbertCubeMap_isClosedEmbedding
    (base : E) {delta : ℝ} (hdelta : 0 < delta) {v : ℕ → E} (hv : ∀ n, ‖v n‖ ≤ 1)
    (ell : ℕ → E →L[ℝ] ℝ)
    (hbio : ∀ n m, ell n (v m) = if n = m then 1 else 0) :
    Topology.IsClosedEmbedding (affinePositiveHilbertCubeMap base delta v) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_affinePositiveHilbertCubeMap base hdelta.le hv
  · exact affinePositiveHilbertCubeMap_injective base hdelta hv ell hbio
  · exact (continuous_affinePositiveHilbertCubeMap base hdelta.le hv).isClosedMap

end

end GaloisForLFunctions.HTGeometry
