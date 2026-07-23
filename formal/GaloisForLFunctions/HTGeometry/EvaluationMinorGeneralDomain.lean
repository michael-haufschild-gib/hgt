import GaloisForLFunctions.HTGeometry.PrimeValuationProfileRankLaw
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Nonsingular evaluation minors over an arbitrary domain

A linearly independent family of scalar functions can always be separated by finitely many sample
points: there are points at which the evaluation matrix is nonsingular.

The corpus records this for sequences indexed by the naturals.  The argument never uses anything
about the index type, so it is restated here for an arbitrary domain.  That generality is what the
multi-row rank condition of the freeness predicate needs, where the samples are complex nodes rather
than natural coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ComplexOrder

noncomputable section

/-- **Nonsingular evaluation minor, general domain.**  A finite linearly independent family of
scalar functions on any domain admits pairwise distinct sample points whose evaluation matrix is
nonsingular. -/
theorem exists_injective_evaluation_minor_of_linearIndependent
    {J α : Type*} [Fintype J] [DecidableEq J]
    (u : J → α → ℂ) (hu : LinearIndependent ℂ u) :
    ∃ (e : J → α) (P : Matrix J J ℂ),
      Function.Injective e ∧ IsUnit P.det ∧
      ∀ r s, P r s = u s (e r) := by
  have hspan : Submodule.span ℂ (Set.range (flip u)) = ⊤ :=
    (span_flip_eq_top_iff_linearIndependent).2 hu
  obtain ⟨v, hvrange, _hvspan, hvLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range (flip u))
  have hfinrank : Module.finrank ℂ
      (Submodule.span ℂ (Set.range (flip u))) = Fintype.card J := by
    rw [hspan]
    simp [Module.finrank_fintype_fun_eq_card]
  let E : J ≃ Fin (Module.finrank ℂ
      (Submodule.span ℂ (Set.range (flip u)))) :=
    (Fintype.equivFin J).trans (finCongr hfinrank.symm)
  let w : J → (J → ℂ) := v ∘ E
  have hwrange : ∀ i, w i ∈ Set.range (flip u) := fun i => hvrange (E i)
  have hwLI : LinearIndependent ℂ w := hvLI.comp E E.injective
  choose e heval using hwrange
  have he : Function.Injective e := by
    intro i j hij
    apply hwLI.injective
    rw [← heval i, ← heval j, hij]
  let P : Matrix J J ℂ := Matrix.of fun r s => w r s
  have hProws : LinearIndependent ℂ P.row := by
    simpa only [P, Matrix.row, Matrix.of_apply] using hwLI
  obtain ⟨Q, hPQ⟩ := exists_matrix_rightInverse_of_linearIndependent_rows P hProws
  have hPdet : P.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hPQ
  refine ⟨e, P, he, isUnit_iff_ne_zero.mpr hPdet, ?_⟩
  intro r s
  change w r s = u s (e r)
  exact (congrFun (heval r) s).symm

/-- Column obtained by evaluating one member of a finite complex function family on a square sample
packet. -/
def finiteEvaluationColumn
    {J α : Type*} [Fintype J] (u : J → α → ℂ)
    (points : J → α) (j : J) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 fun row => u j (points row)

/-- Hermitian Gram matrix of a finite complex function family on a square sample packet. -/
def finiteEvaluationGram
    {J α : Type*} [Fintype J] (u : J → α → ℂ) (points : J → α) :
    Matrix J J ℂ :=
  Matrix.gram ℂ (finiteEvaluationColumn u points)

/-- **Finite evaluation Hilbert reconstruction, general domain.** One packet of pairwise distinct
samples simultaneously carries exact dual reconstruction, a positive-definite evaluation Gram,
and strictly positive Hilbert volume for every finite linearly independent complex function
family. -/
theorem exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
    {J α : Type*} [Fintype J] [DecidableEq J]
    (u : J → α → ℂ) (hu : LinearIndependent ℂ u) :
    ∃ (points : J → α) (dual : J → J → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0) ∧
      (∀ (a : J → ℂ) q,
        ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q) ∧
      (finiteEvaluationGram u points).PosDef ∧
      0 < (finiteEvaluationGram u points).det := by
  classical
  obtain ⟨points, P, hinj, hdet, hP⟩ :=
    exists_injective_evaluation_minor_of_linearIndependent u hu
  let dual : J → J → ℂ := fun q i => P⁻¹ q i
  have hdelta : ∀ q r, ∑ i, dual q i * u r (points i) =
      if q = r then 1 else 0 := by
    intro q r
    have hentry := congrArg (fun M : Matrix J J ℂ => M q r)
      (P.nonsing_inv_mul hdet)
    simpa [dual, Matrix.mul_apply, hP] using hentry
  have hrecovery : ∀ (a : J → ℂ) q,
      ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q := by
    intro a q
    calc
      ∑ i, dual q i * (∑ r, a r * u r (points i)) =
          ∑ i, ∑ r, dual q i * (a r * u r (points i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ r, ∑ i, dual q i * (a r * u r (points i)) :=
        Finset.sum_comm
      _ = ∑ r, a r * (∑ i, dual q i * u r (points i)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
      _ = ∑ r, a r * (if q = r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hdelta q r]
      _ = a q := by simp
  have hgram : (finiteEvaluationGram u points).PosDef := by
    apply Matrix.posDef_gram_of_linearIndependent
    have hcols : LinearIndependent ℂ P.col :=
      Matrix.linearIndependent_cols_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
    rw [Fintype.linearIndependent_iff] at hcols ⊢
    intro q hq
    apply hcols q
    funext row
    have hrow := congrArg (fun v : EuclideanSpace ℂ J => v row) hq
    simpa [finiteEvaluationColumn, Matrix.col_apply, Finset.sum_apply,
      Pi.smul_apply, hP] using hrow
  exact ⟨points, dual, hinj, hdelta, hrecovery, hgram, hgram.det_pos⟩

/-- Complete finite complex evaluation phase: one square packet has distinct nodes, exact dual
coefficient recovery, a positive-definite Hermitian Gram, and positive Hilbert volume. -/
def FiniteEvaluationHilbertReconstruction
    {J α : Type*} [Fintype J] [DecidableEq J] (u : J → α → ℂ) : Prop :=
  ∃ (points : J → α) (dual : J → J → ℂ),
    Function.Injective points ∧
    (∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0) ∧
    (∀ (a : J → ℂ) q,
      ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q) ∧
    (finiteEvaluationGram u points).PosDef ∧
    0 < (finiteEvaluationGram u points).det

/-- **Universal finite complex Hilbert reconstruction law.** Complete finite evaluation
reconstruction exists exactly for linearly independent complex function families. -/
theorem finiteEvaluationHilbertReconstruction_iff_linearIndependent
    {J α : Type*} [Fintype J] [DecidableEq J] (u : J → α → ℂ) :
    FiniteEvaluationHilbertReconstruction u ↔ LinearIndependent ℂ u := by
  constructor
  · rintro ⟨points, _dual, _hinj, _hdelta, _hrecovery, hgram, _hdet⟩
    have hcols : LinearIndependent ℂ (finiteEvaluationColumn u points) :=
      Matrix.posDef_gram_iff_linearIndependent.mp hgram
    rw [Fintype.linearIndependent_iff] at hcols ⊢
    intro c hc
    apply hcols c
    ext row
    have hrow := congrFun hc (points row)
    simpa [finiteEvaluationColumn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hrow
  · exact
      exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent u

/-- **Strict finite evaluation Gram, general domain.** A finite linearly independent complex
function family admits pairwise distinct sample points on which its literal evaluation Gram is
positive definite. -/
theorem exists_injective_finiteEvaluationGram_posDef_of_linearIndependent
    {J α : Type*} [Fintype J] [DecidableEq J]
    (u : J → α → ℂ) (hu : LinearIndependent ℂ u) :
    ∃ points : J → α, Function.Injective points ∧
      (finiteEvaluationGram u points).PosDef := by
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, hgram, _hdet⟩ :=
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent u hu
  exact ⟨points, hinj, hgram⟩

/-- Every strict finite evaluation Gram supplied by function independence has positive determinant,
hence full Hilbert volume. -/
theorem exists_injective_finiteEvaluationGram_det_pos_of_linearIndependent
    {J α : Type*} [Fintype J] [DecidableEq J]
    (u : J → α → ℂ) (hu : LinearIndependent ℂ u) :
    ∃ points : J → α, Function.Injective points ∧
      0 < (finiteEvaluationGram u points).det := by
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, _hgram, hdet⟩ :=
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent u hu
  exact ⟨points, hinj, hdet⟩

/-- **Complex unisolvent dual reconstruction, general domain.** A finite linearly independent
family of complex functions admits pairwise distinct sample points and dual weights that isolate
each feature and exactly recover every complex coefficient vector from its evaluation packet. -/
theorem exists_injective_evaluation_dualReconstruction_of_linearIndependent
    {J α : Type*} [Fintype J] [DecidableEq J]
    (u : J → α → ℂ) (hu : LinearIndependent ℂ u) :
    ∃ (e : J → α) (dual : J → J → ℂ),
      Function.Injective e ∧
      (∀ q r, ∑ i, dual q i * u r (e i) = if q = r then 1 else 0) ∧
      ∀ (a : J → ℂ) q,
        ∑ i, dual q i * (∑ r, a r * u r (e i)) = a q := by
  obtain ⟨e, dual, hinj, hdelta, hrecovery, _hgram, _hdet⟩ :=
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent u hu
  exact ⟨e, dual, hinj, hdelta, hrecovery⟩

end

end GaloisForLFunctions.HTGeometry
