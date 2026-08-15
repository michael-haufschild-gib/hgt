import GaloisForLFunctions.HTGeometry.ComplexAffineLinePolynomialAvoidance

/-!
# Generic one-knob lines through a coordinate splitting

Split the coordinates of a polynomial parameter space into a background block and a direction
block.  A background in the first block together with a direction in the second block spans a line
whose parameter multiplies only the direction block.

Restricting a nonzero polynomial to such a line gives a one-variable polynomial that is nonzero for
almost every pair, because the value at line parameter one is the merged point and merging is a
measure-preserving equivalence.  A countable family of nonzero obstructions therefore fails only on
a countable set of line parameters.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section BlockLine

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- The point of the parameter space at line parameter `g`: the background block is fixed and the
direction block is scaled. -/
def blockPoint (v : {i : Fin n // p i} → ℝ) (a : {i : Fin n // ¬ p i} → ℝ) (g : ℝ) :
    Fin n → ℝ :=
  fun i => if h : p i then g * v ⟨i, h⟩ else a ⟨i, h⟩

/-- Restriction of a real multivariate polynomial to a one-knob line. -/
def blockLineRestriction (v : {i : Fin n // p i} → ℝ) (a : {i : Fin n // ¬ p i} → ℝ)
    (P : MvPolynomial (Fin n) ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => if h : p i then Polynomial.X * Polynomial.C (v ⟨i, h⟩)
      else Polynomial.C (a ⟨i, h⟩)) P

theorem eval_blockLineRestriction (v : {i : Fin n // p i} → ℝ) (a : {i : Fin n // ¬ p i} → ℝ)
    (P : MvPolynomial (Fin n) ℝ) (g : ℝ) :
    Polynomial.eval g (blockLineRestriction p v a P) =
      MvPolynomial.eval (blockPoint p v a g) P := by
  rw [blockLineRestriction, MvPolynomial.polynomial_eval_eval₂]
  have hcomp : (Polynomial.evalRingHom g).comp Polynomial.C = RingHom.id ℝ := by
    ext x
    simp
  rw [hcomp]
  change
    MvPolynomial.eval₂ (RingHom.id ℝ)
        (fun s => Polynomial.eval g
          (if h : p s then Polynomial.X * Polynomial.C (v ⟨s, h⟩)
            else Polynomial.C (a ⟨s, h⟩))) P =
      MvPolynomial.eval₂ (RingHom.id ℝ) (blockPoint p v a g) P
  apply MvPolynomial.eval₂_congr
  intro i c _ _
  by_cases h : p i
  · simp only [blockPoint, dif_pos h, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
  · simp [blockPoint, h]

theorem blockPoint_one (v : {i : Fin n // p i} → ℝ) (a : {i : Fin n // ¬ p i} → ℝ) :
    blockPoint p v a 1 =
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p).symm (v, a) := by
  funext i
  by_cases h : p i <;> simp [blockPoint, h, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd]

/-- Almost every one-knob line has a nonzero restriction of a fixed nonzero polynomial. -/
theorem blockLineRestriction_ne_zero_ae {P : MvPolynomial (Fin n) ℝ} (hP : P ≠ 0) :
    ∀ᵐ va : ({i : Fin n // p i} → ℝ) × ({i : Fin n // ¬ p i} → ℝ) ∂volume,
      blockLineRestriction p va.1 va.2 P ≠ 0 := by
  classical
  set Z : Set (Fin n → ℝ) := {x | MvPolynomial.eval x P = 0} with hZdef
  have hZ : volume Z = 0 := by
    simpa [hZdef] using mvPolynomial_zero_set_volume_real_fin n P hP
  have hZm : MeasurableSet Z :=
    isClosed_singleton.preimage P.continuous_eval |>.measurableSet
  have hmp : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p).symm volume volume :=
    (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p).symm _
  have hnull : volume
      ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p).symm ⁻¹' Z) = 0 := by
    rw [hmp.measure_preimage hZm.nullMeasurableSet, hZ]
  rw [ae_iff]
  refine measure_mono_null (t :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p).symm ⁻¹' Z) ?_ hnull
  intro va hva
  simp only [Set.mem_setOf_eq, ne_eq, not_not] at hva
  have heval : Polynomial.eval 1 (blockLineRestriction p va.1 va.2 P) = 0 := by
    rw [hva]
    simp
  rw [eval_blockLineRestriction, blockPoint_one] at heval
  exact heval

/-- **Countable one-knob avoidance.**  For almost every background and direction, countably many
nonzero polynomial obstructions fail only on a countable set of coupling strengths. -/
theorem countable_blockLineAvoidance_ae (P : ℕ → MvPolynomial (Fin n) ℝ) (hP : ∀ r, P r ≠ 0) :
    ∀ᵐ va : ({i : Fin n // p i} → ℝ) × ({i : Fin n // ¬ p i} → ℝ) ∂volume,
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, ∀ r, MvPolynomial.eval (blockPoint p va.1 va.2 g) (P r) ≠ 0 := by
  have hall : ∀ᵐ va : ({i : Fin n // p i} → ℝ) × ({i : Fin n // ¬ p i} → ℝ) ∂volume,
      ∀ r, blockLineRestriction p va.1 va.2 (P r) ≠ 0 :=
    ae_all_iff.2 fun r => blockLineRestriction_ne_zero_ae p (hP r)
  filter_upwards [hall] with va hva
  refine ⟨{g : ℝ | ∃ r, (blockLineRestriction p va.1 va.2 (P r)).IsRoot g},
    countable_setOf_exists_polynomial_isRoot _ hva, ?_⟩
  intro g hg r heval
  exact hg ⟨r, by
    change Polynomial.eval g (blockLineRestriction p va.1 va.2 (P r)) = 0
    rw [eval_blockLineRestriction]
    exact heval⟩

/-- **Countable one-knob avoidance for complex obstructions.** -/
theorem countable_complexBlockLineAvoidance_ae (Q : ℕ → MvPolynomial (Fin n) ℂ)
    (hQ : ∀ r, Q r ≠ 0) :
    ∀ᵐ va : ({i : Fin n // p i} → ℝ) × ({i : Fin n // ¬ p i} → ℝ) ∂volume,
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, ∀ r, MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => ((blockPoint p va.1 va.2 g i : ℝ) : ℂ)) (Q r) ≠ 0 := by
  have hshadow : ∀ r, mvPolynomialRealShadow (Q r) ≠ 0 := fun r =>
    mvPolynomialRealShadow_ne_zero (hQ r)
  filter_upwards [countable_blockLineAvoidance_ae p
    (fun r => mvPolynomialRealShadow (Q r)) hshadow] with va hva
  obtain ⟨C, hC, hgC⟩ := hva
  refine ⟨C, hC, fun g hg r => ?_⟩
  exact eval₂_ne_zero_of_eval_mvPolynomialRealShadow_ne_zero (hgC g hg r)

end BlockLine

end

end GaloisForLFunctions.HTGeometry
