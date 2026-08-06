import GaloisForLFunctions.RHTower.DivisorReesEulerContinuation

/-!
# The canonical boundary graph of a compact region

The boundary-graph theorems apply to any finite family of spectral points.  A compact region of the
continuation determines such a family canonically: its vertices are the zeros of `xi` inside the
region, which are finite in number because the divisor is discrete.

This makes the relative trace a function of the region alone.  It counts the zeros there — each one
contributing a single unit whatever its multiplicity — it grows with the region, and it vanishes on
any region contained in the Euler chamber or in its reflection.  The four-unit budget on a region
is therefore literally the statement that the region contains at most four zeros.
-/

open scoped BigOperators Matrix

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ### The canonical vertex set -/

/-- The zeros of `xi` in a closed ball, as a finite set. -/
def xiBoundaryVertices (c : ℂ) (R : ℝ) : Finset ℂ :=
  (xi_zeros_closedBall_finite c R).toFinset

theorem mem_xiBoundaryVertices {c : ℂ} {R : ℝ} {z : ℂ} :
    z ∈ xiBoundaryVertices c R ↔ z ∈ Metric.closedBall c R ∧ xi z = 0 :=
  Set.Finite.mem_toFinset _

/-- The vertex type of the canonical boundary graph of a compact region. -/
abbrev XiBoundaryVertex (c : ℂ) (R : ℝ) : Type := {z : ℂ // z ∈ xiBoundaryVertices c R}

instance instDecidableEqXiBoundaryVertex (c : ℂ) (R : ℝ) :
    DecidableEq (XiBoundaryVertex c R) := fun _ _ => Classical.dec _

/-- The canonical boundary graph of a compact region: one vertex for each zero of `xi` there. -/
def xiBoundaryGraph (c : ℂ) (R : ℝ) : XiBoundaryVertex c R → ℂ := Subtype.val

theorem xiBoundaryGraph_injective (c : ℂ) (R : ℝ) :
    Function.Injective (xiBoundaryGraph c R) := Subtype.val_injective

theorem xi_xiBoundaryGraph_eq_zero (c : ℂ) (R : ℝ) (w : XiBoundaryVertex c R) :
    xi (xiBoundaryGraph c R w) = 0 := (mem_xiBoundaryVertices.mp w.2).2

theorem xiBoundaryGraph_mem_closedBall (c : ℂ) (R : ℝ) (w : XiBoundaryVertex c R) :
    xiBoundaryGraph c R w ∈ Metric.closedBall c R := (mem_xiBoundaryVertices.mp w.2).1

/-! ### The relative trace of a region -/

theorem card_XiBoundaryVertex (c : ℂ) (R : ℝ) :
    Fintype.card (XiBoundaryVertex c R) = (xiBoundaryVertices c R).card :=
  Fintype.card_coe _

/-- **The relative trace of a compact region counts its zeros.**  Every zero contributes exactly one
unit, whatever its multiplicity. -/
theorem trace_xiGradedBoundarySymbol_xiBoundaryGraph (c : ℂ) (R : ℝ) :
    Matrix.trace (xiGradedBoundarySymbol (xiBoundaryGraph c R))
      = ((xiBoundaryVertices c R).card : ℝ) := by
  rw [trace_xiGradedBoundarySymbol, card_XiBoundaryVertex]

/-- **The four-unit budget on a region is a four-zero budget.** -/
theorem trace_xiBoundaryGraph_le_four_iff (c : ℂ) (R : ℝ) :
    Matrix.trace (xiGradedBoundarySymbol (xiBoundaryGraph c R)) ≤ 4
      ↔ (xiBoundaryVertices c R).card ≤ 4 := by
  rw [trace_xiGradedBoundarySymbol_xiBoundaryGraph]
  exact_mod_cast Nat.cast_le (α := ℝ)

/-! ### Monotonicity and the chambers -/

theorem xiBoundaryVertices_mono (c : ℂ) {R R' : ℝ} (h : R ≤ R') :
    xiBoundaryVertices c R ⊆ xiBoundaryVertices c R' := by
  intro z hz
  obtain ⟨hmem, hzero⟩ := mem_xiBoundaryVertices.mp hz
  exact mem_xiBoundaryVertices.mpr ⟨Metric.closedBall_subset_closedBall h hmem, hzero⟩

/-- The relative trace grows with the region. -/
theorem trace_xiBoundaryGraph_mono (c : ℂ) {R R' : ℝ} (h : R ≤ R') :
    Matrix.trace (xiGradedBoundarySymbol (xiBoundaryGraph c R))
      ≤ Matrix.trace (xiGradedBoundarySymbol (xiBoundaryGraph c R')) := by
  rw [trace_xiGradedBoundarySymbol_xiBoundaryGraph,
    trace_xiGradedBoundarySymbol_xiBoundaryGraph]
  exact_mod_cast Finset.card_le_card (xiBoundaryVertices_mono c h)

/-- A region inside the Euler chamber has no vertices at all. -/
theorem xiBoundaryVertices_eq_empty_of_one_le_re {c : ℂ} {R : ℝ}
    (h : ∀ z ∈ Metric.closedBall c R, 1 ≤ z.re) : xiBoundaryVertices c R = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  obtain ⟨hmem, hzero⟩ := mem_xiBoundaryVertices.mp hz
  exact xi_ne_zero_of_one_le_re (h z hmem) hzero

/-- **The Euler chamber carries no relative trace.**  Nothing of the boundary budget is visible
where the Euler product converges. -/
theorem trace_xiBoundaryGraph_eq_zero_of_one_le_re {c : ℂ} {R : ℝ}
    (h : ∀ z ∈ Metric.closedBall c R, 1 ≤ z.re) :
    Matrix.trace (xiGradedBoundarySymbol (xiBoundaryGraph c R)) = 0 := by
  rw [trace_xiGradedBoundarySymbol_xiBoundaryGraph,
    xiBoundaryVertices_eq_empty_of_one_le_re h, Finset.card_empty, Nat.cast_zero]

/-- The same on the reflected chamber. -/
theorem trace_xiBoundaryGraph_eq_zero_of_re_nonpos {c : ℂ} {R : ℝ}
    (h : ∀ z ∈ Metric.closedBall c R, z.re ≤ 0) :
    Matrix.trace (xiGradedBoundarySymbol (xiBoundaryGraph c R)) = 0 := by
  rw [trace_xiGradedBoundarySymbol_xiBoundaryGraph]
  have : xiBoundaryVertices c R = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    obtain ⟨hmem, hzero⟩ := mem_xiBoundaryVertices.mp hz
    exact xi_ne_zero_of_re_nonpos (h z hmem) hzero
  rw [this, Finset.card_empty, Nat.cast_zero]

/-! ### The canonical symbol inherits the graded structure -/

theorem xiBoundaryGraph_symbol_posSemidef (c : ℂ) (R : ℝ) :
    (xiGradedBoundarySymbol (xiBoundaryGraph c R)).PosSemidef :=
  xiGradedBoundarySymbol_posSemidef _

theorem xiBoundaryGraph_symbol_idempotent (c : ℂ) (R : ℝ) :
    xiGradedBoundarySymbol (xiBoundaryGraph c R) * xiGradedBoundarySymbol (xiBoundaryGraph c R)
      = xiGradedBoundarySymbol (xiBoundaryGraph c R) :=
  xiGradedBoundarySymbol_idempotent _

end

end RHTower
