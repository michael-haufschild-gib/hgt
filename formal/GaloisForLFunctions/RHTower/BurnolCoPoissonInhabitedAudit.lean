import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezin
import GaloisForLFunctions.RHTower.BurnolSoninEigenWitness

/-!
# Inhabitation audit of the co-Poisson source layer

Every object built from `BurnolCoPoissonSource` is contentful only once that structure is
inhabited: its generator set is indexed by such sources, so if there are none the generator set is
empty, the algebraic and closed source spaces collapse to `⊥`, and the co-Poisson quotient space is
the whole extended Sonine space.  The theorems below record that collapse explicitly, so no later
statement about the source projection or the quotient kernel can be read as content without an
inhabitant.

In the other direction a single inhabited source with nonvanishing completed Mellin evaluation is
exactly the outstanding nonvanishing witness: it settles `k_{w,a} ≠ 0` at every aperture `a ≤ b`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem burnolCoPoissonGeneratorSet_eq_empty_of_isEmpty {b : ℝ}
    (h : IsEmpty (BurnolCoPoissonSource b)) :
    burnolCoPoissonGeneratorSet b = ∅ := by
  ext f
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨g, -⟩
  exact h.elim g

theorem burnolCoPoissonAlgebraicSourceSpace_eq_bot_of_isEmpty {b : ℝ}
    (h : IsEmpty (BurnolCoPoissonSource b)) :
    burnolCoPoissonAlgebraicSourceSpace b = ⊥ := by
  rw [burnolCoPoissonAlgebraicSourceSpace,
    burnolCoPoissonGeneratorSet_eq_empty_of_isEmpty h, Submodule.span_empty]

/-- **Collapse of the closed source space.**  With no inhabited source the closed co-Poisson source
space is trivial. -/
theorem burnolCoPoissonSourceSpace_eq_bot_of_isEmpty {b : ℝ}
    (h : IsEmpty (BurnolCoPoissonSource b)) :
    burnolCoPoissonSourceSpace b = ⊥ := by
  rw [burnolCoPoissonSourceSpace, burnolCoPoissonAlgebraicSourceSpace_eq_bot_of_isEmpty h]
  refine le_antisymm ?_ bot_le
  refine (⊥ : Submodule ℂ evenSubspace).topologicalClosure_minimal le_rfl ?_
  simp

/-- **Collapse of the quotient space.**  With no inhabited source the co-Poisson quotient space is
the whole extended Sonine space, so the quotient kernel carries no extra information. -/
theorem burnolCoPoissonQuotientSpace_eq_of_isEmpty {b : ℝ}
    (h : IsEmpty (BurnolCoPoissonSource b)) :
    burnolCoPoissonQuotientSpace b = soninExtendedSpace b := by
  rw [burnolCoPoissonQuotientSpace, burnolCoPoissonSourceSpace_eq_bot_of_isEmpty h,
    Submodule.bot_orthogonal_eq_top, inf_top_eq]

/-- **An inhabited co-Poisson source with nonvanishing evaluation is the missing witness.**  It
settles the nonvanishing input of the aperture-type limit at every aperture `a ≤ b`. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_coPoissonSource
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (g : BurnolCoPoissonSource b)
    (hval : soninMellinEvaluation w
      (((g.vector : soninExtendedSpace b) : evenSubspace) : SoninL2) ≠ 0) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 :=
  burnolExtendedSoninEvaluationVector_ne_zero_of_witness hlo hhi ha hb hab g.vector hval

end RHTower
