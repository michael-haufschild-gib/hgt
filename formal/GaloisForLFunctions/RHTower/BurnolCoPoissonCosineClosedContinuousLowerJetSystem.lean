import GaloisForLFunctions.RHTower.BurnolCoPoissonCosineClosedLowerJetSystem
import GaloisForLFunctions.RHTower.BurnolSoninCompletedJetBridge
import GaloisForLFunctions.HTGeometry.HardyClosureZeroFree

/-!
# Continuous lower zero-jet system on Burnol's closed co-Poisson source

The literal cosine-closed co-Poisson source is defined as a Hilbert closure,
whereas the completed Mellin identity gives lower Xi-jet vanishing first on
individual generators.  The bounded source-selected jet evaluator supplied by
`BurnolSoninCompletedJetBridge` is extended to the ambient even carrier by
orthogonal projection onto the closed extended Sonine space.  The generic
closed-span theorem then passes the literal lower-jet relation through the
source closure.

This is a genuine `BND + COMP` descent: no density or identification with the
Burnol `P_a` complement is asserted.  In particular it does not prove RH; the
remaining Burnol obstruction is the source-completeness/minimality statement,
not continuity of a fixed lower jet.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- **Closed cosine co-Poisson lower-jet descent.** At a right-half Xi
divisor, every completed Mellin jet below the exact conormal order vanishes
on the entire literal cosine-closed co-Poisson source space, not merely on
its algebraic generator span. -/
theorem iteratedDeriv_soninMellinEvaluation_eq_zero_of_mem_burnolCoPoissonSourceSpace_of_lt
    {b : ℝ} (hb : 0 < b) (rho : XiDivisorSupport)
    (hright : 1 / 2 < (rho : ℂ).re) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonSourceSpace b) :
    iteratedDeriv j (fun w : ℂ => soninMellinEvaluation w ((f : evenSubspace) : SoninL2))
      (rho : ℂ) = 0 := by
  letI : Fact (0 < b) := ⟨hb⟩
  have hrho1 : (rho : ℂ).re < 1 := (xi_divisor_support_re_mem_open_unit rho).2
  obtain ⟨Λ, hΛ⟩ :=
    exists_soninExtendedCompletedMellinJetEvaluator hb j hright hrho1
  let E := soninExtendedSpace b
  let L : evenSubspace →L[ℂ] ℂ := Λ.comp E.orthogonalProjectionOnto
  have hG : ∀ g : burnolCoPoissonGeneratorSet b, L (g : evenSubspace) = 0 := by
    intro g
    have hgE : (g : evenSubspace) ∈ E := by
      exact burnolCoPoissonAlgebraicSourceSpace_le_soninExtendedSpace b
        (Submodule.subset_span g.property)
    have hjet :=
      iteratedDeriv_soninMellinEvaluation_burnolCoPoissonGenerator_eq_zero_of_lt
        hb g.property rho hright hj
    change Λ (E.orthogonalProjectionOnto (g : evenSubspace)) = 0
    rw [E.orthogonalProjectionOnto_mem_subspace_eq_self ⟨(g : evenSubspace), hgE⟩]
    rw [hΛ]
    exact hjet
  have hclosed := GaloisForLFunctions.HTGeometry.continuousLinearMap_eq_zero_on_closedSpan
    L (fun g : burnolCoPoissonGeneratorSet b => (g : evenSubspace)) hG
  have hspan :
      Submodule.span ℂ (Set.range fun g : burnolCoPoissonGeneratorSet b =>
        (g : evenSubspace)) = burnolCoPoissonAlgebraicSourceSpace b := by
    rw [burnolCoPoissonAlgebraicSourceSpace]
    congr 1
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact g.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : f ∈ L.ker := by
    apply hclosed
    change f ∈ (burnolCoPoissonAlgebraicSourceSpace b).topologicalClosure at hf
    rw [hspan]
    exact hf
  have hfE : f ∈ E := burnolCoPoissonSourceSpace_le_soninExtendedSpace hb hf
  change Λ (E.orthogonalProjectionOnto f) = 0 at hfker
  rw [E.orthogonalProjectionOnto_mem_subspace_eq_self ⟨f, hfE⟩] at hfker
  rw [hΛ] at hfker
  exact hfker

end RHTower
