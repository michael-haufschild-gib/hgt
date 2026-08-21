import GaloisForLFunctions.RHTower.EulerSquarefreeWickDefect
import GaloisForLFunctions.HTGeometry.CoprimePrimeResidueInteraction

/-!
# Euler--Wick sign-gauge interaction cohomology

The raw four-factor Euler Wick defect carries a canonical mixed-incidence class.  Two independent
sign gauges act on two literal coefficient legs.  Taking the anchored mixed part of the resulting
gauge orbit kills every row and column marginal, while retaining a checkerboard whose amplitude is
exactly the original Euler defect.

For the two-by-two gauge square the interaction cohomology has dimension one.  A genuine
four-factor Euler packet therefore generates the entire quotient, and its class is unchanged by
every marginal counterterm.  No zero-location, RH, positivity, or receiver-side hypothesis enters.
-/

namespace GaloisForLFunctions.RHTower

open Set
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The nontrivial character of `Fin 2`, normalized to equal one at the distinguished anchor. -/
def finTwoAnchoredSign (x : Fin 2) : ℂ :=
  if x = 1 then 1 else -1

@[simp] theorem finTwoAnchoredSign_one : finTwoAnchoredSign 1 = 1 := by
  simp [finTwoAnchoredSign]

@[simp] theorem finTwoAnchoredSign_zero : finTwoAnchoredSign 0 = -1 := by
  simp [finTwoAnchoredSign]

/-- Two independent sign gauges act on the first two legs of the literal four-factor packet. -/
def eulerSquarefreeWickTwoLegGauge
    (a : Fin 4 → ℂ) (x y : Fin 2) : Fin 4 → ℂ :=
  fun i => if i = 0 then finTwoAnchoredSign x * a i
    else if i = 1 then finTwoAnchoredSign y * a i else a i

/-- The raw Euler Wick defect is bi-equivariant under the two coefficient sign gauges. -/
theorem eulerSquarefreeWickFourDefect_twoLegGauge
    (a : Fin 4 → ℂ) (x y : Fin 2) :
    eulerSquarefreeWickFourDefect (eulerSquarefreeWickTwoLegGauge a x y) =
      finTwoAnchoredSign x * finTwoAnchoredSign y *
        eulerSquarefreeWickFourDefect a := by
  rw [eulerSquarefreeWickFourDefect_eq, eulerSquarefreeWickFourDefect_eq]
  simp [eulerSquarefreeWickTwoLegGauge]
  ring

/-- Orbit observable obtained by applying the two gauges before measuring the raw Euler defect. -/
def eulerSquarefreeWickGaugeOrbitObservable (a : Fin 4 → ℂ) :
    FullValueSubtype (Fin 2 × Fin 2) → ℂ :=
  fun x => eulerSquarefreeWickFourDefect
    (eulerSquarefreeWickTwoLegGauge a x.1.1 x.1.2)

/-- Canonical mixed part of the actual two-leg Euler gauge orbit. -/
def eulerSquarefreeWickAnchoredInteractionObservable (a : Fin 4 → ℂ) :
    FullValueSubtype (Fin 2 × Fin 2) → ℂ :=
  productAnchoredInteractionPart (Fin 2) (Fin 2)
    (eulerSquarefreeWickGaugeOrbitObservable a)

/-- Exact checkerboard law forced by coefficient-gauge covariance. -/
theorem eulerSquarefreeWickAnchoredInteractionObservable_eq
    (a : Fin 4 → ℂ) (x : FullValueSubtype (Fin 2 × Fin 2)) :
    eulerSquarefreeWickAnchoredInteractionObservable a x =
      eulerSquarefreeWickFourDefect a *
        (finTwoAnchoredSign x.1.1 - 1) *
        (finTwoAnchoredSign x.1.2 - 1) := by
  rw [eulerSquarefreeWickAnchoredInteractionObservable]
  simp only [productAnchoredInteractionPart, productRowPart, productColumnPart,
    eulerSquarefreeWickGaugeOrbitObservable,
    eulerSquarefreeWickFourDefect_twoLegGauge, finTwoAnchoredSign_one]
  ring

theorem eulerSquarefreeWickAnchoredInteractionObservable_mem
    (a : Fin 4 → ℂ) :
    eulerSquarefreeWickAnchoredInteractionObservable a ∈
      productAnchoredInteractionSubmodule (Fin 2) (Fin 2) := by
  exact productAnchoredInteractionPart_mem (Fin 2) (Fin 2)
    (eulerSquarefreeWickGaugeOrbitObservable a)

/-- The anchored interaction as a joint observable on the common refinement. -/
def eulerSquarefreeWickJointObservable (a : Fin 4 → ℂ) :
    ClassInvariantRestricted
      (productFstSetoid (Fin 2) (Fin 2) ⊓ productSndSetoid (Fin 2) (Fin 2)) :=
  ⟨eulerSquarefreeWickAnchoredInteractionObservable a, by
    rw [classInvariantRestricted_product_inf_eq_top]
    exact Submodule.mem_top⟩

/-- Canonical Euler--Wick interaction-cohomology class. -/
def eulerSquarefreeWickInteractionClass (a : Fin 4 → ℂ) :
    FiniteQuotientInteractionCohomology
      (productFstSetoid (Fin 2) (Fin 2))
      (productSndSetoid (Fin 2) (Fin 2)) :=
  Submodule.Quotient.mk (eulerSquarefreeWickJointObservable a)

theorem eulerSquarefreeWickAnchoredInteractionObservable_zero_iff
    (a : Fin 4 → ℂ) :
    eulerSquarefreeWickAnchoredInteractionObservable a = 0 ↔
      eulerSquarefreeWickFourDefect a = 0 := by
  constructor
  · intro h
    have h00 : eulerSquarefreeWickAnchoredInteractionObservable a
        (⟨((0 : Fin 2), (0 : Fin 2)), Set.mem_univ _⟩ :
          FullValueSubtype (Fin 2 × Fin 2)) = 0 := by
      simpa using congrFun h
        (⟨((0 : Fin 2), (0 : Fin 2)), Set.mem_univ _⟩ :
          FullValueSubtype (Fin 2 × Fin 2))
    rw [eulerSquarefreeWickAnchoredInteractionObservable_eq] at h00
    simp only [finTwoAnchoredSign_zero] at h00
    ring_nf at h00
    exact (mul_eq_zero.mp h00).resolve_right (by norm_num)
  · intro h
    funext x
    rw [eulerSquarefreeWickAnchoredInteractionObservable_eq, h]
    simp

/-- Exact kernel: quotient collapse occurs precisely when the raw Euler Wick defect vanishes. -/
theorem eulerSquarefreeWickInteractionClass_eq_zero_iff
    (a : Fin 4 → ℂ) :
    eulerSquarefreeWickInteractionClass a = 0 ↔
      eulerSquarefreeWickFourDefect a = 0 := by
  rw [eulerSquarefreeWickInteractionClass, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hmarginal
    have hrawMarginal : eulerSquarefreeWickAnchoredInteractionObservable a ∈
        productMarginalObservableSubmodule (Fin 2) (Fin 2) := hmarginal
    have hzero : eulerSquarefreeWickAnchoredInteractionObservable a = 0 :=
      (Submodule.disjoint_def.mp
        (productAnchoredInteractionSubmodule_isCompl (Fin 2) (Fin 2)).1)
        _ hrawMarginal
        (eulerSquarefreeWickAnchoredInteractionObservable_mem a)
    exact (eulerSquarefreeWickAnchoredInteractionObservable_zero_iff a).mp hzero
  · intro hdefect
    have hzero : eulerSquarefreeWickJointObservable a = 0 := by
      apply Subtype.ext
      exact (eulerSquarefreeWickAnchoredInteractionObservable_zero_iff a).mpr hdefect
    rw [hzero]
    exact Submodule.zero_mem _

/-- Complete local classification of when the canonical interaction class disappears. -/
theorem eulerSquarefreeWickInteractionClass_eq_zero_iff_coordinate
    (a : Fin 4 → ℂ) :
    eulerSquarefreeWickInteractionClass a = 0 ↔
      a 0 = 0 ∨ a 1 = 0 ∨ a 2 = 0 ∨ a 3 = 0 := by
  rw [eulerSquarefreeWickInteractionClass_eq_zero_iff]
  exact eulerSquarefreeWickFourLaw_iff a

/-- The two-by-two interaction cohomology has one and only one mixed direction. -/
theorem finTwoProductInteractionCohomology_finrank :
    Module.finrank ℂ
      (FiniteQuotientInteractionCohomology
        (productFstSetoid (Fin 2) (Fin 2))
        (productSndSetoid (Fin 2) (Fin 2))) = 1 := by
  rw [finiteQuotientInteractionCohomology_finrank,
    productFiniteQuotientInteractionDefect_eq]
  norm_num

/-- A genuine four-factor Euler packet generates the entire interaction quotient. -/
theorem span_eulerSquarefreeWickInteractionClass_eq_top
    (a : Fin 4 → ℂ) (ha : ∀ i, a i ≠ 0) :
    ℂ ∙ eulerSquarefreeWickInteractionClass a = ⊤ := by
  apply (finrank_eq_one_iff_of_nonzero
    (eulerSquarefreeWickInteractionClass a) ?_).mp
  · exact finTwoProductInteractionCohomology_finrank
  · intro hzero
    rcases (eulerSquarefreeWickInteractionClass_eq_zero_iff_coordinate a).mp hzero with
      h0 | h1 | h2 | h3
    · exact ha 0 h0
    · exact ha 1 h1
    · exact ha 2 h2
    · exact ha 3 h3

/-- Full marginal-counterterm neutrality of the canonical class. -/
theorem eulerSquarefreeWickInteractionClass_add_marginal
    (a : Fin 4 → ℂ)
    (m : ClassInvariantRestricted
      (productFstSetoid (Fin 2) (Fin 2) ⊓ productSndSetoid (Fin 2) (Fin 2)))
    (hm : (m : FullValueSubtype (Fin 2 × Fin 2) → ℂ) ∈
      productMarginalObservableSubmodule (Fin 2) (Fin 2)) :
    Submodule.Quotient.mk (eulerSquarefreeWickJointObservable a + m) =
      eulerSquarefreeWickInteractionClass a := by
  change (Submodule.mkQ
      (finiteQuotientInteractionMarginalSubmodule
        (productFstSetoid (Fin 2) (Fin 2))
        (productSndSetoid (Fin 2) (Fin 2))))
      (eulerSquarefreeWickJointObservable a + m) = _
  rw [map_add]
  have hmzero : (Submodule.mkQ
      (finiteQuotientInteractionMarginalSubmodule
        (productFstSetoid (Fin 2) (Fin 2))
        (productSndSetoid (Fin 2) (Fin 2)))) m = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hm
  rw [hmzero, add_zero]
  rfl

end

end GaloisForLFunctions.RHTower
