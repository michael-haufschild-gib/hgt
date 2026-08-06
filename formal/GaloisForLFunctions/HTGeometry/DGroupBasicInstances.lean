import GaloisForLFunctions.HTGeometry.CommutativeDGroupObservable

/-!
# The additive and multiplicative `D`-groups

The two one-dimensional commutative algebraic `D`-groups are presented here: the additive group,
whose logarithmic derivative is the derivation itself, and the multiplicative group, whose
logarithmic derivative is `x′/x`.  In both cases the coordinate derivative is rational in the
coordinate and the logarithmic coordinate, which is the `D`-structure.

These presentations make the general source-boundary theorems non-vacuous and recover the
classical additive and multiplicative source theorems as special cases.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L]

/-! ### Elements and their derivatives generate a differential field -/

omit [Differential K] [DifferentialAlgebra K L] in
theorem self_mem_differentialAdjoin_singleton (x : L) :
    x ∈ differentialAdjoin K ({x} : Set L) :=
  subset_differentialAdjoin K _ rfl

omit [Differential K] [DifferentialAlgebra K L] in
theorem deriv_mem_differentialAdjoin_singleton (x : L) :
    x′ ∈ differentialAdjoin K ({x} : Set L) :=
  IntermediateField.subset_adjoin K _ ⟨x, rfl, 1, by rw [differentialJet_succ,
    differentialJet_zero]⟩

/-! ### The additive `D`-group -/

/-- The additive group of the field, as a commutative `D`-group with logarithmic derivative the
derivation itself. -/
def additiveDGroup : DGroupPresentation (Multiplicative L) K L 1 1 where
  coords g := fun _ => Multiplicative.toAdd g
  ell g := fun _ => (Multiplicative.toAdd g)′
  ell_mul g h := by
    funext j
    show (Multiplicative.toAdd (g * h))′ = _
    show (Multiplicative.toAdd g + Multiplicative.toAdd h)′
      = (Multiplicative.toAdd g)′ + (Multiplicative.toAdd h)′
    rw [Differential.deriv.map_add]
  ell_mem_coordAdjoin g j := by
    have hx : Multiplicative.toAdd g ∈ Set.range (fun _ : Fin 1 => Multiplicative.toAdd g) :=
      ⟨0, rfl⟩
    exact IntermediateField.subset_adjoin K _
      ⟨Multiplicative.toAdd g, hx, 1, by rw [differentialJet_succ, differentialJet_zero]⟩
  deriv_coords_mem g i := by
    refine IntermediateField.subset_adjoin K _ (Or.inr ?_)
    exact ⟨(Multiplicative.toAdd g)′, ⟨0, rfl⟩, 0, differentialJet_zero _⟩

/-! ### The multiplicative `D`-group -/

/-- The multiplicative group of the field, as a commutative `D`-group with logarithmic derivative
`x′/x`. -/
def multiplicativeDGroup : DGroupPresentation Lˣ K L 1 1 where
  coords g := fun _ => (g : L)
  ell g := fun _ => ((g : L))′ / (g : L)
  ell_mul g h := by
    funext j
    show ((g * h : Lˣ) : L)′ / ((g * h : Lˣ) : L)
      = (g : L)′ / (g : L) + (h : L)′ / (h : L)
    have hg : (g : L) ≠ 0 := g.ne_zero
    have hh : (h : L) ≠ 0 := h.ne_zero
    rw [Units.val_mul, Derivation.leibniz]
    field_simp
    ring
  ell_mem_coordAdjoin g j := by
    have hx : (g : L) ∈ Set.range (fun _ : Fin 1 => (g : L)) := ⟨0, rfl⟩
    have hmem : (g : L) ∈ differentialAdjoin K (Set.range (fun _ : Fin 1 => (g : L))) :=
      IntermediateField.subset_adjoin K _ ⟨(g : L), hx, 0, differentialJet_zero _⟩
    have hderiv : ((g : L))′ ∈ differentialAdjoin K (Set.range (fun _ : Fin 1 => (g : L))) :=
      IntermediateField.subset_adjoin K _
        ⟨(g : L), hx, 1, by rw [differentialJet_succ, differentialJet_zero]⟩
    exact IntermediateField.div_mem _ hderiv hmem
  deriv_coords_mem g i := by
    have hg : (g : L) ≠ 0 := g.ne_zero
    have hcoord : (g : L) ∈ IntermediateField.adjoin K
        (Set.range (fun _ : Fin 1 => (g : L)) ∪
          differentialJetSet (Set.range (fun _ : Fin 1 => ((g : L))′ / (g : L)))) :=
      IntermediateField.subset_adjoin K _ (Or.inl ⟨0, rfl⟩)
    have hell : ((g : L))′ / (g : L) ∈ IntermediateField.adjoin K
        (Set.range (fun _ : Fin 1 => (g : L)) ∪
          differentialJetSet (Set.range (fun _ : Fin 1 => ((g : L))′ / (g : L)))) :=
      IntermediateField.subset_adjoin K _
        (Or.inr ⟨((g : L))′ / (g : L), ⟨0, rfl⟩, 0, differentialJet_zero _⟩)
    have hmul := IntermediateField.mul_mem _ hcoord hell
    rw [mul_div_cancel₀ _ hg] at hmul
    exact hmul

end

end GaloisForLFunctions.HTGeometry
