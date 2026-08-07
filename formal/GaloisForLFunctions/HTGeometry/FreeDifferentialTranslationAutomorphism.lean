import GaloisForLFunctions.HTGeometry.FreeDifferentialFieldPresentation
import GaloisForLFunctions.HTGeometry.TranslationInvariantRationalFunction

/-!
# The translation automorphisms of a free differential field

Translating a free differential generator by a base constant gives another free differential
generator of the same field, so the two jet evaluations differ by a differential automorphism.
This is the deck group of the additive group: the automorphism fixes `u′` and moves `u`.

It is the model of the compact orbifold signatures, whose universal cover is the additive group and
whose deck transformations are translations by lattice points.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

omit [Differential F] [DifferentialAlgebra F E] in
/-- Translating by a base constant shifts only the zeroth jet. -/
theorem differentialJet_add_const (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F) (u : E) :
    ∀ n : ℕ, differentialJet n (u + algebraMap F E a)
      = differentialJet n u + (if n = 0 then algebraMap F E a else 0)
  | 0 => by simp
  | n + 1 => by
      rw [differentialJet_succ, differentialJet_add_const hF a u n, differentialJet_succ]
      by_cases h : n = 0 <;> simp [h, hF a]

omit [Differential F] [DifferentialAlgebra F E] in
/-- Translating a differentially independent element by a base constant keeps it differentially
independent. -/
theorem differentialIndependent_add_const (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F)
    {u : E} (hu : DifferentialIndependent F (fun _ : Unit ↦ u)) :
    DifferentialIndependent F (fun _ : Unit ↦ u + algebraMap F E a) := by
  classical
  have hbase : AlgebraicIndependent F (fun p : Unit × ℕ => differentialJet p.2 u) := hu
  have hshift := GaloisForLFunctions.AlgebraicIndependent.add_algebraMap hbase
    (fun p : Unit × ℕ => if p.2 = 0 then a else 0)
  have hfun : (fun p : Unit × ℕ => differentialJet p.2 (u + algebraMap F E a))
      = fun p : Unit × ℕ => differentialJet p.2 u
        + algebraMap F E (if p.2 = 0 then a else 0) := by
    funext p
    rw [differentialJet_add_const hF a u p.2]
    by_cases h : p.2 = 0 <;> simp [h]
  show AlgebraicIndependent F (fun p : Unit × ℕ => differentialJet p.2 (u + algebraMap F E a))
  rw [hfun]
  exact hshift

end

end GaloisForLFunctions.HTGeometry
