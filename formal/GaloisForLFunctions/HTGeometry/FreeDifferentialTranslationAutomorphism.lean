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


/-- Translating by a base constant does not change the generated differential field. -/
theorem differentialAdjoin_add_const (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F) (u : E) :
    differentialAdjoin F ({u + algebraMap F E a} : Set E) = differentialAdjoin F ({u} : Set E) := by
  have hmem : ∀ (b : F) (z : E), z + algebraMap F E b ∈ differentialAdjoin F ({z} : Set E) := by
    intro b z
    exact (differentialAdjoin F ({z} : Set E)).add_mem
      (subset_differentialAdjoin F _ rfl)
      ((differentialAdjoin F ({z} : Set E)).algebraMap_mem b)
  refine le_antisymm ?_ ?_
  · exact differentialAdjoin_le F (by simpa using hmem a u)
      (derivationClosed_differentialAdjoin F _)
  · refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
    have hgoal : u ∈ differentialAdjoin F ({u + algebraMap F E a} : Set E) := by
      have h1 : (u + algebraMap F E a) + algebraMap F E (-a)
          ∈ differentialAdjoin F ({u + algebraMap F E a} : Set E) := hmem (-a) _
      have h2 : (u + algebraMap F E a) + algebraMap F E (-a) = u := by
        rw [map_neg]
        ring
      rwa [h2] at h1
    simpa using hgoal

/-- **The translation automorphism.**  A base constant `a` induces a differential `F`-automorphism
of a freely differentially generated field translating the generator by `a`. -/
def translationAutomorphism (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F)
    {u : E} (hu : DifferentialIndependent F (fun _ : Unit ↦ u))
    (hutop : differentialAdjoin F ({u} : Set E) = ⊤) : E ≃ₐ[F] E :=
  let hau := differentialIndependent_add_const hF a hu
  let hautop : differentialAdjoin F ({u + algebraMap F E a} : Set E) = ⊤ := by
    rw [differentialAdjoin_add_const hF a u, hutop]
  (AlgEquiv.ofBijective (differentialJetFieldEval F hu)
      ⟨jetFieldEval_injective hu, jetFieldEval_surjective hF hu hutop⟩).symm.trans
    (AlgEquiv.ofBijective (differentialJetFieldEval F hau)
      ⟨jetFieldEval_injective hau, jetFieldEval_surjective hF hau hautop⟩)

theorem translationAutomorphism_deriv (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F)
    {u : E} (hu : DifferentialIndependent F (fun _ : Unit ↦ u))
    (hutop : differentialAdjoin F ({u} : Set E) = ⊤) (z : E) :
    translationAutomorphism hF a hu hutop z′ = (translationAutomorphism hF a hu hutop z)′ := by
  classical
  set hau := differentialIndependent_add_const hF a hu with hauDef
  set eu := AlgEquiv.ofBijective (differentialJetFieldEval F hu)
    ⟨jetFieldEval_injective hu, jetFieldEval_surjective hF hu hutop⟩ with heuDef
  have hinv : ∀ w : E, differentialJetFieldEval F hu (eu.symm w) = w := fun w =>
    eu.apply_symm_apply w
  have hsymmderiv : ∀ w : E, eu.symm (w′) = (eu.symm w)′ := by
    intro w
    have hkey : differentialJetFieldEval F hu (eu.symm (w′))
        = differentialJetFieldEval F hu ((eu.symm w)′) := by
      rw [hinv, jetFieldEval_deriv hF hu, hinv]
    exact jetFieldEval_injective hu hkey
  simp only [translationAutomorphism, AlgEquiv.trans_apply, ← heuDef]
  rw [hsymmderiv]
  have hstep : (AlgEquiv.ofBijective (differentialJetFieldEval F hau)
      ⟨jetFieldEval_injective hau, jetFieldEval_surjective hF hau (by
        rw [differentialAdjoin_add_const hF a u, hutop])⟩ : JetField F Unit ≃ₐ[F] E)
      ((eu.symm z)′) = differentialJetFieldEval F hau ((eu.symm z)′) := rfl
  rw [hstep, jetFieldEval_deriv hF hau]
  rfl

theorem translationAutomorphism_generator (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F)
    {u : E} (hu : DifferentialIndependent F (fun _ : Unit ↦ u))
    (hutop : differentialAdjoin F ({u} : Set E) = ⊤) :
    translationAutomorphism hF a hu hutop u = u + algebraMap F E a := by
  classical
  set hau := differentialIndependent_add_const hF a hu with hauDef
  set eu := AlgEquiv.ofBijective (differentialJetFieldEval F hu)
    ⟨jetFieldEval_injective hu, jetFieldEval_surjective hF hu hutop⟩ with heuDef
  have hjet : eu (algebraMap (JetPoly F Unit) (JetField F Unit) (MvPolynomial.X ((), 0))) = u := by
    simp only [heuDef, AlgEquiv.ofBijective_apply]
    rw [jetFieldEval_algebraMap, jetPolyEval_X, differentialJet_zero]
  have hsymm : eu.symm u = algebraMap (JetPoly F Unit) (JetField F Unit) (MvPolynomial.X ((), 0)) :=
    by rw [← hjet, AlgEquiv.symm_apply_apply]
  simp only [translationAutomorphism, AlgEquiv.trans_apply, ← heuDef, hsymm,
    AlgEquiv.ofBijective_apply]
  rw [jetFieldEval_algebraMap, jetPolyEval_X, differentialJet_zero]

/-- **The translation automorphisms fix the derivative of the generator.** -/
theorem translationAutomorphism_deriv_generator (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F)
    {u : E} (hu : DifferentialIndependent F (fun _ : Unit ↦ u))
    (hutop : differentialAdjoin F ({u} : Set E) = ⊤) :
    translationAutomorphism hF a hu hutop (u′) = u′ := by
  rw [translationAutomorphism_deriv hF a hu hutop u,
    translationAutomorphism_generator hF a hu hutop, map_add, hF a, add_zero]

end

end GaloisForLFunctions.HTGeometry
