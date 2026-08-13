import GaloisForLFunctions.HTGeometry.FreeDifferentialScalingAutomorphism

/-!
# The translation automorphism of a freely differentially generated field

Translating the generator of a freely differentially generated field by a base constant leaves
every higher jet unchanged, so it preserves differential independence and the generated field, and
therefore induces a differential automorphism `y ↦ c + y`.  This is the deck transformation of the
additive universal cover, the counterpart of the multiplicative `scalingAutomorphism`.

* `differentialJet_const_add`, `differentialIndependent_const_add`,
  `differentialAdjoin_const_add`;
* `translationAutomorphism`, `translationAutomorphism_deriv`,
  `translationAutomorphism_generator`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

omit [Differential F] [DifferentialAlgebra F E] in
/-- Translating by a base constant leaves every positive jet unchanged. -/
theorem differentialJet_const_add (hF : ∀ a : F, (algebraMap F E a)′ = 0) (c : F) (y : E) (n : ℕ) :
    differentialJet (n + 1) (algebraMap F E c + y) = differentialJet (n + 1) y := by
  induction n with
  | zero =>
      rw [differentialJet_succ, differentialJet_succ, differentialJet_zero, differentialJet_zero,
        map_add, hF c, zero_add]
  | succ n ih =>
      rw [differentialJet_succ, ih, ← differentialJet_succ]

omit [Differential F] [DifferentialAlgebra F E] in
/-- Translating a differentially independent element by a base constant keeps it differentially
independent. -/
theorem differentialIndependent_const_add (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (c : F) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    DifferentialIndependent F (fun _ : Unit ↦ algebraMap F E c + y) := by
  classical
  have hinj : Function.Injective (differentialJetEval F (algebraMap F E c + y)) := by
    have hcomp : (differentialJetEval F (algebraMap F E c + y) : JetPoly F Unit →ₐ[F] E)
        = (differentialJetEval F y).comp
          (MvPolynomial.aeval fun p : Unit × ℕ =>
            (if p.2 = 0 then MvPolynomial.C c + MvPolynomial.X p
              else MvPolynomial.X p : JetPoly F Unit)) := by
      apply MvPolynomial.algHom_ext
      intro p
      rcases p with ⟨u, n⟩
      cases n with
      | zero =>
          simp only [differentialJetEval, AlgHom.comp_apply, MvPolynomial.aeval_X,
            map_add, MvPolynomial.aeval_C, if_true, differentialJet_zero]
      | succ n =>
          simp only [differentialJetEval, AlgHom.comp_apply, MvPolynomial.aeval_X,
            if_neg (Nat.succ_ne_zero n)]
          rw [differentialJet_const_add hF]
    rw [hcomp, AlgHom.coe_comp]
    refine Function.Injective.comp (jetPolyEval_injective hy) ?_
    set S : JetPoly F Unit →ₐ[F] JetPoly F Unit :=
      MvPolynomial.aeval (fun p : Unit × ℕ =>
        (if p.2 = 0 then MvPolynomial.C c + MvPolynomial.X p
          else MvPolynomial.X p : JetPoly F Unit)) with hSdef
    set S' : JetPoly F Unit →ₐ[F] JetPoly F Unit :=
      MvPolynomial.aeval (fun p : Unit × ℕ =>
        (if p.2 = 0 then MvPolynomial.C (-c) + MvPolynomial.X p
          else MvPolynomial.X p : JetPoly F Unit)) with hS'def
    have hSX : ∀ p : Unit × ℕ, S (MvPolynomial.X p)
        = if p.2 = 0 then MvPolynomial.C c + MvPolynomial.X p else MvPolynomial.X p := by
      intro p
      rw [hSdef, MvPolynomial.aeval_X]
    have hS'X : ∀ p : Unit × ℕ, S' (MvPolynomial.X p)
        = if p.2 = 0 then MvPolynomial.C (-c) + MvPolynomial.X p else MvPolynomial.X p := by
      intro p
      rw [hS'def, MvPolynomial.aeval_X]
    have htrans : Function.Bijective S := by
      refine Function.bijective_iff_has_inverse.mpr ⟨S', ?_, ?_⟩
      · intro q
        induction q using MvPolynomial.induction_on with
        | C r => simp [hSdef, hS'def]
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p v hp =>
            rw [map_mul, map_mul, hp, hSX v]
            by_cases hv : v.2 = 0
            · rw [if_pos hv, map_add, hS'X v, if_pos hv]
              have hC : S' (MvPolynomial.C c) = MvPolynomial.C c := by
                rw [hS'def]
                exact MvPolynomial.aeval_C _ c
              rw [hC]
              have hzero : (MvPolynomial.C c : JetPoly F Unit) + MvPolynomial.C (-c) = 0 := by
                rw [← MvPolynomial.C_add, add_neg_cancel, map_zero]
              linear_combination (p : JetPoly F Unit) * hzero
            · rw [if_neg hv, hS'X v, if_neg hv]
      · intro q
        induction q using MvPolynomial.induction_on with
        | C r => simp [hSdef, hS'def]
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p v hp =>
            rw [map_mul, map_mul, hp, hS'X v]
            by_cases hv : v.2 = 0
            · rw [if_pos hv, map_add, hSX v, if_pos hv]
              have hC : S (MvPolynomial.C (-c)) = MvPolynomial.C (-c) := by
                rw [hSdef]
                exact MvPolynomial.aeval_C _ (-c)
              rw [hC]
              have hzero : (MvPolynomial.C (-c) : JetPoly F Unit) + MvPolynomial.C c = 0 := by
                rw [← MvPolynomial.C_add, neg_add_cancel, map_zero]
              linear_combination (p : JetPoly F Unit) * hzero
            · rw [if_neg hv, hSX v, if_neg hv]
    exact htrans.injective
  exact hinj

/-- Translating by a base constant does not change the generated differential field. -/
theorem differentialAdjoin_const_add (c : F) (y : E) :
    differentialAdjoin F ({algebraMap F E c + y} : Set E)
      = differentialAdjoin F ({y} : Set E) := by
  have hmem : ∀ b : F, ∀ z : E,
      algebraMap F E b + z ∈ differentialAdjoin F ({z} : Set E) := fun b z ↦
    (differentialAdjoin F ({z} : Set E)).add_mem
      ((differentialAdjoin F ({z} : Set E)).algebraMap_mem b)
      (subset_differentialAdjoin F _ rfl)
  refine le_antisymm ?_ ?_
  · exact differentialAdjoin_le F (by simpa using hmem c y)
      (derivationClosed_differentialAdjoin F _)
  · refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
    have hgoal : y ∈ differentialAdjoin F ({algebraMap F E c + y} : Set E) := by
      have h1 : algebraMap F E (-c) + (algebraMap F E c + y)
          ∈ differentialAdjoin F ({algebraMap F E c + y} : Set E) := hmem (-c) _
      have h2 : algebraMap F E (-c) + (algebraMap F E c + y) = y := by
        rw [map_neg]
        ring
      rwa [h2] at h1
    simpa using hgoal

/-- **The translation automorphism.**  A base constant `c` induces a differential
`F`-automorphism of a freely differentially generated field translating the generator by `c`. -/
def translationAutomorphism (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (c : F) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) : E ≃ₐ[F] E :=
  let hcy := differentialIndependent_const_add hF c hy
  let hcytop : differentialAdjoin F ({algebraMap F E c + y} : Set E) = ⊤ := by
    rw [differentialAdjoin_const_add c y, hytop]
  (AlgEquiv.ofBijective (differentialJetFieldEval F hy)
      ⟨jetFieldEval_injective hy, jetFieldEval_surjective hF hy hytop⟩).symm.trans
    (AlgEquiv.ofBijective (differentialJetFieldEval F hcy)
      ⟨jetFieldEval_injective hcy, jetFieldEval_surjective hF hcy hcytop⟩)

theorem translationAutomorphism_deriv (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (c : F) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) (z : E) :
    translationAutomorphism hF c hy hytop z′ = (translationAutomorphism hF c hy hytop z)′ := by
  classical
  set hcy := differentialIndependent_const_add hF c hy with hcyDef
  set ey := AlgEquiv.ofBijective (differentialJetFieldEval F hy)
    ⟨jetFieldEval_injective hy, jetFieldEval_surjective hF hy hytop⟩ with heyDef
  have hinv : ∀ w : E, differentialJetFieldEval F hy (ey.symm w) = w := fun w =>
    ey.apply_symm_apply w
  have hsymmderiv : ∀ w : E, ey.symm (w′) = (ey.symm w)′ := by
    intro w
    have hkey : differentialJetFieldEval F hy (ey.symm (w′))
        = differentialJetFieldEval F hy ((ey.symm w)′) := by
      rw [hinv, jetFieldEval_deriv hF hy, hinv]
    exact jetFieldEval_injective hy hkey
  simp only [translationAutomorphism, AlgEquiv.trans_apply, ← heyDef]
  rw [hsymmderiv]
  have hshow : (AlgEquiv.ofBijective (differentialJetFieldEval F hcy)
      ⟨jetFieldEval_injective hcy, jetFieldEval_surjective hF hcy (by
        rw [differentialAdjoin_const_add c y, hytop])⟩ : JetField F Unit ≃ₐ[F] E)
      ((ey.symm z)′) = differentialJetFieldEval F hcy ((ey.symm z)′) := rfl
  rw [hshow]
  rw [jetFieldEval_deriv hF hcy]
  rfl

theorem translationAutomorphism_generator (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (c : F) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    translationAutomorphism hF c hy hytop y = algebraMap F E c + y := by
  classical
  set hcy := differentialIndependent_const_add hF c hy with hcyDef
  set ey := AlgEquiv.ofBijective (differentialJetFieldEval F hy)
    ⟨jetFieldEval_injective hy, jetFieldEval_surjective hF hy hytop⟩ with heyDef
  have hjet : ey (algebraMap (JetPoly F Unit) (JetField F Unit) (MvPolynomial.X ((), 0))) = y := by
    simp only [heyDef, AlgEquiv.ofBijective_apply]
    rw [jetFieldEval_algebraMap, jetPolyEval_X, differentialJet_zero]
  have hsymm : ey.symm y = algebraMap (JetPoly F Unit) (JetField F Unit) (MvPolynomial.X ((), 0)) :=
    by rw [← hjet, AlgEquiv.symm_apply_apply]
  simp only [translationAutomorphism, AlgEquiv.trans_apply, ← heyDef, hsymm,
    AlgEquiv.ofBijective_apply]
  rw [jetFieldEval_algebraMap, jetPolyEval_X, differentialJet_zero]

end

end GaloisForLFunctions.HTGeometry
