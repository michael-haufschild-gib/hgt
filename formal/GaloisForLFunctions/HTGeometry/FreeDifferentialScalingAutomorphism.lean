import GaloisForLFunctions.HTGeometry.FreeDifferentialFieldPresentation

/-!
# The scaling automorphisms of a free differential field

Scaling a free differential generator by a nonzero constant gives another free differential
generator of the same field, so the two jet evaluations differ by a differential automorphism.
This is the multiplicative deck group of the logarithmic derivative: the automorphism fixes
`y′/y` and multiplies `y`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

omit [Differential F] [DifferentialAlgebra F E] in
/-- Scaling by a base constant multiplies every jet. -/
theorem differentialJet_const_mul (hF : ∀ a : F, (algebraMap F E a)′ = 0) (a : F) (y : E) (n : ℕ) :
    differentialJet n (algebraMap F E a * y) = algebraMap F E a * differentialJet n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, ih, differentialJet_succ]
      have hleib := Differential.deriv.leibniz (algebraMap F E a) (differentialJet n y)
      simp only [smul_eq_mul] at hleib
      rw [hleib, hF a, mul_zero, add_zero]

omit [Differential F] [DifferentialAlgebra F E] in
/-- Scaling a differentially independent element by a nonzero constant keeps it differentially
independent. -/
theorem differentialIndependent_const_mul (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    DifferentialIndependent F (fun _ : Unit ↦ algebraMap F E a * y) := by
  classical
  have hinj : Function.Injective (differentialJetEval F (algebraMap F E a * y)) := by
    have hcomp : (differentialJetEval F (algebraMap F E a * y) : JetPoly F Unit →ₐ[F] E)
        = (differentialJetEval F y).comp
          (MvPolynomial.aeval fun p : Unit × ℕ =>
            (MvPolynomial.C a * MvPolynomial.X p : JetPoly F Unit)) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp only [differentialJetEval, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul,
        MvPolynomial.aeval_C]
      rw [differentialJet_const_mul hF]
    rw [hcomp, AlgHom.coe_comp]
    refine Function.Injective.comp (jetPolyEval_injective hy) ?_
    -- the coordinate scaling is an automorphism of the jet polynomial ring
    set S : JetPoly F Unit →ₐ[F] JetPoly F Unit :=
      MvPolynomial.aeval (fun p : Unit × ℕ =>
        (MvPolynomial.C a * MvPolynomial.X p : JetPoly F Unit)) with hSdef
    set S' : JetPoly F Unit →ₐ[F] JetPoly F Unit :=
      MvPolynomial.aeval (fun p : Unit × ℕ =>
        (MvPolynomial.C a⁻¹ * MvPolynomial.X p : JetPoly F Unit)) with hS'def
    have hscale : Function.Bijective S := by
      refine Function.bijective_iff_has_inverse.mpr ⟨S', ?_, ?_⟩
      · intro q
        induction q using MvPolynomial.induction_on with
        | C r => simp [hSdef, hS'def]
        | add p q hp hq => simp [map_add, hp, hq]
        | mul_X p n hp =>
            simp only [hSdef, hS'def, map_mul, MvPolynomial.aeval_X, map_mul,
              MvPolynomial.aeval_C] at hp ⊢
            rw [hp, MvPolynomial.algebraMap_eq, ← mul_assoc (MvPolynomial.C a),
              ← MvPolynomial.C_mul, mul_inv_cancel₀ ha, map_one, one_mul]
      · intro q
        induction q using MvPolynomial.induction_on with
        | C r => simp [hSdef, hS'def]
        | add p q hp hq => simp [map_add, hp, hq]
        | mul_X p n hp =>
            simp only [hSdef, hS'def, map_mul, MvPolynomial.aeval_X, map_mul,
              MvPolynomial.aeval_C] at hp ⊢
            rw [hp, MvPolynomial.algebraMap_eq, ← mul_assoc (MvPolynomial.C a⁻¹),
              ← MvPolynomial.C_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    exact hscale.injective
  exact hinj


/-- Scaling by a nonzero constant does not change the generated differential field. -/
theorem differentialAdjoin_const_mul {a : F} (ha : a ≠ 0) (y : E) :
    differentialAdjoin F ({algebraMap F E a * y} : Set E) = differentialAdjoin F ({y} : Set E) := by
  have hmem : ∀ b : F, b ≠ 0 → ∀ z : E,
      algebraMap F E b * z ∈ differentialAdjoin F ({z} : Set E) := by
    intro b _ z
    exact (differentialAdjoin F ({z} : Set E)).mul_mem
      ((differentialAdjoin F ({z} : Set E)).algebraMap_mem b)
      (subset_differentialAdjoin F _ rfl)
  refine le_antisymm ?_ ?_
  · exact differentialAdjoin_le F (by simpa using hmem a ha y)
      (derivationClosed_differentialAdjoin F _)
  · refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
    have hgoal : y ∈ differentialAdjoin F ({algebraMap F E a * y} : Set E) := by
      have h1 : algebraMap F E a⁻¹ * (algebraMap F E a * y)
          ∈ differentialAdjoin F ({algebraMap F E a * y} : Set E) :=
        hmem a⁻¹ (inv_ne_zero ha) _
      have h2 : algebraMap F E a⁻¹ * (algebraMap F E a * y) = y := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
      rwa [h2] at h1
    simpa using hgoal

/-- **The scaling automorphism.**  A nonzero base constant `a` induces a differential
`F`-automorphism of a freely differentially generated field multiplying the generator by `a`. -/
def scalingAutomorphism (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) : E ≃ₐ[F] E :=
  let hay := differentialIndependent_const_mul hF ha hy
  let haytop : differentialAdjoin F ({algebraMap F E a * y} : Set E) = ⊤ := by
    rw [differentialAdjoin_const_mul ha y, hytop]
  (AlgEquiv.ofBijective (differentialJetFieldEval F hy)
      ⟨jetFieldEval_injective hy, jetFieldEval_surjective hF hy hytop⟩).symm.trans
    (AlgEquiv.ofBijective (differentialJetFieldEval F hay)
      ⟨jetFieldEval_injective hay, jetFieldEval_surjective hF hay haytop⟩)

theorem scalingAutomorphism_deriv (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) (z : E) :
    scalingAutomorphism hF ha hy hytop z′ = (scalingAutomorphism hF ha hy hytop z)′ := by
  classical
  set hay := differentialIndependent_const_mul hF ha hy with hayDef
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
  simp only [scalingAutomorphism, AlgEquiv.trans_apply, ← heyDef]
  rw [hsymmderiv]
  have : (AlgEquiv.ofBijective (differentialJetFieldEval F hay)
      ⟨jetFieldEval_injective hay, jetFieldEval_surjective hF hay (by
        rw [differentialAdjoin_const_mul ha y, hytop])⟩ : JetField F Unit ≃ₐ[F] E)
      ((ey.symm z)′) = differentialJetFieldEval F hay ((ey.symm z)′) := rfl
  rw [this]
  rw [jetFieldEval_deriv hF hay]
  rfl

theorem scalingAutomorphism_generator (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {a : F} (ha : a ≠ 0) {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    scalingAutomorphism hF ha hy hytop y = algebraMap F E a * y := by
  classical
  set hay := differentialIndependent_const_mul hF ha hy with hayDef
  set ey := AlgEquiv.ofBijective (differentialJetFieldEval F hy)
    ⟨jetFieldEval_injective hy, jetFieldEval_surjective hF hy hytop⟩ with heyDef
  have hjet : ey (algebraMap (JetPoly F Unit) (JetField F Unit) (MvPolynomial.X ((), 0))) = y := by
    simp only [heyDef, AlgEquiv.ofBijective_apply]
    rw [jetFieldEval_algebraMap, jetPolyEval_X, differentialJet_zero]
  have hsymm : ey.symm y = algebraMap (JetPoly F Unit) (JetField F Unit) (MvPolynomial.X ((), 0)) :=
    by rw [← hjet, AlgEquiv.symm_apply_apply]
  simp only [scalingAutomorphism, AlgEquiv.trans_apply, ← heyDef, hsymm,
    AlgEquiv.ofBijective_apply]
  rw [jetFieldEval_algebraMap, jetPolyEval_X, differentialJet_zero]

end

end GaloisForLFunctions.HTGeometry
