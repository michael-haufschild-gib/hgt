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

variable {F E : Type*} [Field F] [Field E] [Differential E] [Algebra F E]

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
            rw [hp]
            field_simp
            ring
      · intro q
        induction q using MvPolynomial.induction_on with
        | C r => simp [hSdef, hS'def]
        | add p q hp hq => simp [map_add, hp, hq]
        | mul_X p n hp =>
            simp only [hSdef, hS'def, map_mul, MvPolynomial.aeval_X, map_mul,
              MvPolynomial.aeval_C] at hp ⊢
            rw [hp]
            field_simp
            ring
    exact hscale.injective
  exact hinj

end

end GaloisForLFunctions.HTGeometry
