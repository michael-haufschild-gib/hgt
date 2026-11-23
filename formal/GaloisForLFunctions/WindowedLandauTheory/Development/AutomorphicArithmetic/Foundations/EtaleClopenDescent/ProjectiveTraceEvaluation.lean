import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTraceQuotient

/-! Evaluating the multiplication trace of a projective algebra gives the
trace on the rational fibre. -/

noncomputable section

namespace GlobalTheory.SchemeCohomology

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
  [Module.Finite A B] [Module.Projective A B]

theorem projectiveAlgebraTrace_rationalFibre (e : A →ₐ[k] k) (b : B) :
    e (projectiveAlgebraTrace A B b) =
      Algebra.trace k (B ⧸ (RingHom.ker e.toRingHom).map (algebraMap A B)) (Ideal.Quotient.mk _ b) := by
  let p := RingHom.ker e.toRingHom
  let J := p.map (algebraMap A B)
  let Q := B ⧸ J
  have hs : Function.Surjective e := fun r => ⟨algebraMap k A r, e.commutes r⟩
  letI : p.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hs
  let e₀ : A ⧸ p ≃+* k := (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv
  have hc : (algebraMap k Q).comp e₀.toRingHom = (RingEquiv.refl Q).toRingHom.comp
      (algebraMap (A ⧸ p) Q) := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    change Ideal.Quotient.mk J (algebraMap k B (e a)) =
      Ideal.Quotient.mk J (algebraMap A B a)
    apply Ideal.Quotient.eq.mpr
    have ha : a - algebraMap k A (e a) ∈ p := by
      change e (a - algebraMap k A (e a)) = 0
      rw [map_sub, e.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hm := Ideal.mem_map_of_mem (algebraMap A B) ha
    rw [map_sub, ← IsScalarTower.algebraMap_apply] at hm
    simpa only [neg_sub] using J.neg_mem hm
  have h := trace_quotient_eq_projectiveAlgebraTrace p b
  rw [Algebra.trace_eq_of_equiv_equiv e₀ (RingEquiv.refl Q) hc] at h
  have h' := congrArg e₀ h
  change e₀ (e₀.symm (Algebra.trace k Q (Ideal.Quotient.mk _ b))) =
    e (projectiveAlgebraTrace A B b) at h'
  rw [RingEquiv.apply_symm_apply] at h'
  exact h'.symm

end GlobalTheory.SchemeCohomology
