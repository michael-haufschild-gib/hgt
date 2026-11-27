import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PadicComplexFieldEquiv

/-! Extension of field embeddings across transcendence bases. -/

noncomputable section

open Cardinal

namespace GlobalTheory.TeichPlace

private theorem exists_equiv_of_basis {F L M ι κ : Type} [Field F] [Field L] [Field M]
    [Algebra F L] [Algebra F M] [IsAlgClosed L] [IsAlgClosed M]
    {v : ι → L} {w : κ → M} (hv : IsTranscendenceBasis F v)
    (hw : IsTranscendenceBasis F w) (e : ι ≃ κ) :
    ∃ σ : L ≃+* M, ∀ x : F, σ (algebraMap F L x) = algebraMap F M x := by
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis w hw
  let E := Algebra.adjoin F (Set.range v)
  let J := Algebra.adjoin F (Set.range w)
  let φ : E ≃ₐ[F] J := hv.1.aevalEquiv.symm.trans
    ((MvPolynomial.renameEquiv F e).trans hw.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv L M φ.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply F E L, IsScalarTower.algebraMap_apply F J M,
    IsAlgClosure.equivOfEquiv_algebraMap]
  exact congrArg (algebraMap J M) (φ.commutes x)

/-- Any two embeddings of a countable field into the complex field are
conjugate by a field automorphism. Their transcendence bases have the same cardinality. -/
theorem exists_complex_aut_of_countable {F : Type} [Field F] [Countable F]
    (a b : F →+* ℂ) : ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (a x) = b x := by
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hF : #F ≤ ℵ₀ := Cardinal.mk_le_aleph0
  letI A : Algebra F ℂ := a.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F ℂ
  have hsc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
    _ hs hF hC
  letI B : Algebra F ℂ := b.toAlgebra
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F ℂ
  have htc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
    _ ht hF hC
  obtain ⟨e⟩ := Cardinal.eq.mp (hsc.symm.trans htc)
  exact @exists_equiv_of_basis F ℂ ℂ s t _ _ _ A B _ _ _ _ hs ht e

/-- Choose the p-adic-to-complex field equivalence to carry a specified
countable subfield embedding to its prescribed complex embedding. -/
theorem exists_padicAlgCl_ringEquiv_complex_comp_eq (p : ℕ) [Fact p.Prime]
    {K : Type} [Field K] [Countable K] (a : K →+* PadicAlgCl p) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl p ≃+* ℂ, e.toRingHom.comp a = b := by
  obtain ⟨e₀⟩ := nonempty_padicAlgCl_ringEquiv_complex p
  obtain ⟨σ, hσ⟩ := exists_complex_aut_of_countable (e₀.toRingHom.comp a) b
  exact ⟨e₀.trans σ, RingHom.ext hσ⟩

end GlobalTheory.TeichPlace
