import GaloisForLFunctions.GaloisTheoryOfZeros.TheMaximalRealSubfieldOfTheZeroField
import GaloisForLFunctions.HTGeometry.EigenLogDerivNormalization

/-!
# The source equations of the signed widths

Translation to the fibre ordinate followed by a Gaussian rotation produces a
monic equation for all signed widths, with their analytic multiplicities.
Realness eliminates the imaginary Gaussian phases, so its coefficients remain
in the original complete-fibre source field.
-/

noncomputable section
set_option autoImplicit false
open Complex Polynomial Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem gaussian_power_phases (n : ℕ) :
    I^n = 1 ∨ I^n = I ∨ I^n = -1 ∨ I^n = -I := by
  induction n with
  | zero => exact Or.inl (pow_zero I)
  | succ n ih =>
    rcases ih with h | h | h | h
    · exact Or.inr (Or.inl (by rw [pow_succ,h,one_mul]))
    · exact Or.inr (Or.inr (Or.inl (by rw [pow_succ,h,I_mul_I])))
    · exact Or.inr (Or.inr (Or.inr (by rw [pow_succ,h,neg_one_mul])))
    · exact Or.inl (by rw [pow_succ,h,neg_mul,I_mul_I,neg_neg])

/-- A Gaussian phase cannot enlarge a real coefficient field while leaving its value real. -/
private theorem gaussian_phase_real_mem (K : Subfield ℂ)
    (hK : K ≤ Complex.ofRealHom.fieldRange) {z y : ℂ}
    (hz : z ∈ K) (hy : y ∈ Complex.ofRealHom.fieldRange) (n : ℕ)
    (he : y = I^n*z) : y ∈ K := by
  obtain ⟨x,hx⟩ := hK hz
  obtain ⟨r,hr⟩ := hy
  rcases gaussian_power_phases n with h | h | h | h
  · rw [he,h,one_mul]
    exact hz
  · have him := congrArg Complex.im he
    rw [h,← hx,← hr] at him
    have hx0 : x = 0 := by simpa using him.symm
    have hz0 : z = 0 := by rw [← hx,hx0]; rfl
    rw [he,hz0,mul_zero]
    exact K.zero_mem
  · rw [he,h,neg_one_mul]
    exact K.neg_mem hz
  · have him := congrArg Complex.im he
    rw [h,← hx,← hr] at him
    have hx0 : x = 0 := by
      have hp : (0 : ℝ) = -x := by simpa using him
      linarith only [hp]
    have hz0 : z = 0 := by rw [← hx,hx0]; rfl
    rw [he,hz0,mul_zero]
    exact K.zero_mem

/-- The real polynomial recording every signed width in a complete ordinate fibre. -/
def realWidthFibrePolynomial (t : ℝ) : ℝ[X] :=
  ∏ q ∈ ordinateFibreCopies t, (X-C (xiSpectralPoint q).im)

/-- The source fibre equation translated to its ordinate. -/
def translatedSourceFibrePolynomial (q : XiZeroCopy) : fullFibreSourceField[X] :=
  (sourceFibrePolynomial (xiSpectralPoint q).re).comp
    (X+C ⟨((xiSpectralPoint q).re : ℂ),ordinate_mem_fullFibreSourceField q⟩)

private theorem realWidthFibrePolynomial_map (t : ℝ) :
    (realWidthFibrePolynomial t).map Complex.ofRealHom =
      ∏ r ∈ ordinateFibreCopies t, (X-C (zeroWidth r) : ℂ[X]) := by
  classical
  change (Polynomial.mapRingHom Complex.ofRealHom)
    (∏ r ∈ ordinateFibreCopies t, (X-C (xiSpectralPoint r).im)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r _
  change (X-C (xiSpectralPoint r).im : ℝ[X]).map Complex.ofRealHom = X-C (zeroWidth r)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- Gaussian rotation transports the complete source equation to the full width divisor. -/
theorem translatedSourceFibrePolynomial_rotation (q : XiZeroCopy) :
    ((translatedSourceFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ)).comp (C I*X) =
      C (I^(ordinateFibreCopies (xiSpectralPoint q).re).card) *
        (realWidthFibrePolynomial (xiSpectralPoint q).re).map Complex.ofRealHom := by
  classical
  let t := (xiSpectralPoint q).re
  have htranslate :
      ((X+C ⟨(t : ℂ),ordinate_mem_fullFibreSourceField q⟩ : fullFibreSourceField[X]).map
        (algebraMap fullFibreSourceField ℂ)).comp (C I*X) = C I*X+C (t : ℂ) := by
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    rfl
  rw [translatedSourceFibrePolynomial, Polynomial.map_comp, Polynomial.comp_assoc, htranslate,
    sourceFibrePolynomial_map_eq_prod, realWidthFibrePolynomial_map]
  change (Polynomial.eval₂RingHom C (C I*X+C (t : ℂ)))
    (∏ r ∈ ordinateFibreCopies t, (X-C (xiSpectralPoint r) : ℂ[X])) = _
  rw [map_prod]
  have hf (r : XiZeroCopy) (hr : r ∈ ordinateFibreCopies t) :
      (Polynomial.eval₂RingHom C (C I*X+C (t : ℂ))) (X-C (xiSpectralPoint r)) =
        C I*(X-C (zeroWidth r)) := by
    change (X-C (xiSpectralPoint r)).comp (C I*X+C (t : ℂ)) = _
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have ho := zeroImaginaryOffset_eq r
    change xiSpectralPoint r - ((xiSpectralPoint r).re : ℂ) = I*zeroWidth r at ho
    rw [(mem_ordinateFibreCopies t r).mp hr] at ho
    have hw : xiSpectralPoint r = (t : ℂ)+I*zeroWidth r := by linear_combination ho
    rw [hw, map_add, map_mul]
    ring
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_const, ← map_pow]

/-- Rotation leaves the coefficients of the full width equation in the source field. -/
theorem realWidthFibrePolynomial_coeff_mem_sourceField (q : XiZeroCopy) (j : ℕ) :
    ((realWidthFibrePolynomial (xiSpectralPoint q).re).coeff j : ℂ) ∈ fullFibreSourceField := by
  let n := (ordinateFibreCopies (xiSpectralPoint q).re).card
  let a : fullFibreSourceField := (translatedSourceFibrePolynomial q).coeff j
  let b : ℝ := (realWidthFibrePolynomial (xiSpectralPoint q).re).coeff j
  have hc := congrArg (fun P : ℂ[X] => P.coeff j) (translatedSourceFibrePolynomial_rotation q)
  simp only [HTGeometry.coeff_comp_C_mul_X, Polynomial.coeff_map, Polynomial.coeff_C_mul] at hc
  change I^j*(a : ℂ) = I^n*(b : ℂ) at hc
  have hinv : (-I)^n*I^n = 1 := by
    rw [← mul_pow,neg_mul,I_mul_I,neg_neg,one_pow]
  have he : (b : ℂ) = I^(j+n)*((-1:ℂ)^n*(a : ℂ)) := by
    calc
      (b : ℂ) = ((-I)^n*I^n)*(b : ℂ) := by rw [hinv,one_mul]
      _ = (-I)^n*(I^n*(b : ℂ)) := by ring
      _ = (-I)^n*(I^j*(a : ℂ)) := by rw [hc]
      _ = I^(j+n)*((-1:ℂ)^n*(a : ℂ)) := by rw [neg_pow,pow_add]; ring
  exact gaussian_phase_real_mem fullFibreSourceField fullFibreSourceField_le_real
    (fullFibreSourceField.mul_mem
      (fullFibreSourceField.pow_mem (fullFibreSourceField.neg_mem fullFibreSourceField.one_mem) n)
      a.property) ⟨b,rfl⟩ (j+n) he

private theorem exists_sourceWidthFibrePolynomial (q : XiZeroCopy) :
    ∃ P : fullFibreSourceField[X], P.map (algebraMap fullFibreSourceField ℂ) =
      (realWidthFibrePolynomial (xiSpectralPoint q).re).map Complex.ofRealHom := by
  have h : (realWidthFibrePolynomial (xiSpectralPoint q).re).map Complex.ofRealHom ∈
      Polynomial.lifts (algebraMap fullFibreSourceField ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    refine ⟨⟨_,realWidthFibrePolynomial_coeff_mem_sourceField q j⟩,?_⟩
    rw [Polynomial.coeff_map]
    rfl
  exact h

/-- The monic source-field equation of all widths in a nonempty ordinate fibre. -/
def sourceWidthFibrePolynomial (q : XiZeroCopy) : fullFibreSourceField[X] :=
  Classical.choose (exists_sourceWidthFibrePolynomial q)

theorem sourceWidthFibrePolynomial_map (q : XiZeroCopy) :
    (sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ) =
      (realWidthFibrePolynomial (xiSpectralPoint q).re).map Complex.ofRealHom :=
  Classical.choose_spec (exists_sourceWidthFibrePolynomial q)

private theorem sourceWidthFibrePolynomial_map_eq_rootProduct (q : XiZeroCopy) :
    (sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ) =
      (((ordinateFibreCopies (xiSpectralPoint q).re).val.map zeroWidth).map
        (fun z : ℂ => (X-C z : ℂ[X]))).prod := by
  rw [sourceWidthFibrePolynomial_map,realWidthFibrePolynomial_map,Multiset.map_map]
  rfl

/-- The width equation preserves the complete analytic multiplicity of the fibre. -/
theorem sourceWidthFibrePolynomial_roots (q : XiZeroCopy) :
    ((sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ)).roots =
      (ordinateFibreCopies (xiSpectralPoint q).re).val.map zeroWidth := by
  rw [sourceWidthFibrePolynomial_map_eq_rootProduct,roots_multiset_prod_X_sub_C]

theorem sourceWidthFibrePolynomial_monic (q : XiZeroCopy) :
    (sourceWidthFibrePolynomial q).Monic := by
  have hm : ((sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ)).Monic := by
    rw [sourceWidthFibrePolynomial_map_eq_rootProduct]
    exact monic_multisetProd_X_sub_C _
  exact Polynomial.monic_map_iff.mp hm

/-- Degree equals the full analytic mass, with repeated widths retained. -/
theorem sourceWidthFibrePolynomial_natDegree (q : XiZeroCopy) :
    (sourceWidthFibrePolynomial q).natDegree = (ordinateFibreCopies (xiSpectralPoint q).re).card := by
  calc
    (sourceWidthFibrePolynomial q).natDegree =
        ((sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ)).natDegree :=
      ((sourceWidthFibrePolynomial_monic q).natDegree_map _).symm
    _ = _ := by
      rw [sourceWidthFibrePolynomial_map_eq_rootProduct,natDegree_multiset_prod_X_sub_C_eq_card]
      simp

/-- The source equation has exactly the signed widths in the selected complete fibre as roots. -/
theorem sourceWidthFibrePolynomial_rootSet (q : XiZeroCopy) (z : ℂ) :
    z ∈ (sourceWidthFibrePolynomial q).rootSet ℂ ↔
      ∃ r ∈ ordinateFibreCopies (xiSpectralPoint q).re, zeroWidth r = z := by
  rw [Polynomial.mem_rootSet',Polynomial.aeval_def,← Polynomial.eval_map]
  change ((sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ)) ≠ 0 ∧
    ((sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ)).IsRoot z ↔ _
  rw [← Polynomial.mem_roots',sourceWidthFibrePolynomial_roots]
  simp only [Multiset.mem_map,Finset.mem_val]

/-- Every complex root of a width equation is real, without assuming any width vanishes. -/
theorem sourceWidthFibrePolynomial_hyperbolic (q : XiZeroCopy) :
    ∀ z ∈ (sourceWidthFibrePolynomial q).rootSet ℂ, z.im = 0 := by
  intro z hz
  obtain ⟨r,_,hr⟩ := (sourceWidthFibrePolynomial_rootSet q z).mp hz
  rw [← hr]
  simp only [zeroWidth,ofReal_im]

private theorem union_sourceWidthFibre_rootSet :
    (⋃ q : XiZeroCopy, (sourceWidthFibrePolynomial q).rootSet ℂ) = Set.range zeroWidth := by
  ext z
  simp only [Set.mem_iUnion,Set.mem_range,sourceWidthFibrePolynomial_rootSet]
  constructor
  · rintro ⟨q,r,_,hr⟩
    exact ⟨r,hr⟩
  · rintro ⟨q,rfl⟩
    exact ⟨q,q,(mem_ordinateFibreCopies _ q).mpr rfl,rfl⟩

/-- The complete real width field is the compositum of its source splitting fields. -/
theorem realWidthField_eq_iSup_sourceWidthFields :
    realWidthField = ⨆ q : XiZeroCopy,
      IntermediateField.adjoin fullFibreSourceField ((sourceWidthFibrePolynomial q).rootSet ℂ) := by
  rw [realWidthField,← union_sourceWidthFibre_rootSet,IntermediateField.adjoin_iUnion]

/-- The explicit source equations prove normality of the entire width extension. -/
theorem realWidthField_normal_from_source : Normal fullFibreSourceField realWidthField := by
  have hn (q : XiZeroCopy) : Normal fullFibreSourceField
      (IntermediateField.adjoin fullFibreSourceField ((sourceWidthFibrePolynomial q).rootSet ℂ)) := by
    letI := IntermediateField.adjoin_rootSet_isSplittingField
      (IsAlgClosed.splits ((sourceWidthFibrePolynomial q).map (algebraMap fullFibreSourceField ℂ)))
    exact Normal.of_isSplittingField (sourceWidthFibrePolynomial q)
  letI := hn
  rw [realWidthField_eq_iSup_sourceWidthFields]
  infer_instance

/-- Source-field automorphisms send a width to another width in the same complete ordinate fibre. -/
theorem sourceWidthFibrePolynomial_aut_image
    (E : IntermediateField fullFibreSourceField ℂ) (σ : E ≃ₐ[fullFibreSourceField] E)
    (q : XiZeroCopy) (hqE : zeroWidth q ∈ E) :
    ∃ r ∈ ordinateFibreCopies (xiSpectralPoint q).re,
      (σ ⟨zeroWidth q,hqE⟩ : ℂ) = zeroWidth r := by
  let P := sourceWidthFibrePolynomial q
  have hq : zeroWidth q ∈ P.rootSet ℂ :=
    (sourceWidthFibrePolynomial_rootSet q _).mpr
      ⟨q,(mem_ordinateFibreCopies _ q).mpr rfl,rfl⟩
  have heval : aeval (⟨zeroWidth q,hqE⟩ : E) P = 0 := by
    apply (IntermediateField.val E).injective
    change (IntermediateField.val E) (aeval (⟨zeroWidth q,hqE⟩ : E) P) =
      (IntermediateField.val E) 0
    rw [map_zero,← Polynomial.aeval_algHom_apply (IntermediateField.val E)]
    exact (Polynomial.mem_rootSet'.mp hq).2
  have hσeval : aeval (σ ⟨zeroWidth q,hqE⟩) P = 0 := by
    rw [Polynomial.aeval_algHom_apply σ _ P,heval,map_zero]
  have hC : aeval (σ ⟨zeroWidth q,hqE⟩ : ℂ) P = 0 := by
    change aeval ((IntermediateField.val E) (σ ⟨zeroWidth q,hqE⟩)) P = 0
    rw [Polynomial.aeval_algHom_apply (IntermediateField.val E) _ P,hσeval,map_zero]
  have hroot : (σ ⟨zeroWidth q,hqE⟩ : ℂ) ∈ P.rootSet ℂ :=
    Polynomial.mem_rootSet'.mpr ⟨(Polynomial.mem_rootSet'.mp hq).1,hC⟩
  obtain ⟨r,hr,heq⟩ := (sourceWidthFibrePolynomial_rootSet q _).mp hroot
  exact ⟨r,hr,heq.symm⟩

/-- Any global width reversal is central in the Galois group of the entire width field. -/
theorem realWidth_reversal_central
    (ν : realWidthField ≃ₐ[fullFibreSourceField] realWidthField)
    (hν : ∀ q : XiZeroCopy,
      ν ⟨zeroWidth q,zeroWidth_mem_realWidthField q⟩ =
        -(⟨zeroWidth q,zeroWidth_mem_realWidthField q⟩ : realWidthField))
    (σ : realWidthField ≃ₐ[fullFibreSourceField] realWidthField) :
    ν.trans σ = σ.trans ν := by
  have hzero (q : XiZeroCopy) :
      σ (ν ⟨zeroWidth q,zeroWidth_mem_realWidthField q⟩) =
        ν (σ ⟨zeroWidth q,zeroWidth_mem_realWidthField q⟩) := by
    obtain ⟨r,_,hr⟩ := sourceWidthFibrePolynomial_aut_image realWidthField σ q
      (zeroWidth_mem_realWidthField q)
    have he : σ ⟨zeroWidth q,zeroWidth_mem_realWidthField q⟩ =
        ⟨zeroWidth r,zeroWidth_mem_realWidthField r⟩ := Subtype.ext hr
    rw [hν,map_neg,he,hν]
  have heq := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
    (S := realWidthField) rfl (φ₁ := (ν.trans σ).toAlgHom) (φ₂ := (σ.trans ν).toAlgHom)
    (by rintro z ⟨q,rfl⟩; exact hzero q)
  exact AlgEquiv.ext fun z => DFunLike.congr_fun heq z

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.translatedSourceFibrePolynomial_rotation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.realWidthFibrePolynomial_coeff_mem_sourceField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceWidthFibrePolynomial_roots
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceWidthFibrePolynomial_hyperbolic
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.realWidthField_normal_from_source

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceWidthFibrePolynomial_aut_image
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.realWidth_reversal_central
