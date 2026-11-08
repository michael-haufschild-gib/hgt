import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockExtractions
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeCoreProjections

/-! Each truncated upper block retracts from the original adjacent complex.
Extraction and realization recover exactly the original core projection in
all three tagged degrees; their boundary compatibility follows from that identity. -/

noncomputable section
open scoped Classical
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

private theorem tag_degree_zero (t : TwoPrimeFaceTag) : t.degree=0 ↔ t=.base := by
  cases t <;> simp [TwoPrimeFaceTag.degree]

private theorem tag_degree_one (t : TwoPrimeFaceTag) : t.degree=1 ↔ t=.two ∨ t=.three := by
  cases t <;> simp [TwoPrimeFaceTag.degree]

private theorem tag_degree_two (t : TwoPrimeFaceTag) : t.degree=2 ↔ t=.both := by
  cases t <;> simp [TwoPrimeFaceTag.degree]

/-- Core projection on a bounded basis vector either retains it or annihilates it. -/
theorem twoPrimeCoreCutoffProjection_basis (k N : ℕ) (c : TwoPrimeCoreFace)
    (ct : TwoPrimeBlockIndex k N) :
    (twoPrimeCoreCutoffProjection R k N c (twoPrimeBlockBasis R k N ct)).val =
      if ct.val.1=c then (twoPrimeBlockBasis R k N ct).val else 0 := by
  change twoPrimeCoreProjection R k c (twoPrimeBlockBasis R k N ct).val = _
  simp only [twoPrimeBlockBasis_val,twoPrimeCoreProjection_basis,twoPrimeFaceCore_tagged]

/-- Extracting and realizing the bottom coefficient is the full bottom-degree core projection. -/
theorem twoPrimeBase_realization_extraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (twoPrimeBlockScalarRealization R c .base N).comp (twoPrimeBlockScalarExtraction R c .base N) =
      twoPrimeCoreCutoffProjection R c.val.card N c := by
  apply (twoPrimeBlockBasis R c.val.card N).ext
  intro ct
  apply Subtype.ext
  change (twoPrimeBlockScalarExtraction R c .base N (twoPrimeBlockBasis R c.val.card N ct)).val •
    twoPrimeBaseVector R c = (twoPrimeCoreCutoffProjection R c.val.card N c
      (twoPrimeBlockBasis R c.val.card N ct)).val
  refine (congrArg (fun a : R => a • twoPrimeBaseVector R c)
    (twoPrimeBlockScalarExtraction_basis R c .base N ct)).trans ?_
  refine Eq.trans ?_ (twoPrimeCoreCutoffProjection_basis R c.val.card N c ct).symm
  by_cases h : ct.val.1=c
  · have hd : ct.val.2.degree=0 := by
      have hg := ct.property.1
      rw [h] at hg
      omega
    have ht : ct.val=(c,TwoPrimeFaceTag.base) := Prod.ext h ((tag_degree_zero _).mp hd)
    rw [if_pos ht,if_pos h,one_smul]
    exact (twoPrimeBlockBasis_eq_vector R c .base N ct ht).symm
  · have ht : ct.val ≠ (c,TwoPrimeFaceTag.base) := fun he => h (congrArg Prod.fst he)
    rw [if_neg ht,if_neg h,zero_smul]

/-- Extracting and realizing the top coefficient is the full top-degree core projection. -/
theorem twoPrimeTop_realization_extraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (twoPrimeBlockScalarRealization R c .both N).comp (twoPrimeBlockScalarExtraction R c .both N) =
      twoPrimeCoreCutoffProjection R (c.val.card+2) N c := by
  apply (twoPrimeBlockBasis R (c.val.card+2) N).ext
  intro ct
  apply Subtype.ext
  change (twoPrimeBlockScalarExtraction R c .both N (twoPrimeBlockBasis R (c.val.card+2) N ct)).val •
    twoPrimeTopVector R c = (twoPrimeCoreCutoffProjection R (c.val.card+2) N c
      (twoPrimeBlockBasis R (c.val.card+2) N ct)).val
  refine (congrArg (fun a : R => a • twoPrimeTopVector R c)
    (twoPrimeBlockScalarExtraction_basis R c .both N ct)).trans ?_
  refine Eq.trans ?_ (twoPrimeCoreCutoffProjection_basis R (c.val.card+2) N c ct).symm
  by_cases h : ct.val.1=c
  · have hd : ct.val.2.degree=2 := by
      have hg := ct.property.1
      rw [h] at hg
      omega
    have ht : ct.val=(c,TwoPrimeFaceTag.both) := Prod.ext h ((tag_degree_two _).mp hd)
    rw [if_pos ht,if_pos h,one_smul]
    exact (twoPrimeBlockBasis_eq_vector R c .both N ct ht).symm
  · have ht : ct.val ≠ (c,TwoPrimeFaceTag.both) := fun he => h (congrArg Prod.fst he)
    rw [if_neg ht,if_neg h,zero_smul]

/-- Extracting and realizing the middle pair is the full middle-degree core projection. -/
theorem twoPrimeMiddle_realization_extraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (twoPrimeBlockMiddleRealization R c N).comp (twoPrimeBlockMiddleExtraction R c N) =
      twoPrimeCoreCutoffProjection R (c.val.card+1) N c := by
  apply (twoPrimeBlockBasis R (c.val.card+1) N).ext
  intro ct
  apply Subtype.ext
  change
    (twoPrimeBlockScalarExtraction R c .two N (twoPrimeBlockBasis R (c.val.card+1) N ct)).val •
        twoPrimeTwoVector R c +
      (twoPrimeBlockScalarExtraction R c .three N (twoPrimeBlockBasis R (c.val.card+1) N ct)).val •
        twoPrimeThreeVector R c =
    (twoPrimeCoreCutoffProjection R (c.val.card+1) N c (twoPrimeBlockBasis R (c.val.card+1) N ct)).val
  refine (congrArg₂ (fun a b : R => a • twoPrimeTwoVector R c + b • twoPrimeThreeVector R c)
    (twoPrimeBlockScalarExtraction_basis R c .two N ct)
    (twoPrimeBlockScalarExtraction_basis R c .three N ct)).trans ?_
  refine Eq.trans ?_ (twoPrimeCoreCutoffProjection_basis R (c.val.card+1) N c ct).symm
  by_cases h : ct.val.1=c
  · have hd : ct.val.2.degree=1 := by
      have hg := ct.property.1
      rw [h] at hg
      omega
    rcases (tag_degree_one _).mp hd with h2 | h3
    · have ht : ct.val=(c,TwoPrimeFaceTag.two) := Prod.ext h h2
      have hn : ct.val ≠ (c,TwoPrimeFaceTag.three) := by
        intro he
        have hx := congrArg Prod.snd (ht.symm.trans he)
        cases hx
      rw [if_pos ht,if_neg hn,if_pos h,one_smul,zero_smul,add_zero]
      exact (twoPrimeBlockBasis_eq_vector R c .two N ct ht).symm
    · have ht : ct.val=(c,TwoPrimeFaceTag.three) := Prod.ext h h3
      have hn : ct.val ≠ (c,TwoPrimeFaceTag.two) := by
        intro he
        have hx := congrArg Prod.snd (ht.symm.trans he)
        cases hx
      rw [if_neg hn,if_pos ht,if_pos h,one_smul,zero_smul,zero_add]
      exact (twoPrimeBlockBasis_eq_vector R c .three N ct ht).symm
  · have h2 : ct.val ≠ (c,TwoPrimeFaceTag.two) := fun he => h (congrArg Prod.fst he)
    have h3 : ct.val ≠ (c,TwoPrimeFaceTag.three) := fun he => h (congrArg Prod.fst he)
    rw [if_neg h2,if_neg h3,if_neg h,zero_smul,zero_smul,add_zero]

/-- Extracting the top coefficient intertwines the original boundary with the block column. -/
theorem twoPrimeBlockTopExtraction_boundary (c : TwoPrimeCoreFace) (N : ℕ) :
    (twoPrimeBlockCutoffTop R (twoPrimeCoreHeight c) N).comp (twoPrimeBlockScalarExtraction R c .both N) =
    (twoPrimeBlockMiddleExtraction R c N).comp
      (primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N) := by
  apply LinearMap.ext
  intro x
  apply twoPrimeBlockMiddleRealization_injective R c N
  calc
    _ = primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N
        (twoPrimeBlockScalarRealization R c .both N (twoPrimeBlockScalarExtraction R c .both N x)) :=
      (LinearMap.congr_fun (twoPrimeBlockTopRealization_boundary R c N)
        (twoPrimeBlockScalarExtraction R c .both N x)).symm
    _ = primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N
        (twoPrimeCoreCutoffProjection R (c.val.card+2) N c x) :=
      congrArg (primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N)
        (LinearMap.congr_fun (twoPrimeTop_realization_extraction R c N) x)
    _ = twoPrimeCoreCutoffProjection R (c.val.card+1) N c
        (primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N x) :=
      Subtype.ext (LinearMap.congr_fun (twoPrimeCoreProjection_boundary R (c.val.card+1) c) x.val)
    _ = _ := (LinearMap.congr_fun (twoPrimeMiddle_realization_extraction R c N)
      (primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N x)).symm

/-- Extracting the middle pair intertwines the original boundary with the block row. -/
theorem twoPrimeBlockMiddleExtraction_boundary (c : TwoPrimeCoreFace) (N : ℕ) :
    (twoPrimeBlockCutoffRow R (twoPrimeCoreHeight c) N).comp (twoPrimeBlockMiddleExtraction R c N) =
    (twoPrimeBlockScalarExtraction R c .base N).comp
      (primeCutoffDifferential R (primeValueFunctional R) c.val.card N) := by
  apply LinearMap.ext
  intro x
  apply twoPrimeBlockScalarRealization_injective R c .base N
  calc
    _ = primeCutoffDifferential R (primeValueFunctional R) c.val.card N
        (twoPrimeBlockMiddleRealization R c N (twoPrimeBlockMiddleExtraction R c N x)) :=
      (LinearMap.congr_fun (twoPrimeBlockMiddleRealization_boundary R c N)
        (twoPrimeBlockMiddleExtraction R c N x)).symm
    _ = primeCutoffDifferential R (primeValueFunctional R) c.val.card N
        (twoPrimeCoreCutoffProjection R (c.val.card+1) N c x) :=
      congrArg (primeCutoffDifferential R (primeValueFunctional R) c.val.card N)
        (LinearMap.congr_fun (twoPrimeMiddle_realization_extraction R c N) x)
    _ = twoPrimeCoreCutoffProjection R c.val.card N c
        (primeCutoffDifferential R (primeValueFunctional R) c.val.card N x) :=
      Subtype.ext (LinearMap.congr_fun (twoPrimeCoreProjection_boundary R c.val.card c) x.val)
    _ = _ := (LinearMap.congr_fun (twoPrimeBase_realization_extraction R c N)
      (primeCutoffDifferential R (primeValueFunctional R) c.val.card N x)).symm

/-- The original adjacent complex retracts onto each truncated upper arithmetic block. -/
def twoPrimeUpperBlockRetraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffComplex R (primeValueFunctional R) N).sc' (c.val.card+2) (c.val.card+1) c.val.card ⟶
      twoPrimeUpperBlock R (twoPrimeCoreHeight c) N where
  τ₁ := ModuleCat.ofHom (twoPrimeBlockScalarExtraction R c .both N)
  τ₂ := ModuleCat.ofHom (twoPrimeBlockMiddleExtraction R c N)
  τ₃ := ModuleCat.ofHom (twoPrimeBlockScalarExtraction R c .base N)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change (twoPrimeBlockCutoffTop R (twoPrimeCoreHeight c) N).comp
      (twoPrimeBlockScalarExtraction R c .both N) =
      (twoPrimeBlockMiddleExtraction R c N).comp
        ((primeCutoffComplex R (primeValueFunctional R) N).d ((c.val.card+1)+1) (c.val.card+1)).hom
    simp only [primeCutoffComplex,ChainComplex.of_d]
    exact twoPrimeBlockTopExtraction_boundary R c N
  comm₂₃ := by
    apply ModuleCat.hom_ext
    change (twoPrimeBlockCutoffRow R (twoPrimeCoreHeight c) N).comp
      (twoPrimeBlockMiddleExtraction R c N) =
      (twoPrimeBlockScalarExtraction R c .base N).comp
        ((primeCutoffComplex R (primeValueFunctional R) N).d (c.val.card+1) c.val.card).hom
    simp only [primeCutoffComplex,ChainComplex.of_d]
    exact twoPrimeBlockMiddleExtraction_boundary R c N

/-- Each upper block is a retract through its actual tagged chain representatives. -/
theorem twoPrimeUpperBlock_section (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeUpperBlockRealization R c N ≫ twoPrimeUpperBlockRetraction R c N = 𝟙 _ := by
  apply ShortComplex.Hom.ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact twoPrimeBlockScalarExtraction_realization R c .both N x
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact twoPrimeBlockMiddleExtraction_realization R c N x
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact twoPrimeBlockScalarExtraction_realization R c .base N x

/-- Reconstructing the extracted upper block is precisely the original chain core projection. -/
theorem twoPrimeUpperBlock_projection (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeUpperBlockRetraction R c N ≫ twoPrimeUpperBlockRealization R c N =
      (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ)
        (c.val.card+2) (c.val.card+1) c.val.card).map (twoPrimeCoreChainProjection R c N) := by
  apply ShortComplex.Hom.ext
  · exact ModuleCat.hom_ext (twoPrimeTop_realization_extraction R c N)
  · exact ModuleCat.hom_ext (twoPrimeMiddle_realization_extraction R c N)
  · exact ModuleCat.hom_ext (twoPrimeBase_realization_extraction R c N)

#print axioms twoPrimeUpperBlockRetraction
#print axioms twoPrimeUpperBlock_section
#print axioms twoPrimeUpperBlock_projection
#print axioms twoPrimeBase_realization_extraction
#print axioms twoPrimeMiddle_realization_extraction
#print axioms twoPrimeTop_realization_extraction
end GaloisForLFunctions.EffectiveScalingGeometry
