import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverGenericGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineTraceFunctionField

/-! Trace of a section on an affine intersection is computed by trace
in the function fields. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)} [Smooth s] [Smooth t]
  {f : Y ⟶ X} [IsFinite f] [Etale f] [IsDominant f] {ι κ : Type}
  {U : ι → X.Opens} {V : κ → Y.Opens}

theorem IsAffCover.sectionRationalForms_trace (hf : f ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := f.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower hf
    letI := finiteDimensional_functionFieldPullback f
    letI := functionFieldPullback_etale (f := f) s
    ∀ {A : Finset ι → Subalgebra k X.functionField} {B : Finset κ → Subalgebra k Y.functionField}
      (hX : IsAffCover s U A) (hY : IsAffCover t V B)
      {I : Finset ι} {J : Finset κ} (hi : I.Nonempty) (hj : J.Nonempty)
      (e : f ⁻¹ᵁ coverInter ⊤ U I = coverInter ⊤ V J) (p : ℕ)
      (x : Γ(relativeForms t p, f ⁻¹ᵁ coverInter ⊤ U I)),
      traceDR k X.functionField Y.functionField
        (hY.sectionRationalForms hj p ((relativeForms t p).presheaf.map (eqToHom e.symm).op x)) =
        (hX.sectionRationalForms hi p ((relativeFormsTrace hf p).app (coverInter ⊤ U I) x) :
          DR k X.functionField) := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := f.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower hf
  letI := finiteDimensional_functionFieldPullback f
  letI := functionFieldPullback_etale (f := f) s
  intro A B hX hY I J hi hj e p x
  let W := coverInter ⊤ U I
  let Q := coverInter ⊤ V J
  let a : Q ⟶ f ⁻¹ᵁ W := eqToHom e.symm
  have hW : IsAffineOpen W := by simpa only [W, coverInter, top_inf_eq] using hX.affine I hi
  have hηX : genericPoint X ∈ W := ⟨trivial, hX.ne I⟩
  have hηY : genericPoint Y ∈ Q := ⟨trivial, hY.ne J⟩
  have hη' : genericPoint Y ∈ f ⁻¹ᵁ W := leOfHom a hηY
  letI : Nonempty W := ⟨⟨genericPoint X, hηX⟩⟩
  letI : Nonempty (f ⁻¹ᵁ W) := ⟨⟨genericPoint Y, hη'⟩⟩
  obtain ⟨ω, hω⟩ := (affineFormsSections t p (hW.preimage f)).surjective x
  change formsOnToSections t p (f ⁻¹ᵁ W) ω = x at hω
  have hXA : genericSectionAlg hX.alg hηX = sectionToFunctionField s W := AlgHom.ext fun _ => rfl
  have hYB : (genericSectionAlg hY.alg hηY).comp (sectionRes t a) =
      sectionToFunctionField t (f ⁻¹ᵁ W) := by
    exact (genericSectionAlg_res hY.alg a hη' hηY).trans (AlgHom.ext fun _ => rfl)
  rw [← hω, relativeFormsTrace_app hf p hW, formsOnToSections_res,
    hY.sectionRationalForms_formsOn, hX.sectionRationalForms_formsOn,
    ← ExteriorDifferentials.map_comp, hYB, hXA]
  exact affineFormTrace_functionField hf hW hηX p ω

/-- Finite étale trace carries regular rational forms on the inverse
image of an affine intersection to regular forms on that intersection. -/
theorem IsAffCover.traceDR_mem_regularForms (hf : f ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := f.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower hf
    letI := finiteDimensional_functionFieldPullback f
    letI := functionFieldPullback_etale (f := f) s
    ∀ {A : Finset ι → Subalgebra k X.functionField} {B : Finset κ → Subalgebra k Y.functionField}
      (hX : IsAffCover s U A) (hY : IsAffCover t V B)
      {I : Finset ι} {J : Finset κ} (hi : I.Nonempty) (hj : J.Nonempty)
      (e : f ⁻¹ᵁ coverInter ⊤ U I = coverInter ⊤ V J) (p : ℕ),
      omB k Y.functionField (B J) p ≤
        (omB k X.functionField (A I) p).comap (traceDR k X.functionField Y.functionField) := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := f.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower hf
  letI := finiteDimensional_functionFieldPullback f
  letI := functionFieldPullback_etale (f := f) s
  intro A B hX hY I J hi hj e p ω hω
  obtain ⟨z, hz⟩ := (hY.sectionRationalForms hj p).surjective ⟨ω, hω⟩
  let G := (SheafOfModules.toSheaf Y.ringCatSheaf).obj (relativeForms t p)
  let j := G.1.map (eqToHom e.symm).op
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso j).surjective z
  have heq : ((hY.sectionRationalForms hj p) (j x) : DR k Y.functionField) = ω :=
    congrArg Subtype.val ((congrArg (hY.sectionRationalForms hj p) hx).trans hz)
  have htr := IsAffCover.sectionRationalForms_trace hf hX hY hi hj e p x
  change traceDR k X.functionField Y.functionField ω ∈ omB k X.functionField (A I) p
  rw [(congrArg (traceDR k X.functionField Y.functionField) heq.symm).trans htr]
  exact (hX.sectionRationalForms hi p ((relativeFormsTrace hf p).app (coverInter ⊤ U I) x)).2

end GlobalTheory.PD
