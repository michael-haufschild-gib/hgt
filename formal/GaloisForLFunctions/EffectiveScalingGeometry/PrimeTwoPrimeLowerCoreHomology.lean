import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeCoreDegrees
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeUpperCoreHomology

/-! The actual bottom core homology is its truncated lower scalar quotient.
Bottom representatives are cycles in every augmented degree, including the
empty core. Original cycle-class maps identify realization and extraction
as inverse homology maps on the core range. -/

noncomputable section
open scoped Classical
open CategoryTheory RHTower DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Every realized bottom coefficient is an actual cycle, including the empty core. -/
theorem twoPrimeBaseRealization_closed (c : TwoPrimeCoreFace) (N j : ℕ)
    (a : twoPrimeBlockScalar R (twoPrimeCoreHeight c) N) :
    (primeCutoffComplex R (primeValueFunctional R) N).d c.val.card j
      (twoPrimeBlockScalarRealization R c .base N a) = 0 := by
  by_cases hj : j < c.val.card
  · have hf : twoPrimeCoreCutoffProjection R c.val.card N c
        (twoPrimeBlockScalarRealization R c .base N a) =
        twoPrimeBlockScalarRealization R c .base N a := by
      exact (LinearMap.congr_fun (twoPrimeBase_realization_extraction R c N)
        (twoPrimeBlockScalarRealization R c .base N a)).symm.trans
        (congrArg (twoPrimeBlockScalarRealization R c .base N)
          (twoPrimeBlockScalarExtraction_realization R c .base N a))
    have he := congrArg (fun f :
        (primeCutoffComplex R (primeValueFunctional R) N).X c.val.card ⟶
        (primeCutoffComplex R (primeValueFunctional R) N).X j =>
          f (twoPrimeBlockScalarRealization R c .base N a))
      ((twoPrimeCoreChainProjection R c N).comm c.val.card j)
    change (primeCutoffComplex R (primeValueFunctional R) N).d c.val.card j
      (twoPrimeCoreCutoffProjection R c.val.card N c (twoPrimeBlockScalarRealization R c .base N a)) =
      twoPrimeCoreCutoffProjection R j N c
        ((primeCutoffComplex R (primeValueFunctional R) N).d c.val.card j
          (twoPrimeBlockScalarRealization R c .base N a)) at he
    rw [hf,twoPrimeCoreCutoffProjection_below R j N c hj] at he
    exact he
  · have hd : (primeCutoffComplex R (primeValueFunctional R) N).d c.val.card j = 0 := by
      apply HomologicalComplex.shape
      change ¬j+1=c.val.card
      omega
    rw [hd]
    rfl

/-- Realize a lower block in the original adjacent complex. -/
def twoPrimeLowerBlockRealization (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeLowerBlock R (twoPrimeCoreHeight c) N ⟶
      (primeCutoffComplex R (primeValueFunctional R) N).sc'
        (c.val.card+1) c.val.card (c.val.card-1) where
  τ₁ := ModuleCat.ofHom (twoPrimeBlockMiddleRealization R c N)
  τ₂ := ModuleCat.ofHom (twoPrimeBlockScalarRealization R c .base N)
  τ₃ := 0
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change ((primeCutoffComplex R (primeValueFunctional R) N).d (c.val.card+1) c.val.card).hom.comp
      (twoPrimeBlockMiddleRealization R c N) = _
    simp only [primeCutoffComplex,ChainComplex.of_d]
    exact twoPrimeBlockMiddleRealization_boundary R c N
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact twoPrimeBaseRealization_closed R c N (c.val.card-1) a

/-- Extract the lower block from the original adjacent complex. -/
def twoPrimeLowerBlockExtraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffComplex R (primeValueFunctional R) N).sc'
      (c.val.card+1) c.val.card (c.val.card-1) ⟶
    twoPrimeLowerBlock R (twoPrimeCoreHeight c) N where
  τ₁ := ModuleCat.ofHom (twoPrimeBlockMiddleExtraction R c N)
  τ₂ := ModuleCat.ofHom (twoPrimeBlockScalarExtraction R c .base N)
  τ₃ := 0
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change (twoPrimeBlockCutoffRow R (twoPrimeCoreHeight c) N).comp
      (twoPrimeBlockMiddleExtraction R c N) =
      (twoPrimeBlockScalarExtraction R c .base N).comp
        ((primeCutoffComplex R (primeValueFunctional R) N).d (c.val.card+1) c.val.card).hom
    simp only [primeCutoffComplex,ChainComplex.of_d]
    exact twoPrimeBlockMiddleExtraction_boundary R c N
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def twoPrimeLowerOriginalRealization (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeLowerBlock R (twoPrimeCoreHeight c) N ⟶
      (primeCutoffComplex R (primeValueFunctional R) N).sc c.val.card :=
  twoPrimeLowerBlockRealization R c N ≫
    ((primeCutoffComplex R (primeValueFunctional R) N).isoSc'
      (c.val.card+1) c.val.card (c.val.card-1) (by simp)
      (by cases hc : c.val.card <;> simp)).inv

def twoPrimeLowerOriginalExtraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffComplex R (primeValueFunctional R) N).sc c.val.card ⟶
      twoPrimeLowerBlock R (twoPrimeCoreHeight c) N :=
  ((primeCutoffComplex R (primeValueFunctional R) N).isoSc'
    (c.val.card+1) c.val.card (c.val.card-1) (by simp)
    (by cases hc : c.val.card <;> simp)).hom ≫
      twoPrimeLowerBlockExtraction R c N

def twoPrimeLowerHomologyRealization (c : TwoPrimeCoreFace) (N : ℕ) :
    (twoPrimeLowerBlock R (twoPrimeCoreHeight c) N).homology →ₗ[R]
      (primeCutoffComplex R (primeValueFunctional R) N).homology c.val.card :=
  (ShortComplex.homologyMap (twoPrimeLowerOriginalRealization R c N)).hom

def twoPrimeLowerHomologyExtraction (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffComplex R (primeValueFunctional R) N).homology c.val.card →ₗ[R]
      (twoPrimeLowerBlock R (twoPrimeCoreHeight c) N).homology :=
  (ShortComplex.homologyMap (twoPrimeLowerOriginalExtraction R c N)).hom

theorem twoPrimeLowerHomology_section (c : TwoPrimeCoreFace) (N : ℕ)
    (x : (twoPrimeLowerBlock R (twoPrimeCoreHeight c) N).homology) :
    twoPrimeLowerHomologyExtraction R c N (twoPrimeLowerHomologyRealization R c N x) = x := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    (twoPrimeLowerBlock R (twoPrimeCoreHeight c) N) x
  change ShortComplex.homologyMap (twoPrimeLowerOriginalExtraction R c N)
    (ShortComplex.homologyMap (twoPrimeLowerOriginalRealization R c N) _) = _
  rw [moduleHomologyClass_map,moduleHomologyClass_map]
  apply congrArg (moduleHomologyClass (twoPrimeLowerBlock R (twoPrimeCoreHeight c) N))
  apply Subtype.ext
  exact twoPrimeBlockScalarExtraction_realization R c .base N z.val

theorem twoPrimeLowerHomology_projection (c : TwoPrimeCoreFace) (N : ℕ)
    (x : (primeCutoffComplex R (primeValueFunctional R) N).homology c.val.card) :
    twoPrimeLowerHomologyRealization R c N (twoPrimeLowerHomologyExtraction R c N x) =
      twoPrimeCoreHomologyProjection R c.val.card N c x := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex R (primeValueFunctional R) N).sc c.val.card) x
  change ShortComplex.homologyMap (twoPrimeLowerOriginalRealization R c N)
    (ShortComplex.homologyMap (twoPrimeLowerOriginalExtraction R c N) _) = _
  rw [moduleHomologyClass_map,moduleHomologyClass_map,twoPrimeCoreHomologyProjection_class]
  apply congrArg (moduleHomologyClass
    ((primeCutoffComplex R (primeValueFunctional R) N).sc c.val.card))
  apply Subtype.ext
  exact LinearMap.congr_fun (twoPrimeBase_realization_extraction R c N) z.val

/-- Actual bottom core homology is the lower truncated-block homology. -/
def twoPrimeLowerCoreHomologyEquiv (c : TwoPrimeCoreFace) (N : ℕ) :
    TwoPrimeHomologyCore R c.val.card N c ≃ₗ[R]
      (twoPrimeLowerBlock R (twoPrimeCoreHeight c) N).homology where
  toFun x := twoPrimeLowerHomologyExtraction R c N x.val
  invFun y := ⟨twoPrimeLowerHomologyRealization R c N y,by
    refine ⟨twoPrimeLowerHomologyRealization R c N y,?_⟩
    exact (twoPrimeLowerHomology_projection R c N
      (twoPrimeLowerHomologyRealization R c N y)).symm.trans
      (congrArg (twoPrimeLowerHomologyRealization R c N) (twoPrimeLowerHomology_section R c N y))⟩
  left_inv x := by
    apply Subtype.ext
    exact (twoPrimeLowerHomology_projection R c N x.val).trans
      ((twoPrimeCoreHomologyProjection_range R c.val.card N c c x).trans (if_pos rfl))
  right_inv y := twoPrimeLowerHomology_section R c N y
  map_add' x y := (twoPrimeLowerHomologyExtraction R c N).map_add x.val y.val
  map_smul' a x := (twoPrimeLowerHomologyExtraction R c N).map_smul a x.val

/-- Exact scalar quotient coordinates for the actual bottom core contribution. -/
def twoPrimeLowerCoreCoefficientEquiv (c : TwoPrimeCoreFace) (N : ℕ) :
    TwoPrimeHomologyCore R c.val.card N c ≃ₗ[R]
      TwoPrimeLowerHomology R (twoPrimeCoreHeight c) N :=
  (twoPrimeLowerCoreHomologyEquiv R c N).trans
    (twoPrimeLowerHomologyEquiv R (twoPrimeCoreHeight c) N)

#print axioms twoPrimeBaseRealization_closed
#print axioms twoPrimeLowerHomology_section
#print axioms twoPrimeLowerHomology_projection
#print axioms twoPrimeLowerCoreCoefficientEquiv
end GaloisForLFunctions.EffectiveScalingGeometry
