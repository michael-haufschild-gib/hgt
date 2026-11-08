import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockCoordinates
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeTruncatedBlocks

/-!
# Realization of arithmetic blocks in the original chain complex

Each core tag represents its transformed exterior vector with its exact
prime-product birth condition. The middle pair realizes the two small-prime
vectors; the row and top maps become the original cutoff differential.
Consequently each upper block maps to the original adjacent short complex,
naturally in arithmetic height.
-/

noncomputable section
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The prime-product height of a core omitting two and three. -/
def twoPrimeCoreHeight (c : TwoPrimeCoreFace) : ℕ := ∏ p ∈ c.val, p.val

/-- Birth heights of the four tagged faces of a core. -/
def twoPrimeTaggedBirth (c : TwoPrimeCoreFace) : TwoPrimeFaceTag → ℕ
  | .base => twoPrimeCoreHeight c
  | .two => 2*twoPrimeCoreHeight c
  | .three => 3*twoPrimeCoreHeight c
  | .both => 6*twoPrimeCoreHeight c

theorem twoPrimeTaggedBirth_eq (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) :
    twoPrimeTaggedBirth c t = t.height*twoPrimeCoreHeight c := by
  cases t <;> simp only [twoPrimeTaggedBirth,TwoPrimeFaceTag.height,Nat.one_mul]

/-- A tagged transformed vector lies in its exact prime-product cutoff. -/
theorem twoPrimeBlockVector_mem_cutoff (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag)
    (N : ℕ) (h : twoPrimeTaggedBirth c t ≤ N) :
    twoPrimeBlockVector R c t ∈ primeChainCutoff R (c.val.card+t.degree) N := by
  rw [primeChainCutoff_eq_span_twoPrimeBasis]
  apply Submodule.subset_span
  refine ⟨⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩,?_,rfl⟩
  change (∏ p ∈ twoPrimeTaggedFace c t, p.val) ≤ N
  rw [twoPrimeTaggedFace_product]
  rw [twoPrimeTaggedBirth_eq] at h
  exact h

/-- A coefficient satisfying its birth condition realizes an actual cutoff chain. -/
theorem twoPrimeScaledVector_mem_cutoff (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag)
    (N : ℕ) (a : R) (ha : N < twoPrimeTaggedBirth c t → a=0) :
    a • twoPrimeBlockVector R c t ∈ primeChainCutoff R (c.val.card+t.degree) N := by
  by_cases h : twoPrimeTaggedBirth c t ≤ N
  · exact Submodule.smul_mem _ a (twoPrimeBlockVector_mem_cutoff R c t N h)
  · rw [ha (by omega),zero_smul]
    exact Submodule.zero_mem _

/-- Realize a born scalar as its actual transformed face. -/
def twoPrimeBlockScalarRealization (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) (N : ℕ) :
    twoPrimeBlockScalar R (twoPrimeTaggedBirth c t) N →ₗ[R]
      primeChainCutoff R (c.val.card+t.degree) N where
  toFun a := ⟨a.val • twoPrimeBlockVector R c t,
    twoPrimeScaledVector_mem_cutoff R c t N a.val a.property⟩
  map_add' a b := by apply Subtype.ext; exact add_smul a.val b.val (twoPrimeBlockVector R c t)
  map_smul' a b := by apply Subtype.ext; exact mul_smul a b.val (twoPrimeBlockVector R c t)

/-- Homogeneous bottom vector of a core. -/
def twoPrimeBaseVector (c : TwoPrimeCoreFace) : PrimeChainSpace R c.val.card :=
  twoPrimeBlockVector R c .base

/-- Homogeneous two-tag vector of a core. -/
def twoPrimeTwoVector (c : TwoPrimeCoreFace) : PrimeChainSpace R (c.val.card+1) :=
  twoPrimeBlockVector R c .two

/-- Homogeneous three-tag vector of a core. -/
def twoPrimeThreeVector (c : TwoPrimeCoreFace) : PrimeChainSpace R (c.val.card+1) :=
  twoPrimeBlockVector R c .three

/-- Homogeneous top vector of a core. -/
def twoPrimeTopVector (c : TwoPrimeCoreFace) : PrimeChainSpace R (c.val.card+2) :=
  twoPrimeBlockVector R c .both

/-- The middle pair realizes the two small-prime transformed faces. -/
def twoPrimeBlockMiddleRealization (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeBlockMiddle R (twoPrimeCoreHeight c) N →ₗ[R] primeChainCutoff R (c.val.card+1) N where
  toFun x := ⟨Add.add (α := PrimeChainSpace R (c.val.card+1))
      (x.val.1 • twoPrimeTwoVector R c) (x.val.2 • twoPrimeThreeVector R c),
    Submodule.add_mem _
      (twoPrimeScaledVector_mem_cutoff R c .two N x.val.1 x.property.1)
      (twoPrimeScaledVector_mem_cutoff R c .three N x.val.2 x.property.2)⟩
  map_add' x y := by
    apply Subtype.ext
    change (x.val.1+y.val.1) • twoPrimeTwoVector R c +
      (x.val.2+y.val.2) • twoPrimeThreeVector R c =
      (x.val.1 • twoPrimeTwoVector R c + x.val.2 • twoPrimeThreeVector R c) +
      (y.val.1 • twoPrimeTwoVector R c + y.val.2 • twoPrimeThreeVector R c)
    rw [add_smul,add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    change (a*x.val.1) • twoPrimeTwoVector R c +
      (a*x.val.2) • twoPrimeThreeVector R c = _
    rw [mul_smul,mul_smul,← smul_add]
    rfl

private theorem row_linear_combination {V W : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (d : V →ₗ[R] W) (v₂ v₃ : V) (w : W)
    (h₂ : d v₂ = (2 : R) • w) (h₃ : d v₃ = (3 : R) • w) (a b : R) :
    d (a • v₂ + b • v₃) = (2*a+3*b) • w := by
  rw [map_add,map_smul,map_smul,h₂,h₃,smul_smul,smul_smul,add_smul,
    mul_comm a 2,mul_comm b 3]

private theorem top_linear_combination {V W : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (d : V →ₗ[R] W) (v : V) (w₂ w₃ : W)
    (ht : d v = (2 : R) • w₃ - (3 : R) • w₂) (a : R) :
    d (a • v) = (-3*a) • w₂ + (2*a) • w₃ := by
  rw [map_smul,ht,smul_sub,smul_smul,smul_smul,
    neg_mul,neg_smul,mul_comm a 2,mul_comm a 3,sub_eq_add_neg,add_comm]

/-- The realized middle boundary is the exact row `(2,3)` in actual cutoff chains. -/
theorem twoPrimeBlockMiddleRealization_boundary (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffDifferential R (primeValueFunctional R) c.val.card N).comp
      (twoPrimeBlockMiddleRealization R c N) =
    (twoPrimeBlockScalarRealization R c .base N).comp
      (twoPrimeBlockCutoffRow R (twoPrimeCoreHeight c) N) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change primeValueBoundary R c.val.card
      (Add.add (α := PrimeChainSpace R (c.val.card+1))
        (x.val.1 • twoPrimeTwoVector R c) (x.val.2 • twoPrimeThreeVector R c)) =
    (2*x.val.1+3*x.val.2) • twoPrimeBaseVector R c
  exact row_linear_combination R (primeValueBoundary R c.val.card)
    (twoPrimeTwoVector R c) (twoPrimeThreeVector R c) (twoPrimeBaseVector R c)
    (twoPrimeBlockVector_boundary_two R c) (twoPrimeBlockVector_boundary_three R c) x.val.1 x.val.2

/-- The realized top boundary is the exact column `(-3,2)` in actual cutoff chains. -/
theorem twoPrimeBlockTopRealization_boundary (c : TwoPrimeCoreFace) (N : ℕ) :
    (primeCutoffDifferential R (primeValueFunctional R) (c.val.card+1) N).comp
      (twoPrimeBlockScalarRealization R c .both N) =
    (twoPrimeBlockMiddleRealization R c N).comp
      (twoPrimeBlockCutoffTop R (twoPrimeCoreHeight c) N) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change primeValueBoundary R (c.val.card+1) (x.val • twoPrimeTopVector R c) =
    Add.add (α := PrimeChainSpace R (c.val.card+1))
      ((-3*x.val) • twoPrimeTwoVector R c) ((2*x.val) • twoPrimeThreeVector R c)
  exact top_linear_combination R (primeValueBoundary R (c.val.card+1))
    (twoPrimeTopVector R c) (twoPrimeTwoVector R c) (twoPrimeThreeVector R c)
    (twoPrimeBlockVector_boundary_both R c) x.val

/-- Each upper arithmetic block maps to the original adjacent chain complex. -/
def twoPrimeUpperBlockRealization (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeUpperBlock R (twoPrimeCoreHeight c) N ⟶
      (primeCutoffComplex R (primeValueFunctional R) N).sc' (c.val.card+2) (c.val.card+1) c.val.card where
  τ₁ := ModuleCat.ofHom (twoPrimeBlockScalarRealization R c .both N)
  τ₂ := ModuleCat.ofHom (twoPrimeBlockMiddleRealization R c N)
  τ₃ := ModuleCat.ofHom (twoPrimeBlockScalarRealization R c .base N)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change ((primeCutoffComplex R (primeValueFunctional R) N).d
      ((c.val.card+1)+1) (c.val.card+1)).hom.comp (twoPrimeBlockScalarRealization R c .both N) = _
    simp only [primeCutoffComplex,ChainComplex.of_d]
    exact twoPrimeBlockTopRealization_boundary R c N
  comm₂₃ := by
    apply ModuleCat.hom_ext
    change ((primeCutoffComplex R (primeValueFunctional R) N).d
      (c.val.card+1) c.val.card).hom.comp (twoPrimeBlockMiddleRealization R c N) = _
    simp only [primeCutoffComplex,ChainComplex.of_d]
    exact twoPrimeBlockMiddleRealization_boundary R c N

#print axioms twoPrimeBlockVector_mem_cutoff
#print axioms twoPrimeBlockMiddleRealization_boundary
#print axioms twoPrimeBlockTopRealization_boundary
#print axioms twoPrimeUpperBlockRealization
/-- Raising height commutes with realization of every scalar tag. -/
theorem twoPrimeBlockScalarRealization_natural (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag)
    {N M : ℕ} (h : N ≤ M) :
    (Submodule.inclusion (primeChainCutoff_mono R (c.val.card+t.degree) h)).comp
      (twoPrimeBlockScalarRealization R c t N) =
    (twoPrimeBlockScalarRealization R c t M).comp
      (Submodule.inclusion (twoPrimeBlockScalar_mono R (twoPrimeTaggedBirth c t) h)) := by
  apply LinearMap.ext
  intro x
  rfl

/-- Raising height commutes with realization of the middle pair. -/
theorem twoPrimeBlockMiddleRealization_natural (c : TwoPrimeCoreFace) {N M : ℕ} (h : N ≤ M) :
    (Submodule.inclusion (primeChainCutoff_mono R (c.val.card+1) h)).comp
      (twoPrimeBlockMiddleRealization R c N) =
    (twoPrimeBlockMiddleRealization R c M).comp
      (Submodule.inclusion (twoPrimeBlockMiddle_mono R (twoPrimeCoreHeight c) h)) := by
  apply LinearMap.ext
  intro x
  rfl

/-- The upper block realization is natural into the original prime-valued chain persistence. -/
def twoPrimeUpperBlockRealizationNat (c : TwoPrimeCoreFace) :
    twoPrimeUpperBlockPersistence R (twoPrimeCoreHeight c) ⟶
      primeCutoffPersistence R (primeValueFunctional R) ⋙
        HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ)
          (c.val.card+2) (c.val.card+1) c.val.card where
  app N := twoPrimeUpperBlockRealization R c N
  naturality {N M} h := by ext <;> rfl

#print axioms twoPrimeBlockScalarRealization_natural
#print axioms twoPrimeBlockMiddleRealization_natural
#print axioms twoPrimeUpperBlockRealizationNat

end GaloisForLFunctions.EffectiveScalingGeometry
