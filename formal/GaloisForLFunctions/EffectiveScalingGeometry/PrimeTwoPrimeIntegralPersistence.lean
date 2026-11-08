import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedIntegralCoefficients
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeCorePersistence

/-!
# Integer coefficient extension in the arithmetic block quotients

Canonical extension on the original weighted homology becomes the integer
scalar map on both core quotients. The proof retains actual cycle extraction
and preserves each birth and boundary relation. These quotient maps commute
with every height inclusion; annihilator classes newly present over the target
ring are not asserted to come from integral classes.
-/

noncomputable section
open scoped Classical
open CategoryTheory RHTower DifferentialGeometry.Topology
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

local instance integralScalarModule (m N : ℕ) : Module ℤ (twoPrimeBlockScalar ℤ m N) :=
  (twoPrimeBlockScalar ℤ m N).module
local instance integralUpperModule (m N : ℕ) : Module ℤ (twoPrimeUpperCoefficients ℤ m N) :=
  (twoPrimeUpperCoefficients ℤ m N).module

/-- Canonical integer extension preserves the scalar birth condition. -/
def twoPrimeBlockScalarIntegralMap (m N : ℕ) :
    twoPrimeBlockScalar ℤ m N →ₗ[ℤ] twoPrimeBlockScalar R m N where
  toFun x := ⟨(x.val : R),fun h => by rw [x.property h,Int.cast_zero]⟩
  map_add' x y := Subtype.ext (Int.cast_add x.val y.val)
  map_smul' a x := by
    apply Subtype.ext
    change ((a*x.val : ℤ) : R) = a • (x.val : R)
    rw [Int.cast_mul,zsmul_eq_mul]

/-- Canonical integer extension preserves both upper cycle birth conditions. -/
def twoPrimeUpperCoefficientIntegralMap (m N : ℕ) :
    twoPrimeUpperCoefficients ℤ m N →ₗ[ℤ] twoPrimeUpperCoefficients R m N where
  toFun x := ⟨(x.val : R),⟨fun h => by rw [x.property.1 h,Int.cast_zero],fun h => by
    have he := congrArg (fun a : ℤ => (a : R)) (x.property.2 h)
    simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_zero] using he⟩⟩
  map_add' x y := Subtype.ext (Int.cast_add x.val y.val)
  map_smul' a x := by
    apply Subtype.ext
    change ((a*x.val : ℤ) : R) = a • (x.val : R)
    rw [Int.cast_mul,zsmul_eq_mul]

/-- The lower relation ideal is preserved by the canonical integer scalar map. -/
theorem twoPrimeLowerRelations_integral (m N : ℕ) (x : twoPrimeBlockScalar ℤ m N)
    (hx : x ∈ twoPrimeLowerRelations ℤ m N) :
    twoPrimeBlockScalarIntegralMap R m N x ∈ twoPrimeLowerRelations R m N := by
  change x.val ∈ twoPrimeLowerIdeal ℤ m N at hx
  change (x.val : R) ∈ twoPrimeLowerIdeal R m N
  unfold twoPrimeLowerIdeal at hx ⊢
  by_cases h3 : 3*m ≤ N
  · rw [if_pos h3]
    trivial
  · rw [if_neg h3] at hx ⊢
    by_cases h2 : 2*m ≤ N
    · rw [if_pos h2] at hx ⊢
      obtain ⟨a,ha⟩ := hx
      refine ⟨(a : R),?_⟩
      change (2 : R)*(a : R)=(x.val : R)
      have he : (2 : ℤ)*a=x.val := ha
      have hc := congrArg (fun b : ℤ => (b : R)) he
      simpa only [Int.cast_mul,Int.cast_ofNat] using hc
    · rw [if_neg h2] at hx ⊢
      change (x.val : R)=0
      change x.val=0 at hx
      rw [hx,Int.cast_zero]

/-- Upper boundary coefficients stay zero before the same top birth. -/
theorem twoPrimeUpperRelations_integral (m N : ℕ) (x : twoPrimeUpperCoefficients ℤ m N)
    (hx : x ∈ twoPrimeUpperRelations ℤ m N) :
    twoPrimeUpperCoefficientIntegralMap R m N x ∈ twoPrimeUpperRelations R m N := by
  intro h
  change (x.val : R)=0
  have hz : x.val=0 := hx h
  exact (congrArg (fun a : ℤ => (a : R)) hz).trans (Int.cast_zero)

/-- The lower quotient class of the canonically extended integer coefficient. -/
def twoPrimeLowerIntegralClassMap (m N : ℕ) :
    twoPrimeBlockScalar ℤ m N →ₗ[ℤ] TwoPrimeLowerHomology R m N :=
  ((twoPrimeLowerRelations R m N).mkQ.restrictScalars ℤ).comp
    (twoPrimeBlockScalarIntegralMap R m N)

/-- The upper quotient class of the canonically extended integer coefficient. -/
def twoPrimeUpperIntegralClassMap (m N : ℕ) :
    twoPrimeUpperCoefficients ℤ m N →ₗ[ℤ] TwoPrimeUpperHomology R m N :=
  ((twoPrimeUpperRelations R m N).mkQ.restrictScalars ℤ).comp
    (twoPrimeUpperCoefficientIntegralMap R m N)

/-- Integer extension on lower homology is scalar extension modulo the same relations. -/
def twoPrimeLowerIntegralHomologyMap (m N : ℕ) :
    TwoPrimeLowerHomology ℤ m N →ₗ[ℤ] TwoPrimeLowerHomology R m N :=
  (twoPrimeLowerRelations ℤ m N).liftQ (twoPrimeLowerIntegralClassMap R m N) (by
    intro x hx
    change Submodule.Quotient.mk (twoPrimeBlockScalarIntegralMap R m N x)=0
    rw [Submodule.Quotient.mk_eq_zero]
    exact twoPrimeLowerRelations_integral R m N x hx)

/-- Integer extension on upper homology is scalar extension modulo the same relations. -/
def twoPrimeUpperIntegralHomologyMap (m N : ℕ) :
    TwoPrimeUpperHomology ℤ m N →ₗ[ℤ] TwoPrimeUpperHomology R m N :=
  (twoPrimeUpperRelations ℤ m N).liftQ (twoPrimeUpperIntegralClassMap R m N) (by
    intro x hx
    change Submodule.Quotient.mk (twoPrimeUpperCoefficientIntegralMap R m N x)=0
    rw [Submodule.Quotient.mk_eq_zero]
    exact twoPrimeUpperRelations_integral R m N x hx)

/-- Original upper cycle coordinates extend by the canonical integer scalar map. -/
theorem twoPrimeUpperCycleCoefficient_integral (c : TwoPrimeCoreFace) (N : ℕ)
    (z : ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc (c.val.card+1)).g.hom.ker) :
    twoPrimeUpperCycleEquiv R (twoPrimeCoreHeight c) N
      (moduleCycleMap (twoPrimeUpperOriginalRetraction R c N)
        (primeWeightedIntegralCycleMap R (c.val.card+1) N z)) =
      twoPrimeUpperCoefficientIntegralMap R (twoPrimeCoreHeight c) N
        (twoPrimeUpperCycleEquiv ℤ (twoPrimeCoreHeight c) N
          (moduleCycleMap (twoPrimeUpperOriginalRetraction ℤ c N) z)) := by
  apply Subtype.ext
  change (twoPrimeBlockScalarExtraction R c .two N
      (primeIntegralCutoffMap R (c.val.card+1) N z.val)).val +
    (twoPrimeBlockScalarExtraction R c .three N
      (primeIntegralCutoffMap R (c.val.card+1) N z.val)).val =
    (((twoPrimeBlockScalarExtraction ℤ c .two N z.val).val +
      (twoPrimeBlockScalarExtraction ℤ c .three N z.val).val : ℤ) : R)
  exact (congrArg₂ (fun a b : R => a+b)
    (primeIntegralCutoffMap_twoPrimeScalar R c .two N z.val)
    (primeIntegralCutoffMap_twoPrimeScalar R c .three N z.val)).trans (Int.cast_add _ _).symm

/-- The original upper homology coefficient map is exactly the quotient scalar map. -/
theorem twoPrimeUpperHomologyCoefficient_integral (c : TwoPrimeCoreFace) (N : ℕ)
    (x : (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).homology (c.val.card+1)) :
    twoPrimeUpperHomologyEquiv R (twoPrimeCoreHeight c) N
      (twoPrimeUpperHomologyExtraction R c N
        (primeWeightedIntegralHomologyMap R (c.val.card+1) N x)) =
      twoPrimeUpperIntegralHomologyMap R (twoPrimeCoreHeight c) N
        (twoPrimeUpperHomologyEquiv ℤ (twoPrimeCoreHeight c) N
          (twoPrimeUpperHomologyExtraction ℤ c N x)) := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc (c.val.card+1)) x
  rw [primeWeightedIntegralHomologyMap_class]
  change twoPrimeUpperHomologyEquiv R (twoPrimeCoreHeight c) N
    (ShortComplex.homologyMap (twoPrimeUpperOriginalRetraction R c N) _) =
      twoPrimeUpperIntegralHomologyMap R (twoPrimeCoreHeight c) N
        (twoPrimeUpperHomologyEquiv ℤ (twoPrimeCoreHeight c) N
          (ShortComplex.homologyMap (twoPrimeUpperOriginalRetraction ℤ c N) _))
  rw [moduleHomologyClass_map,moduleHomologyClass_map,
    twoPrimeUpperHomologyEquiv_class,twoPrimeUpperHomologyEquiv_class]
  change Submodule.Quotient.mk
    (twoPrimeUpperCycleEquiv R (twoPrimeCoreHeight c) N
      (moduleCycleMap (twoPrimeUpperOriginalRetraction R c N)
        (primeWeightedIntegralCycleMap R (c.val.card+1) N z))) =
      Submodule.Quotient.mk
        (twoPrimeUpperCoefficientIntegralMap R (twoPrimeCoreHeight c) N
          (twoPrimeUpperCycleEquiv ℤ (twoPrimeCoreHeight c) N
            (moduleCycleMap (twoPrimeUpperOriginalRetraction ℤ c N) z)))
  exact congrArg Submodule.Quotient.mk (twoPrimeUpperCycleCoefficient_integral R c N z)

/-- The original bottom homology coefficient map is exactly the quotient scalar map. -/
theorem twoPrimeLowerHomologyCoefficient_integral (c : TwoPrimeCoreFace) (N : ℕ)
    (x : (primeCutoffComplex ℤ (primeValueFunctional ℤ) N).homology c.val.card) :
    twoPrimeLowerHomologyEquiv R (twoPrimeCoreHeight c) N
      (twoPrimeLowerHomologyExtraction R c N
        (primeWeightedIntegralHomologyMap R c.val.card N x)) =
      twoPrimeLowerIntegralHomologyMap R (twoPrimeCoreHeight c) N
        (twoPrimeLowerHomologyEquiv ℤ (twoPrimeCoreHeight c) N
          (twoPrimeLowerHomologyExtraction ℤ c N x)) := by
  obtain ⟨z,rfl⟩ := moduleHomologyClass_surjective
    ((primeCutoffComplex ℤ (primeValueFunctional ℤ) N).sc c.val.card) x
  rw [primeWeightedIntegralHomologyMap_class]
  change twoPrimeLowerHomologyEquiv R (twoPrimeCoreHeight c) N
    (ShortComplex.homologyMap (twoPrimeLowerOriginalExtraction R c N) _) =
      twoPrimeLowerIntegralHomologyMap R (twoPrimeCoreHeight c) N
        (twoPrimeLowerHomologyEquiv ℤ (twoPrimeCoreHeight c) N
          (ShortComplex.homologyMap (twoPrimeLowerOriginalExtraction ℤ c N) _))
  rw [moduleHomologyClass_map,moduleHomologyClass_map,
    twoPrimeLowerHomologyEquiv_class,twoPrimeLowerHomologyEquiv_class]
  change Submodule.Quotient.mk
    (twoPrimeBlockScalarExtraction R c .base N (primeIntegralCutoffMap R c.val.card N z.val)) =
      Submodule.Quotient.mk
        (twoPrimeBlockScalarIntegralMap R (twoPrimeCoreHeight c) N
          (twoPrimeBlockScalarExtraction ℤ c .base N z.val))
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact primeIntegralCutoffMap_twoPrimeScalar R c .base N z.val

/-- The lower quotient scalar map commutes with every arithmetic height inclusion. -/
theorem twoPrimeLowerIntegralHomologyMap_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : TwoPrimeLowerHomology ℤ m N) :
    twoPrimeLowerHomologyMap R m h (twoPrimeLowerIntegralHomologyMap R m N x) =
      twoPrimeLowerIntegralHomologyMap R m M (twoPrimeLowerHomologyMap ℤ m h x) := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations ℤ m N) x
  rfl

#print axioms twoPrimeLowerIntegralHomologyMap_natural
/-- The upper quotient scalar map commutes with every arithmetic height inclusion. -/
theorem twoPrimeUpperIntegralHomologyMap_natural (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : TwoPrimeUpperHomology ℤ m N) :
    twoPrimeUpperHomologyMap R m h (twoPrimeUpperIntegralHomologyMap R m N x) =
      twoPrimeUpperIntegralHomologyMap R m M (twoPrimeUpperHomologyMap ℤ m h x) := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations ℤ m N) x
  rfl

#print axioms twoPrimeUpperIntegralHomologyMap_natural
#print axioms twoPrimeLowerIntegralHomologyMap
#print axioms twoPrimeUpperIntegralHomologyMap
#print axioms twoPrimeUpperCycleCoefficient_integral
#print axioms twoPrimeUpperHomologyCoefficient_integral
#print axioms twoPrimeLowerHomologyCoefficient_integral
end GaloisForLFunctions.EffectiveScalingGeometry
