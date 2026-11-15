import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentSystem

/-!
# Exact affine linear consequences of arbitrary moment equations

An affine linear polynomial belongs to a consistent moment ideal precisely
when its coefficient vector lies in the row space and its constant agrees
with the prescribed level. For an arbitrary equation family, membership is
equivalent to either inconsistency or a finite linear combination producing
both the requested row and constant.

The proof translates to homogeneous coordinates and separates the linear
part from the constant by evaluation at zero and the coordinate unit points.
It works over every field, including finite fields, and for infinite families
of equations. In particular, a neutral coordinate vanishes exactly when the
equations force that coordinate to zero.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Evaluation at a coordinate unit point recovers the corresponding basis coefficient. -/
private theorem eval_basisLinearForm_single {V κ : Type*} [AddCommGroup V] [Module K V]
    [Fintype κ] (b : Basis κ K V) (v : V) (j : κ) :
    eval (Pi.single j 1) (b.constr K X v) = b.repr v j := by
  classical
  rw [Basis.constr_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]
  simp [smul_eq_C_mul, Pi.single_apply]

/-- A homogeneous linear form vanishes at the origin. -/
private theorem eval_basisLinearForm_zero {V κ : Type*} [AddCommGroup V] [Module K V]
    [Fintype κ] (b : Basis κ K V) (v : V) :
    eval (0 : κ → K) (b.constr K X v) = 0 := by
  classical
  rw [Basis.constr_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]
  simp [smul_eq_C_mul]

/-- The linear and constant parts of an affine polynomial vanish independently. -/
theorem basisLinearForm_add_C_eq_zero_iff {V κ : Type*} [AddCommGroup V] [Module K V]
    [Fintype κ] (b : Basis κ K V) (v : V) (t : K) :
    b.constr K X v + C t = 0 ↔ v = 0 ∧ t = 0 := by
  classical
  constructor
  · intro h
    have ht : t = 0 := by
      have he := congrArg (eval (0 : κ → K)) h
      simpa only [map_add, eval_basisLinearForm_zero, eval_C, map_zero, zero_add] using he
    refine ⟨?_, ht⟩
    apply b.repr.injective
    ext j
    have he := congrArg (eval (Pi.single j 1)) h
    simpa only [map_add, eval_basisLinearForm_single, eval_C, ht, add_zero,
      map_zero, Finsupp.zero_apply] using he
  · rintro ⟨rfl, rfl⟩
    simp

/-- Polynomial coordinates detect the exact affine moment ideal. -/
theorem affineMomentCoordinateMap_eq_zero_iff (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K)
    (f : MvPolynomial ι K) :
    affineMomentCoordinateMap K L ℓ f = 0 ↔ f ∈ affineMomentIdeal K L ℓ := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    apply (affineMomentPolynomialEquiv K L ℓ).injective
    rwa [map_zero, affineMomentCoordinateMap_mk]
  · intro h
    have he := congrArg (affineMomentPolynomialEquiv K L ℓ) h
    simpa only [affineMomentCoordinateMap_mk, map_zero] using he

/-- Translation separates an affine equation into a quotient linear form and its residual constant. -/
theorem affineMomentCoordinateMap_linearForm_sub_C (L : Submodule K (ι → K))
    (ℓ : L →ₗ[K] K) (c : ι → K) (t : K) :
    affineMomentCoordinateMap K L ℓ (momentLinearForm K c - C t) =
      (Module.finBasis K ((ι → K) ⧸ L)).constr K X (L.mkQ c) +
        C (eval (momentLevelPoint K L ℓ) (momentLinearForm K c) - t) := by
  change momentCoordinateMap K L
    (mvPolynomialBaseTranslation (momentLevelPoint K L ℓ) (momentLinearForm K c - C t)) = _
  rw [map_sub, momentTranslation_linearForm]
  have ht : mvPolynomialBaseTranslation (momentLevelPoint K L ℓ) (C t) = C t :=
    (mvPolynomialBaseTranslation (momentLevelPoint K L ℓ)).commutes t
  have hC (r : K) : momentCoordinateMap K L (C r) = C r :=
    (momentCoordinateMap K L).commutes r
  rw [ht, map_sub, map_add, momentCoordinateMap_linearForm, hC, hC, map_sub]
  abel

/-- The affine linear consequences are exactly the prescribed row space and level. -/
theorem affineMomentIdeal_mem_linear_iff (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K)
    (c : ι → K) (t : K) :
    momentLinearForm K c - C t ∈ affineMomentIdeal K L ℓ ↔
      ∃ h : c ∈ L, ℓ ⟨c, h⟩ = t := by
  rw [← affineMomentCoordinateMap_eq_zero_iff, affineMomentCoordinateMap_linearForm_sub_C,
    basisLinearForm_add_C_eq_zero_iff]
  constructor
  · rintro ⟨hc, ht⟩
    have hm : c ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hc
    refine ⟨hm, ?_⟩
    rw [momentLevelPoint_spec K L ℓ ⟨c, hm⟩] at ht
    exact sub_eq_zero.mp ht
  · rintro ⟨hc, ht⟩
    refine ⟨(Submodule.Quotient.mk_eq_zero L).mpr hc, ?_⟩
    rw [momentLevelPoint_spec K L ℓ ⟨c, hc⟩, ht, sub_self]

/-- A coordinate vanishes precisely when its unit coefficient vector is a zero-level relation. -/
theorem affineMomentIdeal_X_mem_iff (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (i : ι) :
    X i ∈ affineMomentIdeal K L ℓ ↔
      ∃ h : Pi.basisFun K ι i ∈ L, ℓ ⟨Pi.basisFun K ι i, h⟩ = 0 := by
  have he := affineMomentIdeal_mem_linear_iff K L ℓ (Pi.basisFun K ι i) 0
  simpa only [momentLinearForm, Basis.constr_basis, map_zero, sub_zero] using he

namespace AffineMomentSystem
variable {α : Type*}

/-- Every affine linear consequence has a finite equation certificate, unless the system is inconsistent. -/
theorem ideal_mem_linear_iff (a : α → ι → K) (b : α → K) (c : ι → K) (t : K) :
    momentLinearForm K c - C t ∈ ideal K a b ↔
      ¬ Compatible K a b ∨ ∃ v : α →₀ K, rowMap K a v = c ∧ valueMap K b v = t := by
  by_cases h : Compatible K a b
  · rw [ideal_eq_affineMomentIdeal K a b h, affineMomentIdeal_mem_linear_iff]
    simp only [h, not_true_eq_false, false_or]
    constructor
    · rintro ⟨hc, ht⟩
      obtain ⟨v, hv⟩ := (show ∃ v, rowMap K a v = c from hc)
      refine ⟨v, hv, ?_⟩
      have he := level_rowMap K a b h v
      have hs : (rowMap K a).rangeRestrict v = ⟨c, ⟨v, hv⟩⟩ := Subtype.ext hv
      rw [hs, ht] at he
      exact he.symm
    · rintro ⟨v, hv, ht⟩
      refine ⟨⟨v, hv⟩, ?_⟩
      have he := level_rowMap K a b h v
      have hs : (rowMap K a).rangeRestrict v = ⟨c, ⟨v, hv⟩⟩ := Subtype.ext hv
      rw [hs, ht] at he
      exact he
  · rw [ideal_eq_top_of_not_compatible K a b h]
    simp [h]

/-- Coordinate vanishing has a finite certificate with unit coefficient row and zero constant. -/
theorem ideal_X_mem_iff (a : α → ι → K) (b : α → K) (i : ι) :
    X i ∈ ideal K a b ↔ ¬ Compatible K a b ∨
      ∃ v : α →₀ K, rowMap K a v = Pi.basisFun K ι i ∧ valueMap K b v = 0 := by
  have he := ideal_mem_linear_iff K a b (Pi.basisFun K ι i) 0
  simpa only [momentLinearForm, Basis.constr_basis, map_zero, sub_zero] using he

end AffineMomentSystem
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affineMomentIdeal_mem_linear_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.ideal_mem_linear_iff
