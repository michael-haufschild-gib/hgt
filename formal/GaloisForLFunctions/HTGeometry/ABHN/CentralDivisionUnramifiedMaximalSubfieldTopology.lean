import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfield
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionRootDeterminantNorm

/-!
# Local-field topology on determinant-unramified maximal subfields

The root-determinant norm is multiplicative on the ambient division algebra and restricts exactly
to the base norm on central scalars.  This file restricts that norm to any commutative subfield and
packages the result as a complete, locally compact, nonarchimedean normed field.

Its norm valuation ring is then identified with the determinant valuation restricted to the
subfield, including exact transport of maximal ideals and residue fields.  This removes the
topological/type-theoretic gap between the residue-exhausting maximal subfield constructed earlier
and the existing Hensel/Frobenius machinery for local fields.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [DivisionRing A] [Algebra F A] [Module.Finite F A]

omit [CompleteSpace F] [IsUltrametricDist F] in
/-- The root-determinant unit ball is exactly the determinant unit ball. -/
theorem divisionAlgebraRootDeterminantNorm_le_one_iff (x : A) :
    divisionAlgebraRootDeterminantNorm (F := F) x ≤ 1 ↔
      ‖Algebra.norm F x‖ ≤ 1 := by
  have hn : (0 : ℝ) < Module.finrank F A := by
    exact_mod_cast Module.finrank_pos (R := F) (M := A)
  simpa only [divisionAlgebraRootDeterminantNorm, Real.one_rpow] using
    (Real.rpow_le_rpow_iff (norm_nonneg (Algebra.norm F x)) zero_le_one (inv_pos.mpr hn))

omit [CompleteSpace F] [IsUltrametricDist F] in
/-- The strict root-determinant unit ball is exactly the strict determinant unit ball. -/
theorem divisionAlgebraRootDeterminantNorm_lt_one_iff (x : A) :
    divisionAlgebraRootDeterminantNorm (F := F) x < 1 ↔
      ‖Algebra.norm F x‖ < 1 := by
  have hn : (0 : ℝ) < Module.finrank F A := by
    exact_mod_cast Module.finrank_pos (R := F) (M := A)
  simpa only [divisionAlgebraRootDeterminantNorm, Real.one_rpow] using
    (Real.rpow_lt_rpow_iff (norm_nonneg (Algebra.norm F x)) zero_le_one (inv_pos.mpr hn))

/-- Multiplicative normed-division-ring structure induced by the root determinant. -/
@[implicit_reducible] noncomputable def divisionAlgebraRootDeterminantNormedDivisionRing :
    NormedDivisionRing A := by
  letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
  exact NormedDivisionRing.mk
    (fun x y => by simpa [sub_eq_add_neg, add_comm] using (dist_eq_norm' x y))
    (fun x y => by
      change divisionAlgebraRootDeterminantNorm (F := F) (x * y) =
        divisionAlgebraRootDeterminantNorm (F := F) x *
          divisionAlgebraRootDeterminantNorm (F := F) y
      simp only [divisionAlgebraRootDeterminantNorm]
      rw [map_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)])

/-- Normed-field structure on a commutative subfield induced from the root determinant. -/
@[implicit_reducible] noncomputable def divisionAlgebraRestrictedRootDeterminantNormedField
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    NormedField T := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : Field T := hT.toField
  letI : NormedDivisionRing T :=
    NormedDivisionRing.induced T A T.val T.val.injective
  exact NormedField.mk
    (fun x y => NormedDivisionRing.dist_eq x y)
    (fun x y => NormedDivisionRing.norm_mul x y)

/-- The restricted root determinant is nontrivial because it extends the nontrivial base norm. -/
@[implicit_reducible] noncomputable def
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    NontriviallyNormedField T := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NormedField T :=
    divisionAlgebraRestrictedRootDeterminantNormedField (F := F) (A := A) T hT
  refine ⟨?_⟩
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm F
  refine ⟨algebraMap F T c, ?_⟩
  change 1 < divisionAlgebraRootDeterminantNorm (F := F) (algebraMap F A c)
  rw [divisionAlgebraRootDeterminantNorm, Algebra.norm_algebraMap, norm_pow,
    Real.pow_rpow_inv_natCast (norm_nonneg c)
      (Module.finrank_pos (R := F) (M := A)).ne']
  exact hc

/-- The restricted root-determinant norm makes the subfield a normed space over the base field. -/
@[implicit_reducible] noncomputable def divisionAlgebraRestrictedRootDeterminantNormedSpace
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NormedSpace F A :=
      divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    NormedSpace F T := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NormedSpace F A :=
    divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  exact {
    one_smul := fun x => by simp [one_smul]
    mul_smul := fun c d x => by simp [mul_smul]
    smul_zero := fun c => by simp
    smul_add := fun c x y => by simp [smul_add]
    add_smul := fun c d x => by simp [add_smul]
    zero_smul := fun x => by simp [zero_smul]
    norm_smul_le := fun c x => by
      change divisionAlgebraRootDeterminantNorm (F := F) (c • (x : A)) ≤
        ‖c‖ * divisionAlgebraRootDeterminantNorm (F := F) (x : A)
      rw [show divisionAlgebraRootDeterminantNorm (F := F) (c • (x : A)) =
        divisionAlgebraRootDeterminantAlgebraNorm (F := F) (A := A) (c • (x : A)) from rfl,
        map_smul_eq_mul]
      rfl }

/-- The restricted root-determinant topology is complete. -/
theorem divisionAlgebraRestrictedRootDeterminantCompleteSpace
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NormedSpace F A :=
      divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    CompleteSpace T := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NormedSpace F A :=
    divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  exact FiniteDimensional.complete F T

/-- The restricted root-determinant metric is ultrametric. -/
theorem divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    IsUltrametricDist T := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  change divisionAlgebraRootDeterminantNorm (F := F) ((x : A) + (y : A)) ≤
    max (divisionAlgebraRootDeterminantNorm (F := F) (x : A))
      (divisionAlgebraRootDeterminantNorm (F := F) (y : A))
  exact divisionAlgebraRootDeterminantNorm_isNonarchimedean (F := F) (A := A) x y

/-- Over a locally compact base, a restricted root-determinant subfield is proper and hence locally
compact. -/
theorem divisionAlgebraRestrictedRootDeterminantProperSpace [LocallyCompactSpace F]
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NormedSpace F A :=
      divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    ProperSpace T := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NormedSpace F A :=
    divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  exact FiniteDimensional.proper F T

/-- Identity-on-elements equivalence between the norm valuation ring on the restricted subfield
and the determinant valuation ring restricted from the ambient division algebra. -/
noncomputable def divisionAlgebraRestrictedNormValuationSubringEquiv
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    NormValuationSubring (F := T) ≃+*
      DivisionAlgebraDeterminantRestrictedValuationSubring (F := F) (A := A) T hT := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  refine {
    toFun := fun x => ⟨(x : T), ?_⟩
    invFun := fun x => ⟨(x : T), ?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
  · change ‖Algebra.norm F (((x : _) : T) : A)‖₊ ≤ 1
    have hroot : divisionAlgebraRootDeterminantNorm (F := F) (((x : _) : T) : A) ≤ 1 := by
      exact_mod_cast x.property
    have hdet :=
      (divisionAlgebraRootDeterminantNorm_le_one_iff
        (F := F) (A := A) (((x : _) : T) : A)).mp hroot
    exact_mod_cast hdet
  · change NormedField.valuation ((x : _) : T) ≤ 1
    rw [NormedField.valuation_apply]
    have hdet : ‖Algebra.norm F (((x : _) : T) : A)‖ ≤ 1 := by
      exact_mod_cast x.property
    have hroot :=
      (divisionAlgebraRootDeterminantNorm_le_one_iff
        (F := F) (A := A) (((x : _) : T) : A)).mpr hdet
    exact_mod_cast hroot

/-- The restricted norm-valuation equivalence sends the norm maximal ideal onto the restricted
determinant maximal ideal. -/
theorem divisionAlgebraRestrictedNormValuationSubringEquiv_map_maximalIdeal
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    IsLocalRing.maximalIdeal
        (DivisionAlgebraDeterminantRestrictedValuationSubring (F := F) (A := A) T hT) =
      Ideal.map (divisionAlgebraRestrictedNormValuationSubringEquiv
        (F := F) (A := A) T hT)
        (IsLocalRing.maximalIdeal (NormValuationSubring (F := T))) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  ext y
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hy
    let x : NormValuationSubring (F := T) :=
      (divisionAlgebraRestrictedNormValuationSubringEquiv
        (F := F) (A := A) T hT).symm y
    refine ⟨x, ?_, (divisionAlgebraRestrictedNormValuationSubringEquiv
      (F := F) (A := A) T hT).apply_symm_apply y⟩
    rw [Valuation.mem_maximalIdeal_iff T (NormedField.valuation (K := T)),
      NormedField.valuation_apply]
    apply NNReal.coe_lt_coe.mp
    have hdet : ‖Algebra.norm F (((y : _) : T) : A)‖ < 1 := by
      rw [Valuation.mem_maximalIdeal_iff T
        (divisionAlgebraDeterminantRestrictedValuation (F := F) (A := A) T hT)] at hy
      exact_mod_cast hy
    have hroot :=
      (divisionAlgebraRootDeterminantNorm_lt_one_iff
        (F := F) (A := A) (((y : _) : T) : A)).mpr hdet
    exact_mod_cast hroot
  · rintro ⟨x, hx, rfl⟩
    rw [Valuation.mem_maximalIdeal_iff T
      (divisionAlgebraDeterminantRestrictedValuation (F := F) (A := A) T hT)]
    rw [Valuation.mem_maximalIdeal_iff T (NormedField.valuation (K := T)),
      NormedField.valuation_apply] at hx
    have hroot : divisionAlgebraRootDeterminantNorm (F := F) (((x : _) : T) : A) < 1 := by
      exact_mod_cast hx
    have hdet :=
      (divisionAlgebraRootDeterminantNorm_lt_one_iff
        (F := F) (A := A) (((x : _) : T) : A)).mp hroot
    exact_mod_cast hdet

/-- The norm residue field of the restricted local field is the determinant residue field of that
subfield. -/
noncomputable def divisionAlgebraRestrictedNormValuationResidueEquiv
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    NormValuationResidue (F := T) ≃+*
      DivisionAlgebraDeterminantRestrictedResidue (F := F) (A := A) T hT := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  exact Ideal.quotientEquiv
    (IsLocalRing.maximalIdeal (NormValuationSubring (F := T)))
    (IsLocalRing.maximalIdeal
      (DivisionAlgebraDeterminantRestrictedValuationSubring (F := F) (A := A) T hT))
    (divisionAlgebraRestrictedNormValuationSubringEquiv (F := F) (A := A) T hT)
    (divisionAlgebraRestrictedNormValuationSubringEquiv_map_maximalIdeal
      (F := F) (A := A) T hT)

/-- The root-determinant norm on a commutative subfield restricts exactly to the original norm on
base-field scalars. -/
theorem divisionAlgebraRestrictedRootDeterminant_norm_algebraMap
    (T : Subalgebra F A) (hT : IsField T) (c : F) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    ‖algebraMap F T c‖ = ‖c‖ := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  change divisionAlgebraRootDeterminantNorm (F := F) (algebraMap F A c) = ‖c‖
  rw [divisionAlgebraRootDeterminantNorm, Algebra.norm_algebraMap, norm_pow,
    Real.pow_rpow_inv_natCast (norm_nonneg c)
      (Module.finrank_pos (R := F) (M := A)).ne']

/-- Integral base scalars map to integral elements of a root-determinant subfield. -/
noncomputable def normValuationSubringToDivisionAlgebraRestrictedNormValuationSubring
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    NormValuationSubring (F := F) →+* NormValuationSubring (F := T) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  exact {
    toFun := fun c => ⟨algebraMap F T (c : F), by
      change ‖algebraMap F T (c : F)‖₊ ≤ 1
      have hc : ‖algebraMap F T (c : F)‖₊ = ‖(c : F)‖₊ := by
        apply NNReal.eq
        exact divisionAlgebraRestrictedRootDeterminant_norm_algebraMap
          (F := F) (A := A) T hT (c : F)
      rw [hc]
      exact c.property⟩
    map_one' := by ext; simp
    map_mul' := by intro x y; ext; simp
    map_zero' := by ext; simp
    map_add' := by intro x y; ext; simp }

/-- The base maximal ideal is exactly the pullback of the subfield maximal ideal.  Equivalently,
the integral scalar embedding is a local homomorphism. -/
theorem divisionAlgebraRestrictedNormValuationSubring_maximalIdeal_comap
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    Ideal.comap
        (normValuationSubringToDivisionAlgebraRestrictedNormValuationSubring
          (F := F) (A := A) T hT)
        (IsLocalRing.maximalIdeal (NormValuationSubring (F := T))) =
      IsLocalRing.maximalIdeal (NormValuationSubring (F := F)) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  ext c
  rw [Ideal.mem_comap,
    Valuation.mem_maximalIdeal_iff T (NormedField.valuation (K := T)),
    Valuation.mem_maximalIdeal_iff F (NormedField.valuation (K := F)),
    NormedField.valuation_apply, NormedField.valuation_apply]
  change ‖algebraMap F T (c : F)‖₊ < 1 ↔ ‖(c : F)‖₊ < 1
  have hc : ‖algebraMap F T (c : F)‖₊ = ‖(c : F)‖₊ := by
    apply NNReal.eq
    exact divisionAlgebraRestrictedRootDeterminant_norm_algebraMap
      (F := F) (A := A) T hT (c : F)
  rw [hc]

/-- Algebra structure on integral root-determinant subfield elements over integral base scalars. -/
noncomputable instance divisionAlgebraRestrictedNormValuationSubringAlgebra
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    Algebra (NormValuationSubring (F := F)) (NormValuationSubring (F := T)) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  exact (normValuationSubringToDivisionAlgebraRestrictedNormValuationSubring
    (F := F) (A := A) T hT).toAlgebra

/-- The integral scalar embedding reflects units, hence induces the canonical extension of norm
residue fields. -/
instance divisionAlgebraRestrictedNormValuationSubringAlgebra_isLocalHom
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    IsLocalHom (algebraMap (NormValuationSubring (F := F))
      (NormValuationSubring (F := T))) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  apply ((IsLocalRing.local_hom_TFAE
    (algebraMap (NormValuationSubring (F := F))
      (NormValuationSubring (F := T)))).out 4 0 rfl rfl).mp
  change Ideal.comap
      (normValuationSubringToDivisionAlgebraRestrictedNormValuationSubring
        (F := F) (A := A) T hT)
      (IsLocalRing.maximalIdeal (NormValuationSubring (F := T))) =
    IsLocalRing.maximalIdeal (NormValuationSubring (F := F))
  exact divisionAlgebraRestrictedNormValuationSubring_maximalIdeal_comap
    (F := F) (A := A) T hT

/-- If the restricted determinant residue exhausts the full determinant residue, then the norm
residue field of the subfield is canonically equivalent to it as an algebra over the base residue
field, not merely as an abstract ring. -/
noncomputable def divisionAlgebraRestrictedNormValuationResidueAlgEquiv_of_bijective
    (T : Subalgebra F A) (hT : IsField T)
    (hbij : Function.Bijective
      (divisionAlgebraDeterminantRestrictedResidueToResidue
        (F := F) (A := A) T hT)) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
      DivisionAlgebraDeterminantResidue (F := F) (A := A) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  let e := (divisionAlgebraRestrictedNormValuationResidueEquiv
    (F := F) (A := A) T hT).trans
      (RingEquiv.ofBijective
        (divisionAlgebraDeterminantRestrictedResidueToResidue
          (F := F) (A := A) T hT) hbij)
  exact {
    toRingEquiv := e
    commutes' := by
      intro c
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rfl }

variable [Algebra.IsCentral F A] [LocallyCompactSpace F]

/-- A local central division algebra contains a maximal-degree subfield whose norm residue field
is the entire determinant residue field as an extension of the base residue field.  This is the
scalar-compatible unramified slice required to compare it with the canonical finite-field and
Hensel unramified lift. -/
theorem exists_maximalSubfield_normValuationResidue_algEquiv :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      let T := Algebra.adjoin F ({(x : A)} : Set A)
      ∃ hT : IsField T,
        letI : NormedDivisionRing A :=
          divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
        letI : NontriviallyNormedField T :=
          divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
            (F := F) (A := A) T hT
        letI : NormedSpace F T :=
          divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
        letI : IsUltrametricDist T :=
          divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
            (F := F) (A := A) T hT
        Module.finrank F T = divisionAlgebraDegree (F := F) (A := A) ∧
          Nonempty (NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
            DivisionAlgebraDeterminantResidue (F := F) (A := A)) := by
  obtain ⟨x, hdegree, hgen⟩ :=
    exists_fullResidueDegree_maximalSubfieldGenerator (F := F) (A := A)
  let T := Algebra.adjoin F ({(x : A)} : Set A)
  let hT : IsField T := algebraAdjoinSingleton_isField_of_finiteDivisionRing F A (x : A)
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  have hbij : Function.Bijective
      (divisionAlgebraDeterminantRestrictedResidueToResidue
        (F := F) (A := A) T hT) := ⟨
    divisionAlgebraDeterminantRestrictedResidueToResidue_injective
      (F := F) (A := A) T hT,
    divisionAlgebraDeterminantRestrictedResidueToResidue_surjective_of_generator
      (F := F) (A := A) T hT x
      (Algebra.self_mem_adjoin_singleton F (x : A)) hgen⟩
  exact ⟨x, hT, hdegree,
    ⟨divisionAlgebraRestrictedNormValuationResidueAlgEquiv_of_bijective
      (F := F) (A := A) T hT hbij⟩⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
