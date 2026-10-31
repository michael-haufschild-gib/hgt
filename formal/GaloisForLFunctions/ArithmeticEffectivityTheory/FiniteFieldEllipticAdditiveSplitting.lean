import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticQuotientHaar

/-!
# Continuous reduction to the elliptic additive domain

The compact gap domain is an additive complement to the diagonal field.
Its quotient homeomorphism gives a continuous additive reduction map.
The rational correction is integral at every finite place where the
original adele is integral, so reduction introduces no new bad places.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open scoped WithZero WithZeroMulInt
noncomputable section

/-- Continuous additive reduction to the actual compact fundamental domain. -/
def adeleGapProjection : Adeles →+ ellipticAdditiveDomain :=
  additiveQuotientEquiv.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' diagonalAdeles)

theorem continuous_adeleGapProjection : Continuous adeleGapProjection :=
  additiveQuotientHomeomorph.symm.continuous.comp QuotientAddGroup.continuous_mk

@[simp] theorem adeleGapProjection_domain (d : ellipticAdditiveDomain) :
    adeleGapProjection (d : Adeles) = d :=
  additiveQuotientEquiv.symm_apply_apply d

@[simp] theorem adeleGapProjection_diagonal (z : K) :
    adeleGapProjection (adeleEmbedding z) = 0 := by
  have hz : (adeleEmbedding z : AdditiveQuotient) = 0 := by
    apply QuotientAddGroup.eq.mpr
    exact ⟨-z, by change adeleEmbedding (-z) = -adeleEmbedding z + 0; rw [map_neg, add_zero]⟩
  change additiveQuotientEquiv.symm (adeleEmbedding z : AdditiveQuotient) = 0
  rw [hz, map_zero]

private def rationalReduction (a : Adeles) : K :=
  Classical.choose (adele_exists_gap_representative a)

private theorem rationalReduction_mem (a : Adeles) :
    a - adeleEmbedding (rationalReduction a) ∈ ellipticAdditiveDomain :=
  Classical.choose_spec (adele_exists_gap_representative a)

private theorem rationalReduction_unique (a : Adeles) (z : K)
    (hz : a - adeleEmbedding z ∈ ellipticAdditiveDomain) : rationalReduction a = z := by
  obtain ⟨w, hw, hu⟩ := adele_existsUnique_gap_representative a
  exact (hu _ (rationalReduction_mem a)).trans (hu z hz).symm

/-- The diagonal function removed by the canonical additive reduction. -/
def adeleRationalProjection : Adeles →+ K where
  toFun := rationalReduction
  map_zero' := rationalReduction_unique 0 0 (by simp only [map_zero, sub_zero]; exact zero_mem _)
  map_add' a b := by
    apply rationalReduction_unique
    have h := ellipticAdditiveDomain.add_mem (rationalReduction_mem a) (rationalReduction_mem b)
    convert h using 1
    rw [map_add]
    abel

/-- Exact rational-plus-compact decomposition, with no choice of a domain left over. -/
theorem adele_rational_add_gap (a : Adeles) :
    adeleEmbedding (adeleRationalProjection a) + (adeleGapProjection a : Adeles) = a := by
  let d : ellipticAdditiveDomain := ⟨a - adeleEmbedding (adeleRationalProjection a), rationalReduction_mem a⟩
  have he : adeleGapProjection a = d := by
    have h := adeleGapProjection_domain d
    change adeleGapProjection (a - adeleEmbedding (adeleRationalProjection a)) = d at h
    simpa only [map_sub, adeleGapProjection_diagonal, sub_zero] using h
  rw [he]
  change adeleEmbedding (adeleRationalProjection a) + (a - adeleEmbedding (adeleRationalProjection a)) = a
  abel

@[simp] theorem adeleRationalProjection_diagonal (z : K) :
    adeleRationalProjection (adeleEmbedding z) = z :=
  rationalReduction_unique _ z (by rw [sub_self]; exact zero_mem _)

@[simp] theorem adeleRationalProjection_domain (d : ellipticAdditiveDomain) :
    adeleRationalProjection (d : Adeles) = 0 :=
  rationalReduction_unique _ 0 (by rw [map_zero, sub_zero]; exact d.property)

/-- The actual adele additive group splits into the diagonal field and its compact domain. -/
def adeleAdditiveSplitting : Adeles ≃+ K × ellipticAdditiveDomain where
  toFun a := (adeleRationalProjection a, adeleGapProjection a)
  invFun p := adeleEmbedding p.1 + (p.2 : Adeles)
  left_inv := adele_rational_add_gap
  right_inv p := by
    apply Prod.ext
    · simp only [map_add, adeleRationalProjection_diagonal, adeleRationalProjection_domain, add_zero]
    · simp only [map_add, adeleGapProjection_diagonal, adeleGapProjection_domain, zero_add]
  map_add' a b := Prod.ext (map_add _ a b) (map_add _ a b)

/-- Rational reduction preserves every finite place of integrality. -/
theorem adeleRationalProjection_integral_at (a : Adeles) (v : FinitePlace)
    (ha : (a.1 v) ∈ v.adicCompletionIntegers K) :
    algebraMap K (v.adicCompletion K) (adeleRationalProjection a) ∈ v.adicCompletionIntegers K := by
  have hd : ((adeleGapProjection a : Adeles).1 v) ∈ v.adicCompletionIntegers K :=
    (adeleGapProjection a).property.1 v
  have he := congrArg (fun x : Adeles => x.1 v) (adele_rational_add_gap a)
  change algebraMap K (v.adicCompletion K) (adeleRationalProjection a) +
    (adeleGapProjection a : Adeles).1 v = a.1 v at he
  rw [eq_sub_of_add_eq he]
  exact (v.adicCompletionIntegers K).sub_mem ha hd

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.continuous_adeleGapProjection
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleAdditiveSplitting
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleRationalProjection_integral_at
