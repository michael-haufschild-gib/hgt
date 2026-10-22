import GaloisForLFunctions.HTGeometry.Critical.Observation.Field
import GaloisForLFunctions.HTGeometry.LocalizationLiftInjective
import GaloisForLFunctions.HTGeometry.FractionFieldFunctorial
import GaloisForLFunctions.HTGeometry.RationalFunctionConstantBaseChange

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private theorem genericRaw_zero_isUnit (K : Type*) [Field K] (N : ℕ) :
    IsUnit (genericRaw K N 0) := by
  rw [isUnit_iff_exists_inv]
  exact ⟨genericInv K N, genericRaw_zero_mul_inv K N⟩

/-- Coefficient extension on polynomial generic-jet coordinates, with codomain the enlarged
generic jet field. -/
noncomputable def genericJetPolynomialBaseChangeToField (N : ℕ) :
    genericJetRing k N →+* genericJetField K N :=
  (genericJetFieldMap K N).toRingHom.comp
    ((algebraMap (genericJetRing K N) (genericJetAlgebra K N)).comp
      (MvPolynomial.map (algebraMap k K)))

/-- Coefficient extension from the generic jet algebra into the enlarged generic jet field. -/
noncomputable def genericJetAlgebraBaseChangeToField (N : ℕ) :
    genericJetAlgebra k N →+* genericJetField K N :=
  IsLocalization.Away.lift (MvPolynomial.X (0 : Fin (N + 1)))
    (g := genericJetPolynomialBaseChangeToField (k := k) (K := K) N)
    (by
      rw [genericJetPolynomialBaseChangeToField, RingHom.comp_apply,
        RingHom.comp_apply, MvPolynomial.map_X]
      have heq :
          algebraMap (genericJetRing K N) (genericJetAlgebra K N)
              (MvPolynomial.X (0 : Fin (N + 1))) = genericRaw K N 0 := by
        rw [genericRaw, dif_pos (by omega : 0 < N + 1)]
        rfl
      rw [heq]
      exact (genericRaw_zero_isUnit K N).map (genericJetFieldMap K N).toRingHom)

/-- Coefficient extension on generic jet algebras. -/
noncomputable def genericJetAlgebraBaseChange (N : ℕ) :
    genericJetAlgebra k N →ₐ[k] genericJetAlgebra K N :=
  jetLiftₐ (fun i : Fin (N + 1) ↦ genericRaw K N (i : ℕ))
    (genericRaw_zero_isUnit K N)

@[simp] theorem genericJetAlgebraBaseChange_genericRaw
    (N : ℕ) {j : ℕ} (hj : j < N + 1) :
    genericJetAlgebraBaseChange (k := k) (K := K) N (genericRaw k N j) =
      genericRaw K N j := by
  rw [genericJetAlgebraBaseChange, jetLiftₐ_apply, jetLift_genericRaw _ _ hj]

@[simp] theorem genericJetAlgebraBaseChange_genericRaw_all (N j : ℕ) :
    genericJetAlgebraBaseChange (k := k) (K := K) N (genericRaw k N j) =
      genericRaw K N j := by
  by_cases hj : j < N + 1
  · exact genericJetAlgebraBaseChange_genericRaw N hj
  · rw [genericRaw, dif_neg hj, map_zero, genericRaw, dif_neg hj]

@[simp] theorem genericJetAlgebraBaseChange_genericInv (N : ℕ) :
    genericJetAlgebraBaseChange (k := k) (K := K) N (genericInv k N) =
      genericInv K N := by
  have hs := congrArg (genericJetAlgebraBaseChange (k := k) (K := K) N)
    (genericRaw_zero_mul_inv k N)
  rw [map_mul, map_one, genericJetAlgebraBaseChange_genericRaw_all] at hs
  apply mul_left_cancel₀ (genericRaw_zero_isUnit K N).ne_zero
  rw [hs, genericRaw_zero_mul_inv K N]

@[simp] theorem genericJetAlgebraBaseChange_genericRecip (N j : ℕ) :
    genericJetAlgebraBaseChange (k := k) (K := K) N (genericRecip k N j) =
      genericRecip K N j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => simp [genericRecip]
      | succ r =>
          rw [genericRecip, genericRecip, map_mul, map_neg, map_sum,
            genericJetAlgebraBaseChange_genericInv]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_mul, genericJetAlgebraBaseChange_genericRaw_all,
            ih (r - i) (by omega)]

@[simp] theorem genericJetAlgebraBaseChangeToField_genericRaw
    (N : ℕ) {j : ℕ} (hj : j < N + 1) :
    genericJetAlgebraBaseChangeToField (k := k) (K := K) N (genericRaw k N j) =
      genericJetFieldMap K N (genericRaw K N j) := by
  rw [genericRaw, dif_pos hj, genericJetAlgebraBaseChangeToField,
    IsLocalization.Away.lift_eq, genericJetPolynomialBaseChangeToField,
    RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_X]
  apply congrArg (genericJetFieldMap K N)
  rw [genericRaw, dif_pos hj]

theorem genericJetAlgebraBaseChangeToField_injective (N : ℕ) :
    Function.Injective (genericJetAlgebraBaseChangeToField (k := k) (K := K) N) := by
  have hpoly : Function.Injective
      (genericJetPolynomialBaseChangeToField (k := k) (K := K) N) := by
    exact (genericJetFieldMap_injective K N).comp
      ((IsLocalization.injective (genericJetAlgebra K N)
        (powers_le_nonZeroDivisors_of_noZeroDivisors
          (MvPolynomial.X_ne_zero (R := K) (0 : Fin (N + 1))))).comp
        (MvPolynomial.map_injective _ (algebraMap k K).injective))
  rw [genericJetAlgebraBaseChangeToField]
  exact injective_localizationLift_of_injective
    (M := Submonoid.powers (MvPolynomial.X (0 : Fin (N + 1))))
    (genericJetPolynomialBaseChangeToField (k := k) (K := K) N) hpoly
    (by
      rintro ⟨r, hr⟩
      exact pow_ne_zero r (MvPolynomial.X_ne_zero (R := k) (0 : Fin (N + 1))) hr)

theorem genericJetAlgebraBaseChange_injective (N : ℕ) :
    Function.Injective (genericJetAlgebraBaseChange (k := k) (K := K) N) := by
  intro x y hxy
  have hcomp :
      (genericJetFieldMap K N).toRingHom.comp
          (genericJetAlgebraBaseChange (k := k) (K := K) N).toRingHom =
        genericJetAlgebraBaseChangeToField (k := k) (K := K) N := by
    apply IsLocalization.ringHom_ext
      (R := MvPolynomial (Fin (N + 1)) k)
      (S := genericJetAlgebra k N) (P := genericJetField K N)
      (Submonoid.powers (MvPolynomial.X (0 : Fin (N + 1))))
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [genericJetAlgebraBaseChange, genericJetAlgebraBaseChangeToField,
        genericJetPolynomialBaseChangeToField, jetLiftₐ, jetLift_algebraMap,
        IsScalarTower.algebraMap_apply k K (genericJetAlgebra K N)]
      change algebraMap K (genericJetField K N) (algebraMap k K c) =
        algebraMap (genericJetAlgebra K N) (genericJetField K N)
          (algebraMap (genericJetRing K N) (genericJetAlgebra K N)
            (algebraMap K (genericJetRing K N) (algebraMap k K c)))
      rw [← IsScalarTower.algebraMap_apply K (genericJetRing K N) (genericJetAlgebra K N),
        ← IsScalarTower.algebraMap_apply K (genericJetAlgebra K N) (genericJetField K N)]
    · intro i
      simp [genericJetAlgebraBaseChange, genericJetAlgebraBaseChangeToField,
        genericJetPolynomialBaseChangeToField, jetLiftₐ, jetLift_algebraMap,
        genericRaw]
      rw [if_pos (by omega)]
  apply genericJetAlgebraBaseChangeToField_injective (k := k) (K := K) N
  calc
    genericJetAlgebraBaseChangeToField (k := k) (K := K) N x =
        genericJetFieldMap K N
          (genericJetAlgebraBaseChange (k := k) (K := K) N x) :=
      (DFunLike.congr_fun hcomp x).symm
    _ = genericJetFieldMap K N
          (genericJetAlgebraBaseChange (k := k) (K := K) N y) :=
      congrArg (genericJetFieldMap K N) hxy
    _ = genericJetAlgebraBaseChangeToField (k := k) (K := K) N y :=
      DFunLike.congr_fun hcomp y

/-- Coefficient extension on generic jet function fields. -/
noncomputable def genericJetFieldBaseChange (N : ℕ) :
    genericJetField k N →+* genericJetField K N :=
  fracLift (genericJetAlgebraBaseChange_injective (k := k) (K := K) N)

/-- Coefficient extension on generic jet function fields, as an algebra homomorphism over the
smaller coefficient field. -/
noncomputable def genericJetFieldBaseChangeAlgHom (N : ℕ) :
    genericJetField k N →ₐ[k] genericJetField K N where
  toRingHom := genericJetFieldBaseChange (k := k) (K := K) N
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply k (genericJetAlgebra k N) (genericJetField k N)]
    change fracLift (genericJetAlgebraBaseChange_injective (k := k) (K := K) N)
      (algebraMap (genericJetAlgebra k N) (genericJetField k N)
        (algebraMap k (genericJetAlgebra k N) c)) = _
    rw [fracLift_algebraMap]
    change algebraMap (genericJetAlgebra K N) (genericJetField K N)
        (genericJetAlgebraBaseChange (k := k) (K := K) N
          (algebraMap k (genericJetAlgebra k N) c)) = _
    rw [(genericJetAlgebraBaseChange (k := k) (K := K) N).commutes c]
    exact (IsScalarTower.algebraMap_apply k (genericJetAlgebra K N)
      (genericJetField K N) c).symm

theorem genericJetFieldBaseChange_injective (N : ℕ) :
    Function.Injective (genericJetFieldBaseChange (k := k) (K := K) N) :=
  fracLift_injective (genericJetAlgebraBaseChange_injective (k := k) (K := K) N)

@[simp] theorem genericJetFieldBaseChange_genericRaw
    (N : ℕ) {j : ℕ} (hj : j < N + 1) :
    genericJetFieldBaseChange (k := k) (K := K) N
        (genericJetFieldMap k N (genericRaw k N j)) =
      genericJetFieldMap K N (genericRaw K N j) := by
  change fracLift (genericJetAlgebraBaseChange_injective (k := k) (K := K) N)
      (algebraMap (genericJetAlgebra k N) (genericJetField k N) (genericRaw k N j)) = _
  rw [fracLift_algebraMap]
  change genericJetFieldMap K N
      (genericJetAlgebraBaseChange (k := k) (K := K) N (genericRaw k N j)) = _
  rw [genericJetAlgebraBaseChange_genericRaw _ hj]

@[simp] theorem genericJetFieldBaseChange_genericRecip (N j : ℕ) :
    genericJetFieldBaseChange (k := k) (K := K) N
        (genericJetFieldMap k N (genericRecip k N j)) =
      genericJetFieldMap K N (genericRecip K N j) := by
  change fracLift (genericJetAlgebraBaseChange_injective (k := k) (K := K) N)
      (algebraMap (genericJetAlgebra k N) (genericJetField k N) (genericRecip k N j)) = _
  rw [fracLift_algebraMap]
  change genericJetFieldMap K N
      (genericJetAlgebraBaseChange (k := k) (K := K) N (genericRecip k N j)) = _
  rw [genericJetAlgebraBaseChange_genericRecip]

theorem genericJetFieldBaseChange_mem_criticalSourceField
    (m n : ℕ) {x : genericJetField k (m + n)}
    (hx : x ∈ criticalSourceField k m n) :
    genericJetFieldBaseChange (k := k) (K := K) (m + n) x ∈
      criticalSourceField K m n := by
  let f := genericJetFieldBaseChangeAlgHom (k := k) (K := K) (m + n)
  let p : ∀ z, z ∈ IntermediateField.adjoin k
      (Set.range (fun j : Fin (m + n) ↦ criticalAmbientRaw k m n (j : ℕ))) → Prop :=
    fun z _ ↦ f z ∈ criticalSourceField K m n
  have hx' : x ∈ IntermediateField.adjoin k
      (Set.range (fun j : Fin (m + n) ↦ criticalAmbientRaw k m n (j : ℕ))) := by
    simpa [criticalSourceField] using hx
  change p x hx'
  refine IntermediateField.adjoin_induction k (p := p) ?_ ?_ ?_ ?_ ?_ hx'
  · intro z hz
    obtain ⟨j, rfl⟩ := hz
    change genericJetFieldBaseChange (k := k) (K := K) (m + n)
        (genericJetFieldMap k (m + n) (genericRaw k (m + n) (j : ℕ))) ∈ _
    rw [genericJetFieldBaseChange_genericRaw _ (by omega)]
    exact criticalAmbientRaw_mem_criticalSourceField K j.isLt
  · intro c
    change f (algebraMap k (genericJetField k (m + n)) c) ∈ _
    rw [f.commutes]
    exact IntermediateField.algebraMap_mem _ (algebraMap k K c)
  · intro z w hz hw hz' hw'
    change f (z + w) ∈ _
    rw [map_add]
    exact (criticalSourceField K m n).add_mem hz' hw'
  · intro z hz hz'
    change f z⁻¹ ∈ _
    rw [map_inv₀]
    exact (criticalSourceField K m n).inv_mem hz'
  · intro z w hz hw hz' hw'
    change f (z * w) ∈ _
    rw [map_mul]
    exact (criticalSourceField K m n).mul_mem hz' hw'

/-- Coefficient extension restricted to the exact critical source fields. -/
noncomputable def criticalSourceFieldBaseChange (m n : ℕ) :
    criticalSourceField k m n →ₐ[k] criticalSourceField K m n where
  toFun x := ⟨genericJetFieldBaseChange (k := k) (K := K) (m + n) x,
    genericJetFieldBaseChange_mem_criticalSourceField m n x.property⟩
  map_one' := Subtype.ext (genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_one
  map_mul' x y := Subtype.ext
    ((genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_mul x y)
  map_zero' := Subtype.ext (genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_zero
  map_add' x y := Subtype.ext
    ((genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_add x y)
  commutes' c := by
    apply Subtype.ext
    exact (genericJetFieldBaseChangeAlgHom (k := k) (K := K) (m + n)).commutes c

@[simp] theorem criticalSourceFieldBaseChange_raw (m n : ℕ) (j : Fin (m + n)) :
    criticalSourceFieldBaseChange (k := k) (K := K) m n (criticalSourceRaw k m n j) =
      criticalSourceRaw K m n j := by
  apply Subtype.ext
  exact genericJetFieldBaseChange_genericRaw (k := k) (K := K) (m + n) (by omega)

theorem genericJetFieldBaseChange_mem_criticalObservationField
    (m n : ℕ) {x : genericJetField k (m + n)}
    (hx : x ∈ criticalObservationField k m n) :
    genericJetFieldBaseChange (k := k) (K := K) (m + n) x ∈
      criticalObservationField K m n := by
  let f := genericJetFieldBaseChangeAlgHom (k := k) (K := K) (m + n)
  let p : ∀ z, z ∈ IntermediateField.adjoin k
      (Set.range (criticalFieldObservation k m n)) → Prop :=
    fun z _ ↦ f z ∈ criticalObservationField K m n
  have hx' : x ∈ IntermediateField.adjoin k
      (Set.range (criticalFieldObservation k m n)) := by
    simpa [criticalObservationField] using hx
  change p x hx'
  refine IntermediateField.adjoin_induction k (p := p) ?_ ?_ ?_ ?_ ?_ hx'
  · intro z hz
    obtain ⟨s, rfl⟩ := hz
    rcases s with i | j
    · change genericJetFieldBaseChange (k := k) (K := K) (m + n)
          (genericJetFieldMap k (m + n) (genericRaw k (m + n) (m + (i : ℕ)))) ∈ _
      rw [genericJetFieldBaseChange_genericRaw _ (by omega)]
      apply IntermediateField.subset_adjoin K
      exact ⟨Sum.inl i, rfl⟩
    · change genericJetFieldBaseChange (k := k) (K := K) (m + n)
          (genericJetFieldMap k (m + n) (genericRecip k (m + n) (n + (j : ℕ)))) ∈ _
      rw [genericJetFieldBaseChange_genericRecip]
      apply IntermediateField.subset_adjoin K
      exact ⟨Sum.inr j, rfl⟩
  · intro c
    change f (algebraMap k (genericJetField k (m + n)) c) ∈ _
    rw [f.commutes]
    exact IntermediateField.algebraMap_mem _ (algebraMap k K c)
  · intro z w hz hw hz' hw'
    change f (z + w) ∈ _
    rw [map_add]
    exact (criticalObservationField K m n).add_mem hz' hw'
  · intro z hz hz'
    change f z⁻¹ ∈ _
    rw [map_inv₀]
    exact (criticalObservationField K m n).inv_mem hz'
  · intro z w hz hw hz' hw'
    change f (z * w) ∈ _
    rw [map_mul]
    exact (criticalObservationField K m n).mul_mem hz' hw'

/-- Coefficient extension restricted to the exact critical observation fields. -/
noncomputable def criticalObservationFieldBaseChange (m n : ℕ) :
    criticalObservationField k m n →ₐ[k] criticalObservationField K m n where
  toFun x := ⟨genericJetFieldBaseChange (k := k) (K := K) (m + n) x,
    genericJetFieldBaseChange_mem_criticalObservationField m n x.property⟩
  map_one' := Subtype.ext (genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_one
  map_mul' x y := Subtype.ext
    ((genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_mul x y)
  map_zero' := Subtype.ext (genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_zero
  map_add' x y := Subtype.ext
    ((genericJetFieldBaseChange (k := k) (K := K) (m + n)).map_add x y)
  commutes' c := by
    apply Subtype.ext
    exact (genericJetFieldBaseChangeAlgHom (k := k) (K := K) (m + n)).commutes c

@[simp] theorem criticalObservationFieldBaseChange_coord
    (m n : ℕ) (s : Fin n ⊕ Fin m) :
    criticalObservationFieldBaseChange (k := k) (K := K) m n
        ⟨criticalFieldObservation k m n s,
          by
            apply IntermediateField.subset_adjoin k
            exact Set.mem_range_self s⟩ =
      ⟨criticalFieldObservation K m n s,
        by
          apply IntermediateField.subset_adjoin K
          exact Set.mem_range_self s⟩ := by
  apply Subtype.ext
  rcases s with i | j
  · exact genericJetFieldBaseChange_genericRaw _ (by omega)
  · exact genericJetFieldBaseChange_genericRecip _ _

@[simp] theorem criticalObservationFieldBaseChange_raw
    (m n : ℕ) (i : Fin n) :
    criticalObservationFieldBaseChange (k := k) (K := K) m n
        (criticalObservationRaw k m n i) =
      criticalObservationRaw K m n i := by
  simpa [criticalObservationRaw, criticalFieldObservation] using
    (criticalObservationFieldBaseChange_coord (k := k) (K := K)
      m n (Sum.inl i))

@[simp] theorem criticalObservationFieldBaseChange_recip
    (m n : ℕ) (j : Fin m) :
    criticalObservationFieldBaseChange (k := k) (K := K) m n
        (criticalObservationRecip k m n j) =
      criticalObservationRecip K m n j := by
  simpa [criticalObservationRecip, criticalFieldObservation] using
    (criticalObservationFieldBaseChange_coord (k := k) (K := K)
      m n (Sum.inr j))

end

end GaloisForLFunctions.HTGeometry
