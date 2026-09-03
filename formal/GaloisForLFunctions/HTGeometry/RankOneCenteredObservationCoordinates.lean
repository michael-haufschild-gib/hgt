import GaloisForLFunctions.HTGeometry.TailParameterChange
import GaloisForLFunctions.HTGeometry.FracXTranscendental
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem
import GaloisForLFunctions.HTGeometry.TailCenteredCoefficientMatch
import GaloisForLFunctions.HTGeometry.CriticalObservationField

/-!
# Centered coordinates for the rank-one observation field

Write the rank-one observation field as the rational functions in the raw tail parameters and one
free reciprocal coefficient.  Dividing the tail coefficients by that free coefficient gives the
centered coefficients of the monic fibre polynomial.  The first tail parameter replaces the free
reciprocal coefficient because its `n`-th power is the first tail coefficient.

This file proves the resulting family of `n + 1` coordinates is algebraically independent and
generates the whole iterated rational function field.  Thus the actual rank-one observation model
is birationally the centered coefficient field with one free parameter; no Kummer hypothesis is
retained.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Rational function field in the raw rank-one tail parameters. -/
abbrev TailRat (K : Type*) [Field K] (n : ℕ) :=
  FractionRing (MvPolynomial (Fin n) K)

/-- One further free rational parameter over the raw tail field. -/
abbrev TailRatFree (K : Type*) [Field K] (n : ℕ) :=
  FractionRing (Polynomial (TailRat K n))

/-- A polynomial ring on the disjoint raw-tail and free coordinates is the iterated polynomial
ring with the free coordinate outermost. -/
noncomputable def iteratedMvPolynomialEquiv :
    MvPolynomial (Fin n ⊕ Unit) K ≃ₐ[K]
      Polynomial (MvPolynomial (Fin n) K) :=
  (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin n) Unit)).trans
    ((MvPolynomial.sumAlgEquiv K Unit (Fin n)).trans
      ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin n) K) Unit).restrictScalars K))

/-- Evaluation of the joint polynomial coordinates in the iterated rational function field. -/
noncomputable def iteratedMvPolynomialToFree :
    MvPolynomial (Fin n ⊕ Unit) K →ₐ[K] TailRatFree K n :=
  (IsScalarTower.toAlgHom K (Polynomial (TailRat K n)) (TailRatFree K n)).comp
    ((Polynomial.mapAlgHom
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (TailRat K n))).comp
      (iteratedMvPolynomialEquiv (K := K) (n := n)).toAlgHom)

omit [CharZero K] in
theorem iteratedMvPolynomialToFree_injective :
    Function.Injective (iteratedMvPolynomialToFree (K := K) (n := n)) := by
  intro p q hpq
  apply (iteratedMvPolynomialEquiv (K := K) (n := n)).injective
  apply Polynomial.map_injective
    (algebraMap (MvPolynomial (Fin n) K) (TailRat K n))
    (IsFractionRing.injective (MvPolynomial (Fin n) K) (TailRat K n))
  exact IsFractionRing.injective (Polynomial (TailRat K n)) (TailRatFree K n) hpq

/-- The standard raw-tail coordinates together with the free outer variable. -/
noncomputable def iteratedRationalFamily :
    Fin n ⊕ Unit → TailRatFree K n := fun i =>
  iteratedMvPolynomialToFree (K := K) (n := n) (MvPolynomial.X i)

omit [CharZero K] in
theorem algebraicIndependent_iteratedRationalFamily :
    AlgebraicIndependent K (iteratedRationalFamily (K := K) (n := n)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have heq : MvPolynomial.aeval (iteratedRationalFamily (K := K) (n := n)) =
      iteratedMvPolynomialToFree (K := K) (n := n) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    rfl
  rw [heq]
  exact iteratedMvPolynomialToFree_injective

omit [CharZero K] in
@[simp] theorem iteratedRationalFamily_inl (i : Fin n) :
    iteratedRationalFamily (K := K) (Sum.inl i) =
      algebraMap (TailRat K n) (TailRatFree K n)
        (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X i)) := by
  simp [iteratedRationalFamily, iteratedMvPolynomialToFree,
    iteratedMvPolynomialEquiv]
  simpa [Polynomial.algebraMap_apply] using
    (IsScalarTower.algebraMap_apply (TailRat K n) (Polynomial (TailRat K n))
      (TailRatFree K n)
      (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X i))).symm

omit [CharZero K] in
@[simp] theorem iteratedRationalFamily_inr (i : Unit) :
    iteratedRationalFamily (K := K) (Sum.inr i) = fracX (TailRat K n) := by
  cases i
  simp [iteratedRationalFamily, iteratedMvPolynomialToFree,
    iteratedMvPolynomialEquiv, fracX]

/-- The standard iterated rational coordinates generate the whole field. -/
theorem iteratedRationalFamily_adjoin_eq_top :
    IntermediateField.adjoin K
      (Set.range (iteratedRationalFamily (K := K) (n := n))) = ⊤ := by
  let T := TailRat K n
  let Q := TailRatFree K n
  let C : IntermediateField K Q := IntermediateField.adjoin K
    (Set.range (iteratedRationalFamily (K := K) (n := n)))
  have hx_mem (i : Fin n) :
      algebraMap T Q
        (algebraMap (MvPolynomial (Fin n) K) T (MvPolynomial.X i)) ∈ C := by
    rw [← iteratedRationalFamily_inl]
    exact IntermediateField.subset_adjoin K _ (Set.mem_range_self (Sum.inl i))
  have hq_mem : fracX T ∈ C := by
    rw [← iteratedRationalFamily_inr Unit.unit]
    exact IntermediateField.subset_adjoin K _ (Set.mem_range_self (Sum.inr Unit.unit))
  have hconstants : ∀ a : T, algebraMap T Q a ∈ C := by
    let D : IntermediateField K T := IntermediateField.comap
      (IsScalarTower.toAlgHom K T Q) C
    have htailCoeff (j : Fin n) :
        algebraMap (MvPolynomial (Fin n) K) T (tailCoeff K n j) ∈ D := by
      apply algebraMap_mem_of_vars_subset (S := Set.univ) (F := D)
      · exact fun _ _ => Set.mem_univ _
      · intro i _
        exact hx_mem i
    have htail : tailParamField K n ≤ D := by
      rw [tailParamField, IntermediateField.adjoin_le_iff]
      rintro z (⟨j, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact htailCoeff j
      · exact hx_mem j
    have hD : D = ⊤ := by
      rw [tailParamField_eq_top] at htail
      exact top_unique htail
    intro a
    have ha : a ∈ D := by rw [hD]; trivial
    exact ha
  change C = ⊤
  exact eq_top_of_mem_of_mem hconstants hq_mem

/-- The joint rational function field in the raw-tail and free coordinates is the iterated
rational function field. -/
noncomputable def iteratedRationalFieldEquiv :
    FractionRing (MvPolynomial (Fin n ⊕ Unit) K) ≃ₐ[K] TailRatFree K n :=
  (algebraicIndependent_iteratedRationalFamily (K := K) (n := n)).aevalEquivField |>.trans
    (IntermediateField.equivOfEq
      (iteratedRationalFamily_adjoin_eq_top (K := K) (n := n))) |>.trans
    IntermediateField.topEquiv

@[simp] theorem iteratedRationalFieldEquiv_X (i : Fin n ⊕ Unit) :
    iteratedRationalFieldEquiv (K := K) (n := n)
        (algebraMap (MvPolynomial (Fin n ⊕ Unit) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Unit) K)) (MvPolynomial.X i)) =
      iteratedRationalFamily (K := K) (n := n) i := by
  simp [iteratedRationalFieldEquiv,
    AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]

/-- Centered coefficients of the monic fibre polynomial, followed by the first raw tail
parameter. -/
noncomputable def rankOneCenteredFreeFamily (hn : 0 < n) :
    Fin n ⊕ Unit → TailRatFree K n
  | Sum.inl j =>
      -algebraMap (TailRat K n) (TailRatFree K n) (tailCoeffIn K n j) /
        fracX (TailRat K n)
  | Sum.inr _ =>
      algebraMap (TailRat K n) (TailRatFree K n)
        (algebraMap (MvPolynomial (Fin n) K) (TailRat K n)
          (MvPolynomial.X (⟨0, hn⟩ : Fin n)))

omit [CharZero K] in
theorem fracX_tailRat_ne_zero : fracX (TailRat K n) ≠ 0 := by
  intro h
  have hX : (Polynomial.X : Polynomial (TailRat K n)) = 0 :=
    IsFractionRing.injective (Polynomial (TailRat K n)) (TailRatFree K n) (by
      simpa [fracX] using h)
  exact Polynomial.X_ne_zero hX

/-- The centered coefficients and first tail parameter generate the full rank-one observation
model. -/
theorem rankOneCenteredFreeFamily_adjoin_eq_top (hn : 0 < n) :
    IntermediateField.adjoin K
      (Set.range (rankOneCenteredFreeFamily (K := K) hn)) = ⊤ := by
  let T := TailRat K n
  let Q := TailRatFree K n
  let p : T := algebraMap (MvPolynomial (Fin n) K) T
    (MvPolynomial.X (⟨0, hn⟩ : Fin n))
  let q : Q := fracX T
  let C : IntermediateField K Q := IntermediateField.adjoin K
    (Set.range (rankOneCenteredFreeFamily (K := K) hn))
  have hpT : p ≠ 0 := by
    dsimp [p, T]
    intro h
    apply MvPolynomial.X_ne_zero (R := K) (⟨0, hn⟩ : Fin n)
    apply IsFractionRing.injective (MvPolynomial (Fin n) K) (TailRat K n)
    simpa using h
  have hp : algebraMap T Q p ≠ 0 := by
    intro h
    apply hpT
    apply (algebraMap T Q).injective
    simpa using h
  have hq : q ≠ 0 := fracX_tailRat_ne_zero
  have hp_mem : algebraMap T Q p ∈ C := by
    apply IntermediateField.subset_adjoin K
    exact ⟨Sum.inr Unit.unit, rfl⟩
  have hc_mem (j : Fin n) :
      -algebraMap T Q (tailCoeffIn K n j) / q ∈ C := by
    apply IntermediateField.subset_adjoin K
    exact ⟨Sum.inl j, rfl⟩
  let j0 : Fin n := ⟨0, hn⟩
  have ht0 : algebraMap T Q (tailCoeffIn K n j0) = (algebraMap T Q p) ^ n := by
    dsimp [tailCoeffIn, p, T]
    rw [← map_pow, pow_algebraMap_X_zero hn]
  have ht0ne : algebraMap T Q (tailCoeffIn K n j0) ≠ 0 := by
    rw [ht0]
    exact pow_ne_zero _ hp
  have hc0ne : -algebraMap T Q (tailCoeffIn K n j0) / q ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr ht0ne) hq
  have hq_formula :
      q = -(algebraMap T Q p) ^ n /
        (-algebraMap T Q (tailCoeffIn K n j0) / q) := by
    rw [← ht0]
    symm
    apply (div_eq_iff hc0ne).2
    exact (mul_div_cancel₀ _ hq).symm
  have hq_mem : q ∈ C := by
    rw [hq_formula]
    exact C.div_mem (C.neg_mem (C.pow_mem hp_mem n)) (hc_mem j0)
  have ht_mem (j : Fin n) : algebraMap T Q (tailCoeffIn K n j) ∈ C := by
    have h := C.mul_mem hq_mem (hc_mem j)
    have heq : algebraMap T Q (tailCoeffIn K n j) =
        -(q * (-algebraMap T Q (tailCoeffIn K n j) / q)) := by
      rw [mul_div_cancel₀ _ hq, neg_neg]
    rw [heq]
    exact C.neg_mem h
  have hconstants : ∀ a : T, algebraMap T Q a ∈ C := by
    let D : IntermediateField K T := IntermediateField.comap
      (IsScalarTower.toAlgHom K T Q) C
    have htail : tailParamField K n ≤ D := by
      rw [tailParamField, IntermediateField.adjoin_le_iff]
      rintro z (⟨j, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ht_mem j
      · have hj0 : j = (⟨0, hn⟩ : Fin n) := Fin.ext hj
        subst j
        exact hp_mem
    have hD : D = ⊤ := by
      rw [tailParamField_eq_top] at htail
      exact top_unique htail
    intro a
    have ha : a ∈ D := by rw [hD]; trivial
    exact ha
  change C = ⊤
  exact eq_top_of_mem_of_mem hconstants hq_mem

/-- The centered coefficients together with the first raw tail parameter are algebraically
independent.  Combined with `rankOneCenteredFreeFamily_adjoin_eq_top`, they are rational
coordinates on the whole rank-one observation field model. -/
theorem algebraicIndependent_rankOneCenteredFreeFamily (hn : 0 < n) :
    AlgebraicIndependent K (rankOneCenteredFreeFamily (K := K) hn) := by
  apply algebraicIndependent_of_adjoin_eq_of_finite
    (iteratedRationalFamily (K := K) (n := n))
    (rankOneCenteredFreeFamily (K := K) hn)
    algebraicIndependent_iteratedRationalFamily
  rw [rankOneCenteredFreeFamily_adjoin_eq_top hn,
    iteratedRationalFamily_adjoin_eq_top]

/-- The rational function field on centered coefficients and one free coordinate is the actual
rank-one observation model in raw coordinates. -/
noncomputable def rankOneCenteredFreeFieldEquiv (hn : 0 < n) :
    FractionRing (MvPolynomial (Fin n ⊕ Unit) K) ≃ₐ[K] TailRatFree K n :=
  (algebraicIndependent_rankOneCenteredFreeFamily (K := K) hn).aevalEquivField |>.trans
    (IntermediateField.equivOfEq
      (rankOneCenteredFreeFamily_adjoin_eq_top (K := K) hn)) |>.trans
    IntermediateField.topEquiv

@[simp] theorem rankOneCenteredFreeFieldEquiv_X (hn : 0 < n) (i : Fin n ⊕ Unit) :
    rankOneCenteredFreeFieldEquiv (K := K) hn
        (algebraMap (MvPolynomial (Fin n ⊕ Unit) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Unit) K)) (MvPolynomial.X i)) =
      rankOneCenteredFreeFamily (K := K) hn i := by
  simp [rankOneCenteredFreeFieldEquiv,
    AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]

/-- Reindex the unique reciprocal observation coordinate as a singleton free coordinate. -/
noncomputable def rankOneObservationIndexEquiv :
    Fin n ⊕ Fin 1 ≃ Fin n ⊕ Unit :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique _ _)

/-- Reindexing the unique reciprocal observation coordinate induces an equivalence of rational
function fields. -/
noncomputable def rankOneObservationRationalReindexEquiv :
    FractionRing (MvPolynomial (Fin n ⊕ Fin 1) K) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin n ⊕ Unit) K) :=
  IsFractionRing.fieldEquivOfAlgEquiv K
    (FractionRing (MvPolynomial (Fin n ⊕ Fin 1) K))
    (FractionRing (MvPolynomial (Fin n ⊕ Unit) K))
    (MvPolynomial.renameEquiv K (rankOneObservationIndexEquiv (n := n)))

/-- Raw rank-one observation coordinates identify the actual observation field with the iterated
rational model in the raw tail variables and the final reciprocal coordinate. -/
noncomputable def rankOneCriticalObservationFieldEquiv
    [IsAlgClosed K] (hn : 0 < n) :
    criticalObservationField K 1 n ≃ₐ[K] TailRatFree K n :=
  (criticalObservationFieldEquiv K (m := 1) (n := n) (by omega) hn).symm |>.trans
    (rankOneObservationRationalReindexEquiv (K := K) (n := n)) |>.trans
    (iteratedRationalFieldEquiv (K := K) (n := n))

/-- Rational presentation of the centered coefficient field in degree `n + 1`. -/
noncomputable def centeredCoeffFieldRationalEquiv (hn : 0 < n) :
    TailRat K n ≃ₐ[K] centeredCoeffField K (n + 1) :=
  (centeredCoeffFieldEquiv K (n + 1) (by omega)).trans
    (IntermediateField.equivOfEq (adjoin_range_centeredLowCoeffIn (K := K) (by omega)))

set_option maxHeartbeats 800000 in
@[simp] theorem centeredCoeffFieldRationalEquiv_X (hn : 0 < n) (j : Fin n) :
    centeredCoeffFieldRationalEquiv (K := K) hn
        (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X j)) =
      centeredCoeffIn K (n + 1) (centeredIndex (n + 1) j) := by
  apply Subtype.ext
  change ((centeredCoeffFieldEquiv K (n + 1) (by omega)
      (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X j)) :
      IntermediateField.adjoin K (Set.range (centeredLowCoeffIn K (n + 1)))) :
      centeredField K (n + 1)) = centeredLowCoeffIn K (n + 1) j
  exact coe_centeredCoeffFieldEquiv_X (K := K) (d := n + 1) (by omega) j

/-- Extend the rational presentation of the centered coefficient field by one free parameter. -/
noncomputable def centeredCoeffFreeRationalEquiv (hn : 0 < n) :
    TailRatFree K n ≃ₐ[K]
      FractionRing (Polynomial (centeredCoeffField K (n + 1))) :=
  IsFractionRing.fieldEquivOfAlgEquiv K
    (TailRatFree K n)
    (FractionRing (Polynomial (centeredCoeffField K (n + 1))))
    (Polynomial.mapAlgEquiv (centeredCoeffFieldRationalEquiv (K := K) hn))

@[simp] theorem centeredCoeffFreeRationalEquiv_inner_X (hn : 0 < n) (j : Fin n) :
    centeredCoeffFreeRationalEquiv (K := K) hn
        (algebraMap (TailRat K n) (TailRatFree K n)
          (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X j))) =
      algebraMap (Polynomial (centeredCoeffField K (n + 1)))
        (FractionRing (Polynomial (centeredCoeffField K (n + 1))))
        (Polynomial.C (centeredCoeffIn K (n + 1) (centeredIndex (n + 1) j))) := by
  let e := centeredCoeffFieldRationalEquiv (K := K) hn
  change (IsFractionRing.ringEquivOfRingEquiv
      (Polynomial.mapAlgEquiv e).toRingEquiv)
      (algebraMap (Polynomial (TailRat K n)) (TailRatFree K n)
        (Polynomial.C
          (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X j)))) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [e]

@[simp] theorem centeredCoeffFreeRationalEquiv_fracX (hn : 0 < n) :
    centeredCoeffFreeRationalEquiv (K := K) hn (fracX (TailRat K n)) =
      fracX (centeredCoeffField K (n + 1)) := by
  let e := centeredCoeffFieldRationalEquiv (K := K) hn
  change (IsFractionRing.ringEquivOfRingEquiv
      (Polynomial.mapAlgEquiv e).toRingEquiv)
      (algebraMap (Polynomial (TailRat K n)) (TailRatFree K n) Polynomial.X) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simpa [fracX]

/-- The raw iterated model, expressed in the centered coefficient field with one free parameter. -/
noncomputable def rankOneRawToCenteredCoeffFreeEquiv (hn : 0 < n) :
    TailRatFree K n ≃ₐ[K]
      FractionRing (Polynomial (centeredCoeffField K (n + 1))) :=
  (rankOneCenteredFreeFieldEquiv (K := K) hn).symm |>.trans
    (iteratedRationalFieldEquiv (K := K) (n := n)) |>.trans
    (centeredCoeffFreeRationalEquiv (K := K) hn)

@[simp] theorem rankOneRawToCenteredCoeffFreeEquiv_centered
    (hn : 0 < n) (j : Fin n) :
    rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
        (-algebraMap (TailRat K n) (TailRatFree K n) (tailCoeffIn K n j) /
          fracX (TailRat K n)) =
      algebraMap (Polynomial (centeredCoeffField K (n + 1)))
        (FractionRing (Polynomial (centeredCoeffField K (n + 1))))
        (Polynomial.C (centeredCoeffIn K (n + 1) (centeredIndex (n + 1) j))) := by
  have hsymm :
      (rankOneCenteredFreeFieldEquiv (K := K) hn).symm
          (rankOneCenteredFreeFamily (K := K) hn (Sum.inl j)) =
        algebraMap (MvPolynomial (Fin n ⊕ Unit) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Unit) K))
          (MvPolynomial.X (Sum.inl j)) := by
    rw [AlgEquiv.symm_apply_eq]
    exact rankOneCenteredFreeFieldEquiv_X (K := K) hn (Sum.inl j)
  change rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
      (rankOneCenteredFreeFamily (K := K) hn (Sum.inl j)) = _
  rw [rankOneRawToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hsymm, iteratedRationalFieldEquiv_X, iteratedRationalFamily_inl,
    centeredCoeffFreeRationalEquiv_inner_X]

@[simp] theorem rankOneRawToCenteredCoeffFreeEquiv_free (hn : 0 < n) :
    rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
        (algebraMap (TailRat K n) (TailRatFree K n)
          (algebraMap (MvPolynomial (Fin n) K) (TailRat K n)
            (MvPolynomial.X (⟨0, hn⟩ : Fin n)))) =
      fracX (centeredCoeffField K (n + 1)) := by
  have hsymm :
      (rankOneCenteredFreeFieldEquiv (K := K) hn).symm
          (rankOneCenteredFreeFamily (K := K) hn (Sum.inr Unit.unit)) =
        algebraMap (MvPolynomial (Fin n ⊕ Unit) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Unit) K))
          (MvPolynomial.X (Sum.inr Unit.unit)) := by
    rw [AlgEquiv.symm_apply_eq]
    exact rankOneCenteredFreeFieldEquiv_X (K := K) hn (Sum.inr Unit.unit)
  change rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
      (rankOneCenteredFreeFamily (K := K) hn (Sum.inr Unit.unit)) = _
  rw [rankOneRawToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hsymm, iteratedRationalFieldEquiv_X, iteratedRationalFamily_inr,
    centeredCoeffFreeRationalEquiv_fracX]

end

end GaloisForLFunctions.HTGeometry
