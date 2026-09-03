import GaloisForLFunctions.HTGeometry.TailParameterChange
import GaloisForLFunctions.HTGeometry.FracXTranscendental
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem
import GaloisForLFunctions.HTGeometry.TailCenteredCoefficientMatch
import GaloisForLFunctions.HTGeometry.CriticalObservationField
import GaloisForLFunctions.HTGeometry.CriticalGeometricSheetFibre
import GaloisForLFunctions.HTGeometry.CenteredFreeParameter

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
      algebraMap (TailRat K n) (TailRatFree K n) (tailCoeffIn K n j) /
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
      algebraMap T Q (tailCoeffIn K n j) / q ∈ C := by
    apply IntermediateField.subset_adjoin K
    exact ⟨Sum.inl j, rfl⟩
  let j0 : Fin n := ⟨0, hn⟩
  have ht0 : algebraMap T Q (tailCoeffIn K n j0) = (algebraMap T Q p) ^ n := by
    dsimp [tailCoeffIn, p, T]
    rw [← map_pow, pow_algebraMap_X_zero hn]
  have ht0ne : algebraMap T Q (tailCoeffIn K n j0) ≠ 0 := by
    rw [ht0]
    exact pow_ne_zero _ hp
  have hc0ne : algebraMap T Q (tailCoeffIn K n j0) / q ≠ 0 :=
    div_ne_zero ht0ne hq
  have hq_formula :
      q = (algebraMap T Q p) ^ n /
        (algebraMap T Q (tailCoeffIn K n j0) / q) := by
    rw [← ht0]
    symm
    apply (div_eq_iff hc0ne).2
    exact (mul_div_cancel₀ _ hq).symm
  have hq_mem : q ∈ C := by
    rw [hq_formula]
    exact C.div_mem (C.pow_mem hp_mem n) (hc_mem j0)
  have ht_mem (j : Fin n) : algebraMap T Q (tailCoeffIn K n j) ∈ C := by
    have h := C.mul_mem hq_mem (hc_mem j)
    have heq : algebraMap T Q (tailCoeffIn K n j) =
        q * (algebraMap T Q (tailCoeffIn K n j) / q) := by
      rw [mul_div_cancel₀ _ hq]
    rw [heq]
    exact h
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

@[simp] theorem rankOneObservationRationalReindexEquiv_X (i : Fin n ⊕ Fin 1) :
    rankOneObservationRationalReindexEquiv (K := K) (n := n)
        (algebraMap (MvPolynomial (Fin n ⊕ Fin 1) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Fin 1) K)) (MvPolynomial.X i)) =
      algebraMap (MvPolynomial (Fin n ⊕ Unit) K)
        (FractionRing (MvPolynomial (Fin n ⊕ Unit) K))
        (MvPolynomial.X (rankOneObservationIndexEquiv (n := n) i)) := by
  change (IsFractionRing.ringEquivOfRingEquiv
      (MvPolynomial.renameEquiv K (rankOneObservationIndexEquiv (n := n))).toRingEquiv)
      (algebraMap (MvPolynomial (Fin n ⊕ Fin 1) K)
        (FractionRing (MvPolynomial (Fin n ⊕ Fin 1) K)) (MvPolynomial.X i)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp

/-- Raw rank-one observation coordinates identify the actual observation field with the iterated
rational model in the raw tail variables and the final reciprocal coordinate. -/
noncomputable def rankOneCriticalObservationFieldEquiv
    [IsAlgClosed K] (hn : 0 < n) :
    criticalObservationField K 1 n ≃ₐ[K] TailRatFree K n :=
  (criticalObservationFieldEquiv K (m := 1) (n := n) (by omega) hn).symm |>.trans
    (rankOneObservationRationalReindexEquiv (K := K) (n := n)) |>.trans
    (iteratedRationalFieldEquiv (K := K) (n := n))

@[simp] theorem rankOneCriticalObservationFieldEquiv_raw
    [IsAlgClosed K] (hn : 0 < n) (i : Fin n) :
    rankOneCriticalObservationFieldEquiv (K := K) hn
        (criticalObservationRaw K 1 n i) =
      iteratedRationalFamily (K := K) (n := n) (Sum.inl i) := by
  have hcrit :
      (criticalObservationFieldEquiv K (m := 1) (n := n) (by omega) hn).symm
          (criticalObservationRaw K 1 n i) =
        algebraMap (MvPolynomial (Fin n ⊕ Fin 1) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Fin 1) K))
          (MvPolynomial.X (Sum.inl i)) := by
    apply (criticalObservationFieldEquiv K (m := 1) (n := n) (by omega) hn).injective
    simp only [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [criticalObservationFieldEquiv, criticalObservationRaw,
      criticalFieldObservation]
  rw [rankOneCriticalObservationFieldEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hcrit, rankOneObservationRationalReindexEquiv_X, iteratedRationalFieldEquiv_X]
  rfl

@[simp] theorem rankOneCriticalObservationFieldEquiv_recip
    [IsAlgClosed K] (hn : 0 < n) (j : Fin 1) :
    rankOneCriticalObservationFieldEquiv (K := K) hn
        (criticalObservationRecip K 1 n j) =
      iteratedRationalFamily (K := K) (n := n) (Sum.inr Unit.unit) := by
  have hcrit :
      (criticalObservationFieldEquiv K (m := 1) (n := n) (by omega) hn).symm
          (criticalObservationRecip K 1 n j) =
        algebraMap (MvPolynomial (Fin n ⊕ Fin 1) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Fin 1) K))
          (MvPolynomial.X (Sum.inr j)) := by
    apply (criticalObservationFieldEquiv K (m := 1) (n := n) (by omega) hn).injective
    simp only [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [criticalObservationFieldEquiv, criticalObservationRecip,
      criticalFieldObservation]
  rw [rankOneCriticalObservationFieldEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hcrit, rankOneObservationRationalReindexEquiv_X, iteratedRationalFieldEquiv_X]
  congr 2

/-- Evaluation in the actual raw observation coordinates becomes ordinary evaluation in the raw
tail rational coordinates. -/
theorem rankOneCriticalObservationFieldEquiv_aeval_raw
    [IsAlgClosed K] (hn : 0 < n) (P : MvPolynomial (Fin n) K) :
    rankOneCriticalObservationFieldEquiv (K := K) hn
        (MvPolynomial.aeval (criticalObservationRaw K 1 n) P) =
      algebraMap (TailRat K n) (TailRatFree K n)
        (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) P) := by
  let e := rankOneCriticalObservationFieldEquiv (K := K) hn
  let lhs : MvPolynomial (Fin n) K →ₐ[K] TailRatFree K n :=
    e.toAlgHom.comp (MvPolynomial.aeval (criticalObservationRaw K 1 n))
  let rhs : MvPolynomial (Fin n) K →ₐ[K] TailRatFree K n :=
    (IsScalarTower.toAlgHom K (TailRat K n) (TailRatFree K n)).comp
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (TailRat K n))
  have hhom : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [lhs, rhs, e]
  exact DFunLike.congr_fun hhom P

/-- Centered coefficients inside the actual rank-one observation field. -/
noncomputable def rankOneCriticalCenteredCoeff
    [IsAlgClosed K] (hn : 0 < n) (j : Fin n) :
    criticalObservationField K 1 n :=
  MvPolynomial.aeval (criticalObservationRaw K 1 n) (tailCoeff K n j) /
    criticalObservationRecip K 1 n (0 : Fin 1)

/-- Canonical identification of a rank-one tail index with a low centered-coefficient index. -/
def rankOneCenteredLowIndex (j : Fin n) : Fin (n.succ - 1) :=
  ⟨j, by omega⟩

/-- The corresponding coefficient index in a centered polynomial of degree `n + 1`. -/
def rankOneCenteredIndex (j : Fin n) : Fin n.succ :=
  centeredIndex n.succ (rankOneCenteredLowIndex j)

/-- Rational presentation of the centered coefficient field in degree `n + 1`. -/
noncomputable def centeredCoeffFieldRationalEquiv (hn : 0 < n) :
    TailRat K n ≃ₐ[K] centeredCoeffField K n.succ :=
  (centeredCoeffFieldEquiv K n.succ (by omega)).trans
    (IntermediateField.equivOfEq (adjoin_range_centeredLowCoeffIn (K := K) (by omega)))

set_option maxHeartbeats 800000 in
@[simp] theorem centeredCoeffFieldRationalEquiv_X (hn : 0 < n) (j : Fin n) :
    centeredCoeffFieldRationalEquiv (K := K) hn
        (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X j)) =
      centeredCoeffIn K n.succ (rankOneCenteredIndex j) := by
  apply Subtype.ext
  change ((centeredCoeffFieldEquiv K n.succ (by omega)
      (algebraMap (MvPolynomial (Fin n) K)
        (FractionRing (MvPolynomial (Fin n) K)) (MvPolynomial.X j)) :
      IntermediateField.adjoin K (Set.range (centeredLowCoeffIn K n.succ))) :
      centeredField K n.succ) =
        centeredLowCoeffIn K n.succ (rankOneCenteredLowIndex j)
  exact coe_centeredCoeffFieldEquiv_X (K := K) (d := n.succ) (by omega)
    (rankOneCenteredLowIndex j)

/-- Extend the rational presentation of the centered coefficient field by one free parameter. -/
noncomputable def centeredCoeffFreeRationalEquiv (hn : 0 < n) :
    TailRatFree K n ≃ₐ[K]
      FractionRing (Polynomial (centeredCoeffField K n.succ)) :=
  IsFractionRing.fieldEquivOfAlgEquiv K
    (TailRatFree K n)
    (FractionRing (Polynomial (centeredCoeffField K n.succ)))
    (Polynomial.mapAlgEquiv (centeredCoeffFieldRationalEquiv (K := K) hn))

@[simp] theorem centeredCoeffFreeRationalEquiv_inner_X (hn : 0 < n) (j : Fin n) :
    centeredCoeffFreeRationalEquiv (K := K) hn
        (algebraMap (TailRat K n) (TailRatFree K n)
          (algebraMap (MvPolynomial (Fin n) K) (TailRat K n) (MvPolynomial.X j))) =
      algebraMap (Polynomial (centeredCoeffField K n.succ))
        (FractionRing (Polynomial (centeredCoeffField K n.succ)))
        (Polynomial.C (centeredCoeffIn K n.succ (rankOneCenteredIndex j))) := by
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
      fracX (centeredCoeffField K n.succ) := by
  let e := centeredCoeffFieldRationalEquiv (K := K) hn
  change (IsFractionRing.ringEquivOfRingEquiv
      (Polynomial.mapAlgEquiv e).toRingEquiv)
      (algebraMap (Polynomial (TailRat K n)) (TailRatFree K n) Polynomial.X) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simpa [fracX]

/-- The raw iterated model, expressed in the centered coefficient field with one free parameter. -/
noncomputable def rankOneRawToCenteredCoeffFreeEquiv (hn : 0 < n) :
    TailRatFree K n ≃ₐ[K]
      FractionRing (Polynomial (centeredCoeffField K n.succ)) :=
  (rankOneCenteredFreeFieldEquiv (K := K) hn).symm |>.trans
    (iteratedRationalFieldEquiv (K := K) (n := n)) |>.trans
    (centeredCoeffFreeRationalEquiv (K := K) hn)

set_option maxHeartbeats 800000 in
@[simp] theorem rankOneRawToCenteredCoeffFreeEquiv_centered
    (hn : 0 < n) (j : Fin n) :
    rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
        (algebraMap (TailRat K n) (TailRatFree K n) (tailCoeffIn K n j) /
          fracX (TailRat K n)) =
      algebraMap (Polynomial (centeredCoeffField K n.succ))
        (FractionRing (Polynomial (centeredCoeffField K n.succ)))
        (Polynomial.C (centeredCoeffIn K n.succ (rankOneCenteredIndex j))) := by
  have hsymm :
      (rankOneCenteredFreeFieldEquiv (K := K) hn).symm
          (rankOneCenteredFreeFamily (K := K) hn (Sum.inl j)) =
        algebraMap (MvPolynomial (Fin n ⊕ Unit) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Unit) K))
          (MvPolynomial.X (Sum.inl j)) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (rankOneCenteredFreeFieldEquiv_X (K := K) hn (Sum.inl j)).symm
  change rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
      (rankOneCenteredFreeFamily (K := K) hn (Sum.inl j)) = _
  rw [rankOneRawToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hsymm, iteratedRationalFieldEquiv_X, iteratedRationalFamily_inl,
    centeredCoeffFreeRationalEquiv_inner_X]

set_option maxHeartbeats 800000 in
@[simp] theorem rankOneRawToCenteredCoeffFreeEquiv_free (hn : 0 < n) :
    rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
        (algebraMap (TailRat K n) (TailRatFree K n)
          (algebraMap (MvPolynomial (Fin n) K) (TailRat K n)
            (MvPolynomial.X (⟨0, hn⟩ : Fin n)))) =
      fracX (centeredCoeffField K n.succ) := by
  have hsymm :
      (rankOneCenteredFreeFieldEquiv (K := K) hn).symm
          (rankOneCenteredFreeFamily (K := K) hn (Sum.inr Unit.unit)) =
        algebraMap (MvPolynomial (Fin n ⊕ Unit) K)
          (FractionRing (MvPolynomial (Fin n ⊕ Unit) K))
          (MvPolynomial.X (Sum.inr Unit.unit)) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (rankOneCenteredFreeFieldEquiv_X (K := K) hn (Sum.inr Unit.unit)).symm
  change rankOneRawToCenteredCoeffFreeEquiv (K := K) hn
      (rankOneCenteredFreeFamily (K := K) hn (Sum.inr Unit.unit)) = _
  rw [rankOneRawToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    hsymm, iteratedRationalFieldEquiv_X, iteratedRationalFamily_inr,
    centeredCoeffFreeRationalEquiv_fracX]

/-- The actual observation field, in centered coefficient coordinates and the first raw tail
parameter. -/
noncomputable def rankOneCriticalObservationToCenteredCoeffFreeEquiv
    [IsAlgClosed K] (hn : 0 < n) :
    criticalObservationField K 1 n ≃ₐ[K]
      FractionRing (Polynomial (centeredCoeffField K n.succ)) :=
  (rankOneCriticalObservationFieldEquiv (K := K) hn).trans
    (rankOneRawToCenteredCoeffFreeEquiv (K := K) hn)

set_option maxHeartbeats 800000 in
@[simp] theorem rankOneCriticalObservationToCenteredCoeffFreeEquiv_centered
    [IsAlgClosed K] (hn : 0 < n) (j : Fin n) :
    rankOneCriticalObservationToCenteredCoeffFreeEquiv (K := K) hn
        (rankOneCriticalCenteredCoeff (K := K) hn j) =
      algebraMap (Polynomial (centeredCoeffField K n.succ))
        (FractionRing (Polynomial (centeredCoeffField K n.succ)))
        (Polynomial.C (centeredCoeffIn K n.succ (rankOneCenteredIndex j))) := by
  have hmap :
      rankOneCriticalObservationFieldEquiv (K := K) hn
          (rankOneCriticalCenteredCoeff (K := K) hn j) =
        algebraMap (TailRat K n) (TailRatFree K n) (tailCoeffIn K n j) /
          fracX (TailRat K n) := by
    rw [rankOneCriticalCenteredCoeff]
    calc
      rankOneCriticalObservationFieldEquiv (K := K) hn
          (MvPolynomial.aeval (criticalObservationRaw K 1 n) (tailCoeff K n j) /
            criticalObservationRecip K 1 n (0 : Fin 1)) =
          rankOneCriticalObservationFieldEquiv (K := K) hn
              (MvPolynomial.aeval (criticalObservationRaw K 1 n) (tailCoeff K n j)) /
            rankOneCriticalObservationFieldEquiv (K := K) hn
              (criticalObservationRecip K 1 n (0 : Fin 1)) :=
        map_div₀ _ _ _
      _ = _ := by
        rw [rankOneCriticalObservationFieldEquiv_aeval_raw,
          rankOneCriticalObservationFieldEquiv_recip, iteratedRationalFamily_inr]
        rfl
  rw [rankOneCriticalObservationToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply, hmap]
  exact rankOneRawToCenteredCoeffFreeEquiv_centered (K := K) hn j

set_option maxHeartbeats 800000 in
@[simp] theorem rankOneCriticalObservationToCenteredCoeffFreeEquiv_free
    [IsAlgClosed K] (hn : 0 < n) :
    rankOneCriticalObservationToCenteredCoeffFreeEquiv (K := K) hn
        (criticalObservationRaw K 1 n (⟨0, hn⟩ : Fin n)) =
      fracX (centeredCoeffField K n.succ) := by
  rw [rankOneCriticalObservationToCenteredCoeffFreeEquiv, AlgEquiv.trans_apply,
    rankOneCriticalObservationFieldEquiv_raw, iteratedRationalFamily_inl]
  exact rankOneRawToCenteredCoeffFreeEquiv_free (K := K) hn

end

end GaloisForLFunctions.HTGeometry
