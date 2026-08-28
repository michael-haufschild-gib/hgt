import GaloisForLFunctions.HTGeometry.DisjointRationalFunctionFields
import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import Mathlib.Tactic

/-!
# Two-packet rational primitive rigidity

This file proves the denominator-safe algebraic core of ULF-PFRM-1.  A rational function on a
finite free coordinate family satisfying the two-copy additive Cauchy equation is a unique
constant-coefficient linear form.  Algebraically independent evaluation families extend to the
fraction field, and commuting packet-evaluation diagrams transfer the classification to concrete
finite rational formations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-- Polynomial addition comultiplication on a free coordinate family. -/
def freeCoordinateAddPolynomialMap
    (C ι : Type*) [Field C] :
    MvPolynomial ι C →ₐ[C] MvPolynomial (ι ⊕ ι) C :=
  MvPolynomial.aeval fun i => MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)

/-- Specialize the right packet to zero and retain the left packet. -/
def freeCoordinateRightZeroPolynomialMap
    (C ι : Type*) [Field C] :
    MvPolynomial (ι ⊕ ι) C →ₐ[C] MvPolynomial ι C :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X fun _ => 0)

@[simp]
theorem freeCoordinateRightZeroPolynomialMap_add
    {C ι : Type*} [Field C] (p : MvPolynomial ι C) :
    freeCoordinateRightZeroPolynomialMap C ι
        (freeCoordinateAddPolynomialMap C ι p) = p := by
  have hcomp :
      (freeCoordinateRightZeroPolynomialMap C ι).comp
          (freeCoordinateAddPolynomialMap C ι) =
        AlgHom.id C (MvPolynomial ι C) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [freeCoordinateRightZeroPolynomialMap, freeCoordinateAddPolynomialMap]
  exact DFunLike.congr_fun hcomp p

theorem freeCoordinateAddPolynomialMap_injective
    {C ι : Type*} [Field C] :
    Function.Injective (freeCoordinateAddPolynomialMap C ι) := by
  intro p q hpq
  simpa using congrArg (freeCoordinateRightZeroPolynomialMap C ι) hpq

theorem pderiv_freeCoordinateAddPolynomialMap_left
    {C ι : Type*} [Field C] (i : ι) (p : MvPolynomial ι C) :
    MvPolynomial.pderiv (Sum.inl i) (freeCoordinateAddPolynomialMap C ι p) =
      freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i p) := by
  classical
  letI : Algebra (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (freeCoordinateAddPolynomialMap C ι).toRingHom.toAlgebra
  let D₁ : Derivation C (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (MvPolynomial.pderiv (R := C) (Sum.inl i)).compAlgebraMap (MvPolynomial ι C)
  let D₂ : Derivation C (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    Derivation.mk'
      ((freeCoordinateAddPolynomialMap C ι).toLinearMap.comp
        (MvPolynomial.pderiv (R := C) i).toLinearMap)
      (by
        intro x y
        change freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i (x * y)) =
          freeCoordinateAddPolynomialMap C ι x *
              freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i y) +
            freeCoordinateAddPolynomialMap C ι y *
              freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i x)
        rw [Derivation.leibniz]
        simp only [smul_eq_mul, map_add, map_mul])
  have hD : D₁ = D₂ := by
    apply MvPolynomial.derivation_ext
    intro j
    change MvPolynomial.pderiv (Sum.inl i)
        (freeCoordinateAddPolynomialMap C ι (MvPolynomial.X j)) =
      freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i (MvPolynomial.X j))
    by_cases h : i = j
    · subst j
      simp [freeCoordinateAddPolynomialMap]
    · simp [freeCoordinateAddPolynomialMap, h]
  exact DFunLike.congr_fun hD p

theorem pderiv_freeCoordinateAddPolynomialMap_right
    {C ι : Type*} [Field C] (i : ι) (p : MvPolynomial ι C) :
    MvPolynomial.pderiv (Sum.inr i) (freeCoordinateAddPolynomialMap C ι p) =
      freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i p) := by
  classical
  letI : Algebra (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (freeCoordinateAddPolynomialMap C ι).toRingHom.toAlgebra
  let D₁ : Derivation C (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (MvPolynomial.pderiv (R := C) (Sum.inr i)).compAlgebraMap (MvPolynomial ι C)
  let D₂ : Derivation C (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    Derivation.mk'
      ((freeCoordinateAddPolynomialMap C ι).toLinearMap.comp
        (MvPolynomial.pderiv (R := C) i).toLinearMap)
      (by
        intro x y
        change freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i (x * y)) =
          freeCoordinateAddPolynomialMap C ι x *
              freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i y) +
            freeCoordinateAddPolynomialMap C ι y *
              freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i x)
        rw [Derivation.leibniz]
        simp only [smul_eq_mul, map_add, map_mul])
  have hD : D₁ = D₂ := by
    apply MvPolynomial.derivation_ext
    intro j
    change MvPolynomial.pderiv (Sum.inr i)
        (freeCoordinateAddPolynomialMap C ι (MvPolynomial.X j)) =
      freeCoordinateAddPolynomialMap C ι (MvPolynomial.pderiv i (MvPolynomial.X j))
    by_cases h : i = j
    · subst j
      simp [freeCoordinateAddPolynomialMap]
    · simp [freeCoordinateAddPolynomialMap, h]
  exact DFunLike.congr_fun hD p

theorem pderiv_rename_inl
    {C ι : Type*} [Field C] (i : ι) (p : MvPolynomial ι C) :
    MvPolynomial.pderiv (Sum.inl i)
        (MvPolynomial.rename (Sum.inl : ι → ι ⊕ ι) p) =
      MvPolynomial.rename (Sum.inl : ι → ι ⊕ ι) (MvPolynomial.pderiv i p) :=
  MvPolynomial.pderiv_rename Sum.inl_injective i p

theorem pderiv_rename_inr
    {C ι : Type*} [Field C] (i : ι) (p : MvPolynomial ι C) :
    MvPolynomial.pderiv (Sum.inr i)
        (MvPolynomial.rename (Sum.inr : ι → ι ⊕ ι) p) =
      MvPolynomial.rename (Sum.inr : ι → ι ⊕ ι) (MvPolynomial.pderiv i p) :=
  MvPolynomial.pderiv_rename Sum.inr_injective i p

theorem pderiv_rename_inl_cross
    {C ι : Type*} [Field C] (i : ι) (p : MvPolynomial ι C) :
    MvPolynomial.pderiv (Sum.inr i) (MvPolynomial.rename Sum.inl p) = 0 := by
  classical
  letI : Algebra (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (MvPolynomial.rename (R := C) Sum.inl).toRingHom.toAlgebra
  let D : Derivation C (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (MvPolynomial.pderiv (R := C) (Sum.inr i)).compAlgebraMap (MvPolynomial ι C)
  have hD : D = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    change MvPolynomial.pderiv (Sum.inr i)
        (MvPolynomial.rename Sum.inl (MvPolynomial.X j)) = 0
    simp
  exact DFunLike.congr_fun hD p

theorem pderiv_rename_inr_cross
    {C ι : Type*} [Field C] (i : ι) (p : MvPolynomial ι C) :
    MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.rename Sum.inr p) = 0 := by
  classical
  letI : Algebra (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (MvPolynomial.rename (R := C) Sum.inr).toRingHom.toAlgebra
  let D : Derivation C (MvPolynomial ι C) (MvPolynomial (ι ⊕ ι) C) :=
    (MvPolynomial.pderiv (R := C) (Sum.inl i)).compAlgebraMap (MvPolynomial ι C)
  have hD : D = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    change MvPolynomial.pderiv (Sum.inl i)
        (MvPolynomial.rename Sum.inr (MvPolynomial.X j)) = 0
    simp
  exact DFunLike.congr_fun hD p

/-- Rational addition comultiplication `F(X) ↦ F(X + Y)`. -/
def freeCoordinateAddMap
    (C ι : Type*) [Field C] :
    FreeCoordinateRationalField C ι →ₐ[C]
      FreeCoordinateRationalField C (ι ⊕ ι) := by
  let g : MvPolynomial ι C →ₐ[C] FreeCoordinateRationalField C (ι ⊕ ι) :=
    (IsScalarTower.toAlgHom C (MvPolynomial (ι ⊕ ι) C)
      (FreeCoordinateRationalField C (ι ⊕ ι))).comp
        (freeCoordinateAddPolynomialMap C ι)
  exact IsFractionRing.liftAlgHom (g := g)
    ((IsFractionRing.injective (MvPolynomial (ι ⊕ ι) C)
      (FreeCoordinateRationalField C (ι ⊕ ι))).comp
        freeCoordinateAddPolynomialMap_injective)

@[simp]
theorem freeCoordinateAddMap_algebraMap
    {C ι : Type*} [Field C] (p : MvPolynomial ι C) :
    freeCoordinateAddMap C ι
        (algebraMap (MvPolynomial ι C) (FreeCoordinateRationalField C ι) p) =
      algebraMap (MvPolynomial (ι ⊕ ι) C)
        (FreeCoordinateRationalField C (ι ⊕ ι))
          (freeCoordinateAddPolynomialMap C ι p) := by
  simp [freeCoordinateAddMap, IsFractionRing.liftAlgHom_apply,
    IsFractionRing.lift_algebraMap]

/-- Left pure-packet embedding `F(X)`. -/
def freeCoordinateLeftMap
    (C ι : Type*) [Field C] :
    FreeCoordinateRationalField C ι →ₐ[C]
      FreeCoordinateRationalField C (ι ⊕ ι) :=
  mvFractionRename Sum.inl Sum.inl_injective

/-- Right pure-packet embedding `F(Y)`. -/
def freeCoordinateRightMap
    (C ι : Type*) [Field C] :
    FreeCoordinateRationalField C ι →ₐ[C]
      FreeCoordinateRationalField C (ι ⊕ ι) :=
  mvFractionRename Sum.inr Sum.inr_injective

@[simp]
theorem freeCoordinateLeftMap_algebraMap
    {C ι : Type*} [Field C] (p : MvPolynomial ι C) :
    freeCoordinateLeftMap C ι
        (algebraMap (MvPolynomial ι C) (FreeCoordinateRationalField C ι) p) =
      algebraMap (MvPolynomial (ι ⊕ ι) C)
        (FreeCoordinateRationalField C (ι ⊕ ι))
          (MvPolynomial.rename (Sum.inl : ι → ι ⊕ ι) p) := by
  simp [freeCoordinateLeftMap, mvFractionRename_algebraMap]

@[simp]
theorem freeCoordinateRightMap_algebraMap
    {C ι : Type*} [Field C] (p : MvPolynomial ι C) :
    freeCoordinateRightMap C ι
        (algebraMap (MvPolynomial ι C) (FreeCoordinateRationalField C ι) p) =
      algebraMap (MvPolynomial (ι ⊕ ι) C)
        (FreeCoordinateRationalField C (ι ⊕ ι))
          (MvPolynomial.rename (Sum.inr : ι → ι ⊕ ι) p) := by
  simp [freeCoordinateRightMap, mvFractionRename_algebraMap]

@[simp]
theorem freeCoordinateAddMap_freeCoordinate
    {C ι : Type*} [Field C] (i : ι) :
    freeCoordinateAddMap C ι (freeCoordinate C ι i) =
      freeCoordinate C (ι ⊕ ι) (Sum.inl i) +
        freeCoordinate C (ι ⊕ ι) (Sum.inr i) := by
  simp [freeCoordinate, freeCoordinateAddPolynomialMap]

@[simp]
theorem freeCoordinateLeftMap_freeCoordinate
    {C ι : Type*} [Field C] (i : ι) :
    freeCoordinateLeftMap C ι (freeCoordinate C ι i) =
      freeCoordinate C (ι ⊕ ι) (Sum.inl i) := by
  simp [freeCoordinateLeftMap, freeCoordinate, mvFractionRename_algebraMap]

@[simp]
theorem freeCoordinateRightMap_freeCoordinate
    {C ι : Type*} [Field C] (i : ι) :
    freeCoordinateRightMap C ι (freeCoordinate C ι i) =
      freeCoordinate C (ι ⊕ ι) (Sum.inr i) := by
  simp [freeCoordinateRightMap, freeCoordinate, mvFractionRename_algebraMap]

/-- A derivation commutes with a fraction-field map once it commutes on the source domain. -/
theorem fractionRingAlgHom_derivation_commutes
    {C A K E : Type*} [CommRing C] [CommRing A] [IsDomain A]
    [Field K] [Field E] [Algebra C A] [Algebra A K] [Algebra C K]
    [IsScalarTower C A K] [IsFractionRing A K] [Algebra C E]
    (φ : K →ₐ[C] E) (DK : Derivation C K K) (DE : Derivation C E E)
    (hsource : ∀ a : A,
      DE (φ (algebraMap A K a)) = φ (DK (algebraMap A K a)))
    (z : K) : DE (φ z) = φ (DK z) := by
  obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors A) z
  have hE := congrArg DE (congrArg φ hz)
  have hK := congrArg φ (congrArg DK hz)
  simp only [map_add, map_mul, Derivation.leibniz, smul_eq_mul] at hE hK
  rw [hsource a, hsource s.1] at hE
  have hsK : algebraMap A K s.1 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hsE : φ (algebraMap A K s.1) ≠ 0 := by
    exact (map_ne_zero φ).2 hsK
  have hd : φ (algebraMap A K s.1) * (DE (φ z) - φ (DK z)) = 0 := by
    calc
      φ (algebraMap A K s.1) * (DE (φ z) - φ (DK z)) =
          (φ z * φ (DK (algebraMap A K s.1)) +
              φ (algebraMap A K s.1) * DE (φ z)) -
            (φ z * φ (DK (algebraMap A K s.1)) +
              φ (algebraMap A K s.1) * φ (DK z)) := by ring
      _ = φ (DK (algebraMap A K a)) - φ (DK (algebraMap A K a)) := by
        rw [hE, hK]
      _ = 0 := sub_self _
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hsE)

theorem freeCoordinateDerivation_addMap_left
    {C ι : Type*} [Field C] (i : ι) (z : FreeCoordinateRationalField C ι) :
    freeCoordinateDerivation C (ι ⊕ ι) (Sum.inl i) (freeCoordinateAddMap C ι z) =
      freeCoordinateAddMap C ι (freeCoordinateDerivation C ι i z) := by
  apply fractionRingAlgHom_derivation_commutes
    (A := MvPolynomial ι C) (freeCoordinateAddMap C ι)
      (freeCoordinateDerivation C ι i)
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inl i))
  intro p
  simp only [freeCoordinateAddMap_algebraMap, freeCoordinateDerivation_algebraMap]
  rw [pderiv_freeCoordinateAddPolynomialMap_left]

theorem freeCoordinateDerivation_addMap_right
    {C ι : Type*} [Field C] (i : ι) (z : FreeCoordinateRationalField C ι) :
    freeCoordinateDerivation C (ι ⊕ ι) (Sum.inr i) (freeCoordinateAddMap C ι z) =
      freeCoordinateAddMap C ι (freeCoordinateDerivation C ι i z) := by
  apply fractionRingAlgHom_derivation_commutes
    (A := MvPolynomial ι C) (freeCoordinateAddMap C ι)
      (freeCoordinateDerivation C ι i)
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inr i))
  intro p
  simp only [freeCoordinateAddMap_algebraMap, freeCoordinateDerivation_algebraMap]
  rw [pderiv_freeCoordinateAddPolynomialMap_right]

theorem freeCoordinateDerivation_leftMap_left
    {C ι : Type*} [Field C] (i : ι) (z : FreeCoordinateRationalField C ι) :
    freeCoordinateDerivation C (ι ⊕ ι) (Sum.inl i) (freeCoordinateLeftMap C ι z) =
      freeCoordinateLeftMap C ι (freeCoordinateDerivation C ι i z) := by
  apply fractionRingAlgHom_derivation_commutes
    (A := MvPolynomial ι C) (freeCoordinateLeftMap C ι)
      (freeCoordinateDerivation C ι i)
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inl i))
  intro p
  simp only [freeCoordinateLeftMap_algebraMap, freeCoordinateDerivation_algebraMap]
  rw [pderiv_rename_inl]

theorem freeCoordinateDerivation_rightMap_right
    {C ι : Type*} [Field C] (i : ι) (z : FreeCoordinateRationalField C ι) :
    freeCoordinateDerivation C (ι ⊕ ι) (Sum.inr i) (freeCoordinateRightMap C ι z) =
      freeCoordinateRightMap C ι (freeCoordinateDerivation C ι i z) := by
  apply fractionRingAlgHom_derivation_commutes
    (A := MvPolynomial ι C) (freeCoordinateRightMap C ι)
      (freeCoordinateDerivation C ι i)
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inr i))
  intro p
  simp only [freeCoordinateRightMap_algebraMap, freeCoordinateDerivation_algebraMap]
  rw [pderiv_rename_inr]

theorem freeCoordinateDerivation_leftMap_cross
    {C ι : Type*} [Field C] (i : ι) (z : FreeCoordinateRationalField C ι) :
    freeCoordinateDerivation C (ι ⊕ ι) (Sum.inr i) (freeCoordinateLeftMap C ι z) = 0 := by
  simpa using fractionRingAlgHom_derivation_commutes
    (A := MvPolynomial ι C) (freeCoordinateLeftMap C ι)
      (0 : Derivation C (FreeCoordinateRationalField C ι)
        (FreeCoordinateRationalField C ι))
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inr i))
      (by
        intro p
        simp only [freeCoordinateLeftMap_algebraMap,
          freeCoordinateDerivation_algebraMap, Derivation.zero_apply, map_zero]
        rw [pderiv_rename_inl_cross, map_zero]) z

theorem freeCoordinateDerivation_rightMap_cross
    {C ι : Type*} [Field C] (i : ι) (z : FreeCoordinateRationalField C ι) :
    freeCoordinateDerivation C (ι ⊕ ι) (Sum.inl i) (freeCoordinateRightMap C ι z) = 0 := by
  simpa using fractionRingAlgHom_derivation_commutes
    (A := MvPolynomial ι C) (freeCoordinateRightMap C ι)
      (0 : Derivation C (FreeCoordinateRationalField C ι)
        (FreeCoordinateRationalField C ι))
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inl i))
      (by
        intro p
        simp only [freeCoordinateRightMap_algebraMap,
          freeCoordinateDerivation_algebraMap, Derivation.zero_apply, map_zero]
        rw [pderiv_rename_inr_cross, map_zero]) z

/-- Linear rational forms on a finite free coordinate family. -/
def freeCoordinateLinearForm
    (C ι : Type*) [Field C] [Fintype ι] (c : ι → C) :
    FreeCoordinateRationalField C ι :=
  ∑ i, algebraMap C (FreeCoordinateRationalField C ι) (c i) * freeCoordinate C ι i

@[simp]
theorem freeCoordinateDerivation_linearForm
    {C ι : Type*} [Field C] [Fintype ι] (c : ι → C) (i : ι) :
    freeCoordinateDerivation C ι i (freeCoordinateLinearForm C ι c) =
      algebraMap C (FreeCoordinateRationalField C ι) (c i) := by
  classical
  simp only [freeCoordinateLinearForm, map_sum, Derivation.leibniz,
    Derivation.map_algebraMap, smul_eq_mul, mul_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · rw [freeCoordinateDerivation_freeCoordinate_self, mul_one]
  · intro j hj hji
    rw [freeCoordinateDerivation_freeCoordinate_of_ne hji, mul_zero]
  · simp

theorem freeCoordinateLinearForm_additive
    {C ι : Type*} [Field C] [Fintype ι] (c : ι → C) :
    freeCoordinateAddMap C ι (freeCoordinateLinearForm C ι c) =
      freeCoordinateLeftMap C ι (freeCoordinateLinearForm C ι c) +
        freeCoordinateRightMap C ι (freeCoordinateLinearForm C ι c) := by
  classical
  simp only [freeCoordinateLinearForm, map_sum, map_mul, AlgHom.commutes,
    freeCoordinateAddMap_freeCoordinate, freeCoordinateLeftMap_freeCoordinate,
    freeCoordinateRightMap_freeCoordinate]
  calc
    ∑ i, algebraMap C (FreeCoordinateRationalField C (ι ⊕ ι)) (c i) *
          (freeCoordinate C (ι ⊕ ι) (Sum.inl i) +
            freeCoordinate C (ι ⊕ ι) (Sum.inr i)) =
        ∑ i, (algebraMap C (FreeCoordinateRationalField C (ι ⊕ ι)) (c i) *
            freeCoordinate C (ι ⊕ ι) (Sum.inl i) +
          algebraMap C (FreeCoordinateRationalField C (ι ⊕ ι)) (c i) *
            freeCoordinate C (ι ⊕ ι) (Sum.inr i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := Finset.sum_add_distrib

/-- Every rational solution of the additive Cauchy equation on a finite free coordinate family
is a unique linear form. -/
theorem freeCoordinate_rational_additive_eq_linear
    {C ι : Type*} [Field C] [CharZero C] [Fintype ι]
    (F : FreeCoordinateRationalField C ι)
    (hadd : freeCoordinateAddMap C ι F =
      freeCoordinateLeftMap C ι F + freeCoordinateRightMap C ι F) :
    ∃! c : ι → C, F = freeCoordinateLinearForm C ι c := by
  classical
  have hfirst (j : ι) :
      freeCoordinateAddMap C ι (freeCoordinateDerivation C ι j F) =
        freeCoordinateRightMap C ι (freeCoordinateDerivation C ι j F) := by
    have h := congrArg
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inr j)) hadd
    simpa only [freeCoordinateDerivation_addMap_right, map_add,
      freeCoordinateDerivation_leftMap_cross,
      freeCoordinateDerivation_rightMap_right, zero_add] using h
  have hsecond (i j : ι) :
      freeCoordinateDerivation C ι i (freeCoordinateDerivation C ι j F) = 0 := by
    have h := congrArg
      (freeCoordinateDerivation C (ι ⊕ ι) (Sum.inl i)) (hfirst j)
    have hz : freeCoordinateAddMap C ι
        (freeCoordinateDerivation C ι i (freeCoordinateDerivation C ι j F)) = 0 := by
      simpa only [freeCoordinateDerivation_addMap_left,
        freeCoordinateDerivation_rightMap_cross] using h
    exact (map_eq_zero (freeCoordinateAddMap C ι)).mp hz
  have hconstant (j : ι) : ∃ c : C,
      freeCoordinateDerivation C ι j F =
        algebraMap C (FreeCoordinateRationalField C ι) c :=
    (all_freeCoordinateDerivations_eq_zero_iff
      (freeCoordinateDerivation C ι j F)).1 (fun i => hsecond i j)
  choose c hc using hconstant
  have hresidual : ∀ i : ι,
      freeCoordinateDerivation C ι i (F - freeCoordinateLinearForm C ι c) = 0 := by
    intro i
    simp only [map_sub, freeCoordinateDerivation_linearForm, hc i, sub_self]
  obtain ⟨a, ha⟩ :=
    (all_freeCoordinateDerivations_eq_zero_iff
      (F - freeCoordinateLinearForm C ι c)).1 hresidual
  have hF : F = freeCoordinateLinearForm C ι c +
      algebraMap C (FreeCoordinateRationalField C ι) a := by
    calc
      F = (F - freeCoordinateLinearForm C ι c) +
          freeCoordinateLinearForm C ι c := by ring
      _ = algebraMap C (FreeCoordinateRationalField C ι) a +
          freeCoordinateLinearForm C ι c := by rw [ha]
      _ = _ := by ring
  have haTarget :
      algebraMap C (FreeCoordinateRationalField C (ι ⊕ ι)) a = 0 := by
    have h := hadd
    rw [hF] at h
    simp only [map_add, AlgHom.commutes] at h
    rw [freeCoordinateLinearForm_additive] at h
    linear_combination -h
  have ha0 : a = 0 := by
    apply (algebraMap C (FreeCoordinateRationalField C (ι ⊕ ι))).injective
    simpa using haTarget
  have hlinear : F = freeCoordinateLinearForm C ι c := by
    simpa [ha0] using hF
  refine ⟨c, hlinear, ?_⟩
  intro d hd
  funext i
  apply (algebraMap C (FreeCoordinateRationalField C ι)).injective
  calc
    algebraMap C (FreeCoordinateRationalField C ι) (d i) =
        freeCoordinateDerivation C ι i (freeCoordinateLinearForm C ι d) := by
      rw [freeCoordinateDerivation_linearForm]
    _ = freeCoordinateDerivation C ι i F := by rw [hd]
    _ = freeCoordinateDerivation C ι i (freeCoordinateLinearForm C ι c) := by
      rw [hlinear]
    _ = algebraMap C (FreeCoordinateRationalField C ι) (c i) :=
      freeCoordinateDerivation_linearForm c i

/-- Evaluation of a free rational coordinate field at an algebraically independent family.
Algebraic independence is exactly the denominator-legality condition. -/
def freeCoordinateEvalMap
    {C E ι : Type*} [Field C] [Field E] [Algebra C E]
    (g : ι → E) (hg : AlgebraicIndependent C g) :
    FreeCoordinateRationalField C ι →ₐ[C] E :=
  IsFractionRing.liftAlgHom (g := MvPolynomial.aeval g)
    (algebraicIndependent_iff_injective_aeval.mp hg)

@[simp]
theorem freeCoordinateEvalMap_algebraMap
    {C E ι : Type*} [Field C] [Field E] [Algebra C E]
    (g : ι → E) (hg : AlgebraicIndependent C g) (p : MvPolynomial ι C) :
    freeCoordinateEvalMap g hg
        (algebraMap (MvPolynomial ι C) (FreeCoordinateRationalField C ι) p) =
      MvPolynomial.aeval g p := by
  simp [freeCoordinateEvalMap, IsFractionRing.liftAlgHom_apply,
    IsFractionRing.lift_algebraMap]

@[simp]
theorem freeCoordinateEvalMap_freeCoordinate
    {C E ι : Type*} [Field C] [Field E] [Algebra C E]
    (g : ι → E) (hg : AlgebraicIndependent C g) (i : ι) :
    freeCoordinateEvalMap g hg (freeCoordinate C ι i) = g i := by
  simp [freeCoordinate]

/-- Finite-form form of the abstract two-packet primitive theorem.  The three commuting diagrams
are the exact rational extensions supplied by two-packet algebraic freeness. -/
theorem twoPacketRationalFormation_eq_linear
    {C ι L E : Type*} [Field C] [CharZero C] [Fintype ι]
    [Field L] [Field E] [Algebra C L] [Algebra C E]
    (sourceEval : FreeCoordinateRationalField C ι →ₐ[C] L)
    (packetEval : FreeCoordinateRationalField C (ι ⊕ ι) →ₐ[C] E)
    (r₀ r₁ r₀₁ : L →ₐ[C] E)
    (F : FreeCoordinateRationalField C ι)
    (hpacket : r₀₁ (sourceEval F) = r₀ (sourceEval F) + r₁ (sourceEval F))
    (h₀₁ : packetEval.comp (freeCoordinateAddMap C ι) = r₀₁.comp sourceEval)
    (h₀ : packetEval.comp (freeCoordinateLeftMap C ι) = r₀.comp sourceEval)
    (h₁ : packetEval.comp (freeCoordinateRightMap C ι) = r₁.comp sourceEval) :
    ∃! c : ι → C, F = freeCoordinateLinearForm C ι c := by
  have hformal : freeCoordinateAddMap C ι F =
      freeCoordinateLeftMap C ι F + freeCoordinateRightMap C ι F := by
    apply packetEval.injective
    calc
      packetEval (freeCoordinateAddMap C ι F) = r₀₁ (sourceEval F) :=
        DFunLike.congr_fun h₀₁ F
      _ = r₀ (sourceEval F) + r₁ (sourceEval F) := hpacket
      _ = packetEval (freeCoordinateLeftMap C ι F) +
          packetEval (freeCoordinateRightMap C ι F) := by
        have h₀F : packetEval (freeCoordinateLeftMap C ι F) = r₀ (sourceEval F) := by
          exact DFunLike.congr_fun h₀ F
        have h₁F : packetEval (freeCoordinateRightMap C ι F) = r₁ (sourceEval F) := by
          exact DFunLike.congr_fun h₁ F
        rw [h₀F, h₁F]
      _ = packetEval
          (freeCoordinateLeftMap C ι F + freeCoordinateRightMap C ι F) := by
        rw [map_add]
  exact freeCoordinate_rational_additive_eq_linear F hformal

/-- Image form: a packet-additive finite rational formation is a unique source-evaluated linear
form. -/
theorem twoPacketRationalFormation_image_eq_linear
    {C ι L E : Type*} [Field C] [CharZero C] [Fintype ι]
    [Field L] [Field E] [Algebra C L] [Algebra C E]
    (sourceEval : FreeCoordinateRationalField C ι →ₐ[C] L)
    (packetEval : FreeCoordinateRationalField C (ι ⊕ ι) →ₐ[C] E)
    (r₀ r₁ r₀₁ : L →ₐ[C] E)
    (F : FreeCoordinateRationalField C ι)
    (hpacket : r₀₁ (sourceEval F) = r₀ (sourceEval F) + r₁ (sourceEval F))
    (h₀₁ : packetEval.comp (freeCoordinateAddMap C ι) = r₀₁.comp sourceEval)
    (h₀ : packetEval.comp (freeCoordinateLeftMap C ι) = r₀.comp sourceEval)
    (h₁ : packetEval.comp (freeCoordinateRightMap C ι) = r₁.comp sourceEval) :
    ∃! c : ι → C,
      sourceEval F = sourceEval (freeCoordinateLinearForm C ι c) := by
  obtain ⟨c, hc, hunique⟩ := twoPacketRationalFormation_eq_linear
    sourceEval packetEval r₀ r₁ r₀₁ F hpacket h₀₁ h₀ h₁
  refine ⟨c, congrArg sourceEval hc, ?_⟩
  intro d hd
  apply hunique d
  apply sourceEval.injective
  exact hd

end

end GaloisForLFunctions.HTGeometry
