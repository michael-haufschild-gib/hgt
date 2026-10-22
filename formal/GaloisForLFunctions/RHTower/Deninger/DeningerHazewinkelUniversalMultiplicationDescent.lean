import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelReducedMultiplication

/-!
# Universal descent for corrected Hazewinkel multiplication

This file constructs the literal two-input universal coordinate ring and its
Hazewinkel pair quotient.  It proves that reducedness of this one universal
quotient implies the corrected product-minor ideal containment, and then
evaluates that containment into every commutative target ring, including rings
with nilpotents.

Thus arbitrary-target descent is complete.  Remaining global input is the
concrete reducedness theorem for `DeningerHazewinkelPairQuotient n m`.
-/

namespace RHTower
noncomputable section

abbrev DeningerHazewinkelCoordinateRing := MvPolynomial ℕ ℤ
abbrev DeningerHazewinkelPairCoordinateRing := MvPolynomial (Bool × ℕ) ℤ

def deningerHazewinkelPairLeft :
    DeningerHazewinkelCoordinateRing →+* DeningerHazewinkelPairCoordinateRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => MvPolynomial.X (false, j))

def deningerHazewinkelPairRight :
    DeningerHazewinkelCoordinateRing →+* DeningerHazewinkelPairCoordinateRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => MvPolynomial.X (true, j))

def deningerHazewinkelPairIdeal (n m : ℕ) :
    Ideal DeningerHazewinkelPairCoordinateRing :=
  Ideal.map deningerHazewinkelPairLeft (deningerHazewinkelIdeal n) ⊔
    Ideal.map deningerHazewinkelPairRight (deningerHazewinkelIdeal m)

abbrev DeningerHazewinkelPairQuotient (n m : ℕ) :=
  DeningerHazewinkelPairCoordinateRing ⧸ deningerHazewinkelPairIdeal n m

def deningerHazewinkelUniversalWitt :
    DeningerBigWittAdditive DeningerHazewinkelCoordinateRing :=
  deningerBigWittOfSeries
    (PowerSeries.mk deningerHazewinkelUniversalCoeff) (by
      change deningerHazewinkelUniversalCoeff 0 = 1
      rfl)

@[simp] theorem deningerHazewinkelUniversalWitt_hankel :
    deningerBigWittHankel deningerHazewinkelUniversalWitt =
      deningerHazewinkelUniversalHankel := by
  funext i j
  simp [deningerBigWittHankel, deningerHazewinkelUniversalWitt,
    deningerHazewinkelUniversalHankel]

theorem deningerHazewinkelUniversalWitt_map_rankLT
    {A : Type*} [CommRing A] (n : ℕ)
    (f : DeningerHazewinkelCoordinateRing →+* A)
    (hf : deningerHazewinkelIdeal n ≤ RingHom.ker f) :
    DeningerBigWittHankelRankLT (n + 1)
      (deningerBigWittMap f deningerHazewinkelUniversalWitt) := by
  intro rows cols
  have hmem :
      (deningerHazewinkelUniversalHankel.submatrix rows cols).det ∈
        deningerHazewinkelIdeal n :=
    deningerMatrixMinorDet_mem (n + 1) deningerHazewinkelUniversalHankel rows cols
  have hzero := RingHom.mem_ker.mp (hf hmem)
  rw [f.map_det] at hzero
  have heq : f.mapMatrix
        (deningerHazewinkelUniversalHankel.submatrix rows cols) =
      (deningerBigWittHankel
        (deningerBigWittMap f deningerHazewinkelUniversalWitt)).submatrix rows cols := by
    ext i j
    simp only [Matrix.submatrix_apply, deningerBigWittHankel_map,
      deningerHazewinkelUniversalWitt_hankel]
    rfl
  rwa [heq] at hzero

def deningerHazewinkelPairLeftQuotient (n m : ℕ) :
    DeningerHazewinkelCoordinateRing →+* DeningerHazewinkelPairQuotient n m :=
  (Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m)).comp
    deningerHazewinkelPairLeft

def deningerHazewinkelPairRightQuotient (n m : ℕ) :
    DeningerHazewinkelCoordinateRing →+* DeningerHazewinkelPairQuotient n m :=
  (Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m)).comp
    deningerHazewinkelPairRight

theorem deningerHazewinkelPairLeftQuotient_ker (n m : ℕ) :
    deningerHazewinkelIdeal n ≤ RingHom.ker
      (deningerHazewinkelPairLeftQuotient n m) := by
  intro p hp
  apply RingHom.mem_ker.mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (le_sup_left : Ideal.map deningerHazewinkelPairLeft
    (deningerHazewinkelIdeal n) ≤ deningerHazewinkelPairIdeal n m)
      (Ideal.mem_map_of_mem deningerHazewinkelPairLeft hp)

theorem deningerHazewinkelPairRightQuotient_ker (n m : ℕ) :
    deningerHazewinkelIdeal m ≤ RingHom.ker
      (deningerHazewinkelPairRightQuotient n m) := by
  intro p hp
  apply RingHom.mem_ker.mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (le_sup_right : Ideal.map deningerHazewinkelPairRight
    (deningerHazewinkelIdeal m) ≤ deningerHazewinkelPairIdeal n m)
      (Ideal.mem_map_of_mem deningerHazewinkelPairRight hp)

def deningerHazewinkelPairUniversalLeft (n m : ℕ) :
    DeningerBigWittAdditive (DeningerHazewinkelPairQuotient n m) :=
  deningerBigWittMap (deningerHazewinkelPairLeftQuotient n m)
    deningerHazewinkelUniversalWitt

def deningerHazewinkelPairUniversalRight (n m : ℕ) :
    DeningerBigWittAdditive (DeningerHazewinkelPairQuotient n m) :=
  deningerBigWittMap (deningerHazewinkelPairRightQuotient n m)
    deningerHazewinkelUniversalWitt

theorem deningerHazewinkelPairUniversalLeft_rankLT (n m : ℕ) :
    DeningerBigWittHankelRankLT (n + 1)
      (deningerHazewinkelPairUniversalLeft n m) :=
  deningerHazewinkelUniversalWitt_map_rankLT n _
    (deningerHazewinkelPairLeftQuotient_ker n m)

theorem deningerHazewinkelPairUniversalRight_rankLT (n m : ℕ) :
    DeningerBigWittHankelRankLT (m + 1)
      (deningerHazewinkelPairUniversalRight n m) :=
  deningerHazewinkelUniversalWitt_map_rankLT m _
    (deningerHazewinkelPairRightQuotient_ker n m)

def deningerHazewinkelPairRawLeft :
    DeningerBigWittAdditive DeningerHazewinkelPairCoordinateRing :=
  deningerBigWittMap deningerHazewinkelPairLeft deningerHazewinkelUniversalWitt

def deningerHazewinkelPairRawRight :
    DeningerBigWittAdditive DeningerHazewinkelPairCoordinateRing :=
  deningerBigWittMap deningerHazewinkelPairRight deningerHazewinkelUniversalWitt

def deningerHazewinkelPairProductMinorIdeal (n m : ℕ) :
    Ideal DeningerHazewinkelPairCoordinateRing :=
  deningerMatrixMinorIdeal
    (deningerCorrectedWittMulStageBound n m + 1)
    (deningerBigWittHankel
      (deningerBigWittMul deningerHazewinkelPairRawLeft
        deningerHazewinkelPairRawRight))

theorem deningerHazewinkelPairRawLeft_map_quotient (n m : ℕ) :
    deningerBigWittMap (Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m))
        deningerHazewinkelPairRawLeft =
      deningerHazewinkelPairUniversalLeft n m := by
  rw [deningerHazewinkelPairRawLeft, deningerHazewinkelPairUniversalLeft,
    ← deningerBigWittMap_comp]
  rfl

theorem deningerHazewinkelPairRawRight_map_quotient (n m : ℕ) :
    deningerBigWittMap (Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m))
        deningerHazewinkelPairRawRight =
      deningerHazewinkelPairUniversalRight n m := by
  rw [deningerHazewinkelPairRawRight, deningerHazewinkelPairUniversalRight,
    ← deningerBigWittMap_comp]
  rfl

/-- Reducedness of the universal pair quotient forces the corrected
comultiplication ideal containment. -/
theorem deningerHazewinkelPairProductMinorIdeal_le_of_isReduced
    (n m : ℕ) [IsReduced (DeningerHazewinkelPairQuotient n m)] :
    deningerHazewinkelPairProductMinorIdeal n m ≤
      deningerHazewinkelPairIdeal n m := by
  let q := Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m)
  have hproduct : DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMap q
        (deningerBigWittMul deningerHazewinkelPairRawLeft
          deningerHazewinkelPairRawRight)) := by
    rw [deningerBigWittMul_natural,
      deningerHazewinkelPairRawLeft_map_quotient,
      deningerHazewinkelPairRawRight_map_quotient]
    exact deningerReduced_hankelRankLT_mul_corrected
      (deningerHazewinkelPairUniversalLeft_rankLT n m)
      (deningerHazewinkelPairUniversalRight_rankLT n m)
  have h := deningerBigWittMinorIdeal_le_ker_of_rankLT_map q
    (deningerCorrectedWittMulStageBound n m + 1)
    (deningerBigWittMul deningerHazewinkelPairRawLeft
      deningerHazewinkelPairRawRight) hproduct
  simpa [deningerHazewinkelPairProductMinorIdeal, q, Ideal.mk_ker] using h

/-- Evaluation of the two universal coefficient blocks at an arbitrary pair
of big Witt vectors. -/
def deningerHazewinkelPairEval
    {A : Type*} [CommRing A]
    (u v : DeningerBigWittAdditive A) :
    DeningerHazewinkelPairCoordinateRing →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) fun x =>
    if x.1 then PowerSeries.coeff (x.2 + 1) (deningerBigWittSeries v)
    else PowerSeries.coeff (x.2 + 1) (deningerBigWittSeries u)

@[simp] theorem deningerHazewinkelPairEval_left_coeff
    {A : Type*} [CommRing A]
    (u v : DeningerBigWittAdditive A) (s : ℕ) :
    deningerHazewinkelPairEval u v
        (deningerHazewinkelPairLeft (deningerHazewinkelUniversalCoeff s)) =
      PowerSeries.coeff s (deningerBigWittSeries u) := by
  cases s with
  | zero =>
      simp [deningerHazewinkelUniversalCoeff, deningerHazewinkelPairLeft,
        deningerHazewinkelPairEval, PowerSeries.coeff_zero_eq_constantCoeff,
        deningerBigWittSeries_constantCoeff]
  | succ s =>
      simp [deningerHazewinkelUniversalCoeff, deningerHazewinkelPairLeft,
        deningerHazewinkelPairEval]

@[simp] theorem deningerHazewinkelPairEval_right_coeff
    {A : Type*} [CommRing A]
    (u v : DeningerBigWittAdditive A) (s : ℕ) :
    deningerHazewinkelPairEval u v
        (deningerHazewinkelPairRight (deningerHazewinkelUniversalCoeff s)) =
      PowerSeries.coeff s (deningerBigWittSeries v) := by
  cases s with
  | zero =>
      simp [deningerHazewinkelUniversalCoeff, deningerHazewinkelPairRight,
        deningerHazewinkelPairEval, PowerSeries.coeff_zero_eq_constantCoeff,
        deningerBigWittSeries_constantCoeff]
  | succ s =>
      simp [deningerHazewinkelUniversalCoeff, deningerHazewinkelPairRight,
        deningerHazewinkelPairEval]

theorem deningerHazewinkelPairEval_rawLeft
    {A : Type*} [CommRing A]
    (u v : DeningerBigWittAdditive A) :
    deningerBigWittMap (deningerHazewinkelPairEval u v)
        deningerHazewinkelPairRawLeft = u := by
  rw [deningerHazewinkelPairRawLeft]
  calc
    deningerBigWittMap (deningerHazewinkelPairEval u v)
        (deningerBigWittMap deningerHazewinkelPairLeft
          deningerHazewinkelUniversalWitt) =
      deningerBigWittMap
        ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairLeft)
        deningerHazewinkelUniversalWitt :=
      (deningerBigWittMap_comp _ _ _).symm
    _ = u := by
      apply Subtype.ext
      apply Units.ext
      apply PowerSeries.ext
      intro s
      change PowerSeries.coeff s
          (deningerBigWittSeries
            (deningerBigWittMap
              ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairLeft)
              deningerHazewinkelUniversalWitt)) =
        PowerSeries.coeff s (deningerBigWittSeries u)
      rw [deningerBigWittSeries_map, PowerSeries.coeff_map]
      rw [show PowerSeries.coeff s
          (deningerBigWittSeries deningerHazewinkelUniversalWitt) =
            deningerHazewinkelUniversalCoeff s by
        simp [deningerHazewinkelUniversalWitt]]
      change deningerHazewinkelPairEval u v
          (deningerHazewinkelPairLeft (deningerHazewinkelUniversalCoeff s)) =
        PowerSeries.coeff s (deningerBigWittSeries u)
      exact deningerHazewinkelPairEval_left_coeff u v s

theorem deningerHazewinkelPairEval_rawRight
    {A : Type*} [CommRing A]
    (u v : DeningerBigWittAdditive A) :
    deningerBigWittMap (deningerHazewinkelPairEval u v)
        deningerHazewinkelPairRawRight = v := by
  rw [deningerHazewinkelPairRawRight]
  calc
    deningerBigWittMap (deningerHazewinkelPairEval u v)
        (deningerBigWittMap deningerHazewinkelPairRight
          deningerHazewinkelUniversalWitt) =
      deningerBigWittMap
        ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairRight)
        deningerHazewinkelUniversalWitt :=
      (deningerBigWittMap_comp _ _ _).symm
    _ = v := by
      apply Subtype.ext
      apply Units.ext
      apply PowerSeries.ext
      intro s
      change PowerSeries.coeff s
          (deningerBigWittSeries
            (deningerBigWittMap
              ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairRight)
              deningerHazewinkelUniversalWitt)) =
        PowerSeries.coeff s (deningerBigWittSeries v)
      rw [deningerBigWittSeries_map, PowerSeries.coeff_map]
      rw [show PowerSeries.coeff s
          (deningerBigWittSeries deningerHazewinkelUniversalWitt) =
            deningerHazewinkelUniversalCoeff s by
        simp [deningerHazewinkelUniversalWitt]]
      change deningerHazewinkelPairEval u v
          (deningerHazewinkelPairRight (deningerHazewinkelUniversalCoeff s)) =
        PowerSeries.coeff s (deningerBigWittSeries v)
      exact deningerHazewinkelPairEval_right_coeff u v s

theorem DeningerBigWittHankelRankLT.map_of_minorIdeal_le_ker
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (d : ℕ) (w : DeningerBigWittAdditive A)
    (h : deningerMatrixMinorIdeal d (deningerBigWittHankel w) ≤
      RingHom.ker f) :
    DeningerBigWittHankelRankLT d (deningerBigWittMap f w) := by
  intro rows cols
  have hmem := deningerMatrixMinorDet_mem d (deningerBigWittHankel w) rows cols
  have hzero := RingHom.mem_ker.mp (h hmem)
  rw [f.map_det] at hzero
  have heq : f.mapMatrix ((deningerBigWittHankel w).submatrix rows cols) =
      (deningerBigWittHankel (deningerBigWittMap f w)).submatrix rows cols := by
    ext i j
    simp only [Matrix.submatrix_apply, deningerBigWittHankel_map]
    rfl
  rwa [heq] at hzero

/-- The input stage equations are exactly enough for the pair evaluation to
factor through the universal pair quotient. -/
theorem deningerHazewinkelPairIdeal_le_ker_eval
    {A : Type*} [CommRing A] {n m : ℕ}
    {u v : DeningerBigWittAdditive A}
    (hu : DeningerBigWittHankelRankLT (n + 1) u)
    (hv : DeningerBigWittHankelRankLT (m + 1) v) :
    deningerHazewinkelPairIdeal n m ≤
      RingHom.ker (deningerHazewinkelPairEval u v) := by
  have hmapLeft : deningerBigWittMap
      ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairLeft)
      deningerHazewinkelUniversalWitt = u := by
    rw [deningerBigWittMap_comp]
    exact deningerHazewinkelPairEval_rawLeft u v
  have hmapRight : deningerBigWittMap
      ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairRight)
      deningerHazewinkelUniversalWitt = v := by
    rw [deningerBigWittMap_comp]
    exact deningerHazewinkelPairEval_rawRight u v
  have hleft : deningerHazewinkelIdeal n ≤
      RingHom.ker ((deningerHazewinkelPairEval u v).comp
        deningerHazewinkelPairLeft) := by
    have hRankLeft : DeningerBigWittHankelRankLT (n + 1)
        (deningerBigWittMap
          ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairLeft)
          deningerHazewinkelUniversalWitt) := by
      rw [hmapLeft]
      exact hu
    have h := deningerBigWittMinorIdeal_le_ker_of_rankLT_map
      ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairLeft)
      (n + 1) deningerHazewinkelUniversalWitt hRankLeft
    simpa [deningerHazewinkelIdeal,
      deningerHazewinkelUniversalWitt_hankel] using h
  have hright : deningerHazewinkelIdeal m ≤
      RingHom.ker ((deningerHazewinkelPairEval u v).comp
        deningerHazewinkelPairRight) := by
    have hRankRight : DeningerBigWittHankelRankLT (m + 1)
        (deningerBigWittMap
          ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairRight)
          deningerHazewinkelUniversalWitt) := by
      rw [hmapRight]
      exact hv
    have h := deningerBigWittMinorIdeal_le_ker_of_rankLT_map
      ((deningerHazewinkelPairEval u v).comp deningerHazewinkelPairRight)
      (m + 1) deningerHazewinkelUniversalWitt hRankRight
    simpa [deningerHazewinkelIdeal,
      deningerHazewinkelUniversalWitt_hankel] using h
  rw [deningerHazewinkelPairIdeal, sup_le_iff]
  constructor
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change deningerHazewinkelPairEval u v (deningerHazewinkelPairLeft p) = 0
    exact RingHom.mem_ker.mp (hleft hp)
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change deningerHazewinkelPairEval u v (deningerHazewinkelPairRight p) = 0
    exact RingHom.mem_ker.mp (hright hp)

/-- Corrected multiplication over every target ring follows from reducedness
of the concrete universal pair quotient.  Nilpotents in the target are retained
by universal evaluation. -/
theorem deninger_hankelRankLT_mul_corrected_of_pairQuotient_isReduced
    {A : Type*} [CommRing A] {n m : ℕ}
    [IsReduced (DeningerHazewinkelPairQuotient n m)]
    {u v : DeningerBigWittAdditive A}
    (hu : DeningerBigWittHankelRankLT (n + 1) u)
    (hv : DeningerBigWittHankelRankLT (m + 1) v) :
    DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMul u v) := by
  let e := deningerHazewinkelPairEval u v
  let w := deningerBigWittMul deningerHazewinkelPairRawLeft
    deningerHazewinkelPairRawRight
  have hminor : deningerMatrixMinorIdeal
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittHankel w) ≤ RingHom.ker e :=
    (deningerHazewinkelPairProductMinorIdeal_le_of_isReduced n m).trans
      (deningerHazewinkelPairIdeal_le_ker_eval hu hv)
  have hmap := DeningerBigWittHankelRankLT.map_of_minorIdeal_le_ker
    e (deningerCorrectedWittMulStageBound n m + 1) w hminor
  change DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMap (deningerHazewinkelPairEval u v)
        (deningerBigWittMul deningerHazewinkelPairRawLeft
          deningerHazewinkelPairRawRight)) at hmap
  rw [deningerBigWittMul_natural,
    deningerHazewinkelPairEval_rawLeft,
    deningerHazewinkelPairEval_rawRight] at hmap
  exact hmap

end
end RHTower
