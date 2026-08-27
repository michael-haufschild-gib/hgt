import GaloisForLFunctions.HTGeometry.MilnorKTwoBruhatPairRightActions

/-!
# Choice-free commutation on Milnor's Bruhat-pair space

The adjacent-Weyl corrections are deterministic functions of their monomial quotients.  This
removes an otherwise uncontrolled central factor and proves every left/right generator
commutation in Milnor's Lemma 12.10 except the Weyl--Weyl case.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MilnorDiagonalExtension

variable {F : Type*} [Field F]

theorem fin4BruhatLeftQuotient_mul_right_upper
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4))
    (t : upperSteinbergSubgroup (F := F) (Fin 4)) :
    fin4BruhatLeftQuotient hij (A * fin4SteinbergElementary t.1) =
      fin4BruhatLeftQuotient hij A := by
  rw [fin4BruhatLeftQuotient, ← mul_assoc,
    fin4BruhatProjection_mul_right_upper _ t.1 t.2,
    fin4BruhatProjection_mul_right_upper A t.1 t.2,
    fin4BruhatLeftQuotient]

theorem fin4BruhatLeftQuotient_mul_right_diagonal
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4))
    (h : MilnorDiagonalExtension F 4) :
    fin4BruhatLeftQuotient hij (A * fin4DiagonalElementary h.diag) =
      fin4BruhatLeftQuotient hij A := by
  rw [fin4BruhatLeftQuotient, ← mul_assoc,
    fin4BruhatProjection_mul_diagonal,
    fin4BruhatProjection_mul_diagonal,
    fin4BruhatLeftQuotient]
  group

theorem fin4BruhatRightQuotient_mul_left_upper
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4))
    (t : upperSteinbergSubgroup (F := F) (Fin 4)) :
    fin4BruhatRightQuotient hij (fin4SteinbergElementary t.1 * A) =
      fin4BruhatRightQuotient hij A := by
  rw [fin4BruhatRightQuotient, mul_assoc,
    fin4BruhatProjection_mul_left_upper t.1 t.2,
    fin4BruhatProjection_mul_left_upper t.1 t.2,
    fin4BruhatRightQuotient]

theorem fin4BruhatRightQuotient_mul_left_diagonal
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4))
    (h : MilnorDiagonalExtension F 4) :
    fin4BruhatRightQuotient hij (fin4DiagonalElementary h.diag * A) =
      fin4BruhatRightQuotient hij A := by
  rw [fin4BruhatRightQuotient, mul_assoc,
    fin4BruhatProjection_diagonal_mul,
    fin4BruhatProjection_diagonal_mul,
    fin4BruhatRightQuotient]
  group

theorem fin4BruhatLeftLift_value_mul_right_upper
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A)
    (A : elementaryGroup F (Fin 4))
    (t : upperSteinbergSubgroup (F := F) (Fin 4)) :
    (fin4BruhatLeftLift hij htrans
      (A * fin4SteinbergElementary t.1)).value =
      (fin4BruhatLeftLift hij htrans A).value := by
  change fin4BruhatCanonicalLeftValue hij
      (fin4BruhatLeftQuotient hij (A * fin4SteinbergElementary t.1)) =
    fin4BruhatCanonicalLeftValue hij (fin4BruhatLeftQuotient hij A)
  rw [fin4BruhatLeftQuotient_mul_right_upper]

theorem fin4BruhatLeftLift_value_mul_right_diagonal
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A)
    (A : elementaryGroup F (Fin 4)) (h : MilnorDiagonalExtension F 4) :
    (fin4BruhatLeftLift hij htrans
      (A * fin4DiagonalElementary h.diag)).value =
      (fin4BruhatLeftLift hij htrans A).value := by
  change fin4BruhatCanonicalLeftValue hij
      (fin4BruhatLeftQuotient hij (A * fin4DiagonalElementary h.diag)) =
    fin4BruhatCanonicalLeftValue hij (fin4BruhatLeftQuotient hij A)
  rw [fin4BruhatLeftQuotient_mul_right_diagonal]

theorem fin4BruhatRightLift_value_mul_left_upper
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))
    (A : elementaryGroup F (Fin 4))
    (t : upperSteinbergSubgroup (F := F) (Fin 4)) :
    (fin4BruhatRightLift hij htrans
      (fin4SteinbergElementary t.1 * A)).value =
      (fin4BruhatRightLift hij htrans A).value := by
  change fin4BruhatCanonicalRightValue hij
      (fin4BruhatRightQuotient hij (fin4SteinbergElementary t.1 * A)) =
    fin4BruhatCanonicalRightValue hij (fin4BruhatRightQuotient hij A)
  rw [fin4BruhatRightQuotient_mul_left_upper]

theorem fin4BruhatRightLift_value_mul_left_diagonal
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))
    (A : elementaryGroup F (Fin 4)) (h : MilnorDiagonalExtension F 4) :
    (fin4BruhatRightLift hij htrans
      (fin4DiagonalElementary h.diag * A)).value =
      (fin4BruhatRightLift hij htrans A).value := by
  change fin4BruhatCanonicalRightValue hij
      (fin4BruhatRightQuotient hij (fin4DiagonalElementary h.diag * A)) =
    fin4BruhatCanonicalRightValue hij (fin4BruhatRightQuotient hij A)
  rw [fin4BruhatRightQuotient_mul_left_diagonal]

theorem fin4BruhatPair_diagonal_diagonal_commute
    (h k : MilnorDiagonalExtension F 4) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairDiagonalMap h (fin4BruhatPairDiagonalRightMap k x) =
      fin4BruhatPairDiagonalRightMap k (fin4BruhatPairDiagonalMap h x) := by
  apply Fin4BruhatPair.ext
  · change fin4DiagonalElementary h.diag *
        (x.matrix * fin4DiagonalElementary k.diag) =
      (fin4DiagonalElementary h.diag * x.matrix) *
        fin4DiagonalElementary k.diag
    group
  · change milnorWDiagonalIncl h * (x.lift * milnorWDiagonalIncl k) =
      (milnorWDiagonalIncl h * x.lift) * milnorWDiagonalIncl k
    group

theorem fin4BruhatPair_diagonal_upperRight_commute
    (h : MilnorDiagonalExtension F 4)
    (t : upperSteinbergSubgroup (F := F) (Fin 4))
    (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairDiagonalMap h (fin4BruhatPairUpperRightMap t x) =
      fin4BruhatPairUpperRightMap t (fin4BruhatPairDiagonalMap h x) := by
  apply Fin4BruhatPair.ext
  · change fin4DiagonalElementary h.diag *
        (x.matrix * fin4SteinbergElementary t.1) =
      (fin4DiagonalElementary h.diag * x.matrix) *
        fin4SteinbergElementary t.1
    group
  · rfl

theorem fin4BruhatPair_upper_diagonalRight_commute
    (t : upperSteinbergSubgroup (F := F) (Fin 4))
    (h : MilnorDiagonalExtension F 4)
    (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairUpperMap t (fin4BruhatPairDiagonalRightMap h x) =
      fin4BruhatPairDiagonalRightMap h (fin4BruhatPairUpperMap t x) := by
  apply Fin4BruhatPair.ext
  · change fin4SteinbergElementary t.1 *
        (x.matrix * fin4DiagonalElementary h.diag) =
      (fin4SteinbergElementary t.1 * x.matrix) *
        fin4DiagonalElementary h.diag
    group
  · rfl

theorem fin4BruhatPair_upper_upperRight_commute
    (t u : upperSteinbergSubgroup (F := F) (Fin 4))
    (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairUpperMap t (fin4BruhatPairUpperRightMap u x) =
      fin4BruhatPairUpperRightMap u (fin4BruhatPairUpperMap t x) := by
  apply Fin4BruhatPair.ext
  · change fin4SteinbergElementary t.1 *
        (x.matrix * fin4SteinbergElementary u.1) =
      (fin4SteinbergElementary t.1 * x.matrix) *
        fin4SteinbergElementary u.1
    group
  · rfl

theorem fin4BruhatPair_simpleWeyl_upperRight_commute
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A)
    (t : upperSteinbergSubgroup (F := F) (Fin 4))
    (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairSimpleWeylMap hij htrans (fin4BruhatPairUpperRightMap t x) =
      fin4BruhatPairUpperRightMap t (fin4BruhatPairSimpleWeylMap hij htrans x) := by
  apply Fin4BruhatPair.ext
  · change fin4SimpleWeylElementary hij 1 *
        (x.matrix * fin4SteinbergElementary t.1) =
      (fin4SimpleWeylElementary hij 1 * x.matrix) *
        fin4SteinbergElementary t.1
    group
  · change (fin4BruhatLeftLift hij htrans
        (x.matrix * fin4SteinbergElementary t.1)).value * x.lift =
      (fin4BruhatLeftLift hij htrans x.matrix).value * x.lift
    rw [fin4BruhatLeftLift_value_mul_right_upper]

theorem fin4BruhatPair_simpleWeyl_diagonalRight_commute
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A)
    (h : MilnorDiagonalExtension F 4) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairSimpleWeylMap hij htrans (fin4BruhatPairDiagonalRightMap h x) =
      fin4BruhatPairDiagonalRightMap h (fin4BruhatPairSimpleWeylMap hij htrans x) := by
  apply Fin4BruhatPair.ext
  · change fin4SimpleWeylElementary hij 1 *
        (x.matrix * fin4DiagonalElementary h.diag) =
      (fin4SimpleWeylElementary hij 1 * x.matrix) *
        fin4DiagonalElementary h.diag
    group
  · change (fin4BruhatLeftLift hij htrans
        (x.matrix * fin4DiagonalElementary h.diag)).value *
          (x.lift * milnorWDiagonalIncl h) =
      ((fin4BruhatLeftLift hij htrans x.matrix).value * x.lift) *
        milnorWDiagonalIncl h
    rw [fin4BruhatLeftLift_value_mul_right_diagonal]
    group

theorem fin4BruhatPair_upper_simpleWeylRight_commute
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))
    (t : upperSteinbergSubgroup (F := F) (Fin 4))
    (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairUpperMap t (fin4BruhatPairSimpleWeylRightMap hij htrans x) =
      fin4BruhatPairSimpleWeylRightMap hij htrans (fin4BruhatPairUpperMap t x) := by
  apply Fin4BruhatPair.ext
  · change fin4SteinbergElementary t.1 *
        (x.matrix * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
      (fin4SteinbergElementary t.1 * x.matrix) *
        fin4SimpleWeylElementary hij (-1 : Fˣ)
    group
  · change x.lift * (fin4BruhatRightLift hij htrans x.matrix).value =
      x.lift * (fin4BruhatRightLift hij htrans
        (fin4SteinbergElementary t.1 * x.matrix)).value
    rw [fin4BruhatRightLift_value_mul_left_upper]

theorem fin4BruhatPair_diagonal_simpleWeylRight_commute
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))
    (h : MilnorDiagonalExtension F 4) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairDiagonalMap h (fin4BruhatPairSimpleWeylRightMap hij htrans x) =
      fin4BruhatPairSimpleWeylRightMap hij htrans (fin4BruhatPairDiagonalMap h x) := by
  apply Fin4BruhatPair.ext
  · change fin4DiagonalElementary h.diag *
        (x.matrix * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
      (fin4DiagonalElementary h.diag * x.matrix) *
        fin4SimpleWeylElementary hij (-1 : Fˣ)
    group
  · change milnorWDiagonalIncl h *
        (x.lift * (fin4BruhatRightLift hij htrans x.matrix).value) =
      (milnorWDiagonalIncl h * x.lift) *
        (fin4BruhatRightLift hij htrans
          (fin4DiagonalElementary h.diag * x.matrix)).value
    rw [fin4BruhatRightLift_value_mul_left_diagonal]
    group

end GaloisForLFunctions.HTGeometry
