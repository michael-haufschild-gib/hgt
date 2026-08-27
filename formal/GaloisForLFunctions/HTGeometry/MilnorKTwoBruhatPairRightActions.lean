import GaloisForLFunctions.HTGeometry.MilnorKTwoBruhatPairActions

/-!
# Right generator permutations on the rank-four Bruhat-pair space

This file lifts right diagonal, upper-unipotent, and adjacent-Weyl multiplication
to permutations of `Fin4BruhatPair`.  The adjacent-Weyl correction is supplied
by the right-hand alternative in Milnor's Lemma 12.7.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MilnorDiagonalExtension

variable {F : Type*} [Field F]

theorem fin4SimpleWeylMonomial_one_inv
    {i j : Fin 4} (hij : i ≠ j) :
    (fin4SimpleWeylMonomial hij (1 : Fˣ))⁻¹ =
      fin4SimpleWeylMonomial hij (-1 : Fˣ) := by
  apply Subtype.ext
  change (steinbergToGL (steinbergWeyl hij (1 : Fˣ)))⁻¹ =
    steinbergToGL (steinbergWeyl hij (-1 : Fˣ))
  rw [← map_inv, steinbergWeyl_neg]

noncomputable def fin4BruhatPairDiagonalRightMap
    (h : MilnorDiagonalExtension F 4) (x : Fin4BruhatPair (F := F)) :
    Fin4BruhatPair (F := F) :=
  { matrix := x.matrix * fin4DiagonalElementary h.diag
    lift := x.lift * milnorWDiagonalIncl h
    compatible := by
      rw [fin4BruhatProjection_mul_diagonal, map_mul,
        milnorWProjection_diagonalIncl]
      change fin4BruhatProjection x.matrix * detOneDiagonalToFieldMonomial h.diag =
        milnorWProjection x.lift * detOneDiagonalToFieldMonomial h.diag
      rw [x.compatible] }

theorem fin4BruhatPairDiagonalRightMap_matrix
    (h : MilnorDiagonalExtension F 4) (x : Fin4BruhatPair (F := F)) :
    (fin4BruhatPairDiagonalRightMap h x).matrix =
      x.matrix * fin4DiagonalElementary h.diag := rfl

theorem fin4BruhatPairDiagonalRightMap_equivariant
    (h : MilnorDiagonalExtension F 4)
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairDiagonalRightMap h (z • x) =
      z • fin4BruhatPairDiagonalRightMap h x := by
  apply Fin4BruhatPair.ext
  · rfl
  · change (milnorWCentralIncl z * x.lift) * milnorWDiagonalIncl h =
      milnorWCentralIncl z * (x.lift * milnorWDiagonalIncl h)
    rw [mul_assoc]

noncomputable def fin4BruhatPairDiagonalRightEquiv
    (h : MilnorDiagonalExtension F 4) :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairEquivOfFiberEquivariant
    (Equiv.mulRight (fin4DiagonalElementary h.diag))
    (fin4BruhatPairDiagonalRightMap h)
    (fin4BruhatPairDiagonalRightMap_matrix h)
    (fin4BruhatPairDiagonalRightMap_equivariant h)

noncomputable def fin4BruhatPairUpperRightMap
    (t : upperSteinbergSubgroup (F := F) (Fin 4))
    (x : Fin4BruhatPair (F := F)) : Fin4BruhatPair (F := F) :=
  { matrix := x.matrix * fin4SteinbergElementary t.1
    lift := x.lift
    compatible := by
      rw [fin4BruhatProjection_mul_right_upper x.matrix t.1 t.2]
      exact x.compatible }

theorem fin4BruhatPairUpperRightMap_matrix
    (t : upperSteinbergSubgroup (F := F) (Fin 4))
    (x : Fin4BruhatPair (F := F)) :
    (fin4BruhatPairUpperRightMap t x).matrix =
      x.matrix * fin4SteinbergElementary t.1 := rfl

theorem fin4BruhatPairUpperRightMap_equivariant
    (t : upperSteinbergSubgroup (F := F) (Fin 4))
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairUpperRightMap t (z • x) =
      z • fin4BruhatPairUpperRightMap t x := rfl

noncomputable def fin4BruhatPairUpperRightEquiv
    (t : upperSteinbergSubgroup (F := F) (Fin 4)) :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairEquivOfFiberEquivariant
    (Equiv.mulRight (fin4SteinbergElementary t.1))
    (fin4BruhatPairUpperRightMap t)
    (fin4BruhatPairUpperRightMap_matrix t)
    (fin4BruhatPairUpperRightMap_equivariant t)

noncomputable def fin4BruhatCanonicalRightValue
    {i j : Fin 4} (hij : i ≠ j)
    (q : fieldDetOneMonomialSubgroup (F := F)) : MilnorW F := by
  classical
  exact if q = fin4SimpleWeylMonomial hij (-1 : Fˣ) then
      (milnorWWeylGenerator (F := F) i j hij)⁻¹
    else
      milnorWDiagonalIncl (F := F)
        (fin4MatsumotoDiagonalLift hij ((fieldMonomialData q).2 i))

theorem fin4BruhatCanonicalRightValue_projection
    {i j : Fin 4} (hij : i ≠ j)
    (q : fieldDetOneMonomialSubgroup (F := F))
    (hq : q = fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
      ∃ u : Fˣ, q =
        detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u)) :
    milnorWProjection (fin4BruhatCanonicalRightValue hij q) = q := by
  classical
  rcases hq with hweyl | ⟨u, hdiag⟩
  · rw [fin4BruhatCanonicalRightValue, if_pos hweyl, map_inv,
      milnorWProjection_weylGenerator_eq_simple,
      fin4SimpleWeylMonomial_one_inv, hweyl]
  · have hne : q ≠ fin4SimpleWeylMonomial hij (-1 : Fˣ) := by
      rw [hdiag]
      exact detOneDiagonalToFieldMonomial_ne_simpleWeyl hij _ _
    have hdata : (fieldMonomialData q).2 =
        (fin4MatsumotoDiagonal i j u).1 := by
      rw [hdiag]
      exact (fieldMonomialData_detOneDiagonal _).2
    rw [fin4BruhatCanonicalRightValue, if_neg hne,
      milnorWProjection_matsumotoDiagonalLift]
    have hi : (fieldMonomialData q).2 i = u := by
      rw [hdata]
      simp [fin4MatsumotoDiagonal, hij]
    rw [hi]
    exact hdiag.symm

noncomputable def fin4BruhatRightQuotient
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4)) :
    fieldDetOneMonomialSubgroup (F := F) :=
  (fin4BruhatProjection A)⁻¹ *
    fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ))

theorem fin4BruhatRightQuotient_allowed
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4))
    (htrans :
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u)) :
    fin4BruhatRightQuotient hij A =
        fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
      ∃ u : Fˣ, fin4BruhatRightQuotient hij A =
        detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u) := by
  rcases htrans with hweyl | ⟨u, hdiag⟩
  · left
    rw [fin4BruhatRightQuotient, hweyl]
    group
  · right
    refine ⟨u, ?_⟩
    rw [fin4BruhatRightQuotient, hdiag]
    group

structure Fin4BruhatRightLift
    (A : elementaryGroup F (Fin 4)) {i j : Fin 4} (hij : i ≠ j) where
  value : MilnorW F
  projection_eq :
    fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
      fin4BruhatProjection A * milnorWProjection value

noncomputable def fin4BruhatRightLift
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))
    (A : elementaryGroup F (Fin 4)) : Fin4BruhatRightLift A hij :=
  { value := fin4BruhatCanonicalRightValue hij (fin4BruhatRightQuotient hij A)
    projection_eq := by
      rw [fin4BruhatCanonicalRightValue_projection
        (q := fin4BruhatRightQuotient hij A) hij
        (fin4BruhatRightQuotient_allowed hij A (htrans A)),
        fin4BruhatRightQuotient]
      group }

noncomputable def fin4BruhatPairSimpleWeylRightMap
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))
    (x : Fin4BruhatPair (F := F)) :
    Fin4BruhatPair (F := F) :=
  { matrix := x.matrix * fin4SimpleWeylElementary hij (-1 : Fˣ)
    lift := x.lift * (fin4BruhatRightLift hij htrans x.matrix).value
    compatible := by
      rw [map_mul, ← x.compatible]
      exact (fin4BruhatRightLift hij htrans x.matrix).projection_eq }

theorem fin4BruhatPairSimpleWeylRightMap_matrix
    {i j : Fin 4} (hij : i ≠ j) (htrans) (x : Fin4BruhatPair (F := F)) :
    (fin4BruhatPairSimpleWeylRightMap hij htrans x).matrix =
      x.matrix * fin4SimpleWeylElementary hij (-1 : Fˣ) := rfl

theorem fin4BruhatPairSimpleWeylRightMap_equivariant
    {i j : Fin 4} (hij : i ≠ j) (htrans)
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairSimpleWeylRightMap hij htrans (z • x) =
      z • fin4BruhatPairSimpleWeylRightMap hij htrans x := by
  apply Fin4BruhatPair.ext
  · rfl
  · change (milnorWCentralIncl z * x.lift) *
        (fin4BruhatRightLift hij htrans x.matrix).value =
      milnorWCentralIncl z *
        (x.lift * (fin4BruhatRightLift hij htrans x.matrix).value)
    rw [mul_assoc]

noncomputable def fin4BruhatPairSimpleWeylRightEquiv
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
          fin4BruhatProjection A * fin4SimpleWeylMonomial hij (-1 : Fˣ) ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (A * fin4SimpleWeylElementary hij (-1 : Fˣ)) =
            fin4BruhatProjection A *
              detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u)) :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairEquivOfFiberEquivariant
    (Equiv.mulRight (fin4SimpleWeylElementary hij (-1 : Fˣ)))
    (fin4BruhatPairSimpleWeylRightMap hij htrans)
    (fin4BruhatPairSimpleWeylRightMap_matrix hij htrans)
    (fin4BruhatPairSimpleWeylRightMap_equivariant hij htrans)

noncomputable def fin4BruhatPairW01RightEquiv :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairSimpleWeylRightEquiv (by decide)
    (fun A => fin4BruhatProjection_mul_w01_neg_one A)

noncomputable def fin4BruhatPairW12RightEquiv :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairSimpleWeylRightEquiv (by decide)
    (fun A => fin4BruhatProjection_mul_w12_neg_one A)

noncomputable def fin4BruhatPairW23RightEquiv :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairSimpleWeylRightEquiv (by decide)
    (fun A => fin4BruhatProjection_mul_w23_neg_one A)

end GaloisForLFunctions.HTGeometry
