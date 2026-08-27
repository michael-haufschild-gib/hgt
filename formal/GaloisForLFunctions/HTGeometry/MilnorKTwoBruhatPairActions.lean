import GaloisForLFunctions.HTGeometry.MilnorKTwoBruhatPairs

/-!
# Left permutations of Milnor's Bruhat-pair space

Diagonal, upper-unipotent, and adjacent-Weyl transformations lift to permutations of the pair
space.  Bijectivity is proved uniformly: any Milnor-`K₂`-equivariant lift of a base bijection is
automatically bijective because every fixed-matrix fiber is a `K₂` torsor.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MilnorDiagonalExtension

variable {F : Type*} [Field F]

theorem milnorWProjection_weylGenerator_eq_simple
    {i j : Fin 4} (hij : i ≠ j) :
    milnorWProjection (F := F) (milnorWWeylGenerator (F := F) i j hij) =
      fin4SimpleWeylMonomial hij 1 := by
  apply Subtype.ext
  exact milnorWProjection_weylGenerator i j hij

theorem milnorWProjection_matsumotoDiagonalLift
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    milnorWProjection (F := F)
        (milnorWDiagonalIncl (F := F) (fin4MatsumotoDiagonalLift hij u)) =
      detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u) := by
  rw [milnorWProjection_diagonalIncl]
  rfl

noncomputable def fin4BruhatPairEquivOfFiberEquivariant
    (base : elementaryGroup F (Fin 4) ≃ elementaryGroup F (Fin 4))
    (f : Fin4BruhatPair (F := F) → Fin4BruhatPair (F := F))
    (hbase : ∀ x, (f x).matrix = base x.matrix)
    (hequiv : ∀ (z : Multiplicative (MilnorKDeg F 2)) x,
      f (z • x) = z • f x) :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  Equiv.ofBijective f <| by
    constructor
    · intro x y hxy
      have hmatrix : x.matrix = y.matrix := base.injective (by
        rw [← hbase x, ← hbase y, hxy])
      obtain ⟨z, hz, _⟩ := existsUnique_milnorKTwo_smul_bruhatPair hmatrix
      have hzfix : z • f x = f x := by
        rw [← hequiv, hz, hxy]
      obtain ⟨z₀, hz₀, hunique⟩ :=
        existsUnique_milnorKTwo_smul_bruhatPair
          (x := f x) (y := f x) rfl
      have hz_one : z = 1 := (hunique z hzfix).trans (hunique 1 (one_smul _ _)).symm
      rw [← hz, hz_one, one_smul]
    · intro y
      obtain ⟨x, hx⟩ := exists_fin4BruhatPair_over (base.symm y.matrix)
      have hmatrix : (f x).matrix = y.matrix := by
        rw [hbase, hx, base.apply_symm_apply]
      obtain ⟨z, hz, _⟩ := existsUnique_milnorKTwo_smul_bruhatPair hmatrix
      exact ⟨z • x, by rw [hequiv, hz]⟩

noncomputable def fin4BruhatPairDiagonalMap
    (h : MilnorDiagonalExtension F 4) (x : Fin4BruhatPair (F := F)) :
    Fin4BruhatPair (F := F) :=
  { matrix := fin4DiagonalElementary h.diag * x.matrix
    lift := milnorWDiagonalIncl h * x.lift
    compatible := by
      rw [fin4BruhatProjection_diagonal_mul, map_mul,
        milnorWProjection_diagonalIncl]
      change detOneDiagonalToFieldMonomial h.diag * fin4BruhatProjection x.matrix =
        detOneDiagonalToFieldMonomial h.diag * milnorWProjection x.lift
      rw [x.compatible] }

theorem fin4BruhatPairDiagonalMap_matrix
    (h : MilnorDiagonalExtension F 4) (x : Fin4BruhatPair (F := F)) :
    (fin4BruhatPairDiagonalMap h x).matrix =
      fin4DiagonalElementary h.diag * x.matrix := rfl

theorem fin4BruhatPairDiagonalMap_equivariant
    (h : MilnorDiagonalExtension F 4)
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairDiagonalMap h (z • x) =
      z • fin4BruhatPairDiagonalMap h x := by
  apply Fin4BruhatPair.ext
  · rfl
  · change milnorWDiagonalIncl h * (milnorWCentralIncl z * x.lift) =
      milnorWCentralIncl z * (milnorWDiagonalIncl h * x.lift)
    have hc := Subgroup.mem_center_iff.1
      (milnorWCentralIncl_mem_center (F := F) z) (milnorWDiagonalIncl h)
    rw [← mul_assoc, hc, mul_assoc]

noncomputable def fin4BruhatPairDiagonalEquiv
    (h : MilnorDiagonalExtension F 4) :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairEquivOfFiberEquivariant
    (Equiv.mulLeft (fin4DiagonalElementary h.diag))
    (fin4BruhatPairDiagonalMap h)
    (fin4BruhatPairDiagonalMap_matrix h)
    (fin4BruhatPairDiagonalMap_equivariant h)

noncomputable def fin4BruhatPairUpperMap
    (t : (upperSteinbergSubgroup (F := F) (Fin 4)))
    (x : Fin4BruhatPair (F := F)) : Fin4BruhatPair (F := F) :=
  { matrix := fin4SteinbergElementary t.1 * x.matrix
    lift := x.lift
    compatible := by
      rw [fin4BruhatProjection_mul_left_upper t.1 t.2]
      exact x.compatible }

theorem fin4BruhatPairUpperMap_matrix
    (t : (upperSteinbergSubgroup (F := F) (Fin 4)))
    (x : Fin4BruhatPair (F := F)) :
    (fin4BruhatPairUpperMap t x).matrix =
      fin4SteinbergElementary t.1 * x.matrix := rfl

theorem fin4BruhatPairUpperMap_equivariant
    (t : (upperSteinbergSubgroup (F := F) (Fin 4)))
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairUpperMap t (z • x) =
      z • fin4BruhatPairUpperMap t x := by
  rfl

noncomputable def fin4BruhatPairUpperEquiv
    (t : (upperSteinbergSubgroup (F := F) (Fin 4))) :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairEquivOfFiberEquivariant
    (Equiv.mulLeft (fin4SteinbergElementary t.1))
    (fin4BruhatPairUpperMap t)
    (fin4BruhatPairUpperMap_matrix t)
    (fin4BruhatPairUpperMap_equivariant t)

theorem fieldMonomialData_detOneDiagonal
    (d : detOneDiagonalUnits F 4) :
    (fieldMonomialData (detOneDiagonalToFieldMonomial d)).1 = 1 ∧
      (fieldMonomialData (detOneDiagonalToFieldMonomial d)).2 = d.1 := by
  exact fieldMonomialData_eq (detOneDiagonalMatrixUnitHom_matrix d)

theorem fieldMonomialData_simpleWeyl
    {i j : Fin 4} (hij : i ≠ j) (u : Fˣ) :
    (fieldMonomialData (fin4SimpleWeylMonomial hij u)).1 = Equiv.swap i j := by
  apply (fieldMonomialData_eq (sigma := Equiv.swap i j)
    (c := steinbergWeylRootScale (i := i) (j := j) u) ?_).1
  have hval : (fin4SimpleWeylMonomial hij u).1 =
      steinbergToGL (steinbergWeyl hij u) := rfl
  rw [hval, steinbergToGL_weyl, weylMatrix_eq_signedMonomial hij]

theorem detOneDiagonalToFieldMonomial_ne_simpleWeyl
    {i j : Fin 4} (hij : i ≠ j) (d : detOneDiagonalUnits F 4) (u : Fˣ) :
    detOneDiagonalToFieldMonomial d ≠ fin4SimpleWeylMonomial hij u := by
  intro h
  have hp := congrArg (fun q : fieldDetOneMonomialSubgroup (F := F) =>
    (fieldMonomialData q).1) h
  rw [(fieldMonomialData_detOneDiagonal d).1,
    fieldMonomialData_simpleWeyl hij u] at hp
  have hs : Equiv.swap i j i = j := Equiv.swap_apply_left i j
  have hi := DFunLike.congr_fun hp i
  simp [hs, hij] at hi

noncomputable def fin4BruhatCanonicalLeftValue
    {i j : Fin 4} (hij : i ≠ j)
    (q : fieldDetOneMonomialSubgroup (F := F)) : MilnorW F := by
  classical
  exact if q = fin4SimpleWeylMonomial hij (1 : Fˣ) then
      milnorWWeylGenerator (F := F) i j hij
    else
      (milnorWDiagonalIncl (F := F)
        (fin4MatsumotoDiagonalLift hij
          ((fieldMonomialData q).2 i)⁻¹))⁻¹

theorem fin4BruhatCanonicalLeftValue_projection
    {i j : Fin 4} (hij : i ≠ j)
    (q : fieldDetOneMonomialSubgroup (F := F))
    (hq : q = fin4SimpleWeylMonomial hij (1 : Fˣ) ∨
      ∃ u : Fˣ, q =
        (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹) :
    milnorWProjection (fin4BruhatCanonicalLeftValue hij q) = q := by
  classical
  rcases hq with hweyl | ⟨u, hdiag⟩
  · simp [fin4BruhatCanonicalLeftValue, hweyl,
      milnorWProjection_weylGenerator_eq_simple]
  · have hdiag' : q = detOneDiagonalToFieldMonomial
        (fin4MatsumotoDiagonal i j u⁻¹) := by
      rw [hdiag, ← map_inv, fin4MatsumotoDiagonal_inv]
    have hne : q ≠ fin4SimpleWeylMonomial hij (1 : Fˣ) := by
      rw [hdiag']
      exact detOneDiagonalToFieldMonomial_ne_simpleWeyl hij _ _
    have hdata : (fieldMonomialData q).2 =
        (fin4MatsumotoDiagonal i j u⁻¹).1 := by
      rw [hdiag']
      exact (fieldMonomialData_detOneDiagonal _).2
    rw [fin4BruhatCanonicalLeftValue, if_neg hne, map_inv,
      milnorWProjection_matsumotoDiagonalLift]
    have hi : (fieldMonomialData q).2 i = u⁻¹ := by
      rw [hdata]
      simp [fin4MatsumotoDiagonal, hij]
    rw [hi, inv_inv, ← map_inv, fin4MatsumotoDiagonal_inv]
    exact hdiag'.symm

noncomputable def fin4BruhatLeftQuotient
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4)) :
    fieldDetOneMonomialSubgroup (F := F) :=
  fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) *
    (fin4BruhatProjection A)⁻¹

theorem fin4BruhatLeftQuotient_allowed
    {i j : Fin 4} (hij : i ≠ j) (A : elementaryGroup F (Fin 4))
    (htrans :
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A) :
    fin4BruhatLeftQuotient hij A =
        fin4SimpleWeylMonomial hij (1 : Fˣ) ∨
      ∃ u : Fˣ, fin4BruhatLeftQuotient hij A =
        (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ := by
  rcases htrans with hweyl | ⟨u, hdiag⟩
  · left
    rw [fin4BruhatLeftQuotient, hweyl]
    group
  · right
    refine ⟨u, ?_⟩
    rw [fin4BruhatLeftQuotient, hdiag]
    group

structure Fin4BruhatLeftLift
    (A : elementaryGroup F (Fin 4)) {i j : Fin 4} (hij : i ≠ j) where
  value : MilnorW F
  projection_eq :
    fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
      milnorWProjection value * fin4BruhatProjection A

noncomputable def fin4BruhatLeftLift
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A)
    (A : elementaryGroup F (Fin 4)) : Fin4BruhatLeftLift A hij :=
  { value := fin4BruhatCanonicalLeftValue hij (fin4BruhatLeftQuotient hij A)
    projection_eq := by
      rw [fin4BruhatCanonicalLeftValue_projection
        (q := fin4BruhatLeftQuotient hij A) hij
        (fin4BruhatLeftQuotient_allowed hij A (htrans A)),
        fin4BruhatLeftQuotient]
      group }

noncomputable def fin4BruhatPairSimpleWeylMap
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A)
    (x : Fin4BruhatPair (F := F)) : Fin4BruhatPair (F := F) :=
  { matrix := fin4SimpleWeylElementary hij 1 * x.matrix
    lift := (fin4BruhatLeftLift hij htrans x.matrix).value * x.lift
    compatible := by
      rw [map_mul, ← x.compatible]
      exact (fin4BruhatLeftLift hij htrans x.matrix).projection_eq }

theorem fin4BruhatPairSimpleWeylMap_matrix
    {i j : Fin 4} (hij : i ≠ j) (htrans) (x : Fin4BruhatPair (F := F)) :
    (fin4BruhatPairSimpleWeylMap hij htrans x).matrix =
      fin4SimpleWeylElementary hij 1 * x.matrix := rfl

theorem fin4BruhatPairSimpleWeylMap_equivariant
    {i j : Fin 4} (hij : i ≠ j) (htrans)
    (z : Multiplicative (MilnorKDeg F 2)) (x : Fin4BruhatPair (F := F)) :
    fin4BruhatPairSimpleWeylMap hij htrans (z • x) =
      z • fin4BruhatPairSimpleWeylMap hij htrans x := by
  apply Fin4BruhatPair.ext
  · rfl
  · change (fin4BruhatLeftLift hij htrans x.matrix).value *
        (milnorWCentralIncl z * x.lift) =
      milnorWCentralIncl z *
        ((fin4BruhatLeftLift hij htrans x.matrix).value * x.lift)
    have hc := Subgroup.mem_center_iff.1
      (milnorWCentralIncl_mem_center (F := F) z)
      (fin4BruhatLeftLift hij htrans x.matrix).value
    rw [← mul_assoc, hc, mul_assoc]

noncomputable def fin4BruhatPairSimpleWeylEquiv
    {i j : Fin 4} (hij : i ≠ j)
    (htrans : ∀ A : elementaryGroup F (Fin 4),
      fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
          fin4SimpleWeylMonomial hij 1 * fin4BruhatProjection A ∨
        ∃ u : Fˣ,
          fin4BruhatProjection (fin4SimpleWeylElementary hij 1 * A) =
            (detOneDiagonalToFieldMonomial (fin4MatsumotoDiagonal i j u))⁻¹ *
              fin4BruhatProjection A) :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairEquivOfFiberEquivariant
    (Equiv.mulLeft (fin4SimpleWeylElementary hij 1))
    (fin4BruhatPairSimpleWeylMap hij htrans)
    (fin4BruhatPairSimpleWeylMap_matrix hij htrans)
    (fin4BruhatPairSimpleWeylMap_equivariant hij htrans)

noncomputable def fin4BruhatPairW01Equiv :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairSimpleWeylEquiv (by decide)
    (fun A => fin4BruhatProjection_w01_mul A)

noncomputable def fin4BruhatPairW12Equiv :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairSimpleWeylEquiv (by decide)
    (fun A => fin4BruhatProjection_w12_mul A)

noncomputable def fin4BruhatPairW23Equiv :
    Fin4BruhatPair (F := F) ≃ Fin4BruhatPair (F := F) :=
  fin4BruhatPairSimpleWeylEquiv (by decide)
    (fun A => fin4BruhatProjection_w23_mul A)

end GaloisForLFunctions.HTGeometry
