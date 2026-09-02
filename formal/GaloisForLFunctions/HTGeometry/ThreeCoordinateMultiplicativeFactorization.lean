import GaloisForLFunctions.HTGeometry.AlgebraicClosureAlgClosed
import GaloisForLFunctions.HTGeometry.IntermediateFieldEigenvectorDescent
import GaloisForLFunctions.HTGeometry.RittDifferentialAlgebraicBridge
import GaloisForLFunctions.HTGeometry.SimpleTranscendentalLinearDisjoint
import GaloisForLFunctions.HTGeometry.ThreeCoordinateLogarithmicSeparation

/-!
# Three-coordinate multiplicative factorization

For algebraic branches on the three pairwise coordinate faces, a product which loses the common
coordinate has tensor rank one after finite algebraic covers.  The proof descends one logarithmic
derivative through a concrete linearly disjoint compositum, divides by the resulting one-coordinate
eigenvector, and applies free-coordinate constant-field descent to all three factors.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-- A coordinate derivation absent from the generating set kills every algebraic branch over that
coordinate field, in the canonical free-coordinate algebraic closure. -/
theorem freeCoordinateAlgebraicClosureDerivation_eq_zero_of_isAlgebraic_adjoin
    {C σ : Type*} [Field C] [CharZero C] [DecidableEq σ]
    (S : Set σ) {i : σ} (hi : i ∉ S)
    {u : FreeCoordinateAlgebraicClosure C σ}
    (hu : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C σ '' S)) u) :
    freeCoordinateAlgebraicClosureDerivation i u = 0 := by
  exact coordinateDerivation_eq_zero_of_isAlgebraic_pair
    (algebraicClosureFreeCoordinate C σ)
    (fun j => freeCoordinateAlgebraicClosureDerivation j)
    (fun j k => freeCoordinateAlgebraicClosureDerivation_coordinate j k)
    hi hu

/-- A three-face product supplies a nonzero one-coordinate factor with the same logarithmic
derivative as the `(x,y)` branch in the `y` direction. -/
theorem exists_coordinateOne_eigenfactor
    {C : Type*} [Field C] [IsAlgClosed C] [CharZero C]
    {A B Q : FreeCoordinateAlgebraicClosure C (Fin 3)}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hA : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 1} : Set (Fin 3)))) A)
    (hB : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 2} : Set (Fin 3)))) B)
    (hQ : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({1, 2} : Set (Fin 3)))) Q)
    (hprod : A * B = Q) :
    ∃ c : FreeCoordinateAlgebraicClosure C (Fin 3),
      c ≠ 0 ∧
      IsAlgebraic (IntermediateField.adjoin C
        (algebraicClosureFreeCoordinate C (Fin 3) '' ({1} : Set (Fin 3)))) c ∧
      freeCoordinateAlgebraicClosureDerivation 1 c =
        (freeCoordinateAlgebraicClosureDerivation 1 A / A) * c := by
  let L := FreeCoordinateAlgebraicClosure C (Fin 3)
  let v : Fin 3 → L := algebraicClosureFreeCoordinate C (Fin 3)
  let D : Fin 3 → Derivation C L L :=
    fun i => freeCoordinateAlgebraicClosureDerivation i
  let X : IntermediateField C L := IntermediateField.adjoin C ({v 0} : Set L)
  let Y : IntermediateField C L := IntermediateField.adjoin C ({v 1} : Set L)
  let XY : IntermediateField C L :=
    IntermediateField.adjoin C (v '' ({0, 1} : Set (Fin 3)))
  let Yalg : IntermediateField C L :=
    (algebraicClosure (↥Y) L).restrictScalars C
  have hlog := freeCoordinate_three_logarithmicDerivative_separation
    hA0 hB0 hA hB hQ hprod
  have hD0Yalg : ∀ y : Yalg, D 0 (y : L) = 0 := by
    intro y
    apply derivationBase_eq_zero_of_isAlgebraic_adjoin
      (D 0) (S := ({v 1} : Set L))
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      subst w
      simpa [D, v, L] using
        (freeCoordinateAlgebraicClosureDerivation_coordinate
          (C := C) (i := (0 : Fin 3)) (j := (1 : Fin 3)))
    · apply mem_algebraicClosure_iff.mp
      exact y.property
  have hxTrans : Transcendental Yalg (v 0) := by
    intro hxAlg
    have hxZero := derivationBase_eq_zero_of_isAlgebraic Yalg (D 0)
      (fun y hy => hD0Yalg ⟨y, hy⟩) hxAlg
    have hxOne : D 0 (v 0) = 1 := by
      simpa [D, v, L] using
        (freeCoordinateAlgebraicClosureDerivation_coordinate
          (C := C) (i := (0 : Fin 3)) (j := (0 : Fin 3)))
    exact one_ne_zero (hxOne.symm.trans hxZero)
  have hYX : Yalg.LinearDisjoint X :=
    linearDisjoint_adjoin_of_transcendental Yalg (v 0) hxTrans
  have hD1Yalg : ∀ y : L, y ∈ Yalg → D 1 y ∈ Yalg := by
    intro y hy
    change D 1 y ∈ (algebraicClosure (↥Y) L).restrictScalars C
    rw [IntermediateField.mem_restrictScalars]
    apply derivationBase_mem_algebraicClosure_adjoin
      (D 1) (S := ({v 1} : Set L))
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      subst w
      rw [show D 1 (v 1) = 1 by
        simpa [D, v, L] using
          (freeCoordinateAlgebraicClosureDerivation_coordinate
            (C := C) (i := (1 : Fin 3)) (j := (1 : Fin 3)))]
      exact (IntermediateField.adjoin C ({v 1} : Set L)).one_mem
    · exact hy
  let DY : Derivation C Yalg Yalg := restrictDerivation (D 1) Yalg hD1Yalg
  have hD1X : ∀ x : X, D 1 (x : L) = 0 := by
    intro x
    apply derivationBase_eq_zero_of_mem_adjoin
      (D 1) (S := ({v 0} : Set L))
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      subst w
      simpa [D, v, L] using
        (freeCoordinateAlgebraicClosureDerivation_coordinate
          (C := C) (i := (1 : Fin 3)) (j := (0 : Fin 3)))
    · exact x.property
  let qL : L := D 1 A / A
  have hqYalg : qL ∈ Yalg := by
    change qL ∈ (algebraicClosure (↥Y) L).restrictScalars C
    rw [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
    exact hlog.2
  let q : Yalg := ⟨qL, hqYalg⟩
  have hXYle : XY ≤ Yalg ⊔ X := by
    change IntermediateField.adjoin C (v '' ({0, 1} : Set (Fin 3))) ≤ Yalg ⊔ X
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · exact (show X ≤ Yalg ⊔ X from le_sup_right)
        (IntermediateField.subset_adjoin C ({v 0} : Set L) (by simp))
    · apply (show Yalg ≤ Yalg ⊔ X from le_sup_left)
      rw [IntermediateField.mem_restrictScalars]
      exact IntermediateField.algebraMap_mem _
        (⟨v 1, IntermediateField.subset_adjoin C ({v 1} : Set L) (by simp)⟩ : Y)
  have hAK : IsAlgebraic ↥(Yalg ⊔ X) A :=
    isAlgebraic_of_intermediateField_le hXYle hA
  have hA_eigen : D 1 A = (q : L) * A := by
    change D 1 A = (D 1 A / A) * A
    rw [div_mul_cancel₀ _ hA0]
  letI : IsAlgClosed Yalg := algebraicClosure_isAlgClosed (↥Y) L
  obtain ⟨cY, hcY0, hcY_eigen⟩ :=
    exists_left_eigenvector_of_algebraic_intermediateField_sup
      C L Yalg X hYX DY (D 1)
      (fun _ => rfl) hD1X q hAK hA0 hA_eigen
  refine ⟨(cY : L), ?_, ?_, ?_⟩
  · intro hc
    apply hcY0
    exact Subtype.ext hc
  · rw [← mem_algebraicClosure_iff]
    have hc : (cY : L) ∈ algebraicClosure (↥Y) L := cY.property
    have hYeq : IntermediateField.adjoin C
        (algebraicClosureFreeCoordinate C (Fin 3) '' ({1} : Set (Fin 3))) = Y := by
      simp [Y, v, L, Set.image_singleton]
    rw [hYeq]
    exact hc
  · exact congrArg Subtype.val hcY_eigen

theorem exists_remaining_factors_of_coordinateOne_eigenfactor
    {C : Type*} [Field C] [CharZero C]
    {A B Q c : FreeCoordinateAlgebraicClosure C (Fin 3)}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hc0 : c ≠ 0)
    (hA : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 1} : Set (Fin 3)))) A)
    (hB : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 2} : Set (Fin 3)))) B)
    (hQ : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({1, 2} : Set (Fin 3)))) Q)
    (hcYAlg : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({1} : Set (Fin 3)))) c)
    (hc_eigen : freeCoordinateAlgebraicClosureDerivation 1 c =
      (freeCoordinateAlgebraicClosureDerivation 1 A / A) * c)
    (hprod : A * B = Q) :
    ∃ a b : FreeCoordinateAlgebraicClosure C (Fin 3),
      a ≠ 0 ∧ b ≠ 0 ∧
      IsAlgebraic (freeCoordinateField C (Fin 3) ({0} : Set (Fin 3))) a ∧
      IsAlgebraic (freeCoordinateField C (Fin 3) ({2} : Set (Fin 3))) b ∧
      IsAlgebraic (freeCoordinateField C (Fin 3) ({1} : Set (Fin 3))) c ∧
      A = a * c ∧ B = b / a ∧ Q = b * c := by
  have hA_eigen : freeCoordinateAlgebraicClosureDerivation 1 A =
      (freeCoordinateAlgebraicClosureDerivation 1 A / A) * A := by
    rw [div_mul_cancel₀ _ hA0]
  have hD0c : freeCoordinateAlgebraicClosureDerivation 0 c = 0 :=
    freeCoordinateAlgebraicClosureDerivation_eq_zero_of_isAlgebraic_adjoin
      (C := C) (σ := Fin 3) ({1} : Set (Fin 3)) (i := (0 : Fin 3))
      (by simp) (u := c) hcYAlg
  have hD2c : freeCoordinateAlgebraicClosureDerivation 2 c = 0 :=
    freeCoordinateAlgebraicClosureDerivation_eq_zero_of_isAlgebraic_adjoin
      (C := C) (σ := Fin 3) ({1} : Set (Fin 3)) (i := (2 : Fin 3))
      (by simp) (u := c) hcYAlg
  let a : FreeCoordinateAlgebraicClosure C (Fin 3) := A / c
  have ha0 : a ≠ 0 := div_ne_zero hA0 hc0
  have hD1a : freeCoordinateAlgebraicClosureDerivation 1 a = 0 := by
    dsimp only [a]
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      hA_eigen, hc_eigen]
    simp only [smul_eq_mul]
    field_simp [hc0]
    ring
  have hD2A : freeCoordinateAlgebraicClosureDerivation 2 A = 0 :=
    freeCoordinateAlgebraicClosureDerivation_eq_zero_of_isAlgebraic_adjoin
      (C := C) ({0, 1} : Set (Fin 3)) (i := (2 : Fin 3)) (by simp) hA
  have hD2a : freeCoordinateAlgebraicClosureDerivation 2 a = 0 := by
    dsimp only [a]
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      hD2A, hD2c]
    simp
  have haAlg : IsAlgebraic
      (freeCoordinateField C (Fin 3) ({0} : Set (Fin 3))) a := by
    apply isAlgebraic_freeCoordinateField_of_algebraicClosureDerivations_eq_zero
    intro i hi
    fin_cases i
    · exact (hi (by simp)).elim
    · exact hD1a
    · exact hD2a
  have hQ0 : Q ≠ 0 := by rw [← hprod]; exact mul_ne_zero hA0 hB0
  have hD0Q : freeCoordinateAlgebraicClosureDerivation 0 Q = 0 :=
    freeCoordinateAlgebraicClosureDerivation_eq_zero_of_isAlgebraic_adjoin
      (C := C) ({1, 2} : Set (Fin 3)) (i := (0 : Fin 3)) (by simp) hQ
  have hD1B : freeCoordinateAlgebraicClosureDerivation 1 B = 0 :=
    freeCoordinateAlgebraicClosureDerivation_eq_zero_of_isAlgebraic_adjoin
      (C := C) ({0, 2} : Set (Fin 3)) (i := (1 : Fin 3)) (by simp) hB
  have hQ_eigen : freeCoordinateAlgebraicClosureDerivation 1 Q =
      (freeCoordinateAlgebraicClosureDerivation 1 A / A) * Q := by
    have hp := congrArg (freeCoordinateAlgebraicClosureDerivation 1) hprod
    rw [Derivation.leibniz, hD1B, hA_eigen] at hp
    simp only [smul_eq_mul, mul_zero, add_zero] at hp
    calc
      freeCoordinateAlgebraicClosureDerivation 1 Q =
          0 + B * ((freeCoordinateAlgebraicClosureDerivation 1 A / A) * A) := hp.symm
      _ = (freeCoordinateAlgebraicClosureDerivation 1 A / A) * A * B := by ring
      _ = (freeCoordinateAlgebraicClosureDerivation 1 A / A) * Q := by
        rw [← hprod]
        ring
  let b : FreeCoordinateAlgebraicClosure C (Fin 3) := Q / c
  have hb0 : b ≠ 0 := div_ne_zero hQ0 hc0
  have hD0b : freeCoordinateAlgebraicClosureDerivation 0 b = 0 := by
    dsimp only [b]
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      hD0Q, hD0c]
    simp
  have hD1b : freeCoordinateAlgebraicClosureDerivation 1 b = 0 := by
    dsimp only [b]
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      hQ_eigen, hc_eigen]
    simp only [smul_eq_mul]
    field_simp [hc0]
    ring
  have hbAlg : IsAlgebraic
      (freeCoordinateField C (Fin 3) ({2} : Set (Fin 3))) b := by
    apply isAlgebraic_freeCoordinateField_of_algebraicClosureDerivations_eq_zero
    intro i hi
    fin_cases i
    · exact hD0b
    · exact hD1b
    · exact (hi (by simp)).elim
  have hcAlg : IsAlgebraic
      (freeCoordinateField C (Fin 3) ({1} : Set (Fin 3))) c := by
    apply isAlgebraic_freeCoordinateField_of_algebraicClosureDerivations_eq_zero
    intro i hi
    fin_cases i
    · exact hD0c
    · exact (hi (by simp)).elim
    · exact hD2c
  refine ⟨a, b, ha0, hb0, haAlg, hbAlg, hcAlg, ?_, ?_, ?_⟩
  · change A = (A / c) * c
    exact (div_mul_cancel₀ A hc0).symm
  · change B = (Q / c) / (A / c)
    field_simp [hA0, hc0]
    calc B * A = A * B := mul_comm _ _
      _ = Q := hprod
  · change Q = (Q / c) * c
    exact (div_mul_cancel₀ Q hc0).symm

/-- **Three-coordinate rank-one factorization.**  In the canonical common algebraic closure of
`C(x,y,z)`, nonzero branches algebraic on the `(x,y)`, `(x,z)`, and `(y,z)` faces and satisfying
`A * B = Q` split into one-coordinate algebraic factors `A = a*c`, `B = b/a`, `Q = b*c`.

No regularity, specialization, normal-cover, or branch hypothesis is imposed. -/
theorem freeCoordinate_three_multiplicative_factorization
    {C : Type*} [Field C] [IsAlgClosed C] [CharZero C]
    {A B Q : FreeCoordinateAlgebraicClosure C (Fin 3)}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hA : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 1} : Set (Fin 3)))) A)
    (hB : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 2} : Set (Fin 3)))) B)
    (hQ : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({1, 2} : Set (Fin 3)))) Q)
    (hprod : A * B = Q) :
    ∃ a b c : FreeCoordinateAlgebraicClosure C (Fin 3),
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      IsAlgebraic (freeCoordinateField C (Fin 3) ({0} : Set (Fin 3))) a ∧
      IsAlgebraic (freeCoordinateField C (Fin 3) ({2} : Set (Fin 3))) b ∧
      IsAlgebraic (freeCoordinateField C (Fin 3) ({1} : Set (Fin 3))) c ∧
      A = a * c ∧ B = b / a ∧ Q = b * c := by
  obtain ⟨c, hc0, hcYAlg, hc_eigen⟩ :=
    exists_coordinateOne_eigenfactor hA0 hB0 hA hB hQ hprod
  obtain ⟨a, b, ha0, hb0, haAlg, hbAlg, hcAlg, hAc, hBa, hQc⟩ :=
    exists_remaining_factors_of_coordinateOne_eigenfactor
      hA0 hB0 hc0 hA hB hQ hcYAlg hc_eigen hprod
  exact ⟨a, b, c, ha0, hb0, hc0, haAlg, hbAlg, hcAlg, hAc, hBa, hQc⟩

end

end GaloisForLFunctions.HTGeometry
