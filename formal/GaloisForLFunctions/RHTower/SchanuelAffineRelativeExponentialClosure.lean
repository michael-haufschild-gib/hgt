import GaloisForLFunctions.RHTower.SchanuelStageWitnesses
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg

/-!
# Relative exponential closure and stage-two Schanuel

Let `A = ℚ̄(e^α)` inside `ℂ`.  Two numbers algebraic over `A` cannot be algebraically independent
over `ℚ̄`, because the relative algebraic closure of `A` still has transcendence degree at most
one.  Consequently, a second exponential edge `z ↦ e^z` inside that closure, with
`z ∉ ℚ α`, gives a literal counterexample to the two-variable extraction form of Schanuel's
conjecture.

No conjectural interface is introduced here: the field, algebraicity conditions, and failed
Schanuel stage are the existing concrete objects.
-/

open scoped IntermediateField

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Field generated over the algebraic numbers by one exponential value. -/
def relativeExponentialBase (alpha : ℂ) :
    IntermediateField (algebraicClosure ℚ ℂ) ℂ :=
  IntermediateField.adjoin (algebraicClosure ℚ ℂ)
    (Set.range (fun _ : Unit => Complex.exp alpha))

/-- Two elements algebraic over a one-generator exponential field cannot be algebraically
independent over the algebraic numbers. -/
theorem not_algebraicIndependent_fin_two_of_isAlgebraic_relativeExponentialBase
    (alpha : ℂ) (t : Fin 2 → ℂ)
    (ht : ∀ i, IsAlgebraic (relativeExponentialBase alpha) (t i)) :
    ¬ AlgebraicIndependent (algebraicClosure ℚ ℂ) t := by
  intro hind
  let D : IntermediateField (algebraicClosure ℚ ℂ) ℂ :=
    (algebraicClosure (relativeExponentialBase alpha) ℂ).restrictScalars
      (algebraicClosure ℚ ℂ)
  have htD : ∀ i, t i ∈ D := by
    intro i
    change t i ∈
      (algebraicClosure (relativeExponentialBase alpha) ℂ).restrictScalars
        (algebraicClosure ℚ ℂ)
    rw [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
    exact ht i
  let u : Fin 2 → D := fun i => ⟨t i, htD i⟩
  have hu : AlgebraicIndependent (algebraicClosure ℚ ℂ) u := by
    apply AlgebraicIndependent.of_comp D.val
    simpa [u, Function.comp_def] using hind
  have hlower : Cardinal.mk (Fin 2) ≤
      Algebra.trdeg (algebraicClosure ℚ ℂ) D :=
    hu.cardinalMk_le_trdeg
  have hupper : Algebra.trdeg (algebraicClosure ℚ ℂ) D ≤ Cardinal.mk Unit := by
    change Algebra.trdeg (algebraicClosure ℚ ℂ)
      ((algebraicClosure
        (IntermediateField.adjoin (algebraicClosure ℚ ℂ)
          (Set.range (fun _ : Unit => Complex.exp alpha))) ℂ).restrictScalars
            (algebraicClosure ℚ ℂ)) ≤ Cardinal.mk Unit
    exact trdeg_algebraicClosure_adjoin_range_le
      (K := algebraicClosure ℚ ℂ) (L := ℂ)
      (fun _ : Unit => Complex.exp alpha)
  have himpossible : Cardinal.mk (Fin 2) ≤ Cardinal.mk Unit := hlower.trans hupper
  norm_num [Cardinal.mk_fin, Cardinal.mk_unit] at himpossible

/-- A failure of relative exponential-edge rigidity produces an actual counterexample to the
two-variable extraction form of Schanuel's conjecture. -/
theorem not_schanuelExtractionAt_two_of_relativeExponentialBase_edge
    (alpha z : ℂ) (halpha0 : alpha ≠ 0) (halpha : IsAlgebraic ℚ alpha)
    (hznot : ∀ q : ℚ, z ≠ q • alpha)
    (hz : IsAlgebraic (relativeExponentialBase alpha) z)
    (hexpz : IsAlgebraic (relativeExponentialBase alpha) (Complex.exp z)) :
    ¬ SchanuelExtractionAt 2 := by
  intro hS
  let x : Fin 2 → ℂ := ![alpha, z]
  have hx : LinearIndependent ℚ x := by
    rw [Fintype.linearIndependent_iff]
    intro q hq i
    rw [Fin.sum_univ_two] at hq
    simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hq
    have hq1 : q 1 = 0 := by
      by_contra hq1
      apply hznot (-(q 0) / q 1)
      rw [Rat.smul_def]
      have hq1C : (q 1 : ℂ) ≠ 0 := by exact_mod_cast hq1
      calc
        z = -(q 0 : ℂ) * alpha / (q 1 : ℂ) := by
          apply (eq_div_iff hq1C).2
          linear_combination hq
        _ = ((-(q 0) / q 1 : ℚ) : ℂ) * alpha := by
          push_cast
          field_simp
    have hq0 : q 0 = 0 := by
      rw [hq1, Rat.cast_zero, zero_mul, add_zero] at hq
      have hq0C : (q 0 : ℂ) = 0 :=
        (mul_eq_zero.mp hq).resolve_right halpha0
      exact_mod_cast hq0C
    fin_cases i
    · exact hq0
    · exact hq1
  obtain ⟨t, _, htmem, htind⟩ := hS x hx
  apply not_algebraicIndependent_fin_two_of_isAlgebraic_relativeExponentialBase
    alpha t
  · intro i
    rcases htmem i with ht | ht
    · obtain ⟨j, hj⟩ := ht
      rw [← hj]
      fin_cases j
      · have halphaA : alpha ∈ algebraicClosure ℚ ℂ :=
          mem_algebraicClosure_iff.mpr halpha
        let aA : algebraicClosure ℚ ℂ := ⟨alpha, halphaA⟩
        have ha := isAlgebraic_algebraMap
          (R := relativeExponentialBase alpha) (A := ℂ)
          (⟨alpha, (relativeExponentialBase alpha).algebraMap_mem aA⟩ :
            relativeExponentialBase alpha)
        simpa [x, aA] using ha
      · simpa [x] using hz
    · obtain ⟨j, hj⟩ := ht
      rw [← hj]
      fin_cases j
      · have hexpMem : Complex.exp alpha ∈ relativeExponentialBase alpha := by
          exact IntermediateField.subset_adjoin _ _ ⟨(), rfl⟩
        have he := isAlgebraic_algebraMap
          (R := relativeExponentialBase alpha) (A := ℂ)
          (⟨Complex.exp alpha, hexpMem⟩ : relativeExponentialBase alpha)
        simpa [x] using he
      · simpa [x] using hexpz
  · letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
      algebraicClosure.isAlgebraic ℚ ℂ
    exact htind.extendScalars (algebraicClosure ℚ ℂ)

end

end GaloisForLFunctions.RHTower
