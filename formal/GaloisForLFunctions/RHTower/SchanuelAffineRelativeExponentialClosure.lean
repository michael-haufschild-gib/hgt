import GaloisForLFunctions.RHTower.SchanuelStageWitnesses
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg
import GaloisForLFunctions.HTGeometry.FiniteLindemannWeierstrass

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

/-- Two complex numbers form a rationally independent pair when the first is nonzero and the
second is not a rational multiple of it. -/
theorem linearIndependent_fin_two_of_ne_zero_of_not_rat_smul
    (alpha z : ℂ) (halpha0 : alpha ≠ 0)
    (hznot : ∀ q : ℚ, z ≠ q • alpha) :
    LinearIndependent ℚ ![alpha, z] := by
  rw [Fintype.linearIndependent_iff]
  intro q hq i
  rw [Fin.sum_univ_two] at hq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hq
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

/-- A second element transcendental over `Qbar(exp(alpha))` is jointly algebraically independent
with `exp(alpha)` over `Qbar`. -/
theorem algebraicIndependent_exp_and_of_transcendental_relativeExponentialBase
    (alpha w : ℂ) (halpha0 : alpha ≠ 0) (halpha : IsAlgebraic ℚ alpha)
    (hw : Transcendental (relativeExponentialBase alpha) w) :
    AlgebraicIndependent (algebraicClosure ℚ ℂ) ![Complex.exp alpha, w] := by
  have hexpQ : Transcendental ℚ (Complex.exp alpha) :=
    exp_algebraic_transcendental
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr halpha) halpha0
  letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  have hexpA : Transcendental (algebraicClosure ℚ ℂ) (Complex.exp alpha) :=
    hexpQ.extendScalars (algebraicClosure ℚ ℂ)
  let base : Unit → ℂ := fun _ => Complex.exp alpha
  have hbase : AlgebraicIndependent (algebraicClosure ℚ ℂ) base := by
    rw [algebraicIndependent_unique_type_iff]
    exact hexpA
  have hwAdjoin : Transcendental
      (Algebra.adjoin (algebraicClosure ℚ ℂ)
        (Set.range (fun _ : Unit => Complex.exp alpha))) w := by
    rw [← IntermediateField.transcendental_adjoin_iff]
    exact hw
  have hopt : AlgebraicIndependent (algebraicClosure ℚ ℂ)
      (fun o : Option Unit => o.elim w base) :=
    (hbase.option_iff_transcendental w).mpr (by simpa [base] using hwAdjoin)
  let f : Fin 2 → Option Unit := ![some (), none]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hcomp := hopt.comp f hf
  have heq : ((fun o : Option Unit => o.elim w base) ∘ f) =
      ![Complex.exp alpha, w] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hcomp
  exact hcomp

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

/-- **Exact normalized affine equivalence.** For nonzero algebraic `alpha`, the four-element
family `alpha, z, exp alpha, exp z` has no two-element algebraically independent extraction exactly
when both `z` and `exp z` are algebraic over `Qbar(exp alpha)`.  Rational independence is not needed
for this field-theoretic equivalence; it is needed only to make the pair a Schanuel input. -/
theorem relativeExponentialBase_edge_iff_no_affine_stageTwo_extraction
    (alpha z : ℂ) (halpha0 : alpha ≠ 0) (halpha : IsAlgebraic ℚ alpha) :
    (IsAlgebraic (relativeExponentialBase alpha) z ∧
        IsAlgebraic (relativeExponentialBase alpha) (Complex.exp z)) ↔
      ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ Set.range (![alpha, z] : Fin 2 → ℂ) ∪
          Set.range (fun j : Fin 2 => Complex.exp ((![alpha, z] : Fin 2 → ℂ) j))) ∧
        AlgebraicIndependent ℚ t := by
  constructor
  · rintro ⟨hz, hexpz⟩ ⟨t, _, htmem, htind⟩
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
          simpa [aA] using ha
        · exact hz
      · obtain ⟨j, hj⟩ := ht
        rw [← hj]
        fin_cases j
        · have hexpMem : Complex.exp alpha ∈ relativeExponentialBase alpha := by
            exact IntermediateField.subset_adjoin _ _ ⟨(), rfl⟩
          have he := isAlgebraic_algebraMap
            (R := relativeExponentialBase alpha) (A := ℂ)
            (⟨Complex.exp alpha, hexpMem⟩ : relativeExponentialBase alpha)
          simpa using he
        · exact hexpz
    · letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
        algebraicClosure.isAlgebraic ℚ ℂ
      exact htind.extendScalars (algebraicClosure ℚ ℂ)
  · intro hfail
    constructor
    · by_contra hzalg
      have hztrans : Transcendental (relativeExponentialBase alpha) z := hzalg
      have hindA :=
        algebraicIndependent_exp_and_of_transcendental_relativeExponentialBase
          alpha z halpha0 halpha hztrans
      have hindQ : AlgebraicIndependent ℚ ![Complex.exp alpha, z] :=
        hindA.restrictScalars (algebraMap ℚ (algebraicClosure ℚ ℂ)).injective
      apply hfail
      refine ⟨![Complex.exp alpha, z], hindQ.injective, ?_, hindQ⟩
      intro i
      fin_cases i
      · exact Or.inr ⟨0, rfl⟩
      · exact Or.inl ⟨1, rfl⟩
    · by_contra hexpzalg
      have hexpztrans : Transcendental (relativeExponentialBase alpha) (Complex.exp z) :=
        hexpzalg
      have hindA :=
        algebraicIndependent_exp_and_of_transcendental_relativeExponentialBase
          alpha (Complex.exp z) halpha0 halpha hexpztrans
      have hindQ : AlgebraicIndependent ℚ ![Complex.exp alpha, Complex.exp z] :=
        hindA.restrictScalars (algebraMap ℚ (algebraicClosure ℚ ℂ)).injective
      apply hfail
      refine ⟨![Complex.exp alpha, Complex.exp z], hindQ.injective, ?_, hindQ⟩
      intro i
      fin_cases i
      · exact Or.inr ⟨0, rfl⟩
      · exact Or.inr ⟨1, rfl⟩

/-- **Algebraic-vertex relative rigidity.** If `alpha` and `z` are algebraic, `alpha` is nonzero,
and `exp z` is algebraic over `Qbar(exp alpha)`, then `z` is a rational multiple of `alpha`.
Thus every genuine failure of relative exponential-edge rigidity has a transcendental second
vertex. -/
theorem exists_rat_smul_of_isAlgebraic_of_exp_isAlgebraic_relativeExponentialBase
    (alpha z : ℂ) (halpha0 : alpha ≠ 0)
    (halpha : IsAlgebraic ℚ alpha) (hz : IsAlgebraic ℚ z)
    (hexpz : IsAlgebraic (relativeExponentialBase alpha) (Complex.exp z)) :
    ∃ q : ℚ, z = q • alpha := by
  by_contra hnot
  push Not at hnot
  have hlin : LinearIndependent ℚ ![alpha, z] :=
    linearIndependent_fin_two_of_ne_zero_of_not_rat_smul alpha z halpha0 hnot
  have hexpQ : AlgebraicIndependent ℚ ![Complex.exp alpha, Complex.exp z] := by
    have heq : (fun j => Complex.exp (![alpha, z] j)) =
        ![Complex.exp alpha, Complex.exp z] := by
      funext j
      fin_cases j <;> rfl
    rw [← heq]
    exact exp_algebraicIndependent_of_linearIndependent ![alpha, z]
      (by
        intro i
        fin_cases i
        · exact halpha
        · exact hz)
      hlin
  letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  have hexpA : AlgebraicIndependent (algebraicClosure ℚ ℂ)
      ![Complex.exp alpha, Complex.exp z] :=
    hexpQ.extendScalars (algebraicClosure ℚ ℂ)
  apply not_algebraicIndependent_fin_two_of_isAlgebraic_relativeExponentialBase
    alpha ![Complex.exp alpha, Complex.exp z]
  · intro i
    fin_cases i
    · have hexpMem : Complex.exp alpha ∈ relativeExponentialBase alpha := by
        exact IntermediateField.subset_adjoin _ _ ⟨(), rfl⟩
      have he := isAlgebraic_algebraMap
        (R := relativeExponentialBase alpha) (A := ℂ)
        (⟨Complex.exp alpha, hexpMem⟩ : relativeExponentialBase alpha)
      simpa using he
    · exact hexpz
  · exact hexpA

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
    simpa [x] using
      linearIndependent_fin_two_of_ne_zero_of_not_rat_smul alpha z halpha0 hznot
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
