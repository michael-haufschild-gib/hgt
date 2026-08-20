import GaloisForLFunctions.HTGeometry.DifferentialFieldExtension
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange

/-!
# Finitely many consistent differential systems are jointly solvable

Extending the coefficients of a differential ideal keeps it differential and, over a field, keeps it
proper; its radical is then a proper radical differential ideal over the extension, so a system
consistent over the base stays solvable one extension further up.

Iterating that over a finite family — solving the next system over the field already built, and
pushing the solutions found so far forward — puts solutions of all of them in a single differential
field extension.  This is the finite consistency statement a differential closure rests on.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable {F : Type u} [Field F] [Algebra ℚ F] [Differential F]

variable {ι : Type u}

omit [Algebra ℚ F] in
/-- The coefficient extension of a differential ideal is again differential. -/
theorem deriv_mem_map_differentialCoeffExtend {L : Type u} [Field L] [Differential L] [Algebra F L]
    (hcompat : ∀ a : F, Differential.deriv (algebraMap F L a)
      = algebraMap F L (Differential.deriv a))
    {I : Ideal (DifferentialPolynomial ι F)}
    (hδ : ∀ x ∈ I, differentialPolynomialOverDerivation ι F x ∈ I) :
    ∀ z ∈ Ideal.map (differentialCoeffExtend (ι := ι) (F := F) (L := L)) I,
      differentialPolynomialOverDerivation ι L z
        ∈ Ideal.map (differentialCoeffExtend (ι := ι) (F := F) (L := L)) I := by
  intro z hz
  set J : Ideal (DifferentialPolynomial ι L) :=
    Ideal.map (differentialCoeffExtend (ι := ι) (F := F) (L := L)) I with hJ
  have hzz : z ∈ Ideal.span
      ((differentialCoeffExtend (ι := ι) (F := F) (L := L)) '' (I : Set _)) := hz
  refine Submodule.span_induction
    (p := fun w _ => differentialPolynomialOverDerivation ι L w ∈ J) ?_ ?_ ?_ ?_ hzz
  · rintro w ⟨x, hx, rfl⟩
    have hcomm := differentialCoeffExtend_deriv (ι := ι) (F := F) (L := L) hcompat x
    rw [← hcomm]
    exact Ideal.mem_map_of_mem _ (hδ x hx)
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]
    exact add_mem ha hb
  · intro a w hw hderiv
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    refine add_mem (Ideal.mul_mem_left _ _ hderiv) (Ideal.mul_mem_right _ _ hw)

/-- **A consistent system has a solution in a differential extension of any given extension.** -/
theorem exists_point_over_ext (E : DiffFieldExt F) {I : Ideal (DifferentialPolynomial ι F)}
    (hδ : ∀ x ∈ I, differentialPolynomialOverDerivation ι F x ∈ I) (hne : I ≠ ⊤) :
    ∃ (M : DiffFieldExt E.carrier) (y : ι → M.carrier),
      ∀ p ∈ I, differentialPolynomialEvalOver (K := E.carrier) y
        (differentialCoeffExtend (ι := ι) (F := F) (L := E.carrier) p) = 0 := by
  classical
  set J : Ideal (DifferentialPolynomial ι E.carrier) :=
    Ideal.map (differentialCoeffExtend (ι := ι) (F := F) (L := E.carrier)) I with hJ
  have hJne : J ≠ ⊤ := map_ne_top_of_ne_top (E := E.carrier) (σ := ι × ℕ) hne
  have hJδ := deriv_mem_map_differentialCoeffExtend (L := E.carrier) E.compat hδ
  have hradne : J.radical ≠ ⊤ := by
    intro htop
    exact hJne (Ideal.radical_eq_top.mp htop)
  have hradrad : J.radical.IsRadical := Ideal.radical_isRadical J
  have hradδ : ∀ x ∈ J.radical, differentialPolynomialOverDerivation ι E.carrier x ∈ J.radical := by
    letI : Differential (DifferentialPolynomial ι E.carrier) :=
      differentialPolynomialOverDifferential ι E.carrier
    intro x hx
    exact deriv_mem_radical (I := J) hJδ hx
  obtain ⟨L', hL'field, hL'diff, hL'alg, hL'compat, y, hy⟩ :=
    exists_point_of_ne_top (F := E.carrier) (ι := ι) hradrad hradδ hradne
  letI := hL'field
  letI := hL'diff
  letI := hL'alg
  letI : Algebra ℚ L' := ((algebraMap E.carrier L').comp (algebraMap ℚ E.carrier)).toAlgebra
  refine ⟨⟨L', hL'compat⟩, y, ?_⟩
  intro p hp
  exact hy _ (Ideal.le_radical (Ideal.mem_map_of_mem _ hp))

/-- **Finitely many consistent systems are jointly solvable** in a single differential field
extension. -/
theorem exists_jointExt : ∀ (k : ℕ) (ιf : Fin k → Type u)
    (I : ∀ j, Ideal (DifferentialPolynomial (ιf j) F)),
    (∀ j, ∀ x ∈ I j, differentialPolynomialOverDerivation (ιf j) F x ∈ I j) →
    (∀ j, I j ≠ ⊤) →
    ∃ (E : DiffFieldExt F) (y : ∀ j, ιf j → E.carrier),
      ∀ j, ∀ p ∈ I j, differentialPolynomialEvalOver (K := F) (y j) p = 0 := by
  intro k
  induction k with
  | zero =>
      intro ιf I _ _
      exact ⟨DiffFieldExt.refl, fun j => j.elim0, fun j => j.elim0⟩
  | succ k ih =>
      intro ιf I hδ hne
      obtain ⟨E, y, hy⟩ := ih (fun j => ιf j.castSucc) (fun j => I j.castSucc)
        (fun j => hδ j.castSucc) (fun j => hne j.castSucc)
      obtain ⟨M, z, hz⟩ :=
        exists_point_over_ext E (I := I (Fin.last k)) (hδ (Fin.last k)) (hne (Fin.last k))
      letI : Algebra F M.carrier :=
        ((algebraMap E.carrier M.carrier).comp (algebraMap F E.carrier)).toAlgebra
      haveI htower : IsScalarTower F E.carrier M.carrier :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hFM : ∀ a : F, algebraMap F M.carrier a
          = algebraMap E.carrier M.carrier (algebraMap F E.carrier a) := fun _ => rfl
      have hcompatFM : ∀ a : F, Differential.deriv (algebraMap F M.carrier a)
          = algebraMap F M.carrier (Differential.deriv a) := by
        intro a
        rw [hFM, hFM, M.compat, E.compat]
      obtain ⟨y', hylast, hycast⟩ : ∃ y' : ∀ j, ιf j → M.carrier,
          y' (Fin.last k) = z ∧
            ∀ j : Fin k, y' j.castSucc = fun i => algebraMap E.carrier M.carrier (y j i) := by
        refine ⟨Fin.lastCases z fun j i => algebraMap E.carrier M.carrier (y j i), ?_, fun j => ?_⟩
        · exact Fin.lastCases_last
        · exact Fin.lastCases_castSucc j
      refine ⟨⟨M.carrier, hcompatFM⟩, y', ?_⟩
      refine Fin.lastCases ?_ ?_
      · intro p hp
        rw [hylast]
        rw [← differentialPolynomialEvalOver_differentialCoeffExtend (F := F) (L := E.carrier)
          (M := M.carrier) z p]
        exact hz p hp
      · intro j p hp
        rw [hycast j]
        have hφδ : ∀ x : E.carrier, algebraMap E.carrier M.carrier (Differential.deriv x)
            = Differential.deriv (algebraMap E.carrier M.carrier x) := fun x => (M.compat x).symm
        have hφF : ∀ a : F, algebraMap E.carrier M.carrier (algebraMap F E.carrier a)
            = algebraMap F M.carrier a := fun a => (hFM a).symm
        have hmapped := map_differentialPolynomialEvalOver (F := F) (L := E.carrier)
          (M := M.carrier) (algebraMap E.carrier M.carrier) hφδ hφF (y j) p
        rw [← hmapped, hy j p hp, map_zero]

end

end GaloisForLFunctions.HTGeometry
