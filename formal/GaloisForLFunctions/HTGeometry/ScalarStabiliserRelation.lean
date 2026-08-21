import GaloisForLFunctions.HTGeometry.IdentityTangentSubmodule
import GaloisForLFunctions.HTGeometry.AdditiveDifferentialSubgroupLinear

/-!
# The scalars scaling a tangent direction back into the tangent space

`cassidy_sl2_of_differentialSolution` asks that for each nonzero `Y` in the Lie algebra the scalars
`c` with `c·Y` again in it solve a *monic* scalar linear differential equation.  Those scalars form
an additive subgroup, because the Lie algebra is a module over the constants and scaling is additive
in the scalar; and a nonzero linear relation among jets becomes monic on dividing by the coefficient
of the highest jet that occurs.

* `scalarStabiliser` — the additive subgroup of such scalars;
* `exists_monic_relation_of_linear` — a nonzero linear jet relation becomes a monic one;
* `exists_monic_relation_scalarStabiliser`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]

/-- **A nonzero linear jet relation can be made monic.** -/
theorem exists_monic_relation_of_linear :
    ∀ (n : ℕ) (b : Fin (n + 1) → C), (∃ i, b i ≠ 0) →
      ∀ {T : Set C}, (∀ v ∈ T, ∑ i : Fin (n + 1), b i * differentialJet (i : ℕ) v = 0) →
      ∃ (m : ℕ) (a : Fin m → C), ∀ v ∈ T,
        differentialJet m v = ∑ i : Fin m, a i * differentialJet (i : ℕ) v
  | 0, b, hb, T, hT => by
      refine ⟨0, fun i => i.elim0, fun v hv => ?_⟩
      have h := hT v hv
      rw [Fin.sum_univ_one] at h
      have hb0 : b 0 ≠ 0 := by
        obtain ⟨i, hi⟩ := hb
        have hi0 : i = 0 := Fin.ext (by omega)
        rwa [hi0] at hi
      have hz : differentialJet 0 v = 0 := (mul_eq_zero.mp h).resolve_left hb0
      rw [hz]
      simp
  | (n + 1), b, hb, T, hT => by
      by_cases hlast : b (Fin.last (n + 1)) = 0
      · refine exists_monic_relation_of_linear n (fun i => b i.castSucc) ?_ ?_
        · obtain ⟨i, hi⟩ := hb
          have hine : i ≠ Fin.last (n + 1) := by
            intro h0
            exact hi (by rw [h0, hlast])
          obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hine
          exact ⟨j, hi⟩
        · intro v hv
          have h := hT v hv
          rw [Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at h
          simpa only [Fin.val_castSucc] using h
      · refine ⟨n + 1, fun i => -(b i.castSucc / b (Fin.last (n + 1))), fun v hv => ?_⟩
        have h := hT v hv
        rw [Fin.sum_univ_castSucc, Fin.val_last] at h
        simp only [Fin.val_castSucc] at h
        refine mul_right_cancel₀ hlast ?_
        rw [Finset.sum_mul]
        have hterm : ∀ i : Fin (n + 1),
            -(b i.castSucc / b (Fin.last (n + 1))) * differentialJet (i : ℕ) v
              * b (Fin.last (n + 1)) = -(b i.castSucc * differentialJet (i : ℕ) v) := by
          intro i
          field_simp
        rw [Finset.sum_congr rfl fun i _ => hterm i]
        simp only [Finset.sum_neg_distrib]
        linear_combination h

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- The scalars scaling `Y` back into the tangent space at the identity. -/
def scalarStabiliser (Y : Matrix (Fin 2) (Fin 2) C) : AddSubgroup C where
  carrier := {c : C | (fun q : Fin 2 × Fin 2 => c * Y q.1 q.2) ∈ matrixTangent S}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zero_mul]
    exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hsum := Submodule.add_mem (matrixTangent S) ha hb
    convert hsum using 1
    funext q
    show (a + b) * Y q.1 q.2 = a * Y q.1 q.2 + b * Y q.1 q.2
    ring
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hneg := Submodule.neg_mem (matrixTangent S) ha
    convert hneg using 1
    funext q
    show (-a) * Y q.1 q.2 = -(a * Y q.1 q.2)
    ring

@[simp] theorem mem_scalarStabiliser {Y : Matrix (Fin 2) (Fin 2) C} {c : C} :
    c ∈ scalarStabiliser S Y
      ↔ (fun q : Fin 2 × Fin 2 => c * Y q.1 q.2) ∈ matrixTangent S := Iff.rfl

variable [CharZero C]

/-- **The scalar stabiliser satisfies a monic linear differential equation** as soon as it lies in
the zero set of one nonzero differential polynomial in one indeterminate. -/
theorem exists_monic_relation_scalarStabiliser (Y : Matrix (Fin 2) (Fin 2) C)
    {P : DifferentialPolynomial Unit C} (hP : P ≠ 0)
    (hPT : ∀ c ∈ scalarStabiliser S Y,
      differentialPolynomialEvalOver (K := C) (fun _ : Unit => c) P = 0) :
    ∃ (m : ℕ) (a : Fin m → C), ∀ c ∈ scalarStabiliser S Y,
      differentialJet m c = ∑ i : Fin m, a i * differentialJet (i : ℕ) c := by
  obtain ⟨n, b, hb, hrel⟩ :=
    exists_nonzero_linear_jet_relation_of_addSubgroup (scalarStabiliser S Y) hP hPT
  exact exists_monic_relation_of_linear n b hb hrel

end

end GaloisForLFunctions.HTGeometry
