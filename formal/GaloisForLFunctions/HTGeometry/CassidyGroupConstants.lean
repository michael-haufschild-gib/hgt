import GaloisForLFunctions.HTGeometry.CassidyTangentDichotomy
import GaloisForLFunctions.HTGeometry.Sl2ConstantNormaliser
import GaloisForLFunctions.HTGeometry.FiniteConstantSpanOperator

/-!
# The group step of Cassidy's classification

`cassidy_tangent_dichotomy` puts the Lie algebra of a differential algebraic subgroup of `SL₂` into
one of two shapes.  In the second shape one conjugation carries it onto `sl₂` over the constants;
this module carries that conclusion from the Lie algebra to the *group*.

The mechanism needs no exponential map.  The Lie algebra of a differential algebraic subgroup is
stable under the adjoint action of the group, so after the conjugation every group element
normalises `sl₂` over the constants — and a determinant-one matrix normalising `sl₂(K)` for a
square-root-closed `K` has all its entries in `K` (`entries_mem_of_conj_sl2`).

Undoing the conjugation puts every entry of every group element in the `K`-span of the sixteen
products `Q i k · P l j`, a space of dimension at most sixteen over the constants, so
`exists_nonzero_linearJet_relation_of_span` produces one nonzero linear differential operator
annihilating every entry of every group element — the hypothesis `hGL` of
`isomonodromy_of_no_riccati_of_linearRelation`.

* `entries_mem_of_mem_span_sl2`;
* `conj_entries_mem_constants` — the group step;
* `entries_mem_span_of_conj_constants`, `exists_linearJet_relation_of_conj_constants`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]

/-- Every entry of an element of the constant span of `h`, `e`, `f` is a constant. -/
theorem entries_mem_of_mem_span_sl2 {Z : Matrix (Fin 2) (Fin 2) C}
    (hZ : Z ∈ Submodule.span (differentialConstants C) {sl2H C, sl2E C, sl2F C}) :
    ∀ i j, Z i j ∈ differentialConstants C := by
  induction hZ using Submodule.span_induction with
  | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp only [sl2H_00, sl2H_01, sl2H_10, sl2H_11]
        · exact (differentialConstants C).one_mem
        · exact (differentialConstants C).zero_mem
        · exact (differentialConstants C).zero_mem
        · exact (differentialConstants C).neg_mem (differentialConstants C).one_mem
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp only [sl2E_00, sl2E_01, sl2E_10, sl2E_11]
        · exact (differentialConstants C).zero_mem
        · exact (differentialConstants C).one_mem
        · exact (differentialConstants C).zero_mem
        · exact (differentialConstants C).zero_mem
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp only [sl2F_00, sl2F_01, sl2F_10, sl2F_11]
        · exact (differentialConstants C).zero_mem
        · exact (differentialConstants C).zero_mem
        · exact (differentialConstants C).one_mem
        · exact (differentialConstants C).zero_mem
  | zero => intro i j; simpa using (differentialConstants C).zero_mem
  | add x y _ _ hx hy =>
      intro i j
      rw [Matrix.add_apply]
      exact (differentialConstants C).add_mem (hx i j) (hy i j)
  | smul c x _ hx =>
      intro i j
      rw [Matrix.smul_apply]
      exact (differentialConstants C).mul_mem c.2 (hx i j)

/-- The constants of a differential field with algebraically closed constants are closed under
square roots. -/
theorem sq_root_mem_differentialConstants [IsAlgClosed (differentialConstants C)]
    (x : C) (hx : x ∈ differentialConstants C) :
    ∃ y ∈ differentialConstants C, y * y = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (⟨x, hx⟩ : differentialConstants C) (n := 2) (by norm_num)
  refine ⟨(z : C), z.2, ?_⟩
  have := congrArg (fun t : differentialConstants C => (t : C)) hz
  simpa [pow_two] using this

/-- **The group step.**  If one conjugation carries the Lie algebra onto `sl₂` over the constants,
then every determinant-one element of the group has constant entries after that conjugation. -/
theorem conj_entries_mem_constants [IsAlgClosed C] [CharZero C]
    [IsAlgClosed (differentialConstants C)]
    {L : Submodule (differentialConstants C) (Matrix (Fin 2) (Fin 2) C)}
    {P Q : Matrix (Fin 2) (Fin 2) C} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hLconj : L.map (conjLinear (differentialConstants C) P Q)
      = Submodule.span (differentialConstants C) {sl2H C, sl2E C, sl2F C})
    {g g' : Matrix (Fin 2) (Fin 2) C} (hgg' : g * g' = 1) (hdet : g.det = 1)
    (hAd : ∀ A ∈ L, g * A * g' ∈ L) :
    ∀ i j, (P * g * Q) i j ∈ differentialConstants C := by
  classical
  set K := differentialConstants C with hK
  set gc : Matrix (Fin 2) (Fin 2) C := P * g * Q with hgc
  set gc' : Matrix (Fin 2) (Fin 2) C := P * g' * Q with hgc'
  have hconj : ∀ A B : Matrix (Fin 2) (Fin 2) C,
      (P * A * Q) * (P * B * Q) = P * (A * B) * Q := conj_mul_conj hQP
  have hgcgc' : gc * gc' = 1 := by
    rw [hgc, hgc', hconj, hgg', Matrix.mul_one, hPQ]
  have hdetPQ : P.det * Q.det = 1 := by
    have h := congrArg Matrix.det hPQ
    rwa [Matrix.det_mul, Matrix.det_one] at h
  have hdetgc : gc.det = 1 := by
    rw [hgc, Matrix.det_mul, Matrix.det_mul, hdet]
    calc P.det * 1 * Q.det = P.det * Q.det := by ring
      _ = 1 := hdetPQ
  have hadjgc : Matrix.adjugate gc = gc' := by
    have h1 : gc' * gc = 1 := mul_eq_one_comm.mp hgcgc'
    have h2 : gc * Matrix.adjugate gc = gc.det • (1 : Matrix (Fin 2) (Fin 2) C) :=
      Matrix.mul_adjugate gc
    rw [hdetgc, one_smul] at h2
    calc Matrix.adjugate gc = (gc' * gc) * Matrix.adjugate gc := by rw [h1, Matrix.one_mul]
      _ = gc' * (gc * Matrix.adjugate gc) := by rw [Matrix.mul_assoc]
      _ = gc' := by rw [h2, Matrix.mul_one]
  -- the adjoint action of the conjugated element preserves the constant span
  have hstab : ∀ A ∈ Submodule.span K {sl2H C, sl2E C, sl2F C},
      gc * A * gc' ∈ Submodule.span K {sl2H C, sl2E C, sl2F C} := by
    intro A hA
    rw [← hLconj] at hA ⊢
    obtain ⟨A₀, hA₀, hA₀eq⟩ := Submodule.mem_map.mp hA
    refine Submodule.mem_map.mpr ⟨g * A₀ * g', hAd A₀ hA₀, ?_⟩
    have hA' : A = P * A₀ * Q := hA₀eq.symm
    rw [hA', hgc, hgc', hconj, hconj]
    rfl
  have hmemE : sl2E C ∈ Submodule.span K {sl2H C, sl2E C, sl2F C} :=
    Submodule.subset_span (by simp)
  have hmemF : sl2F C ∈ Submodule.span K {sl2H C, sl2E C, sl2F C} :=
    Submodule.subset_span (by simp)
  have hmemH : sl2H C ∈ Submodule.span K {sl2H C, sl2E C, sl2F C} :=
    Submodule.subset_span (by simp)
  refine entries_mem_of_conj_sl2 K (sq_root_mem_differentialConstants) hdetgc ?_ ?_ ?_
  · rw [hadjgc]; exact fun i j => entries_mem_of_mem_span_sl2 (hstab _ hmemE) i j
  · rw [hadjgc]; exact fun i j => entries_mem_of_mem_span_sl2 (hstab _ hmemF) i j
  · rw [hadjgc]; exact fun i j => entries_mem_of_mem_span_sl2 (hstab _ hmemH) i j

end

end GaloisForLFunctions.HTGeometry
