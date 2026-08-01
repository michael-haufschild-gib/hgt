import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A rational base for a finite family of real frequencies

Every finite family of real numbers is a family of *integer* combinations of finitely many
`ℚ`-linearly independent reals: extract a maximal independent subfamily, express each member as a
rational combination of it, and divide the base by a common denominator.

This is the input the Bochner–Fejér construction needs — the multi-dimensional Fejér kernel is built
over a `ℚ`-independent base and its frequencies are the *integer* combinations of that base, so a
trigonometric polynomial can be reached by such a kernel only after its frequencies have been
written in this form.
-/

namespace GaloisForLFunctions

/-- Rescaling a family by a nonzero real preserves `ℚ`-linear independence. -/
theorem linearIndependent_const_mul {ι : Type*} {v : ι → ℝ} (h : LinearIndependent ℚ v) {c : ℝ}
    (hc : c ≠ 0) : LinearIndependent ℚ fun i => c * v i := by
  rw [linearIndependent_iff'] at h ⊢
  intro s g hsum i hi
  refine h s g ?_ i hi
  have hrw : ∑ j ∈ s, g j • v j = c⁻¹ * ∑ j ∈ s, g j • (c * v j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Rat.smul_def, Rat.smul_def]
    field_simp
  rw [hrw, hsum, mul_zero]

/-- Multiplying a rational by a multiple of its denominator gives an integer. -/
theorem exists_int_nat_mul (q : ℚ) {d : ℕ} (hd : q.den ∣ d) : ∃ z : ℤ, (d : ℚ) * q = z := by
  obtain ⟨e, he⟩ := hd
  refine ⟨e * q.num, ?_⟩
  have h1 : (q.den : ℚ) * q = (q.num : ℚ) := by
    rw [mul_comm]
    exact_mod_cast Rat.mul_den_eq_num q
  rw [he]
  push_cast
  rw [mul_comm (q.den : ℚ) (e : ℚ), mul_assoc, h1]

/-- **A rational base with integer coordinates.**  Any finite family of reals consists of integer
combinations of a finite `ℚ`-linearly independent family. -/
theorem exists_ratBasis_int_combination {n : ℕ} (lam : Fin n → ℝ) :
    ∃ (k : ℕ) (β : Fin k → ℝ) (m : Fin n → Fin k → ℤ),
      LinearIndependent ℚ β ∧ ∀ j, lam j = ∑ i, (m j i : ℝ) * β i := by
  classical
  obtain ⟨b, hbsub, hspan, hind⟩ := exists_linearIndependent ℚ (Set.range lam)
  have hbfin : b.Finite := (Set.finite_range lam).subset hbsub
  haveI : Fintype b := hbfin.fintype
  set k : ℕ := Fintype.card b with hk
  set e : b ≃ Fin k := Fintype.equivFin b with he
  set b0 : Fin k → ℝ := fun i => (e.symm i : ℝ) with hb0
  have hb0ind : LinearIndependent ℚ b0 := hind.comp e.symm e.symm.injective
  have hrange : Set.range b0 = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [hb0]⟩
  have hmem : ∀ j, lam j ∈ Submodule.span ℚ (Set.range b0) := by
    intro j
    rw [hrange, hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hmem j)
  set D : ℕ := ∏ p : Fin n × Fin k, (c p.1 p.2).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun p _ => (c p.1 p.2).pos
  have hDne : (D : ℝ) ≠ 0 := by
    have : (0 : ℝ) < D := by exact_mod_cast hDpos
    exact ne_of_gt this
  have hdvd : ∀ (j : Fin n) (i : Fin k), (c j i).den ∣ D := by
    intro j i
    exact Finset.dvd_prod_of_mem (fun p : Fin n × Fin k => (c p.1 p.2).den)
      (Finset.mem_univ (j, i))
  choose m hm using fun (j : Fin n) (i : Fin k) => exists_int_nat_mul (c j i) (hdvd j i)
  refine ⟨k, fun i => (D : ℝ)⁻¹ * b0 i, m,
    linearIndependent_const_mul hb0ind (inv_ne_zero hDne), fun j => ?_⟩
  rw [← hc j]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcast : ((m j i : ℤ) : ℝ) = (D : ℝ) * ((c j i : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (hm j i)
    push_cast at this
    exact this.symm
  rw [Rat.smul_def, hcast]
  field_simp

end GaloisForLFunctions
