import GaloisForLFunctions.HTGeometry.TraceDualBasisSeparability

/-!
# The idempotent attached to a section of an étale algebra

Let `B` be a finite free `A`-algebra with a basis `e` whose discriminant is a unit, and let
`ψ : B →ₐ[A] A` be a section.  Since the trace form is nondegenerate, `ψ` is represented by a unique
element,

```text
ε := ∑ᵢ ψ(eᵢ) • fᵢ ,        Tr(ε b) = ψ b   for all b,
```

where `f` is the trace-dual basis.  Two identities make `ε` the idempotent cutting out the section:

```text
ε * b = ψ b • ε          (expand ε b in the dual basis)
ψ ε = 1                  (apply ψ to  ∑ᵢ eᵢ fᵢ = 1)
```

so `ε * ε = ψ ε • ε = ε`.  Both are three-line computations — no reduction to fibres, no infinite
base field, no localisation.

This is the geometric statement that a section of a finite étale cover is an open and closed
immersion, in the only form the algebraic induction needs.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B]
  {n : ℕ} (e : Module.Basis (Fin n) A B) (hd : IsUnit (Algebra.discr A e))

include hd in
theorem trace_traceDual_mul (x : B) (i : Fin n) :
    Algebra.trace A B (traceDual e i * x) = e.repr x i := by
  classical
  set c : Fin n → A := fun j => e.repr x j with hc
  have hx : x = ∑ j, c j • e j := (e.sum_repr x).symm
  have hci : e.repr x i = c i := rfl
  rw [hci]
  conv_lhs => rw [hx]
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single i]
  · rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, mul_comm (traceDual e i) (e i),
      trace_mul_traceDual e hd i i, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, mul_comm (traceDual e i) (e j),
      trace_mul_traceDual e hd j i, if_neg hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

include hd in
theorem dual_expansion (x : B) :
    x = ∑ i, (Algebra.trace A B (traceDual e i * x)) • e i := by
  simp only [trace_traceDual_mul e hd]
  exact (e.sum_repr x).symm

include hd in
theorem dual_expansion' (x : B) :
    x = ∑ i, (Algebra.trace A B (e i * x)) • traceDual e i := by
  classical
  have hz : x - ∑ i, (Algebra.trace A B (e i * x)) • traceDual e i = 0 := by
    refine eq_zero_of_trace_basis_mul_eq_zero e hd (fun k => ?_)
    rw [mul_sub, map_sub, sub_eq_zero, Finset.mul_sum, map_sum, Finset.sum_eq_single k]
    · rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, trace_mul_traceDual e hd k k,
        if_pos rfl, mul_one]
    · intro j _ hj
      rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, trace_mul_traceDual e hd k j,
        if_neg (Ne.symm hj), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  exact sub_eq_zero.mp hz

variable (ψ : B →ₐ[A] A)

/-- The idempotent attached to a section of a finite free algebra with unit discriminant. -/
noncomputable def sectionIdem : B := ∑ i, ψ (e i) • traceDual e i

include hd in
theorem trace_sectionIdem_mul (b : B) :
    Algebra.trace A B (sectionIdem e ψ * b) = ψ b := by
  classical
  rw [sectionIdem, Finset.sum_mul, map_sum]
  have hstep : ∀ i : Fin n, Algebra.trace A B ((ψ (e i) • traceDual e i) * b)
      = ψ (e i) * Algebra.trace A B (traceDual e i * b) := by
    intro i
    rw [Algebra.smul_mul_assoc, map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  conv_rhs => rw [dual_expansion e hd b]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]

include hd in
theorem sectionIdem_mul (b : B) :
    sectionIdem e ψ * b = ψ b • sectionIdem e ψ := by
  classical
  set ε := sectionIdem e ψ with hε
  have hcoef : ∀ j : Fin n, Algebra.trace A B (e j * (ε * b)) = ψ b * ψ (e j) := by
    intro j
    rw [← mul_assoc, mul_comm (e j) ε, mul_assoc, hε, trace_sectionIdem_mul e hd ψ, map_mul,
      mul_comm]
  have hR : ψ b • ε = ∑ i, (ψ b * ψ (e i)) • traceDual e i := by
    rw [hε, sectionIdem, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul])
  rw [hR]
  conv_lhs => rw [dual_expansion' e hd (ε * b)]
  exact Finset.sum_congr rfl (fun i _ => by rw [hcoef i])

include hd in
theorem apply_sectionIdem : ψ (sectionIdem e ψ) = 1 := by
  have h1 : ψ (sectionIdem e ψ) = ∑ i, ψ (e i) * ψ (traceDual e i) := by
    rw [sectionIdem, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])
  have h2 : (1 : A) = ∑ i, ψ (e i) * ψ (traceDual e i) := by
    rw [← map_one ψ, ← sum_mul_traceDual e hd, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul])
  rw [h1, ← h2]

include hd in
theorem sectionIdem_idem : sectionIdem e ψ * sectionIdem e ψ = sectionIdem e ψ := by
  rw [sectionIdem_mul e hd ψ, apply_sectionIdem e hd ψ, one_smul]

include hd in
theorem trace_sectionIdem : Algebra.trace A B (sectionIdem e ψ) = 1 := by
  have := trace_sectionIdem_mul e hd ψ 1
  rwa [mul_one, map_one] at this

end GaloisForLFunctions.HTGeometry
