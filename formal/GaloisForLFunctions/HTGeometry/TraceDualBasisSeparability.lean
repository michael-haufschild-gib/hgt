import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The trace-dual basis, and the vanishing of derivations over the base

For a finite free algebra `B` over a commutative ring `A` with a basis `e` whose discriminant is a
unit, the Gram matrix of the trace form is invertible, so the dual basis `f` with
`Tr(eᵢ fⱼ) = δᵢⱼ` exists.  Two identities follow by pure matrix algebra:

```text
∑ᵢ eᵢ fᵢ = 1                       and       b fᵢ = ∑ⱼ (e.repr (b eⱼ) i) fⱼ
```

which together are the *separability idempotent* `∑ᵢ eᵢ ⊗ fᵢ` written without tensor products.
Their standard consequence is recorded here:

```text
derivation_eq_zero :  every A-derivation of B is zero
```

so a derivation of `A` has **at most one** lift to `B`.  This is the uniqueness half of the
derivation used by the multivariable simple connectedness of affine space; the corresponding
existence statement is a Hochschild-cocycle computation with the same two identities.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B]
  {n : ℕ} (e : Module.Basis (Fin n) A B)

/-- The dual basis of a basis with respect to the trace form. -/
noncomputable def traceDual (i : Fin n) : B :=
  ∑ j, (Algebra.traceMatrix A e)⁻¹ i j • e j

variable (hd : IsUnit (Algebra.discr A e))

include hd in
theorem isUnit_det_traceMatrix : IsUnit (Algebra.traceMatrix A e).det := hd

theorem traceMatrix_symm : (Algebra.traceMatrix A e)ᵀ = Algebra.traceMatrix A e := by
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]

theorem traceMatrix_inv_symm :
    ((Algebra.traceMatrix A e)⁻¹)ᵀ = (Algebra.traceMatrix A e)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, traceMatrix_symm]

theorem repr_sum_apply (c : Fin n → A) (i : Fin n) :
    e.repr (∑ j, c j • e j) i = c i := by
  classical
  rw [map_sum]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- Expansion of the trace of a product against a basis element. -/
theorem trace_mul_basis_repr (y : B) (i : Fin n) :
    Algebra.trace A B (e i * y) = ∑ j, Algebra.traceMatrix A e i j * e.repr y j := by
  conv_lhs => rw [← e.sum_repr y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, mul_comm]

include hd in
theorem eq_zero_of_trace_basis_mul_eq_zero {y : B}
    (h : ∀ i : Fin n, Algebra.trace A B (e i * y) = 0) : y = 0 := by
  classical
  set M := Algebra.traceMatrix A e with hM
  set c : Fin n → A := fun j => e.repr y j with hc
  have hmul : M *ᵥ c = 0 := by
    funext i
    rw [Matrix.mulVec, dotProduct]
    have := h i
    rw [trace_mul_basis_repr e y i] at this
    simpa [hc, hM] using this
  have hczero : c = 0 := by
    have h2 : M⁻¹ *ᵥ (M *ᵥ c) = M⁻¹ *ᵥ (0 : Fin n → A) := by rw [hmul]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_traceMatrix e hd),
      Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  have : e.repr y = 0 := by
    ext j
    exact congrFun hczero j
  simpa using congrArg e.repr.symm this

include hd in
theorem trace_mul_traceDual (i j : Fin n) :
    Algebra.trace A B (e i * traceDual e j) = if i = j then 1 else 0 := by
  classical
  rw [traceDual, Finset.mul_sum, map_sum]
  have hstep : ∀ k, Algebra.trace A B (e i * ((Algebra.traceMatrix A e)⁻¹ j k • e k)) =
      (Algebra.traceMatrix A e) i k * ((Algebra.traceMatrix A e)⁻¹)ᵀ k j := by
    intro k
    rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, mul_comm]
    rfl
  rw [Finset.sum_congr rfl (fun k _ => hstep k), traceMatrix_inv_symm e,
    ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_det_traceMatrix e hd), Matrix.one_apply]


include hd in
theorem trace_mul_sum_traceDual (x : B) :
    Algebra.trace A B (x * ∑ i, e i * traceDual e i) = Algebra.trace A B x := by
  classical
  rw [Finset.mul_sum, map_sum]
  have hstep : ∀ i : Fin n, Algebra.trace A B (x * (e i * traceDual e i)) =
      e.repr (x * e i) i := by
    intro i
    set c : Fin n → A := fun j => e.repr (x * e i) j with hc
    have hxe : x * e i = ∑ j, c j • e j := (e.sum_repr (x * e i)).symm
    rw [← mul_assoc, hxe, Finset.sum_mul, map_sum]
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_assoc, map_smul, smul_eq_mul, trace_mul_traceDual e hd i i, if_pos rfl,
        mul_one]
      rw [repr_sum_apply]
    · intro j _ hj
      rw [smul_mul_assoc, map_smul, smul_eq_mul, trace_mul_traceDual e hd j i, if_neg hj,
        mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [Algebra.trace_eq_matrix_trace e, Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]

include hd in
theorem sum_mul_traceDual : ∑ i, e i * traceDual e i = 1 := by
  have hz : (∑ i, e i * traceDual e i) - 1 = 0 := by
    refine eq_zero_of_trace_basis_mul_eq_zero e hd (fun k => ?_)
    rw [mul_sub, mul_one, map_sub, trace_mul_sum_traceDual e hd, sub_self]
  exact sub_eq_zero.mp hz

include hd in
theorem mul_traceDual (b : B) (i : Fin n) :
    b * traceDual e i = ∑ j, (e.repr (b * e j) i) • traceDual e j := by
  classical
  have hz : b * traceDual e i - ∑ j, (e.repr (b * e j) i) • traceDual e j = 0 := by
    refine eq_zero_of_trace_basis_mul_eq_zero e hd (fun k => ?_)
    rw [mul_sub, map_sub, sub_eq_zero]
    have hL : Algebra.trace A B (e k * (b * traceDual e i)) = e.repr (b * e k) i := by
      rw [← mul_assoc, mul_comm (e k) b]
      set c : Fin n → A := fun j => e.repr (b * e k) j with hc
      have hbe : b * e k = ∑ j, c j • e j := (e.sum_repr (b * e k)).symm
      rw [hbe, Finset.sum_mul, map_sum, Finset.sum_eq_single i]
      · rw [smul_mul_assoc, map_smul, smul_eq_mul, trace_mul_traceDual e hd i i, if_pos rfl,
          mul_one, repr_sum_apply]
      · intro j _ hj
        rw [smul_mul_assoc, map_smul, smul_eq_mul, trace_mul_traceDual e hd j i, if_neg hj,
          mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have hR : Algebra.trace A B (e k * ∑ j, (e.repr (b * e j) i) • traceDual e j)
        = e.repr (b * e k) i := by
      rw [Finset.mul_sum, map_sum, Finset.sum_eq_single k]
      · rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, trace_mul_traceDual e hd k k,
          if_pos rfl, mul_one]
      · intro j _ hj
        rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, trace_mul_traceDual e hd k j,
          if_neg (Ne.symm hj), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hL, hR]
  exact sub_eq_zero.mp hz

include hd in
theorem sum_deriv_traceDual (D : Derivation A B B) (b : B) :
    ∑ i, D (b * e i) * traceDual e i = ∑ i, D (e i) * (b * traceDual e i) := by
  classical
  have hL : ∀ i : Fin n, D (b * e i) * traceDual e i =
      ∑ j, (e.repr (b * e i) j) • (D (e j) * traceDual e i) := by
    intro i
    set c : Fin n → A := fun j => e.repr (b * e i) j with hc
    have hbe : b * e i = ∑ j, c j • e j := (e.sum_repr (b * e i)).symm
    rw [hbe, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Derivation.map_smul, smul_mul_assoc, repr_sum_apply]
  have hR : ∀ i : Fin n, D (e i) * (b * traceDual e i) =
      ∑ j, (e.repr (b * e j) i) • (D (e i) * traceDual e j) := by
    intro i
    rw [mul_traceDual e hd b i, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.mul_smul_comm]
  rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_congr rfl (fun i _ => hR i),
    Finset.sum_comm]

include hd in
/-- **A finite free algebra with unit discriminant has no nonzero derivations over the base.** -/
theorem derivation_eq_zero (D : Derivation A B B) : D = 0 := by
  ext b
  have hkey := sum_deriv_traceDual e hd D b
  have hL : ∑ i, D (b * e i) * traceDual e i =
      D b * (∑ i, e i * traceDual e i) + b * ∑ i, D (e i) * traceDual e i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [D.leibniz, smul_eq_mul, smul_eq_mul, add_mul]
    ring
  have hR : ∑ i, D (e i) * (b * traceDual e i) = b * ∑ i, D (e i) * traceDual e i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hL, hR, sum_mul_traceDual e hd, mul_one] at hkey
  have hzero : D b + b * ∑ i, D (e i) * traceDual e i = 0 + b * ∑ i, D (e i) * traceDual e i := by
    rw [hkey, zero_add]
  have : D b = 0 := add_right_cancel hzero
  simpa using this

end GaloisForLFunctions.HTGeometry
