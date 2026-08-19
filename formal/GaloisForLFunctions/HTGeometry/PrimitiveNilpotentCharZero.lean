import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Primitive elements of a characteristic-zero coalgebra are not nilpotent

If `x` is primitive for a comultiplication, `Δ (x ^ n)` expands binomially, and multiplying the
expansion by `x ^ (n-2) ⊗ 1` kills every term except the first-order one.  In characteristic zero
that term is a nonzero multiple of `x ^ (n-1) ⊗ x ^ (n-1)`, which is nonzero whenever `x ^ (n-1)`
is.  Hence a nilpotent primitive element vanishes.

This is the characteristic-zero input to Cartier's theorem that a commutative Hopf algebra over a
field of characteristic zero is reduced.
-/

open TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Over a field, a nonzero vector has nonzero self-tensor. -/
theorem tmul_self_ne_zero {k A : Type*} [Field k] [AddCommGroup A] [Module k A]
    {v : A} (hv : v ≠ 0) : v ⊗ₜ[k] v ≠ (0 : A ⊗[k] A) := by
  intro h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv
  have h2 := congrArg (fun t => TensorProduct.lid k A (LinearMap.rTensor A φ t)) h
  simp [hφ] at h2
  exact hv h2

/-- **A nilpotent primitive element of a characteristic-zero algebra vanishes.** -/
theorem eq_zero_of_isNilpotent_of_primitive
    {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    (Δ : A →ₐ[k] A ⊗[k] A) {x : A}
    (hprim : Δ x = x ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] x) (hnil : IsNilpotent x) : x = 0 := by
  classical
  by_contra hx
  haveI : Nontrivial A := nontrivial_of_ne x 0 hx
  have hex : ∃ m, x ^ m = 0 := hnil
  set n := Nat.find hex with hn
  have hxn : x ^ n = 0 := Nat.find_spec hex
  have hmin : ∀ j, j < n → x ^ j ≠ 0 := fun j hj => Nat.find_min hex hj
  have hn0 : n ≠ 0 := by
    intro h; rw [h, pow_zero] at hxn; exact one_ne_zero hxn
  have hn1 : n ≠ 1 := by
    intro h; rw [h, pow_one] at hxn; exact hx hxn
  have hn2 : 2 ≤ n := by omega
  have hxn1 : x ^ (n - 1) ≠ 0 := hmin _ (by omega)
  have hterm : ∀ i : ℕ,
      (x ⊗ₜ[k] (1 : A)) ^ i * ((1 : A) ⊗ₜ[k] x) ^ (n - i) * ((x ^ (n - 2)) ⊗ₜ[k] (1 : A))
        = (x ^ (i + (n - 2))) ⊗ₜ[k] (x ^ (n - i)) := by
    intro i
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp [pow_add]
  have h0 : (0 : A ⊗[k] A) = ∑ i ∈ Finset.range (n + 1),
      (x ⊗ₜ[k] (1 : A)) ^ i * ((1 : A) ⊗ₜ[k] x) ^ (n - i) * (n.choose i : A ⊗[k] A) := by
    rw [← add_pow, ← hprim, ← map_pow, hxn, map_zero]
  have hmul : (0 : A ⊗[k] A) = ∑ i ∈ Finset.range (n + 1),
      ((x ^ (i + (n - 2))) ⊗ₜ[k] (x ^ (n - i))) * (n.choose i : A ⊗[k] A) := by
    have := congrArg (fun t : A ⊗[k] A => t * ((x ^ (n - 2)) ⊗ₜ[k] (1 : A))) h0
    simp only [zero_mul, Finset.sum_mul] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_right_comm, hterm i]
  have hsingle : ∑ i ∈ Finset.range (n + 1),
      ((x ^ (i + (n - 2))) ⊗ₜ[k] (x ^ (n - i))) * (n.choose i : A ⊗[k] A)
      = ((x ^ (1 + (n - 2))) ⊗ₜ[k] (x ^ (n - 1))) * (n.choose 1 : A ⊗[k] A) := by
    refine Finset.sum_eq_single 1 ?_ ?_
    · intro i _ hi1
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have : x ^ (n - 0) = 0 := by simpa using hxn
        rw [this, TensorProduct.tmul_zero, zero_mul]
      · have hi2 : 2 ≤ i := by omega
        have : x ^ (i + (n - 2)) = 0 := by
          have hsplit : i + (n - 2) = (i - 2) + n := by omega
          rw [hsplit, pow_add, hxn, mul_zero]
        rw [this, TensorProduct.zero_tmul, zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hsingle] at hmul
  have hidx : 1 + (n - 2) = n - 1 := by omega
  rw [hidx] at hmul
  have hchoose : (n.choose 1 : A ⊗[k] A) = (n : ℕ) • (1 : A ⊗[k] A) := by
    rw [Nat.choose_one_right, nsmul_eq_mul, mul_one]
  rw [hchoose, mul_smul_comm, mul_one] at hmul
  have hcast : ((n : ℕ) • ((x ^ (n - 1)) ⊗ₜ[k] (x ^ (n - 1))) : A ⊗[k] A)
      = ((n : k)) • ((x ^ (n - 1)) ⊗ₜ[k] (x ^ (n - 1))) := by
    rw [← Nat.cast_smul_eq_nsmul k]
  rw [hcast] at hmul
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have := (smul_eq_zero.mp hmul.symm).resolve_left hnk
  exact tmul_self_ne_zero hxn1 this

end

end GaloisForLFunctions.HTGeometry
