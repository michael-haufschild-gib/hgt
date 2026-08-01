import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The iterated Leibniz rule for a derivation

Iterating a derivation on a product distributes over the binomial coefficients: the `m`-th
derivative of a product is the sum over `k` of `binom(m,k)` times the `k`-th derivative of the first
factor against the `(m-k)`-th derivative of the second.  The induction step is Pascal's rule, read
off by peeling the first term of the shifted sum.

Applied to a pair of mutually inverse elements it gives the relations that a product being constant
imposes on the two jet sequences.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Iterating a derivation kills zero. -/
theorem derivation_iterate_zero (D : Derivation R A A) (m : ℕ) : (⇑D)^[m] 0 = 0 := by
  induction m with
  | zero => rw [Function.iterate_zero_apply]
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]

/-- **The iterated Leibniz rule.** -/
theorem derivation_iterate_mul (D : Derivation R A A) (u v : A) (m : ℕ) :
    (⇑D)^[m] (u * v) =
      ∑ k ∈ Finset.range (m + 1),
        (Nat.choose m k) • ((⇑D)^[k] u * (⇑D)^[m - k] v) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hterm : ∀ k ∈ Finset.range (m + 1),
          D ((Nat.choose m k) • ((⇑D)^[k] u * (⇑D)^[m - k] v)) =
            (Nat.choose m k) • ((⇑D)^[k + 1] u * (⇑D)^[m - k] v) +
              (Nat.choose m k) • ((⇑D)^[k] u * (⇑D)^[m + 1 - k] v) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have h1 : D ((⇑D)^[k] u) = (⇑D)^[k + 1] u :=
          (Function.iterate_succ_apply' _ _ _).symm
        have h2 : D ((⇑D)^[m - k] v) = (⇑D)^[m + 1 - k] v := by
          rw [show m + 1 - k = (m - k) + 1 from by omega, Function.iterate_succ_apply']
        rw [map_nsmul, Derivation.leibniz, h1, h2]
        simp only [smul_eq_mul, nsmul_eq_mul]
        ring
      have hsplit : (⇑D)^[m + 1] (u * v) =
          (∑ k ∈ Finset.range (m + 1),
              (Nat.choose m k) • ((⇑D)^[k + 1] u * (⇑D)^[m - k] v)) +
            ∑ k ∈ Finset.range (m + 1),
              (Nat.choose m k) • ((⇑D)^[k] u * (⇑D)^[m + 1 - k] v) := by
        rw [Function.iterate_succ_apply', ih, map_sum, Finset.sum_congr rfl hterm,
          Finset.sum_add_distrib]
      rw [hsplit]
      rw [Finset.sum_range_succ' (fun k =>
        (Nat.choose (m + 1) k) • ((⇑D)^[k] u * (⇑D)^[m + 1 - k] v)) (m + 1)]
      have hshift : ∀ i ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (i + 1)) • ((⇑D)^[i + 1] u * (⇑D)^[m + 1 - (i + 1)] v) =
            (Nat.choose m i) • ((⇑D)^[i + 1] u * (⇑D)^[m - i] v) +
              (Nat.choose m (i + 1)) • ((⇑D)^[i + 1] u * (⇑D)^[m - i] v) := by
        intro i _
        rw [Nat.succ_sub_succ, Nat.choose_succ_succ, add_smul]
      rw [Finset.sum_congr rfl hshift, Finset.sum_add_distrib]
      have htail : ∑ i ∈ Finset.range (m + 1),
          (Nat.choose m (i + 1)) • ((⇑D)^[i + 1] u * (⇑D)^[m - i] v) =
          ∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k) • ((⇑D)^[k] u * (⇑D)^[m + 1 - k] v) -
              (Nat.choose (m + 1) 0) • ((⇑D)^[0] u * (⇑D)^[m + 1 - 0] v) := by
        rw [Finset.sum_range_succ' (fun k =>
          (Nat.choose m k) • ((⇑D)^[k] u * (⇑D)^[m + 1 - k] v)) m]
        rw [Finset.sum_range_succ (fun i =>
          (Nat.choose m (i + 1)) • ((⇑D)^[i + 1] u * (⇑D)^[m - i] v)) m]
        rw [Nat.choose_succ_self, zero_smul, add_zero]
        have hin : ∀ i ∈ Finset.range m,
            (Nat.choose m (i + 1)) • ((⇑D)^[i + 1] u * (⇑D)^[m - i] v) =
              (Nat.choose m (i + 1)) • ((⇑D)^[i + 1] u * (⇑D)^[m + 1 - (i + 1)] v) := by
          intro i _
          rw [Nat.succ_sub_succ]
        rw [Finset.sum_congr rfl hin]
        simp
      rw [htail]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
      ring

/-- **The relations imposed by a constant product.**  If the product of two elements is a constant,
then from the first derivative on the binomial combination of their jets vanishes. -/
theorem derivation_iterate_mul_eq_zero_of_mul_eq_one (D : Derivation R A A) {u v : A}
    (huv : u * v = 1) {m : ℕ} (hm : 0 < m) :
    ∑ k ∈ Finset.range (m + 1), (Nat.choose m k) • ((⇑D)^[k] u * (⇑D)^[m - k] v) = 0 := by
  rw [← derivation_iterate_mul D u v m, huv]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Function.iterate_succ_apply, Derivation.map_one_eq_zero, derivation_iterate_zero]

end GaloisForLFunctions.HTGeometry
