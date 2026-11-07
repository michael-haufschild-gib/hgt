import GaloisForLFunctions.RigidArithmeticOfCuts.TheLiouvilleChebyshevIdentity

/-!
# The exact identity determines the parity

Every reading of `Λ` sees the Liouville twin only through even prime powers. What reads `λ` on all integers through the cut system?
The cut system does, exactly. A weight `f` on the integers whose partial sums satisfy Liouville's cut identity

`Σ_{k ≤ x} F(⌊x/k⌋) = ⌊√x⌋`,  `F(x) = Σ_{n ≤ x} f(n)`,

is `λ` (`eq_liouville_of_floorSum`), because floor sums are triangular (`eq_of_floorSum_eq`). The twisted signs `λ χ` for a nontrivial
completely multiplicative sign `χ` fail it (`not_floorSum_of_ne_liouville`).

So parity is not missing information: the exact identity pins `λ` on every integer. What is missing is a size statement for its
partial sums, and at a power saving that size statement is a zero-free strip (`zeroFree_iff_liouville_power`). Parity in this field is
quantitative, and it reduces to the zero location exactly.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The partial sums of a weight. -/
def partialWeight (f : ℕ → ℝ) (x : ℕ) : ℝ := ∑ n ∈ Ioc 0 x, f n

/-- **The exact identity determines `λ`.** A weight whose partial sums satisfy Liouville's cut identity is `λ`. -/
theorem eq_liouville_of_floorSum {f : ℕ → ℝ} (h : ∀ x, floorSum (partialWeight f) x = (Nat.sqrt x : ℝ))
    {n : ℕ} (hn : 1 ≤ n) : f n = (ArithmeticFunction.liouville n : ℝ) := by
  have hF : ∀ x, partialWeight f x = liouvilleR x := by
    intro x
    refine eq_of_floorSum_eq (by simp [partialWeight]) (by simp [liouvilleR]) (fun y => ?_) x
    rw [h y, floorSum_liouvilleR]
  have hstep : ∀ m : ℕ, partialWeight f (m + 1) = partialWeight f m + f (m + 1) := by
    intro m
    rw [partialWeight, partialWeight, ← Finset.insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le m),
      sum_insert (by simp)]
    ring
  have hstepL : ∀ m : ℕ, liouvilleR (m + 1) = liouvilleR m + (ArithmeticFunction.liouville (m + 1) : ℝ) := by
    intro m
    rw [liouvilleR, liouvilleR, ← Finset.insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le m),
      sum_insert (by simp)]
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := hstep m
  have h2 := hstepL m
  rw [hF, hF] at h1
  linarith

/-- **The twisted signs fail it.** For a weight `g ≠ λ` on some positive integer, the cut identity fails. -/
theorem not_floorSum_of_ne_liouville {g : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hne : g n ≠ (ArithmeticFunction.liouville n : ℝ)) :
    ¬ ∀ x, floorSum (partialWeight g) x = (Nat.sqrt x : ℝ) :=
  fun h => hne (eq_liouville_of_floorSum h hn)

/-- `λ` itself satisfies the identity. -/
theorem floorSum_partialWeight_liouville (x : ℕ) :
    floorSum (partialWeight fun n => (ArithmeticFunction.liouville n : ℝ)) x = (Nat.sqrt x : ℝ) := by
  have h : partialWeight (fun n => (ArithmeticFunction.liouville n : ℝ)) = liouvilleR := by
    funext y
    rfl
  rw [h, floorSum_liouvilleR]

end GaloisForLFunctions.RigidArithmeticOfCuts
