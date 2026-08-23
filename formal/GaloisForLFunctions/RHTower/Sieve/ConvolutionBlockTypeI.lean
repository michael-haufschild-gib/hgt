import GaloisForLFunctions.RHTower.Sieve.DivisorFibreInterval

/-!
# A convolution over a block, in type-I form

Combining the convolution rearrangement with the fibre identity puts every Vaughan piece into the
shape the block estimates consume: an outer sum over one factor, and an inner sum over an INTERVAL
of the other.
-/

namespace RHTower.Sieve

open Finset

/-- The `[1,L]`-filter is invisible on a fibre interval. -/
theorem filter_Icc_Ico_eq {A' B' L : ℕ} (hA' : 1 ≤ A') (hB'L : B' - 1 ≤ L) :
    (Finset.Icc 1 L).filter (fun a => a ∈ Finset.Ico A' B') = Finset.Ico A' B' := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, ⟨h1, h2⟩⟩

/-- **A convolution summed over a block, in type-I form.** -/
theorem sum_conv_mul_Ico_eq {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (f g w : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico A B, (∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) * w n)
      = ∑ b ∈ Finset.Icc 1 L,
          g b * ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1), f a * w (a * b) := by
  classical
  have hI : ∀ n ∈ Finset.Ico A B, 1 ≤ n ∧ n ≤ L := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact ⟨by omega, by omega⟩
  rw [sum_conv_mul_eq hI f g w, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  have hb1 : 1 ≤ b := hb.1
  have hstep : (∑ a ∈ Finset.Icc 1 L,
        (if a * b ∈ Finset.Ico A B then f a * g b * w (a * b) else 0))
      = ∑ a ∈ (Finset.Icc 1 L).filter (fun a => a * b ∈ Finset.Ico A B),
          f a * g b * w (a * b) := (Finset.sum_filter _ _).symm
  rw [hstep, filter_mul_mem_Ico hb1 hA hB L,
    filter_Icc_Ico_eq (Nat.le_add_left 1 _)
      (by simpa using le_trans (Nat.div_le_self (B - 1) b) hBL), Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

end RHTower.Sieve
