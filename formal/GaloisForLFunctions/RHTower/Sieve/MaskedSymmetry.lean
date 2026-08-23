import GaloisForLFunctions.RHTower.Sieve.EffectiveSetHypotheses

/-!
# The masked summand is symmetric

`maskedNdExp T r A B d m = maskedNdExp T r A B m d` for `d, m ≥ 1`, because the fibre relation is
symmetric and `F(d·m) = F(m·d)`.  Consequently the type-II bilinear form may be Cauchy--Schwarzed
on EITHER variable with the same lemmas — which is exactly what the exponent budget's
`min(A(D), B(D))` step needs.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem ndExp_symm (T r : ℝ) (m d : ℕ) : ndExp T r m d = ndExp T r d m := by
  rw [ndExp, ndExp, mul_comm ((m : ℝ)) ((d : ℝ))]

/-- **The masked summand is symmetric.** -/
theorem maskedNdExp_symm {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (T r : ℝ) {d m : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) :
    maskedNdExp T r A B d m = maskedNdExp T r A B m d := by
  rw [maskedNdExp, maskedNdExp]
  by_cases h : m ∈ fibreIco A B d
  · have h' : d ∈ fibreIco A B m := (mem_fibre_symm hA hB hd hm).1 h
    rw [if_pos h, if_pos h', ndExp_symm]
  · have h' : d ∉ fibreIco A B m := fun hcon => h ((mem_fibre_symm hA hB hd hm).2 hcon)
    rw [if_neg h, if_neg h']

/-- **The type-II bilinear form, with the roles of the variables exchanged.** -/
theorem sum_typeII_masked_swap {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (T r : ℝ) (f g : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 L, f d * ∑ m ∈ Finset.Icc 1 L, g m * maskedNdExp T r A B d m)
      = ∑ m ∈ Finset.Icc 1 L, g m * ∑ d ∈ Finset.Icc 1 L, f d * maskedNdExp T r A B m d := by
  classical
  have hexp : ∀ d ∈ Finset.Icc 1 L, (f d * ∑ m ∈ Finset.Icc 1 L, g m * maskedNdExp T r A B d m)
      = ∑ m ∈ Finset.Icc 1 L, f d * g m * maskedNdExp T r A B d m := by
    intro d _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hexp' : ∀ m ∈ Finset.Icc 1 L, (g m * ∑ d ∈ Finset.Icc 1 L, f d * maskedNdExp T r A B m d)
      = ∑ d ∈ Finset.Icc 1 L, f d * g m * maskedNdExp T r A B m d := by
    intro m _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_congr rfl hexp', Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hm hd
  rw [maskedNdExp_symm hA hB T r hd.1 hm.1]

end

end RHTower.Sieve
