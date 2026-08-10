import GaloisForLFunctions.RHTower.Sieve.MaximalWindowReduction

/-!
# The dyadic mean square, expanded into pairs

Gallagher's lemma is an identity between a mean square of short sums and a double sum weighted by
the overlap of two windows; on the integers the same expansion is elementary.  Writing a
fixed-length window as an ordinary sum,

```text
fixedWindowSq f ℓ z = (∑_{b ∈ (z, z+ℓ]} f(b))² ,
```

and expanding the square gives

```text
dyadicMeanSquare f ℓ A B
  = ∑_{m, n ∈ (A, B+ℓ]} f(m)·f(n)·#{ z ∈ [A,B] : m, n ∈ (z, z+ℓ] } ,
```

whose kernel is the discrete overlap `#{z}` — the analogue of `volume_real_logWindow_inter`'s
`(δ − |log m − log n|)₊`.  The kernel vanishes as soon as `|m − n| ≥ ℓ`, which is the near-diagonal
structure the whole estimate rests on.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- A fixed-length window is an ordinary sum. -/
theorem fixedWindowSq_eq (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (z : ℕ) :
    fixedWindowSq f ℓ z = (∑ b ∈ Finset.Icc (z + 1) (z + ℓ), f b) ^ 2 := by
  have hw := window_eq_partialSum f (y := z + 1) (by omega) (ℓ - 1)
  have hidx : z + 1 + (ℓ - 1) = z + ℓ := by omega
  have hidx2 : z + 1 - 1 = z := by omega
  rw [hidx, hidx2] at hw
  rw [fixedWindowSq, ← hw]

/-- The mean square, with the square expanded. -/
theorem dyadicMeanSquare_eq_pairs (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : ℕ) :
    dyadicMeanSquare f ℓ A B
      = ∑ z ∈ Finset.Icc A B, ∑ m ∈ Finset.Icc (z + 1) (z + ℓ),
          ∑ n ∈ Finset.Icc (z + 1) (z + ℓ), f m * f n := by
  rw [dyadicMeanSquare]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [fixedWindowSq_eq f hℓ z, sq, Finset.sum_mul_sum]

/-- **The mean square as a weighted double sum over pairs.** -/
theorem dyadicMeanSquare_eq_count (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : ℕ) :
    dyadicMeanSquare f ℓ A B
      = ∑ m ∈ Finset.Icc (A + 1) (B + ℓ), ∑ n ∈ Finset.Icc (A + 1) (B + ℓ),
          f m * f n
            * (((Finset.Icc A B).filter
                (fun z => m ∈ Finset.Icc (z + 1) (z + ℓ)
                  ∧ n ∈ Finset.Icc (z + 1) (z + ℓ))).card : ℝ) := by
  classical
  rw [dyadicMeanSquare_eq_pairs f hℓ A B]
  -- widen the inner ranges to a fixed one
  have hwiden : ∀ z ∈ Finset.Icc A B,
      (∑ m ∈ Finset.Icc (z + 1) (z + ℓ), ∑ n ∈ Finset.Icc (z + 1) (z + ℓ), f m * f n)
        = ∑ m ∈ Finset.Icc (A + 1) (B + ℓ), ∑ n ∈ Finset.Icc (A + 1) (B + ℓ),
            (if m ∈ Finset.Icc (z + 1) (z + ℓ) ∧ n ∈ Finset.Icc (z + 1) (z + ℓ)
              then f m * f n else 0) := by
    intro z hz
    rw [Finset.mem_Icc] at hz
    have hsub : Finset.Icc (z + 1) (z + ℓ) ⊆ Finset.Icc (A + 1) (B + ℓ) := by
      intro b hb
      rw [Finset.mem_Icc] at hb ⊢
      omega
    rw [← Finset.sum_subset hsub (fun m _ hm => ?_)]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [← Finset.sum_subset hsub (fun n _ hn => ?_)]
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [if_pos ⟨hm, hn⟩]
      · rw [if_neg (fun h => hn h.2)]
    · refine Finset.sum_eq_zero fun n _ => ?_
      rw [if_neg (fun h => hm h.1)]
  rw [Finset.sum_congr rfl hwiden]
  -- swap the order of summation
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

end RHTower.Sieve

end
