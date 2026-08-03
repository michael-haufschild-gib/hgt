import GaloisForLFunctions.RHTower.Sieve.InverseDFT

/-!
# The surviving residue class is a single index

In `kernel_of_symbol` the right-hand side is a sum over `{d < Q : Q ∣ d + k}`.  When `k < Q` that set
is a singleton: `d + k < 2Q`, so the only multiples of `Q` it can equal are `0` and `Q`, which pins
`d` to `(Q - k) % Q` in both cases — `0` when `k = 0`, and `Q - k` otherwise.

Hence the inverse discrete Fourier transform returns a single coefficient,

`∑_j (∑_d K_d ζ^{jd}) ζ^{jk} = Q · K_{(Q-k) % Q}`,

which is the form in which a prescribed kernel is matched against a symbol.
-/

namespace RHTower.Sieve

open Finset

/-- The residue class surviving the orthogonality filter is a singleton. -/
theorem filter_dvd_add_eq {Q k : ℕ} (hQ : 0 < Q) (hk : k < Q) :
    {d ∈ Finset.range Q | Q ∣ d + k} = {(Q - k) % Q} := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, hdvd⟩
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : c < 2 := by
      by_contra hcon
      have h2 : 2 ≤ c := by omega
      have : 2 * Q ≤ Q * c := by
        calc 2 * Q = Q * 2 := by ring
          _ ≤ Q * c := Nat.mul_le_mul_left Q h2
      omega
    interval_cases c
    · simp only [Nat.mul_zero, Nat.add_eq_zero_iff] at hc
      obtain ⟨hd0, hk0⟩ := hc
      subst hd0
      subst hk0
      simp
    · simp only [Nat.mul_one] at hc
      have hkpos : 0 < k := by omega
      have hlt : Q - k < Q := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
  · intro hd
    subst hd
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · refine ⟨?_, ?_⟩
      · simpa using hQ
      · simp
    · have hlt : Q - k < Q := by omega
      have hmod : (Q - k) % Q = Q - k := Nat.mod_eq_of_lt hlt
      rw [hmod]
      exact ⟨hlt, ⟨1, by omega⟩⟩

/-- The filtered sum is a single coefficient. -/
theorem sum_filter_dvd_add (K : ℕ → ℂ) {Q k : ℕ} (hQ : 0 < Q) (hk : k < Q) :
    ∑ d ∈ {d ∈ Finset.range Q | Q ∣ d + k}, K d = K ((Q - k) % Q) := by
  rw [filter_dvd_add_eq hQ hk, Finset.sum_singleton]

/-- **Inverse discrete Fourier transform.**  Pairing a symbol against a character returns a single
coefficient. -/
theorem kernel_of_symbol_singleton {ζ : ℂ} {Q : ℕ} (hζ : IsPrimitiveRoot ζ Q) (K : ℕ → ℂ)
    {k : ℕ} (hQ : 0 < Q) (hk : k < Q) :
    ∑ j ∈ Finset.range Q, (∑ d ∈ Finset.range Q, K d * ζ ^ (j * d)) * ζ ^ (j * k)
      = (Q : ℂ) * K ((Q - k) % Q) := by
  rw [kernel_of_symbol hζ K k, sum_filter_dvd_add K hQ hk]

end RHTower.Sieve
