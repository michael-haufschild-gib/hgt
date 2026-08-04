import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareNormalized

/-!
# When the normalized bound tends to zero

The normalized bound has the shape `2 log 2 · (1+ε)/ε · F`, and `(1+ε)/ε · F = F/ε + F`.  So it tends
to zero exactly when both `F/ε` and `F` do — which for `F` the sum of the three error terms is the
three conditions named on the card:

    (B(N)N)²/(ε Y L) → 0 ,    N²/(ε W L²) → 0 ,    (εL+1)²/L² → 0 ,

together with the same three without the `1/ε`, which they imply once `ε` is bounded.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **The normalized bound tends to zero.** -/
theorem tendsto_normalizedBound {F E : ℝ → ℝ} (hE : ∀ᶠ N : ℝ in atTop, E N ≠ 0)
    (h1 : Tendsto (fun N => F N / E N) atTop (𝓝 0)) (h2 : Tendsto F atTop (𝓝 0)) :
    Tendsto (fun N => 2 * Real.log 2 * ((1 + E N) / E N) * F N) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N => F N / E N + F N) atTop (𝓝 0) := by
    simpa using h1.add h2
  have hlim : Tendsto (fun N => 2 * Real.log 2 * (F N / E N + F N)) atTop (𝓝 0) := by
    simpa using hsum.const_mul (2 * Real.log 2)
  refine hlim.congr' ?_
  filter_upwards [hE] with N hN
  field_simp

/-- The three error terms, each divided by `ε`, tending to zero suffices. -/
theorem tendsto_normalizedBound_of_three {A B C E : ℝ → ℝ}
    (hE : ∀ᶠ N : ℝ in atTop, E N ≠ 0)
    (hA : Tendsto (fun N => A N / E N) atTop (𝓝 0))
    (hB : Tendsto (fun N => B N / E N) atTop (𝓝 0))
    (hC : Tendsto (fun N => C N / E N) atTop (𝓝 0))
    (hA' : Tendsto A atTop (𝓝 0)) (hB' : Tendsto B atTop (𝓝 0))
    (hC' : Tendsto C atTop (𝓝 0)) :
    Tendsto (fun N => 2 * Real.log 2 * ((1 + E N) / E N) * (A N + B N + C N))
      atTop (𝓝 0) := by
  refine tendsto_normalizedBound hE ?_ ?_
  · have h : Tendsto (fun N => A N / E N + B N / E N + C N / E N) atTop (𝓝 0) := by
      simpa using (hA.add hB).add hC
    refine h.congr fun N => ?_
    ring
  · simpa using (hA'.add hB').add hC'

end RHTower.Sieve
