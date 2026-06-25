/-
# Hurwitz N=2 — the Laurent-coefficient extraction kernel

The density-shadow needs the most-singular coefficient of a vanishing singular block
`∑_{k≤K} c_k(t)·t^{−(s+k)} = 0`. Multiplying by `t^{s+K}` collapses the exponents to non-negative integer
powers `t^{K−k}` (via `cpow_add` on the positive real ray and `cpow_natCast`); letting `t → 0⁺` kills
every `k < K` term and leaves the top coefficient `c_K(0)`. So `c_K(0) = 0`. This is the linear-eigenspace
analogue of `quadratic_filtration_top`, with a complex (`cpow`) singular base rather than integer powers.
-/
import Mathlib

open Complex Filter Topology

namespace HurwitzN2Laurent

/-- **Laurent top-coefficient extraction.** A singular block `∑_{k≤K} c_k(t)·t^{−(s+k)}` (`t > 0` real)
that vanishes near `t = 0⁺`, with each coefficient `c_k` continuous at `0`, forces the top coefficient
`c_K(0) = 0`. -/
theorem linear_laurent_top {s : ℂ} {K : ℕ} {c : ℕ → ℂ → ℂ}
    (hc : ∀ k, ContinuousAt (c k) 0)
    (hrel : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∑ k ∈ Finset.range (K + 1), c k (t : ℂ) * ((t : ℂ)) ^ (-(s + (k : ℂ))) = 0) :
    c K 0 = 0 := by
  -- on the positive ray, t^{s+K}·t^{-(s+k)} = t^{K-k} (a non-negative integer power)
  have hmul : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∑ k ∈ Finset.range (K + 1), c k (t : ℂ) * ((t : ℂ)) ^ (K - k) = 0 := by
    filter_upwards [hrel, self_mem_nhdsWithin] with t ht htpos
    have htne : ((t : ℂ)) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt htpos
    have key : ((t : ℂ)) ^ ((s : ℂ) + (K : ℂ)) * (∑ k ∈ Finset.range (K + 1),
        c k (t : ℂ) * ((t : ℂ)) ^ (-(s + (k : ℂ))))
        = ∑ k ∈ Finset.range (K + 1), c k (t : ℂ) * ((t : ℂ)) ^ (K - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show ((t : ℂ)) ^ ((s : ℂ) + (K : ℂ)) * (c k (t : ℂ) * ((t : ℂ)) ^ (-(s + (k : ℂ))))
            = c k (t : ℂ) * (((t : ℂ)) ^ ((s : ℂ) + (K : ℂ)) * ((t : ℂ)) ^ (-(s + (k : ℂ)))) from by
            ring,
        ← Complex.cpow_add _ _ htne,
        show ((s : ℂ) + (K : ℂ)) + (-(s + (k : ℂ))) = (((K - k : ℕ)) : ℂ) from by
          rw [Nat.cast_sub hkK]; ring,
        Complex.cpow_natCast]
    rw [ht, mul_zero] at key
    exact key.symm
  -- take t → 0⁺ : only the k = K term (power t^0) survives, → c_K 0
  have h1 : Tendsto (fun t : ℝ => ((t : ℂ))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    simpa using this
  have hterm : ∀ k : ℕ, k ∈ Finset.range (K + 1) →
      Tendsto (fun t : ℝ => c k (t : ℂ) * ((t : ℂ)) ^ (K - k)) (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (if k = K then c K 0 else 0)) := by
    intro k hk
    have hck : Tendsto (fun t : ℝ => c k (t : ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (c k 0)) :=
      (hc k).tendsto.comp h1
    by_cases hkK : k = K
    · subst hkK
      simp only [Nat.sub_self, pow_zero, mul_one, ↓reduceIte]
      exact hck
    · rw [if_neg hkK]
      have hpow : Tendsto (fun t : ℝ => ((t : ℂ)) ^ (K - k)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
        have hlt : k < K := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkK
        simpa [zero_pow (by omega : K - k ≠ 0)] using h1.pow (K - k)
      simpa using hck.mul hpow
  have hsum := tendsto_finsetSum (Finset.range (K + 1)) hterm
  rw [Finset.sum_ite_eq' (Finset.range (K + 1)) K (fun _ => c K 0)] at hsum
  simp only [Finset.mem_range, Nat.lt_succ_self, if_true] at hsum
  have hzero : Tendsto (fun t : ℝ => ∑ k ∈ Finset.range (K + 1), c k (t : ℂ) * ((t : ℂ)) ^ (K - k))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := tendsto_const_nhds.congr' (hmul.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique hsum hzero

end HurwitzN2Laurent
